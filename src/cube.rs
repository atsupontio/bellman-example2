#![allow(unused_imports)]
#![allow(unused_variables)]
use std::clone;

use bellman::pairing::bls12_381::{Bls12};
// For randomness (during paramgen and proof generation)
use rand::{thread_rng, Rng};
use bellman::pairing::ff::{PrimeField, ScalarEngine, Field, PrimeFieldRepr};
use bellman::pairing::{Engine, CurveAffine, EncodedPoint};

use bellman::{
    Circuit,
    ConstraintSystem,
    SynthesisError
};

use bellman::groth16::{
    Proof,
    generate_random_parameters,
    prepare_verifying_key,
    create_random_proof,
    verify_proof,
};

// proving that I know x such that x^3 + x + 5 == 35
// Generalized: x^3 + x + 5 == out
#[derive(Clone)]
pub struct CubeDemo<E:Engine> {
    pub x: Option<E::Fr>,
}

impl <E: Engine> Circuit<E> for CubeDemo<E> {
    fn synthesize<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS
    ) -> Result<(), SynthesisError>
    {
        // Flattened into quadratic equations (x^3 + x + 5 == 35):
        // x * x = tmp_1
        // tmp_1 * x = y
        // y + x = tmp_2
        // tmp_2 + 5 = out
        // Resulting R1CS with w = [one, x, tmp_1, y, tmp_2, out]

        // Allocate the first private "auxiliary" variable
        let x_val = self.x;
        let x = cs.alloc(|| "x", || {
            x_val.ok_or(SynthesisError::AssignmentMissing)
        })?;

        // Allocate: x * x = tmp_1
        let tmp_1_val = x_val.map(|mut e| {
            e.square();
            e
        });
        let tmp_1 = cs.alloc(|| "tmp_1", || {
            tmp_1_val.ok_or(SynthesisError::AssignmentMissing)
        })?;
        // Enforce: x * x = tmp_1
        cs.enforce(
            || "tmp_1",
            |lc| lc + x,
            |lc| lc + x,
            |lc| lc + tmp_1
        );

        // Allocate: tmp_1 * x = y
        let x_cubed_val = tmp_1_val.map(|mut e| {
            e.mul_assign(&x_val.unwrap());
            e
        });
        let x_cubed = cs.alloc(|| "x_cubed", || {
            x_cubed_val.ok_or(SynthesisError::AssignmentMissing)
        })?;
        // Enforce: tmp_1 * x = y
        cs.enforce(
            || "x_cubed",
            |lc| lc + tmp_1,
            |lc| lc + x,
            |lc| lc + x_cubed
        );

        // Allocating the public "primary" output uses alloc_input
        let out = cs.alloc_input(|| "out", || {
            let mut tmp = x_cubed_val.unwrap();
            tmp.add_assign(&x_val.unwrap());
            tmp.add_assign(&E::Fr::from_str("5").unwrap());
            Ok(tmp)
        })?;
        // tmp_2 + 5 = out
        // => (tmp_2 + 5) * 1 = out
        cs.enforce(
            || "out",
            |lc| lc + x_cubed + x + (E::Fr::from_str("5").unwrap(), CS::one()),
            |lc| lc + CS::one(),
            |lc| lc + out
        );
        // lc is an inner product of all variables with some vector of coefficients
        // bunch of variables added together with some coefficients

        // usually if mult by 1 can do more efficiently
        // x2 * x = out - x - 5

        // mult quadratic constraints
        //

        Ok(())
    }
}

pub fn proof_write(proof: &mut Proof<Bls12>, proof_encode:&mut Vec<u8>){
    proof_encode[0..32*2].copy_from_slice(proof.a.into_uncompressed().as_ref());
    proof_encode[32*2..32*6].copy_from_slice(proof.b.into_uncompressed().as_ref());
    proof_encode[32*6..32*8].copy_from_slice(proof.c.into_uncompressed().as_ref());

    println!("proof : {:?}", proof_encode);
    println!("proof_encode: {:?}", proof_encode.len());
}

#[test]
fn test_cube_proof(){
    // This may not be cryptographically safe, use
    // `OsRng` (for example) in production software.
    let mut rng = thread_rng();

    println!("Creating parameters...");

    // Create parameters for our circuit
    let params = {
        let c = CubeDemo::<Bls12> {
            x: None
        };

        generate_random_parameters::<Bls12, _, _>(c, &mut rng).unwrap()
    };

    // Prepare the verification key (for proof verification)
    let pvk = prepare_verifying_key(&params.vk);

    // println!("alphag1{:?}", params.vk.alpha_g1.to_uncompressed());
    // println!("betag1{:?}", params.vk.beta_g1.to_compressed());
    // println!("betag2{:?}", params.vk.beta_g2.to_compressed());
    // println!("gammag2{:?}", params.vk.gamma_g2.to_compressed());
    // println!("deltag1{:?}", params.vk.delta_g1.to_compressed());
    // println!("deltag2{:?}", params.vk.delta_g2.to_compressed());
    // println!("ic0{:?}", params.vk.ic[0].to_compressed());
    // println!("ic1{:?}", params.vk.ic[1].to_compressed());

    // println!(r#"{{"alpha_1":{:?},"beta_1":{:?},"beta_2":{:?},"gamma_2":{:?},"delta_1":{:?},"delta_2":{:?},"ic":[{:?},{:?}]}}"#, params.vk.alpha_g1.into_uncompressed(), params.vk.beta_g1.into_uncompressed(), params.vk.beta_g2.into_uncompressed(), params.vk.gamma_g2.into_uncompressed(), params.vk.delta_g1.into_uncompressed(), params.vk.delta_g2.into_uncompressed(), params.vk.ic[0].into_uncompressed(), params.vk.ic[1].into_uncompressed());
    
    println!("Creating proofs...");

    // Create an instance of circuit
    let c = CubeDemo::<Bls12> {
        x: PrimeField::from_str("3")
    };

    // Create a groth16 proof with our parameters.
    let proof = create_random_proof(c, &params, &mut rng).unwrap();

    let mut proof_vec = vec![];
    proof.write(&mut proof_vec).unwrap();

    // println!("proof_vec: {:?}", proof_vec);

    let proof_a_affine = proof.a.into_uncompressed();
    println!("proofaaffine: {:?}", proof_a_affine);

    let test = proof_a_affine.into_affine().unwrap();

    println!("proof: {:?}", proof);
    println!("test: {:?}", test);

    let proof_b_affine = proof.b.into_uncompressed();
    // println!("proofabffine: {:?}", proof_b_affine);

    let proof_c_affine = proof.c.into_uncompressed();
    // println!("proofacffine: {:?}", proof_c_affine);

    println!(r#"{{"pi_a":{:?},"pi_b":{:?},"pi_c":{:?}}}"#, proof_a_affine, proof_b_affine, proof_c_affine);
    let res_proof = format!(r#"{{"pi_a":{:?},"pi_b":{:?},"pi_c":{:?}}}"#, proof_a_affine, proof_b_affine, proof_c_affine);
    let res_vkey = format!(r#"{{"alpha_1":{:?},"beta_1":{:?},"beta_2":{:?},"gamma_2":{:?},"delta_1":{:?},"delta_2":{:?},"ic":[{:?},{:?}]}}"#, params.vk.alpha_g1.into_uncompressed(), params.vk.beta_g1.into_uncompressed(), params.vk.beta_g2.into_uncompressed(), params.vk.gamma_g2.into_uncompressed(), params.vk.delta_g1.into_uncompressed(), params.vk.delta_g2.into_uncompressed(), params.vk.ic[0].into_uncompressed(), params.vk.ic[1].into_uncompressed());

    assert!(verify_proof(
        &pvk,
        &proof,
        &[PrimeField::from_str("35").unwrap()]
    ).is_ok());
}