#![allow(unused_imports)]
#![allow(unused_variables)]
use bellman::gadgets::boolean;
use bls12_381::{Bls12, Scalar};
// For randomness (during paramgen and proof generation)
use rand::{thread_rng, Rng};
use ff::PrimeField as Fr;

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

use crate::encode;

#[derive(Clone)]
pub struct CIDPreimage {
    pub user_id_bits: Vec<Option<bool>>,
    pub secret_bits: Vec<Option<bool>>,
    pub nonce_bits: Vec<Option<bool>>,
}


// proving that I know x such that x^3 + x + 5 == 35
// Generalized: x^3 + x + 5 == out
#[allow(clippy::upper_case_acronyms)]
pub struct VacPassDemo<E: Fr> {
    pub CID: Option<E>,
    pub preimage: CIDPreimage<E>,
    pub VacCnt: Option<E>,
}

impl<E: Fr> Clone for VacPassDemo<E> {
    fn clone(&self) -> Self {
        VacPassDemo {
            CID: self.CID.clone(),
            preimage: self.preimage.clone(),
            VacCnt: self.VacCnt.clone(),
        }
    }
}

const NUM_USER_ID_BITS: usize = 128;

impl <E: Fr> Circuit<E> for VacPassDemo<E> {
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

        let mut user_id_bits = Vec::<boolean::Boolean>::with_capacity(NUM_USER_ID_BITS);
        // Allocate bits for use of making CID
        for i in 0..NUM_USER_ID_BITS {
            let bit = boolean::Boolean::from(boolean::AllocatedBit::alloc(
                cs.namespace(|| format!("allocating user id bit {}", i)),
                self.preimage.user_id_bits[i]
            )?
            );
            user_id_bits.push(bit);
        }

        let mut secret_bits = Vec::<boolean::Boolean>::with_capacity(NUM_USER_ID_BITS);
        // Allocate bits for use of making CID
        for i in 0..NUM_USER_ID_BITS {
            let bit = boolean::Boolean::from(boolean::AllocatedBit::alloc(
                cs.namespace(|| format!("allocating secret bit {}", i)),
                self.preimage.secret_bits[i]
            )?
            );
            secret_bits.push(bit);
        }

        let mut user_id_bits = Vec::<boolean::Boolean>::with_capacity(NUM_USER_ID_BITS);
        // Allocate bits for use of making CID
        for i in 0..NUM_USER_ID_BITS {
            let bit = boolean::Boolean::from(boolean::AllocatedBit::alloc(
                cs.namespace(|| format!("allocating user id bit {}", i)),
                self.preimage.user_id_bits[i]
            )?
            );
            user_id_bits.push(bit);
        }

        // Allocate: x * x = tmp_1
        let tmp_1_val = x_val.map(|e| {
            e.square()
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
            tmp.add_assign(&E::from_str_vartime("5").unwrap());
            Ok(tmp)
        })?;
        // tmp_2 + 5 = out
        // => (tmp_2 + 5) * 1 = out
        cs.enforce(
            || "out",
            |lc| lc + x_cubed + x + (E::from_str_vartime("5").unwrap(), CS::one()),
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

#[test]
fn test_cube_proof(){
    // This may not be cryptographically safe, use
    // `OsRng` (for example) in production software.
    let mut rng = thread_rng();

    const NUM_USER_ID_BITS: u32 = 128;
    const NUM_SECRET_BITS: u32 = 128;
    const NUM_NONCE_BITS: u32 = 128;

    println!("Creating parameters...");

    // Create parameters for our circuit
     // Create parameters for our circuit
     let params = {
        let preimage = CIDPreimage {
            user_id_bits: vec![None; NUM_USER_ID_BITS],
            secret_bits: vec![None; NUM_SECRET_BITS],
            nonce_bits: vec![None; NUM_NONCE_BITS],
        };

        let circuit = CubeDemo::<Scalar> {
            CID: None,
            preimage: preimage,
            VacCnt: None,
        };


        generate_random_parameters::<Bls12, _, _>(circuit, &mut rng).unwrap()
    };

    // Prepare the verification key (for proof verification)
    let pvk = prepare_verifying_key(&params.vk);
    
    println!("Creating proofs...");

    let mut hash_bits = user_id_bits;
    hash_bits.extend(secret_bits);
    hash_bits.extend(nonce_bits);

    // Create an instance of circuit
    let preimage = CIDPreimage {
        user_id_bits: vec![None; NUM_USER_ID_BITS],
        secret_bits: vec![None; NUM_SECRET_BITS],
        nonce_bits: vec![None; NUM_NONCE_BITS],
    };

    let circuit = CubeDemo::<Scalar> {
        CID: None,
        preimage: preimage,
        VacCnt: Some(Fr::from_str_vartime("4")),
    };

    // Create a groth16 proof with our parameters.
    let proof = create_random_proof(circuit, &params, &mut rng).unwrap();

    let proof_a_affine = proof.a.to_uncompressed();
    // println!("proofaaffine: {:?}", proof_a_affine);

    let proof_b_affine = proof.b.to_uncompressed();
    // println!("proofabffine: {:?}", proof_b_affine);

    let proof_c_affine = proof.c.to_uncompressed();
    // println!("proofacffine: {:?}", proof_c_affine);

    // println!(r#"{{"pi_a":{:?},"pi_b":{:?},"pi_c":{:?}}}"#, proof_a_affine, proof_b_affine, proof_c_affine);
    let res_proof = format!(r#"{{"pi_a":{:?},"pi_b":{:?},"pi_c":{:?}}}"#, proof_a_affine, proof_b_affine, proof_c_affine);
    let res_vkey = format!(r#"{{"alpha_1":{:?},"beta_1":{:?},"beta_2":{:?},"gamma_2":{:?},"delta_1":{:?},"delta_2":{:?},"ic":[{:?},{:?}]}}"#, params.vk.alpha_g1.to_uncompressed(), params.vk.beta_g1.to_uncompressed(), params.vk.beta_g2.to_uncompressed(), params.vk.gamma_g2.to_uncompressed(), params.vk.delta_g1.to_uncompressed(), params.vk.delta_g2.to_uncompressed(), params.vk.ic[0].to_uncompressed(), params.vk.ic[1].to_uncompressed());
    encode::create_uncompressed_file(res_proof, res_vkey);
    encode::encode_uncompressed();

    assert!(verify_proof(
        &pvk,
        &proof,
        &[Fr::from_str_vartime("35").unwrap()]
    ).is_ok());
}
