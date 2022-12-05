#![allow(unused_imports)]
#![allow(unused_variables)]
use std::hash;

use bellman::gadgets::Assignment;
use bellman::gadgets::boolean;
use bellman::groth16::Parameters;
use bls12_381::{Bls12, Scalar};
// For randomness (during paramgen and proof generation)
use rand::{thread_rng, Rng};
use ff::PrimeField as Fr;
use ff::Field;

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

pub const MIMC_ROUNDS: usize = 322;

pub fn mimc<S: ff::PrimeField>(mut xl: S, mut xr: S, constants: &[S]) -> S {
    assert_eq!(constants.len(), MIMC_ROUNDS);

    for c in constants {
        let mut tmp1 = xl;
        tmp1.add_assign(c);
        let mut tmp2 = tmp1.square();
        tmp2.mul_assign(&tmp1);
        tmp2.add_assign(&xr);
        xr = xl;
        xl = tmp2;
    }

    xl
}


pub struct VacPassDemo<'a, S: Fr> {
    pub id: Option<S>,
    pub secret: Option<S>,
    pub nonce: Option<S>,
    pub constants: &'a [S],
    pub image: Option<S>,
}

const NUM_USER_ID_BITS: usize = 128;

impl <'a, E: Fr> Circuit<E> for VacPassDemo<'a, E> {
    fn synthesize<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS
    ) -> Result<(), SynthesisError>
    {
        assert_eq!(self.constants.len(), MIMC_ROUNDS);

        // Allocate the first component of the preimage.
        let mut xl_value = self.id;
        let mut xl = cs.alloc_input(
            || "preimage xl",
            || xl_value.ok_or(SynthesisError::AssignmentMissing),
        )?;

        // Allocate the second component of the preimage.
        let mut xr_value = self.secret;
        let mut xr = cs.alloc(
            || "preimage xr",
            || xr_value.ok_or(SynthesisError::AssignmentMissing),
        )?;
        let a = xr_value.get();
        if let Ok(s) = a {
            
        }

        let mut hashed_number_val = None;
        let mut hashed_number;

        for i in 0..MIMC_ROUNDS {
            // xL, xR := xR + (xL + Ci)^3, xL
            let cs = &mut cs.namespace(|| format!("round {}", i));

            // tmp = (xL + Ci)^2
            let tmp_value = xl_value.map(|mut e| {
                e.add_assign(&self.constants[i]);
                e.square()
            });
            let tmp = cs.alloc(
                || "tmp",
                || tmp_value.ok_or(SynthesisError::AssignmentMissing),
            )?;

            cs.enforce(
                || "tmp = (xL + Ci)^2",
                |lc| lc + xl + (self.constants[i], CS::one()),
                |lc| lc + xl + (self.constants[i], CS::one()),
                |lc| lc + tmp,
            );

            // new_xL = xR + (xL + Ci)^3
            // new_xL = xR + tmp * (xL + Ci)
            // new_xL - xR = tmp * (xL + Ci)
            let new_xl_value = xl_value.map(|mut e| {
                e.add_assign(&self.constants[i]);
                e.mul_assign(&tmp_value.unwrap());
                e.add_assign(&xr_value.unwrap());
                e
            });

            let new_xl = if i == (MIMC_ROUNDS - 1) {
                // This is the last round, xL is our image and so
                // we allocate a public input.
                cs.alloc(
                    || "image",
                    || new_xl_value.ok_or(SynthesisError::AssignmentMissing),
                )?
                
            } else {
                cs.alloc(
                    || "new_xl",
                    || new_xl_value.ok_or(SynthesisError::AssignmentMissing),
                )?
            };

            cs.enforce(
                || "new_xL = xR + (xL + Ci)^3",
                |lc| lc + tmp,
                |lc| lc + xl + (self.constants[i], CS::one()),
                |lc| lc + new_xl - xr,
            );

            // xR = xL
            xr = xl;
            xr_value = xl_value;

            // xL = new_xL
            xl = new_xl;
            xl_value = new_xl_value;

            if(i == (MIMC_ROUNDS - 1)) {
                hashed_number_val = new_xl_value;
                hashed_number = new_xl;
            }
        }

        // Allocate the first component of the preimage.
        let mut xl_value = hashed_number_val;
        let mut xl = cs.alloc(
            || "preimage xl",
            || xl_value.ok_or(SynthesisError::AssignmentMissing),
        )?;

        // Allocate the second component of the preimage.
        let mut xr_value = self.nonce;
        let mut xr = cs.alloc(
            || "preimage xr",
            || xr_value.ok_or(SynthesisError::AssignmentMissing),
        )?;

        for i in 0..MIMC_ROUNDS {
            // xL, xR := xR + (xL + Ci)^3, xL
            let cs = &mut cs.namespace(|| format!("round {}", i));

            // tmp = (xL + Ci)^2
            let tmp_value = xl_value.map(|mut e| {
                e.add_assign(&self.constants[i]);
                e.square()
            });
            let tmp = cs.alloc(
                || "tmp",
                || tmp_value.ok_or(SynthesisError::AssignmentMissing),
            )?;

            cs.enforce(
                || "tmp = (xL + Ci)^2",
                |lc| lc + xl + (self.constants[i], CS::one()),
                |lc| lc + xl + (self.constants[i], CS::one()),
                |lc| lc + tmp,
            );

            // new_xL = xR + (xL + Ci)^3
            // new_xL = xR + tmp * (xL + Ci)
            // new_xL - xR = tmp * (xL + Ci)
            let new_xl_value = xl_value.map(|mut e| {
                e.add_assign(&self.constants[i]);
                e.mul_assign(&tmp_value.unwrap());
                e.add_assign(&xr_value.unwrap());
                e
            });

            let new_xl = if i == (MIMC_ROUNDS - 1) {
                // This is the last round, xL is our image and so
                // we allocate a public input.
                cs.alloc(
                    || "image",
                    || new_xl_value.ok_or(SynthesisError::AssignmentMissing),
                )?
                
            } else {
                cs.alloc(
                    || "new_xl",
                    || new_xl_value.ok_or(SynthesisError::AssignmentMissing),
                )?
            };

            cs.enforce(
                || "new_xL = xR + (xL + Ci)^3",
                |lc| lc + tmp,
                |lc| lc + xl + (self.constants[i], CS::one()),
                |lc| lc + new_xl - xr,
            );

            // xR = xL
            xr = xl;
            xr_value = xl_value;

            // xL = new_xL
            xl = new_xl;
            xl_value = new_xl_value;


            if(i == (MIMC_ROUNDS - 1)) {
                cs.enforce(
                    || "new_xL = secret",
                    |lc| lc + (self.image.unwrap(), CS::one()),
                    |lc| lc + CS::one(),
                    |lc| lc + new_xl,
                );
            }
        }

        Ok(())
    }
}

fn encode_adapter(proof: Proof<Bls12>, params: Parameters<Bls12>) {
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
}

#[test]
fn test_cube_proof(){
    // This may not be cryptographically safe, use
    // `OsRng` (for example) in production software.
    let mut rng = thread_rng();

    // Generate the MiMC round constants
    let constants = (0..MIMC_ROUNDS)
        .map(|_| Scalar::random(&mut rng))
        .collect::<Vec<_>>();

    println!("Creating parameters...");

    let xl_str = "291159717780246467128751248815521818849185286175227135210";
    let xr_str = "15521818849185286175227135210";
    let xl = Scalar::from_str_vartime(xl_str).unwrap();
    let xr = Scalar::from_str_vartime(xr_str).unwrap();

    // let user_id = 291159717780246467128751248815521818849;
    // let secret = 185286;
    // let nonce = 175227135210;
    let id = ff::PrimeField::from_str_vartime("291159717780246467128751248815521818849").unwrap();
    let secret = ff::PrimeField::from_str_vartime("185286").unwrap();
    let nonce = ff::PrimeField::from_str_vartime("175227135210").unwrap();
    let image1 = mimc(id, secret, &constants);
    let image2 = mimc(image1, nonce, &constants);
    // let image2 = ff::PrimeField::from_str_vartime("123").unwrap();
    println!("image: {:?}", image2);

    // Create parameters for our circuit
     // Create parameters for our circuit
     let params = {

        let circuit = VacPassDemo::<Scalar> {
            id: None,
            secret: None,
            nonce: None,
            constants: &constants,
            image: Some(image2),
        };


        generate_random_parameters::<Bls12, _, _>(circuit, &mut rng).unwrap()
    };

    // Prepare the verification key (for proof verification)
    let pvk = prepare_verifying_key(&params.vk);
    
    println!("Creating proofs...");


    let circuit = VacPassDemo::<Scalar> {
        id: Some(id),
        secret: Some(secret),
        nonce: Some(nonce),
        constants: &constants,
        image: Some(image2),
    };

    // Create a groth16 proof with our parameters.
    let proof = create_random_proof(circuit, &params, &mut rng).unwrap();

    encode_adapter(proof.clone(), params.clone());

    assert!(verify_proof(
        &pvk,
        &proof,
        &[id]
    ).is_ok());
}
