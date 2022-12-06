#![allow(unused_imports)]
#![allow(unused_variables)]
use std::hash;

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
    pub name_and_birth: Option<S>,
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

        // Allocate the first component of the preimage (id).
        let mut xl_value = self.id;
        let mut xl = cs.alloc(
            || "preimage xl",
            || xl_value.ok_or(SynthesisError::AssignmentMissing),
        )?;

        // Allocate the second component of the preimage (secret).
        let mut xr_value = self.secret;
        let mut xr = cs.alloc(
            || "preimage xr",
            || xr_value.ok_or(SynthesisError::AssignmentMissing),
        )?;

        let mut hashed_number_val1 = None;
        let mut hashed_number1;

        // hash(id, secret)
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

            // save hashed number
            if(i == (MIMC_ROUNDS - 1)) {
                hashed_number_val1 = new_xl_value;
                hashed_number1 = new_xl;
            }
        }

        // Allocate the first component of the preimage (image1).
        let mut xl_value = hashed_number_val1;
        let mut xl = cs.alloc(
            || "preimage xl",
            || xl_value.ok_or(SynthesisError::AssignmentMissing),
        )?;

        // Allocate the second component of the preimage (nonce).
        let mut xr_value = self.name_and_birth;
        let mut xr = cs.alloc_input(
            || "preimage xr",
            || xr_value.ok_or(SynthesisError::AssignmentMissing),
        )?;

        let mut hashed_number_val2 = None;
        let mut hashed_number2;

        // hash(image1, nonce)
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


            // save hashed number
            if(i == (MIMC_ROUNDS - 1)) {
                hashed_number_val2 = new_xl_value;
                hashed_number2 = new_xl;
            }
        }

        // Allocate the first component of the preimage (image2).
        let mut xl_value = hashed_number_val2;
        let mut xl = cs.alloc(
            || "preimage xl",
            || xl_value.ok_or(SynthesisError::AssignmentMissing),
        )?;

        // Allocate the second component of the preimage (name and birth).
        let mut xr_value = self.nonce;
        let mut xr = cs.alloc(
            || "preimage xr",
            || xr_value.ok_or(SynthesisError::AssignmentMissing),
        )?;

        // Allocate the first component of the preimage (image2).
        let  out_val = self.image;
        let out = cs.alloc_input(
            || "output image",
            || out_val.ok_or(SynthesisError::AssignmentMissing),
        )?;

        // hash(image1, nonce)
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
                    |lc| lc + out,
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
    let res_vkey = format!(r#"{{"alpha_1":{:?},"beta_1":{:?},"beta_2":{:?},"gamma_2":{:?},"delta_1":{:?},"delta_2":{:?},"ic":[{:?},{:?},{:?}]}}"#, params.vk.alpha_g1.to_uncompressed(), params.vk.beta_g1.to_uncompressed(), params.vk.beta_g2.to_uncompressed(), params.vk.gamma_g2.to_uncompressed(), params.vk.delta_g1.to_uncompressed(), params.vk.delta_g2.to_uncompressed(), params.vk.ic[0].to_uncompressed(), params.vk.ic[1].to_uncompressed(), params.vk.ic[2].to_uncompressed());
    println!("vkey_id: {:?}", params.vk.ic[2].to_uncompressed());
    encode::create_uncompressed_file(res_proof, res_vkey);
    encode::encode_uncompressed_2inputs();
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

    // let user_id = 291159717780246467128751248815521818849;
    // let secret = 185286;
    // let nonce = 175227135210;
    let id = ff::PrimeField::from_str_vartime("291159717780246467128751248815521818849").unwrap();
    let secret = ff::PrimeField::from_str_vartime("185286").unwrap();
    let nonce = ff::PrimeField::from_str_vartime("175227135210").unwrap();
    let name = ff::PrimeField::from_str_vartime("107111121971099797116115117107105").unwrap();
    let birth = ff::PrimeField::from_str_vartime("320516").unwrap();

    let name_and_birth = mimc(name, birth, &constants);
    let name_and_birth_repr = name_and_birth.to_repr();
    // println!("hashed name and birth: {:?}", name_and_birth);
    let res_name_and_birth = format!("{}{}", "0x", encode::encode_hex(&name_and_birth_repr));
    println!("repr_name_and_birth_hex: {:?}", res_name_and_birth);

    let image1 = mimc(id, secret, &constants);
    let image2 = mimc(image1, name_and_birth, &constants);
    let image3 = mimc(image2, nonce, &constants);
    let image3_repr = image3.to_repr();
    let res_image3 = format!("{}{}", "0x", encode::encode_hex(&image3_repr));
    println!("repr_image_hex: {:?}", res_image3);

    // Create parameters for our circuit
     // Create parameters for our circuit
     let params = {

        let circuit = VacPassDemo::<Scalar> {
            id: None,
            secret: None,
            nonce: None,
            name_and_birth: None,
            constants: &constants,
            image: None,
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
        name_and_birth: Some(name_and_birth),
        constants: &constants,
        image: Some(image3),
    };

    // Create a groth16 proof with our parameters.
    let proof = create_random_proof(circuit, &params, &mut rng).unwrap();

    encode_adapter(proof.clone(), params.clone());

    assert!(verify_proof(
        &pvk,
        &proof,
        &[name_and_birth, image3]
    ).is_ok());
}
