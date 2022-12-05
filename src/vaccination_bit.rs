#![allow(unused_imports)]
#![allow(unused_variables)]
use bellman::gadgets::{boolean, sha256, num, Assignment};
use bls12_381::{Bls12, Scalar};
use crypto::digest::Digest;
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
pub struct CIDPreimage<E: Fr> {
    pub user_id_bits: Option<E>,
    pub secret_bits: Option<E>,
    pub nonce_bits: Option<E>,
}


// proving that I know x such that x^3 + x + 5 == 35
// Generalized: x^3 + x + 5 == out
#[allow(clippy::upper_case_acronyms)]
pub struct VacPassDemo<E: Fr> {
    pub CID: Option<E>,
    pub preimage: CIDPreimage<E>,
}

impl<E: Fr> Clone for VacPassDemo<E> {
    fn clone(&self) -> Self {
        VacPassDemo {
            CID: self.CID.clone(),
            preimage: self.preimage.clone(),
        }
    }
}

const NUM_USER_ID_BITS: usize = 128;

impl <E: Fr + ff::PrimeFieldBits> Circuit<E> for VacPassDemo<E> {
    fn synthesize<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS
    ) -> Result<(), SynthesisError>
    {
        let CID = num::AllocatedNum::alloc(
            cs.namespace(|| "CID image"),
            || {
                let value = self.CID;
                Ok(*value.get()?)
            }
        )?;
        CID.inputize(cs.namespace(|| "CID"))?;
        

        // let mut user_id_bool = Vec::<boolean::Boolean>::with_capacity(NUM_USER_ID_BITS);
        // Allocate bits for use of making CID
        let mut user_id_bits = match self.preimage.user_id_bits {
            Some(_) => boolean::field_into_boolean_vec_le(
                cs.namespace(|| "field into bits"),
                self.preimage.user_id_bits,
            )?,
            _ => boolean::field_into_boolean_vec_le(
                cs.namespace(|| "field into bits"),
                Some(E::zero()),
            )?,
        };

        // let mut user_id_bool = Vec::<boolean::Boolean>::with_capacity(NUM_USER_ID_BITS);
        // Allocate bits for use of making CID
        let secret_bits = match self.preimage.secret_bits {
            Some(_) => boolean::field_into_boolean_vec_le(
                cs.namespace(|| "field into bits"),
                self.preimage.secret_bits,
            )?,
            _ => boolean::field_into_boolean_vec_le(
                cs.namespace(|| "field into bits"),
                Some(E::zero()),
            )?,
        };

        let nonce_bits = match self.preimage.nonce_bits {
            Some(_) => boolean::field_into_boolean_vec_le(
                cs.namespace(|| "field into bits"),
                self.preimage.nonce_bits,
            )?,
            _ => boolean::field_into_boolean_vec_le(
                cs.namespace(|| "field into bits"),
                Some(E::zero()),
            )?,
        };

        user_id_bits.extend(secret_bits);
        user_id_bits.extend(nonce_bits);
        println!("user_id_len: {:?}", user_id_bits.len());
        if user_id_bits.len() % 8 != 0 {
            let n = 8 - user_id_bits.len() % 8;
            for i in 0..n {
                let bit = boolean::Boolean::from(boolean::AllocatedBit::alloc(
                    cs.namespace(|| format!("allocating extra bit {}", i)),
                    Some(true)
                    )?
                );
                user_id_bits.push(bit);
            }
        }

        println!("user_id_len: {:?}", user_id_bits.len());

        let mut hash = sha256::sha256(
            cs.namespace(|| "calculate old state hash"),
            &user_id_bits
        )?;

        hash.reverse();
        hash.truncate(E::CAPACITY as usize);

        let mut packed_hash_lc = num::Num::<E>::zero();
        let mut coeff = E::one();
        for bit in hash {
            packed_hash_lc = packed_hash_lc.add_bool_with_coeff(CS::one(), &bit, coeff);
            coeff = coeff.double();
        }

        cs.enforce(
            || "enforce hash",
            |lc| lc + CID.get_variable(),
            |lc| lc + CS::one(),
            |_| packed_hash_lc.lc(E::one()),
        );

        Ok(())
    }
}

#[test]
fn test_cube_proof(){
    use crypto::sha2::Sha256;
    use crate::encode_bit::encode_bit;

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
            user_id_bits: None,
            secret_bits: None,
            nonce_bits: None,
        };

        let circuit = VacPassDemo::<Scalar> {
            CID: None,
            preimage: preimage,
        };


        generate_random_parameters::<Bls12, _, _>(circuit, &mut rng).unwrap()
    };

    // Prepare the verification key (for proof verification)
    let pvk = prepare_verifying_key(&params.vk);
    
    println!("Creating proofs...");


    let id = ff::PrimeField::from_str_vartime("291159717780246467128751248815521818849");
    let secret = ff::PrimeField::from_str_vartime("185286120");
    let nonce = ff::PrimeField::from_str_vartime("175227135210");

    let mut hash_result = encode_bit();

    let mut repr = Scalar::zero().into_repr();
        repr.read_be(&hash_result[..]).expect("pack hash as field element");
        let current_account_state = Fr::from_repr(repr).expect("must be a valud representation");

    // Create an instance of circuit
    let preimage = CIDPreimage::<Scalar> {
        user_id_bits: id,
        secret_bits: secret,
        nonce_bits: nonce,
    };

    let circuit = VacPassDemo::<Scalar> {
        CID: ,
        preimage: preimage,
    };

    // Create a groth16 proof with our parameters.
    let proof = create_random_proof(circuit, &params, &mut rng).unwrap();

    // let proof_a_affine = proof.a.to_uncompressed();
    // // println!("proofaaffine: {:?}", proof_a_affine);

    // let proof_b_affine = proof.b.to_uncompressed();
    // // println!("proofabffine: {:?}", proof_b_affine);

    // let proof_c_affine = proof.c.to_uncompressed();
    // // println!("proofacffine: {:?}", proof_c_affine);

    // // println!(r#"{{"pi_a":{:?},"pi_b":{:?},"pi_c":{:?}}}"#, proof_a_affine, proof_b_affine, proof_c_affine);
    // let res_proof = format!(r#"{{"pi_a":{:?},"pi_b":{:?},"pi_c":{:?}}}"#, proof_a_affine, proof_b_affine, proof_c_affine);
    // let res_vkey = format!(r#"{{"alpha_1":{:?},"beta_1":{:?},"beta_2":{:?},"gamma_2":{:?},"delta_1":{:?},"delta_2":{:?},"ic":[{:?},{:?}]}}"#, params.vk.alpha_g1.to_uncompressed(), params.vk.beta_g1.to_uncompressed(), params.vk.beta_g2.to_uncompressed(), params.vk.gamma_g2.to_uncompressed(), params.vk.delta_g1.to_uncompressed(), params.vk.delta_g2.to_uncompressed(), params.vk.ic[0].to_uncompressed(), params.vk.ic[1].to_uncompressed());
    // encode::create_uncompressed_file(res_proof, res_vkey);
    // encode::encode_uncompressed();

    assert!(verify_proof(
        &pvk,
        &proof,
        &[Fr::from_str_vartime("35").unwrap()]
    ).is_ok());
}
