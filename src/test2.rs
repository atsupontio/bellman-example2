use sapling_crypto_ce::circuit::boolean::Boolean;
use sapling_crypto_ce::jubjub::{
    edwards,
    JubjubEngine,
    JubjubParams,
    FixedGenerators
};

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

use sapling_crypto_ce::eddsa::{PrivateKey, PublicKey, Signature};
use sapling_crypto_ce::circuit::{ecc::EdwardsPoint, num::AllocatedNum, baby_eddsa, boolean::AllocatedBit};
use sapling_crypto_ce::alt_babyjubjub::{ AltJubjubBn256};
use sapling_crypto_ce::circuit::baby_eddsa::EddsaSignature;

pub struct EddsaSignatureDemo<'a, E: JubjubEngine> {
    pub private_key: Option<PrivateKey<E>>,
    pub public_key: Option<PublicKey<E>>,
    pub r: Option<EdwardsPoint<E>>,
    pub s: Option<AllocatedNum<E>>,
    pub pk: Option<EdwardsPoint<E>>,
    pub generator: Option<EdwardsPoint<E>>,
    pub inputs_bool: Option<Vec<Boolean>>,
    pub params: Option<&'a E::Params>,
}


impl <'a, E: JubjubEngine> Circuit<E> for EddsaSignatureDemo<'a, E> {
    fn synthesize<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS
    ) -> Result<(), SynthesisError>
    {

        let r = self.r.unwrap();
        let s = self.s.unwrap();
        let pk = self.pk.unwrap();
        let generator = self.generator.unwrap();
        let message = self.inputs_bool.unwrap();
        let params = self.params.unwrap();

        let signature = EddsaSignature{r, s, pk};

        let value = signature.verify_schnorr_blake2s(
            cs.namespace(|| "verify signature"),
            params,
            &message,
            generator
        );

        Ok(())
    }
}


#[cfg(test)]
mod test {
    use bellman::domain::Point;
    use sapling_crypto_ce::circuit::ecc::EdwardsPoint;
    use sapling_crypto_ce::circuit::baby_eddsa::EddsaSignature;
    use sapling_crypto_ce::circuit::num::AllocatedNum;
    use sapling_crypto_ce::eddsa::{PrivateKey, PublicKey};
    use rand::{SeedableRng, Rng, XorShiftRng};
    use super::*;
    use sapling_crypto_ce::circuit::test::*;
    use sapling_crypto_ce::circuit::boolean::{Boolean, AllocatedBit};
    use bellman::pairing::bn256::{Bn256, Fr};
    use bellman::pairing::ff::{PrimeField, PrimeFieldRepr};
    use sapling_crypto_ce::alt_babyjubjub::AltJubjubBn256;
    use sapling_crypto_ce::alt_babyjubjub::fs::Fs;
    use sapling_crypto_ce::babyjubjub::JubjubBn256;

    use sapling_crypto_ce::circuit::test::TestConstraintSystem;

    use bellman::{
        SynthesisError,
        ConstraintSystem
    };
    
    
    #[test]
    fn test_schnorr_signatures() {
        
        let mut rng = XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
        let p_g = FixedGenerators::SpendingKeyGenerator;
        let params = &AltJubjubBn256::new();
        // let params = &JubjubBn256::new();
        let mut cs = EddsaSignatureDemo::<Bn256> {
            private_key: None,
            public_key: None,
            r: None, 
            s: None,
            pk: None,
            generator: None,
            inputs_bool: None,
            params: None,
        };
        let sk = PrivateKey::<Bn256>(rng.gen());
        let vk = PublicKey::from_private(&sk, p_g, params);

        let msg1 = b"Foo bar pad to16"; // 16 bytes

        let mut input: Vec<bool> = vec![];

        for b in msg1.iter() {  
            for i in (0..8).into_iter() {
                if (b & (1 << i)) != 0 {
                    input.extend(&[true; 1]);
                } else {
                    input.extend(&[false; 1]);
                }
            }
        }

        let sig1 = sk.sign_schnorr_blake2s(msg1, &mut rng, p_g, params);
        assert!(vk.verify_schnorr_blake2s(msg1, &sig1, p_g, params));

        let input_bools: Vec<Boolean> = input.iter().enumerate().map(|(i, b)| {
            Boolean::from(
                AllocatedBit::alloc(cs.namespace(|| format!("input {}", i)), Some(*b)).unwrap()
            )
        }).collect();

        let mut sigs_bytes = [0u8; 32];
        sig1.s.into_repr().write_le(& mut sigs_bytes[..]).expect("get LE bytes of signature S");
        let mut sigs_repr = <Fr as PrimeField>::Repr::from(0);
        sigs_repr.read_le(&sigs_bytes[..]).expect("interpret S as field element representation");

        let sigs_converted = Fr::from_repr(sigs_repr).unwrap();

        let s = AllocatedNum::alloc(cs.namespace(|| "allocate s"), || {
                Ok(sigs_converted)
            }
        ).unwrap();

        // let params = &JubjubBn256::new();

        let public_generator = params.generator(FixedGenerators::SpendingKeyGenerator).clone();

        let generator = EdwardsPoint::witness(cs.namespace(|| "allocate public generator"), Some(public_generator), params).unwrap();

        let r = EdwardsPoint::witness(cs.namespace(|| "allocate r"), Some(sig1.r), params).unwrap();

        let pk = EdwardsPoint::witness(cs.namespace(|| "allocate pk"), Some(vk.0), params).unwrap();

        // let signature = EddsaSignature{r, s, pk};
        // signature.verify_schnorr_blake2s(cs.namespace(|| "verify signature"), params, &input_bools, generator).expect("succesfully generated verifying gadget");

        // Create parameters for our circuit
        let proof_params = {
            let c = EddsaSignatureDemo::<Bn256> {
                private_key: None,
                public_key: None,
                r: None, 
                s: None,
                pk: None,
                generator: None,
                inputs_bool: None,
                params: None,
            };

            generate_random_parameters::<Bn256, _, _>(c, &mut rng).unwrap()
        };

        // Prepare the verification key (for proof verification)
        let pvk = prepare_verifying_key(&proof_params.vk);


        let vk1 = PublicKey::from_private(&sk, p_g, params);
            // Create an instance of circuit
        let c = EddsaSignatureDemo::<Bn256> {
            private_key: Some(sk),
            public_key: Some(vk1),
            r: Some(r),
            s: Some(s),
            pk: Some(pk),
            generator: Some(generator),
            inputs_bool: Some(input_bools),
            params: Some(params),
        };

        // Create a groth16 proof with our parameters.
        let proof = create_random_proof(c, &proof_params, &mut rng).unwrap();

        assert!(verify_proof(
            &pvk,
            &proof,
            &[]
        ).is_ok());

        assert!(cs.is_satisfied());
        print!("Schnorr signature verification takes constraints: {}\n", cs.num_constraints());
    }

    #[test]
    fn test_valid_musig_signatures() {
        
        let mut rng = XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
        let p_g = FixedGenerators::SpendingKeyGenerator;
        let params = &AltJubjubBn256::new();
        let mut cs = TestConstraintSystem::<Bn256>::new();
        let sk = PrivateKey::<Bn256>(rng.gen());
        let vk = PublicKey::from_private(&sk, p_g, params);

        let msg1 = b"Foo bar pad to16".to_vec(); // 16 bytes

        let mut input: Vec<bool> = vec![];

        for input_byte in msg1.iter() {
            for bit_i in (0..8).rev() {
                input.push((input_byte >> bit_i) & 1u8 == 1u8);
            }
        }

        let sig1 = sk.musig_sha256_sign(&msg1[..], &mut rng, p_g, params);
        assert!(vk.verify_musig_sha256(&msg1[..], &sig1, p_g, params));

        let input_bools: Vec<Boolean> = input.iter().enumerate().map(|(i, b)| {
            Boolean::from(
                AllocatedBit::alloc(cs.namespace(|| format!("input {}", i)), Some(*b)).unwrap()
            )
        }).collect();

        let mut sigs_bytes = [0u8; 32];
        sig1.s.into_repr().write_le(& mut sigs_bytes[..]).expect("get LE bytes of signature S");
        let mut sigs_repr = <Fr as PrimeField>::Repr::from(0);
        sigs_repr.read_le(&sigs_bytes[..]).expect("interpret S as field element representation");

        let sigs_converted = Fr::from_repr(sigs_repr).unwrap();

        let s = AllocatedNum::alloc(cs.namespace(|| "allocate s"), || {
                Ok(sigs_converted)
            }
        ).unwrap();

        let public_generator = params.generator(FixedGenerators::SpendingKeyGenerator).clone();

        let generator = EdwardsPoint::witness(cs.namespace(|| "allocate public generator"), Some(public_generator), params).unwrap();

        let r = EdwardsPoint::witness(cs.namespace(|| "allocate r"), Some(sig1.r), params).unwrap();

        let pk = EdwardsPoint::witness(cs.namespace(|| "allocate pk"), Some(vk.0), params).unwrap();

        let signature = EddsaSignature{r, s, pk};

        signature.verify_sha256_musig(
            cs.namespace(|| "verify signature"), 
            params, 
            &input_bools, 
            generator).expect("succesfully generated verifying gadget");

        assert!(cs.is_satisfied());
        print!("MuSig verification without message hashing takes constraints: {}\n", cs.num_constraints());
    }

    #[test]
    fn test_valid_raw_message_signatures() {
        let mut rng = XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
        let p_g = FixedGenerators::SpendingKeyGenerator;
        let params = &AltJubjubBn256::new();
        let mut cs = TestConstraintSystem::<Bn256>::new();
        let sk = PrivateKey::<Bn256>(rng.gen());
        let vk = PublicKey::from_private(&sk, p_g, params);

        let msg1 = b"Foo bar pad to16"; // 16 bytes

        let mut input: Vec<bool> = vec![];

        for b in msg1.iter() {  
            for i in (0..8).into_iter() {
                if (b & (1 << i)) != 0 {
                    input.extend(&[true; 1]);
                } else {
                    input.extend(&[false; 1]);
                }
            }
        }

        // test for maximum message length of 16 bytes
        let sig1 = sk.sign_raw_message(msg1, &mut rng, p_g, params, 16);
        assert!(vk.verify_for_raw_message(msg1, &sig1, p_g, params, 16));

        let input_bools: Vec<Boolean> = input.iter().enumerate().map(|(i, b)| {
            Boolean::from(
                AllocatedBit::alloc(cs.namespace(|| format!("input {}", i)), Some(*b)).unwrap()
            )
        }).collect();

        let mut sigs_bytes = [0u8; 32];
        sig1.s.into_repr().write_le(& mut sigs_bytes[..]).expect("get LE bytes of signature S");
        let mut sigs_repr = <Fr as PrimeField>::Repr::from(0);
        sigs_repr.read_le(&sigs_bytes[..]).expect("interpret S as field element representation");

        let sigs_converted = Fr::from_repr(sigs_repr).unwrap();

        let s = AllocatedNum::alloc(cs.namespace(|| "allocate s"), || {
                Ok(sigs_converted)
            }
        ).unwrap();

        let public_generator = params.generator(FixedGenerators::SpendingKeyGenerator).clone();

        let generator = EdwardsPoint::witness(cs.namespace(|| "allocate public generator"), Some(public_generator), params).unwrap();

        let r = EdwardsPoint::witness(cs.namespace(|| "allocate r"), Some(sig1.r), params).unwrap();

        let pk = EdwardsPoint::witness(cs.namespace(|| "allocate pk"), Some(vk.0), params).unwrap();

        let signature = EddsaSignature{r, s, pk};
        signature.verify_raw_message_signature(cs.namespace(|| "verify signature"), params, &input_bools, generator, 16).expect("succesfully generated verifying gadget");

        assert!(cs.is_satisfied());
        print!("EdDSA variant raw message signature takes constraints: {}\n", cs.num_constraints());
    }

}
