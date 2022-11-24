
use bellman::pairing::bn256::{Bn256, Fr};
use bellman::pairing::{Engine, RawEncodable, EncodedPoint};
// For randomness (during paramgen and proof generation)
use rand::{thread_rng, Rng, XorShiftRng, SeedableRng};
use bellman::pairing::ff::{PrimeField, ScalarEngine, Field, PrimeFieldRepr};
use bellman::pairing::CurveAffine;

use sapling_crypto_ce::circuit::boolean::Boolean;
use sapling_crypto_ce::jubjub::{JubjubEngine, JubjubParams, FixedGenerators};

use sapling_crypto_ce::circuit::{ecc::EdwardsPoint, num::AllocatedNum, baby_eddsa, boolean::AllocatedBit};

use sapling_crypto_ce::circuit::baby_eddsa::EddsaSignature;
use sapling_crypto_ce::circuit::test::TestConstraintSystem;

use sapling_crypto_ce::alt_babyjubjub::{self, AltJubjubBn256};

use sapling_crypto_ce::eddsa::{PrivateKey, PublicKey, Signature};


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

pub struct EddsaSignatureDemo<'a, E: JubjubEngine> {
    pub private_key: Option<PrivateKey<E>>,
    pub public_key: Option<PublicKey<E>>,
    pub msg: Option<Vec<u8>>,
    pub sig: Option<Signature<E>>,
    pub params: &'a E::Params,
    pub input: Option<Vec<bool>>,
}

// impl<E: JubjubEngine> EddsaSignatureDemo<E> {
//     pub fn new() -> EddsaSignatureDemo<E> {
//         let mut map = HashMap::new();
//         map.insert("ONE".into(), NamedObject::Var(TestConstraintSystem::<E>::one()));

//         EddsaSignatureDemo { signature: (), input: (), params: () }
//     }
// }

impl <'a, E: JubjubEngine> Circuit<E> for EddsaSignatureDemo<'a, E> {
    fn synthesize<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS
    ) -> Result<(), SynthesisError>
    {

        let input_bools: Vec<Boolean> = self.input.unwrap().iter().enumerate().map(|(i, b)| {
            Boolean::from(
                AllocatedBit::alloc(cs.namespace(|| format!("input {}", i)), Some(*b)).unwrap()
            )
        }).collect();

        let mut sigs_bytes = [0u8; 32];
        self.sig.clone().unwrap().s.into_repr().write_le(& mut sigs_bytes[..]).expect("get LE bytes of signature S");
        let mut sigs_repr = <E::Fr as PrimeField>::Repr::from(0);
        sigs_repr.read_le(&sigs_bytes[..]).expect("interpret S as field element representation");

        let sigs_converted = <E::Fr as PrimeField>::from_repr(sigs_repr).unwrap();

        let s = AllocatedNum::alloc(cs.namespace(|| "allocate s"), || {
                Ok(sigs_converted)
            }
        ).unwrap();

        let params = self.params;

        let public_generator = params.generator(FixedGenerators::SpendingKeyGenerator).clone();

        let generator = EdwardsPoint::witness(cs.namespace(|| "allocate public generator"), Some(public_generator), params).unwrap();

        let r = EdwardsPoint::witness(cs.namespace(|| "allocate r"), Some(self.sig.unwrap().r), params).unwrap();

        let pk = EdwardsPoint::witness(cs.namespace(|| "allocate pk"), Some(self.public_key.unwrap().0), params).unwrap();

        let signature = EddsaSignature{r, s, pk};

        let value = signature.verify_schnorr_blake2s(
            cs.namespace(|| "value"),
            params,
            &input_bools,
            generator
        ).expect("succesfully generated verifying gadget");

        Ok(())
    }
}

#[test]
fn test_cube_proof(){
    // This may not be cryptographically safe, use
    // `OsRng` (for example) in production software.
    // let mut rng = thread_rng();

    println!("Creating parameters...");

    let mut rng = XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
    let test_params = &AltJubjubBn256::new();
        let p_g = FixedGenerators::SpendingKeyGenerator;
        let params = &AltJubjubBn256::new();
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

        let mut sigs_bytes = [0u8; 32];
        sig1.s.into_repr().write_le(& mut sigs_bytes[..]).expect("get LE bytes of signature S");
        let mut sigs_repr = <Fr as PrimeField>::Repr::from(0);
        sigs_repr.read_le(&sigs_bytes[..]).expect("interpret S as field element representation");

        let sigs_converted = Fr::from_repr(sigs_repr).unwrap();

    // Create parameters for our circuit
    let params = {
        let c = EddsaSignatureDemo::<Bn256> {
            private_key: None,
            public_key: None,
            msg: Some(msg1.to_vec()),
            sig: Some(sig1.clone()),
            params: test_params,
            input: Some(input.clone()),
        };

        generate_random_parameters::<Bn256, _, _>(c, &mut rng).unwrap()
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

    println!(r#"{{"alpha_1":{:?},"beta_1":{:?},"beta_2":{:?},"gamma_2":{:?},"delta_1":{:?},"delta_2":{:?},"ic":[{:?},{:?}]}}"#, params.vk.alpha_g1.into_compressed(), params.vk.beta_g1.into_compressed(), params.vk.beta_g2.into_compressed(), params.vk.gamma_g2.into_compressed(), params.vk.delta_g1.into_compressed(), params.vk.delta_g2.into_compressed(), params.vk.ic[0].into_compressed(), params.vk.ic[1].into_compressed());

    println!("Creating proofs...");

    // Create an instance of circuit
    let c = EddsaSignatureDemo::<Bn256> {
        private_key: Some(sk),
        public_key: Some(vk),
        msg: Some(msg1.to_vec()),
        sig: Some(sig1),
        params: test_params,
        input: Some(input)
    };

    // Create a groth16 proof with our parameters.
    let proof = create_random_proof(c, &params, &mut rng).unwrap();

    let mut proof_vec = vec![];
    proof.write(&mut proof_vec).unwrap();

    let proof_a_affine = proof.a.into_uncompressed();
    // println!("proofaaffine: {:?}", proof_a_affine)

    let proof_b_affine = proof.b.into_uncompressed();
    // println!("proofabffine: {:?}", proof_b_affine);

    let proof_c_affine = proof.c.into_uncompressed();
    // println!("proofacffine: {:?}", proof_c_affine);

    let test = proof_a_affine.into_affine().unwrap();

    println!("proof: {:?}", proof);
    println!("test: {:?}", test);

    println!(r#"{{"pi_a":{:?},"pi_b":{:?},"pi_c":{:?}}}"#, proof_a_affine, proof_b_affine, proof_c_affine);


    assert!(verify_proof(
        &pvk,
        &proof,
        &[]
    ).is_ok());
}