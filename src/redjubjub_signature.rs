use ff::PrimeField;

use bellman::{Circuit, ConstraintSystem, SynthesisError, Variable};

use crate::redjubjub::{PrivateKey, PublicKey, Signature, h_star, read_scalar};
use zcash_primitives::constants::SPENDING_KEY_GENERATOR;
use jubjub::{Fr, ExtendedPoint, SubgroupPoint};
use group::GroupEncoding;
use std::ops::MulAssign;

use zcash_primitives::sapling::util::hash_to_scalar;

// For randomness (during paramgen and proof generation)
use rand::thread_rng;

// For benchmarking
use std::{time::{Duration, Instant}, collections::btree_map::OccupiedEntry};

// Bring in some tools for using finite fiels
use ff::Field;

// We're going to use the BLS12-381 pairing-friendly elliptic curve.
use bls12_381::{Bls12, Scalar};

// We're going to use the Groth16 proving system.
use bellman::groth16::{
    batch, create_random_proof, generate_random_parameters, prepare_verifying_key, verify_proof,
    Proof,
};


pub fn mimc<S: PrimeField>(mut xl: S, mut xr: S, constants: &[S]) -> S {
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


/// This is our demo circuit for proving knowledge of the
/// preimage of a MiMC hash invocation.
#[allow(clippy::upper_case_acronyms)]
pub struct RedSignature<'a> {
    pub prv_key: Option<PrivateKey>,
    pub pub_key: Option<PublicKey>,
    pub msg: Option<&'a [u8]>,
    pub sig: Option<Signature>,
    pub c: Option<Fr>,
    pub vk: Option<ExtendedPoint>,
    pub S: Option<Fr>,
    pub P_G: Option<SubgroupPoint>,
    pub R: Option<ExtendedPoint>,
}


// #[allow(clippy::upper_case_acronyms)]
// pub struct RedSignature<'a> {
//     pub prv_key: Option<PrivateKey>,
//     pub pub_key: Option<PublicKey>,
//     pub msg: Option<&'a [u8]>,
//     pub sig: Option<Signature>,
// }

/// Our demo circuit implements this `Circuit` trait which
/// is used during paramgen and proving in order to
/// synthesize the constraint system.
impl<'a, S: PrimeField> Circuit<S> for RedSignature<'a> {
    fn synthesize<CS: ConstraintSystem<S>>(self, cs: &mut CS) -> Result<(), SynthesisError> {

        // Allocate the first component of the preimage.
        let mut c_value = self.c;
        let mut c = cs.alloc(
            || "c",
            || c_value.ok_or(SynthesisError::AssignmentMissing),
        )?;

        // Allocate the second component of the preimage.
        let mut vk_value = self.vk;
        let mut vk = cs.alloc(
            || "vk",
            || vk_value.ok_or(SynthesisError::AssignmentMissing),
        )?;

        let tmp1_value = c_value.map(|mut e| {
            e.mul_assign(&vk_value.unwrap());
            e
        });
        let tmp1 = cs.alloc(
            || "tmp1",
            || tmp1_value.ok_or(SynthesisError::AssignmentMissing),
        )?;

        cs.enforce(
            || "tmp1 = (c * vk)",
            |lc| lc + c,
            |lc| lc + vk,
            |lc| lc + tmp1,
        );

        let mut S_value = self.S;
        let mut S = cs.alloc(
            || "S",
            || S_value.ok_or(SynthesisError::AssignmentMissing),
        )?;

        let mut P_G_value = self.P_G;
        let mut P_G = cs.alloc(
            || "P_G",
            || P_G_value.ok_or(SynthesisError::AssignmentMissing),
        )?;


        let tmp2_value = S_value.map(|mut e| {
            e.mul_assign(&P_G_value.unwrap())
            e
        });
        let tmp2 = cs.alloc(
            || "tmp2",
            || tmp2_value.ok_or(SynthesisError::AssignmentMissing),
        )?;

        cs.enforce(
            || "tmp2 = (c * vk)",
            |lc| lc + S,
            |lc| lc + P_G,
            |lc| lc + tmp2,
        );
        
        let mut r_value = self.R;
        let mut r = cs.alloc(
            || "r",
            || r_value.ok_or(SynthesisError::AssignmentMissing),
        )?;

        let tmp3_value = tmp1_value.map(|mut e| {
            e.add_assign(&P_G_value.unwrap());
            e
        });
        let tmp3 = cs.alloc(
            || "tmp3",
            || tmp3_value.ok_or(SynthesisError::AssignmentMissing),
        )?;
        let out_value = tmp3_value.map(|mut e| {
            e.sub_assign(&tmp2_value.unwrap());
            e
        });
        let out = cs.alloc(
            || "out",
            || out_value.ok_or(SynthesisError::AssignmentMissing),
        )?;


        cs.enforce(
            || "out = (tmp3 - tmp2)",
            |lc| lc + tmp3 - tmp2,
            |lc| lc + CS::one(),
            |lc| lc + out,
        );

        // let new_out: ExtendedPoint = ((vk_value.unwrap() * c_value.unwrap()) + r_value.unwrap() - (P_G_value.unwrap() * S_value.unwrap()))
        // .mul_by_cofactor()
        //     .is_identity()
        //     .into();

        Ok(())
    }
}

#[test]
fn test_redjubjub() {
    // This may not be cryptographically safe, use
    // `OsRng` (for example) in production software.
    let mut rng = thread_rng();

    // let mut rng = XorShiftRng::from_seed([
    //     0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
    //     0xbc, 0xe5,
    // ]);
    let p_g = SPENDING_KEY_GENERATOR;

    // Generate the MiMC round constants
    let constants = Scalar::random(&mut rng);

    println!("Creating parameters...");

    let secret_key = PrivateKey(jubjub::Fr::random(&mut rng));
    let verification_key = PublicKey::from_private(&secret_key, p_g);
    let msg = b"Foo bar";
    let sig = secret_key.sign(msg, &mut rng, p_g);

    // Create parameters for our circuit
    let params = {
        let c = RedSignature {
            prv_key: None,
            pub_key: None,
            msg: None,
            sig: None,
            c: None,
            vk: None,
            S: None,
            P_G: None,
            R: None,
        };

        generate_random_parameters::<Bls12, _, _>(c, &mut rng).unwrap()
    };

    // Prepare the verification key (for proof verification)
    let pvk = prepare_verifying_key(&params.vk);

    println!("Creating proofs...");

    let c = h_star(&sig.rbar[..], msg);
    let vk = verification_key.0;
    let S = match read_scalar::<&[u8]>(&sig.sbar[..]) {
        Ok(s) => s,
        Err(_) => return (),
    };
    let P_G = p_g;
    let r = {
        let r = ExtendedPoint::from_bytes(&sig.rbar);
        
        if r.is_none().into() {
            return ();
        }
        r.unwrap()
    };


            // Create an instance of our circuit (with the
            // witness)
            let c = RedSignature {
                prv_key: Some(secret_key),
                pub_key: Some(verification_key),
                msg: Some(msg),
                sig: Some(sig),
                c: c,
                vk: Some(vk),
                S: Some(S),
                P_G: Some(p_g),
                R: Some(r),
            };

            // Create a groth16 proof with our parameters.
            let proof = create_random_proof(c, &params, &mut rng).unwrap();

        // Check the proof
        assert!(verify_proof(&pvk, &proof, &[msg]).is_ok());
}

