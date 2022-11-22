use bellman::pairing::Engine;
use bellman::pairing::ff::{PrimeField, ScalarEngine};

use bellman::{Circuit, ConstraintSystem, SynthesisError};

pub const MIMC_ROUNDS: usize = 322;


// For randomness (during paramgen and proof generation)
use rand::thread_rng;

// For benchmarking
use std::time::{Duration, Instant};

// Bring in some tools for using finite fiels
use bellman::pairing::ff::Field;

// We're going to use the BLS12-381 pairing-friendly elliptic curve.
use bellman::pairing::bls12_381::{G1Uncompressed ,Bls12, G1Affine, G2Affine};

// We're going to use the Groth16 proving system.
use bellman::groth16::{
    create_random_proof, generate_random_parameters, prepare_verifying_key, verify_proof,
    Proof,
};

use bellman::pairing::{RawEncodable, CurveAffine};

use rand::{self, Rand};

fn mimc<E: Engine>(mut x: E::Fr, k: E::Fr, constants: &[E::Fr]) -> E::Fr {
    assert_eq!(constants.len(), MIMC_ROUNDS);

    for i in 0..MIMC_ROUNDS {
        // tmp1 = x + k + c[i]
        let mut tmp1 = x;
        tmp1.add_assign(&constants[i]);
        tmp1.add_assign(&k);
        // tmp2 = (x + k + c[i])^2
        let mut tmp2 = tmp1;
        tmp2.square();
        // tmp3 = (x + k + c[i])^4
        let mut tmp3 = tmp2;
        tmp3.square();
        // tmp4 = (x + k + c[i])^6
        let mut tmp4 = tmp3;
        tmp4.mul_assign(&tmp2);
        // tmp5 = (x + k + c[i])^7
        let mut tmp5 = tmp4;
        tmp5.mul_assign(&tmp1);
        x = tmp5;
    }

    x
}

/// This is our demo circuit for proving knowledge of the
/// preimage of a MiMC hash invocation.
#[allow(clippy::upper_case_acronyms)]
pub struct MiMCDemo<'a, S: Engine> {
    pub xl: Option<S::Fr>,
    pub xr: Option<S::Fr>,
    pub constants: &'a [S::Fr],
}

/// Our demo circuit implements this `Circuit` trait which
/// is used during paramgen and proving in order to
/// synthesize the constraint system.
impl<'a, S: Engine> Circuit<S> for MiMCDemo<'a, S> {
    fn synthesize<CS: ConstraintSystem<S>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
        assert_eq!(self.constants.len(), MIMC_ROUNDS);

        // Allocate the first component of the preimage.
        let mut xl_value = self.xl;
        let mut xl = cs.alloc(
            || "preimage xl",
            || xl_value.ok_or(SynthesisError::AssignmentMissing),
        )?;

        // Allocate the second component of the preimage.
        let mut xr_value = self.xr;
        let mut xr = cs.alloc(
            || "preimage xr",
            || xr_value.ok_or(SynthesisError::AssignmentMissing),
        )?;

        for i in 0..MIMC_ROUNDS {
            // xL, xR := xR + (xL + Ci)^3, xL
            let cs = &mut cs.namespace(|| format!("round {}", i));

            // tmp = (xL + Ci)^2
            let tmp_value = xl_value.map(|mut e| {
                e.add_assign(&xr_value.unwrap());
                e.add_assign(&self.constants[i]);
                e.square();
                e
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
                cs.alloc_input(
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
        }

        Ok(())
    }
}

#[test]
fn test_mimc() {
    // This may not be cryptographically safe, use
    // `OsRng` (for example) in production software.
    let mut rng = thread_rng();

    // Generate the MiMC round constants
    let constants = (0..MIMC_ROUNDS)
        .map(|_| <Bls12 as ScalarEngine>::Fr::rand(&mut rng))
        .collect::<Vec<_>>();

    println!("Creating parameters...");

    // Create parameters for our circuit
    let params = {
        let c = MiMCDemo {
            xl: None,
            xr: None,
            constants: &constants,
        };

        generate_random_parameters::<Bls12, _, _>(c, &mut rng).unwrap()
    };

    // Prepare the verification key (for proof verification)
    let pvk = prepare_verifying_key(&params.vk);

    println!(r#"{{"alpha_1":{:?},"beta_1":{:?},"beta_2":{:?},"gamma_2":{:?},"delta_1":{:?},"delta_2":{:?},"ic":[{:?},{:?}]}}"#, params.vk.alpha_g1.into_uncompressed(), params.vk.beta_g1.into_uncompressed(), params.vk.beta_g2.into_uncompressed(), params.vk.gamma_g2.into_uncompressed(), params.vk.delta_g1.into_uncompressed(), params.vk.delta_g2.into_uncompressed(), params.vk.ic[0].into_uncompressed(), params.vk.ic[1].into_uncompressed());


    println!("Creating proofs...");

    // Let's benchmark stuff!
    const SAMPLES: u32 = 1;
    let mut total_proving = Duration::new(0, 0);
    let mut total_verifying = Duration::new(0, 0);

    // Just a place to put the proof data, so we can
    // benchmark deserialization.
    let mut proof_vec = vec![];

    for _ in 0..SAMPLES {
        // Generate a random preimage and compute the image
        let xl = <Bls12 as ScalarEngine>::Fr::rand(&mut rng);
        let xr = <Bls12 as ScalarEngine>::Fr::rand(&mut rng);
        let image = mimc::<Bls12>(xl, xr, &constants);

        proof_vec.truncate(0);

        let start = Instant::now();
        {
            // Create an instance of our circuit (with the
            // witness)
            let c = MiMCDemo {
                xl: Some(xl),
                xr: Some(xr),
                constants: &constants,
            };

            // Create a groth16 proof with our parameters.
            let proof = create_random_proof(c, &params, &mut rng).unwrap();

            proof.write(&mut proof_vec).unwrap();
            println!("proof: {:?}", proof);
        }

        total_proving += start.elapsed();

        let start = Instant::now();
        let proof = Proof::read(&proof_vec[..]).unwrap();

        let proof_a: G1Affine = proof.a;

        let proof_a_affine: G1Uncompressed = proof_a.into_uncompressed();

        let proof_b: G2Affine = proof.b;

        let proof_b_affine = proof_b.into_uncompressed();


        let proof_c: G1Affine = proof.c;

        let proof_c_affine = proof_c.into_uncompressed();


        let proof_a_raw_affine = proof_a.into_uncompressed();
        let proof_b_raw_affine = proof_a.into_raw_uncompressed_le();
        let proof_c_raw_affine = proof_c.into_raw_uncompressed_le();

        println!(r#"{{"pi_a":{:?},"pi_b":{:?},"pi_c":{:?}}}"#, proof_a_raw_affine, proof_b_affine, proof_c_raw_affine);

        // println!(r#"{{"pi_a":{:?},"pi_b":{:?},"pi_c":{:?}}}"#, proof_a_affine, proof_b_affine, proof_c_affine);

        // Check the proof
        assert!(verify_proof(&pvk, &proof, &[image]).is_ok());
        total_verifying += start.elapsed();
    }

}

