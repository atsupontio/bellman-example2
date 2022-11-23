use ff::PrimeField;

use bellman::{Circuit, ConstraintSystem, SynthesisError};

pub const MIMC_ROUNDS: usize = 322;


// For randomness (during paramgen and proof generation)
use rand::thread_rng;

// For benchmarking
use std::time::{Duration, Instant};

// Bring in some tools for using finite fiels
use ff::Field;

// We're going to use the BLS12-381 pairing-friendly elliptic curve.
use bls12_381::{Bls12, Scalar};

// We're going to use the Groth16 proving system.
use bellman::groth16::{
    batch, create_random_proof, generate_random_parameters, prepare_verifying_key, verify_proof,
    Proof,
};

use crate::encode;


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
pub struct MiMCDemo<'a, S: PrimeField> {
    pub xl: Option<S>,
    pub xr: Option<S>,
    pub constants: &'a [S],
    pub secret: Option<S>,
}

/// Our demo circuit implements this `Circuit` trait which
/// is used during paramgen and proving in order to
/// synthesize the constraint system.
impl<'a, S: PrimeField> Circuit<S> for MiMCDemo<'a, S> {
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
                    |lc| lc + (self.secret.unwrap(), CS::one()),
                    |lc| lc + CS::one(),
                    |lc| lc + new_xl,
                );
            }
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
        .map(|_| Scalar::random(&mut rng))
        .collect::<Vec<_>>();

    println!("Creating parameters...");

    let xl = Scalar::random(&mut rng);
    let xr = Scalar::random(&mut rng);
    let image = mimc(xl, xr, &constants);
    // let image = PrimeField::from_str_vartime("5").unwrap();

    // Create parameters for our circuit
    let params = {
        let c = MiMCDemo {
            xl: None,
            xr: None,
            constants: &constants,
            secret: Some(image),
        };

        generate_random_parameters::<Bls12, _, _>(c, &mut rng).unwrap()
    };

    // Prepare the verification key (for proof verification)
    let pvk = prepare_verifying_key(&params.vk);

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
        // let xl = Scalar::random(&mut rng);
        // let xr = Scalar::random(&mut rng);
        // let image = mimc(xl, xr, &constants);

        proof_vec.truncate(0);

        let start = Instant::now();
        {
            // Create an instance of our circuit (with the
            // witness)
            let c = MiMCDemo {
                xl: Some(xl),
                xr: Some(xr),
                constants: &constants,
                secret: Some(image),
            };

            // Create a groth16 proof with our parameters.
            let proof = create_random_proof(c, &params, &mut rng).unwrap();

            
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

            proof.write(&mut proof_vec).unwrap();
        }

        total_proving += start.elapsed();

        let start = Instant::now();
        let proof = Proof::read(&proof_vec[..]).unwrap();

        // Check the proof
        assert!(verify_proof(&pvk, &proof, &[]).is_ok());
        total_verifying += start.elapsed();
    }
    let proving_avg = total_proving / SAMPLES;
    let proving_avg =
        proving_avg.subsec_nanos() as f64 / 1_000_000_000f64 + (proving_avg.as_secs() as f64);

    let verifying_avg = total_verifying / SAMPLES;
    let verifying_avg =
        verifying_avg.subsec_nanos() as f64 / 1_000_000_000f64 + (verifying_avg.as_secs() as f64);

    println!("Average proving time: {:?} seconds", proving_avg);
    println!("Average verifying time: {:?} seconds", verifying_avg);
}

// #[test]
// fn batch_verify() {
//     let mut rng = thread_rng();

//     let mut batch = batch::Verifier::new();

//     // Generate the MiMC round constants
//     let constants = (0..MIMC_ROUNDS)
//         .map(|_| Scalar::random(&mut rng))
//         .collect::<Vec<_>>();

//     println!("Creating parameters...");

//     // Create parameters for our circuit
//     let params = {
//         let c = MiMCDemo {
//             xl: None,
//             xr: None,
//             constants: &constants,
//         };

//         generate_random_parameters::<Bls12, _, _>(c, &mut rng).unwrap()
//     };

//     // Prepare the verification key (for proof verification)
//     let pvk = prepare_verifying_key(&params.vk);

//     println!("Creating proofs...");

//     // Let's benchmark stuff!
//     const SAMPLES: u32 = 50;
//     let mut total_proving = Duration::new(0, 0);
//     let mut total_verifying = Duration::new(0, 0);

//     // Just a place to put the proof data, so we can
//     // benchmark deserialization.
//     let mut proof_vec = vec![];

//     for _ in 0..SAMPLES {
//         // Generate a random preimage and compute the image
//         let xl = Scalar::random(&mut rng);
//         let xr = Scalar::random(&mut rng);
//         let image = mimc(xl, xr, &constants);

//         proof_vec.truncate(0);

//         let start = Instant::now();
//         {
//             // Create an instance of our circuit (with the
//             // witness)
//             let c = MiMCDemo {
//                 xl: Some(xl),
//                 xr: Some(xr),
//                 constants: &constants,
//             };

//             // Create a groth16 proof with our parameters.
//             let proof = create_random_proof(c, &params, &mut rng).unwrap();

//             proof.write(&mut proof_vec).unwrap();
//         }

//         total_proving += start.elapsed();

//         let start = Instant::now();
//         let proof = Proof::read(&proof_vec[..]).unwrap();

//         println!("proof: {:?}", proof);

//         // Check the proof
//         assert!(verify_proof(&pvk, &proof, &[image]).is_ok());

//         total_verifying += start.elapsed();

//         // Queue the proof and inputs for batch verification.
//         batch.queue((proof, [image].into()));
//     }

//     let mut batch_verifying = Duration::new(0, 0);
//     let batch_start = Instant::now();

//     // Verify this batch for this specific verifying key
//     assert!(batch.verify(rng, &params.vk).is_ok());

//     batch_verifying += batch_start.elapsed();

//     let proving_avg = total_proving / SAMPLES;
//     let proving_avg =
//         proving_avg.subsec_nanos() as f64 / 1_000_000_000f64 + (proving_avg.as_secs() as f64);

//     let verifying_avg = total_verifying / SAMPLES;
//     let verifying_avg =
//         verifying_avg.subsec_nanos() as f64 / 1_000_000_000f64 + (verifying_avg.as_secs() as f64);

//     let batch_amortized = batch_verifying / SAMPLES;
//     let batch_amortized = batch_amortized.subsec_nanos() as f64 / 1_000_000_000f64
//         + (batch_amortized.as_secs() as f64);

//     println!("Average proving time: {:?} seconds", proving_avg);
//     println!("Average verifying time: {:?} seconds", verifying_avg);
//     println!(
//         "Amortized batch verifying time: {:?} seconds",
//         batch_amortized
//     );
// }
