#![allow(unused_imports)]
#![allow(unused_variables)]
use rand::thread_rng;
use bellman::{Circuit, ConstraintSystem, SynthesisError};
use bellman::pairing::bls12_381::{Bls12};
use bellman::pairing::ff::PrimeField as Fr;

mod cube;
// mod mimc;
mod test;
mod into_affine;

fn main() {
    // use bellman::groth16::{
    //     create_random_proof, generate_random_parameters, prepare_verifying_key, verify_proof, Proof,
    // };
    // // This may not be cryptographically safe, use
    // // `OsRng` (for example) in production software.
    // let mut rng = thread_rng();

    // println!("Creating parameters...");

    // // Create parameters for our circuit
    // let params = {
    //     let c = cube::CubeDemo::<Bls12> {
    //         x: None
    //     };

    //     generate_random_parameters::<Bls12, _, _>(c, &mut rng).unwrap()
    // };
    //  // Prepare the verification key (for proof verification)
    //  let pvk = prepare_verifying_key(&params.vk);

    //  println!("Creating proofs...");
     
    //  // Create an instance of circuit
    //  let c = cube::CubeDemo {
    //      x: Fr::from_str_vartime("3")
    //  };
     
    //  // Create a groth16 proof with our parameters.
    //  let proof = create_random_proof(c, &params, &mut rng).unwrap();
         
    // assert!(verify_proof(
    //      &pvk,
    //      &proof,
    //      &[Fr::from_str_vartime("35").unwrap()]
    //  ).is_ok());
}
