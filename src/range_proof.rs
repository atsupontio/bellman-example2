#![allow(unused_imports)]
#![allow(unused_variables)]
use bellman::gadgets::num;
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

// proving that I know x such that x^3 + x + 5 == 35
// Generalized: x^3 + x + 5 == out
#[allow(clippy::upper_case_acronyms)]
pub struct CubeDemo<E: Fr> {
    pub x: Option<E>,
}

impl <E: Fr> Circuit<E> for CubeDemo<E> {
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

        // Allocate the first private "auxiliary" variable
        let x_val = self.x;
        let x = cs.alloc(|| "x", || {
            x_val.ok_or(SynthesisError::AssignmentMissing)
        })?;

        let goal_val = Fr::from_str_vartime("2");

        let ans_val = x_val.map(|mut e| {
            e.sub_assign(&goal_val.unwrap());
            e
        });
        let ans = cs.alloc(|| "ans", || {
            ans_val.ok_or(SynthesisError::AssignmentMissing)
        })?;

        // Enforce: x - goal = tmp_1
        cs.enforce(
            || "tmp_1",
            |lc| lc + x - (E::from_str_vartime("2").unwrap(), CS::one()),
            |lc| lc + CS::one(),
            |lc| lc + ans
        );

       
        Ok(())
    }
}

#[test]
fn test_cube_proof(){
    // This may not be cryptographically safe, use
    // `OsRng` (for example) in production software.
    let mut rng = thread_rng();

    println!("Creating parameters...");

    // Create parameters for our circuit
    let params = {
        let c = CubeDemo::<> {
            x: None, 
        };

        generate_random_parameters::<Bls12, _, _>(c, &mut rng).unwrap()
    };

    // Prepare the verification key (for proof verification)
    let pvk = prepare_verifying_key(&params.vk);


    println!("Creating proofs...");

    // Create an instance of circuit
    let c = CubeDemo::<Scalar> {
        x: Fr::from_str_vartime("3"),
    };

    // Create a groth16 proof with our parameters.
    let proof = create_random_proof(c, &params, &mut rng).unwrap();

    assert!(verify_proof(
        &pvk,
        &proof,
        &[]
    ).is_ok());
}
