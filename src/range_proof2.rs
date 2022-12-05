#![allow(unused_imports)]
#![allow(unused_variables)]
use bellman::gadgets::{num, boolean};
use bls12_381::{Bls12, Scalar};
// For randomness (during paramgen and proof generation)
use rand::{thread_rng, Rng};
use ff::PrimeField as Fr;

use bellman::{
    Circuit,
    ConstraintSystem,
    SynthesisError, Variable
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

impl <E: Fr + ff::PrimeFieldBits> Circuit<E> for CubeDemo<E> {
    fn synthesize<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS
    ) -> Result<(), SynthesisError>
    {
        let x_val = self.x;
        let x = cs.alloc(|| "x", || {
            x_val.ok_or(SynthesisError::AssignmentMissing)
        })?;
        println!("x_val: {:?}", x_val);

        let goal_val: Option<E> = Fr::from_str_vartime("2");
        let goal = cs.alloc_input(|| "goal", || {
            goal_val.ok_or(SynthesisError::AssignmentMissing)
        })?;

        // Allocate: x * x = tmp_1
        let tmp_1_val = x_val.map(|mut e| {
            e.sub_assign(&goal_val.unwrap());
            e
        });
        let tmp_1 = cs.alloc(|| "tmp_1", || {
            tmp_1_val.ok_or(SynthesisError::AssignmentMissing)
        })?;

        let tmp_1_bits_val = num::AllocatedNum::alloc(
            cs.namespace(|| "utxo value"),
            || {
                let value = tmp_1_val;
                Ok(value.unwrap())
            }
        )?;

        let tmp1_bits = tmp_1_bits_val.to_bits_le(
            cs.namespace(|| "get utxo value bits")
        )?;

        println!("tmp_1_val: {:?}", tmp_1_val);

        let a = tmp1_bits.get(0).unwrap();

        // boolean::Boolean::into(tmp1_bits.get(0).unwrap());
       
        cs.enforce(
            || "out",
            |lc| lc + x - goal,
            |lc| lc + CS::one(),
            |lc| lc + tmp_1
        );

        let a_val = cs.alloc(|| "x", || {
            Ok(*a)
        })?;
       
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
        let c = CubeDemo::<Scalar> {
            x: None, 
        };

        generate_random_parameters::<Bls12, _, _>(c, &mut rng).unwrap()
    };

    // Prepare the verification key (for proof verification)
    let pvk = prepare_verifying_key(&params.vk);


    println!("Creating proofs...");

    let mut a: Vec<Option<bool>> = Vec::new();
    // 4 = 0100
    a.push(Some(false));
    a.push(Some(true));
    a.push(Some(false));
    a.push(Some(false));

    // Create an instance of circuit
    let c = CubeDemo::<Scalar> {
        x: Scalar::from_str_vartime("1"),
    };

    // Create a groth16 proof with our parameters.
    let proof = create_random_proof(c, &params, &mut rng).unwrap();

    assert!(verify_proof(
        &pvk,
        &proof,
        &[Fr::from_str_vartime("2").unwrap()]
    ).is_ok());
}
