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
pub struct CubeDemo<> {
    pub x: Vec<Option<bool>>,
}

impl <E: Fr + ff::PrimeFieldBits> Circuit<E> for CubeDemo<> {
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

        let mut x_bits = Vec::<boolean::Boolean>::with_capacity(4);
        // allocate bits for use of sha256 
        for i in 0..4 {
            let bit = boolean::Boolean::from(boolean::AllocatedBit::alloc(
                cs.namespace(|| format!("allocating blinding bit {}", i)),
                self.x[i]
                )?
            );
            x_bits.push(bit);
        }

        let mut goal: Vec<Option<bool>> = Vec::new();
        // 2 = 0010
        goal.push(Some(false));
        goal.push(Some(false));
        goal.push(Some(true));
        goal.push(Some(false));

        let mut goal_bits = Vec::<boolean::Boolean>::with_capacity(4);
        // allocate bits for use of sha256 
        for i in 0..4 {
            let bit = boolean::Boolean::from(boolean::AllocatedBit::alloc(
                cs.namespace(|| format!("allocating blinding bit {}", i)),
                goal[i]
                )?
            );
            goal_bits.push(bit);
        }

        let mut coeff = E::one();
        let mut x_lc = num::Num::<E>::zero();
        for bit in x_bits.iter() {
            x_lc = x_lc.add_bool_with_coeff(CS::one(), bit, coeff);
            coeff = coeff.double();
        }

        // allocate some number that should be equal to this combination
        let value = num::AllocatedNum::alloc(
            cs.namespace(|| "current value"), 
            || {
                let value = x_lc.get_value();

                Ok(value.unwrap())
            }
        )?;

        let mut coeff = E::one();
        let mut goal_lc = num::Num::<E>::zero();
        for bit in goal_bits.iter() {
            goal_lc = goal_lc.add_bool_with_coeff(CS::one(), bit, coeff);
            coeff = coeff.double();
        }

        // allocate some number that should be equal to this combination
        let goal_value = num::AllocatedNum::alloc(
            cs.namespace(|| "current value"), 
            || {
                let value = goal_lc.get_value();

                Ok(value.unwrap())
            }
        )?;

        let new_x = value.get_value();
        let new_goal = goal_value.get_value();
        new_x.unwrap().sub_assign(new_goal.unwrap());


        let ans_value = num::AllocatedNum::alloc(
            cs.namespace(|| "answer value"),
            || {
                let value = new_x;
                Ok(value.unwrap())
            }
        )?;

        let ans_bits = ans_value.to_bits_le(
            cs.namespace(|| "get answer value bits")
        )?;

        let a = ans_bits[0].get_value().unwrap();

        if !a {
            // Enforce: x - goal = tmp_1
            cs.enforce(
                || "tmp_1",
                |lc| lc + value.get_variable() - goal_value.get_variable(),
                |lc| lc + CS::one(),
                |lc| lc + ans_value.get_variable()
            );
        } else {
            return Err(SynthesisError::AssignmentMissing)
        }
       
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
            x: vec![None; 4], 
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
    let c = CubeDemo::<> {
        x: a,
    };

    // Create a groth16 proof with our parameters.
    let proof = create_random_proof(c, &params, &mut rng).unwrap();

    assert!(verify_proof(
        &pvk,
        &proof,
        &[]
    ).is_ok());
}
