#![allow(unused_imports)]
#![allow(unused_variables)]
use bellman::gadgets::{num, boolean};
use bls12_381::{Bls12, Scalar};
// For randomness (during paramgen and proof generation)
use rand::{thread_rng, Rng};
use ff::{PrimeField, Field};

use bellman::{
    Circuit,
    ConstraintSystem,
    SynthesisError, Variable, LinearCombination
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
pub struct RangeProof<E: PrimeField> {
    pub lhs: Option<E>,
    pub rhs: Option<E>,
    pub n: u64,
}

impl <E: PrimeField + ff::PrimeFieldBits> Circuit<E> for RangeProof<E> {
    fn synthesize<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS
    ) -> Result<(), SynthesisError>
    {
        let n: u64 = self.n;

        let mut coeff = E::one();
        let lhs_value = self.lhs;
        let lhs = cs.alloc(
            || "A",
            || lhs_value.ok_or(SynthesisError::AssignmentMissing),
        )?;

        let rhs_value = self.rhs;
        let rhs = cs.alloc(
            || "B",
            || rhs_value.ok_or(SynthesisError::AssignmentMissing),
        )?;

        let twon_value = Some(E::from_str_vartime("2").unwrap().pow_vartime(&[n]));
        let twon = cs.alloc_input(
            || "2^n",
            || twon_value.ok_or(SynthesisError::AssignmentMissing),
        )?;

        let alpha_packed_value = match (&self.rhs, &self.lhs){
            (Some(_r), Some(_l)) => {
                let mut tmp = E::from_str_vartime("2").unwrap().pow_vartime(&[n]);
                tmp.add_assign(&self.rhs.unwrap());
                tmp.sub_assign(&self.lhs.unwrap());
                Some(tmp)
            }
            _ => None,
        };
        let alpha_packed = cs.alloc(
            || "alpha_packed",
            || alpha_packed_value.ok_or(SynthesisError::AssignmentMissing),
        )?;

        let mut alpha_bits: Vec<Option<E>> = Vec::new();

        let bits = match alpha_packed_value {
            Some(_) => boolean::field_into_allocated_bits_le(
                cs.namespace(|| "field into bits"),
                alpha_packed_value,
            )?,
            _ => boolean::field_into_allocated_bits_le(
                cs.namespace(|| "field into bits"),
                Some(E::zero()),
            )?,
        };
        for i in 0..(n + 1) {
            if bits[i as usize].get_value() == Some(true) {
                alpha_bits.push(Some(E::one()));
            } else {
                alpha_bits.push(Some(E::zero()));
            }
        }
        assert_eq!(alpha_bits.len(), (n + 1) as usize);

        let mut alpha: Vec<Variable> = Vec::new();

        for i in 0..n {
            let alpha_i = cs.alloc(
                || format!("alpha[{}]", i),
                || alpha_bits[i as usize].ok_or(SynthesisError::AssignmentMissing),
            )?;
            alpha.push(alpha_i);
        }
        let less_or_equal_value = alpha_bits[n as usize].unwrap();
        let less_or_equal = cs.alloc(
            || "less_or_equal",
            || alpha_bits[n as usize].ok_or(SynthesisError::AssignmentMissing),
        )?;
        alpha.push(less_or_equal);

        let mut sum_value = E::zero();
        for i in 0..n {
            if !alpha_bits[i as usize].unwrap().is_zero_vartime() {
                sum_value.add_assign(&E::one())
            };
        }

        let (inv_value, not_all_zeros) = if sum_value.is_zero_vartime() {
            (Some(E::zero()), Some(E::zero()))
        } else {
            (Some(sum_value.invert().unwrap()), Some(E::one()))
        };

        let inv = cs.alloc(
            || "inv",
            || inv_value.ok_or(SynthesisError::AssignmentMissing),
        )?;
        let output = cs.alloc(
            || "output",
            || not_all_zeros.ok_or(SynthesisError::AssignmentMissing),
        )?;

        cs.enforce(
            || "main_constraint",
            |lc| lc + CS::one(),
            |lc| lc + twon + rhs -lhs,
            |lc| lc + alpha_packed,
        );

        for b in &alpha {
            cs.enforce(
                || "bit[i] boolean constraint",
                |lc| lc + CS::one() - (coeff, *b),
                |lc| lc + (coeff, *b),
                |lc| lc,
            )
        }

        let mut lc2 = LinearCombination::<E>::zero();
        for i in 0..n {
            lc2 = lc2 + (coeff, alpha[i as usize]);
        }
        cs.enforce(
            || "inv * sum = output",
            |lc| lc + inv,
            |_| lc2,
            |lc| lc + output,
        );

        let mut lc2 = LinearCombination::<E>::zero();
        for i in 0..n {
            lc2 = lc2 + (coeff, alpha[i as usize]);
        }
        cs.enforce(
            || "(1 - out) * sum = 0",
            |lc| lc + CS::one() - output,
            |_| lc2,
            |lc| lc,
        );

        let mut less_value = Some(E::one());
        if less_or_equal_value.is_zero_vartime() || not_all_zeros.unwrap().is_zero_vartime() {
            less_value = Some(E::zero());
        }
        let less = cs.alloc(
            || "less",
            || less_value.ok_or(SynthesisError::AssignmentMissing),
        )?;

        cs.enforce(
            || "less or equal * output = less",
            |lc| lc + less_or_equal,
            |lc| lc + output,
            |lc| lc + less,
        );

        cs.enforce(
            || "output boolean constraint",
            |lc| lc + CS::one() - output,
            |lc| lc + output,
            |lc| lc,
        );

        let mut lc2 = LinearCombination::<E>::zero();
        for b in &alpha {
            lc2 = lc2 + (coeff, *b);
            coeff = coeff.double();
        }
        cs.enforce(
            || "packing_constraints",
            |lc| lc + CS::one(),
            |_| lc2,
            |lc| lc + alpha_packed,
        );

        cs.enforce(
            || "less * 1 = 1",
            |lc| lc + less,
            |lc| lc + CS::one(),
            |lc| lc + CS::one(),
        );

        Ok(())
    }
}

#[test]
fn test_cube_proof(){
    // This may not be cryptographically safe, use
    // `OsRng` (for example) in production software.
    let mut rng = thread_rng();
    let n = 5u64;
    let n_bits_str = format!("{:b}", n);
    let n_bits: [u64; 4] = [5, 0, 0, 0]; 

    println!("Creating parameters...");

    // Create parameters for our circuit
    let params = {
        let c = RangeProof::<Scalar> {
            lhs: None, 
            rhs: None,
            n: n,
        };

        generate_random_parameters::<Bls12, _, _>(c, &mut rng).unwrap()
    };

    // Prepare the verification key (for proof verification)
    let pvk = prepare_verifying_key(&params.vk);


    println!("Creating proofs...");

    // Create an instance of circuit
    let c = RangeProof::<Scalar> {
        lhs: PrimeField::from_str_vartime("3"),
        rhs: PrimeField::from_str_vartime("34"),
        n: n,
    };

    // Create a groth16 proof with our parameters.
    let proof = create_random_proof(c, &params, &mut rng).unwrap();

    let tmp = Scalar::from_str_vartime("2").unwrap().pow_vartime(&n_bits);

    assert!(verify_proof(
        &pvk,
        &proof,
        &[tmp]
    ).is_ok());
}
