use ark_poly::{
    univariate::DensePolynomial as DensePoly,
    UVPolynomial, Polynomial
};
use ark_bls12_377::Bls12_377;
use ark_bls12_381::Bls12_381;
use ark_bls12_381::Fr as F;
use ark_ec::PairingEngine;
use ark_poly_commit::{
    // kzg10::{KZG10, UniversalParams, Powers, VerifierKey, Randomness},
    PCRandomness
};
use ark_std::{Zero, One, test_rng, UniformRand};
use ark_ff::fields::PrimeField;
use ark_relations::{lc, r1cs::{
  ConstraintSynthesizer, ConstraintSystemRef,
  SynthesisError, ConstraintSystem as ArkR1CS, Variable}};
#[macro_use]
use voproof::*;
use voproof::error::Error;
use voproof::tools::{to_int, to_field};
use voproof::{accumulate_vector, define_vec, delta,
              expression_vector, multi_delta, linear_combination};
use voproof::cs::{ConstraintSystem, r1cs::{R1CS, R1CSInstance, R1CSWitness}};
use voproof::snarks::{SNARK, voproof_r1cs::*};
use voproof::kzg::UniversalParams;
// use voproof::kzg::{KZG10, UniversalParams, Powers, VerifierKey, Randomness};

#[derive(Copy)]
struct TestCircuit<F: PrimeField> {
  pub a: Option<F>,
  pub b: Option<F>,
  pub num_variables: usize,
  pub num_constraints: usize,
}

impl<F: PrimeField> Clone for TestCircuit<F> {
  fn clone(&self) -> Self {
    TestCircuit {
      a: self.a.clone(),
      b: self.b.clone(),
      num_variables: self.num_variables.clone(),
      num_constraints: self.num_constraints.clone(),
    }
  }
}

impl<F: PrimeField> ConstraintSynthesizer<F> for TestCircuit<F> {
  fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> Result<(), SynthesisError> {
    let a = cs.new_input_variable(|| self.a.ok_or(SynthesisError::AssignmentMissing))?;
    let b = cs.new_input_variable(|| self.b.ok_or(SynthesisError::AssignmentMissing))?;
    let c = cs.new_input_variable(|| {
      let a = self.a.ok_or(SynthesisError::AssignmentMissing)?;
      let b = self.b.ok_or(SynthesisError::AssignmentMissing)?;
      Ok(a * b)
    })?;

    for _ in 0..(self.num_variables - 3) {
      let v = cs.new_witness_variable(|| self.a.ok_or(SynthesisError::AssignmentMissing))?;
      cs.enforce_constraint(lc!() + a + b, lc!() + Variable::One, lc!() + v + b)?;
    }

    for _ in 0..self.num_constraints - 1 {
      cs.enforce_constraint(lc!() + a, lc!() + b, lc!() + c)?;
    }
    
    cs.enforce_constraint(lc!(), lc!(), lc!())?;

    Ok(())
  }
}

fn run_r1cs_example<E: PairingEngine>() -> Result<(), Error> {
  let c = TestCircuit::<E::Fr> {
    a: Some(to_field::<E::Fr>(3)),
    b: Some(to_field::<E::Fr>(2)),
    num_variables: 10,
    num_constraints: 5,
  };
  let x = vec![c.a.unwrap(), c.b.unwrap(), (c.a.unwrap() * c.b.unwrap())];
  let w = vec![c.a.unwrap(); 7];

  let cs = ArkR1CS::<E::Fr>::new_ref();
  c.generate_constraints(cs.clone()).unwrap();
  let r1cs = R1CS::from(cs.into_inner().unwrap());
  println!("R1CS num rows: {}", r1cs.nrows);
  println!("R1CS num cols: {}", r1cs.ncols);
  println!("R1CS A row indices: {:?}", r1cs.arows);
  println!("R1CS A col indices: {:?}", r1cs.acols);
  println!("R1CS A vals: {:?}", to_int!(r1cs.avals));
  println!("R1CS B row indices: {:?}", r1cs.brows);
  println!("R1CS B col indices: {:?}", r1cs.bcols);
  println!("R1CS B vals: {:?}", to_int!(r1cs.bvals));
  println!("R1CS C row indices: {:?}", r1cs.crows);
  println!("R1CS C col indices: {:?}", r1cs.ccols);
  println!("R1CS C vals: {:?}", to_int!(r1cs.cvals));

  let instance = R1CSInstance{instance: x};
  let witness = R1CSWitness{witness: w};

  if r1cs.satisfy(&instance, &witness) {
    println!("R1CS satisfied!");
  } else {
    println!("R1CS unsatisfied!");
  }

  let max_degree = VOProofR1CS::get_max_degree(r1cs.get_size());
  let universal_params : UniversalParams::<E> = VOProofR1CS::setup(max_degree).unwrap();
  println!("Universal parameter size: {}", universal_params.powers_of_g.len());
  let (pk, vk) = VOProofR1CS::index(&universal_params, &r1cs).unwrap();
  println!("Prover key matrix size: {}", pk.M_mat.0.len());
  println!("Prover key u size: {}", pk.u_vec.len());
  println!("Prover key v size: {}", pk.v_vec.len());
  println!("Prover key w size: {}", pk.w_vec.len());

  println!("M A row indices: {:?}", pk.M_mat.0);
  println!("M A col indices: {:?}", pk.M_mat.1);
  println!("M A vals: {:?}", to_int!(pk.M_mat.2));
  let vksize = vk.size.clone();
  println!("H: {}", vksize.nrows);
  println!("K: {}", vksize.ncols);

  let proof = VOProofR1CS::prove(&pk, &instance, &witness)?;
  VOProofR1CS::verify(&vk, &instance, &proof)
}


fn main() {
  if let Err(err) = run_r1cs_example::<ark_bls12_381::Bls12_381>() {
    println!("{}", err);
  } else {
    println!("Verification pass");
  }
}
