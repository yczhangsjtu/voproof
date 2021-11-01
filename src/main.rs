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
    Error, PCRandomness
};
use ark_std::{Zero, One, test_rng, UniformRand};
use ark_ff::fields::PrimeField;
use ark_relations::{lc, r1cs::{
  ConstraintSynthesizer, ConstraintSystemRef,
  SynthesisError, ConstraintSystem, Variable}};
use voproof::tools::{to_int, to_field};
use voproof::{accumulate_vector, define_vec, delta,
              expression_vector, multi_delta, linear_combination};
use voproof::cs::r1cs::{R1CS, R1CSInstance, R1CSWitness};
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
      cs.enforce_constraint(lc!() + a, lc!() + Variable::One, lc!() + v)?;
    }

    for _ in 0..self.num_constraints - 1 {
      cs.enforce_constraint(lc!() + a, lc!() + b, lc!() + c)?;
    }
    
    cs.enforce_constraint(lc!(), lc!(), lc!())?;

    Ok(())
  }
}


fn main() {
  let c = TestCircuit::<F> {
    a: Some(to_field::<F>(3)),
    b: Some(to_field::<F>(2)),
    num_variables: 10,
    num_constraints: 5,
  };
  let x = vec![c.a.unwrap(), c.b.unwrap(), (c.a.unwrap() * c.b.unwrap())];
  let w = vec![c.a.unwrap(); 7];

  let cs = ConstraintSystem::<F>::new_ref();
  c.generate_constraints(cs.clone()).unwrap();
  let r1cs = R1CS::from(cs.into_inner().unwrap());
  println!("R1CS num rows: {}", r1cs.nrows);
  println!("R1CS num cols: {}", r1cs.ncols);
  println!("R1CS A row indices: {:?}", r1cs.arows);
  println!("R1CS A col indices: {:?}", r1cs.acols);
  println!("R1CS A vals: {:?}", r1cs.avals);
  println!("R1CS B row indices: {:?}", r1cs.brows);
  println!("R1CS B col indices: {:?}", r1cs.bcols);
  println!("R1CS B vals: {:?}", r1cs.bvals);
  println!("R1CS C row indices: {:?}", r1cs.crows);
  println!("R1CS C col indices: {:?}", r1cs.ccols);
  println!("R1CS C vals: {:?}", r1cs.cvals);

  if r1cs.satisfy(&R1CSInstance{instance: x}, &R1CSWitness{witness: w}) {
    println!("R1CS satisfied!");
  } else {
    println!("R1CS unsatisfied!");
  }
}
