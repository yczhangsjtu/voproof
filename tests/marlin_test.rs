use ark_bls12_381::Bls12_381 as E;
use ark_bls12_381::Fr;
use ark_ec::PairingEngine;
use ark_ff::fields::PrimeField;
use ark_marlin::{Marlin, UniversalSRS};
use ark_poly::univariate::DensePolynomial as P;
use ark_poly_commit::sonic_pc::SonicKZG10;
use ark_relations::{
  lc,
  r1cs::{
    ConstraintSynthesizer, ConstraintSystem as ArkR1CS, ConstraintSystemRef, SynthesisError,
    Variable,
  },
};
use blake2::Blake2s;
use ark_std::{start_timer, end_timer};
use voproof::tools::to_field;
use voproof::*;

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

fn computes_universal_scale<E: PairingEngine>(scale: usize) -> (usize, usize, usize) {
  let c = TestCircuit::<E::Fr> {
    a: Some(to_field::<E::Fr>(3)),
    b: Some(to_field::<E::Fr>(2)),
    num_variables: scale,
    num_constraints: scale,
  };
  let x = vec![c.a.unwrap(), c.b.unwrap(), (c.a.unwrap() * c.b.unwrap())];
  let w = vec![c.a.unwrap(); scale - 3];

  let mut cs = ArkR1CS::<E::Fr>::new_ref();
  c.generate_constraints(cs.clone()).unwrap();
  cs.inline_all_lcs();
  let matrices = cs.to_matrices().unwrap();
  (
    matrices.num_constraints,
    matrices.num_instance_variables + matrices.num_witness_variables,
    max!(matrices.a_num_non_zero, matrices.b_num_non_zero, matrices.c_num_non_zero),
  )
}

fn computes_universal_parameter_and_circuit<E: PairingEngine>(
  scale: usize,
) -> (
  UniversalSRS<E::Fr, SonicKZG10<E, P<E::Fr>>>,
  TestCircuit<E::Fr>,
  Vec::<E::Fr>,
) {
  let rng = &mut ark_std::test_rng();
  let c = TestCircuit::<E::Fr> {
    a: Some(to_field::<E::Fr>(3)),
    b: Some(to_field::<E::Fr>(2)),
    num_variables: scale,
    num_constraints: scale,
  };
  let x = vec![c.a.unwrap(), c.b.unwrap(), (c.a.unwrap() * c.b.unwrap())];
  let w = vec![c.a.unwrap(); scale - 3];

  let mut cs = ArkR1CS::<E::Fr>::new_ref();
  c.generate_constraints(cs.clone()).unwrap();
  cs.inline_all_lcs();
  let matrices = cs.to_matrices().unwrap();
  let (m, n, s) = (
    matrices.num_constraints,
    matrices.num_instance_variables + matrices.num_witness_variables,
    max!(matrices.a_num_non_zero, matrices.b_num_non_zero, matrices.c_num_non_zero),
  );
  (
    Marlin::<E::Fr, SonicKZG10<E, P<E::Fr>>, Blake2s>::universal_setup(m, n, s, rng).unwrap(),
    c,
    x,
  )
}

#[test]
fn test_marlin_setup_test_circuit_scale_1000() {
  let rng = &mut ark_std::test_rng();
  let (m, n, s) = computes_universal_scale::<E>(1000);
  let timer = start_timer!(|| "Setup");
  let _ = Marlin::<Fr, SonicKZG10<E, P<Fr>>, Blake2s>::universal_setup(m, n, s, rng).unwrap();
  end_timer!(timer);
}

#[test]
fn test_marlin_index_test_circuit_scale_1000() {
  let (srs, c, _) = computes_universal_parameter_and_circuit::<E>(1000);
  let timer = start_timer!(|| "Index");
  let (pk, _) = Marlin::<Fr, SonicKZG10<E, P<Fr>>, Blake2s>::index(&srs, c).unwrap();
  end_timer!(timer);
}

#[test]
fn test_marlin_prover_test_circuit_scale_1000() {
  let (srs, c, _) = computes_universal_parameter_and_circuit::<E>(1000);
  let (pk, _) = Marlin::<Fr, SonicKZG10<E, P<Fr>>, Blake2s>::index(&srs, c).unwrap();
  let rng = &mut ark_std::test_rng();
  let timer = start_timer!(|| "Proving");
  let _ = Marlin::<Fr, SonicKZG10<E, P<Fr>>, Blake2s>::prove(&pk, c.clone(), rng).unwrap();
  end_timer!(timer);
}

#[test]
fn test_marlin_prover_test_circuit_scale_2000() {
  let (srs, c, _) = computes_universal_parameter_and_circuit::<E>(2000);
  let (pk, _) = Marlin::<Fr, SonicKZG10<E, P<Fr>>, Blake2s>::index(&srs, c).unwrap();
  let rng = &mut ark_std::test_rng();
  let timer = start_timer!(|| "Proving");
  let _ = Marlin::<Fr, SonicKZG10<E, P<Fr>>, Blake2s>::prove(&pk, c.clone(), rng).unwrap();
  end_timer!(timer);
}

#[test]
fn test_marlin_prover_test_circuit_scale_4000() {
  let (srs, c, _) = computes_universal_parameter_and_circuit::<E>(4000);
  let (pk, _) = Marlin::<Fr, SonicKZG10<E, P<Fr>>, Blake2s>::index(&srs, c).unwrap();
  let rng = &mut ark_std::test_rng();
  let timer = start_timer!(|| "Proving");
  let _ = Marlin::<Fr, SonicKZG10<E, P<Fr>>, Blake2s>::prove(&pk, c.clone(), rng).unwrap();
  end_timer!(timer);
}

#[test]
fn test_marlin_prover_test_circuit_scale_8000() {
  let (srs, c, _) = computes_universal_parameter_and_circuit::<E>(8000);
  let (pk, _) = Marlin::<Fr, SonicKZG10<E, P<Fr>>, Blake2s>::index(&srs, c).unwrap();
  let rng = &mut ark_std::test_rng();
  let timer = start_timer!(|| "Proving");
  let _ = Marlin::<Fr, SonicKZG10<E, P<Fr>>, Blake2s>::prove(&pk, c.clone(), rng).unwrap();
  end_timer!(timer);
}

#[test]
fn test_marlin_prover_test_circuit_scale_16000() {
  let (srs, c, _) = computes_universal_parameter_and_circuit::<E>(16000);
  let (pk, _) = Marlin::<Fr, SonicKZG10<E, P<Fr>>, Blake2s>::index(&srs, c).unwrap();
  let rng = &mut ark_std::test_rng();
  let timer = start_timer!(|| "Proving");
  let _ = Marlin::<Fr, SonicKZG10<E, P<Fr>>, Blake2s>::prove(&pk, c.clone(), rng).unwrap();
  end_timer!(timer);
}

#[test]
fn test_marlin_prover_test_circuit_scale_32000() {
  let (srs, c, _) = computes_universal_parameter_and_circuit::<E>(32000);
  let (pk, _) = Marlin::<Fr, SonicKZG10<E, P<Fr>>, Blake2s>::index(&srs, c).unwrap();
  let rng = &mut ark_std::test_rng();
  let timer = start_timer!(|| "Proving");
  let _ = Marlin::<Fr, SonicKZG10<E, P<Fr>>, Blake2s>::prove(&pk, c.clone(), rng).unwrap();
  end_timer!(timer);
}

#[test]
fn test_marlin_prover_test_circuit_scale_64000() {
  let (srs, c, _) = computes_universal_parameter_and_circuit::<E>(64000);
  let (pk, _) = Marlin::<Fr, SonicKZG10<E, P<Fr>>, Blake2s>::index(&srs, c).unwrap();
  let rng = &mut ark_std::test_rng();
  let timer = start_timer!(|| "Proving");
  let _ = Marlin::<Fr, SonicKZG10<E, P<Fr>>, Blake2s>::prove(&pk, c.clone(), rng).unwrap();
  end_timer!(timer);
}

#[test]
fn test_marlin_prover_test_circuit_scale_128000() {
  let (srs, c, _) = computes_universal_parameter_and_circuit::<E>(128000);
  let (pk, _) = Marlin::<Fr, SonicKZG10<E, P<Fr>>, Blake2s>::index(&srs, c).unwrap();
  let rng = &mut ark_std::test_rng();
  let timer = start_timer!(|| "Proving");
  let _ = Marlin::<Fr, SonicKZG10<E, P<Fr>>, Blake2s>::prove(&pk, c.clone(), rng).unwrap();
  end_timer!(timer);
}

#[test]
fn test_marlin_prover_test_circuit_scale_256000() {
  let (srs, c, _) = computes_universal_parameter_and_circuit::<E>(256000);
  let (pk, _) = Marlin::<Fr, SonicKZG10<E, P<Fr>>, Blake2s>::index(&srs, c).unwrap();
  let rng = &mut ark_std::test_rng();
  let timer = start_timer!(|| "Proving");
  let _ = Marlin::<Fr, SonicKZG10<E, P<Fr>>, Blake2s>::prove(&pk, c.clone(), rng).unwrap();
  end_timer!(timer);
}

#[test]
fn test_marlin_prover_test_circuit_scale_512000() {
  let (srs, c, _) = computes_universal_parameter_and_circuit::<E>(512000);
  let (pk, _) = Marlin::<Fr, SonicKZG10<E, P<Fr>>, Blake2s>::index(&srs, c).unwrap();
  let rng = &mut ark_std::test_rng();
  let timer = start_timer!(|| "Proving");
  let _ = Marlin::<Fr, SonicKZG10<E, P<Fr>>, Blake2s>::prove(&pk, c.clone(), rng).unwrap();
  end_timer!(timer);
}

#[test]
fn test_marlin_prover_test_circuit_scale_1024000() {
  let (srs, c, _) = computes_universal_parameter_and_circuit::<E>(1024000);
  let (pk, _) = Marlin::<Fr, SonicKZG10<E, P<Fr>>, Blake2s>::index(&srs, c).unwrap();
  let rng = &mut ark_std::test_rng();
  let timer = start_timer!(|| "Proving");
  let _ = Marlin::<Fr, SonicKZG10<E, P<Fr>>, Blake2s>::prove(&pk, c.clone(), rng).unwrap();
  end_timer!(timer);
}

#[test]
fn test_marlin_verifier_test_circuit_scale_1000() {
  let (srs, c, x) = computes_universal_parameter_and_circuit::<E>(1000);
  let (pk, vk) = Marlin::<Fr, SonicKZG10<E, P<Fr>>, Blake2s>::index(&srs, c).unwrap();
  let rng = &mut ark_std::test_rng();
  let proof = Marlin::<Fr, SonicKZG10<E, P<Fr>>, Blake2s>::prove(&pk, c.clone(), rng).unwrap();
  let timer = start_timer!(|| "Verifier");
  Marlin::<Fr, SonicKZG10<E, P<Fr>>, Blake2s>::verify(&vk, &x, &proof, rng).unwrap();
  end_timer!(timer);
}

