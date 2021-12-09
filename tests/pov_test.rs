use ark_ff::{PrimeField, FftField, FpParameters};
use ark_ec::PairingEngine;
use ark_std::Zero;
use voproof::cs::{circuit::fan_in_two::FanInTwoCircuit, pov::*, r1cs::*, ConstraintSystem};
use ark_relations::{
  lc, ns,
  r1cs::{
    ConstraintSynthesizer, ConstraintSystem as ArkR1CS, ConstraintSystemRef, SynthesisError,
    Variable,
  },
};
use voproof::error::Error;
use voproof::kzg::UniversalParams;
use voproof::snarks::{voproof_pov::*, SNARK};
use voproof::tools::{to_field, try_to_int};
use voproof::*;
mod utils;
use utils::test_circuit::TestCircuit;

fn run_pov_example<E: PairingEngine>() -> Result<(), Error> {
  let mut circ = FanInTwoCircuit::<E::Fr>::new();
  let a = circ.add_global_input_variable().unwrap();
  let b = circ.add_global_input_variable().unwrap();
  let c = circ.add_global_input_variable().unwrap();
  let d = circ.add_vars(&a, &b);
  let e = circ.mul_vars(&b, &c);
  let f = circ.mul_vars(&d, &e);
  let g = circ.add_vars(&a, &d);
  let h = circ.mul_vars(&g, &f);
  let o = circ.const_var(to_field::<E::Fr>(10));
  let p = circ.mul_vars(&h, &o);
  circ.mark_as_complete().unwrap();
  circ.mark_variable_as_public(&a).unwrap();
  circ.mark_variable_as_public(&p).unwrap();
  circ
    .evaluate(&vec![
      to_field::<E::Fr>(1),
      to_field::<E::Fr>(2),
      to_field::<E::Fr>(3),
    ])
    .unwrap();
  let ins = POVInstance {
    instance: circ.get_instance().unwrap(),
  };
  let mut wit = POVWitness {
    witness: circ.get_witness().unwrap(),
  };
  println!("{:?}", ins.instance.0);
  println!("{}", fmt_ff_vector!(ins.instance.1));
  println!("{}", fmt_ff_vector!(wit.witness.0));
  println!("{}", fmt_ff_vector!(wit.witness.1));
  println!("{}", fmt_ff_vector!(wit.witness.2));
  println!("{:?}", circ.get_wiring());
  assert_eq!(circ.get_add_num(), 2);
  assert_eq!(circ.get_mul_num(), 4);
  assert_eq!(circ.get_const_num(), 1);
  assert_eq!(wit.witness.0.len(), 7);
  assert_eq!(wit.witness.1.len(), 7);
  assert_eq!(wit.witness.2.len(), 7);
  let pov = POV::from(circ);
  assert!(pov.satisfy(&ins, &wit));
  let max_degree = VOProofPOV::get_max_degree(pov.get_size());
  // Let the universal parameters take a larger size than expected
  let universal_params: UniversalParams<E> = VOProofPOV::setup(max_degree + 10).unwrap();
  println!(
    "Universal parameter size: {}",
    universal_params.powers_of_g.len()
  );
  let (pk, vk) = VOProofPOV::index(&universal_params, &pov).unwrap();
  println!("Degree bound: {}", vk.degree_bound);
  println!("Max degree: {}", pk.max_degree);
  println!("Prover key sigma size: {}", pk.sigma_vec.len());
  println!("Prover key d size: {}", pk.d_vec.len());

  let mut proof = VOProofPOV::prove(&pk, &ins, &wit)?;
  VOProofPOV::verify(&vk, &ins, &proof)?;
  proof.y = E::Fr::zero();
  let result = VOProofPOV::verify(&vk, &ins, &proof);
  assert!(result.is_err());
  wit.witness.0[0] = E::Fr::zero();
  let result = VOProofPOV::prove(&pk, &ins, &wit);
  assert!(result.is_err());
  Ok(())
}

#[test]
fn test_simple_pov() {
  assert!(run_pov_example::<ark_bls12_381::Bls12_381>().is_ok());
}

fn run_pov_from_r1cs<E: PairingEngine>(scale: usize) {
  let c = TestCircuit::<E::Fr> {
    a: Some(generator_of!(E)),
    b: Some(generator_of!(E) * generator_of!(E)),
    num_variables: scale,
    num_constraints: scale,
  };
  let x = vec![c.a.unwrap(), c.b.unwrap(), (c.a.unwrap() * c.b.unwrap())];
  let w = vec![c.a.unwrap(); scale - 3];

  let cs = ArkR1CS::<E::Fr>::new_ref();
  c.generate_constraints(cs.clone()).unwrap();
  let r1cs = R1CS::from(cs.into_inner().unwrap());
  println!("R1CS num rows: {}", r1cs.nrows);
  println!("R1CS num cols: {}", r1cs.ncols);
  println!(
    "R1CS non entries: {}, {}, {} (total {}, max {})",
    r1cs.arows.len(),
    r1cs.brows.len(),
    r1cs.crows.len(),
    r1cs.arows.len() + r1cs.brows.len() + r1cs.crows.len(),
    max!(r1cs.arows.len(), r1cs.brows.len(), r1cs.crows.len())
  );

  let instance = R1CSInstance { instance: x };
  let witness = R1CSWitness { witness: w };

  if r1cs.satisfy(&instance, &witness) {
    println!("R1CS satisfied!");
  } else {
    println!("R1CS unsatisfied!");
  }

  let (pov, instance, witness) = pov_triple_from_r1cs_triple(r1cs, instance, witness);
  assert!(pov.satisfy_gate_logics(&witness));
  assert!(pov.satisfy_wiring(&witness));
  assert!(witness.satisfy_instance(&instance));
}

#[test]
fn test_pov_from_r1cs() {
  run_pov_from_r1cs::<ark_bls12_381::Bls12_381>(5);
}
