use ark_ec::PairingEngine;
use ark_ff::fields::PrimeField;
use ark_std::{test_rng, Zero};
use voproof::cs::{pov::*, circuit::fan_in_two::FanInTwoCircuit, ConstraintSystem};
use voproof::error::Error;
use voproof::kzg::UniversalParams;
use voproof::snarks::{voproof_pov::*, SNARK};
use voproof::tools::{to_field, to_int, try_to_int};
use voproof::*;

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
    .evaluate(&vec![to_field::<E::Fr>(1), to_field::<E::Fr>(2), to_field::<E::Fr>(3)])
    .unwrap();
  let ins = POVInstance{ instance: circ.get_instance().unwrap() };
  let wit = POVWitness{ witness: circ.get_witness().unwrap() };
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
  Ok(())
}

#[test]
fn test_simple_pov() {
  assert!(run_pov_example::<ark_bls12_381::Bls12_381>().is_ok());
}
