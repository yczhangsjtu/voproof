use ark_crypto_primitives::{
  crh::{
    poseidon::{
      CRH,
      {
        constraints::{CRHGadget, TwoToOneCRHGadget},
        TwoToOneCRH,
      },
    },
    TwoToOneCRHScheme, TwoToOneCRHSchemeGadget,
  },
  merkle_tree::{constraints::ConfigGadget, Config, IdentityDigestConverter},
  CRHScheme, CRHSchemeGadget, Path, PathVar,
};
use ark_ec::PairingEngine;
use ark_ff::fields::{FftField, Field, FpParameters, PrimeField};
use ark_r1cs_std::{alloc::AllocVar, fields::fp::FpVar, uint64::UInt64, R1CSVar};
use ark_relations::{
  lc, ns,
  r1cs::{
    ConstraintSynthesizer, ConstraintSystem as ArkR1CS, ConstraintSystemRef, SynthesisError,
    Variable,
  },
};
use ark_sponge::Absorb;
use ark_std::{end_timer, rc::Rc, start_timer};
use voproof::cs::{
  r1cs::{R1CSInstance, R1CSWitness, R1CS},
  ConstraintSystem,
};
use voproof::error::Error;
use voproof::kzg::UniversalParams;
use voproof::snarks::{voproof_r1cs::*, voproof_r1cs_prover_efficient::*, SNARK};
use voproof::*;

mod utils;
// use voproof::kzg::{KZG10, UniversalParams, Powers, VerifierKey, Randomness};
//

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

fn run_r1cs_example<E: PairingEngine>(scale: usize) -> Result<(), Error> {
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
  // println!("R1CS A row indices: {:?}", r1cs.arows);
  // println!("R1CS A col indices: {:?}", r1cs.acols);
  // println!("R1CS A vals: {:?}", to_int!(r1cs.avals));
  // println!("R1CS B row indices: {:?}", r1cs.brows);
  // println!("R1CS B col indices: {:?}", r1cs.bcols);
  // println!("R1CS B vals: {:?}", to_int!(r1cs.bvals));
  // println!("R1CS C row indices: {:?}", r1cs.crows);
  // println!("R1CS C col indices: {:?}", r1cs.ccols);
  // println!("R1CS C vals: {:?}", to_int!(r1cs.cvals));

  let instance = R1CSInstance { instance: x };
  let witness = R1CSWitness { witness: w };

  if r1cs.satisfy(&instance, &witness) {
    println!("R1CS satisfied!");
  } else {
    println!("R1CS unsatisfied!");
  }

  let max_degree = VOProofR1CS::get_max_degree(r1cs.get_size());
  // Let the universal parameters take a larger size than expected
  let timer = start_timer!(|| "Universal setup");
  let universal_params: UniversalParams<E> = VOProofR1CS::setup(max_degree + 10).unwrap();
  end_timer!(timer);
  // println!(
  // "Universal parameter size: {}",
  // universal_params.powers_of_g.len()
  // );
  let timer = start_timer!(|| "Indexing");
  let (pk, vk) = VOProofR1CS::index(&universal_params, &r1cs).unwrap();
  end_timer!(timer);
  // println!("Degree bound: {}", vk.degree_bound);
  // println!("Max degree: {}", pk.max_degree);
  // println!("Prover key matrix size: {}", pk.cap_m_mat.0.len());
  // println!("Prover key u size: {}", pk.u_vec.len());
  // println!("Prover key v size: {}", pk.v_vec.len());
  // println!("Prover key w size: {}", pk.w_vec.len());
  //
  // println!("M A row indices: {:?}", pk.cap_m_mat.0);
  // println!("M A col indices: {:?}", pk.cap_m_mat.1);
  // println!("M A vals: {:?}", to_int!(pk.cap_m_mat.2));
  // let vksize = vk.size.clone();
  // println!("H: {}", vksize.nrows);
  // println!("K: {}", vksize.ncols);

  let timer = start_timer!(|| "Proving");
  let proof = VOProofR1CS::prove(&pk, &instance, &witness)?;
  end_timer!(timer);
  let timer = start_timer!(|| "Verifying");
  let ret = VOProofR1CS::verify(&vk, &instance, &proof);
  end_timer!(timer);
  ret
}

fn run_r1cs_pe_example<E: PairingEngine>(scale: usize) -> Result<(), Error> {
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
  // println!("R1CS A row indices: {:?}", r1cs.arows);
  // println!("R1CS A col indices: {:?}", r1cs.acols);
  // println!("R1CS A vals: {:?}", to_int!(r1cs.avals));
  // println!("R1CS B row indices: {:?}", r1cs.brows);
  // println!("R1CS B col indices: {:?}", r1cs.bcols);
  // println!("R1CS B vals: {:?}", to_int!(r1cs.bvals));
  // println!("R1CS C row indices: {:?}", r1cs.crows);
  // println!("R1CS C col indices: {:?}", r1cs.ccols);
  // println!("R1CS C vals: {:?}", to_int!(r1cs.cvals));

  let instance = R1CSInstance { instance: x };
  let witness = R1CSWitness { witness: w };

  if r1cs.satisfy(&instance, &witness) {
    println!("R1CS satisfied!");
  } else {
    println!("R1CS unsatisfied!");
  }

  let max_degree = VOProofR1CSProverEfficient::get_max_degree(r1cs.get_size());
  // Let the universal parameters take a larger size than expected
  let timer = start_timer!(|| "Universal setup");
  let universal_params: UniversalParams<E> =
    VOProofR1CSProverEfficient::setup(max_degree + 10).unwrap();
  end_timer!(timer);
  // println!(
  // "Universal parameter size: {}",
  // universal_params.powers_of_g.len()
  // );
  let timer = start_timer!(|| "Indexing");
  let (pk, vk) = VOProofR1CSProverEfficient::index(&universal_params, &r1cs).unwrap();
  end_timer!(timer);
  // println!("Degree bound: {}", vk.degree_bound);
  // println!("Max degree: {}", pk.max_degree);
  // println!("Prover key matrix size: {}", pk.cap_m_mat.0.len());
  // println!("Prover key u size: {}", pk.u_vec.len());
  // println!("Prover key v size: {}", pk.v_vec.len());
  // println!("Prover key w size: {}", pk.w_vec.len());
  //
  // println!("M A row indices: {:?}", pk.cap_m_mat.0);
  // println!("M A col indices: {:?}", pk.cap_m_mat.1);
  // println!("M A vals: {:?}", to_int!(pk.cap_m_mat.2));
  // let vksize = vk.size.clone();
  // println!("H: {}", vksize.nrows);
  // println!("K: {}", vksize.ncols);

  let timer = start_timer!(|| "Proving");
  let proof = VOProofR1CSProverEfficient::prove(&pk, &instance, &witness)?;
  end_timer!(timer);
  let timer = start_timer!(|| "Verifying");
  let ret = VOProofR1CSProverEfficient::verify(&vk, &instance, &proof);
  end_timer!(timer);
  ret
}

macro_rules! define_test_small_scale {
  ($func_name:ident, $exec_name:ident) => {
    #[test]
    fn $func_name() {
      let result = $exec_name::<ark_bls12_381::Bls12_381>(5);
      if !result.is_ok() {
        if let Err(Error::VectorNotEqual(info)) = result {
          println!("{}", info);
        } else {
          println!("{:?}", result);
        }
        assert!(false);
      }
      $exec_name::<ark_bls12_381::Bls12_381>(10).unwrap();
      $exec_name::<ark_bls12_381::Bls12_381>(15).unwrap();
      $exec_name::<ark_bls12_381::Bls12_381>(20).unwrap();
    }
  };
}

define_test_small_scale!(test_simple_r1cs_small_scales, run_r1cs_example);
define_test_small_scale!(test_simple_r1cs_pe_small_scales, run_r1cs_pe_example);

macro_rules! define_test_large_scale {
  ($func_name: ident, $exec_name: ident, $scale: literal) => {
    #[test]
    fn $func_name() {
      assert!($exec_name::<ark_bls12_381::Bls12_381>($scale).is_ok());
    }
  };
}

define_test_large_scale!(test_simple_r1cs_large_scale_1000, run_r1cs_example, 1000);
define_test_large_scale!(test_simple_r1cs_large_scale_2000, run_r1cs_example, 2000);
define_test_large_scale!(test_simple_r1cs_large_scale_4000, run_r1cs_example, 4000);
define_test_large_scale!(test_simple_r1cs_large_scale_8000, run_r1cs_example, 8000);
define_test_large_scale!(test_simple_r1cs_large_scale_16000, run_r1cs_example, 16000);
define_test_large_scale!(test_simple_r1cs_large_scale_32000, run_r1cs_example, 32000);
define_test_large_scale!(test_simple_r1cs_large_scale_64000, run_r1cs_example, 64000);
define_test_large_scale!(
  test_simple_r1cs_large_scale_128000,
  run_r1cs_example,
  128000
);
define_test_large_scale!(
  test_simple_r1cs_large_scale_256000,
  run_r1cs_example,
  256000
);
define_test_large_scale!(
  test_simple_r1cs_large_scale_512000,
  run_r1cs_example,
  512000
);
define_test_large_scale!(
  test_simple_r1cs_large_scale_1024000,
  run_r1cs_example,
  1024000
);
define_test_large_scale!(
  test_simple_r1cs_pe_large_scale_1000,
  run_r1cs_pe_example,
  1000
);
define_test_large_scale!(
  test_simple_r1cs_pe_large_scale_2000,
  run_r1cs_pe_example,
  2000
);
define_test_large_scale!(
  test_simple_r1cs_pe_large_scale_4000,
  run_r1cs_pe_example,
  4000
);
define_test_large_scale!(
  test_simple_r1cs_pe_large_scale_8000,
  run_r1cs_pe_example,
  8000
);
define_test_large_scale!(
  test_simple_r1cs_pe_large_scale_16000,
  run_r1cs_pe_example,
  16000
);
define_test_large_scale!(
  test_simple_r1cs_pe_large_scale_32000,
  run_r1cs_pe_example,
  32000
);
define_test_large_scale!(
  test_simple_r1cs_pe_large_scale_64000,
  run_r1cs_pe_example,
  64000
);
define_test_large_scale!(
  test_simple_r1cs_pe_large_scale_128000,
  run_r1cs_pe_example,
  128000
);
define_test_large_scale!(
  test_simple_r1cs_pe_large_scale_256000,
  run_r1cs_pe_example,
  256000
);
define_test_large_scale!(
  test_simple_r1cs_pe_large_scale_512000,
  run_r1cs_pe_example,
  512000
);
define_test_large_scale!(
  test_simple_r1cs_pe_large_scale_1024000,
  run_r1cs_pe_example,
  1024000
);

type F = ark_bls12_381::Fr;
type E = ark_bls12_381::Bls12_381;
struct FieldMTConfig;
impl Config for FieldMTConfig {
  type Leaf = [F];
  type LeafDigest = F;
  type LeafInnerDigestConverter = IdentityDigestConverter<F>;
  type InnerDigest = F;
  type LeafHash = CRH<F>;
  type TwoToOneHash = TwoToOneCRH<F>;
}

struct FieldMTConfigVar;
impl ConfigGadget<FieldMTConfig, F> for FieldMTConfigVar {
  type Leaf = [FpVar<F>];
  type LeafDigest = FpVar<F>;
  type LeafInnerConverter = IdentityDigestConverter<FpVar<F>>;
  type InnerDigest = FpVar<F>;
  type LeafHash = CRHGadget<F>;
  type TwoToOneHash = TwoToOneCRHGadget<F>;
}

#[derive(Copy, Clone)]
struct MerkleTreeCircuit {
  pub height: usize,
}

impl ConstraintSynthesizer<F> for MerkleTreeCircuit {
  fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> Result<(), SynthesisError> {
    let generator: F =
      F::from_repr(<<<E as PairingEngine>::Fr as FftField>::FftParams as FpParameters>::GENERATOR)
        .unwrap();
    let leaf_crh_params = utils::poseidon_parameters();
    let two_to_one_params = leaf_crh_params.clone();
    let mut path = Path::<FieldMTConfig> {
      leaf_sibling_hash: generator,
      auth_path: vec![generator; self.height],
      leaf_index: 0,
    };
    let leaf = vec![generator];
    let mut curr = CRH::<F>::evaluate(&leaf_crh_params, leaf.clone()).unwrap();
    curr = TwoToOneCRH::<F>::evaluate(&two_to_one_params, &curr, &path.leaf_sibling_hash).unwrap();
    for node in path.auth_path.iter() {
      curr = TwoToOneCRH::<F>::evaluate(&two_to_one_params, &curr, &node).unwrap();
    }
    let root = curr;
    assert!(path
      .verify(&leaf_crh_params, &two_to_one_params, &root, leaf.clone())
      .unwrap());

    let root = FpVar::new_input(cs.clone(), || Ok(root)).unwrap();
    let constraints_from_digest = cs.num_constraints();
    println!("constraints from digest: {}", constraints_from_digest);

    let leaf_crh_params_var =
      <CRHGadget<F> as CRHSchemeGadget<CRH<F>, _>>::ParametersVar::new_constant(
        ns!(cs, "leaf_crh_params"),
        &leaf_crh_params,
      )
      .unwrap();

    let two_to_one_crh_params_var = <TwoToOneCRHGadget<F> as TwoToOneCRHSchemeGadget<
      TwoToOneCRH<F>,
      _,
    >>::ParametersVar::new_constant(
      ns!(cs, "two_to_one_params"), &leaf_crh_params
    )
    .unwrap();

    let leaf_g: Vec<_> = leaf
      .iter()
      .map(|x| FpVar::new_input(cs.clone(), || Ok(*x)).unwrap())
      .collect();

    let mut cw =
      PathVar::<FieldMTConfig, F, FieldMTConfigVar>::new_witness(ns!(cs, "new_witness"), || {
        Ok(&path)
      })
      .unwrap();

    assert!(cs.is_satisfied().unwrap());

    let leaf_pos = UInt64::new_witness(cs.clone(), || Ok(0))
      .unwrap()
      .to_bits_le();
    cw.set_leaf_position(leaf_pos.clone());

    let expected_leaf_pos = leaf_pos.value().unwrap();
    let mut actual_leaf_pos = cw.get_leaf_position().value().unwrap();
    actual_leaf_pos.extend((0..(64 - actual_leaf_pos.len())).map(|_| false));
    assert_eq!(expected_leaf_pos, actual_leaf_pos);

    assert!(cw
      .verify_membership(
        &leaf_crh_params_var,
        &two_to_one_crh_params_var,
        &root,
        &leaf_g
      )
      .unwrap()
      .value()
      .unwrap());

    assert!(
      cs.is_satisfied().unwrap(),
      "verification constraints not satisfied"
    );

    println!("number of public inputs {}", cs.num_instance_variables());

    println!("number of witness {}", cs.num_witness_variables());
    Ok(())
  }
}

fn run_r1cs_mt_example(height: u32) -> Result<(), Error> {
  let c = MerkleTreeCircuit {
    height: height as usize,
  };
  let cs = ArkR1CS::<F>::new_ref();
  c.generate_constraints(cs.clone()).unwrap();
  let cs = cs.into_inner().unwrap();
  let x = cs
    .instance_assignment
    .iter()
    .skip(1)
    .map(|x| *x)
    .collect::<Vec<F>>();
  let w = cs.witness_assignment.clone();
  let r1cs = R1CS::from(cs);
  println!("R1CS num rows: {}", r1cs.nrows);
  println!("R1CS num cols: {}", r1cs.ncols);
  println!("R1CS num inputs: {}", r1cs.input_size);
  println!("Instance size: {}", x.len());
  println!("Witness size: {}", w.len());
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

  let max_degree = VOProofR1CS::get_max_degree(r1cs.get_size());
  // Let the universal parameters take a larger size than expected
  let timer = start_timer!(|| "Universal setup");
  let universal_params: UniversalParams<E> = VOProofR1CS::setup(max_degree + 10).unwrap();
  end_timer!(timer);
  // println!(
  // "Universal parameter size: {}",
  // universal_params.powers_of_g.len()
  // );
  let timer = start_timer!(|| "Indexing");
  let (pk, vk) = VOProofR1CS::index(&universal_params, &r1cs).unwrap();
  end_timer!(timer);
  // println!("Degree bound: {}", vk.degree_bound);
  // println!("Max degree: {}", pk.max_degree);
  // println!("Prover key matrix size: {}", pk.cap_m_mat.0.len());
  // println!("Prover key u size: {}", pk.u_vec.len());
  // println!("Prover key v size: {}", pk.v_vec.len());
  // println!("Prover key w size: {}", pk.w_vec.len());
  //
  // println!("M A row indices: {:?}", pk.cap_m_mat.0);
  // println!("M A col indices: {:?}", pk.cap_m_mat.1);
  // println!("M A vals: {:?}", to_int!(pk.cap_m_mat.2));
  // let vksize = vk.size.clone();
  // println!("H: {}", vksize.nrows);
  // println!("K: {}", vksize.ncols);

  let timer = start_timer!(|| "Proving");
  let proof = VOProofR1CS::prove(&pk, &instance, &witness)?;
  end_timer!(timer);
  let timer = start_timer!(|| "Verifying");
  let ret = VOProofR1CS::verify(&vk, &instance, &proof);
  end_timer!(timer);
  ret
}

#[test]
fn test_r1cs_mt() {
  run_r1cs_mt_example(10).unwrap();
  run_r1cs_mt_example(20).unwrap();
  run_r1cs_mt_example(30).unwrap();
  run_r1cs_mt_example(40).unwrap();
  run_r1cs_mt_example(50).unwrap();
  run_r1cs_mt_example(60).unwrap();
}
