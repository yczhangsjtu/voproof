pub mod voproof_hpr;
pub mod voproof_pov;
pub mod voproof_r1cs;
// mod template;

use ark_ec::{AffineCurve, PairingEngine, ProjectiveCurve};
use ark_ff::{fields::batch_inversion, FftField, Field, FpParameters, PrimeField};
use ark_poly_commit::UVPolynomial;
use ark_ff::to_bytes;
use crate::cs::{
  r1cs::{R1CSInstance, R1CSSize, R1CSWitness, R1CS},
  CSSize, ConstraintSystem, Instance, Witness,
};
use crate::error::Error;
use crate::kzg::{Proof as KZGProof, UniversalParams, VerifierKey};
use crate::tools::*;
use ark_poly::{Polynomial, univariate::{DensePolynomial as DensePoly}};
use ark_std::{ops::Mul, test_rng, vec::Vec, One, Zero};
use crate::*;
use crate::kzg::*;

pub trait SNARKProverKey<E: PairingEngine> {}
pub trait SNARKVerifierKey<E: PairingEngine> {}
pub trait SNARKProof<E: PairingEngine> {}

// degree_bound can be larger than powers.len() when powers neglect the unused
// items in the middle.
// degree_bound always equals the exponent of the largest power + 1
pub fn vector_to_commitment<E: PairingEngine>(
  powers: &Vec<E::G1Affine>,
  vec: &Vec<E::Fr>,
) -> Result<Commitment<E>, Error> {
  KZG10::<E, DensePoly<E::Fr>>::commit_with_coefficients(&powers[..], vec)
}

pub fn scalar_to_commitment<E: PairingEngine>(
  g: &E::G1Affine,
  c: &E::Fr,
) -> Result<Commitment<E>, Error> {
  KZG10::<E, DensePoly<E::Fr>>::commit_single(g, c)
}

pub trait SNARK<E: PairingEngine> {
  type Size: CSSize;
  type CS: ConstraintSystem<E::Fr, Self::Size>;
  type PK: SNARKProverKey<E>;
  type VK: SNARKVerifierKey<E>;
  type Ins: Instance<E::Fr>;
  type Wit: Witness<E::Fr>;
  type Pf: SNARKProof<E>;

  fn setup(size: usize) -> Result<UniversalParams<E>, Error>;
  fn index(pp: &UniversalParams<E>, cs: &Self::CS) -> Result<(Self::PK, Self::VK), Error>;
  fn prove(pk: &Self::PK, x: &Self::Ins, w: &Self::Wit) -> Result<Self::Pf, Error>;
  fn verify(vk: &Self::VK, x: &Self::Ins, proof: &Self::Pf) -> Result<(), Error>;
}
