mod voproof_r1cs;
mod voproof_hpr;
mod voproof_pov;
// mod template;

use ark_ec::PairingEngine;
use ark_ff::{
    PrimeField as Field,
    fields::batch_inversion
};
#[macro_use]
use ark_ff::to_bytes;
use ark_poly::univariate::DensePolynomial as DensePoly;
use ark_std::{test_rng, Zero, vec::Vec};
use crate::kzg::{
    UniversalParams, Powers, VerifierKey,
    Proof as KZGProof
};
use crate::error::Error;
use crate::cs::{
    CSSize, ConstraintSystem, Instance, Witness,
    r1cs::{R1CS, R1CSSize, R1CSInstance, R1CSWitness}
};
use crate::tools::*;
#[macro_use]
use crate::*;
use crate::kzg::*;

pub trait SNARKProverKey<E: PairingEngine> {}
pub trait SNARKVerifierKey<E: PairingEngine> {}
pub trait SNARKProof<E: PairingEngine> {}

pub fn vector_to_commitment<E: PairingEngine>(powers: &Powers<E>, vec: &Vec<E::Fr>)
        -> Result<Commitment<E>, Error> {
    KZG10::<E, DensePoly<E::Fr>>::commit_with_coefficients(powers, vec)
}

pub fn scalar_to_commitment<E: PairingEngine>(g: &E::G1Affine, c: &E::Fr)
        -> Result<Commitment<E>, Error> {
    KZG10::<E, DensePoly<E::Fr>>::commit_single(g, c)
}

pub trait SNARK<'a, E: PairingEngine, F: Field> {
    type Size: CSSize;
    type CS: ConstraintSystem<E::Fr, Self::Size>;
    type PK: SNARKProverKey<E>;
    type VK: SNARKVerifierKey<E>;
    type Ins: Instance<E::Fr>;
    type Wit: Witness<E::Fr>;
    type Pf: SNARKProof<E>;

    fn setup(size: usize) -> Result<UniversalParams<E>, Error>;
    fn index(pp: &UniversalParams<E>, cs: &Self::CS)
        -> Result<(Self::PK, Self::VK), Error>;
    fn prove(pk: &Self::PK, x: &Self::Ins, w: &Self::Wit) -> Result<Self::Pf, Error>;
    fn verify(vk: &Self::VK, x: &Self::Ins, proof: &Self::Pf) -> Result<(), Error>;
}

