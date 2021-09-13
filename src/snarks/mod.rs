mod voproof_r1cs;
mod voproof_hpr;
mod voproof_pov;
mod template;

use ark_ec::PairingEngine;
use ark_ff::PrimeField as Field;
use ark_poly::univariate::DensePolynomial as DensePoly;
use ark_std::{test_rng, Zero};
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
use crate::kzg::*;

pub trait SNARKProverKey<E: PairingEngine> {}
pub trait SNARKVerifierKey<E: PairingEngine> {}
pub trait SNARKProof<E: PairingEngine> {}

pub trait SNARK<E: PairingEngine, F: Field> {
    type Size: CSSize;
    type CS: ConstraintSystem<E::Fr>;
    type PK: SNARKProverKey<E>;
    type VK: SNARKVerifierKey<E>;
    type Ins: Instance<E::Fr>;
    type Wit: Witness<E::Fr>;
    type Pf: SNARKProof<E>;

    fn setup(size: &Self::Size) -> UniversalParams<E>;
    fn index(pp: &UniversalParams<E>, cs: &Self::CS)
        -> Result<(Self::PK, Self::VK), Error>;
    fn prove(pk: &Self::PK, x: &Self::Ins, w: &Self::Wit) -> Result<Self::Pf, Error>;
    fn verify(vk: &Self::VK, x: &Self::Ins, proof: &Self::Pf) -> Result<(), Error>;
}

