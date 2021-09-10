mod voproof_r1cs;
mod voproof_hpr;
mod voproof_pov;

use ark_ec::PairingEngine;
use ark_ff::Field;
use crate::kzg::{UniversalParams, Powers, VerifierKey};
use crate::error::Error;
use crate::cs::{
    CSSize, ConstraintSystem, Instance, Witness,
    r1cs::{R1CS, R1CSSize, R1CSInstance, R1CSWitness}
};

pub trait SNARKProverKey<E: PairingEngine> {}
pub trait SNARKVerifierKey<E: PairingEngine> {}
pub trait SNARKProof<E: PairingEngine> {}

pub trait SNARK<'a, E: PairingEngine,
                    Size: CSSize,
                    CS: ConstraintSystem<E::Fr>,
                    PK: SNARKProverKey<E>,
                    VK: SNARKVerifierKey<E>,
                    Ins: Instance<E::Fr>,
                    Wit: Witness<E::Fr>,
                    Pf: SNARKProof<E>> {
    fn setup(size: &Size) -> UniversalParams<E>;
    fn index(pp: &UniversalParams<E>, cs: &CS)
        -> Result<(PK, VK), Error>;
    fn prove(pk: &PK, x: &Ins, w: &Wit) -> Result<Pf, Error>;
    fn verify(vk: &VK, x: &Ins, proof: &Pf) -> Result<(), Error>;
}

pub struct VOProofR1CS<E: PairingEngine> {}

pub struct R1CSProverKey<E: PairingEngine> {
}

pub struct R1CSVerifierKey<E: PairingEngine> {
}

pub struct R1CSProof<E: PairingEngine> {
}

impl<E: PairingEngine> SNARK<E, R1CSSize, R1CS<E::Fr>,
                             R1CSProverKey<E>, R1CSVerifierKey<E>,
                             R1CSInstance<E::Fr>, R1CSWitness<E::Fr>,
                             R1CSProof<E>> for VOProofR1CS<E> {
}

