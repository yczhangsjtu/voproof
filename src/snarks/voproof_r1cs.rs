use ark_ec::PairingEngine;
use ark_std::Zero;
use crate::error::Error;
use crate::kzg::{
    Proof as KZGProof,
    UniversalParams
};
use crate::cs::r1cs::{R1CSSize};
use super::*;

pub struct R1CSProverKey<E: PairingEngine> {
    /*{R1CSProverKey}*/
    pub verifier_key: R1CSVerifierKey<E>,
}

pub struct R1CSVerifierKey<E: PairingEngine> {
    /*{R1CSVerifierKey}*/
    pub comms: Vec<E::G1Affine>, /*{Remove this line}*/
}

pub struct R1CSProof<E: PairingEngine> {
    pub comms: Vec<E::G1Affine>, /*{Remove this line}*/
    pub kzg_proofs: Vec<KZGProof<E>>, /*{Remove this line}*/
}

pub struct VOProofR1CS {}

impl<E: PairingEngine> SNARKProverKey<E> for R1CSProverKey<E> {}

impl<E: PairingEngine> SNARKVerifierKey<E> for R1CSVerifierKey<E> {}

impl<E: PairingEngine> SNARKProof<E> for R1CSProof<E> {}

impl<E: PairingEngine> SNARK<E> for VOProofR1CS {
    type Size = R1CSSize;
    type CS = R1CS<E::Fr>;
    type PK = R1CSProverKey<E>;
    type VK = R1CSVerifierKey<E>;
    type Ins = R1CSInstance<E::Fr>;
    type Wit = R1CSWitness<E::Fr>;
    type Pf = R1CSProof<E>;

    fn setup(size: &R1CSSize) -> UniversalParams<E> {
        UniversalParams::<E>::empty() /*{Remove this line}*/
    }

    fn index(pp: &UniversalParams<E>, r1cs: &R1CS<E::Fr>)
        -> Result<(R1CSProverKey<E>, R1CSVerifierKey<E>), Error> {
        Err(Error::Unimplemented("R1CS index".into())) /*{Remove this line}*/
    }
    fn prove(pk: &Self::PK, x: &Self::Ins, w: &Self::Wit) -> Result<Self::Pf, Error> {
        Err(Error::Unimplemented("R1CS prove".into())) /*{Remove this line}*/
    }
    fn verify(vk: &Self::VK, x: &Self::Ins, proof: &Self::Pf) -> Result<(), Error> {
        Err(Error::Unimplemented("R1CS verify".into())) /*{Remove this line}*/
    }
}

