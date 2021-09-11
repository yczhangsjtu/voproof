///! This file is generated automatically
use super::*;

pub struct __NAME__<F: Field> { /*{Remove this line}*/
    a: F, /*{Remove this line}*/
} /*{Remove this line}*/

impl<F: Field> ConstraintSystem<F> for __NAME__<F> {} /*{Remove this line}*/

pub struct __NAME__Size {} /*{Remove this line}*/

impl CSSize for __NAME__Size {} /*{Remove this line}*/

pub struct __NAME__Instance<F: Field> { /*{Remove this line}*/
    a: F, /*{Remove this line}*/
} /*{Remove this line}*/

pub struct __NAME__Witness<F: Field> { /*{Remove this line}*/
    a: F, /*{Remove this line}*/
} /*{Remove this line}*/

impl<F: Field> Instance<F> for __NAME__Instance<F> {} /*{Remove this line}*/
impl<F: Field> Witness<F> for __NAME__Witness<F> {} /*{Remove this line}*/

pub struct __NAME__ProverKey<E: PairingEngine> {
    /*{ProverKey}*/
    pub verifier_key: __NAME__VerifierKey<E>,
}

pub struct __NAME__VerifierKey<E: PairingEngine> {
    /*{VerifierKey}*/
    pub comms: Vec<E::G1Affine>, /*{Remove this line}*/
}

pub struct __NAME__Proof<E: PairingEngine> {
    pub comms: Vec<E::G1Affine>, /*{Remove this line}*/
    pub kzg_proofs: Vec<KZGProof<E>>, /*{Remove this line}*/
}

pub struct VOProof__NAME__ {}

impl<E: PairingEngine> SNARKProverKey<E> for __NAME__ProverKey<E> {}

impl<E: PairingEngine> SNARKVerifierKey<E> for __NAME__VerifierKey<E> {}

impl<E: PairingEngine> SNARKProof<E> for __NAME__Proof<E> {}

impl<E: PairingEngine> SNARK<E> for VOProof__NAME__ {
    type Size = __NAME__Size;
    type CS = __NAME__<E::Fr>;
    type PK = __NAME__ProverKey<E>;
    type VK = __NAME__VerifierKey<E>;
    type Ins = __NAME__Instance<E::Fr>;
    type Wit = __NAME__Witness<E::Fr>;
    type Pf = __NAME__Proof<E>;

    fn setup(size: &__NAME__Size) -> UniversalParams<E> {
        /*{setup}*/
        UniversalParams::<E>::empty() /*{Remove this line}*/
    }

    fn index(pp: &UniversalParams<E>, cs: &__NAME__<E::Fr>)
        -> Result<(__NAME__ProverKey<E>, __NAME__VerifierKey<E>), Error> {
        /*{index}*/
        Err(Error::Unimplemented("__NAME__ index".into())) /*{Remove this line}*/
    }
    fn prove(pk: &Self::PK, x: &Self::Ins, w: &Self::Wit) -> Result<Self::Pf, Error> {
        /*{prove}*/
        Err(Error::Unimplemented("__NAME__ prove".into())) /*{Remove this line}*/
    }
    fn verify(vk: &Self::VK, x: &Self::Ins, proof: &Self::Pf) -> Result<(), Error> {
        /*{verify}*/
        Err(Error::Unimplemented("__NAME__ verify".into())) /*{Remove this line}*/
    }
}

