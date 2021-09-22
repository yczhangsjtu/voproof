use super::*;

pub struct __NAME__<F: Field> { /*{Remove this line}*/
    a: F, /*{Remove this line}*/
} /*{Remove this line}*/

impl<F: Field> ConstraintSystem<F, __NAME__Size> for __NAME__<F> {} /*{Remove this line}*/

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

pub struct __NAME__ProverKey<'a, E: PairingEngine> {
    pub verifier_key: __NAME__VerifierKey<E>,
    pub powers: Powers<'a, E>,
    pub max_degree: u64,
    /*{ProverKey}*/
}

pub struct __NAME__VerifierKey<E: PairingEngine> {
    pub comms: Vec<E::G1Affine>, /*{Remove this line}*/
    /*{VerifierKey}*/
    pub kzg_vk: VerifierKey<E>,
    pub size: __NAME__Size,
}

pub struct __NAME__Proof<E: PairingEngine> {
    /*{Proof}*/
    pub comms: Vec<E::G1Affine>, /*{Remove this line}*/
    pub kzg_proofs: Vec<KZGProof<E>>, /*{Remove this line}*/
}

pub struct VOProof__NAME__ {}

impl<'a, E: PairingEngine> SNARKProverKey<E> for __NAME__ProverKey<'a, E> {}

impl<E: PairingEngine> SNARKVerifierKey<E> for __NAME__VerifierKey<E> {}

impl<E: PairingEngine> SNARKProof<E> for __NAME__Proof<E> {}

impl VOProof__NAME__ {
    fn get_max_degree(size: &__NAME__Size) -> usize {
        /*{size}*/
        0 /*{Remove this line}*/
    }
}

impl<'a, E: PairingEngine, F: Field> SNARK<E, F> for VOProof__NAME__ {
    type Size = __NAME__Size;
    type CS = __NAME__<E::Fr>;
    type PK = __NAME__ProverKey<'a, E>;
    type VK = __NAME__VerifierKey<E>;
    type Ins = __NAME__Instance<E::Fr>;
    type Wit = __NAME__Witness<E::Fr>;
    type Pf = __NAME__Proof<E>;

    fn setup(size: usize) -> UniversalParams<E> {
        KZG10::<E, DensePoly<E::Fr>>::setup(size)
    }

    fn index(pp: &UniversalParams<E>, cs: &__NAME__<F>)
        -> Result<(__NAME__ProverKey<'a, E>, __NAME__VerifierKey<E>), Error> {
        let max_degree = Self::get_max_degree(cs.get_size());
        assert!(pp.powers_of_g.len() > max_degree);

        let mut powers_of_g = Vec::new();
        // The prover needs both the lowest `max_degree` powers of g,
        // and the highest `max_degree` powers of g, to make sure that
        // some polynomials are bounded by particular degree bounds
        // To save space, store all the needed powers of g in the same
        // vector, because the lower part and the higher part may share
        // common powers of g.
        if pp.powers_of_g.len() >= 2 * (max_degree + 1) {
            powers_of_g = pp.powers_of_g[..=max_degree].to_vec();
            powers_of_g.append(pp.powers_of_g[pp.powers_of_g.len()-max_degree-1..]);
        } else {
            powers_of_g = pp.powers_of_g[..].to_vec();
        }
        let size = cs.get_size();
        /*{index}*/
        let verifier_key = __NAME__VerifierKey::<E> {
            /*{index verifier key}*/
            kzg_vk: VerifierKey {
                g: pp.powers_of_g[0],
                h: pp.h,
                beta_h: pp.beta_h,
                prepared_h: pp.prepared_h.clone(),
                prepared_beta_h: pp.prepared_beta_h.clone(),
            },
            size,
        };
        Ok((__NAME__ProverKey::<E> {
            verifier_key,
            powers: powers_of_g,
            max_degree,
            /*{index prover key}*/
        }, verifier_key))
    }
    fn prove(pk: &Self::PK, x: &Self::Ins, w: &Self::Wit) -> Result<Self::Pf, Error> {
        let size = pk.verifier_key.size;
        let rng = &mut test_rng();
        /*{prove}*/
        Ok(__NAME__Proof::<E> {
            /*{proof}*/
        })
    }
    fn verify(vk: &Self::VK, x: &Self::Ins, proof: &Self::Pf) -> Result<(), Error> {
        let size = vk.size;
        /*{verify}*/
        Err(Error::Unimplemented("__NAME__ verify".into())) /*{Remove this line}*/
    }
}

