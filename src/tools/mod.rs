use ark_ff::PrimeField as Field;
use ark_std::{vec, vec::Vec};
use ark_std::rand::RngCore;
use ark_poly::{UVPolynomial,
    univariate::DensePolynomial
};
use ark_ec::{msm::VariableBaseMSM, PairingEngine, ProjectiveCurve};
use sha2::{Sha256, Digest};
use crate::{
    error::Error,
    kzg::Commitment
};

pub fn power<F: Field>(a: F, e: i64) -> F {
    if e < 0 {
        a.pow(&[(-e) as u64])
    } else {
        a.pow(&[e as u64])
    }
}

/// Compute the matrix-vector product using the sparse
/// representation of the matrix, where the row indices
/// and column indices start from 0
pub fn sparse_mvp<F: Field>(
    H: u64, K: u64,
    rows: &Vec<u64>, cols: &Vec<u64>, vals: &Vec<F>,
    right: &Vec<F>) -> Result<Vec<F>, Error> {
    assert!(H > 0);
    assert!(K > 0);
    assert_eq!(right.len(), K as usize);

    let mut res = vec![F::zero(); H as usize];
    for ((r, c), v) in rows.iter().zip(cols).zip(vals) {
        res[r.clone() as usize] += right[c.clone() as usize] * v;
    }
    Ok(res)
}

pub fn sample_field<F: Field, R: RngCore>(rng: &mut R) -> F {
    F::rand(rng)
}

pub fn sample_vec<F: Field, R: RngCore>(rng: &mut R, k: u64) -> Vec<F> {
    let mut res = Vec::new();
    for _ in 0..k {
        res.push(sample_field(rng));
    }
    res
}

pub fn poly_from_vec<F: Field>(v: Vec<F>) -> DensePolynomial<F> {
    DensePolynomial::from_coefficients_vec(v)
}

/// Note: use the macro to_bytes![a, b, c] to convert any collection
/// of elements to a single bytes array, as long as a, b, c implement
/// the ToBytes trait.
pub fn hash_to_field<F: Field>(bytes: Vec<u8>) -> F {
    let mut sha = Sha256::new();
    sha.update(bytes);
    let output = sha.finalize();
    F::from_le_bytes_mod_order(&output)
}

pub fn combine_commits<E: PairingEngine>(
    comms: &Vec<Commitment<E>>, coeffs: &Vec<E::Fr>)
    -> Commitment<E> {
    Commitment{ 
        0: VariableBaseMSM::multi_scalar_mul(
            &comms.iter().map(|x| x.0).collect::<Vec<_>>()[..],
            &coeffs.iter().map(|x| x.into_repr()).collect::<Vec<_>>()[..]).into_affine()
    }
}

pub fn evaluate_sparse<F: Field>(x: F, coeffs: &Vec<F>, indices: &Vec<u64>) -> F {
    coeffs.iter().zip(indices).fold(F::zero(),
        |y, (c, i)| y + c.clone() * power(x, i.clone() as i64))
}

pub fn evaluate_short<F: Field>(x: F, coeffs: &Vec<F>) -> F {
    coeffs.iter().enumerate().fold(F::zero(),
        |y, (i, c)| y + c.clone() * power(x, i.clone() as i64))
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bls12_381::Fr as F;

    #[test]
    fn test_sparse_mvp() {
        let rows = vec![1, 0, 3, 2];
        let cols = vec![0, 1, 2, 3];
        let vals = vec![F::from_repr(1.into()).unwrap(),
                        F::from_repr(3.into()).unwrap(),
                        F::from_repr(2.into()).unwrap(),
                        F::from_repr(5.into()).unwrap()];
        let right = vec![F::from_repr(1.into()).unwrap(),
                         F::from_repr(1.into()).unwrap(),
                         F::from_repr(1.into()).unwrap(),
                         F::from_repr(1.into()).unwrap()];
        let left = sparse_mvp(4, 4, &rows, &cols, &vals, &right).unwrap();
        assert_eq!(left, vec![F::from_repr(3.into()).unwrap(),
                              F::from_repr(1.into()).unwrap(),
                              F::from_repr(5.into()).unwrap(),
                              F::from_repr(2.into()).unwrap()]);
    }
}
