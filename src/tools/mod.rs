use ark_ff::PrimeField as Field;
use ark_std::{vec, vec::Vec};
use ark_std::{
    rand::RngCore,
    iter::Iterator,
    One, Zero,
};
use ark_poly::{UVPolynomial,
    univariate::DensePolynomial
};
use ark_ec::{msm::VariableBaseMSM, PairingEngine, ProjectiveCurve};
use sha2::{Sha256, Digest};
use crate::{
    error::Error,
    kzg::Commitment
};

pub fn to_field<F: Field>(i: u64) -> F {
    F::from_repr(i.into()).unwrap()
}

pub fn to_int<F: Field>(e: F) -> u64 {
    let digits = e.into_repr().into().to_u64_digits();
    match digits.len() {
        0 => 0,
        1 => digits[0],
        _ => {
            println!("{:?}", digits);
            panic!("Number too big!")
        }
    }
}

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

pub struct PowerVectorIterator<F: Field> {
    _start: u64,
    _end: u64,
    _alpha: F,
    _length: u64,
    _shifted: u64,
    _i: u64,
    _curr: Option<F>,
}

impl<F: Field> Iterator for PowerVectorIterator<F> {
    type Item = F;
    fn next(&mut self) -> Option<F> {
        if self._end <= self._start || self._i >= self._end {
            return None;
        }
        let ret = if self._i < self._shifted || self._i >= self._length + self._shifted {
            Some(F::zero())
        } else if let Some(curr) = self._curr {
            Some(curr)
        } else {
            let curr = power(self._alpha, (self._i - self._shifted) as i64);
            self._curr = Some(curr);
            Some(curr)
        };

        self._i += 1;
        if let Some(curr) = self._curr {
            self._curr = Some(curr * self._alpha);
        }

        ret
    }
}

pub fn power_iter<F: Field>(start: u64, end: u64, alpha: F, length: u64, shifted: u64)
    -> PowerVectorIterator<F> {
    if end <= start {
        panic!("Invalid range");
    }
    PowerVectorIterator {
        _start: start,
        _end: end,
        _alpha: alpha,
        _length: length,
        _shifted: shifted,
        _i: start,
        _curr: None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bls12_381::Fr as F;

    #[test]
    fn test_int_field_transform() {
        for i in 0..1000 {
            assert_eq!(i, to_int::<F>(to_field::<F>(i)));
        }
    }

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

    #[test]
    fn test_power_iterator() {
        assert_eq!(power_iter::<F>(0, 5, F::one(), 3, 0).collect::<Vec<F>>(),
                   vec![F::one(), F::one(), F::one(), F::zero(), F::zero()]);
        assert_eq!(power_iter::<F>(2, 6, to_field(2), 3, 0).collect::<Vec<F>>(),
                   vec![to_field(4), F::zero(), F::zero(), F::zero()]);
        assert_eq!(power_iter::<F>(2, 6, to_field(2), 3, 3).collect::<Vec<F>>(),
                   vec![F::zero(), to_field(1), to_field(2), to_field(4)]);
    }
}
