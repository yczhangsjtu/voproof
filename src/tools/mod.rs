use ark_ff::PrimeField as Field;
use ark_std::{vec, vec::Vec};
use crate::error::Error;

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
