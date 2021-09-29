use ark_ff::{
    PrimeField as Field
};
use ark_std::{vec, vec::Vec};
use ark_std::{
    rand::RngCore,
    iter::Iterator,
    One, Zero, ops::Mul
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

pub struct FixedLengthVectorIterator<'a, F: Field> {
    v: &'a Vec<F>,
    i: usize,
    n: usize,
}

impl<'a, F: Field> Iterator for FixedLengthVectorIterator<'a, F> {
    type Item = F;
    fn next(&mut self) -> Option<F> {
        match self.i {
            i if i >= 0 && i < self.v.len() => Some(self.v[i]),
            i if i >= self.v.len() && i < self.n => Some(F::zero()),
            _ => None,
        }
    }
}

pub fn fixed_length_vector_iter<'a, F: Field>(v: &'a Vec<F>, n: usize) -> FixedLengthVectorIterator<'a, F> {
    FixedLengthVectorIterator {
        v, i: 0, n,
    }
}

#[macro_export]
macro_rules! to_int {
    ( $v: expr) => {
        $v.iter().map(|e| to_int::<F>(*e)).collect::<Vec<_>>()
    };
}

#[macro_export]
macro_rules! to_field {
    ( $v: expr) => {
        $v.iter().map(|e| to_field::<F>(*e)).collect::<Vec<_>>()
    };
}

#[macro_export]
macro_rules! define_vec {
    ( $v: ident, $expr: expr ) => {
        let $v: Vec<F> = $expr;
    };
}

#[macro_export]
macro_rules! delta {
    ( $i: expr, $j: expr ) => {
        {
            if $i == $j {
                F::one()
            } else {
                F::zero()
            }
        }
    };
}

#[macro_export]
macro_rules! multi_delta {
    ( $i: expr, $( $c:expr, $j:expr ),+ ) => {
        {
            let mut s = F::zero();
            $( s = s + $c * delta!($i, $j); )+
            s
        }
    };
}

#[macro_export]
macro_rules! linear_combination {
    ( $i: expr ) => {
        linear_combination!($i, )
    };

    ( $i: expr, $( $c:expr, $j:expr ),* ) => {
        {
            let mut s = $i;
            $( s = s + $c * $j; )*
            s
        }
    };
}

#[macro_export]
macro_rules! power_linear_combination {
    ( $alpha: expr, $( $a:expr ),+ ) => {
        {
            let mut s = F::zero();
            let mut c = F::one();
            $(
                s = s + c * $a;
                c = c * $alpha;
            )+
            s
        }
    };
}

#[macro_export]
macro_rules! vector_index {
    ( $v: expr, $i: expr ) => {
        {
            if $i >= 1 && ($i as i64) <= $v.len() as i64 {
                $v[$i as usize-1]
            } else {
                F::zero()
            }
        }
    };
}

#[macro_export]
macro_rules! power_vector_index {
    ( $a: expr, $n: expr, $i: expr ) => {
        {
            if $i >= 1 && ($i as i64) <= ($n as i64) {
                power::<F>($a, $i-1)
            } else {
                F::zero()
            }
        }
    };
}

#[macro_export]
macro_rules! expression_vector {
    ( $i: ident, $v: expr, $n: expr) => {
         (1..=$n).map(|$i| $v).collect::<Vec<_>>()
    };
}

#[macro_export]
macro_rules! accumulate_vector {
    ( $i: ident, $init: expr, $v: expr, $n: expr, $op: tt ) => {
         (1..=$n).scan($init, |acc, $i| {*acc = *acc $op ($v); Some(*acc)})
                 .collect::<Vec<_>>()
    };

    ( $i: ident, $v: expr, $n: expr, $op: tt ) => {
        accumulate_vector!($i, F::zero(), $v, $n, $op)
    };

    ( $v: expr, $init: expr, $op: tt ) => {
        accumulate_vector!(i, $init, $v[i-1], $v.len(), $op)
    };

    ( $v: expr, $op: tt ) => {
        accumulate_vector!(i, F::zero(), $v[i-1], $v.len(), $op)
    };
}

#[macro_export]
macro_rules! vector_concat {
    ( $u: expr, $( $v: expr ),+ ) => {
        $u.into_iter()$(.chain($v.into_iter()))+.collect::<Vec<_>>()
    }
}

#[macro_export]
macro_rules! sum {
    ($h:expr) => ($h);
    ($h:expr, $($v: expr),+) => {
        ($h + sum!($($v),+))
    };
}

#[macro_export]
macro_rules! poly_from_vec {
    ($v: expr) => {
        DensePolynomial::from_coefficients_vec($v)
    };
}

#[macro_export]
macro_rules! vector_reverse_omega {
    ($v: expr, $omega:expr) => {
        $v.iter().enumerate().map(|(i,c)| *c*power($omega, i as i64))
          .rev().collect::<Vec<_>>()
    };
}

#[macro_export]
macro_rules! vector_poly_mul {
    // Given vectors u, v and field element omega, compute
    // the coefficient vector of X^{|u|-1} f_u(omega X^{-1}) f_v(X)
    ($u:expr, $v:expr, $omega:expr) => {
        poly_from_vec!(vector_reverse_omega!($u, $omega)).mul(&poly_from_vec!($v))
    };
}

#[macro_export]
macro_rules! vector_power_mul {
    // Given vector v, element alpha, length n, compute
    // the coefficient vector of v * power(alpha, n)
    ($v:expr, $alpha:expr, $n:expr) => {
        {
            let alpha_power = power($alpha, $n as i64);
            (1..($n as usize)+$v.len()).scan(F::zero(), |acc, i| {
                *acc = *acc * $alpha + vector_index!($v, i) -
                       vector_index!($v, (i as i64) - ($n as i64)) * alpha_power;
                Some(*acc)
            }).collect::<Vec<_>>()
        }
    };
}

#[macro_export]
macro_rules! power_power_mul {
    // Given two power vector, compute the coefficient vector
    // of their product
    ($alpha:expr, $n:expr, $beta:expr, $m:expr) => {
        {
            let alpha_power = power($alpha, $n as i64);
            let mut beta_power = F::one();
            let mut late_beta_power = F::zero();
            (1..($n as usize)+($m as usize)).scan(F::zero(), |acc, i| {
                *acc = *acc * $alpha + beta_power - late_beta_power * alpha_power;
                beta_power = if i >= $m {
                    F::zero()
                } else {
                    beta_power * $beta
                };
                late_beta_power = if i < $n {
                    F::zero()
                } else if i == $n {
                    F::one()
                } else {
                    late_beta_power * $beta
                };
                Some(*acc)
            }).collect::<Vec<_>>()
        }
    };
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

    #[test]
    fn test_linear_combination() {
        assert_eq!(linear_combination!(1), 1);
        assert_eq!(linear_combination!(1, 2, 3), 7);
        assert_eq!(linear_combination!(1, 2, 3, 4, 5), 27);
    }

    #[test]
    fn test_multi_delta() {
        define_vec!(v, expression_vector!(i,
                multi_delta!(i, to_field::<F>(3), 5, to_field::<F>(2), 6), 10));
        assert_eq!(v.iter().map(|e| to_int::<F>(*e)).collect::<Vec<_>>(), vec![0, 0, 0, 0, 3, 2, 0, 0, 0, 0]);
    }

    #[test]
    fn test_delta() {
        define_vec!(v, expression_vector!(i, delta!(i, 5), 10));
        assert_eq!(v.iter().map(|e| to_int::<F>(*e)).collect::<Vec<_>>(), vec![0, 0, 0, 0, 1, 0, 0, 0, 0, 0]);
    }

    #[test]
    fn test_accumulate_vector() {
        define_vec!(v, accumulate_vector!(i, to_field::<F>(i*i), 10, +));
        assert_eq!(v.iter().map(|e| to_int::<F>(*e)).collect::<Vec<_>>(), vec![1, 5, 14, 30, 55, 91, 140, 204, 285, 385]);
    }

    #[test]
    fn test_vector_index() {
        let v = to_field!(vec![1, 2, 3, 4]);
        define_vec!(v, expression_vector!(i, vector_index!(v, i as i64-3), 10));
        assert_eq!(to_int!(v), vec![0, 0, 0, 1, 2, 3, 4, 0, 0, 0]);
    }

    #[test]
    fn test_power_vector_index() {
        define_vec!(v, expression_vector!(i, power_vector_index!(to_field::<F>(2), 9, i as i64-3), 10));
        assert_eq!(to_int!(v), vec![0, 0, 0, 1, 2, 4, 8, 16, 32, 64]);
        define_vec!(v, expression_vector!(i, power_vector_index!(to_field::<F>(2), 4, i as i64-3), 10));
        assert_eq!(to_int!(v), vec![0, 0, 0, 1, 2, 4, 8, 0, 0, 0]);
    }

    #[test]
    fn test_power_linear_combination() {
        assert_eq!(power_linear_combination!(to_field::<F>(2), to_field::<F>(1)), to_field::<F>(1));
        assert_eq!(power_linear_combination!(to_field::<F>(2),
                                             to_field::<F>(1), to_field::<F>(2),
                                             to_field::<F>(3), to_field::<F>(4)),
                                             to_field::<F>(1 + 2 * 2 + 2 * 2 * 3 +
                                                           2 * 2 * 2 * 4));
    }

    #[test]
    fn test_sum() {
        assert_eq!(sum!(1, 2, 3), 6);
    }

    #[test]
    fn test_vector_concat() {
        assert_eq!(vector_concat!(vec![1, 2, 3u64], vec![4, 5, 6u64]),
                   vec![1, 2, 3, 4, 5, 6u64]);
        assert_eq!(vector_concat!(vec![1, 2, 3u64], vec![4, 5, 6u64], vec![7, 8, 9]),
                   vec![1, 2, 3, 4, 5, 6, 7, 8, 9]);
    }

    #[test]
    fn test_vector_reverse_omega() {
        let omega = to_field::<F>(2);
        let v = to_field!(vec![1, 2, 3, 1]);
        assert_eq!(to_int!(vector_reverse_omega!(v, omega)),
                   vec![8, 12, 4, 1]);
    }

    #[test]
    fn test_vector_poly_mul() {
        let u = to_field!(vec![1, 1, 1, 1]);
        let v = to_field!(vec![1, 2, 3, 4]);
        let omega = to_field::<F>(2);
        let poly = vector_poly_mul!(u, v, omega);
        assert_eq!(to_int!(poly.coeffs), vec![8, 20, 34, 49, 24, 11, 4]);
    }

    #[test]
    fn test_vector_power_mul() {
        let v = to_field!(vec![1, 2, 3, 4]);
        let alpha = to_field::<F>(2);
        assert_eq!(to_int!(vector_power_mul!(v, alpha, 3)), vec![1, 4, 11, 18, 20, 16]);
        assert_eq!(to_int!(vector_power_mul!(v, alpha, 4)), vec![1, 4, 11, 26, 36, 40, 32]);
        assert_eq!(to_int!(vector_power_mul!(v, alpha, 5)), vec![1, 4, 11, 26, 52, 72, 80, 64]);
    }

    #[test]
    fn test_power_power_mul() {
        let alpha = to_field::<F>(2);
        let beta = to_field::<F>(3);
        assert_eq!(to_int!(power_power_mul!(alpha, 3, beta, 4)), vec![1, 5, 19, 57, 90, 108]);
        assert_eq!(to_int!(power_power_mul!(alpha, 4, beta, 4)), vec![1, 5, 19, 65, 114, 180, 216]);
        assert_eq!(to_int!(power_power_mul!(alpha, 5, beta, 4)), vec![1, 5, 19, 65, 130, 228, 360, 432]);
    }
}
