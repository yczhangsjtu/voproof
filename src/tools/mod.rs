use crate::{error::Error, kzg::Commitment};
use ark_ec::{msm::VariableBaseMSM, PairingEngine, ProjectiveCurve};
use ark_ff::PrimeField as Field;
use ark_std::{iter::Iterator, rand::RngCore, vec, vec::Vec};
use sha2::{Digest, Sha256};

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

pub fn try_to_int<F: Field>(e: F) -> Option<u64> {
    let digits = e.into_repr().into().to_u64_digits();
    match digits.len() {
        0 => Some(0),
        1 => Some(digits[0]),
        _ => None,
    }
}

#[macro_export]
macro_rules! custom_add_literal {
    (-$a: literal, $b: expr) => {
        $b - to_field::<E::Fr>($a)
    };

    ($a: literal, $b: expr) => {
        to_field::<E::Fr>($a) + $b
    };

    ($a: expr, $b: literal) => {
        to_field::<E::Fr>(($b) as u64) + $a
    };
}

#[macro_export]
macro_rules! custom_add {
    ($a: expr, $b: expr) => {
        $a + $b
    };

    ($a: expr, $b: expr, $($c: expr),+) => {
        $a as i64 + $b as i64 $(+ $c as i64)+
    };
}

pub fn custom_add_ff<F: Field>(a: F, b: F) -> F {
    a + b
}

pub fn custom_add_fi<F: Field>(a: F, b: i64) -> F {
    a + to_field::<F>(b as u64)
}

pub fn custom_add_if<F: Field>(a: i64, b: F) -> F {
    custom_add_fi(b, a)
}

pub fn custom_add_three<F: Field>(a: F, b: F, c: F) -> F {
    a + b + c
}

pub fn power<F: Field>(a: F, e: i64) -> F {
    if e < 0 {
        a.inverse().unwrap().pow(&[(-e) as u64])
    } else {
        a.pow(&[e as u64])
    }
}

/// Compute the matrix-vector product using the sparse
/// representation of the matrix, where the row indices
/// and column indices start from 0
pub fn sparse_mvp<F: Field>(
    h: i64,
    k: i64,
    rows: &Vec<u64>,
    cols: &Vec<u64>,
    vals: &Vec<F>,
    right: &Vec<F>,
) -> Result<Vec<F>, Error> {
    assert!(h > 0);
    assert!(k > 0);
    assert_eq!(right.len(), k as usize);

    let mut res = vec![F::zero(); h as usize];
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
    comms: &Vec<Commitment<E>>,
    coeffs: &Vec<E::Fr>,
) -> Commitment<E> {
    Commitment {
        0: VariableBaseMSM::multi_scalar_mul(
            &comms.iter().map(|x| x.0).collect::<Vec<_>>()[..],
            &coeffs.iter().map(|x| x.into_repr()).collect::<Vec<_>>()[..],
        )
        .into_affine(),
    }
}

pub fn evaluate_sparse<F: Field>(x: F, coeffs: &Vec<F>, indices: &Vec<u64>) -> F {
    coeffs.iter().zip(indices).fold(F::zero(), |y, (c, i)| {
        y + c.clone() * power(x, i.clone() as i64)
    })
}

pub fn evaluate_short<F: Field>(x: F, coeffs: &Vec<F>) -> F {
    coeffs.iter().enumerate().fold(F::zero(), |y, (i, c)| {
        y + c.clone() * power(x, i.clone() as i64)
    })
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

pub fn power_iter<F: Field>(
    start: u64,
    end: u64,
    alpha: F,
    length: u64,
    shifted: u64,
) -> PowerVectorIterator<F> {
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
        let ret = match self.i {
            i if i >= 0 && i < self.v.len() => Some(self.v[i]),
            i if i >= self.v.len() && i < self.n => Some(F::zero()),
            _ => None,
        };
        self.i += 1;
        ret
    }
}

pub fn fixed_length_vector_iter<'a, F: Field>(
    v: &'a Vec<F>,
    n: i64,
) -> FixedLengthVectorIterator<'a, F> {
    FixedLengthVectorIterator {
        v,
        i: 0,
        n: n as usize,
    }
}

#[macro_export]
macro_rules! to_int {
    ( $v: expr) => {
        $v.iter().map(|e| to_int::<E::Fr>(*e)).collect::<Vec<_>>()
    };
}

#[macro_export]
macro_rules! to_field {
    ( $v: expr) => {
        $v.iter().map(|e| to_field::<E::Fr>(*e)).collect::<Vec<_>>()
    };
}

#[macro_export]
macro_rules! zero_pad {
    ( $u: expr, $n: expr ) => {
        (&$u)
            .iter()
            .map(|a| *a)
            .chain((0..($n as usize - $u.len())).map(|_| E::Fr::zero()))
            .collect::<Vec<_>>()
    };
}

#[macro_export]
macro_rules! zero_pad_and_concat {
    ( $u: expr, $n: expr, $( $v: expr ),+ ) => {
        (&$u).iter().map(|a| *a)
          .chain((0..($n as usize-$u.len())).map(|_| E::Fr::zero()))
          $(.chain((&$v).iter().map(|a| *a)))+.collect::<Vec<_>>()
    }
}

#[macro_export]
macro_rules! define {
    ( $v: ident, $expr: expr ) => {
        let $v = $expr;
    };
}

#[macro_export]
macro_rules! define_mut {
    ( $v: ident, $expr: expr ) => {
        let mut $v = $expr;
    };
}

#[macro_export]
macro_rules! define_vec {
    ( $v: ident, $expr: expr ) => {
        let $v: Vec<E::Fr> = $expr;
    };
}

#[macro_export]
macro_rules! define_vec_mut {
    ( $v: ident, $expr: expr ) => {
        let mut $v: Vec<E::Fr> = $expr;
    };
}

#[macro_export]
macro_rules! concat_matrix_vertically {
    ($result:ident, $h:expr,
   $arows:expr, $brows:expr, $crows:expr,
   $acols:expr, $bcols:expr, $ccols:expr,
   $avals:expr, $bvals:expr, $cvals:expr) => {
        let $result = (
            $arows
                .iter()
                .map(|a| *a)
                .chain($brows.iter().map(|&i| i + $h as u64))
                .chain($crows.iter().map(|&i| i + $h as u64 * 2))
                .collect::<Vec<u64>>(),
            $acols
                .iter()
                .chain($bcols.iter())
                .chain($ccols.iter())
                .map(|a| *a)
                .collect::<Vec<u64>>(),
            $avals
                .iter()
                .chain($bvals.iter())
                .chain($cvals.iter())
                .map(|a| *a)
                .collect::<Vec<E::Fr>>(),
        );
    };
}

#[macro_export]
macro_rules! delta {
    ( $i: expr, $j: expr ) => {{
        if $i == $j {
            E::Fr::one()
        } else {
            E::Fr::zero()
        }
    }};
}

#[macro_export]
macro_rules! multi_delta {
    ( $i: expr, $( $c:expr, $j:expr ),+ ) => {
        {
            let mut s = E::Fr::zero();
            $( s = s + $c * delta!($i, $j); )+
            s
        }
    };
}

#[macro_export]
macro_rules! linear_combination {
    ( $i: expr ) => {
        $i
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
macro_rules! sample_randomizers {
    ( $rng: expr, $( $ident:ident, $size:expr ),+ ) => {
        $( let $ident = sample_vec::<E::Fr, _>($rng, $size); )+
    };
}

#[macro_export]
macro_rules! power_linear_combination {
    ( $alpha: expr, $( $a:expr ),+ ) => {
        {
            let mut s = E::Fr::zero();
            let mut c = E::Fr::one();
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
    ( $v: expr, $i: expr ) => {{
        if ($i as i64) >= 1i64 && ($i as i64) <= $v.len() as i64 {
            $v[($i as i64 - 1) as usize]
        } else {
            E::Fr::zero()
        }
    }};
}

#[macro_export]
macro_rules! power_vector_index {
    ( $a: expr, $n: expr, $i: expr ) => {{
        if $i >= 1 && ($i as i64) <= ($n as i64) {
            power::<E::Fr>($a, ($i - 1) as i64)
        } else {
            E::Fr::zero()
        }
    }};
}

#[macro_export]
macro_rules! range_index {
  ( $s: expr, $e: expr, $i: expr ) => {{
    if ($i as i64) >= ($s as i64) && ($i as i64) <= ($e as i64) {
      E::Fr::one()
    } else {
      E::Fr::zero()
    }
  }};
}

#[macro_export]
macro_rules! expression_vector {
    ( $i: ident, $v: expr, $n: expr) => {
        (1..=$n).map(|$i| $v).collect::<Vec<_>>()
    };
}

#[macro_export]
macro_rules! define_expression_vector {
    ( $name:ident, $i: ident, $v: expr, $n: expr) => {
        let $name = expression_vector!($i, $v, $n);
    };
}

#[macro_export]
macro_rules! define_expression_vector_inverse {
    ( $name:ident, $i: ident, $v: expr, $n: expr) => {
        let mut $name = expression_vector!($i, $v, $n);
        batch_inversion(&mut $name);
        let $name = $name;
    };
}

#[macro_export]
macro_rules! add_expression_vector_to_vector {
    ( $u:ident, $i: ident, $v: expr) => {
        for $i in (1i64..=$u.len() as i64) {
            $u[($i - 1) as usize] += $v;
        }
    };
}

#[macro_export]
macro_rules! add_vector_to_vector {
    ( $u:ident, $v: expr) => {
        for i in (1i64..=$u.len() as i64) {
            $u[(i - 1) as usize] += vector_index!($v, i);
        }
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
        accumulate_vector!(i, E::Fr::zero(), $v[i-1], $v.len(), $op)
    };
}

#[macro_export]
macro_rules! vector_concat {
    ( $u: expr, $( $v: expr ),+ ) => {
        (&$u).iter().map(|a| *a)$(.chain((&$v).iter().map(|a| *a)))+.collect::<Vec<_>>()
    }
}

#[macro_export]
macro_rules! max {
    ($h:expr) => ($h);
    ($h:expr, $($v: expr),+) => {
      {
        let a = $h;
        let b = max!($($v),+);
        if a < b { b } else { a }
      }
    };
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
        DensePoly::from_coefficients_vec($v.clone())
    };
}

#[macro_export]
macro_rules! vector_reverse_omega {
    ($v: expr, $omega:expr) => {
        $v.iter()
            .enumerate()
            .map(|(i, c)| *c * power($omega, i as i64))
            .rev()
            .collect::<Vec<_>>()
    };
}

#[macro_export]
macro_rules! int_array_to_power_vector {
    ($v:expr, $gamma:expr) => {
        expression_vector!(i, power($gamma, $v[i - 1] as i64), $v.len())
    };
}

#[macro_export]
macro_rules! define_int_array_to_power_vector {
    ($name:ident, $v:expr, $gamma:expr) => {
        define_vec!($name, int_array_to_power_vector!($v, $gamma));
    };
}

#[macro_export]
macro_rules! define_clone_vector {
    ($name:ident, $v:expr) => {
        define_vec!($name, $v.to_vec());
    };
}

#[macro_export]
macro_rules! define_matrix_vectors {
    ($u:ident, $w:ident, $v:ident, $mat:expr, $gamma:expr) => {
        define_int_array_to_power_vector!($u, $mat.0, $gamma);
        define_int_array_to_power_vector!($w, $mat.1, $gamma);
        define_clone_vector!($v, $mat.2);
    };
}

#[macro_export]
macro_rules! commit_vector {
    ($cm:ident, $v:expr, $powers:expr, $deg:expr) => {
        let $cm = vector_to_commitment::<E>(&$powers, &$v, $deg as u64).unwrap();
    };
}

#[macro_export]
macro_rules! define_hadamard_vector {
    ($name:ident, $u:expr, $v:expr) => {
        define_vec!(
            $name,
            $u.iter()
                .zip($v.iter())
                .map(|(a, b)| *a * *b)
                .collect::<Vec<E::Fr>>()
        );
    };
}

#[macro_export]
macro_rules! define_concat_vector {
    ($name:ident, $( $u:expr ),+ ) => {
        define_vec!(
            $name,
            vector_concat!( $($u),+ )
        );
    };
}

#[macro_export]
macro_rules! define_zero_pad_concat_vector {
    ($name:ident, $v:expr, $n:expr, $( $u:expr ),+ ) => {
        define_vec!(
            $name,
            zero_pad_and_concat!( $v, $n, $($u),+ )
        );
    };
}

#[macro_export]
macro_rules! redefine_zero_pad_concat_vector {
    ($name:ident, $n:expr, $( $u:expr ),+ ) => {
        define_zero_pad_concat_vector!($name, $name, $n, $($u),+);
    };
}

#[macro_export]
macro_rules! define_poly_from_vec {
    ($poly:ident, $v:expr) => {
        let $poly = poly_from_vec!($v);
    };
}

#[macro_export]
macro_rules! sparse_mvp_vector {
    ($mat:expr, $v:expr, $h:expr, $k:expr) => {
        sparse_mvp($h, $k, &$mat.0, &$mat.1, &$mat.2, &$v).unwrap()
    };
}

#[macro_export]
macro_rules! define_sparse_mvp_vector {
    ($name:ident, $mat:expr, $v:expr, $h:expr, $k:expr) => {
        define_vec!($name, sparse_mvp_vector!($mat, $v, $h, $k));
    };
}

#[macro_export]
macro_rules! define_left_sparse_mvp_vector {
    ($name:ident, $mat:expr, $v:expr, $h:expr, $k:expr) => {
        let $name = sparse_mvp($k, $h, &$mat.1, &$mat.0, &$mat.2, &$v).unwrap();
    };
}

#[macro_export]
macro_rules! get_randomness_from_hash {
    ($name:ident, $( $item:expr ),+) => {
        let $name = hash_to_field::<E::Fr>(
            to_bytes!( $( $item ),+ ).unwrap()
        );
    }
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
    ($v:expr, $alpha:expr, $n:expr) => {{
        let alpha_power = power($alpha, $n as i64);
        (1..($n as usize) + $v.len())
            .scan(E::Fr::zero(), |acc, i| {
                *acc = *acc * $alpha + vector_index!($v, i)
                    - vector_index!($v, (i as i64) - ($n as i64)) * alpha_power;
                Some(*acc)
            })
            .collect::<Vec<_>>()
    }};
}

#[macro_export]
macro_rules! power_power_mul {
    // Given two power vector, compute the coefficient vector
    // of their product
    ($alpha:expr, $n:expr, $beta:expr, $m:expr) => {{
        let alpha_power = power($alpha, $n as i64);
        let mut beta_power = E::Fr::one();
        let mut late_beta_power = E::Fr::zero();
        (1..($n as usize) + ($m as usize))
            .scan(E::Fr::zero(), |acc, i| {
                *acc = *acc * $alpha + beta_power - late_beta_power * alpha_power;
                beta_power = if i >= ($m as usize) {
                    E::Fr::zero()
                } else {
                    beta_power * $beta
                };
                late_beta_power = if i < ($n as usize) {
                    E::Fr::zero()
                } else if i == ($n as usize) {
                    E::Fr::one()
                } else {
                    late_beta_power * $beta
                };
                Some(*acc)
            })
            .collect::<Vec<_>>()
    }};
}

#[macro_export]
macro_rules! eval_vector_expression {
    // Compute f(z), where f has coefficient vector
    // expressed by an expression
    ($z:expr, $i:ident, $expr:expr, $n: expr) => {{
        let mut power = E::Fr::one();
        (1..=$n)
            .map(|$i| {
                let ret = $expr * power;
                power = power * $z;
                ret
            })
            .sum::<E::Fr>()
    }};
}

#[macro_export]
macro_rules! eval_vector_as_poly {
    ($v:expr, $z:expr) => {
        eval_vector_expression!($z, i, vector_index!($v, i), $v.len())
    };
}

#[macro_export]
macro_rules! generator_of {
    ($e:ident) => {
        $e::Fr::from_repr(
            <<<E as ark_ec::PairingEngine>::Fr as FftField>::FftParams as FpParameters>::GENERATOR,
        )
        .unwrap()
    };
}

#[macro_export]
macro_rules! define_generator {
    ($gamma:ident, $e:ident) => {
        let $gamma = generator_of!($e);
    };
}

#[macro_export]
macro_rules! init_size {
    ($name:ident, $attr:ident, $size:ident) => {
        let $name: i64 = $size.$attr as i64;
    };
}

#[macro_export]
macro_rules! check_poly_eval {
    ($f:expr, $z:expr, $y:expr, $info:literal) => {
        let y = $f.evaluate(&$z);
        if y != $y.clone() {
            return Err(Error::PolynomialEvaluationUnexpected(
                y.to_string(),
                $y.to_string(),
                $info.to_string(),
            ));
        }
    };
}

#[macro_export]
macro_rules! fmt_ff {
    ($a:expr) => {
        if let Some(x) = try_to_int::<E::Fr>($a.clone()) {
            format!("Fp256({})", x)
        } else {
            if let Some(x) = try_to_int::<E::Fr>(-$a.clone()) {
                format!("Fp256(-{})", x)
            } else {
                $a.to_string()
            }
        }
    };
}

#[macro_export]
macro_rules! fmt_ff_vector {
    ($v: expr) => {
        ($v.iter().map(|e| fmt_ff!(e)).collect::<Vec<String>>()).join("\n")
    };
}

#[macro_export]
macro_rules! vector_diff {
    ($u: expr, $v: expr) => {{
        assert_eq!($u.len(), $v.len());
        ($u).iter()
            .zip(($v).iter())
            .map(|(a, b)| *a - *b)
            .collect::<Vec<_>>()
    }};
}

#[macro_export]
macro_rules! check_vector_eq {
  ($u:expr, $v:expr, $info:literal) => {
    if $u.len() != $v.len() {
      return Err(Error::VectorNotEqual(format!("{}: length not equal, {} != {}", $info, $u.len(), $v.len())));
    }
    if let Some(i) = $u.iter().zip($v.iter()).position(|(a, b)| *a != *b) {
      return Err(Error::VectorNotEqual(
          format!("{}: unequal at {} (total length {}): {} != {}\nleft = [\n{}\n]\nright = [\n{}\n], diff = [\n{}\n], differ at {} places",
          $info, i, $u.len(), $u[i], $v[i], fmt_ff_vector!($u), fmt_ff_vector!($v),
          fmt_ff_vector!(vector_diff!($u, $v)),
          $u.iter().zip($v.iter()).filter(|(a,b)| *a != *b).count())));
    }
  }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bls12_381 as E;
    use ark_bls12_381::Fr as F;
    use ark_poly::univariate::DensePolynomial as DensePoly;
    use ark_poly_commit::UVPolynomial;
    use ark_std::{
        ops::{Add, Mul, Sub},
        One, Zero,
    };

    #[test]
    fn test_int_field_transform() {
        for i in 0..1000 {
            assert_eq!(i, to_int::<F>(to_field::<F>(i)));
        }
    }

    #[test]
    fn test_max() {
        assert_eq!(max!(1, 2, 3), 3);
    }

    #[test]
    fn test_sparse_mvp() {
        let rows = vec![1, 0, 3, 2];
        let cols = vec![0, 1, 2, 3];
        let vals = vec![
            F::from_repr(1.into()).unwrap(),
            F::from_repr(3.into()).unwrap(),
            F::from_repr(2.into()).unwrap(),
            F::from_repr(5.into()).unwrap(),
        ];
        let right = vec![
            F::from_repr(1.into()).unwrap(),
            F::from_repr(1.into()).unwrap(),
            F::from_repr(1.into()).unwrap(),
            F::from_repr(1.into()).unwrap(),
        ];
        let left = sparse_mvp(4, 4, &rows, &cols, &vals, &right).unwrap();
        assert_eq!(
            left,
            vec![
                F::from_repr(3.into()).unwrap(),
                F::from_repr(1.into()).unwrap(),
                F::from_repr(5.into()).unwrap(),
                F::from_repr(2.into()).unwrap()
            ]
        );
    }

    #[test]
    fn test_power_iterator() {
        assert_eq!(
            power_iter::<F>(0, 5, F::one(), 3, 0).collect::<Vec<F>>(),
            vec![F::one(), F::one(), F::one(), F::zero(), F::zero()]
        );
        assert_eq!(
            power_iter::<F>(2, 6, to_field(2), 3, 0).collect::<Vec<F>>(),
            vec![to_field(4), F::zero(), F::zero(), F::zero()]
        );
        assert_eq!(
            power_iter::<F>(2, 6, to_field(2), 3, 3).collect::<Vec<F>>(),
            vec![F::zero(), to_field(1), to_field(2), to_field(4)]
        );
    }

    #[test]
    fn test_linear_combination() {
        assert_eq!(linear_combination!(1), 1);
        assert_eq!(linear_combination!(1, 2, 3), 7);
        assert_eq!(linear_combination!(1, 2, 3, 4, 5), 27);
    }

    #[test]
    fn test_multi_delta() {
        define_vec!(
            v,
            expression_vector!(
                i,
                multi_delta!(i, to_field::<F>(3), 5, to_field::<F>(2), 6),
                10
            )
        );
        assert_eq!(
            v.iter().map(|e| to_int::<F>(*e)).collect::<Vec<_>>(),
            vec![0, 0, 0, 0, 3, 2, 0, 0, 0, 0]
        );
    }

    #[test]
    fn test_delta() {
        define_vec!(v, expression_vector!(i, delta!(i, 5), 10));
        assert_eq!(
            v.iter().map(|e| to_int::<F>(*e)).collect::<Vec<_>>(),
            vec![0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
        );
    }

    #[test]
    fn test_accumulate_vector() {
        define_vec!(v, accumulate_vector!(i, to_field::<F>(i*i), 10, +));
        assert_eq!(
            v.iter().map(|e| to_int::<F>(*e)).collect::<Vec<_>>(),
            vec![1, 5, 14, 30, 55, 91, 140, 204, 285, 385]
        );
    }

    #[test]
    fn test_vector_index() {
        let v = to_field!(vec![1, 2, 3, 4]);
        define_vec!(v, expression_vector!(i, vector_index!(v, i as i64 - 3), 10));
        assert_eq!(to_int!(v), vec![0, 0, 0, 1, 2, 3, 4, 0, 0, 0]);
    }

    #[test]
    fn test_power_vector_index() {
        define_vec!(
            v,
            expression_vector!(
                i,
                power_vector_index!(to_field::<F>(2), 9, i as i64 - 3),
                10
            )
        );
        assert_eq!(to_int!(v), vec![0, 0, 0, 1, 2, 4, 8, 16, 32, 64]);
        define_vec!(
            v,
            expression_vector!(
                i,
                power_vector_index!(to_field::<F>(2), 4, i as i64 - 3),
                10
            )
        );
        assert_eq!(to_int!(v), vec![0, 0, 0, 1, 2, 4, 8, 0, 0, 0]);
    }

    #[test]
    fn test_range_index() {
        define_vec!(
            v,
            expression_vector!(i, range_index!(1, 9, i as i64 - 3), 10)
        );
        assert_eq!(to_int!(v), vec![0, 0, 0, 1, 1, 1, 1, 1, 1, 1]);
        define_vec!(
            v,
            expression_vector!(i, range_index!(2, 4, i as i64 - 3), 10)
        );
        assert_eq!(to_int!(v), vec![0, 0, 0, 0, 1, 1, 1, 0, 0, 0]);
    }

    #[test]
    fn test_power_linear_combination() {
        assert_eq!(
            power_linear_combination!(to_field::<F>(2), to_field::<F>(1)),
            to_field::<F>(1)
        );
        assert_eq!(
            power_linear_combination!(
                to_field::<F>(2),
                to_field::<F>(1),
                to_field::<F>(2),
                to_field::<F>(3),
                to_field::<F>(4)
            ),
            to_field::<F>(1 + 2 * 2 + 2 * 2 * 3 + 2 * 2 * 2 * 4)
        );
    }

    #[test]
    fn test_sum() {
        assert_eq!(sum!(1, 2, 3), 6);
    }

    #[test]
    fn test_vector_concat() {
        assert_eq!(
            vector_concat!(vec![1, 2, 3u64], vec![4, 5, 6u64]),
            vec![1, 2, 3, 4, 5, 6u64]
        );
        assert_eq!(
            vector_concat!(vec![1, 2, 3u64], vec![4, 5, 6u64], vec![7, 8, 9]),
            vec![1, 2, 3, 4, 5, 6, 7, 8, 9]
        );
    }

    #[test]
    fn test_vector_reverse_omega() {
        let omega = to_field::<F>(2);
        let v = to_field!(vec![1, 2, 3, 1]);
        assert_eq!(to_int!(vector_reverse_omega!(v, omega)), vec![8, 12, 4, 1]);
    }

    #[test]
    fn test_int_array_to_power_vector() {
        let gamma = to_field::<F>(2);
        let v = vec![1, 2, 3, 1];
        assert_eq!(
            to_int!(int_array_to_power_vector!(v, gamma)),
            vec![2, 4, 8, 2]
        );
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
        assert_eq!(
            to_int!(vector_power_mul!(v, alpha, 3)),
            vec![1, 4, 11, 18, 20, 16]
        );
        assert_eq!(
            to_int!(vector_power_mul!(v, alpha, 4)),
            vec![1, 4, 11, 26, 36, 40, 32]
        );
        assert_eq!(
            to_int!(vector_power_mul!(v, alpha, 5)),
            vec![1, 4, 11, 26, 52, 72, 80, 64]
        );
    }

    #[test]
    fn test_power_power_mul() {
        let alpha = to_field::<F>(2);
        let beta = to_field::<F>(3);
        assert_eq!(
            to_int!(power_power_mul!(alpha, 3, beta, 4)),
            vec![1, 5, 19, 57, 90, 108]
        );
        assert_eq!(
            to_int!(power_power_mul!(alpha, 4, beta, 4)),
            vec![1, 5, 19, 65, 114, 180, 216]
        );
        assert_eq!(
            to_int!(power_power_mul!(alpha, 5, beta, 4)),
            vec![1, 5, 19, 65, 130, 228, 360, 432]
        );
        assert_eq!(
            to_int!(power_power_mul!(E::Fr::one(), 4, E::Fr::one(), 4)),
            vec![1, 2, 3, 4, 3, 2, 1]
        );
    }

    #[test]
    fn test_eval_vector_expression() {
        assert_eq!(
            eval_vector_expression!(to_field::<F>(2), i, to_field::<F>(i as u64), 4),
            to_field::<F>(49)
        );
    }

    #[test]
    fn test_eval_vector_as_poly() {
        assert_eq!(
            eval_vector_as_poly!(to_field!(vec![1, 2, 3, 4]), to_field::<F>(2)),
            to_field::<F>(49)
        );
    }

    #[test]
    fn test_add_expression_to_vector() {
        let mut u = vec![0, 1, 2, 3, 4];
        add_expression_vector_to_vector!(u, i, i * i);
        assert_eq!(u, vec![1, 5, 11, 19, 29]);
    }

    #[test]
    fn test_add_vector_to_vector() {
        let mut u = to_field!(vec![0, 1, 2, 3, 4]);
        add_vector_to_vector!(u, to_field!(vec![1, 4, 9, 16, 25]));
        assert_eq!(to_int!(u), vec![1, 5, 11, 19, 29]);
    }

    #[test]
    fn test_zero_pad() {
        assert_eq!(
            to_int!(zero_pad!(to_field!(vec![1, 2, 3u64]), 3)),
            vec![1, 2, 3]
        );
        assert_eq!(
            to_int!(zero_pad!(to_field!(vec![1, 2, 3u64]), 5)),
            vec![1, 2, 3, 0, 0]
        );
    }

    #[test]
    fn test_zero_pad_concat() {
        assert_eq!(
            to_int!(zero_pad_and_concat!(
                to_field!(vec![1, 2, 3u64]),
                3,
                to_field!(vec![4, 5, 6u64])
            )),
            vec![1, 2, 3, 4, 5, 6u64]
        );
        assert_eq!(
            to_int!(zero_pad_and_concat!(
                to_field!(vec![1, 2, 3u64]),
                5,
                to_field!(vec![4, 5, 6u64]),
                to_field!(vec![7, 8, 9])
            )),
            vec![1, 2, 3, 0, 0, 4, 5, 6, 7, 8, 9]
        );
    }
}
