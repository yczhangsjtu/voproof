use ark_poly::{univariate::DensePolynomial as DensePoly, UVPolynomial};
use ark_bls12_377::Bls12_377;
use ark_bls12_381::Bls12_381;
use ark_bls12_381::Fr;
use ark_ec::PairingEngine;
use ark_poly_commit::kzg10::KZG10;
use ark_std::test_rng;
use ark_ff::fields::PrimeField;

fn main() {
    type UniPoly381 = DensePoly<<Bls12_381 as PairingEngine>::Fr>;
    type UniPoly377 = DensePoly<<Bls12_377 as PairingEngine>::Fr>;
    type KZGBls381 = KZG10<Bls12_381, UniPoly381>;
    let rng = &mut test_rng();
    let p = DensePoly::from_coefficients_slice(&[
        Fr::from_repr(1.into()).unwrap(),
        Fr::from_repr(2.into()).unwrap(),
        Fr::from_repr(3.into()).unwrap(),
        Fr::from_repr(0.into()).unwrap(),
        Fr::from_repr(7.into()).unwrap(),
        Fr::from_repr(9.into()).unwrap(),
    ]);
    let pp = KZGBls381::setup(10, false, rng).unwrap();
    println!("Hello, world!");
}
