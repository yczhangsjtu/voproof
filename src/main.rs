use ark_poly::{
    univariate::DensePolynomial as DensePoly,
    UVPolynomial, Polynomial
};
use ark_bls12_377::Bls12_377;
use ark_bls12_381::Bls12_381;
use ark_bls12_381::Fr;
use ark_ec::PairingEngine;
use ark_poly_commit::{
    // kzg10::{KZG10, UniversalParams, Powers, VerifierKey, Randomness},
    Error, PCRandomness
};
use ark_std::{Zero, test_rng};
use ark_ff::fields::PrimeField;
use voproof::tools::{to_int, to_field};
// use voproof::kzg::{KZG10, UniversalParams, Powers, VerifierKey, Randomness};

fn main() {
    println!("{:?}", (0..10).map(|i| i*i).collect::<Vec<_>>());
    println!("{:?}", (0..10i32).scan(0, |acc, i| {
        *acc = *acc + i;
        Some(*acc)
    }).collect::<Vec<_>>());
    println!("{:?}", (0..10u64).scan(Fr::zero(), |acc: &mut Fr, i| {
        *acc = *acc + to_field::<Fr>(i) * to_field::<Fr>(i);
        Some(*acc)
    }).map(|e| to_int(e)).collect::<Vec<_>>());
}
