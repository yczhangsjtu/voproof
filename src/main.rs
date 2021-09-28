use ark_poly::{
    univariate::DensePolynomial as DensePoly,
    UVPolynomial, Polynomial
};
use ark_bls12_377::Bls12_377;
use ark_bls12_381::Bls12_381;
use ark_bls12_381::Fr as F;
use ark_ec::PairingEngine;
use ark_poly_commit::{
    // kzg10::{KZG10, UniversalParams, Powers, VerifierKey, Randomness},
    Error, PCRandomness
};
use ark_std::{Zero, One, test_rng};
use ark_ff::fields::PrimeField;
use voproof::tools::{to_int, to_field};
use voproof::{accumulate_vector, define_vec, delta,
              expression_vector, multi_delta, linear_combination};
// use voproof::kzg::{KZG10, UniversalParams, Powers, VerifierKey, Randomness};

fn main() {
    println!("{:?}", (1..=10).map(|i| i*i).collect::<Vec<_>>());
    println!("{:?}", (0..10i32).scan(0, |acc, i| {
        *acc = *acc + i;
        Some(*acc)
    }).collect::<Vec<_>>());
    println!("{:?}", (0..10u64).scan(F::zero(), |acc: &mut F, i| {
        *acc = *acc + to_field::<F>(i) * to_field::<F>(i);
        Some(*acc)
    }).map(|e| to_int(e)).collect::<Vec<_>>());
}
