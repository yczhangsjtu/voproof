use ark_ff::Field;
use super::*;

pub struct R1CS<F: Field> {
    pub arows: Vec<u64>,
    pub acols: Vec<u64>,
    pub avals: Vec<F>,
    pub brows: Vec<u64>,
    pub bcols: Vec<u64>,
    pub bvals: Vec<F>,
    pub crows: Vec<u64>,
    pub ccols: Vec<u64>,
    pub cvals: Vec<F>,
}

impl<F: Field> ConstraintSystem<F> for R1CS<F> {}

pub struct R1CSSize {
    pub nrows: u64,
    pub ncols: u64,
    pub density: u64,
}

impl CSSize for R1CSSize {}

pub struct R1CSInstance<F: Field> {
    pub instance: Vec<F>,
}

pub struct R1CSWitness<F: Field> {
    pub witness: Vec<F>,
}

impl<F: Field> Instance<F> for R1CSInstance<F> {}

