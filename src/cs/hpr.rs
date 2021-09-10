use ark_ff::Field;
use super::*;

pub struct HPR<F: Field> {
    pub arows: Vec<u64>,
    pub acols: Vec<u64>,
    pub avals: Vec<F>,
    pub brows: Vec<u64>,
    pub bcols: Vec<u64>,
    pub bvals: Vec<F>,
    pub crows: Vec<u64>,
    pub ccols: Vec<u64>,
    pub cvals: Vec<F>,
    pub drows: Vec<u64>,
    pub dvals: Vec<F>,
}

impl<F: Field> ConstraintSystem<F> for HPR<F> {}

pub struct HPRSize {
    pub nrows: u64,
    pub ncols: u64,
    pub density: u64,
}

impl CSSize for HPRSize {}

