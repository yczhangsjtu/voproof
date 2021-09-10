use ark_ff::Field;
use super::*;

pub struct POV<F: Field> {
    pub consts: Vec<F>,
    pub wires: Vec<(u64, u64)>,
}

impl<F: Field> ConstraintSystem<F> for POV<F> {}

pub struct POVSize {
    pub nconsts: u64,
    pub nmul: u64,
    pub nadd: u64,
}

impl CSSize for POVSize {}

