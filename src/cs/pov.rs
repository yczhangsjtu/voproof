use ark_ff::Field;
use super::*;

pub struct POV<F: Field> {
    pub consts: Vec<F>,
    pub wires: Vec<(u64, u64)>,
    pub nmul: u64,
    pub nadd: u64,
}

impl<F: Field> ConstraintSystem<F, POVSize> for POV<F> {
    fn get_size(&self) -> POVSize {
        POVSize {
            nconsts: self.consts.len() as u64,
            nmul: self.nmul,
            nadd: self.nadd,
        }
    }
}

pub struct POVSize {
    pub nconsts: u64,
    pub nmul: u64,
    pub nadd: u64,
}

impl CSSize for POVSize {}

