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
    pub nrows: u64,
    pub ncols: u64,
    pub input_size: u64,
}

impl<F: Field> ConstraintSystem<F, R1CSSize> for R1CS<F> {
    fn get_size(&self) -> R1CSSize {
        let density = self.arows.len();
        assert_eq!(density, self.acols.len());
        assert_eq!(density, self.avals.len());
        assert_eq!(density, self.brows.len());
        assert_eq!(density, self.bcols.len());
        assert_eq!(density, self.bvals.len());
        assert_eq!(density, self.crows.len());
        assert_eq!(density, self.ccols.len());
        assert_eq!(density, self.cvals.len());
        R1CSSize {
            nrows: self.nrows,
            ncols: self.ncols,
            density: density as u64,
            input_size: self.input_size,
        }
    }
}

pub struct R1CSSize {
    pub nrows: u64,
    pub ncols: u64,
    pub density: u64,
    pub input_size: u64,
}

impl CSSize for R1CSSize {}

pub struct R1CSInstance<F: Field> {
    pub instance: Vec<F>,
}

pub struct R1CSWitness<F: Field> {
    pub witness: Vec<F>,
}

impl<F: Field> Instance<F> for R1CSInstance<F> {}
impl<F: Field> Witness<F> for R1CSWitness<F> {}

