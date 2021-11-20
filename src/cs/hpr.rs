use super::*;
use ark_ff::Field;

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
  pub nrows: u64,
  pub ncols: u64,
  pub input_size: u64,
}

impl<F: Field> ConstraintSystem<F, HPRSize> for HPR<F> {
  fn get_size(&self) -> HPRSize {
    let density = self.arows.len();
    assert_eq!(density, self.acols.len());
    assert_eq!(density, self.avals.len());
    assert_eq!(density, self.brows.len());
    assert_eq!(density, self.bcols.len());
    assert_eq!(density, self.bvals.len());
    assert_eq!(density, self.crows.len());
    assert_eq!(density, self.ccols.len());
    assert_eq!(density, self.cvals.len());
    let d_density = self.drows.len();
    assert_eq!(d_density, self.dvals.len());
    assert!(self.nrows >= d_density as u64);
    HPRSize {
      nrows: self.nrows,
      ncols: self.ncols,
      density: density as u64,
      d_density: d_density as u64,
      input_size: self.input_size as u64,
    }
  }
}

pub struct HPRSize {
  pub nrows: u64,
  pub ncols: u64,
  pub density: u64,
  pub d_density: u64,
  pub input_size: u64,
}

impl CSSize for HPRSize {}
