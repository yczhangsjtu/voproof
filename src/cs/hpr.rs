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
    let adensity = self.arows.len();
    let bdensity = self.brows.len();
    let cdensity = self.crows.len();
    assert_eq!(adensity, self.acols.len());
    assert_eq!(adensity, self.avals.len());
    assert_eq!(bdensity, self.bcols.len());
    assert_eq!(bdensity, self.bvals.len());
    assert_eq!(cdensity, self.ccols.len());
    assert_eq!(cdensity, self.cvals.len());
    let ddensity = self.drows.len();
    assert_eq!(ddensity, self.dvals.len());
    assert!(self.nrows >= ddensity as u64);
    HPRSize {
      nrows: self.nrows,
      ncols: self.ncols,
      adensity: adensity as u64,
      bdensity: adensity as u64,
      cdensity: adensity as u64,
      ddensity: ddensity as u64,
      input_size: self.input_size as u64,
    }
  }
}

#[derive(Clone)]
pub struct HPRSize {
  pub nrows: u64,
  pub ncols: u64,
  pub adensity: u64,
  pub bdensity: u64,
  pub cdensity: u64,
  pub ddensity: u64,
  pub input_size: u64,
}

impl CSSize for HPRSize {}

pub struct HPRInstance<F: Field> {
  pub instance: Vec<F>,
}

pub struct HPRWitness<F: Field> {
  pub witness: (Vec<F>, Vec<F>, Vec<F>),
}

impl<F: Field> Instance<F> for HPRInstance<F> {}
impl<F: Field> Witness<F> for HPRWitness<F> {}
