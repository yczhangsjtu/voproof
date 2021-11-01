use ark_ff::{Field, PrimeField};
use ark_relations::r1cs::{ConstraintSystem as ArkR1CS};
use crate::*;
use super::*;
use crate::tools::*;

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
        assert_eq!(self.arows.len(), self.acols.len());
        assert_eq!(self.arows.len(), self.avals.len());
        assert_eq!(self.brows.len(), self.bcols.len());
        assert_eq!(self.brows.len(), self.bvals.len());
        assert_eq!(self.crows.len(), self.ccols.len());
        assert_eq!(self.crows.len(), self.cvals.len());
        let density = max!(self.arows.len(), self.brows.len(), self.crows.len());
        R1CSSize {
            nrows: self.nrows,
            ncols: self.ncols,
            density: density as u64,
            input_size: self.input_size,
        }
    }
}

impl<F: PrimeField> R1CS<F> {
  pub fn satisfy(&self, ins: &R1CSInstance::<F>, wit: &R1CSWitness::<F>) -> bool {
    let z = vector_concat!(vec![F::one()], ins.instance, wit.witness);
    let ya = sparse_mvp(self.nrows as i64, self.ncols as i64,
      &self.arows, &self.acols, &self.avals, &z).unwrap();
    let yb = sparse_mvp(self.nrows as i64, self.ncols as i64,
      &self.brows, &self.bcols, &self.bvals, &z).unwrap();
    let yc = sparse_mvp(self.nrows as i64, self.ncols as i64,
      &self.crows, &self.ccols, &self.cvals, &z).unwrap();
    ya.iter().zip(yb.iter()).zip(yc.iter()).all(|((a, b), c)| *a * *b == *c)
  }
}

impl<F: Field> From<ArkR1CS<F>> for R1CS<F> {
  fn from(r1cs: ArkR1CS<F>) -> Self {
    let mut r1cs = r1cs.clone();
    r1cs.inline_all_lcs();
    let matrices = r1cs.to_matrices().unwrap();

    let ell = matrices.num_instance_variables;
    let ncols = (ell + matrices.num_witness_variables) as u64;
    let nrows = matrices.num_constraints as u64;
    let (a, b, c) = (matrices.a, matrices.b, matrices.c);
    let a = a.iter().enumerate()
             .flat_map(|(row_index, row)|
                         row.iter().map(move |(c, col_index)|
                         (row_index.clone() as u64, *col_index as u64, *c)))
             .collect::<Vec<(u64, u64, F)>>();
    let b = b.iter().enumerate()
             .flat_map(|(row_index, row)|
                         row.iter().map(move |(c, col_index)|
                         (row_index.clone() as u64, *col_index as u64, *c)))
             .collect::<Vec<(u64, u64, F)>>();
    let c = c.iter().enumerate()
             .flat_map(|(row_index, row)|
                         row.iter().map(move |(c, col_index)|
                         (row_index.clone() as u64, *col_index as u64, *c)))
             .collect::<Vec<_>>();
    let arows = a.iter().map(|(row_index, col_index, c)| *row_index).collect();
    let acols = a.iter().map(|(row_index, col_index, c)| *col_index).collect();
    let avals = a.iter().map(|(row_index, col_index, c)| *c).collect();
    let brows = b.iter().map(|(row_index, col_index, c)| *row_index).collect();
    let bcols = b.iter().map(|(row_index, col_index, c)| *col_index).collect();
    let bvals = b.iter().map(|(row_index, col_index, c)| *c).collect();
    let crows = c.iter().map(|(row_index, col_index, c)| *row_index).collect();
    let ccols = c.iter().map(|(row_index, col_index, c)| *col_index).collect();
    let cvals = c.iter().map(|(row_index, col_index, c)| *c).collect();
    R1CS {
      arows,
      acols,
      avals,
      brows,
      bcols,
      bvals,
      crows,
      ccols,
      cvals,
      nrows,
      ncols,
      input_size: ell as u64,
    }
  }
}

#[derive(Clone)]
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

