use super::*;
use ark_ff::Field;
use super::circuit::fan_in_two::FanInTwoCircuit;

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
      n: self.consts.len() as u64 + self.nmul + self.nadd,
    }
  }
}

#[derive(Clone)]
pub struct POVSize {
  pub nconsts: u64,
  pub nmul: u64,
  pub nadd: u64,
  pub n: u64,
}

impl CSSize for POVSize {}

pub struct POVInstance<F: Field> {
  pub instance: (Vec<u64>, Vec<F>),
}

pub struct POVWitness<F: Field> {
  pub witness: (Vec<F>, Vec<F>, Vec<F>),
}

impl<F: Field> Instance<F> for POVInstance<F> {}
impl<F: Field> Witness<F> for POVWitness<F> {}

impl<F: Field> From<FanInTwoCircuit<F>> for POV<F> {
  fn from(circuit: FanInTwoCircuit<F>) -> POV<F> {
    POV {
      consts: circuit.get_consts(),
      wires: circuit.get_wiring().unwrap(),
      nmul: circuit.get_mul_num() as u64,
      nadd: circuit.get_add_num() as u64,
    }
  }
}
