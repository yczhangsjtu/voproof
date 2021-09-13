use ark_ff::Field;

pub trait CSSize {}
pub trait ConstraintSystem<F: Field, S: CSSize> {
    fn get_size(&self) -> S;
}
pub trait Instance<F: Field> {}
pub trait Witness<F: Field> {}

pub mod r1cs;
pub mod hpr;
pub mod pov;
