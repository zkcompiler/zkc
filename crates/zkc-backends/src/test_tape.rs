//! Typed deterministic scalar tapes for test providers only.
use crate::{Bn254Scalar, RistrettoScalar, Scalar};
use zkc_runtime::vm::Identity;

#[derive(Clone)]
pub enum TestTape {
    Bls12381(Vec<Scalar>),
    Bn254(Vec<Bn254Scalar>),
    Ristretto(Vec<RistrettoScalar>),
}
impl TestTape {
    pub fn identity(&self) -> Identity {
        match self {
            Self::Bls12381(_) => Identity::Bls12381Fr,
            Self::Bn254(_) => Identity::Bn254Fr,
            Self::Ristretto(_) => Identity::Ristretto255Scalar,
        }
    }
    pub fn len(&self) -> usize {
        match self {
            Self::Bls12381(v) => v.len(),
            Self::Bn254(v) => v.len(),
            Self::Ristretto(v) => v.len(),
        }
    }
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}
impl From<Vec<Scalar>> for TestTape {
    fn from(values: Vec<Scalar>) -> Self {
        Self::Bls12381(values)
    }
}
impl From<Vec<Bn254Scalar>> for TestTape {
    fn from(values: Vec<Bn254Scalar>) -> Self {
        Self::Bn254(values)
    }
}
impl From<Vec<RistrettoScalar>> for TestTape {
    fn from(values: Vec<RistrettoScalar>) -> Self {
        Self::Ristretto(values)
    }
}
