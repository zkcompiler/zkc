#![allow(dead_code)]
use ark_std::rand::{SeedableRng, rngs::StdRng};
use zkc_arkworks::{Bounds, Keys, Scalar};

pub fn bounds() -> Bounds {
    Bounds::new(10, 1024, 1 << 20, 10 * 1024)
}

// Deterministic setup is solely a test fixture, never a security experiment.
pub fn keys(n: usize, seed: u8) -> Keys {
    Keys::setup_with_rng(n, &mut StdRng::from_seed([seed; 32]), &bounds()).unwrap()
}

pub fn scalars(values: &[u64]) -> Vec<Scalar> {
    values.iter().copied().map(Scalar::from).collect()
}
