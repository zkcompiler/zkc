//! Advancing native CSPRNG state. It is neither clonable nor a kernel cache.
use crate::{Bn254Scalar, Result, Scalar, exhausted};
use ark_std::{
    UniformRand,
    rand::{
        SeedableRng,
        rngs::{OsRng, StdRng},
    },
};

pub(crate) struct RandomSource {
    rng: StdRng,
}
impl RandomSource {
    pub(crate) fn from_os() -> Result<Self> {
        Ok(Self {
            rng: StdRng::from_rng(OsRng).map_err(|_| exhausted("entropy-unavailable"))?,
        })
    }
    #[cfg(feature = "test-utils")]
    pub(crate) fn for_testing(seed: [u8; 32]) -> Self {
        Self {
            rng: StdRng::from_seed(seed),
        }
    }
    pub(crate) fn scalar(&mut self) -> Scalar {
        Scalar::rand(&mut self.rng)
    }
    pub(crate) fn bn254_scalar(&mut self) -> Bn254Scalar {
        Bn254Scalar::rand(&mut self.rng)
    }
}

#[cfg(all(test, feature = "test-utils"))]
mod tests {
    use super::*;
    #[test]
    fn owned_sources_advance_without_cloning_or_cross_field_reset() {
        let mut a = RandomSource::for_testing([47; 32]);
        let mut b = RandomSource::for_testing([47; 32]);
        for _ in 0..32 {
            assert_eq!(a.scalar(), b.scalar());
            assert_eq!(a.bn254_scalar(), b.bn254_scalar());
        }
        let mut os = RandomSource::from_os().unwrap();
        let _ = (os.scalar(), os.bn254_scalar());
    }
}
