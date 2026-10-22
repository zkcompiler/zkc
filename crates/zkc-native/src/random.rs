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
    fn owned_source_matches_one_advancing_mixed_field_stream() {
        let seed = [47; 32];
        let mut source = RandomSource::for_testing(seed);
        let mut expected = StdRng::from_seed(seed);
        for round in 0..32 {
            // Asymmetric requests detect per-field resets or separate streams.
            if round % 3 == 0 {
                assert_eq!(source.bn254_scalar(), Bn254Scalar::rand(&mut expected));
            }
            assert_eq!(source.scalar(), Scalar::rand(&mut expected));
            assert_eq!(source.bn254_scalar(), Bn254Scalar::rand(&mut expected));
        }
        let mut os = RandomSource::from_os().unwrap();
        let _ = (os.scalar(), os.bn254_scalar());
    }
}
