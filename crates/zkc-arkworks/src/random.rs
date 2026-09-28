use crate::{Bounds, Error, Scalar, bounds::vector};
use ark_std::{
    UniformRand,
    rand::{
        RngCore, SeedableRng,
        rngs::{OsRng, StdRng},
    },
};

/// An OS-seeded CSPRNG for local development setup and fresh field challenges.
/// Not cloneable; no API forks, resets or exposes the live generator state.
/// Randomness scheduling and resource ownership belong to the calling runtime.
pub struct RandomSource {
    pub(crate) rng: StdRng,
}

impl RandomSource {
    /// Seed once using fallible OS entropy. Subsequent field draws use the
    /// upstream uniform rejection sampler and this CSPRNG's advancing state.
    pub fn from_os() -> Result<Self, Error> {
        Ok(Self {
            rng: StdRng::from_rng(OsRng).map_err(|_| Error::EntropyUnavailable)?,
        })
    }

    /// Deterministic correctness fixtures only. Never a setup ceremony or
    /// evidence for freshness/unpredictability. Requires `test-utils`.
    #[cfg(feature = "test-utils")]
    pub fn for_testing(seed: [u8; 32]) -> Self {
        Self {
            rng: StdRng::from_seed(seed),
        }
    }

    /// Draw one uniformly distributed Fr value using upstream sampling.
    pub fn scalar(&mut self) -> Scalar {
        Scalar::rand(&mut self.rng)
    }

    /// Rejection sampling from canonical 256-bit encodings. Every nonzero Fr
    /// value has one accepted encoding; no modular reduction biases the draw.
    /// The cap is a physical stop, not an alternative mathematical outcome.
    pub fn nonzero_scalar(&mut self) -> Result<crate::NonzeroScalar, Error> {
        nonzero_scalar_with(|| {
            let mut bytes = [0; 32];
            self.rng.fill_bytes(&mut bytes);
            bytes
        })
    }

    /// Draw a uniformly sampled BN254 scalar from this advancing OS-seeded source.
    pub fn bn254_scalar(&mut self) -> crate::bn254::Scalar {
        crate::bn254::Scalar::rand(&mut self.rng)
    }

    /// Draw a point after checking admission and reserving its vector storage.
    /// Failed shape/reservation admission consumes no draws. Empty points are
    /// allowed for zero-variable table evaluation.
    pub fn point(&mut self, n: usize, bounds: &Bounds) -> Result<Vec<Scalar>, Error> {
        bounds.arity(n)?;
        let bytes = n
            .checked_mul(crate::SCALAR_BYTES)
            .ok_or(Error::CapacityOverflow)?;
        bounds.bytes(bytes)?;
        let mut point = vector(n)?;
        for _ in 0..n {
            point.push(self.scalar());
        }
        Ok(point)
    }
}

/// Maximum candidate encodings per nonzero scalar draw.
pub const NONZERO_SAMPLING_ATTEMPTS: usize = 128;

fn nonzero_scalar_with(mut bytes: impl FnMut() -> [u8; 32]) -> Result<crate::NonzeroScalar, Error> {
    for _ in 0..NONZERO_SAMPLING_ATTEMPTS {
        if let Ok(value) = crate::NonzeroScalar::from_bytes(&bytes()) {
            return Ok(value);
        }
    }
    Err(Error::SamplingLimit)
}

#[cfg(test)]
mod nonzero_sampling_tests {
    use super::*;

    #[test]
    fn rejects_zero_and_noncanonical_candidates_without_reduction() {
        let expected = crate::NonzeroScalar::new(Scalar::from(7)).unwrap();
        let mut candidates = [[0; 32], [255; 32], expected.to_bytes().unwrap()].into_iter();
        assert_eq!(
            nonzero_scalar_with(|| candidates.next().unwrap()),
            Ok(expected)
        );
        assert!(candidates.next().is_none());
    }

    #[test]
    fn rejection_is_bounded_and_never_returns_a_sentinel() {
        for bytes in [[0; 32], [255; 32]] {
            let mut count = 0;
            assert_eq!(
                nonzero_scalar_with(|| {
                    count += 1;
                    bytes
                }),
                Err(Error::SamplingLimit)
            );
            assert_eq!(count, NONZERO_SAMPLING_ATTEMPTS);
        }
    }
}
