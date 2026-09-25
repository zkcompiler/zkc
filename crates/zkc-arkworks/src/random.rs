use crate::{Bounds, Error, Scalar, bounds::vector};
use ark_std::{
    UniformRand,
    rand::{
        SeedableRng,
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
