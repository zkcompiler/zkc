//! Isolated executable equations, not a compiler or a security implementation.
//! The native prover and exact validator never call an upstream proof algorithm.

pub mod baseline;
mod codec;
pub mod experiment;
mod generators;
mod linear;
mod prover;
mod transcript;
mod verifier;

use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
pub use generators::Generators;
pub use prover::{ProverMode, prove};
pub use transcript::{APP_DOMAIN, application_transcript, require_nonzero};
pub use verifier::{EquationReport, VerifierMode, evaluate, validate};

pub type Result<T> = std::result::Result<T, Error>;

/// Stable refusal codes, local to this research crate.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    Bits,
    Count,
    Overflow,
    ResourceLimit,
    Shape,
    Context,
    Length,
    CurveEncoding,
    NoncanonicalScalar,
    IdentityPoint,
    ZeroChallenge(&'static str),
    WitnessRange,
    WitnessCommitment,
    RangeEquation,
    IpaEquation,
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "RANGE-NATIVE-{self:?}")
    }
}
impl std::error::Error for Error {}

/// An explicit bounded allocation profile; not an arbitrary-count padding rule.
pub const MAX_TOTAL_BITS: usize = 16384;
pub const MAX_CONTEXT_BYTES: usize = 65536;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Dimensions {
    pub(crate) n: usize,
    pub(crate) m: usize,
    pub(crate) total: usize,
}
impl Dimensions {
    pub fn new(n: usize, m: usize) -> Result<Self> {
        if !matches!(n, 8 | 16 | 32 | 64) {
            return Err(Error::Bits);
        }
        if !m.is_power_of_two() {
            return Err(Error::Count);
        }
        let total = n.checked_mul(m).ok_or(Error::Overflow)?;
        if m > u32::MAX as usize || total > MAX_TOTAL_BITS {
            return Err(Error::ResourceLimit);
        }
        Ok(Self { n, m, total })
    }
    pub fn bits(self) -> usize {
        self.n
    }
    pub fn count(self) -> usize {
        self.m
    }
    pub fn total(self) -> usize {
        self.total
    }
    pub fn rounds(self) -> usize {
        self.total.ilog2() as usize
    }
    pub fn proof_len(self) -> usize {
        32 * (9 + 2 * self.rounds())
    }
}

/// Supplied by the validator's caller, outside the raw upstream proof bytes.
/// `context` must be the actual application's canonical public subject.
#[derive(Clone, Debug)]
pub struct Statement {
    pub bits: usize,
    pub count: usize,
    pub context: Vec<u8>,
    pub commitments: Vec<[u8; 32]>,
}
impl Statement {
    pub fn dimensions(&self) -> Result<Dimensions> {
        let d = Dimensions::new(self.bits, self.count)?;
        if self.commitments.len() != d.m {
            return Err(Error::Count);
        }
        if self.context.is_empty() || self.context.len() > MAX_CONTEXT_BYTES {
            return Err(Error::Context);
        }
        Ok(d)
    }
    pub(crate) fn decode(&self, gens: &Generators) -> Result<Vec<RistrettoPoint>> {
        if self.dimensions()? != gens.dimensions() {
            return Err(Error::Shape);
        }
        self.commitments
            .iter()
            .map(|b| decode_point(*b, false))
            .collect()
    }
}

pub(crate) fn decode_point(bytes: [u8; 32], nonidentity: bool) -> Result<RistrettoPoint> {
    use curve25519_dalek::traits::IsIdentity;
    let p = CompressedRistretto(bytes)
        .decompress()
        .ok_or(Error::CurveEncoding)?;
    if p.compress().to_bytes() != bytes {
        return Err(Error::CurveEncoding);
    }
    if nonidentity && p.is_identity() {
        return Err(Error::IdentityPoint);
    }
    Ok(p)
}

#[cfg(test)]
mod tests;
