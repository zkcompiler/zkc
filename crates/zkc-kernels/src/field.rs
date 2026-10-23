//! Field arithmetic independent of VM values and physical identities.
use std::ops::{Add, Mul, Neg, Sub};

/// Invalid mathematical extents or noncanonical element encodings.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    LengthMismatch,
    CapacityOverflow,
    PackingUnavailable,
    NoncanonicalScalar,
    WireLength,
    ZeroInverse,
}
impl Error {
    pub const fn code(self) -> &'static str {
        match self {
            Self::LengthMismatch => "length-mismatch",
            Self::CapacityOverflow => "capacity-overflow",
            Self::PackingUnavailable => "packing-unavailable",
            Self::NoncanonicalScalar => "noncanonical-scalar",
            Self::WireLength => "wire-length",
            Self::ZeroInverse => "zero-inverse",
        }
    }
}
impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.code())
    }
}
impl std::error::Error for Error {}
pub type Result<T> = std::result::Result<T, Error>;

/// Field operations used by the shared vector, matrix and polynomial kernels.
/// Implementations obey the field laws: `inverse` is `None` exactly at zero,
/// and the selected packing performs the same operations independently in each
/// lane. Implementing this trait does not install a VM type or operation.
pub trait Coefficient:
    Copy
    + Send
    + Sync
    + PartialEq
    + Add<Output = Self>
    + Sub<Output = Self>
    + Mul<Output = Self>
    + Neg<Output = Self>
{
    type Packing: crate::vector::Packing<Self>;
    /// Conservative setup work for the selected dot product, in the caller's
    /// numerical admission units; this is not a CPU-time estimate.
    const DOT_SETUP_WORK: u64 = 1;
    /// Exact dot product, refusing unequal extents with `LengthMismatch` before
    /// performing arithmetic. The empty product sum is zero.
    fn dot_product(a: &[Self], b: &[Self]) -> Result<Self> {
        crate::vector::equal_len(a.len(), b.len())?;
        Ok(a.iter().zip(b).fold(Self::zero(), |s, (a, b)| s + *a * *b))
    }
    fn zero() -> Self;
    fn one() -> Self;
    fn inverse(self) -> Option<Self>;
}
