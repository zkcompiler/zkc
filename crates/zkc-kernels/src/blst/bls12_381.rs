//! Prime-subgroup BLS12-381 arithmetic using blstrs on blst.
//!
//! MSM uses variable-time Pippenger. This provider makes no whole-program timing
//! guarantee. The pinned blst dependency disables its internal worker pool.
//! Callers admit lengths, staging and foreign workspace before entering kernels.
//! Owned bulk carriers borrow the upstream MSM ABI directly.
#![doc = include_str!("bls12_381/README.md")]
use group::{Curve, Group};

/// Upstream mathematical element types for trusted backend family adapters.
/// These are provider-private representation choices, not wire encodings.
/// Raw coordinate fabrication/mutation is outside the mathematical premises;
/// external input must use this module's checked canonical decoders.
pub use blstrs::{G1Projective as G1Element, G2Projective as G2Element, Scalar as ScalarElement};

mod scalar;
pub use scalar::{Scalar, parse_decimal};
mod bulk;
pub use bulk::{G1Vector, G2Vector, ScalarVector};

/// A kernel refusal; malformed input is distinct from a false pairing equation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// Input does not have the exact canonical encoding or subgroup.
    InvalidEncoding,
    /// Corresponding vectors have different lengths.
    LengthMismatch,
    /// A buffer size cannot be represented on this host.
    CapacityOverflow,
    /// A caller-owned fallible buffer reservation failed.
    Allocation,
}
impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Self::InvalidEncoding => "invalid-encoding",
            Self::LengthMismatch => "length-mismatch",
            Self::CapacityOverflow => "capacity-overflow",
            Self::Allocation => "allocation-failed",
        })
    }
}
impl std::error::Error for Error {}

fn vector<T>(len: usize) -> Result<Vec<T>, Error> {
    len.checked_mul(size_of::<T>())
        .filter(|bytes| *bytes <= isize::MAX as usize)
        .ok_or(Error::CapacityOverflow)?;
    if len == 0 {
        return Ok(Vec::new());
    }
    crate::allocation::reserve(len).map_err(|_| Error::Allocation)
}

/// Exact canonical little-endian scalar decoding; never reduces modulo the order.
pub fn decode_scalar(bytes: &[u8]) -> Result<Scalar, Error> {
    let bytes = bytes.try_into().map_err(|_| Error::InvalidEncoding)?;
    Option::from(blstrs::Scalar::from_bytes_le(bytes))
        .map(Scalar)
        .ok_or(Error::InvalidEncoding)
}

macro_rules! source_group {
    ($name:ident, $bulk:ident, $projective:ty, $affine:ty, $bytes:expr) => {
        /// Prime-subgroup point with private provider coordinates, including identity.
        #[derive(Clone, Copy, Debug, PartialEq, Eq)]
        pub struct $name($projective);
        impl $name {
            /// Canonical compressed width in bytes.
            pub const BYTES: usize = $bytes;
            /// Adopt a trusted prime-subgroup upstream value in O(1). This is
            /// the same representation, with no encoding or subgroup check.
            /// The caller must not fabricate/mutate unchecked raw coordinates;
            /// untrusted input must enter through `from_bytes` instead.
            pub fn from_element(element: $projective) -> Self {
                Self(element)
            }
            /// Move the mathematical element into a trusted family adapter.
            pub fn into_element(self) -> $projective {
                self.0
            }
            /// Standard prime-subgroup generator.
            pub fn generator() -> Self {
                Self(<$projective>::generator())
            }
            /// Additive identity.
            pub fn identity() -> Self {
                Self(<$projective>::identity())
            }
            /// Group addition.
            pub fn add(&self, rhs: &Self) -> Self {
                Self(self.0 + rhs.0)
            }
            /// Additive inverse.
            pub fn neg(&self) -> Self {
                Self(-self.0)
            }
            /// Mathematical group equality, independent of projective coordinates.
            pub fn equal(&self, rhs: &Self) -> bool {
                self == rhs
            }
            /// Scalar multiplication; zero and identity are allowed.
            pub fn scale(&self, scalar: Scalar) -> Self {
                Self(self.0 * scalar.0)
            }
            /// Canonical compressed big-endian encoding with unique infinity.
            pub fn to_bytes(&self) -> [u8; Self::BYTES] {
                self.0.to_compressed()
            }
            /// Exact checked curve/subgroup decode, followed by canonical re-encoding.
            pub fn from_bytes(bytes: &[u8]) -> Result<Self, Error> {
                let encoded = bytes.try_into().map_err(|_| Error::InvalidEncoding)?;
                let point = Option::<$affine>::from(<$affine>::from_compressed(encoded))
                    .ok_or(Error::InvalidEncoding)?;
                if point.to_compressed().as_slice() != bytes {
                    return Err(Error::InvalidEncoding);
                }
                Ok(Self(point.into()))
            }
            /// Equal-length variable-time MSM. Empty inputs produce identity.
            /// This slice adapter copies wrappers once per call; use the owned
            /// bulk carrier's `msm` to retain upstream storage across calls.
            pub fn msm(scalars: &[Scalar], points: &[Self]) -> Result<Self, Error> {
                if scalars.len() != points.len() {
                    return Err(Error::LengthMismatch);
                }
                // Upstream indexes the first point; mismatches can panic or truncate.
                if points.is_empty() {
                    return Ok(Self::identity());
                }
                $bulk::from_slice(points)?.msm(&ScalarVector::from_slice(scalars)?)
            }
        }
    };
}
source_group!(G1, G1Vector, blstrs::G1Projective, blstrs::G1Affine, 48);
source_group!(G2, G2Vector, blstrs::G2Projective, blstrs::G2Affine, 96);

/// Product of pairings equals one. No hashing, signatures or BLS ciphersuite is
/// involved. Validated points are aggregated in order; the empty product is one.
pub fn pairing_check(left: &[G1], right: &[G2]) -> Result<bool, Error> {
    if left.len() != right.len() {
        return Err(Error::LengthMismatch);
    }
    Ok(pairing_product(
        left.iter().copied().zip(right.iter().copied()),
    ))
}

/// Pairing-product check borrowing resident storage without wrapper vectors.
/// Equal extents are checked before entering the foreign aggregation API.
pub fn pairing_check_bulk(left: &G1Vector, right: &G2Vector) -> Result<bool, Error> {
    if left.len() != right.len() {
        return Err(Error::LengthMismatch);
    }
    Ok(pairing_product(left.iter().zip(right.iter())))
}

fn pairing_product(pairs: impl Iterator<Item = (G1, G2)>) -> bool {
    // raw_aggregate is a signature accumulator: an empty context final-verifies
    // as false, and batched Miller loops need finite factors. Remove units
    // before allocating the context, including the all-identity case.
    let mut pairs = pairs
        .filter(|(p, q)| !bool::from(p.0.is_identity()) && !bool::from(q.0.is_identity()))
        .peekable();
    if pairs.peek().is_none() {
        return true;
    }
    let mut product = blst::Pairing::new(false, &[]);
    for (p, q) in pairs {
        product.raw_aggregate(q.0.to_affine().as_ref(), p.0.to_affine().as_ref());
    }
    product.commit();
    product.finalverify(None)
}

/// Conservative foreign MSM workspace including point copies, affine conversion,
/// scalar copies/bytes, Pippenger buckets and pinned small-input C stack tables.
/// The same conservative bound applies to resident MSM (which omits wrapper
/// copies). Excludes caller input/output staging and process/allocator overhead.
/// In blst 0.3.17, the bucket count is at most max(2, n), with 384-byte G2 XYZZ
/// buckets. The additional linear allowance covers both groups' Rust buffers.
/// Re-audit this bound when upgrading the pinned provider.
pub fn msm_workspace_bytes(len: usize) -> Result<usize, Error> {
    if len == 0 {
        return Ok(0);
    }
    // Below 32, nested G2 window precomputation uses up to 142,848 stack bytes.
    // At larger lengths, Pippenger replaces those tables. The fixed allowances
    // also cover the pinned affine-conversion and aggregation stack temporaries.
    let fixed = if len < 32 { 256 * 1024 } else { 32 * 1024 };
    len.checked_mul(1024)
        .and_then(|bytes| bytes.checked_add(fixed))
        .ok_or(Error::CapacityOverflow)
}

/// Conservative bound for blst's fixed-size pairing aggregation context.
pub const PAIRING_WORKSPACE_BYTES: usize = 16 * 1024;

pub mod arkworks {
    //! Checked canonical representation bridges. These are real conversions,
    //! not transmutations; callers include their costs in the selected operation.
    use super::{Error, G1, G2, Scalar, decode_scalar};
    use crate::arkworks::bls12_381 as ark;

    /// Import an already validated Arkworks scalar without modular reduction.
    pub fn import_scalar(scalar: ark::Scalar) -> Result<Scalar, Error> {
        decode_scalar(&ark::encode_scalar(&scalar).map_err(|_| Error::InvalidEncoding)?)
    }
    /// Export through the exact shared canonical scalar encoding.
    pub fn export_scalar(scalar: Scalar) -> Result<ark::Scalar, Error> {
        ark::decode_scalar(&scalar.to_bytes_le()).map_err(|_| Error::InvalidEncoding)
    }
    macro_rules! bridge {
        ($point:ident, $import:ident, $export:ident) => {
            /// Import through the exact shared canonical encoding.
            pub fn $import(point: ark::$point) -> Result<$point, Error> {
                $point::from_bytes(&point.to_bytes().map_err(|_| Error::InvalidEncoding)?)
            }
            /// Export through the exact shared canonical encoding.
            pub fn $export(point: $point) -> Result<ark::$point, Error> {
                ark::$point::from_bytes(&point.to_bytes()).map_err(|_| Error::InvalidEncoding)
            }
        };
    }
    bridge!(G1, import_g1, export_g1);
    bridge!(G2, import_g2, export_g2);
}

#[cfg(test)]
mod tests;
