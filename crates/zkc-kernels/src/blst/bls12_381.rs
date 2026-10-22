//! Prime-subgroup BLS12-381 arithmetic using blstrs on blst.
//!
//! MSM uses variable-time Pippenger. This provider makes no whole-program timing
//! guarantee. The pinned blst dependency disables its internal worker pool.
//! Callers admit lengths, staging and foreign workspace before entering kernels.
use group::{Curve, Group};

/// Canonical scalar with private Montgomery coordinates.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Scalar(blstrs::Scalar);
impl From<u64> for Scalar {
    fn from(value: u64) -> Self {
        Self(blstrs::Scalar::from(value))
    }
}
impl Scalar {
    /// Exact canonical little-endian encoding.
    pub fn to_bytes_le(self) -> [u8; 32] {
        self.0.to_bytes_le()
    }
}

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
    ($name:ident, $projective:ty, $affine:ty, $bytes:expr) => {
        /// Prime-subgroup point with private provider coordinates, including identity.
        #[derive(Clone, Copy, Debug, PartialEq, Eq)]
        pub struct $name($projective);
        impl $name {
            /// Canonical compressed width in bytes.
            pub const BYTES: usize = $bytes;
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
            pub fn msm(scalars: &[Scalar], points: &[Self]) -> Result<Self, Error> {
                if scalars.len() != points.len() {
                    return Err(Error::LengthMismatch);
                }
                // Upstream indexes the first point; mismatches can panic or truncate.
                if points.is_empty() {
                    return Ok(Self::identity());
                }
                let mut bases = vector(points.len())?;
                bases.extend(points.iter().map(|p| p.0));
                let mut factors = vector(scalars.len())?;
                factors.extend(scalars.iter().map(|s| s.0));
                Ok(Self(<$projective>::multi_exp(&bases, &factors)))
            }
        }
    };
}
source_group!(G1, blstrs::G1Projective, blstrs::G1Affine, 48);
source_group!(G2, blstrs::G2Projective, blstrs::G2Affine, 96);

/// Product of pairings equals one. No hashing, signatures or BLS ciphersuite is
/// involved. Validated points are aggregated in order; the empty product is one.
pub fn pairing_check(left: &[G1], right: &[G2]) -> Result<bool, Error> {
    if left.len() != right.len() {
        return Err(Error::LengthMismatch);
    }
    if left.is_empty() {
        return Ok(true);
    }
    let mut product = blst::Pairing::new(false, &[]);
    let mut nonidentity = false;
    for (p, q) in left.iter().zip(right) {
        // raw_aggregate is a signature accumulator: an entirely empty context
        // final-verifies as false, and batched Miller loops need finite factors.
        // Remove mathematical unit factors before entering that API.
        if bool::from(p.0.is_identity()) || bool::from(q.0.is_identity()) {
            continue;
        }
        nonidentity = true;
        product.raw_aggregate(q.0.to_affine().as_ref(), p.0.to_affine().as_ref());
    }
    if !nonidentity {
        return Ok(true);
    }
    product.commit();
    Ok(product.finalverify(None))
}

/// Conservative foreign MSM workspace including point copies, affine conversion,
/// scalar copies/bytes, Pippenger buckets and pinned small-input C stack tables.
/// Excludes caller input/output staging and total process/allocator overhead.
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
