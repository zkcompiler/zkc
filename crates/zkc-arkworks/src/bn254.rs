//! BN254 arithmetic primitives. No proof system or trusted-setup validation.
use crate::Error;
/// BN254 scalar field.
pub use ark_bn254::Fr as Scalar;
use ark_ec::{AffineRepr, CurveGroup, VariableBaseMSM, pairing::Pairing};
use ark_ff::{PrimeField, Zero};
use ark_serialize::CanonicalSerialize;
/// Exact scalar modulus.
pub const MODULUS: &str =
    "21888242871839275222246405745257275088548364400416034343698204186575808495617";
/// Parse a canonical nonnegative decimal strictly below the modulus.
pub fn parse_decimal(s: &str) -> Result<Scalar, Error> {
    if s.is_empty()
        || !s.bytes().all(|b| b.is_ascii_digit())
        || (s.len() > 1 && s.starts_with('0'))
        || s.len() > MODULUS.len()
        || (s.len() == MODULUS.len() && s >= MODULUS)
    {
        return Err(Error::NonCanonicalEncoding);
    }
    Ok(s.bytes().fold(Scalar::from(0), |a, b| {
        a * Scalar::from(10) + Scalar::from(u64::from(b - b'0'))
    }))
}
/// Canonical little-endian scalar encoding.
pub fn encode_scalar(s: &Scalar) -> Result<[u8; 32], Error> {
    let mut b = [0; 32];
    s.serialize_compressed(&mut b[..])
        .map_err(|_| Error::InvalidEncoding)?;
    Ok(b)
}
/// Exact canonical scalar decoding, without modular reduction.
pub fn decode_scalar(b: &[u8]) -> Result<Scalar, Error> {
    if b.len() != 32 {
        return Err(Error::InvalidEncoding);
    }
    let mut input = b;
    crate::codec::read(&mut input, 32)
}
macro_rules! group {
    ($name:ident,$affine:ty,$projective:ty,$width:expr) => {
        /// Checked prime-order subgroup point with private upstream coordinates.
        #[derive(Clone, Copy, Debug, PartialEq, Eq)]
        pub struct $name($affine);
        impl $name {
            /// Canonical compressed byte width.
            pub const BYTES: usize = $width;
            /// Standard generator.
            pub fn generator() -> Self {
                Self(<$affine>::generator())
            }
            /// Additive identity.
            pub fn identity() -> Self {
                Self(<$affine>::identity())
            }
            /// Group addition.
            pub fn add(&self, b: &Self) -> Self {
                Self((self.0 + b.0).into_affine())
            }
            /// Additive inverse.
            pub fn neg(&self) -> Self {
                Self(-self.0)
            }
            /// Scalar multiplication.
            pub fn scale(&self, s: Scalar) -> Self {
                Self(self.0.mul_bigint(s.into_bigint()).into_affine())
            }
            /// Checked equal-length MSM. The caller bounds workload and scratch memory.
            pub fn msm(s: &[Scalar], p: &[Self]) -> Result<Self, Error> {
                if s.len() != p.len() {
                    return Err(Error::InvalidEncoding);
                }
                let mut bases = crate::bounds::vector(p.len())?;
                bases.extend(p.iter().map(|p| p.0));
                Ok(Self(
                    <$projective>::msm(&bases, s)
                        .map_err(|_| Error::InvalidEncoding)?
                        .into_affine(),
                ))
            }
            /// Exact canonical compressed encoding.
            pub fn to_bytes(&self) -> Result<[u8; $width], Error> {
                let mut b = [0; $width];
                self.0
                    .serialize_compressed(&mut b[..])
                    .map_err(|_| Error::InvalidEncoding)?;
                Ok(b)
            }
            /// Canonical decoding, including curve, subgroup and unique infinity checks.
            pub fn from_bytes(b: &[u8]) -> Result<Self, Error> {
                if b.len() != $width {
                    return Err(Error::InvalidEncoding);
                }
                let mut input = b;
                Ok(Self(crate::codec::read(&mut input, $width)?))
            }
            /// Validate affine coordinates supplied by a format adapter.
            pub fn from_affine(point: $affine) -> Result<Self, Error> {
                if !point.is_on_curve() || !point.is_in_correct_subgroup_assuming_on_curve() {
                    return Err(Error::InvalidEncoding);
                }
                // Normalize infinity so raw coordinates cannot introduce aliases.
                Ok(if point.is_zero() {
                    Self::identity()
                } else {
                    Self(point)
                })
            }
        }
    };
}
group!(G1, ark_bn254::G1Affine, ark_bn254::G1Projective, 32);
group!(G2, ark_bn254::G2Affine, ark_bn254::G2Projective, 64);
/// Product of pairings equals one. Empty product is one; lengths must match.
/// The caller bounds workload and preparation memory before entering arkworks.
pub fn pairing_check(a: &[G1], b: &[G2]) -> Result<bool, Error> {
    if a.len() != b.len() {
        return Err(Error::InvalidEncoding);
    }
    Ok(ark_bn254::Bn254::multi_pairing(a.iter().map(|p| p.0), b.iter().map(|p| p.0)).is_zero())
}
