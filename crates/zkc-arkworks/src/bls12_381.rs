//! BLS12-381 G2, pairing target and pairings. G1 is [`crate::GroupPoint`].
//! These are arithmetic primitives; no setup or proof system is validated here.
use crate::{Error, GroupPoint, Scalar};
use ark_bls12_381::{Bls12_381, G2Affine, G2Projective};
use ark_ec::{AffineRepr, CurveGroup, VariableBaseMSM, pairing::Pairing};
use ark_ff::{PrimeField, Zero};
use ark_serialize::CanonicalSerialize;

/// Checked prime-order G2 subgroup point with private upstream coordinates.
/// The compressed encoding is the 96-byte big-endian format with the
/// compression, infinity and sign flags in the three most significant bits.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct G2(G2Affine);
impl G2 {
    /// Canonical compressed byte width.
    pub const BYTES: usize = 96;
    /// Standard generator.
    pub fn generator() -> Self {
        Self(G2Affine::generator())
    }
    /// Additive identity.
    pub fn identity() -> Self {
        Self(G2Affine::identity())
    }
    /// Group addition.
    pub fn add(&self, b: &Self) -> Self {
        Self((self.0 + b.0).into_affine())
    }
    /// Additive inverse.
    pub fn neg(&self) -> Self {
        Self(-self.0)
    }
    /// Scalar multiplication; zero is allowed.
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
            G2Projective::msm(&bases, s)
                .map_err(|_| Error::InvalidEncoding)?
                .into_affine(),
        ))
    }
    /// Exact canonical compressed encoding.
    pub fn to_bytes(&self) -> Result<[u8; Self::BYTES], Error> {
        let mut b = [0; Self::BYTES];
        self.0
            .serialize_compressed(&mut b[..])
            .map_err(|_| Error::InvalidEncoding)?;
        Ok(b)
    }
    /// Canonical decoding, including curve, subgroup and unique infinity checks.
    pub fn from_bytes(b: &[u8]) -> Result<Self, Error> {
        if b.len() != Self::BYTES {
            return Err(Error::InvalidEncoding);
        }
        let mut input = b;
        Ok(Self(crate::codec::read(&mut input, Self::BYTES)?))
    }
}

/// Product of pairings equals one. Empty product is one; lengths must match.
/// The caller bounds workload and preparation memory before entering arkworks.
pub fn pairing_check(a: &[GroupPoint], b: &[G2]) -> Result<bool, Error> {
    if a.len() != b.len() {
        return Err(Error::InvalidEncoding);
    }
    Ok(Bls12_381::multi_pairing(a.iter().map(|p| p.0), b.iter().map(|p| p.0)).is_zero())
}

/// Prime-order BLS12-381 pairing target. Abstract additive notation denotes
/// target field multiplication; scalar multiplication denotes exponentiation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Gt(ark_ec::pairing::PairingOutput<Bls12_381>);
impl Gt {
    /// Canonical target-field byte width (twelve base-field coefficients).
    pub const BYTES: usize = 576;
    /// Pairing of the installed source generators.
    pub fn generator() -> Self {
        pairing(&GroupPoint::generator(), &G2::generator())
    }
    /// Multiplicative one, the abstract group identity.
    pub fn identity() -> Self {
        Self(ark_ec::pairing::PairingOutput::zero())
    }
    /// Target group product.
    pub fn add(&self, other: &Self) -> Self {
        Self(self.0 + other.0)
    }
    /// Target group inverse.
    pub fn neg(&self) -> Self {
        Self(-self.0)
    }
    /// Target group exponentiation by a canonical scalar.
    pub fn scale(&self, scalar: Scalar) -> Self {
        Self(self.0 * scalar)
    }
    /// Canonical representation of the twelve base-field coefficients.
    pub fn to_bytes(&self) -> Result<[u8; Self::BYTES], Error> {
        let mut bytes = [0; Self::BYTES];
        self.0
            .serialize_compressed(&mut bytes[..])
            .map_err(|_| Error::InvalidEncoding)?;
        Ok(bytes)
    }
    /// Exact canonical decoding with arkworks' prime-order subgroup check.
    /// In particular, extension-field zero and non-subgroup values are refused.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, Error> {
        if bytes.len() != Self::BYTES {
            return Err(Error::InvalidEncoding);
        }
        let mut input = bytes;
        Ok(Self(crate::codec::read(&mut input, Self::BYTES)?))
    }
}
/// Total bilinear map into the prime-order target, including final exponentiation.
pub fn pairing(a: &GroupPoint, b: &G2) -> Gt {
    Gt(Bls12_381::pairing(a.0, b.0))
}
