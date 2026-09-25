//! Validated BLS12-381 G1 points using the same arkworks library as PCS.
use crate::{Error, Scalar};
use ark_bls12_381::G1Affine;
use ark_ec::{AffineRepr, CurveGroup, VariableBaseMSM};
use ark_ff::PrimeField;
use ark_serialize::CanonicalSerialize;

/// Exact compressed G1 width.
pub const GROUP_BYTES: usize = 48;
/// A subgroup point. Raw upstream coordinates cannot bypass checked decoding.
/// Identity and zero scalar multiplication are legitimate group operations.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct GroupPoint(G1Affine);
impl GroupPoint {
    /// Standard arkworks G1 generator.
    pub fn generator() -> Self {
        Self(G1Affine::generator())
    }
    /// Additive identity (accepted in public codecs and multi-base commitment).
    pub fn identity() -> Self {
        Self(G1Affine::identity())
    }
    /// Group addition.
    pub fn add(&self, other: &Self) -> Self {
        Self((self.0 + other.0).into_affine())
    }
    /// Additive inverse in the prime subgroup.
    pub fn neg(&self) -> Self {
        Self(-self.0)
    }
    /// Checked native MSM; no mismatched-length truncation.
    pub fn msm(scalars: &[Scalar], points: &[Self]) -> Result<Self, Error> {
        if scalars.len() != points.len() {
            return Err(Error::InvalidEncoding);
        }
        let mut bases = crate::bounds::vector(points.len())?;
        bases.extend(points.iter().map(|p| p.0));
        Ok(Self(
            ark_bls12_381::G1Projective::msm(&bases, scalars)
                .map_err(|_| Error::InvalidEncoding)?
                .into_affine(),
        ))
    }
    /// Scalar multiplication; zero is allowed.
    pub fn scale(&self, scalar: Scalar) -> Self {
        Self(self.0.mul_bigint(scalar.into_bigint()).into_affine())
    }
    /// Encode a validated point with canonical compressed arkworks encoding.
    pub fn to_bytes(&self) -> Result<[u8; GROUP_BYTES], Error> {
        let mut bytes = [0; GROUP_BYTES];
        self.0
            .serialize_compressed(&mut bytes[..])
            .map_err(|_| Error::InvalidEncoding)?;
        Ok(bytes)
    }
    /// Exact compressed canonical subgroup decode, including unique infinity.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, Error> {
        if bytes.len() != GROUP_BYTES {
            return Err(Error::InvalidEncoding);
        }
        let mut input = bytes;
        let point = crate::codec::read(&mut input, GROUP_BYTES)?;
        crate::codec::finish(input)?;
        Ok(Self(point))
    }
}
/// Interpret 64 transcript bytes as a big-endian integer modulo Fr. Zero is
/// allowed. This finite sampler is not claimed to be exactly uniform.
pub fn scalar_from_wide_be(bytes: &[u8; 64]) -> Scalar {
    Scalar::from_be_bytes_mod_order(bytes)
}
