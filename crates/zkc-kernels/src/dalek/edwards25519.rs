//! Prime-order Edwards25519 points. Raw encodings enter through explicit checks.
use curve25519_dalek::{
    constants::ED25519_BASEPOINT_POINT,
    edwards::{CompressedEdwardsY, EdwardsPoint},
    scalar::Scalar,
    traits::{Identity, MultiscalarMul},
};

/// The private field prevents native callers from constructing torsion values.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct EdwardsPrime(EdwardsPoint);

fn decode(bytes: &[u8]) -> Option<EdwardsPoint> {
    let compressed = CompressedEdwardsY(bytes.try_into().ok()?);
    let point = compressed.decompress()?;
    // Reject noncanonical y and the negative encoding of x=0.
    (point.compress() == compressed).then_some(point)
}

impl EdwardsPrime {
    pub fn generator() -> Self {
        Self(ED25519_BASEPOINT_POINT)
    }
    pub fn identity() -> Self {
        Self(EdwardsPoint::identity())
    }
    pub fn from_bytes(bytes: &[u8]) -> Option<Self> {
        let point = decode(bytes)?;
        point.is_torsion_free().then_some(Self(point))
    }
    /// Decode a canonical point on the full curve, then multiply by eight.
    /// Callers retain the input bytes separately when their transcript needs them.
    pub fn decode_cofactor(bytes: &[u8]) -> Option<Self> {
        Some(Self(decode(bytes)?.mul_by_cofactor()))
    }
    pub fn to_bytes(self) -> [u8; 32] {
        self.0.compress().to_bytes()
    }
    pub fn scale(self, scalar: Scalar) -> Self {
        Self(self.0 * scalar)
    }
    pub fn msm(scalars: &[Scalar], points: &[Self]) -> Option<Self> {
        if scalars.len() != points.len() {
            return None;
        }
        Some(Self(EdwardsPoint::multiscalar_mul(
            scalars,
            points.iter().map(|p| p.0),
        )))
    }
}

impl std::ops::Add for EdwardsPrime {
    type Output = Self;
    fn add(self, rhs: Self) -> Self {
        Self(self.0 + rhs.0)
    }
}
impl std::ops::Neg for EdwardsPrime {
    type Output = Self;
    fn neg(self) -> Self {
        Self(-self.0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use curve25519_dalek::constants::EIGHT_TORSION;

    #[test]
    fn decoding_keeps_subgroup_and_cofactor_contracts_distinct() {
        let base = ED25519_BASEPOINT_POINT;
        for torsion in EIGHT_TORSION {
            let raw = (base + torsion).compress().to_bytes();
            assert_eq!(
                EdwardsPrime::decode_cofactor(&raw),
                Some(EdwardsPrime(base.mul_by_cofactor()))
            );
            assert_eq!(
                EdwardsPrime::from_bytes(&raw).is_some(),
                torsion == EdwardsPoint::identity()
            );
        }
        let mut negative_zero = EdwardsPoint::identity().compress().to_bytes();
        negative_zero[31] |= 128;
        assert!(EdwardsPrime::decode_cofactor(&negative_zero).is_none());
        let mut noncanonical = [255; 32];
        noncanonical[0] = 237;
        noncanonical[31] = 127;
        assert!(EdwardsPrime::decode_cofactor(&noncanonical).is_none());
        assert!(EdwardsPrime::from_bytes(&[]).is_none());
    }
}
