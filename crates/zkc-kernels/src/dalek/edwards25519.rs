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
    // Reject noncanonical y and the negative encoding of x=0, as Monero does.
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

// Algebraic form of ge_fromfe_frombytes_vartime in Monero
// 4f92268d7c16741cfb41e5bbe2aa46cc260a9ea5, src/crypto/crypto-ops.c.
// Its sign test and Edwards y coordinate suffice: dalek reconstructs x.
// This is the legacy field-element map, not an RFC 9380 hash-to-curve suite.
// See interop/UPSTREAM-LICENSE-BSD. The implementation is variable-time; use it for public generator inputs.
#[derive(ark_ff::MontConfig)]
#[modulus = "57896044618658097711785492504343953926634992332820282019728792003956564819949"]
#[generator = "2"]
struct BaseConfig;
type Base = ark_ff::Fp256<ark_ff::MontBackend<BaseConfig, 4>>;

pub fn map(bytes: [u8; 32]) -> Option<EdwardsPrime> {
    use ark_ff::{AdditiveGroup, BigInteger, Field, PrimeField};
    let u = Base::from_le_bytes_mod_order(&bytes);
    let v = u.square().double();
    let w = v + Base::from(1u64);
    let a = Base::from(486662u64);
    let denominator = w.square() - a.square() * v;
    let cube = denominator.square() * denominator;
    let seventh = cube.square() * denominator;
    let candidate = w
        * cube
        * (w * seventh).pow([
            0xfffffffffffffffd,
            0xffffffffffffffff,
            0xffffffffffffffff,
            0x0fffffffffffffff,
        ]);
    let check = candidate.square() * denominator;
    let negative = check != w && check != -w;
    let z = -a * if negative { Base::from(1u64) } else { v };
    let y = (z - w) * (z + w).inverse()?;
    let mut encoded: [u8; 32] = y.into_bigint().to_bytes_le().try_into().ok()?;
    encoded[31] |= u8::from(negative) << 7;
    EdwardsPrime::decode_cofactor(&encoded)
}

#[cfg(test)]
mod tests {
    use super::*;
    use curve25519_dalek::constants::EIGHT_TORSION;

    fn bytes(s: &str) -> [u8; 32] {
        std::array::from_fn(|i| u8::from_str_radix(&s[2 * i..2 * i + 2], 16).unwrap())
    }

    #[test]
    fn legacy_map_matches_pinned_monero() {
        // Monero 4f92268d, ge_fromfe_frombytes_vartime followed by ge_mul8.
        let vectors: Vec<(String, String)> =
            serde_json::from_str(include_str!("../../tests/fixtures/edwards-map.json")).unwrap();
        for (input, expected) in vectors {
            assert_eq!(
                map(bytes(&input)).unwrap().to_bytes(),
                bytes(&expected),
                "{input}"
            );
        }
    }

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
