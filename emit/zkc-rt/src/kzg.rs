//! The BLS12-381 KZG supplier set: the `fr_be32` and `bls_g1_be48`
//! codecs as concrete types, and the two opaque check predicates the
//! protocol vocabulary admits — single-point opening and same-point
//! batch opening — implemented exactly as their content-addressed
//! predicate specifications state them. The curve arithmetic is the
//! borrowed kernel (the arkworks BLS12-381 implementation, whose point
//! serialization is the standard compressed big-endian form the codec
//! names); this module owns only wire canonicality, the transcript
//! derivation for `fr` challenges, and the acceptance equations.
//!
//! `tau_g2` — τ·g2 from the pinned SRS — is setup material: it arrives
//! through the supplier binding, never from the artifact, and a binding
//! for deployment pins a ceremony point where a test binding pins a
//! known-τ one.

use ark_bls12_381::{Bls12_381, Fq12, Fr as ArkFr, G1Affine, G1Projective, G2Affine};
use ark_ec::pairing::Pairing;
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::{AdditiveGroup, BigInteger, Field, PrimeField, Zero};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};

/// The scalar field element carried by class `fr`.
pub type Fr = ArkFr;
/// The group element carried by class `g1`.
pub type G1 = G1Affine;
/// The setup-side group of `tau_g2`.
pub type G2 = G2Affine;

/// The `fr_be32` wire: 32 big-endian bytes, canonical-or-none.
pub fn fr_from_wire(bytes: &[u8]) -> Option<Fr> {
    if bytes.len() != 32 {
        return None;
    }
    let value = Fr::from_be_bytes_mod_order(bytes);
    // Canonical exactly when the reduction was the identity.
    if fr_to_wire(&value) == bytes {
        Some(value)
    } else {
        None
    }
}

/// The write direction of `fr_be32` (round-trip and canonicity are the
/// codec obligations; both hold by construction here).
pub fn fr_to_wire(value: &Fr) -> [u8; 32] {
    value
        .into_bigint()
        .to_bytes_be()
        .try_into()
        .expect("a BLS12-381 scalar is 32 bytes")
}

/// The `bls_g1_be48` wire: 48 bytes, standard compressed form —
/// canonical field element, on curve, in the prime-order subgroup, or
/// none.
pub fn g1_from_wire(bytes: &[u8]) -> Option<G1> {
    if bytes.len() != 48 {
        return None;
    }
    G1Affine::deserialize_compressed(bytes).ok()
}

/// The write direction of `bls_g1_be48`.
pub fn g1_to_wire(point: &G1) -> [u8; 48] {
    let mut bytes = [0u8; 48];
    point
        .serialize_compressed(&mut bytes[..])
        .expect("a compressed BLS12-381 G1 point is 48 bytes");
    bytes
}

/// A binding-pinned `tau_g2`: 96 compressed bytes as lowercase hex.
pub fn g2_from_hex(hex: &str) -> Option<G2> {
    if hex.len() != 192 {
        return None;
    }
    let mut bytes = [0u8; 96];
    for (index, slot) in bytes.iter_mut().enumerate() {
        let nibble = |c: u8| -> Option<u8> {
            match c {
                b'0'..=b'9' => Some(c - b'0'),
                b'a'..=b'f' => Some(c - b'a' + 10),
                _ => None,
            }
        };
        let at = index * 2;
        *slot = (nibble(hex.as_bytes()[at])? << 4) | nibble(hex.as_bytes()[at + 1])?;
    }
    G2Affine::deserialize_compressed(&bytes[..]).ok()
}

/// Challenge derivation for class `fr` over a 32-byte sponge digest:
/// the digest as a big-endian integer, reduced into the scalar field.
/// The declared sample space is exactly the field order, so the
/// reduction is the uniform rule the squeeze row states.
pub fn fr_from_digest(digest: &[u8; 32]) -> Fr {
    Fr::from_be_bytes_mod_order(digest)
}

/// The challenge-log spelling: the canonical decimal of the scalar.
pub fn fr_decimal(value: &Fr) -> String {
    value.into_bigint().to_string()
}

/// The single-point opening predicate
/// (`zkc.check.kzg-opening`): accept exactly when
/// `e(C - y*g1, g2) == e(W, tau_g2 - z*g2)`.
pub fn kzg_opening_accepts(
    tau_g2: &G2,
    commitment: &G1,
    point: &Fr,
    value: &Fr,
    proof: &G1,
) -> bool {
    let g1 = G1Affine::generator();
    let g2 = G2Affine::generator();
    let lhs = (commitment.into_group() - g1 * value).into_affine();
    let rhs = (tau_g2.into_group() - g2 * point).into_affine();
    Bls12_381::pairing(lhs, g2) == Bls12_381::pairing(*proof, rhs)
}

/// The same-point batch-opening predicate
/// (`zkc.check.kzg-batch-opening`): fold `C* = Σ γ^i C_i` and
/// `y* = Σ γ^i y_i` — positions paired by index, γ⁰ on the first —
/// then accept exactly when `e(C* - y**g1, g2) == e(W, tau_g2 - z*g2)`.
pub fn kzg_batch_opening_accepts(
    tau_g2: &G2,
    commitments: &[G1],
    point: &Fr,
    values: &[Fr],
    batch_challenge: &Fr,
    proof: &G1,
) -> bool {
    if commitments.len() != values.len() || commitments.len() < 2 {
        return false;
    }
    let mut weight = Fr::ONE;
    let mut folded_commitment = G1Projective::zero();
    let mut folded_value = Fr::ZERO;
    for (commitment, value) in commitments.iter().zip(values) {
        folded_commitment += commitment.into_group() * weight;
        folded_value += *value * weight;
        weight *= batch_challenge;
    }
    kzg_opening_accepts(
        tau_g2,
        &folded_commitment.into_affine(),
        point,
        &folded_value,
        proof,
    )
}

/// The pairing must be nondegenerate for either predicate to mean
/// anything. Emitted conformance suites call this before replaying a
/// vector, so a borrowed curve implementation that drifts is caught
/// where it would otherwise make every acceptance meaningless.
pub fn pairing_self_check() {
    let paired = Bls12_381::pairing(G1Affine::generator(), G2Affine::generator());
    assert_ne!(paired.0, Fq12::ONE, "degenerate pairing on the generators");
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ec::PrimeGroup;

    /// The standard compressed generators (the IETF/zcash test vectors):
    /// the codec name says big-endian standard form, and these bytes are
    /// that claim's anchor.
    #[test]
    fn generator_wire_forms_are_the_standard_ones() {
        let g1_hex = "97f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb";
        let wire = g1_to_wire(&G1Affine::generator());
        let hex: String = wire.iter().map(|byte| format!("{byte:02x}")).collect();
        assert_eq!(hex, g1_hex);
        assert_eq!(g1_from_wire(&wire), Some(G1Affine::generator()));

        let g2_hex = "93e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb8";
        assert_eq!(g2_from_hex(g2_hex), Some(G2Affine::generator()));
    }

    /// A known-τ opening: τ = 5, p(X) = X² + 3, z = 2. Then C = 28·g1,
    /// y = 7, and W = ((28 − 7)/(5 − 2))·g1 = 7·g1. The vector is built
    /// from scalar arithmetic alone; the predicate checks it with
    /// pairings — two independent routes to the same equation.
    #[test]
    fn known_tau_opening() {
        let g1 = G1Affine::generator();
        let g2 = ark_bls12_381::G2Projective::generator();
        let tau_g2 = (g2 * Fr::from(5u64)).into_affine();
        let commitment = (g1 * Fr::from(28u64)).into_affine();
        let proof = (g1 * Fr::from(7u64)).into_affine();
        assert!(kzg_opening_accepts(
            &tau_g2,
            &commitment,
            &Fr::from(2u64),
            &Fr::from(7u64),
            &proof
        ));
        // A shifted value dies at the equation, not before.
        assert!(!kzg_opening_accepts(
            &tau_g2,
            &commitment,
            &Fr::from(2u64),
            &Fr::from(8u64),
            &proof
        ));
    }

    /// The batch fold at the same point, γ-weighted in index order:
    /// p0 = X² + 3 and p1 = 2X at τ = 5, z = 2, γ = 3. The batch proof
    /// is W = ((p*(τ) − y*)/(τ − z))·g1 for p* = p0 + γ·p1.
    #[test]
    fn known_tau_batch_opening() {
        let g1 = G1Affine::generator();
        let g2 = ark_bls12_381::G2Projective::generator();
        let tau_g2 = (g2 * Fr::from(5u64)).into_affine();
        let commitments = [
            (g1 * Fr::from(28u64)).into_affine(), // p0(5)
            (g1 * Fr::from(10u64)).into_affine(), // p1(5)
        ];
        let values = [Fr::from(7u64), Fr::from(4u64)]; // p0(2), p1(2)
        let gamma = Fr::from(3u64);
        // p*(5) = 28 + 3·10 = 58, y* = 7 + 3·4 = 19, W = (58−19)/3 = 13.
        let proof = (g1 * Fr::from(13u64)).into_affine();
        assert!(kzg_batch_opening_accepts(
            &tau_g2,
            &commitments,
            &Fr::from(2u64),
            &values,
            &gamma,
            &proof
        ));
        // Swapping the pair order changes the fold; the equation refuses.
        let swapped = [commitments[1], commitments[0]];
        assert!(!kzg_batch_opening_accepts(
            &tau_g2,
            &swapped,
            &Fr::from(2u64),
            &values,
            &gamma,
            &proof
        ));
    }

    #[test]
    fn wire_canonicality_refuses() {
        // The field order itself is the smallest non-canonical scalar.
        let modulus_be: [u8; 32] = [
            0x73, 0xed, 0xa7, 0x53, 0x29, 0x9d, 0x7d, 0x48, 0x33, 0x39, 0xd8, 0x08, 0x09, 0xa1,
            0xd8, 0x05, 0x53, 0xbd, 0xa4, 0x02, 0xff, 0xfe, 0x5b, 0xfe, 0xff, 0xff, 0xff, 0xff,
            0x00, 0x00, 0x00, 0x01,
        ];
        assert_eq!(fr_from_wire(&modulus_be), None);
        // A 48-byte string that is no point refuses.
        assert_eq!(g1_from_wire(&[0xff; 48]), None);
        pairing_self_check();
    }
}
