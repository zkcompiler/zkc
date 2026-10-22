//! Independent arkworks comparisons, interoperable encodings and canonical
//! G2 subgroup rejection controls for the BLS12-381 pairing groups.
use ark_bls12_381::{Bls12_381, Fq, Fq2, Fr, G1Affine, G1Projective, G2Affine, G2Projective};
use ark_ec::{AffineRepr, CurveGroup, pairing::Pairing};
use ark_ff::{One, PrimeField, Zero};
use ark_serialize::CanonicalSerialize;
use zkc_kernels::arkworks::bls12_381::{self, G1, G2, Gt, pairing};

fn hex(text: &str) -> Vec<u8> {
    (0..text.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&text[i..i + 2], 16).unwrap())
        .collect()
}

// Entries of the Ethereum KZG ceremony output as distributed in
// c-kzg-4844 v2.1.8 `src/trusted_setup.txt` (SHA-256 d39b9f2d...26b7):
// the G2 monomial points [1] and [tau], and the G1 monomial point [tau].
const G2_ONE: &str = "93e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb8";
const G2_TAU: &str = "b5bfd7dd8cdeb128843bc287230af38926187075cbfbefa81009a2ce615ac53d2914e5870cb452d2afaaab24f3499f72185cbfee53492714734429b7b38608e23926c911cceceac9a36851477ba4c60b087041de621000edc98edada20c1def2";
const G1_ONE: &str = "97f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb";
const G1_TAU: &str = "ad3eb50121139aa34db1d545093ac9374ab7bca2c0f3bf28e27c8dcd8fc7cb42d25926fc0c97b336e9f0fb35e5a04c81";

#[test]
fn independent_library_group_arithmetic_and_pairing() {
    let s = [3u64, 7, 0, 19].map(Fr::from);
    let a = s.map(|x| G1::generator().scale(x));
    let b = s.map(|x| G2::generator().scale(x));
    let raw1 = s.map(|x| {
        G1Affine::generator()
            .mul_bigint(x.into_bigint())
            .into_affine()
    });
    let raw2 = s.map(|x| {
        G2Affine::generator()
            .mul_bigint(x.into_bigint())
            .into_affine()
    });
    for j in 0..s.len() {
        let mut buf = Vec::new();
        raw2[j].serialize_compressed(&mut buf).unwrap();
        assert_eq!(b[j].to_bytes().unwrap().as_slice(), buf);
        assert_eq!(G2::from_bytes(&buf).unwrap(), b[j]);
    }
    let sum1 = raw1
        .iter()
        .zip(s)
        .fold(G1Projective::zero(), |acc, (p, s)| {
            acc + p.mul_bigint(s.into_bigint())
        })
        .into_affine();
    let sum2 = raw2
        .iter()
        .zip(s)
        .fold(G2Projective::zero(), |acc, (p, s)| {
            acc + p.mul_bigint(s.into_bigint())
        })
        .into_affine();
    let mut buf = Vec::new();
    sum1.serialize_compressed(&mut buf).unwrap();
    assert_eq!(G1::msm(&s, &a).unwrap(), G1::from_bytes(&buf).unwrap());
    buf.clear();
    sum2.serialize_compressed(&mut buf).unwrap();
    assert_eq!(G2::msm(&s, &b).unwrap(), G2::from_bytes(&buf).unwrap());
    assert_eq!(
        bls12_381::pairing_check(&a, &b).unwrap(),
        Bls12_381::multi_pairing(raw1, raw2).is_zero()
    );
    assert!(bls12_381::pairing_check(&[a[0], a[0].neg()], &[b[1], b[1]]).unwrap());
    assert!(!bls12_381::pairing_check(&[a[0]], &[b[1]]).unwrap());
    assert!(bls12_381::pairing_check(&[], &[]).unwrap());
    assert!(bls12_381::pairing_check(&a, &[]).is_err());
    assert!(G2::msm(&s, &[]).is_err());
    assert_eq!(G2::identity().add(&b[0]), b[0]);
    assert_eq!(b[0].add(&b[0].neg()), G2::identity());
    assert_eq!(G2::generator().scale(Fr::zero()), G2::identity());
}

#[test]
fn ceremony_points_use_the_interoperable_compressed_encoding() {
    // The standard generators have the published compressed encodings.
    assert_eq!(G1::generator().to_bytes().unwrap().to_vec(), hex(G1_ONE));
    assert_eq!(G2::generator().to_bytes().unwrap().to_vec(), hex(G2_ONE));
    let tau1 = G1::from_bytes(&hex(G1_TAU)).unwrap();
    let tau2 = G2::from_bytes(&hex(G2_TAU)).unwrap();
    assert_eq!(tau2.to_bytes().unwrap().to_vec(), hex(G2_TAU));
    // Both powers commit to the same secret: e([tau]_1, [1]_2) = e([1]_1, [tau]_2).
    assert!(
        bls12_381::pairing_check(&[tau1, G1::generator().neg()], &[G2::generator(), tau2]).unwrap()
    );
    assert!(!bls12_381::pairing_check(&[tau1, G1::generator()], &[G2::generator(), tau2]).unwrap());
    assert_eq!(
        pairing(&tau1, &G2::generator()),
        pairing(&G1::generator(), &tau2)
    );
}

#[test]
fn canonical_curve_subgroup_flag_and_infinity_refusals() {
    for n in [0, 48, 95, 97, 192] {
        assert!(G2::from_bytes(&vec![0; n]).is_err());
    }
    let identity = G2::identity().to_bytes().unwrap();
    assert_eq!(identity[0], 0xc0);
    assert!(identity[1..].iter().all(|b| *b == 0));
    assert_eq!(G2::from_bytes(&identity).unwrap(), G2::identity());
    // The compression flag is required; infinity carries no sign and no
    // coordinate bits.
    for (byte, value) in [(0, 0x40), (0, 0xe0), (0, 0xc1), (95, 0xc1)] {
        let mut bad = identity;
        bad[byte] = value;
        if byte == 95 {
            bad[0] = 0xc0;
        }
        assert!(G2::from_bytes(&bad).is_err());
    }
    let mut uncompressed = hex(G2_ONE);
    uncompressed[0] &= 0x7f;
    assert!(G2::from_bytes(&uncompressed).is_err());
    // Flip the sign: the other root is a valid, different point.
    let mut negated = hex(G2_ONE);
    negated[0] ^= 0x20;
    assert_eq!(G2::from_bytes(&negated).unwrap(), G2::generator().neg());
    // An x coordinate component equal to the base-field modulus is not canonical.
    let mut modulus = Vec::new();
    Fq::MODULUS.serialize_compressed(&mut modulus).unwrap();
    modulus.reverse();
    let mut noncanonical = vec![0u8; 96];
    noncanonical[48..].copy_from_slice(&modulus);
    noncanonical[0] = 0x80;
    assert!(G2::from_bytes(&noncanonical).is_err());
    // A point on the curve outside the prime-order subgroup.
    let wrong = (0u64..100)
        .find_map(|n| {
            G2Affine::get_point_from_x_unchecked(Fq2::new(Fq::from(n), Fq::one()), false)
                .filter(|p| !p.is_in_correct_subgroup_assuming_on_curve())
        })
        .unwrap();
    assert!(wrong.is_on_curve());
    let mut bytes = Vec::new();
    wrong.serialize_compressed(&mut bytes).unwrap();
    assert!(G2::from_bytes(&bytes).is_err());
    // An x coordinate with no curve point.
    let off = (0u64..100)
        .find(|n| {
            G2Affine::get_point_from_x_unchecked(Fq2::new(Fq::from(*n), Fq::one()), false).is_none()
        })
        .unwrap();
    let mut x = Vec::new();
    Fq::from(off).serialize_compressed(&mut x).unwrap();
    x.reverse();
    let mut absent = vec![0u8; 96];
    absent[47] = 1;
    absent[48..].copy_from_slice(&x);
    absent[0] |= 0x80;
    assert!(G2::from_bytes(&absent).is_err());
}

#[test]
fn target_group_bilinearity_and_checked_canonical_representation() {
    use ark_bls12_381::Fq12;
    let a = Fr::from(7);
    let b = Fr::from(13);
    let target = pairing(&G1::generator().scale(a), &G2::generator().scale(b));
    assert_eq!(target, Gt::generator().scale(a * b));
    assert_eq!(target.add(&target.neg()), Gt::identity());
    assert_eq!(pairing(&G1::identity(), &G2::generator()), Gt::identity());
    let reference = Bls12_381::pairing(
        G1Affine::generator()
            .mul_bigint(a.into_bigint())
            .into_affine(),
        G2Affine::generator()
            .mul_bigint(b.into_bigint())
            .into_affine(),
    );
    let mut expected = Vec::new();
    reference.serialize_compressed(&mut expected).unwrap();
    let bytes = target.to_bytes().unwrap();
    assert_eq!(bytes.as_slice(), expected);
    assert_eq!(Gt::from_bytes(&bytes).unwrap(), target);
    let mut zero = Vec::new();
    Fq12::zero().serialize_compressed(&mut zero).unwrap();
    assert!(Gt::from_bytes(&zero).is_err());
    let mut outside = Vec::new();
    (Fq12::one() + Fq12::one())
        .serialize_compressed(&mut outside)
        .unwrap();
    assert!(Gt::from_bytes(&outside).is_err());
    assert!(Gt::from_bytes(&bytes[..575]).is_err());
}
