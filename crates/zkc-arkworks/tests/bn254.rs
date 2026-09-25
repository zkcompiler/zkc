//! Independent arkworks comparisons and canonical subgroup rejection controls.
use ark_bn254::{Bn254, Fq, Fq2, Fr, G1Affine, G1Projective, G2Affine, G2Projective};
use ark_ec::{AffineRepr, CurveGroup, pairing::Pairing};
use ark_ff::{One, PrimeField, Zero};
use ark_serialize::CanonicalSerialize;
use zkc_arkworks::bn254::{self, G1, G2};
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
        raw1[j].serialize_compressed(&mut buf).unwrap();
        assert_eq!(a[j].to_bytes().unwrap().as_slice(), buf);
        assert_eq!(G1::from_bytes(&buf).unwrap(), a[j]);
        buf.clear();
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
    assert_eq!(G1::msm(&s, &a).unwrap(), G1::from_affine(sum1).unwrap());
    assert_eq!(G2::msm(&s, &b).unwrap(), G2::from_affine(sum2).unwrap());
    assert_eq!(
        bn254::pairing_check(&a, &b).unwrap(),
        Bn254::multi_pairing(raw1, raw2).is_zero()
    );
    assert!(bn254::pairing_check(&[a[0], a[0].neg()], &[b[1], b[1]]).unwrap());
    assert!(!bn254::pairing_check(&[a[0]], &[b[1]]).unwrap());
    assert!(bn254::pairing_check(&[], &[]).unwrap());
    assert!(bn254::pairing_check(&a, &[]).is_err());
    assert!(G1::msm(&s, &[]).is_err());
    assert!(G2::msm(&s, &[]).is_err());
    assert_eq!(G1::identity().add(&a[0]), a[0]);
    assert_eq!(G2::identity().add(&b[0]), b[0]);
    assert_eq!(a[0].add(&a[0].neg()), G1::identity());
    assert_eq!(b[0].add(&b[0].neg()), G2::identity());
}
#[test]
fn canonical_scalar_curve_subgroup_and_infinity_refusals() {
    for s in ["", "00", "01", "-1", "1.0", bn254::MODULUS] {
        assert!(bn254::parse_decimal(s).is_err());
    }
    let max = -Fr::one();
    assert_eq!(
        bn254::decode_scalar(&bn254::encode_scalar(&max).unwrap()).unwrap(),
        max
    );
    let mut modulus = Vec::new();
    Fr::MODULUS.serialize_compressed(&mut modulus).unwrap();
    assert!(bn254::decode_scalar(&modulus).is_err());
    for n in [0, 31, 33, 64, 65] {
        if n != 32 {
            assert!(G1::from_bytes(&vec![0; n]).is_err());
        }
        if n != 64 {
            assert!(G2::from_bytes(&vec![0; n]).is_err());
        }
    }
    let mut bad = G1::identity().to_bytes().unwrap();
    bad[0] = 1;
    assert!(G1::from_bytes(&bad).is_err());
    let mut bad = G2::identity().to_bytes().unwrap();
    bad[0] = 1;
    assert!(G2::from_bytes(&bad).is_err());
    assert!(G1::from_affine(G1Affine::new_unchecked(Fq::one(), Fq::one())).is_err());
    let wrong = (0u64..100)
        .find_map(|n| {
            G2Affine::get_point_from_x_unchecked(Fq2::new(Fq::from(n), Fq::one()), false)
                .filter(|p| !p.is_in_correct_subgroup_assuming_on_curve())
        })
        .unwrap();
    assert!(wrong.is_on_curve());
    assert!(G2::from_affine(wrong).is_err());
    let mut bytes = Vec::new();
    wrong.serialize_compressed(&mut bytes).unwrap();
    assert!(G2::from_bytes(&bytes).is_err());
}
