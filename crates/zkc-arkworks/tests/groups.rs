//! Differential and independently computed public group/sampler controls.
use ark_bls12_381::{Fr, G1Affine};
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::PrimeField;
use ark_serialize::CanonicalSerialize;
use zkc_arkworks::{GroupPoint, Scalar, encode_scalar, scalar_from_wide_be};
fn direct(p: G1Affine) -> Vec<u8> {
    let mut b = Vec::new();
    p.serialize_compressed(&mut b).unwrap();
    b
}
#[test]
fn independent_generator_and_direct_full_width_arithmetic() {
    let g = GroupPoint::generator();
    assert_eq!(
        g.to_bytes().unwrap().to_vec(),
        zkc_test_support::unhex(
            "97f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb"
        )
    );
    for scalar in [
        Scalar::from(0),
        Scalar::from(1),
        Scalar::from(7),
        Fr::from_be_bytes_mod_order(&[0xab; 64]),
    ] {
        let expected = G1Affine::generator()
            .mul_bigint(scalar.into_bigint())
            .into_affine();
        assert_eq!(
            g.scale(scalar).to_bytes().unwrap().to_vec(),
            direct(expected)
        );
        assert_eq!(g.add(&g.scale(scalar)), g.scale(scalar + Scalar::from(1)));
        assert_eq!(
            GroupPoint::from_bytes(&g.scale(scalar).to_bytes().unwrap()).unwrap(),
            g.scale(scalar)
        );
    }
    assert_eq!(g.scale(Scalar::from(0)), GroupPoint::identity());
    assert_eq!(g.add(&GroupPoint::identity()), g);
}
#[test]
fn research_point_fixtures_and_exact_hostile_decode() {
    // Frozen prior probe: x=0 is on-curve but outside the prime subgroup.
    let mut subgroup = vec![0; 48];
    subgroup[0] = 0x80;
    assert!(GroupPoint::from_bytes(&subgroup).is_err());
    let mut infinity = vec![0; 48];
    infinity[0] = 0xc0;
    assert_eq!(
        GroupPoint::from_bytes(&infinity).unwrap(),
        GroupPoint::identity()
    );
    infinity[47] = 1;
    assert!(GroupPoint::from_bytes(&infinity).is_err());
    let b = GroupPoint::generator().to_bytes().unwrap();
    for n in 0..48 {
        assert!(GroupPoint::from_bytes(&b[..n]).is_err());
    }
    let mut trailing = b.to_vec();
    trailing.push(0);
    assert!(GroupPoint::from_bytes(&trailing).is_err());
    assert!(GroupPoint::from_bytes(&[255; 48]).is_err());
}
#[test]
fn wide_big_endian_sampler_independent_integer_answers() {
    let mut one = [0; 64];
    one[63] = 1;
    assert_eq!(scalar_from_wide_be(&one), Scalar::from(1));
    assert_eq!(scalar_from_wide_be(&[0; 64]), Scalar::from(0));
    // Python integer pow/remainder, encoded little endian; not upstream output.
    let expected =
        zkc_test_support::unhex("6c9cf2f390e999c9235c9287cbed6c2b8f3954729614d30511ff599fd9d94807");
    assert_eq!(
        encode_scalar(&scalar_from_wide_be(&[255; 64]))
            .unwrap()
            .to_vec(),
        expected
    );
    let raw = zkc_test_support::unhex(
        "aa884a4de992779087a312c3af4e12cdb18f6bdc112444af048cb6e93ff2110d98c19e3655f26af8c849507850a502b24882a1a40bb9f60ba102493d6cf32969",
    );
    assert_eq!(
        encode_scalar(&scalar_from_wide_be(&raw.try_into().unwrap()))
            .unwrap()
            .to_vec(),
        zkc_test_support::unhex("a91c84a2d85f53b15d557b2ac4ca4795f14fc12edbd4c50ba1f11d2c1b98984a")
    );
}
