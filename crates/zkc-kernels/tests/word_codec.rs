use p3_field::{PrimeCharacteristicRing, PrimeField64};
use zkc_kernels::{
    field::Error,
    plonky3::{
        BabyBear, BabyBearExt4, Goldilocks, GoldilocksExt2, KoalaBear, KoalaBearExt4,
        KoalaBearExt8,
        residue::{self, PrimeWord, Residue},
        words::{self, Form},
    },
};

fn verify_inverse<B: PrimeWord>() {
    let inverse = B::MONTGOMERY_INVERSE.expect("registered Montgomery32 base");
    let modulus = u128::from(B::ORDER_U64);
    let factor = (1u128 << 32) % modulus;
    // This integer product verifies the constant without using field inversion.
    assert!(u128::from(inverse.as_canonical_u64()) < modulus);
    assert_eq!(
        (factor * u128::from(inverse.as_canonical_u64())) % modulus,
        1
    );
    assert_eq!(B::from_u64(1 << 32) * inverse, B::ONE);
    assert_eq!(B::from_u64(1 << 32).inverse(), inverse);
}

#[test]
fn registered_montgomery_inverses_are_exact() {
    verify_inverse::<KoalaBear>();
    verify_inverse::<BabyBear>();
    assert_eq!(
        KoalaBear::MONTGOMERY_INVERSE,
        Some(words::MONTGOMERY_INVERSE)
    );
    assert_eq!(Goldilocks::MONTGOMERY_INVERSE, None);
}

fn check_coordinates<E: Residue>() {
    let modulus = u128::from(E::Base::ORDER_U64);
    let coordinate_width = E::Base::WORD_BYTES;
    let width = words::width::<E>();
    let supported = E::Base::MONTGOMERY_INVERSE.is_some();
    let mut seed = 1_234_567u64;
    let mut concatenated = Vec::new();
    for sample in 0..128 {
        let coordinates: Vec<_> = (0..E::DIMENSION)
            .map(|i| {
                seed = seed
                    .wrapping_mul(6_364_136_223_846_793_005)
                    .wrapping_add(1_442_695_040_888_963_407);
                match (sample + i) % 11 {
                    0 => 0,
                    1 => 1,
                    2 => E::Base::ORDER_U64 - 1,
                    3 => E::Base::ORDER_U64 / 2,
                    4 => (1 << 32) % E::Base::ORDER_U64,
                    5 => ((1 << 53) + 1) % E::Base::ORDER_U64,
                    6 => (1 << 63) % E::Base::ORDER_U64,
                    _ => seed % E::Base::ORDER_U64,
                }
            })
            .collect();
        let value = E::from_basis_coefficients_fn(|i| E::Base::from_u64(coordinates[i]));
        for form in [Form::Canonical, Form::Montgomery] {
            let mut expected = Vec::new();
            for coordinate in &coordinates {
                let word = match form {
                    Form::Canonical => *coordinate,
                    Form::Montgomery => ((u128::from(*coordinate) << 32) % modulus) as u64,
                };
                expected.extend_from_slice(&word.to_le_bytes()[..coordinate_width]);
            }
            assert!(words::valid_elements::<E>(&expected));
            if form == Form::Montgomery && !supported {
                assert_eq!(words::decode::<E>(&expected, form), None);
            } else {
                // Check against independently encoded integers in ascending basis order.
                assert_eq!(words::decode::<E>(&expected, form), Some(value));
                let mut encoded = vec![0xab];
                words::encode_into(&value, form, &mut encoded);
                assert_eq!(&encoded[1..], expected);
                assert_eq!(encoded[0], 0xab);
            }
            if form == Form::Canonical {
                assert_eq!(residue::decode::<E>(&expected), Ok(value));
                concatenated.extend_from_slice(&expected);
            }
        }
    }
    assert!(words::valid_elements::<E>(&concatenated));
    assert!(words::valid_elements::<E>(&[]));
    assert!(!words::valid_elements::<E>(
        &concatenated[..concatenated.len() - 1]
    ));

    let valid = vec![0; width];
    // Rejection at every coordinate prevents an extension from hiding a bad word.
    for coordinate in 0..E::DIMENSION {
        for word in [E::Base::ORDER_U64, E::Base::ORDER_U64 + 1, u64::MAX] {
            let mut invalid = valid.clone();
            invalid[coordinate * coordinate_width..(coordinate + 1) * coordinate_width]
                .copy_from_slice(&word.to_le_bytes()[..coordinate_width]);
            assert_eq!(
                residue::decode::<E>(&invalid),
                Err(Error::NoncanonicalScalar)
            );
            assert!(!words::valid_elements::<E>(&invalid));
            for form in [Form::Canonical, Form::Montgomery] {
                assert_eq!(words::decode::<E>(&invalid, form), None);
            }
        }
    }
    for length in (0..width).chain([width + 1, width * 2]) {
        let invalid = vec![0; length];
        assert_eq!(residue::decode::<E>(&invalid), Err(Error::WireLength));
        for form in [Form::Canonical, Form::Montgomery] {
            assert_eq!(words::decode::<E>(&invalid, form), None);
        }
    }
}

macro_rules! coordinate_test {
    ($name:ident, $field:ty) => {
        #[test]
        fn $name() {
            check_coordinates::<$field>();
        }
    };
}
coordinate_test!(koala_bear_coordinate_words, KoalaBear);
coordinate_test!(koala_bear_quartic_coordinate_words, KoalaBearExt4);
coordinate_test!(koala_bear_octic_coordinate_words, KoalaBearExt8);
coordinate_test!(baby_bear_coordinate_words, BabyBear);
coordinate_test!(baby_bear_quartic_coordinate_words, BabyBearExt4);
coordinate_test!(goldilocks_coordinate_words, Goldilocks);
coordinate_test!(goldilocks_quadratic_coordinate_words, GoldilocksExt2);

fn unsupported_encoder<E: Residue>() {
    let mut out = vec![0xab];
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        words::encode_into(&E::ZERO, Form::Montgomery, &mut out);
    }));
    assert!(result.is_err());
    assert_eq!(out, [0xab]);
}

#[test]
fn unsupported_montgomery_encoders_still_panic_before_writing() {
    unsupported_encoder::<Goldilocks>();
    unsupported_encoder::<GoldilocksExt2>();
}
