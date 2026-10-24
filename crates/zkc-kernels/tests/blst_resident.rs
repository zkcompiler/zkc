//! Resident mathematical chains checked against independent Arkworks arithmetic.
use ark_ff::{BigInteger, Field, PrimeField};
use sha2::{Digest, Sha256};
use zkc_kernels::{
    arkworks::bls12_381 as ark,
    blst::bls12_381::{self as resident, Error, G1, G1Vector, G2, G2Vector, Scalar, ScalarVector},
    field::{Coefficient, Error as FieldError},
    numerical::{Call, Limits},
    vector,
};

fn scalar(index: usize) -> ark::Scalar {
    ark::Scalar::from_le_bytes_mod_order(&Sha256::digest(index.to_le_bytes()))
}
fn import(value: ark::Scalar) -> Scalar {
    resident::arkworks::import_scalar(value).unwrap()
}
fn export(value: Scalar) -> ark::Scalar {
    resident::arkworks::export_scalar(value).unwrap()
}
fn exported(values: &ScalarVector) -> Vec<ark::Scalar> {
    values.iter().map(export).collect()
}

#[test]
fn full_field_arithmetic_matches_arkworks_at_boundaries_and_large_residues() {
    let values: Vec<_> = (0..64)
        .map(scalar)
        .chain([
            ark::Scalar::from(0),
            ark::Scalar::from(1),
            -ark::Scalar::from(1),
        ])
        .collect();
    assert_eq!(Scalar::default(), Scalar::ZERO);
    assert_eq!(Scalar::zero(), Scalar::ZERO);
    assert_eq!(Scalar::one(), Scalar::ONE);
    for (i, &a) in values.iter().enumerate() {
        let b = values[(i + 1) % values.len()];
        let (x, y) = (import(a), import(b));
        assert_eq!(export(x + y), a + b);
        assert_eq!(export(x - y), a - b);
        assert_eq!(export(x * y), a * b);
        assert_eq!(export(-x), -a);
        assert_eq!(x + -x, Scalar::ZERO);
        assert_eq!(x.inverse().map(export), a.inverse());
        if let Some(inverse) = x.inverse() {
            assert_eq!(x * inverse, Scalar::ONE);
        }
        for exponent in [0, 1, 2, 63, 64, u64::MAX] {
            assert_eq!(export(x.pow(exponent)), a.pow([exponent]));
        }
        let mut assignment = x;
        assignment += y;
        assignment -= y;
        assignment *= y;
        assert_eq!(assignment, x * y);
        let decimal = a.into_bigint().to_string();
        assert_eq!(resident::parse_decimal(&decimal).unwrap(), x);
    }
    assert_eq!(Scalar::ZERO.pow(0), Scalar::ONE);
    assert_eq!(Scalar::ZERO.inverse(), None);
    let modulus = ark::Scalar::MODULUS.to_string();
    let overlong = "9".repeat(4096);
    for invalid in [
        "", "00", "01", "+1", "-1", " 1", "1 ", "1\n", "１２", &modulus, &overlong,
    ] {
        assert_eq!(
            resident::parse_decimal(invalid),
            Err(FieldError::NoncanonicalScalar)
        );
    }
    assert_eq!(import(-ark::Scalar::from(1)) + Scalar::ONE, Scalar::ZERO);
}

#[test]
fn scalar_slices_and_resident_buffers_share_vector_algebra() {
    for n in [0, 1, 2, 7, 32, 65] {
        let a: Vec<_> = (0..n).map(scalar).collect();
        let b: Vec<_> = (n..2 * n).map(scalar).collect();
        let wrappers: Vec<_> = a.iter().copied().map(import).collect();
        let left = ScalarVector::from_slice(&wrappers).unwrap();
        let right = ScalarVector::try_from_fn(n, |i| Ok(import(b[i]))).unwrap();
        let mut output = ScalarVector::filled(n, Scalar::ZERO).unwrap();
        let mut slice_output = vec![Scalar::ZERO; n];
        let plan = vector::Plan::<Scalar>::select(n).unwrap();
        assert_eq!(plan.algorithm(), vector::Algorithm::Scalar);
        assert_eq!(plan.output_bytes(), n * size_of::<Scalar>());
        assert_eq!(plan.workspace_bytes(), 0);
        for (operation, expected) in [
            (
                ScalarVector::add_into as fn(&ScalarVector, &ScalarVector, &mut ScalarVector) -> _,
                a.iter().zip(&b).map(|(a, b)| *a + *b).collect::<Vec<_>>(),
            ),
            (
                ScalarVector::sub_into,
                a.iter().zip(&b).map(|(a, b)| *a - *b).collect(),
            ),
            (
                ScalarVector::mul_into,
                a.iter().zip(&b).map(|(a, b)| *a * *b).collect(),
            ),
        ] {
            operation(&left, &right, &mut output).unwrap();
            assert_eq!(exported(&output), expected);
        }
        left.neg_into(&mut output).unwrap();
        assert_eq!(exported(&output), a.iter().map(|a| -*a).collect::<Vec<_>>());
        left.scale_into(import(scalar(99)), &mut output).unwrap();
        plan.scale(&wrappers, import(scalar(99)), &mut slice_output)
            .unwrap();
        assert_eq!(output.iter().collect::<Vec<_>>(), slice_output);
        assert_eq!(
            export(left.dot(&right).unwrap()),
            a.iter().zip(&b).map(|(a, b)| *a * *b).sum()
        );
        assert_eq!(export(left.sum()), a.iter().copied().sum());
        assert_eq!(export(left.product()), a.iter().copied().product());
        left.inverse_into(&mut output).unwrap();
        assert_eq!(
            exported(&output),
            a.iter().map(|a| a.inverse().unwrap()).collect::<Vec<_>>()
        );
        assert_eq!(
            export(left.evaluate(import(scalar(97)))),
            zkc_kernels::polynomial::evaluate(&a, scalar(97))
        );
        assert_eq!(left.get(n), None);
        assert_eq!(
            left.iter().rev().collect::<Vec<_>>(),
            wrappers.iter().rev().copied().collect::<Vec<_>>()
        );
        assert!(left.storage_bytes() >= n * size_of::<Scalar>());
    }
}

#[test]
fn scalar_shape_and_zero_inverse_refusals_preserve_destinations() {
    let a = ScalarVector::from_slice(&[Scalar::from(3), Scalar::from(4)]).unwrap();
    let short = ScalarVector::filled(1, Scalar::ONE).unwrap();
    let mut out = ScalarVector::filled(2, Scalar::from(99)).unwrap();
    for operation in [
        ScalarVector::add_into,
        ScalarVector::sub_into,
        ScalarVector::mul_into,
    ] {
        assert_eq!(
            operation(&a, &short, &mut out),
            Err(FieldError::LengthMismatch)
        );
        assert_eq!(
            operation(&short, &a, &mut out),
            Err(FieldError::LengthMismatch)
        );
        assert_eq!(
            operation(&short, &short, &mut out),
            Err(FieldError::LengthMismatch)
        );
        assert_eq!(out.iter().collect::<Vec<_>>(), vec![Scalar::from(99); 2]);
    }
    assert_eq!(a.dot(&short), Err(FieldError::LengthMismatch));
    assert_eq!(short.neg_into(&mut out), Err(FieldError::LengthMismatch));
    assert_eq!(
        short.scale_into(Scalar::ONE, &mut out),
        Err(FieldError::LengthMismatch)
    );
    assert_eq!(
        short.inverse_into(&mut out),
        Err(FieldError::LengthMismatch)
    );
    for zero_position in 0..2 {
        let mut invalid = ScalarVector::from_slice(&[Scalar::ONE; 2]).unwrap();
        invalid.set(zero_position, Scalar::ZERO);
        assert_eq!(invalid.inverse_into(&mut out), Err(FieldError::ZeroInverse));
        assert_eq!(out.iter().collect::<Vec<_>>(), vec![Scalar::from(99); 2]);
    }
}

macro_rules! resident_group {
    ($test:ident, $point:ident, $bulk:ident, $import:ident, $export:ident) => {
        #[test]
        fn $test() {
            for n in [0, 1, 2, 3, 31, 32, 33, 65] {
                let factors: Vec<_> = (0..n)
                    .map(|i| {
                        if i % 7 == 0 {
                            ark::Scalar::from(0)
                        } else {
                            scalar(i)
                        }
                    })
                    .collect();
                let points: Vec<_> = (0..n)
                    .map(|i| {
                        if i % 11 == 0 {
                            ark::$point::identity()
                        } else {
                            ark::$point::generator().scale(scalar(i + n))
                        }
                    })
                    .collect();
                let scalars = ScalarVector::try_from_fn(n, |i| Ok(import(factors[i]))).unwrap();
                let resident =
                    $bulk::try_from_fn(n, |i| resident::arkworks::$import(points[i])).unwrap();
                let mut scaled = $bulk::filled(n, $point::identity()).unwrap();
                resident.scale_each_into(&scalars, &mut scaled).unwrap();
                let expected: Vec<_> = points
                    .iter()
                    .zip(&factors)
                    .map(|(p, s)| p.scale(*s))
                    .collect();
                for (actual, expected) in scaled.iter().zip(&expected) {
                    assert_eq!(resident::arkworks::$export(actual).unwrap(), *expected);
                }
                let sum = expected
                    .iter()
                    .fold(ark::$point::identity(), |a, b| a.add(b));
                assert_eq!(resident::arkworks::$export(scaled.sum()).unwrap(), sum);
                for _ in 0..2 {
                    let msm = resident.msm(&scalars).unwrap();
                    assert_eq!(resident::arkworks::$export(msm).unwrap(), sum);
                }
                resident
                    .scale_into(import(scalar(91)), &mut scaled)
                    .unwrap();
                for (actual, expected) in scaled.iter().zip(&points) {
                    assert_eq!(
                        resident::arkworks::$export(actual).unwrap(),
                        expected.scale(scalar(91))
                    );
                }
                let mut negated = $bulk::filled(n, $point::identity()).unwrap();
                resident.neg_into(&mut negated).unwrap();
                resident.add_into(&negated, &mut scaled).unwrap();
                assert!(scaled.iter().all(|p| p.equal(&$point::identity())));
                assert!(resident.storage_bytes() >= n * size_of::<$point>());
            }
            let generator = $point::generator();
            assert!(
                generator
                    .add(&generator)
                    .equal(&generator.scale(Scalar::from(2)))
            );
            assert!(!generator.equal(&generator.neg()));
            assert!(generator.scale(Scalar::ZERO).equal(&$point::identity()));
            let empty = $bulk::default();
            let one = $bulk::filled(1, generator).unwrap();
            let empty_scalars = ScalarVector::default();
            let scalars = ScalarVector::filled(1, Scalar::ONE).unwrap();
            assert_eq!(empty.msm(&scalars), Err(Error::LengthMismatch));
            assert_eq!(one.msm(&empty_scalars), Err(Error::LengthMismatch));
            let mut out = $bulk::filled(1, generator).unwrap();
            assert_eq!(
                empty.scale_into(Scalar::ONE, &mut out),
                Err(Error::LengthMismatch)
            );
            assert_eq!(empty.neg_into(&mut out), Err(Error::LengthMismatch));
            assert_eq!(one.add_into(&empty, &mut out), Err(Error::LengthMismatch));
            assert_eq!(empty.add_into(&one, &mut out), Err(Error::LengthMismatch));
            assert_eq!(empty.add_into(&empty, &mut out), Err(Error::LengthMismatch));
            assert_eq!(
                one.scale_each_into(&empty_scalars, &mut out),
                Err(Error::LengthMismatch)
            );
            assert_eq!(
                empty.scale_each_into(&scalars, &mut out),
                Err(Error::LengthMismatch)
            );
            assert_eq!(
                empty.scale_each_into(&empty_scalars, &mut out),
                Err(Error::LengthMismatch)
            );
            assert_eq!(out.get(0), Some(generator));
            out.set(0, $point::identity());
            assert_eq!(out.get(0), Some($point::identity()));
        }
    };
}
resident_group!(
    g1_resident_chain_agrees_with_arkworks,
    G1,
    G1Vector,
    import_g1,
    export_g1
);
resident_group!(
    g2_resident_chain_agrees_with_arkworks,
    G2,
    G2Vector,
    import_g2,
    export_g2
);

#[test]
fn bulk_codecs_are_exact_and_refuse_every_invalid_position() {
    let scalars = ScalarVector::try_from_fn(4, |i| Ok(import(scalar(i)))).unwrap();
    let mut bytes = vec![0; 4 * Scalar::BYTES];
    scalars.write_bytes(&mut bytes).unwrap();
    assert_eq!(ScalarVector::from_bytes(&bytes).unwrap(), scalars);
    assert!(ScalarVector::from_bytes(&[]).unwrap().is_empty());
    for index in 0..4 {
        let mut invalid = bytes.clone();
        invalid[index * 32..(index + 1) * 32].copy_from_slice(&ark::Scalar::MODULUS.to_bytes_le());
        assert_eq!(
            ScalarVector::from_bytes(&invalid),
            Err(Error::InvalidEncoding)
        );
    }
    assert_eq!(
        ScalarVector::from_bytes(&bytes[..bytes.len() - 1]),
        Err(Error::InvalidEncoding)
    );
    let mut wrong = [99; 33];
    assert_eq!(scalars.write_bytes(&mut wrong), Err(Error::LengthMismatch));
    assert_eq!(wrong, [99; 33]);

    macro_rules! point_codec {
        ($point:ident, $bulk:ident) => {{
            let points = $bulk::from_slice(&[
                $point::identity(),
                $point::generator(),
                $point::generator().neg(),
            ])
            .unwrap();
            let mut bytes = vec![0; 3 * $point::BYTES];
            points.write_bytes(&mut bytes).unwrap();
            assert_eq!($bulk::from_bytes(&bytes).unwrap(), points);
            assert!($bulk::from_bytes(&[]).unwrap().is_empty());
            for index in 0..3 {
                let mut invalid = bytes.clone();
                invalid[index * $point::BYTES..(index + 1) * $point::BYTES].fill(255);
                assert_eq!($bulk::from_bytes(&invalid), Err(Error::InvalidEncoding));
            }
            assert_eq!(
                $bulk::from_bytes(&bytes[..bytes.len() - 1]),
                Err(Error::InvalidEncoding)
            );
            let mut wrong = [99; 1];
            assert_eq!(points.write_bytes(&mut wrong), Err(Error::LengthMismatch));
            assert_eq!(wrong, [99; 1]);
        }};
    }
    point_codec!(G1, G1Vector);
    point_codec!(G2, G2Vector);
}

#[test]
fn bulk_decoding_rejects_non_subgroups_and_noncanonical_identity_at_every_position() {
    use ark_bls12_381::{Fq, Fq2, G2Affine};
    use ark_serialize::CanonicalSerialize;

    // (0, 2) is a curve point of order three, outside G1's prime subgroup.
    let mut wrong_g1 = [0; G1::BYTES];
    wrong_g1[0] = 0x80;
    let wrong_g2 = (0u64..100)
        .find_map(|n| {
            G2Affine::get_point_from_x_unchecked(Fq2::new(Fq::from(n), Fq::from(1)), false)
                .filter(|p| !p.is_in_correct_subgroup_assuming_on_curve())
        })
        .unwrap();
    assert!(wrong_g2.is_on_curve());
    let mut wrong_g2_bytes = Vec::new();
    wrong_g2.serialize_compressed(&mut wrong_g2_bytes).unwrap();
    macro_rules! reject {
        ($point:ident, $bulk:ident, $non_subgroup:expr) => {{
            for position in 0..3 {
                let mut invalid = $point::generator().to_bytes().repeat(3);
                let target = &mut invalid[position * $point::BYTES..(position + 1) * $point::BYTES];
                target.copy_from_slice($non_subgroup);
                assert_eq!($bulk::from_bytes(&invalid), Err(Error::InvalidEncoding));
                let mut infinity = $point::identity().to_bytes();
                infinity[0] |= 0x20;
                invalid[position * $point::BYTES..(position + 1) * $point::BYTES]
                    .copy_from_slice(&infinity);
                assert_eq!($bulk::from_bytes(&invalid), Err(Error::InvalidEncoding));
                infinity[0] &= !0x20;
                infinity[$point::BYTES - 1] = 1;
                invalid[position * $point::BYTES..(position + 1) * $point::BYTES]
                    .copy_from_slice(&infinity);
                assert_eq!($bulk::from_bytes(&invalid), Err(Error::InvalidEncoding));
            }
        }};
    }
    reject!(G1, G1Vector, &wrong_g1);
    reject!(G2, G2Vector, &wrong_g2_bytes);
}

#[test]
fn resident_pairing_matches_arkworks_for_batches_and_unit_factors() {
    for n in [0, 1, 7, 8, 9, 17] {
        let p = ark::G1::generator().scale(scalar(n));
        let q = ark::G2::generator().scale(scalar(n + 1));
        let mut left = vec![p; n];
        let mut right = vec![q; n];
        left.extend(vec![p.neg(); n]);
        right.extend(vec![q; n]);
        left.extend([ark::G1::identity(), p]);
        right.extend([q, ark::G2::identity()]);
        for extra in 0..2 {
            if extra == 1 {
                left.push(p);
                right.push(q);
            }
            let a = G1Vector::try_from_fn(left.len(), |i| resident::arkworks::import_g1(left[i]))
                .unwrap();
            let b = G2Vector::try_from_fn(right.len(), |i| resident::arkworks::import_g2(right[i]))
                .unwrap();
            assert_eq!(
                resident::pairing_check_bulk(&a, &b).unwrap(),
                ark::pairing_check(&left, &right).unwrap()
            );
        }
    }
    assert!(resident::pairing_check_bulk(&G1Vector::default(), &G2Vector::default()).unwrap());
    let units = G1Vector::filled(9, G1::identity()).unwrap();
    let right = G2Vector::filled(9, G2::generator()).unwrap();
    assert!(resident::pairing_check_bulk(&units, &right).unwrap());
    assert_eq!(
        resident::pairing_check_bulk(&G1Vector::default(), &right),
        Err(Error::LengthMismatch)
    );
    assert_eq!(
        resident::pairing_check_bulk(&units, &G2Vector::default()),
        Err(Error::LengthMismatch)
    );
}

#[test]
fn resident_result_outlives_numerical_call_and_preserves_overlap_charges() {
    let values = {
        let call = Call::new(Limits {
            work: 100,
            memory: 4096,
            outputs: 1024,
        });
        let output = call
            .output(3, Scalar::ZERO, 3 * size_of::<Scalar>())
            .unwrap();
        assert_eq!(call.usage().memory, 6 * size_of::<Scalar>());
        let values = output
            .finish(|values| ScalarVector::from_slice(&values))
            .unwrap();
        assert_eq!(call.usage().memory, 3 * size_of::<Scalar>());
        assert_eq!(call.usage().outputs, 3 * size_of::<Scalar>());
        values
    };
    assert_eq!(values.sum(), Scalar::ZERO);
    assert_eq!(values.len(), 3);
}

#[test]
fn trusted_elements_share_existing_plans_and_transfer_buffers_without_copies() {
    let values: Vec<resident::ScalarElement> =
        (0..8).map(|i| import(scalar(i)).into_element()).collect();
    let address = values.as_ptr();
    let capacity = values.capacity();
    let carrier = ScalarVector::from_elements(values);
    assert_eq!(carrier.as_elements().as_ptr(), address);
    assert_eq!(
        carrier.storage_bytes(),
        capacity * size_of::<resident::ScalarElement>()
    );
    let mut result = vec![Scalar::ZERO.into_element(); carrier.len()];
    vector::mul(carrier.as_elements(), carrier.as_elements(), &mut result).unwrap();
    let result = ScalarVector::from_elements(result);
    for (index, element) in result.as_elements().iter().copied().enumerate() {
        assert_eq!(
            export(Scalar::from_element(element)),
            scalar(index).square()
        );
    }
    let values = carrier.into_elements();
    assert_eq!(values.as_ptr(), address);

    macro_rules! point_elements {
        ($point:ident, $bulk:ident, $element:ident) => {{
            let values: Vec<resident::$element> = [1u64, 2, 3]
                .into_iter()
                .map(|s| $point::generator().scale(Scalar::from(s)).into_element())
                .collect();
            let address = values.as_ptr();
            let carrier = $bulk::from_elements(values);
            assert_eq!(carrier.as_elements().as_ptr(), address);
            for (i, element) in carrier.as_elements().iter().copied().enumerate() {
                assert_eq!(
                    $point::from_element(element),
                    $point::generator().scale(Scalar::from((i + 1) as u64))
                );
            }
            let values = carrier.into_elements();
            assert_eq!(values.as_ptr(), address);
        }};
    }
    point_elements!(G1, G1Vector, G1Element);
    point_elements!(G2, G2Vector, G2Element);
}
