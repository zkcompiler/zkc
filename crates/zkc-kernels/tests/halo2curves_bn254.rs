//! Mathematical-byte and arithmetic differential controls against Arkworks.
//! These tests are bounded implementation evidence, not timing/security proofs.
use ark_bn254::{Bn254, Fq, Fq2, Fr, G1Affine, G2Affine};
use ark_ec::{AffineRepr, CurveGroup, pairing::Pairing};
use ark_ff::{BigInteger, Field, One, PrimeField, Zero};
use ark_serialize::CanonicalSerialize;
use zkc_kernels::{
    arkworks::bn254 as ark,
    halo2curves::bn254::{self as halo, Error, G1, G2, Scalar, ScalarVector},
};

fn bytes(value: &impl CanonicalSerialize) -> Vec<u8> {
    let mut bytes = Vec::new();
    value.serialize_compressed(&mut bytes).unwrap();
    bytes
}

fn scalars() -> Vec<Fr> {
    let mut values = vec![
        Fr::zero(),
        Fr::one(),
        -Fr::one(),
        -Fr::from(2),
        Fr::from(17),
    ];
    for bit in [63, 64, 127, 128, 191, 192, 253] {
        let mut encoding = [0; 32];
        encoding[bit / 8] = 1 << (bit % 8);
        let value = Fr::from_le_bytes_mod_order(&encoding);
        values.extend([value - Fr::one(), value, value + Fr::one()]);
    }
    values
}

fn scalar(value: Fr) -> Scalar {
    halo::decode_scalar(&bytes(&value)).unwrap()
}

#[test]
fn canonical_scalar_bytes_decimal_and_coefficient_arithmetic() {
    let samples = scalars();
    for a in &samples {
        let x = scalar(*a);
        assert_eq!(x.to_bytes_le().as_slice(), bytes(a));
        assert_eq!(halo::encode_scalar(&x), x.to_bytes_le());
        assert_eq!(halo::parse_decimal(&a.to_string()).unwrap(), x);
        assert_eq!(
            x.inverse().map(|s| s.to_bytes_le().to_vec()),
            a.inverse().map(|s| bytes(&s))
        );
        assert_eq!(x.pow(7).to_bytes_le().as_slice(), bytes(&a.pow([7])));
        for b in &samples {
            let y = scalar(*b);
            assert_eq!((x + y).to_bytes_le().as_slice(), bytes(&(*a + b)));
            assert_eq!((x - y).to_bytes_le().as_slice(), bytes(&(*a - b)));
            assert_eq!((x * y).to_bytes_le().as_slice(), bytes(&(*a * b)));
        }
        assert_eq!((-x).to_bytes_le().as_slice(), bytes(&-*a));
        assert_eq!(
            halo::arkworks::export_scalar(halo::arkworks::import_scalar(*a).unwrap()).unwrap(),
            *a
        );
    }
    assert_eq!(Scalar::ZERO.pow(0), Scalar::ONE);
    // Exercise the wrapper's Coefficient implementation through the shared
    // destination API as well as the upstream-ABI bulk implementation below.
    let wrapped: Vec<_> = samples.iter().copied().map(scalar).collect();
    let mut destination = vec![Scalar::ZERO; wrapped.len()];
    zkc_kernels::vector::mul(&wrapped, &wrapped, &mut destination).unwrap();
    for (actual, reference) in destination.iter().zip(&samples) {
        assert_eq!(actual.to_bytes_le().as_slice(), bytes(&reference.square()));
    }
    for text in [
        "",
        "00",
        "01",
        "-1",
        "+1",
        " 1",
        "1 ",
        "1.0",
        "１",
        halo::MODULUS,
    ] {
        assert!(halo::parse_decimal(text).is_err(), "{text:?}");
        assert!(ark::parse_decimal(text).is_err());
    }
    let modulus = Fr::MODULUS.to_bytes_le();
    for bad in [vec![], vec![0; 31], vec![0; 33], modulus, vec![255; 32]] {
        assert!(halo::decode_scalar(&bad).is_err());
        assert!(ark::decode_scalar(&bad).is_err());
    }
}

#[test]
fn scalar_bulk_arithmetic_matches_independent_field_values_and_preserves_refused_output() {
    let values = scalars();
    let a =
        ScalarVector::from_slice(&values.iter().copied().map(scalar).collect::<Vec<_>>()).unwrap();
    let b = ScalarVector::try_from_fn(a.len(), |i| Ok(Scalar::from(i as u64 + 1))).unwrap();
    let mut out = ScalarVector::filled(a.len(), Scalar::ONE).unwrap();
    a.add_into(&b, &mut out).unwrap();
    for (i, actual) in out.iter().enumerate() {
        assert_eq!(
            actual.to_bytes_le().as_slice(),
            bytes(&(values[i] + Fr::from(i as u64 + 1)))
        );
    }
    a.sub_into(&b, &mut out).unwrap();
    for (i, actual) in out.iter().enumerate() {
        assert_eq!(
            actual.to_bytes_le().as_slice(),
            bytes(&(values[i] - Fr::from(i as u64 + 1)))
        );
    }
    a.mul_into(&b, &mut out).unwrap();
    for (i, actual) in out.iter().enumerate() {
        assert_eq!(
            actual.to_bytes_le().as_slice(),
            bytes(&(values[i] * Fr::from(i as u64 + 1)))
        );
    }
    a.neg_into(&mut out).unwrap();
    assert_eq!(
        out.iter().collect::<Vec<_>>(),
        values.iter().map(|v| scalar(-*v)).collect::<Vec<_>>()
    );
    a.scale_into(Scalar::from(7), &mut out).unwrap();
    assert_eq!(
        out.iter().collect::<Vec<_>>(),
        values
            .iter()
            .map(|v| scalar(*v * Fr::from(7)))
            .collect::<Vec<_>>()
    );
    let saved = out.iter().collect::<Vec<_>>();
    assert!(a.inverse_into(&mut out).is_err()); // zero is refused before writes
    assert_eq!(out.iter().collect::<Vec<_>>(), saved);
    b.inverse_into(&mut out).unwrap();
    for (i, actual) in out.iter().enumerate() {
        assert_eq!(
            actual.to_bytes_le().as_slice(),
            bytes(&Fr::from(i as u64 + 1).inverse().unwrap())
        );
    }
    assert_eq!(a.sum(), scalar(values.iter().copied().sum()));
    assert_eq!(a.product(), scalar(values.iter().copied().product()));
    let dot: Fr = values
        .iter()
        .enumerate()
        .map(|(i, v)| *v * Fr::from(i as u64 + 1))
        .sum();
    assert_eq!(a.dot(&b).unwrap(), scalar(dot));
    let expected = values
        .iter()
        .rev()
        .fold(Fr::zero(), |a, b| a * Fr::from(9) + b);
    assert_eq!(a.evaluate(Scalar::from(9)), scalar(expected));
    let empty = ScalarVector::default();
    assert_eq!(empty.dot(&empty).unwrap(), Scalar::ZERO);
    assert_eq!(empty.sum(), Scalar::ZERO);
    assert_eq!(empty.product(), Scalar::ONE);
    let saved = out.iter().collect::<Vec<_>>();
    assert!(a.add_into(&empty, &mut out).is_err());
    assert!(a.dot(&empty).is_err());
    assert_eq!(out.iter().collect::<Vec<_>>(), saved);
    let mut encoded = vec![0; a.len() * Scalar::BYTES];
    a.write_bytes(&mut encoded).unwrap();
    assert_eq!(ScalarVector::from_bytes(&encoded).unwrap(), a);
    let mut short = vec![42; encoded.len() - 1];
    assert!(a.write_bytes(&mut short).is_err());
    assert!(short.iter().all(|v| *v == 42));
    assert!(ScalarVector::from_bytes(&short).is_err());
    let owned = a.into_elements();
    let address = owned.as_ptr();
    let restored = ScalarVector::from_elements(owned).unwrap();
    assert_eq!(restored.as_elements().as_ptr(), address);
    assert!(restored.storage_bytes() >= restored.len() * size_of::<halo::ScalarElement>());
}

macro_rules! group_tests {
    ($module:ident, $point:ident, $bulk:ident, $element:ident, $raw:ty, $ark:ty) => {
        mod $module {
            use super::*;
            use halo::scaling::{Algorithm, Selection};
            type Point = halo::$point;
            type Bulk = halo::$bulk;
            type Raw = $raw;
            type Ark = $ark;

            fn raw(k: u64) -> Raw {
                Raw::generator()
                    .mul_bigint(Fr::from(k).into_bigint())
                    .into_affine()
            }
            fn point(k: u64) -> Point {
                Point::from_bytes(&bytes(&raw(k))).unwrap()
            }
            fn assert_bytes(actual: Point, expected: Raw) {
                let encoded = bytes(&expected);
                assert_eq!(actual.to_bytes().as_slice(), encoded);
                assert_eq!(Point::from_bytes(&encoded).unwrap(), actual);
            }

            #[test]
            fn exact_bytes_identity_sign_and_arithmetic_match_arkworks() {
                for k in 0..25 {
                    let p = point(k);
                    assert_bytes(p, raw(k));
                    assert_bytes(p.neg(), -raw(k));
                    assert_bytes(
                        p.add(&Point::generator()),
                        (raw(k) + Raw::generator()).into_affine(),
                    );
                    assert_eq!(p.add(&p.neg()), Point::identity());
                    assert_eq!(p.add(&Point::identity()), p);
                    assert_eq!(p.is_identity(), k == 0);
                    assert!(p.equal(&p));
                    assert_eq!(Point::from_element(p.into_element()).unwrap(), p);
                    for s in scalars() {
                        assert_bytes(
                            p.scale(scalar(s)),
                            raw(k).mul_bigint(s.into_bigint()).into_affine(),
                        );
                    }
                }
                for len in [0, 1, Point::BYTES - 1, Point::BYTES + 1, 2 * Point::BYTES] {
                    let bad = vec![0; len];
                    assert!(Point::from_bytes(&bad).is_err());
                    assert!(Ark::from_bytes(&bad).is_err());
                }
                let mut infinity = vec![0; Point::BYTES];
                infinity[Point::BYTES - 1] = 0x40;
                assert_eq!(Point::identity().to_bytes().as_slice(), infinity);
                for changed in [0, Point::BYTES - 1] {
                    let mut bad = infinity.clone();
                    bad[changed] |= 1;
                    assert!(Point::from_bytes(&bad).is_err());
                    assert!(Ark::from_bytes(&bad).is_err());
                }
                infinity[Point::BYTES - 1] |= 0x80;
                assert!(Point::from_bytes(&infinity).is_err());
                assert!(Ark::from_bytes(&infinity).is_err());
                let mut valid = Point::generator().to_bytes();
                valid[Point::BYTES - 1] ^= 0x80;
                assert_eq!(Point::from_bytes(&valid).unwrap(), Point::generator().neg());
            }

            #[test]
            fn malformed_encoding_acceptance_matches_canonical_arkworks() {
                // A deterministic bounded corpus spans nonsquares, subgroup
                // failures (G2), signs and coordinate boundary bit patterns.
                for seed in 0..48u64 {
                    let mut candidate = vec![0; Point::BYTES];
                    let mut state = seed + 1;
                    for value in &mut candidate {
                        state ^= state << 13;
                        state ^= state >> 7;
                        state ^= state << 17;
                        *value = state as u8;
                    }
                    candidate[Point::BYTES - 1] &= 0xbf;
                    let actual = Point::from_bytes(&candidate);
                    let reference = Ark::from_bytes(&candidate);
                    assert_eq!(actual.is_ok(), reference.is_ok(), "seed={seed}");
                    if let (Ok(actual), Ok(reference)) = (actual, reference) {
                        assert_eq!(actual.to_bytes().as_slice(), reference.to_bytes().unwrap());
                    }
                }
            }

            #[test]
            fn vector_scaling_and_arithmetic_match_arkworks_across_chunks_and_cpu_contexts() {
                let cpu = zkc_kernels::cpu::CpuExecution::new(if cfg!(feature = "parallel") {
                    2
                } else {
                    1
                })
                .unwrap();
                let serial = zkc_kernels::cpu::CpuExecution::serial().unwrap();
                for len in [0, 1, 3, 65, 257] {
                    let inputs: Vec<_> = (0..len).map(|i| point((i % 5) as u64)).collect();
                    let originals = inputs.clone();
                    let samples = scalars();
                    let scalars: Vec<_> = (0..len)
                        .map(|i| scalar(samples[i % samples.len()]))
                        .collect();
                    let values = Bulk::from_slice(&inputs).unwrap();
                    let coefficients = ScalarVector::from_slice(&scalars).unwrap();
                    let mut out = Bulk::filled(len, Point::generator()).unwrap();
                    for algorithm in [
                        Algorithm::Direct,
                        Algorithm::Batched {
                            chunk_len: len.min(17),
                        },
                        Algorithm::Batched {
                            chunk_len: len.min(256),
                        },
                    ] {
                        if len < 2 && algorithm != Algorithm::Direct {
                            continue;
                        }
                        let mut plan =
                            Point::scaling_plan(len, Selection::Fixed(algorithm)).unwrap();
                        cpu.enter(|| {
                            values.scale_each_with_plan_into(&coefficients, &mut out, &mut plan)
                        })
                        .unwrap();
                        let parallel_result = out.iter().collect::<Vec<_>>();
                        serial
                            .enter(|| {
                                values.scale_each_with_plan_into(&coefficients, &mut out, &mut plan)
                            })
                            .unwrap();
                        assert_eq!(out.iter().collect::<Vec<_>>(), parallel_result);
                        for i in 0..len {
                            assert_bytes(
                                out.get(i).unwrap(),
                                raw((i % 5) as u64)
                                    .mul_bigint(samples[i % samples.len()].into_bigint())
                                    .into_affine(),
                            );
                        }
                        for s in [Fr::zero(), Fr::from(7), -Fr::one()] {
                            values
                                .scale_with_plan_into(scalar(s), &mut out, &mut plan)
                                .unwrap();
                            for i in 0..len {
                                assert_bytes(
                                    out.get(i).unwrap(),
                                    raw((i % 5) as u64)
                                        .mul_bigint(s.into_bigint())
                                        .into_affine(),
                                );
                            }
                        }
                        let mut wrappers = vec![Point::identity(); len];
                        Point::scale_each_into(&scalars, &inputs, &mut wrappers, &mut plan)
                            .unwrap();
                        for (i, p) in wrappers.iter().enumerate() {
                            assert_bytes(
                                *p,
                                raw((i % 5) as u64)
                                    .mul_bigint(samples[i % samples.len()].into_bigint())
                                    .into_affine(),
                            );
                        }
                        Point::scale_many_into(&inputs, Scalar::from(3), &mut wrappers, &mut plan)
                            .unwrap();
                        assert_eq!(
                            wrappers,
                            inputs
                                .iter()
                                .map(|p| p.scale(Scalar::from(3)))
                                .collect::<Vec<_>>()
                        );
                        assert_eq!(plan.algorithm(), algorithm);
                    }
                    cpu.enter(|| values.add_into(&values, &mut out)).unwrap();
                    assert_eq!(
                        out.iter().collect::<Vec<_>>(),
                        inputs.iter().map(|p| p.add(p)).collect::<Vec<_>>()
                    );
                    values.neg_into(&mut out).unwrap();
                    assert_eq!(
                        out.iter().collect::<Vec<_>>(),
                        inputs.iter().map(Point::neg).collect::<Vec<_>>()
                    );
                    values.scale_into(Scalar::from(5), &mut out).unwrap();
                    assert_eq!(
                        out.iter().collect::<Vec<_>>(),
                        inputs
                            .iter()
                            .map(|p| p.scale(Scalar::from(5)))
                            .collect::<Vec<_>>()
                    );
                    values.scale_each_into(&coefficients, &mut out).unwrap();
                    assert_eq!(
                        out.iter().collect::<Vec<_>>(),
                        inputs
                            .iter()
                            .zip(&scalars)
                            .map(|(p, s)| p.scale(*s))
                            .collect::<Vec<_>>()
                    );
                    assert_eq!(
                        values.sum(),
                        inputs.iter().fold(Point::identity(), |a, b| a.add(b))
                    );
                    assert_eq!(inputs, originals);
                    assert_eq!(values.iter().collect::<Vec<_>>(), originals);
                    let mut encoding = vec![0; len * Point::BYTES];
                    values.write_bytes(&mut encoding).unwrap();
                    assert_eq!(Bulk::from_bytes(&encoding).unwrap(), values);
                    let mut owned = values.into_elements();
                    owned.reserve(3);
                    let address = owned.as_ptr();
                    let expected_capacity_bytes = owned.capacity() * size_of::<halo::$element>();
                    let restored = Bulk::from_elements(owned).unwrap();
                    assert_eq!(restored.as_elements().as_ptr(), address);
                    assert_eq!(restored.storage_bytes(), expected_capacity_bytes);
                }
            }

            #[test]
            fn variable_time_msm_empty_zero_mismatch_and_window_boundaries() {
                let samples = scalars();
                for len in [0, 1, 3, 4, 5, 31, 32, 33, 65] {
                    let points: Vec<_> = (0..len).map(|i| point((i % 5) as u64)).collect();
                    let coefficients: Vec<_> = (0..len)
                        .map(|i| scalar(samples[i % samples.len()]))
                        .collect();
                    let expected = (0..len)
                        .fold(Raw::zero().into_group(), |a, i| {
                            a + raw((i % 5) as u64)
                                .mul_bigint(samples[i % samples.len()].into_bigint())
                        })
                        .into_affine();
                    assert_bytes(Point::msm(&coefficients, &points).unwrap(), expected);
                    let owned = Bulk::from_slice(&points).unwrap();
                    assert_bytes(
                        owned
                            .msm(&ScalarVector::from_slice(&coefficients).unwrap())
                            .unwrap(),
                        expected,
                    );
                    assert_eq!(
                        Point::msm(&vec![Scalar::ZERO; len], &points).unwrap(),
                        Point::identity()
                    );
                    assert_eq!(
                        owned
                            .msm(&ScalarVector::filled(len, Scalar::ZERO).unwrap())
                            .unwrap(),
                        Point::identity()
                    );
                    assert_eq!(
                        Point::msm(&vec![Scalar::ONE; len + 1], &points),
                        Err(Error::LengthMismatch)
                    );
                    assert_eq!(
                        owned.msm(&ScalarVector::filled(len + 1, Scalar::ONE).unwrap()),
                        Err(Error::LengthMismatch)
                    );
                }
            }

            #[test]
            fn plans_and_refusals_have_checked_bounds_and_no_partial_writes() {
                let unit = Point::scaling_workspace_bytes(1).unwrap();
                for budget in [0, 2 * unit - 1, 2 * unit, 7 * unit, usize::MAX] {
                    let plan = Point::scaling_plan(
                        17,
                        Selection::Automatic {
                            max_workspace: budget,
                        },
                    )
                    .unwrap();
                    assert_eq!(
                        plan.workspace_bytes(),
                        Point::scaling_workspace_bound(17, budget)
                    );
                    assert!(plan.workspace_bytes() <= budget);
                    assert_eq!(plan.output_bytes(), 17 * size_of::<halo::$element>());
                    assert_eq!(plan.len(), 17);
                }
                assert!(Point::scaling_workspace_bytes(257).is_none());
                assert!(Point::scaling_workspace_bytes(usize::MAX).is_none());
                for (len, chunk_len) in [(0, 2), (1, 2), (17, 0), (17, 1), (17, 18), (257, 257)] {
                    assert!(matches!(
                        Point::scaling_plan(
                            len,
                            Selection::Fixed(Algorithm::Batched { chunk_len })
                        ),
                        Err(Error::InvalidPlan)
                    ));
                }
                assert!(matches!(
                    Point::scaling_plan(usize::MAX, Selection::Fixed(Algorithm::Direct)),
                    Err(Error::CapacityOverflow)
                ));
                let points = [Point::generator(); 3];
                let mut out = [Point::generator(); 3];
                let saved = out;
                let mut plan =
                    Point::scaling_plan(3, Selection::Fixed(Algorithm::Batched { chunk_len: 2 }))
                        .unwrap();
                assert_eq!(
                    Point::scale_many_into(&points[..2], Scalar::ZERO, &mut out, &mut plan),
                    Err(Error::LengthMismatch)
                );
                assert_eq!(
                    Point::scale_many_into(&points, Scalar::ZERO, &mut out[..2], &mut plan),
                    Err(Error::LengthMismatch)
                );
                assert_eq!(
                    Point::scale_each_into(&[Scalar::ONE; 2], &points, &mut out, &mut plan),
                    Err(Error::LengthMismatch)
                );
                assert_eq!(out, saved);
                let values = Bulk::from_slice(&points).unwrap();
                let mut destination = Bulk::from_slice(&saved).unwrap();
                assert_eq!(
                    values.add_into(&Bulk::default(), &mut destination),
                    Err(Error::LengthMismatch)
                );
                assert_eq!(
                    values.scale_each_into(&ScalarVector::default(), &mut destination),
                    Err(Error::LengthMismatch)
                );
                assert_eq!(destination.iter().collect::<Vec<_>>(), saved);
                let mut bad_shape = vec![42; 3 * Point::BYTES - 1];
                assert_eq!(
                    values.write_bytes(&mut bad_shape),
                    Err(Error::LengthMismatch)
                );
                assert!(bad_shape.iter().all(|b| *b == 42));
                assert!(Bulk::from_bytes(&bad_shape).is_err());
            }

            #[cfg(feature = "test-utils")]
            #[test]
            fn scratch_reservation_failure_precedes_writes_or_selects_direct() {
                for failure in 0..2 {
                    let _guard = zkc_kernels::allocation::failure::after(failure);
                    assert!(matches!(
                        Point::scaling_plan(
                            17,
                            Selection::Fixed(Algorithm::Batched { chunk_len: 7 })
                        ),
                        Err(Error::Allocation)
                    ));
                }
                for failure in 0..2 {
                    let _guard = zkc_kernels::allocation::failure::after(failure);
                    let mut plan = Point::scaling_plan(
                        17,
                        Selection::Automatic {
                            max_workspace: usize::MAX,
                        },
                    )
                    .unwrap();
                    assert_eq!(plan.algorithm(), Algorithm::Direct);
                    assert_eq!(plan.workspace_bytes(), 0);
                    let points = [Point::generator(); 17];
                    let mut out = [Point::identity(); 17];
                    Point::scale_many_into(&points, Scalar::from(3), &mut out, &mut plan).unwrap();
                    assert!(out.iter().all(|p| *p == point(3)));
                }
            }
        }
    };
}

group_tests!(g1, G1, G1Vector, G1Element, G1Affine, ark::G1);
group_tests!(g2, G2, G2Vector, G2Element, G2Affine, ark::G2);

#[test]
fn malformed_fq2_components_never_panic_and_invalid_affine_ingress_is_refused() {
    use halo2curves_axiom::bn256::{Fq as Hq, Fq2 as Hq2};
    let modulus = Fq::MODULUS.to_bytes_le();
    for offset in [0, 32] {
        for bad_component in [modulus.clone(), vec![255; 32]] {
            let mut bad = G2::generator().to_bytes();
            bad[offset..offset + 32].copy_from_slice(&bad_component);
            // Preserve finite flags; keep the noncanonical low 254 bits.
            bad[63] &= 0x3f;
            let decoded = std::panic::catch_unwind(|| G2::from_bytes(&bad));
            assert_eq!(decoded.unwrap(), Err(Error::InvalidEncoding));
            assert!(ark::G2::from_bytes(&bad).is_err());
        }
    }
    let bad_g1 = halo::G1Element {
        x: Hq::from(1),
        y: Hq::from(1),
    };
    assert!(G1::from_element(bad_g1).is_err());
    assert!(halo::G1Vector::from_elements(vec![G1::generator().into_element(), bad_g1]).is_err());
    let bad_g2 = halo::G2Element {
        x: Hq2::from(1),
        y: Hq2::from(1),
    };
    assert!(G2::from_element(bad_g2).is_err());
    assert!(halo::G2Vector::from_elements(vec![G2::generator().into_element(), bad_g2]).is_err());
    for candidate in [Fq::MODULUS.to_bytes_le(), vec![255; 32]] {
        assert!(G1::from_bytes(&candidate).is_err());
        assert!(ark::G1::from_bytes(&candidate).is_err());
    }
}

#[test]
fn on_curve_g2_outside_subgroup_is_refused_at_every_ingress() {
    use halo2curves_axiom::{
        bn256::{Fq as Hq, Fq2 as Hq2},
        ff::PrimeField as _,
    };
    let wrong = (0..100u64)
        .find_map(|n| {
            G2Affine::get_point_from_x_unchecked(Fq2::new(Fq::from(n), Fq::one()), false)
                .filter(|p| !p.is_in_correct_subgroup_assuming_on_curve())
        })
        .unwrap();
    assert!(wrong.is_on_curve());
    let encoded = bytes(&wrong);
    assert!(G2::from_bytes(&encoded).is_err());
    assert!(halo::G2Vector::from_bytes(&encoded).is_err());
    assert!(ark::G2::from_bytes(&encoded).is_err());
    let q = |v: Fq| Option::<Hq>::from(Hq::from_repr(bytes(&v).try_into().unwrap())).unwrap();
    let point = halo::G2Element {
        x: Hq2::new(q(wrong.x.c0), q(wrong.x.c1)),
        y: Hq2::new(q(wrong.y.c0), q(wrong.y.c1)),
    };
    assert!(G2::from_element(point).is_err());
    assert!(halo::G2Vector::from_elements(vec![point]).is_err());
}

#[test]
fn ark_sign_uses_lexicographic_order_including_extension_c1_before_c0() {
    // Ensure this corpus distinguishes mathematical sign from both parity and
    // the wrong extension coefficient priority, rather than only round trips.
    let mut differs_from_parity = false;
    let mut differs_from_c0_first = false;
    for k in 1..33u64 {
        let p = G2Affine::generator()
            .mul_bigint(Fr::from(k).into_bigint())
            .into_affine();
        let negative = p.y > -p.y;
        differs_from_parity |= negative != p.y.c0.into_bigint().is_odd();
        differs_from_c0_first |= negative != (p.y.c0 > -p.y.c0);
        let actual = G2::from_bytes(&bytes(&p)).unwrap().to_bytes();
        assert_eq!(actual[63] & 0x80 != 0, negative);
        assert_eq!(actual.as_slice(), bytes(&p));
    }
    assert!(differs_from_parity);
    assert!(differs_from_c0_first);
}

#[test]
fn pairing_products_match_arkworks_for_empty_units_false_and_bilinear_cancellation() {
    let p = G1::generator();
    let q = G2::generator();
    let cases = [
        (vec![], vec![]),
        (vec![G1::identity()], vec![q]),
        (vec![p], vec![G2::identity()]),
        (vec![p], vec![q]),
        (vec![p, p.neg()], vec![q, q]),
        (vec![p, p], vec![q, q.neg()]),
        (
            vec![p.scale(Scalar::from(7)), p.neg()],
            vec![q, q.scale(Scalar::from(7))],
        ),
        (
            vec![p.scale(Scalar::from(7)), p.neg()],
            vec![q, q.scale(Scalar::from(8))],
        ),
    ];
    for (left, right) in cases {
        let raw_left: Vec<_> = left
            .iter()
            .map(|p| ark::G1::from_bytes(&p.to_bytes()).unwrap())
            .collect();
        let raw_right: Vec<_> = right
            .iter()
            .map(|q| ark::G2::from_bytes(&q.to_bytes()).unwrap())
            .collect();
        let expected = ark::pairing_check(&raw_left, &raw_right).unwrap();
        assert_eq!(halo::pairing_check(&left, &right).unwrap(), expected);
        assert_eq!(
            halo::pairing_check_bulk(
                &halo::G1Vector::from_slice(&left).unwrap(),
                &halo::G2Vector::from_slice(&right).unwrap()
            )
            .unwrap(),
            expected
        );
    }
    assert!(!Bn254::pairing(G1Affine::generator(), G2Affine::generator()).is_zero());
    assert!(!halo::pairing_check(&[p], &[q]).unwrap());
    assert!(halo::pairing_check(&[], &[]).unwrap());
    assert_eq!(halo::pairing_check(&[p], &[]), Err(Error::LengthMismatch));
    assert_eq!(
        halo::pairing_check_bulk(
            &halo::G1Vector::filled(1, p).unwrap(),
            &halo::G2Vector::default()
        ),
        Err(Error::LengthMismatch)
    );
    assert_eq!(
        halo::arkworks::export_g1(halo::arkworks::import_g1(ark::G1::generator()).unwrap())
            .unwrap(),
        ark::G1::generator()
    );
    assert_eq!(
        halo::arkworks::export_g2(halo::arkworks::import_g2(ark::G2::generator()).unwrap())
            .unwrap(),
        ark::G2::generator()
    );
}

#[test]
fn true_pairing_equation_requires_final_exponentiation_of_miller_product() {
    use halo2curves_axiom::{
        bn256::{G2Prepared, Gt, multi_miller_loop},
        pairing::MillerLoopResult,
    };
    let p = G1::generator();
    let q = G2::generator();
    let left = [p.scale(Scalar::from(7)), p.neg()];
    let right = [q, q.scale(Scalar::from(7))];
    let a = left.map(G1::into_element);
    let b = right.map(|q| G2Prepared::from_affine(q.into_element()));
    let unreduced = multi_miller_loop(&[(&a[0], &b[0]), (&a[1], &b[1])]);
    assert_ne!(unreduced, Gt::identity());
    assert_eq!(unreduced.final_exponentiation(), Gt::identity());
    assert!(halo::pairing_check(&left, &right).unwrap());
}

#[test]
fn admission_scores_match_documented_empty_and_window_boundaries() {
    // Fixed examples from the public-shape contract, independent of the helpers
    // used by Native to choose its actual admission limits.
    for (points, work) in [
        (0, 0),
        (1, 1061),
        (3, 1639),
        (4, 1419),
        (31, 4605),
        (32, 4405),
        (54, 6539),
        (55, 6545),
        (148, 14357),
        (149, 14186),
    ] {
        assert_eq!(halo::msm_work(points), Ok(work), "points={points}");
    }
    for (pairs, work) in [(0, 0), (1, 8374), (3, 8738), (32, 14016)] {
        assert_eq!(halo::pairing_work(pairs), Ok(work), "pairs={pairs}");
    }
}

#[test]
fn workspace_and_work_bounds_use_only_public_shape_and_refuse_overflow() {
    assert_eq!(halo::msm_workspace_bytes(0), Ok(0));
    assert_eq!(halo::msm_work(0), Ok(0));
    assert_eq!(halo::pairing_workspace_bytes(0), Ok(0));
    assert_eq!(halo::pairing_work(0), Ok(0));
    for n in [1, 3, 4, 31, 32, 33, 65, 256, 1024] {
        assert!(halo::msm_workspace_bytes(n).unwrap() >= n * (32 + size_of::<halo::G2Element>()));
        assert!(halo::msm_work(n).unwrap() >= 32 * n as u64);
        // 91 Fq2 triples alone are 17,472 bytes per pair; capacity/growth,
        // staging and Miller references must also be admitted.
        assert!(halo::pairing_workspace_bytes(n).unwrap() > n * 17_472);
        assert!(halo::pairing_work(n).unwrap() >= 182 * n as u64);
    }
    assert_eq!(
        halo::msm_workspace_bytes(usize::MAX),
        Err(Error::CapacityOverflow)
    );
    assert_eq!(halo::msm_work(usize::MAX), Err(Error::CapacityOverflow));
    assert_eq!(
        halo::pairing_workspace_bytes(usize::MAX),
        Err(Error::CapacityOverflow)
    );
    assert_eq!(halo::pairing_work(usize::MAX), Err(Error::CapacityOverflow));
    if usize::BITS > 32 {
        let truncated = u32::MAX as usize + 1;
        assert_eq!(
            halo::msm_workspace_bytes(truncated),
            Err(Error::CapacityOverflow)
        );
        assert_eq!(halo::msm_work(truncated), Err(Error::CapacityOverflow));
    }
}

#[cfg(feature = "test-utils")]
#[test]
fn managed_allocation_refusals_precede_msm_pairing_and_bulk_publication() {
    for successful in 0..2 {
        let _guard = zkc_kernels::allocation::failure::after(successful);
        assert_eq!(
            G1::msm(&[Scalar::ONE], &[G1::generator()]),
            Err(Error::Allocation)
        );
    }
    for successful in 0..3 {
        let _guard = zkc_kernels::allocation::failure::after(successful);
        assert_eq!(
            halo::pairing_check(&[G1::generator()], &[G2::generator()]),
            Err(Error::Allocation)
        );
    }
    let _guard = zkc_kernels::allocation::failure::after(0);
    assert!(matches!(
        halo::G2Vector::from_bytes(&G2::generator().to_bytes()),
        Err(Error::Allocation)
    ));
}
