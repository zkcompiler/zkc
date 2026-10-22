//! Installed vector scaling, historical admission, optional scratch and aliases.
#[path = "domains/support.rs"]
mod support;

use support::{Controlled, assert_value, backend, one};
use zkc_native::{Policy, Value};
use zkc_runtime::vm::OperationBinding;

fn binding(name: &str, group: &str, provider: &str) -> OperationBinding {
    OperationBinding {
        contract: name.into(),
        arguments: vec![group.into()],
        implementation: format!("{provider}/{name}"),
        physical_arguments: vec![],
    }
}

macro_rules! ark_scaling_tests {
    ($module:ident, $point:ty, $scalar:ty, $nominal:literal,
        $points:ident, $scalars:ident, $field:ident, $width:expr) => {
        mod $module {
            use super::*;
            use std::sync::Arc;
            type Point = $point;
            type Scalar = $scalar;
            fn repeated_add(point: Point, scalar: usize) -> Point {
                (0..scalar).fold(Point::identity(), |sum, _| sum.add(&point))
            }
            fn points(len: usize) -> Value {
                Value::$points(
                    (0..len)
                        .map(|i| repeated_add(Point::generator(), i % 4))
                        .collect::<Vec<_>>()
                        .into(),
                )
            }
            fn inputs(name: &str, points: Value, len: usize) -> Vec<Value> {
                if name == "curve.vector_scale" {
                    vec![points, Value::$field(Scalar::from(3))]
                } else {
                    vec![
                        Value::$scalars(
                            (0..len)
                                .map(|i| Scalar::from((i % 5) as u64))
                                .collect::<Vec<_>>()
                                .into(),
                        ),
                        points,
                    ]
                }
            }

            #[test]
            fn scratch_boundaries_preserve_values_aliases_and_historical_work_acceptance() {
                let unit = Point::scaling_workspace_bytes(1).unwrap();
                for len in [0, 1, 2, 3, 17, 255, 256, 257, 513] {
                    let input = points(len);
                    let alias = input.clone();
                    let saved = points(len);
                    for bytes in [
                        0,
                        2 * unit - 1,
                        2 * unit,
                        17 * unit,
                        256 * unit - 1,
                        256 * unit,
                    ] {
                        for name in ["curve.vector_scale", "curve.scale_each"] {
                            let expected = Value::$points(
                                (0..len)
                                    .map(|i| {
                                        let base = repeated_add(Point::generator(), i % 4);
                                        repeated_add(
                                            base,
                                            if name == "curve.vector_scale" {
                                                3
                                            } else {
                                                i % 5
                                            },
                                        )
                                    })
                                    .collect::<Vec<_>>()
                                    .into(),
                            );
                            let mut driver = Controlled::new(backend(Policy {
                                max_groups: len.max(1),
                                max_value_bytes: (256 + len * $width).max(512),
                                max_numerical_bytes: bytes,
                                max_numerical_work: 0,
                                ..Policy::default()
                            }));
                            driver.output_limit = Some(256 + len * $width);
                            let (result, driver) = one(
                                driver,
                                binding(name, $nominal, "arkworks"),
                                &[],
                                inputs(name, input.clone(), len),
                            );
                            let output = result.unwrap().remove(0);
                            assert_value(&output, &expected);
                            assert_eq!(driver.outputs.len(), 1);
                            assert_eq!(driver.inner.active_frames(), 0);
                            let (Value::$points(original), Value::$points(result)) =
                                (&input, &output)
                            else {
                                panic!("wrong representation")
                            };
                            if len != 0 {
                                assert!(!Arc::ptr_eq(original, result));
                            }
                            assert_value(&input, &alias);
                            assert_value(&input, &saved);
                            assert_value(&alias, &saved);
                        }
                    }
                }
            }

            #[test]
            fn output_bound_and_length_refusal_order_are_unchanged() {
                for len in [0, 3] {
                    let input = points(len);
                    let retained = 256 + len * $width;
                    for name in ["curve.vector_scale", "curve.scale_each"] {
                        let mut driver = Controlled::new(backend(Policy {
                            max_numerical_bytes: 0,
                            max_numerical_work: 0,
                            ..Policy::default()
                        }));
                        driver.output_limit = Some(retained - 1);
                        let (result, driver) = one(
                            driver,
                            binding(name, $nominal, "arkworks"),
                            &[],
                            inputs(name, input.clone(), len),
                        );
                        assert_eq!(result.unwrap_err(), "exhausted:output-bytes");
                        assert!(driver.outputs.is_empty());
                        assert_eq!(driver.inner.active_frames(), 0);
                    }
                }
                let input = points(3);
                let mut driver = Controlled::new(backend(Policy {
                    max_numerical_bytes: 0,
                    max_numerical_work: 0,
                    ..Policy::default()
                }));
                driver.output_limit = Some(0);
                let (result, driver) = one(
                    driver,
                    binding("curve.scale_each", $nominal, "arkworks"),
                    &[],
                    inputs("curve.scale_each", input.clone(), 2),
                );
                assert_eq!(result.unwrap_err(), "refused:length-mismatch");
                assert!(driver.outputs.is_empty());
                assert_value(&input, &points(3));

                // Installed invocation admission still checks group bounds before
                // the reached output allocation, even with zero scratch/work.
                let mut driver = Controlled::new(backend(Policy {
                    max_groups: 2,
                    max_numerical_bytes: 0,
                    max_numerical_work: 0,
                    ..Policy::default()
                }));
                driver.output_limit = Some(0);
                driver.substitute = Some(input);
                let (result, driver) = one(
                    driver,
                    binding("curve.vector_scale", $nominal, "arkworks"),
                    &[],
                    inputs("curve.vector_scale", points(2), 2),
                );
                assert_eq!(result.unwrap_err(), "exhausted:group-limit");
                assert!(driver.outputs.is_empty());
            }
        }
    };
}

ark_scaling_tests!(
    bls_g1,
    zkc_native::G1,
    zkc_native::Scalar,
    "bls12-381.g1",
    Groups,
    Vector,
    Field,
    128
);
ark_scaling_tests!(
    bls_g2,
    zkc_native::Bls12381G2,
    zkc_native::Scalar,
    "bls12-381.g2",
    Bls12381G2Vector,
    Vector,
    Field,
    size_of::<zkc_native::Bls12381G2>()
);
ark_scaling_tests!(
    bn_g1,
    zkc_native::Bn254G1,
    zkc_native::Bn254Scalar,
    "bn254.g1",
    Bn254G1Vector,
    Bn254Vector,
    Bn254Field,
    size_of::<zkc_native::Bn254G1>()
);
ark_scaling_tests!(
    bn_g2,
    zkc_native::Bn254G2,
    zkc_native::Bn254Scalar,
    "bn254.g2",
    Bn254G2Vector,
    Bn254Vector,
    Bn254Field,
    size_of::<zkc_native::Bn254G2>()
);

#[test]
fn dalek_vector_paths_keep_zero_numerical_budget_acceptance() {
    use zkc_native::{EdwardsPrime, RistrettoScalar};
    for edwards in [false, true] {
        let len = 257;
        let (nominal, input, expected) = if edwards {
            let g = EdwardsPrime::generator();
            (
                "edwards25519.prime",
                Value::EdwardsGroups(vec![g; len].into()),
                Value::EdwardsGroups(vec![g.scale(RistrettoScalar::from(3u64)); len].into()),
            )
        } else {
            let g = curve25519_dalek::constants::RISTRETTO_BASEPOINT_POINT;
            (
                "ristretto255.group",
                Value::RistrettoGroups(vec![g; len].into()),
                Value::RistrettoGroups(vec![g * RistrettoScalar::from(3u64); len].into()),
            )
        };
        for name in ["curve.vector_scale", "curve.scale_each"] {
            let args = if name == "curve.vector_scale" {
                vec![
                    input.clone(),
                    Value::RistrettoField(RistrettoScalar::from(3u64)),
                ]
            } else {
                vec![
                    Value::RistrettoVector(vec![RistrettoScalar::from(3u64); len].into()),
                    input.clone(),
                ]
            };
            let result = one(
                backend(Policy {
                    max_numerical_bytes: 0,
                    max_numerical_work: 0,
                    ..Policy::default()
                }),
                binding(name, nominal, "dalek"),
                &[],
                args,
            )
            .0
            .unwrap();
            assert_value(&result[0], &expected);
        }
    }
}

#[test]
fn nominal_and_physical_operand_checks_precede_output_preflight() {
    use zkc_native::{Bn254Scalar, RistrettoScalar, Scalar};
    for (group, provider, points, scalar, scalars) in [
        (
            "bls12-381.g1",
            "arkworks",
            Value::Groups(vec![].into()),
            Value::Field(Scalar::from(3)),
            Value::Vector(vec![].into()),
        ),
        (
            "bls12-381.g2",
            "arkworks",
            Value::Bls12381G2Vector(vec![].into()),
            Value::Field(Scalar::from(3)),
            Value::Vector(vec![].into()),
        ),
        (
            "bn254.g1",
            "arkworks",
            Value::Bn254G1Vector(vec![].into()),
            Value::Bn254Field(Bn254Scalar::from(3)),
            Value::Bn254Vector(vec![].into()),
        ),
        (
            "bn254.g2",
            "arkworks",
            Value::Bn254G2Vector(vec![].into()),
            Value::Bn254Field(Bn254Scalar::from(3)),
            Value::Bn254Vector(vec![].into()),
        ),
        (
            "ristretto255.group",
            "dalek",
            Value::RistrettoGroups(vec![].into()),
            Value::RistrettoField(RistrettoScalar::from(3u64)),
            Value::RistrettoVector(vec![].into()),
        ),
        (
            "edwards25519.prime",
            "dalek",
            Value::EdwardsGroups(vec![].into()),
            Value::RistrettoField(RistrettoScalar::from(3u64)),
            Value::RistrettoVector(vec![].into()),
        ),
    ] {
        for name in ["curve.vector_scale", "curve.scale_each"] {
            let wrong_nominal = match (name, provider) {
                ("curve.vector_scale", "arkworks") => Value::RistrettoGroups(vec![].into()),
                ("curve.vector_scale", _) => Value::Groups(vec![].into()),
                (_, "arkworks") => Value::RistrettoVector(vec![].into()),
                _ => Value::Vector(vec![].into()),
            };
            for replacement in [wrong_nominal, Value::Bool(false)] {
                let args = if name == "curve.vector_scale" {
                    vec![points.clone(), scalar.clone()]
                } else {
                    vec![scalars.clone(), points.clone()]
                };
                let mut driver = Controlled::new(backend(Policy::default()));
                driver.output_limit = Some(0);
                driver.substitute = Some(replacement);
                let (result, driver) = one(driver, binding(name, group, provider), &[], args);
                assert_eq!(result.unwrap_err(), "refused:kernel-operands");
                assert!(driver.outputs.is_empty());
                assert_eq!(driver.inner.active_frames(), 0);
            }
        }
    }
}

#[test]
fn optional_scratch_allocation_failure_preserves_the_installed_result() {
    use zkc_kernels::{
        allocation::failure,
        arkworks::bls12_381::{G1, Scalar},
    };
    let g = G1::generator();
    let input = Value::Groups(vec![g, G1::identity(), g.neg()].into());
    let saved = input.clone();
    let expected =
        Value::Groups(vec![g.add(&g).add(&g), G1::identity(), g.add(&g).add(&g).neg()].into());
    // The destination is mandatory; each of the following three scratch buffers
    // is optional. Failed preparation must discard partial scratch before using
    // the direct algorithm, preserving the installed operation and input aliases.
    for successful in 0..=3 {
        let driver = Controlled::new(backend(Policy {
            max_numerical_work: 0,
            ..Policy::default()
        }));
        let guard = failure::after(successful);
        let (result, driver) = one(
            driver,
            binding("curve.vector_scale", "bls12-381.g1", "arkworks"),
            &[],
            vec![input.clone(), Value::Field(Scalar::from(3))],
        );
        drop(guard);
        if successful == 0 {
            assert_eq!(result.unwrap_err(), "exhausted:allocation");
            assert!(driver.outputs.is_empty());
        } else {
            assert_value(&result.unwrap()[0], &expected);
            assert_eq!(driver.outputs.len(), 1);
        }
        assert_eq!(driver.inner.active_frames(), 0);
        assert_value(&input, &saved);
    }
}
