//! Shared resident dispatcher boundaries for validated point views and builders.
#[path = "domains/support.rs"]
mod support;
use zkc_runtime::vm::Value as _;

use std::sync::Arc;
use zkc_cpu::{Policy, Value};
use zkc_runtime::vm::OperationBinding;

struct Case {
    provider: &'static str,
    domain: &'static str,
    width: usize,
    point: Value,
    points: Value,
    short_points: Value,
    scalars: Value,
    scalar: Value,
    zero: Value,
    expected_each: Value,
    expected_shared: Value,
    expected_zero: Value,
    scratch_unit: usize,
}
impl Case {
    fn binding(&self, name: &str) -> OperationBinding {
        OperationBinding {
            contract: name.into(),
            arguments: vec![self.domain.into()],
            implementation: format!("{}/resident/{name}", self.provider),
            physical_arguments: vec![],
        }
    }
}

fn cases() -> Vec<Case> {
    cases_with_len(4)
}
fn cases_with_len(len: usize) -> Vec<Case> {
    macro_rules! case {
        ($kernel:path, $provider:literal, $domain:literal, $group:ident, $bulk:ident,
         $single:ident, $many:ident, $scalars:ident, $field:ident, $wrap:expr,
         $scratch_unit:expr) => {{
            use $kernel as kernel;
            let point = kernel::$group::generator();
            let bases = [
                point,
                kernel::$group::identity(),
                point.neg(),
                point.add(&point),
                point.add(&point).add(&point).neg(),
            ];
            let coefficients = [7, 0, 1, 2, 19, u64::MAX, 0];
            // Independent of scalar multiplication and bulk normalization. The
            // full u64 sample also detects scalar truncation and offset errors.
            let multiply = |mut base: kernel::$group, mut coefficient: u64| {
                let mut sum = kernel::$group::identity();
                while coefficient != 0 {
                    if coefficient & 1 != 0 {
                        sum = sum.add(&base);
                    }
                    base = base.add(&base);
                    coefficient >>= 1;
                }
                sum
            };
            Case {
                provider: $provider,
                domain: $domain,
                width: size_of::<kernel::$group>(),
                point: Value::$single(($wrap)(point)),
                points: Value::$many(Arc::new(
                    kernel::$bulk::try_from_fn(len, |index| Ok(bases[index % bases.len()]))
                        .unwrap(),
                )),
                short_points: Value::$many(Arc::new(
                    kernel::$bulk::try_from_fn(len.saturating_sub(1), |_| Ok(point)).unwrap(),
                )),
                scalars: Value::$scalars(Arc::new(
                    kernel::ScalarVector::try_from_fn(len, |index| {
                        Ok(kernel::Scalar::from(
                            coefficients[index % coefficients.len()],
                        ))
                    })
                    .unwrap(),
                )),
                scalar: Value::$field(kernel::Scalar::from(7)),
                zero: Value::$field(kernel::Scalar::from(0)),
                expected_each: Value::$many(Arc::new(
                    kernel::$bulk::try_from_fn(len, |index| {
                        Ok(multiply(
                            bases[index % bases.len()],
                            coefficients[index % coefficients.len()],
                        ))
                    })
                    .unwrap(),
                )),
                expected_shared: Value::$many(Arc::new(
                    kernel::$bulk::try_from_fn(len, |index| {
                        Ok(multiply(bases[index % bases.len()], 7))
                    })
                    .unwrap(),
                )),
                expected_zero: Value::$many(Arc::new(
                    kernel::$bulk::try_from_fn(len, |_| Ok(kernel::$group::identity())).unwrap(),
                )),
                scratch_unit: $scratch_unit,
            }
        }};
    }
    vec![
        case!(
            zkc_kernels::halo2curves::bn254,
            "halo2curves-axiom",
            "bn254.g1",
            G1,
            G1Vector,
            HaloG1,
            HaloG1Vector,
            HaloVector,
            HaloField,
            |v| v,
            zkc_kernels::halo2curves::bn254::G1::scaling_workspace_bound(2, usize::MAX) / 2
        ),
        case!(
            zkc_kernels::halo2curves::bn254,
            "halo2curves-axiom",
            "bn254.g2",
            G2,
            G2Vector,
            HaloG2,
            HaloG2Vector,
            HaloVector,
            HaloField,
            Arc::new,
            zkc_kernels::halo2curves::bn254::G2::scaling_workspace_bound(2, usize::MAX) / 2
        ),
        case!(
            zkc_kernels::blst::bls12_381,
            "blst",
            "bls12-381.g1",
            G1,
            G1Vector,
            BlstG1,
            BlstG1Vector,
            BlstVector,
            BlstField,
            |v| v,
            0
        ),
        case!(
            zkc_kernels::blst::bls12_381,
            "blst",
            "bls12-381.g2",
            G2,
            G2Vector,
            BlstG2,
            BlstG2Vector,
            BlstVector,
            BlstField,
            Arc::new,
            0
        ),
    ]
}

#[test]
fn shape_output_and_workspace_refusals_precede_destination_allocation() {
    for case in cases() {
        for (name, args, policy, output_limit, expected) in [
            (
                "curve.scale_each",
                vec![case.scalars.clone(), case.short_points.clone()],
                Policy::default(),
                Some(0),
                "refused:length-mismatch",
            ),
            (
                "curve.vector_add",
                vec![case.points.clone(), case.short_points.clone()],
                Policy::default(),
                Some(0),
                "refused:length-mismatch",
            ),
            (
                "curve.split",
                vec![case.short_points.clone()],
                Policy::default(),
                Some(0),
                "refused:split-length",
            ),
            (
                "curve.concat",
                vec![case.points.clone(), case.points.clone()],
                Policy::default(),
                Some(8 * case.width - 1),
                "exhausted:output-bytes",
            ),
            (
                "curve.split",
                vec![case.points.clone()],
                Policy::default(),
                Some(4 * case.width - 1),
                "exhausted:output-bytes",
            ),
            (
                "curve.append",
                vec![case.points.clone(), case.point.clone()],
                Policy {
                    max_groups: 4,
                    ..Policy::default()
                },
                Some(0),
                "exhausted:group-limit",
            ),
            (
                "curve.scale_each",
                vec![case.scalars.clone(), case.points.clone()],
                Policy {
                    max_numerical_bytes: 4 * case.width - 1,
                    ..Policy::default()
                },
                None,
                "exhausted:numerical-bytes",
            ),
            // Scalar result admission historically precedes index lookup.
            (
                "curve.get",
                vec![case.points.clone(), Value::Index(u64::MAX)],
                Policy::default(),
                Some(case.point.retained_bytes() - 1),
                "exhausted:output-bytes",
            ),
            (
                "curve.get",
                vec![case.points.clone(), Value::Index(u64::MAX)],
                Policy::default(),
                None,
                "refused:group-index",
            ),
        ] {
            let encoder = support::backend(Policy::default());
            let original: Vec<_> = args
                .iter()
                .map(|v| encoder.encode_native_value(v).unwrap())
                .collect();
            let mut driver = support::Controlled::new(support::backend(policy));
            driver.output_limit = output_limit;
            let _guard = zkc_kernels::allocation::failure::after(0);
            let (result, driver) = support::one(driver, case.binding(name), &[], args.clone());
            assert_eq!(result.unwrap_err(), expected, "{name}/{}", case.domain);
            assert!(driver.outputs.is_empty());
            assert_eq!(driver.inner.active_frames(), 0);
            assert!(zkc_kernels::allocation::reserve::<u8>(1).is_err());
            for (value, bytes) in args.iter().zip(original) {
                assert_eq!(encoder.encode_native_value(value).unwrap(), bytes);
            }
        }
    }
}

#[test]
fn split_reserves_both_destinations_before_publishing_either() {
    for case in cases() {
        let encoder = support::backend(Policy::default());
        let original = encoder.encode_native_value(&case.points).unwrap();
        let driver = support::Controlled::new(support::backend(Policy::default()));
        // The first destination succeeds and the second fails. No result may
        // escape and the borrowed input must remain intact.
        let _guard = zkc_kernels::allocation::failure::after(1);
        let (result, driver) = support::one(
            driver,
            case.binding("curve.split"),
            &[],
            vec![case.points.clone()],
        );
        assert_eq!(
            result.unwrap_err(),
            "exhausted:allocation",
            "{}",
            case.domain
        );
        assert!(driver.outputs.is_empty());
        assert_eq!(driver.inner.active_frames(), 0);
        assert_eq!(encoder.encode_native_value(&case.points).unwrap(), original);
    }
}

// None selects per-element scaling; Some selects shared-scalar scaling. The
// allocation control specifies failure position and whether it must remain
// pending after success. A pending failure proves no additional managed buffer
// was requested. These controls do not instrument arbitrary allocator calls.
fn check_scaling(
    case: &Case,
    scalar: Option<&Value>,
    expected: &Value,
    cpu: &zkc_cpu::CpuExecution,
    memory: usize,
    allocation: Option<(usize, bool)>,
) {
    let (name, args) = if let Some(scalar) = scalar {
        (
            "curve.vector_scale",
            vec![case.points.clone(), scalar.clone()],
        )
    } else {
        (
            "curve.scale_each",
            vec![case.scalars.clone(), case.points.clone()],
        )
    };
    let encoder = support::backend(Policy::default());
    let original: Vec<_> = args
        .iter()
        .map(|value| encoder.encode_native_value(value).unwrap())
        .collect();
    let expected_bytes = encoder.encode_native_value(expected).unwrap();
    let policy = Policy {
        max_numerical_bytes: memory,
        max_numerical_work: 0, // Preserve the existing curve work contract.
        ..Policy::default()
    };
    let backend = support::backend(policy).with_cpu(cpu.clone()).unwrap();
    let mut driver = support::Controlled::new(backend);
    let payload = match &case.points {
        Value::HaloG1Vector(v) => v.len() * case.width,
        Value::HaloG2Vector(v) => v.len() * case.width,
        Value::BlstG1Vector(v) => v.len() * case.width,
        Value::BlstG2Vector(v) => v.len() * case.width,
        _ => unreachable!(),
    };
    driver.output_limit = Some(256 + payload);
    let failure = allocation.map(|(after, _)| zkc_kernels::allocation::failure::after(after));
    let (result, driver) = support::one(driver, case.binding(name), &[], args.clone());
    result
        .unwrap_or_else(|error| panic!("{}/{name}/{memory}/{allocation:?}: {error}", case.domain));
    if let Some((_, pending)) = allocation {
        assert_eq!(
            zkc_kernels::allocation::reserve::<u8>(1).is_err(),
            pending,
            "{}/{name}/{memory}/{allocation:?}",
            case.domain
        );
    }
    drop(failure);
    assert_eq!(driver.outputs.len(), 1);
    assert_eq!(driver.outputs[0].len(), 1);
    let output = &driver.outputs[0][0];
    assert_eq!(
        encoder.encode_native_value(output).unwrap(),
        expected_bytes,
        "{}/{name}/{memory}/{allocation:?}",
        case.domain
    );
    macro_rules! check_storage {
        ($input:expr, $output:expr) => {{
            assert!(!Arc::ptr_eq($input, $output));
            assert_eq!($output.storage_bytes(), payload);
        }};
    }
    match (&case.points, output) {
        (Value::HaloG1Vector(a), Value::HaloG1Vector(b)) => check_storage!(a, b),
        (Value::HaloG2Vector(a), Value::HaloG2Vector(b)) => check_storage!(a, b),
        (Value::BlstG1Vector(a), Value::BlstG1Vector(b)) => check_storage!(a, b),
        (Value::BlstG2Vector(a), Value::BlstG2Vector(b)) => check_storage!(a, b),
        _ => panic!("changed provider or group"),
    }
    for (value, bytes) in args.iter().zip(original) {
        assert_eq!(encoder.encode_native_value(value).unwrap(), bytes);
    }
    assert_eq!(driver.inner.active_frames(), 0);
}

#[test]
fn resident_scaling_matches_addition_across_worker_grain_and_chunk_boundaries() {
    for workers in [1, 4]
        .into_iter()
        .filter(|&n| cfg!(feature = "parallel") || n == 1)
    {
        let cpu = zkc_cpu::CpuExecution::new(workers).unwrap();
        for len in [0, 1, 31, 32, 33, 63, 64, 65, 255, 256, 257] {
            for case in cases_with_len(len) {
                for (scalar, expected) in [
                    (None, &case.expected_each),
                    (Some(&case.scalar), &case.expected_shared),
                    (Some(&case.zero), &case.expected_zero),
                ] {
                    check_scaling(&case, scalar, expected, &cpu, usize::MAX, None);
                }
            }
        }
    }
}

#[test]
fn resident_scaling_has_exact_mandatory_and_optional_storage_boundaries() {
    let cpu = zkc_cpu::CpuExecution::new(if cfg!(feature = "parallel") { 4 } else { 1 }).unwrap();
    for len in [0, 1, 2, 65, 257] {
        for case in cases_with_len(len) {
            let mandatory = 256 + len * case.width;
            for (scalar, expected) in [
                (None, &case.expected_each),
                (Some(&case.scalar), &case.expected_shared),
            ] {
                let unit = case.scratch_unit;
                let mut allowances = vec![0];
                if unit != 0 && len >= 2 {
                    allowances.extend([
                        2 * unit - 1,
                        2 * unit,
                        3 * unit,
                        256 * unit - 1,
                        256 * unit,
                    ]);
                }
                for scratch in allowances {
                    // Halo needs two scratch arrays once at least two points
                    // fit; BLST never requests these arrays. Including the live
                    // destination in the budget is essential at this boundary.
                    let allocations = if unit != 0 && len >= 2 && scratch >= 2 * unit {
                        3
                    } else {
                        1
                    };
                    check_scaling(
                        &case,
                        scalar,
                        expected,
                        &cpu,
                        mandatory + scratch,
                        Some((allocations, true)),
                    );
                }
                if unit != 0 && len >= 2 {
                    // Each optional array fails independently. Arithmetic must
                    // fall back, with the one-shot failure actually consumed.
                    for after in [1, 2] {
                        check_scaling(
                            &case,
                            scalar,
                            expected,
                            &cpu,
                            mandatory + 256 * unit,
                            Some((after, false)),
                        );
                    }
                }
                let (name, args) = if let Some(scalar) = scalar {
                    (
                        "curve.vector_scale",
                        vec![case.points.clone(), scalar.clone()],
                    )
                } else {
                    (
                        "curve.scale_each",
                        vec![case.scalars.clone(), case.points.clone()],
                    )
                };
                for (output, memory, expected_error) in [
                    (mandatory - 1, 0, "exhausted:output-bytes"),
                    (mandatory, mandatory - 1, "exhausted:numerical-bytes"),
                    (mandatory, mandatory, "exhausted:allocation"),
                ] {
                    let encoder = support::backend(Policy::default());
                    let original: Vec<_> = args
                        .iter()
                        .map(|value| encoder.encode_native_value(value).unwrap())
                        .collect();
                    let backend = support::backend(Policy {
                        max_numerical_bytes: memory,
                        max_numerical_work: 0,
                        ..Policy::default()
                    })
                    .with_cpu(cpu.clone())
                    .unwrap();
                    let mut driver = support::Controlled::new(backend);
                    driver.output_limit = Some(output);
                    let failure = zkc_kernels::allocation::failure::after(0);
                    let (result, driver) =
                        support::one(driver, case.binding(name), &[], args.clone());
                    assert_eq!(
                        result.unwrap_err(),
                        expected_error,
                        "{}/{name}/{len}",
                        case.domain
                    );
                    assert!(driver.outputs.is_empty());
                    assert_eq!(driver.inner.active_frames(), 0);
                    assert_eq!(
                        zkc_kernels::allocation::reserve::<u8>(1).is_err(),
                        expected_error != "exhausted:allocation"
                    );
                    drop(failure);
                    for (value, bytes) in args.iter().zip(original) {
                        assert_eq!(encoder.encode_native_value(value).unwrap(), bytes);
                    }
                }
            }
        }
    }
}
