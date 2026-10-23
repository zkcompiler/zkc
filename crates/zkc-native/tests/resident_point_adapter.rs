//! Shared resident dispatcher boundaries for validated point views and builders.
#[path = "domains/support.rs"]
mod support;

use std::sync::Arc;
use zkc_native::{Policy, Value};
use zkc_runtime::vm::OperationBinding;

struct Case {
    provider: &'static str,
    domain: &'static str,
    width: usize,
    point: Value,
    points: Value,
    short_points: Value,
    scalars: Value,
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
    macro_rules! case {
        ($kernel:path, $provider:literal, $domain:literal, $group:ident, $bulk:ident,
         $single:ident, $many:ident, $scalars:ident, $wrap:expr) => {{
            use $kernel as kernel;
            let point = kernel::$group::generator();
            Case {
                provider: $provider,
                domain: $domain,
                width: size_of::<kernel::$group>(),
                point: Value::$single(($wrap)(point)),
                points: Value::$many(Arc::new(
                    kernel::$bulk::from_slice(&[
                        kernel::$group::identity(),
                        point,
                        point.neg(),
                        point,
                    ])
                    .unwrap(),
                )),
                short_points: Value::$many(Arc::new(
                    kernel::$bulk::from_slice(&[point; 3]).unwrap(),
                )),
                scalars: Value::$scalars(Arc::new(
                    kernel::ScalarVector::from_slice(&[kernel::Scalar::ONE; 4]).unwrap(),
                )),
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
            |v| v
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
            Arc::new
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
            |v| v
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
            Arc::new
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
                Some(511),
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
