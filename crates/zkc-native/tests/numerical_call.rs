//! Numerical consumers through the existing installed-operation and VM checks.
#[path = "domains/support.rs"]
mod support;

use p3_field::TwoAdicField;
use std::{mem::size_of, sync::Arc};
use support::{Controlled, backend, one};
use zkc_native::{KoalaBear, KoalaBearExt4, KoalaBearExt8, Policy, Scalar, Value};
use zkc_runtime::vm::{Identity, OperationBinding, Value as RuntimeValue};

fn assert_value(actual: &Value, expected: &Value) {
    assert_eq!(actual.physical_type(), expected.physical_type());
    match (actual, expected) {
        (Value::Table(a), Value::Table(b)) => assert_eq!(a.physical_values(), b.physical_values()),
        (Value::TableMsb(a), Value::TableMsb(b)) => {
            assert_eq!(a.physical_values(), b.physical_values())
        }
        _ => support::assert_value(actual, expected),
    }
}

fn fold_binding(msb: bool) -> OperationBinding {
    OperationBinding {
        contract: "poly.fold".into(),
        arguments: vec!["bls12-381.fr".into()],
        implementation: format!(
            "{}/poly.fold",
            if msb { "arkworks-msb" } else { "arkworks" }
        ),
        physical_arguments: vec![],
    }
}

fn table(msb: bool, values: &[u64]) -> Value {
    let values: Vec<_> = values.iter().copied().map(Scalar::from).collect();
    if msb {
        Value::TableMsb(Arc::new(
            zkc_kernels::arkworks::bls12_381::MsbTable::from_logical(
                &values,
                &Policy::default().ark_bounds(),
            )
            .unwrap(),
        ))
    } else {
        Value::table(&values, &Policy::default()).unwrap()
    }
}

#[test]
fn asymmetric_fold_preserves_each_physical_order_and_input_aliases() {
    for msb in [false, true] {
        let input = table(msb, &[2, 5, 11, 19, 31, 47, 71, 101]);
        let alias = input.clone();
        // Independent first-logical-coordinate restriction at r=3.
        let expected = table(msb, &[89, 131, 191, 265]);
        let first = one(
            backend(Policy::default()),
            fold_binding(msb),
            &[],
            vec![input.clone(), Value::Field(Scalar::from(3))],
        )
        .0
        .unwrap()
        .remove(0);
        assert_eq!(first.physical_type(), input.physical_type());
        assert_value(&first, &expected);
        match (&input, &first) {
            (Value::Table(before), Value::Table(after)) => {
                assert!(!Arc::ptr_eq(before, after));
                assert_eq!(
                    after.physical_values(),
                    &[89u64, 191, 131, 265].map(Scalar::from)
                );
            }
            (Value::TableMsb(before), Value::TableMsb(after)) => {
                assert!(!Arc::ptr_eq(before, after));
                assert_eq!(
                    after.physical_values(),
                    &[89u64, 131, 191, 265].map(Scalar::from)
                );
            }
            _ => panic!("fold changed table representation"),
        }
        // Reuse an alias and then fold again: this also detects a spurious
        // low-bit/logical permutation when freezing the first destination.
        let second = one(
            backend(Policy::default()),
            fold_binding(msb),
            &[],
            vec![alias.clone(), Value::Field(Scalar::from(3))],
        )
        .0
        .unwrap()
        .remove(0);
        assert_value(&second, &expected);
        let next = one(
            backend(Policy::default()),
            fold_binding(msb),
            &[],
            vec![first, Value::Field(Scalar::from(2))],
        )
        .0
        .unwrap()
        .remove(0);
        assert_value(&next, &table(msb, &[293, 399]));
        assert_value(&alias, &table(msb, &[2, 5, 11, 19, 31, 47, 71, 101]));
    }
}

#[test]
fn fold_limits_leave_no_published_result_or_changed_alias() {
    for workers in [1, 4] {
        let cpu = zkc_native::CpuExecution::new(workers).unwrap();
        let retained = 4 * size_of::<Scalar>() + 256;
        let managed = 4 * size_of::<Scalar>() + retained;
        for msb in [false, true] {
            let input = table(msb, &[2, 5, 11, 19, 31, 47, 71, 101]);
            for (policy, available, error) in [
                (
                    Policy {
                        max_numerical_work: 8 * 4,
                        ..Policy::default()
                    },
                    retained,
                    Some("exhausted:numerical-work"),
                ),
                (
                    Policy {
                        max_numerical_work: 8 * 4 + 1,
                        ..Policy::default()
                    },
                    retained,
                    None,
                ),
                (
                    Policy {
                        max_numerical_bytes: managed - 1,
                        ..Policy::default()
                    },
                    retained,
                    Some("exhausted:numerical-bytes"),
                ),
                (
                    Policy {
                        max_numerical_bytes: managed,
                        ..Policy::default()
                    },
                    retained,
                    None,
                ),
                (
                    Policy::default(),
                    retained - 1,
                    Some("exhausted:output-bytes"),
                ),
            ] {
                let mut driver = Controlled::new(backend(policy).with_cpu(cpu.clone()).unwrap());
                driver.output_limit = Some(available);
                let (result, driver) = one(
                    driver,
                    fold_binding(msb),
                    &[],
                    vec![input.clone(), Value::Field(Scalar::from(3))],
                );
                if let Some(error) = error {
                    assert_eq!(result.unwrap_err(), error);
                    assert!(driver.outputs.is_empty());
                } else {
                    assert_value(&result.unwrap()[0], &table(msb, &[89, 131, 191, 265]));
                    assert_eq!(driver.outputs.len(), 1);
                }
                assert_eq!(driver.inner.active_frames(), 0);
                assert_value(&input, &table(msb, &[2, 5, 11, 19, 31, 47, 71, 101]));
            }
        }
    }
}

#[test]
fn constant_fold_keeps_output_capacity_before_positive_arity_refusal() {
    for msb in [false, true] {
        for (available, error) in [
            (255, "exhausted:output-bytes"),
            (256, "refused:positive-arity-required"),
        ] {
            let mut driver = Controlled::new(backend(Policy {
                max_numerical_work: 0,
                max_numerical_bytes: 0,
                ..Policy::default()
            }));
            driver.output_limit = Some(available);
            let (result, driver) = one(
                driver,
                fold_binding(msb),
                &[],
                vec![table(msb, &[7]), Value::Field(Scalar::from(3))],
            );
            assert_eq!(result.unwrap_err(), error);
            assert!(driver.outputs.is_empty());
            assert_eq!(driver.inner.active_frames(), 0);
        }
    }
}

#[test]
fn table_destinations_and_physical_constructors_check_before_writing() {
    let bounds = Policy::default().ark_bounds();
    let lsb = zkc_kernels::arkworks::bls12_381::Table::from_physical_vec(
        vec![2u64, 11, 5, 19]
            .into_iter()
            .map(Scalar::from)
            .collect(),
        &bounds,
    )
    .unwrap();
    let msb = zkc_kernels::arkworks::bls12_381::MsbTable::from_physical_vec(
        vec![2u64, 5, 11, 19]
            .into_iter()
            .map(Scalar::from)
            .collect(),
        &bounds,
    )
    .unwrap();
    assert_eq!(lsb.logical_values().unwrap(), msb.logical_values());
    let mut destination = [Scalar::from(97); 3];
    assert_eq!(
        lsb.restrict_first_into(Scalar::from(3), &mut destination),
        Err(zkc_kernels::arkworks::Error::InvalidTableLength)
    );
    assert_eq!(destination, [Scalar::from(97); 3]);
    assert_eq!(
        msb.restrict_first_into(Scalar::from(3), &mut destination),
        Err(zkc_kernels::arkworks::Error::InvalidTableLength)
    );
    assert_eq!(destination, [Scalar::from(97); 3]);
    for values in [vec![], vec![Scalar::from(1); 3]] {
        assert_eq!(
            zkc_kernels::arkworks::bls12_381::Table::from_physical_vec(values.clone(), &bounds)
                .unwrap_err(),
            zkc_kernels::arkworks::Error::InvalidTableLength
        );
        assert_eq!(
            zkc_kernels::arkworks::bls12_381::MsbTable::from_physical_vec(values, &bounds)
                .unwrap_err(),
            zkc_kernels::arkworks::Error::InvalidTableLength
        );
    }
    let tiny = Policy {
        max_arity: 0,
        ..Policy::default()
    }
    .ark_bounds();
    assert_eq!(
        zkc_kernels::arkworks::bls12_381::Table::from_physical_vec(vec![Scalar::from(1); 2], &tiny)
            .unwrap_err(),
        zkc_kernels::arkworks::Error::ArityLimit
    );
    assert_eq!(
        zkc_kernels::arkworks::bls12_381::MsbTable::from_physical_vec(
            vec![Scalar::from(1); 2],
            &tiny
        )
        .unwrap_err(),
        zkc_kernels::arkworks::Error::ArityLimit
    );
}

fn quotient_binding(field: Identity) -> OperationBinding {
    OperationBinding {
        contract: "poly.opening_quotient".into(),
        arguments: vec![field.name().into()],
        implementation: "plonky3/poly.opening_quotient".into(),
        physical_arguments: vec![],
    }
}

fn sample<E: zkc_kernels::plonky3::residue::Residue<Base = KoalaBear>>(seed: usize) -> E {
    E::from_basis_coefficients_fn(|coordinate| {
        KoalaBear::new((seed * seed + 11 * seed + 7 * coordinate + 1) as u32)
    })
}

fn domain_points_checks<E: zkc_kernels::plonky3::residue::Residue<Base = KoalaBear>>(
    identity: Identity,
    field: fn(E) -> Value,
) {
    let binding = |name: &str| OperationBinding {
        contract: name.into(),
        arguments: vec![identity.name().into()],
        implementation: format!("plonky3/{name}"),
        physical_arguments: vec![],
    };
    let (scalar_tag, vector_tag) = match identity {
        Identity::KoalaBear => (19, 20),
        Identity::KoalaBearExt4 => (21, 22),
        Identity::KoalaBearExt8 => (26, 27),
        _ => unreachable!(),
    };
    // Independent integer arithmetic in each canonical basis coordinate. The
    // root convention is specified in docs/spec/domains/polynomials.md.
    const MODULUS: u64 = 2_130_706_433;
    let shift_coordinates: Vec<_> = (0..E::DIMENSION)
        .map(|i| MODULUS - 17 - 31 * i as u64)
        .collect();
    let shift = E::from_basis_coefficients_fn(|i| KoalaBear::new(shift_coordinates[i] as u32));
    let scalar_bytes = |coordinates: &[u64]| {
        let mut bytes = b"ZKCV\0".to_vec();
        bytes.push(scalar_tag);
        for coordinate in coordinates {
            bytes.extend_from_slice(&(*coordinate as u32).to_le_bytes());
        }
        bytes
    };
    let codec = backend(Policy::default());
    for n in [1usize, 2, 8, 32] {
        let mut root = 1_791_270_792u64;
        for _ in n.trailing_zeros()..24 {
            root = root * root % MODULUS;
        }
        let mut root_coordinates = vec![0; E::DIMENSION];
        root_coordinates[0] = root;
        let result = one(
            backend(Policy::default()),
            binding("poly.domain_root"),
            &[],
            vec![Value::Index(n as u64)],
        )
        .0
        .unwrap();
        assert_eq!(
            codec.encode_native_value(&result[0]).unwrap(),
            scalar_bytes(&root_coordinates)
        );

        let result = one(
            backend(Policy::default()),
            binding("poly.domain_points"),
            &[],
            vec![field(shift), Value::Index(n as u64)],
        )
        .0
        .unwrap();
        let mut expected = b"ZKCV\0".to_vec();
        expected.push(vector_tag);
        expected.extend_from_slice(&(n as u32).to_le_bytes());
        let mut coordinates = shift_coordinates.clone();
        for i in 0..n {
            let point = one(
                backend(Policy::default()),
                binding("poly.domain_point"),
                &[],
                vec![field(shift), Value::Index(n as u64), Value::Index(i as u64)],
            )
            .0
            .unwrap();
            let bytes = scalar_bytes(&coordinates);
            assert_eq!(codec.encode_native_value(&point[0]).unwrap(), bytes);
            expected.extend_from_slice(&bytes[6..]);
            for coordinate in &mut coordinates {
                *coordinate = *coordinate * root % MODULUS;
            }
        }
        assert_eq!(coordinates, shift_coordinates);
        assert_eq!(codec.encode_native_value(&result[0]).unwrap(), expected);
    }

    let retained = 8 * size_of::<E>() + 256;
    // This installed operation uses output/allocation preflight, rather than
    // the managed numerical Call budget. Pin its existing exact allowances.
    for (n, shift, max_elements, max_bytes, available, error) in [
        (8, shift, 8, 8 * retained, retained, None),
        (
            8,
            shift,
            8,
            8 * retained,
            retained - 1,
            Some("exhausted:output-bytes"),
        ),
        (
            8,
            shift,
            8,
            8 * retained - 1,
            retained,
            Some("exhausted:output-bytes"),
        ),
        (0, E::ZERO, 8, 8 * retained, 0, Some("refused:coset-size")),
        (3, E::ZERO, 8, 8 * retained, 0, Some("refused:coset-size")),
        (
            1 << 25,
            E::ZERO,
            8,
            8 * retained,
            0,
            Some("refused:coset-size"),
        ),
        (
            16,
            E::ZERO,
            8,
            8 * retained,
            0,
            Some("refused:coset-element-limit"),
        ),
        (
            8,
            E::ZERO,
            8,
            8 * retained,
            0,
            Some("refused:coset-zero-shift"),
        ),
    ] {
        let mut driver = Controlled::new(backend(Policy {
            max_table_elements: max_elements,
            max_value_bytes: max_bytes,
            max_numerical_work: 0,
            max_numerical_bytes: 0,
            ..Policy::default()
        }));
        driver.output_limit = Some(available);
        let (result, driver) = one(
            driver,
            binding("poly.domain_points"),
            &[],
            vec![field(shift), Value::Index(n)],
        );
        if let Some(error) = error {
            assert_eq!(result.unwrap_err(), error);
            assert!(driver.outputs.is_empty());
        } else {
            assert_eq!(result.unwrap().len(), 1);
            assert_eq!(driver.outputs.len(), 1);
        }
        assert_eq!(driver.inner.active_frames(), 0);
    }
}

#[test]
fn base_installed_domain_points_and_allowances() {
    domain_points_checks::<KoalaBear>(Identity::KoalaBear, Value::KoalaBearField);
}

#[test]
fn quartic_installed_domain_points_and_allowances() {
    domain_points_checks::<KoalaBearExt4>(Identity::KoalaBearExt4, Value::KoalaBearExt4Field);
}

#[test]
fn octic_installed_domain_points_and_allowances() {
    domain_points_checks::<KoalaBearExt8>(Identity::KoalaBearExt8, Value::KoalaBearExt8Field);
}

fn quotient_checks<E: zkc_kernels::plonky3::residue::Residue<Base = KoalaBear>>(
    identity: Identity,
    field: fn(E) -> Value,
    vector: fn(Vec<E>) -> Value,
) {
    for n in [1usize, 2, 8, 16] {
        let values: Vec<E> = (0..n).map(|i| sample(5 + i)).collect();
        let input = vector(values.clone());
        let shift = sample::<E>(3);
        let root = E::from(KoalaBear::two_adic_generator(n.trailing_zeros() as usize));
        let claim = sample::<E>(17);
        for point in [E::ZERO, sample::<E>(29)] {
            // Independent per-element division, with nonbase coordinates in
            // every extension input. No batch inversion or quotient helper.
            let expected: Vec<_> = values
                .iter()
                .enumerate()
                .map(|(i, evaluation)| {
                    let x = shift * root.exp_u64(i as u64);
                    assert_ne!(x, point);
                    (*evaluation - claim) / (x - point)
                })
                .collect();
            let result = one(
                backend(Policy::default()),
                quotient_binding(identity),
                &[],
                vec![input.clone(), field(shift), field(point), field(claim)],
            )
            .0
            .unwrap();
            assert_value(&result[0], &vector(expected.clone()));
            let domain = zkc_kernels::plonky3::polynomial::Domain::new(n, shift, n).unwrap();
            assert_eq!(
                zkc_kernels::plonky3::polynomial::opening_quotient(&values, domain, point, claim)
                    .unwrap(),
                expected
            );
            assert_value(&input, &vector(values.clone()));
        }
    }

    let values: Vec<E> = (0..8).map(|i| sample(5 + i)).collect();
    let input = vector(values.clone());
    let shift = sample::<E>(3);
    let retained = values.len() * size_of::<E>() + 256;
    // One output staging payload, its conservative final representation, and
    // simultaneously live denominator scratch must all fit before allocation.
    let managed = 2 * values.len() * size_of::<E>() + retained;
    for (policy, available, point, error) in [
        (
            Policy {
                max_numerical_work: 16 * 8 + 4096 - 1,
                ..Policy::default()
            },
            retained,
            E::ZERO,
            Some("exhausted:numerical-work"),
        ),
        (
            Policy {
                max_numerical_work: 16 * 8 + 4096,
                ..Policy::default()
            },
            retained,
            E::ZERO,
            None,
        ),
        (
            Policy {
                max_numerical_bytes: managed - 1,
                ..Policy::default()
            },
            retained,
            E::ZERO,
            Some("exhausted:numerical-bytes"),
        ),
        (
            Policy {
                max_numerical_bytes: managed,
                ..Policy::default()
            },
            retained,
            E::ZERO,
            None,
        ),
        (
            Policy::default(),
            retained - 1,
            E::ZERO,
            Some("exhausted:output-bytes"),
        ),
        (
            Policy {
                max_value_bytes: 8 * retained - 1,
                max_numerical_work: 0,
                max_numerical_bytes: 0,
                ..Policy::default()
            },
            retained,
            E::ZERO,
            Some("exhausted:output-bytes"),
        ),
        (
            Policy::default(),
            retained,
            shift,
            Some("refused:coset-opening-point"),
        ),
        (
            Policy {
                max_numerical_work: 0,
                max_numerical_bytes: 0,
                ..Policy::default()
            },
            retained,
            shift,
            Some("refused:coset-opening-point"),
        ),
        (
            Policy {
                max_numerical_bytes: 0,
                ..Policy::default()
            },
            retained,
            shift,
            Some("refused:coset-opening-point"),
        ),
        (
            Policy {
                max_numerical_work: 0,
                max_numerical_bytes: 0,
                ..Policy::default()
            },
            retained - 1,
            shift,
            Some("exhausted:output-bytes"),
        ),
    ] {
        let mut driver = Controlled::new(backend(policy));
        driver.output_limit = Some(available);
        let (result, driver) = one(
            driver,
            quotient_binding(identity),
            &[],
            vec![input.clone(), field(shift), field(point), field(sample(17))],
        );
        if let Some(error) = error {
            assert_eq!(result.unwrap_err(), error);
            assert!(driver.outputs.is_empty());
        } else {
            assert_eq!(result.unwrap().len(), 1);
            assert_eq!(driver.outputs.len(), 1);
        }
        assert_eq!(driver.inner.active_frames(), 0);
        assert_value(&input, &vector(values.clone()));
    }
    for (evaluations, shift, error) in [
        (vec![E::ONE; 3], E::ONE, "refused:coset-size"),
        (vec![E::ONE; 8], E::ZERO, "refused:coset-zero-shift"),
    ] {
        let (result, driver) = one(
            Controlled::new(backend(Policy {
                max_numerical_work: 0,
                max_numerical_bytes: 0,
                ..Policy::default()
            })),
            quotient_binding(identity),
            &[],
            vec![
                vector(evaluations),
                field(shift),
                field(E::ZERO),
                field(E::ZERO),
            ],
        );
        assert_eq!(result.unwrap_err(), error);
        assert!(driver.outputs.is_empty());
    }
}

#[test]
fn base_quotient_reference_and_call_limits() {
    quotient_checks::<KoalaBear>(Identity::KoalaBear, Value::KoalaBearField, |values| {
        Value::KoalaBearVector(values.into())
    });
}

#[test]
fn quartic_quotient_reference_and_call_limits() {
    quotient_checks::<KoalaBearExt4>(
        Identity::KoalaBearExt4,
        Value::KoalaBearExt4Field,
        |values| Value::KoalaBearExt4Vector(values.into()),
    );
}

#[test]
fn octic_quotient_reference_and_call_limits() {
    quotient_checks::<KoalaBearExt8>(
        Identity::KoalaBearExt8,
        Value::KoalaBearExt8Field,
        |values| Value::KoalaBearExt8Vector(values.into()),
    );
}
