use super::*;
use p3_field::PrimeCharacteristicRing;

fn sample<E: Family>(seed: usize) -> E {
    E::from_basis_coefficients_fn(|coordinate| {
        KoalaBear::from_usize(seed * seed + 7 * seed + 11 * coordinate + 1)
    })
}

fn args<E: Family>(values: Vec<E>, columns: u64, height: u64, size: u64) -> Vec<Value> {
    vec![
        E::vector_value(values),
        Value::Index(columns),
        Value::Index(height),
        E::field_value(sample::<E>(3)),
        Value::Index(size),
    ]
}

fn run<E: Family>(args: &[Value], policy: &Policy, available: usize) -> Result<Vec<Value>> {
    execute::<E>(
        "poly.coset_evaluate_batch",
        args,
        policy,
        available,
        &Kernels::default(),
    )
}

fn provider_and_horner_checks<E: Family>() {
    let policy = Policy::default();
    for columns in [1, 3, 16] {
        for (height, size) in [(0, 1), (0, 8), (1, 1), (1, 8), (3, 8), (8, 8), (5, 2)] {
            let shift = sample::<E>(3);
            let domain = Domain::new(size, shift, 32).unwrap();
            let mut coefficients = Vec::new();
            let mut expected = Vec::new();
            for column in 0..columns {
                let block: Vec<_> = (0..height)
                    .map(|row| {
                        if row >= size || (column == 0 && columns > 1) {
                            E::ZERO
                        } else {
                            sample::<E>(19 * column + row + 1)
                        }
                    })
                    .collect();
                let fitting: Vec<_> = block.iter().take(size).copied().collect();
                let horner: Vec<_> = (0..size)
                    .map(|row| polynomial::evaluate_at(&block, domain.point(row).unwrap()))
                    .collect();
                // Pinned p3-dft 0.8.0 scalar DFT is separate from the batch path.
                assert_eq!(
                    Kernels::default().evaluate(&fitting, domain).unwrap(),
                    horner
                );
                expected.extend(horner);
                coefficients.extend(block);
            }
            let args = args(
                coefficients.clone(),
                columns as u64,
                height as u64,
                size as u64,
            );
            let aliases = [args[0].clone(), args[0].clone()];
            let result = run::<E>(&args, &policy, usize::MAX).unwrap();
            assert_eq!(E::vector(&result[0]).unwrap(), expected);
            for alias in &aliases {
                assert_eq!(E::vector(alias).unwrap(), coefficients);
                if !coefficients.is_empty() {
                    assert_ne!(
                        E::vector(alias).unwrap().as_ptr(),
                        E::vector(&result[0]).unwrap().as_ptr()
                    );
                }
            }
        }
    }
}

#[test]
fn coefficient_batches_match_pinned_dft_and_horner_in_every_coordinate() {
    provider_and_horner_checks::<KoalaBear>();
    provider_and_horner_checks::<KoalaBearExt4>();
    provider_and_horner_checks::<KoalaBearExt8>();
}

fn allocation_failure_checks<E: Family>() {
    let policy = Policy::default();
    let values: Vec<_> = (0..9).map(sample::<E>).collect();
    let arguments = args(values.clone(), 3, 3, 8);
    let aliases = [arguments[0].clone(), arguments[0].clone()];
    // First the private destination, then the adapter's transform matrix.
    for successful in [0, 1] {
        let failure = zkc_kernels::allocation::failure::after(successful);
        assert_eq!(
            run::<E>(&arguments, &policy, usize::MAX).unwrap_err().code,
            "exhausted:allocation"
        );
        drop(failure);
        for alias in &aliases {
            assert_eq!(E::vector(alias).unwrap(), values);
        }
        assert!(run::<E>(&arguments, &policy, usize::MAX).is_ok());
    }
    // The lower adapter also leaves its caller's destination untouched when
    // the mandatory matrix reservation fails, before any transform work.
    let mut destination = vec![sample::<E>(99); 24];
    let before = destination.clone();
    let failure = zkc_kernels::allocation::failure::after(0);
    assert_eq!(
        CoefficientBatch::new(&values, 3, 3, Domain::new(8, sample::<E>(3), 32).unwrap())
            .unwrap()
            .write_into(&Kernels::default(), &mut destination),
        Err(polynomial::Error::Allocation)
    );
    drop(failure);
    assert_eq!(destination, before);
}

#[test]
fn coefficient_batch_allocation_failures_publish_nothing_and_preserve_inputs() {
    allocation_failure_checks::<KoalaBear>();
    allocation_failure_checks::<KoalaBearExt4>();
    allocation_failure_checks::<KoalaBearExt8>();
}

fn boundary_checks<E: Family>() {
    let policy = Policy::default();
    let values: Vec<_> = (0..9).map(sample::<E>).collect();
    let arguments = args(values.clone(), 3, 3, 8);
    let shape = CosetBatchShape::new(9, 3, 3, 8).unwrap();
    let element = std::mem::size_of::<E>();
    let retained = size(24, element).unwrap();
    let managed = retained + 48 * element;
    let work = shape.coefficient_evaluation_work(E::DIMENSION).unwrap();
    let exact = Policy {
        max_numerical_bytes: managed,
        max_numerical_work: work,
        ..policy
    };
    assert!(run::<E>(&arguments, &exact, retained).is_ok());
    for (policy, available, expected) in [
        (
            Policy {
                max_numerical_work: work - 1,
                ..exact
            },
            retained,
            "exhausted:numerical-work",
        ),
        (
            Policy {
                max_numerical_bytes: managed - 1,
                ..exact
            },
            retained,
            "exhausted:numerical-bytes",
        ),
        (
            Policy {
                max_numerical_work: 0,
                ..exact
            },
            retained - 1,
            "exhausted:output-bytes",
        ),
        (
            Policy {
                max_value_bytes: retained - 1,
                ..exact
            },
            retained,
            "exhausted:output-bytes",
        ),
        (
            Policy {
                max_table_elements: 7,
                ..exact
            },
            retained,
            "refused:coset-element-limit",
        ),
        (
            Policy {
                max_table_elements: 16,
                ..exact
            },
            retained,
            "exhausted:element-limit",
        ),
    ] {
        let alias = arguments[0].clone();
        assert_eq!(
            run::<E>(&arguments, &policy, available).unwrap_err().code,
            expected
        );
        assert_eq!(E::vector(&alias).unwrap(), values);
    }
    // Zero coefficient height still has real output, workspace and work bounds.
    let arguments = args::<E>(vec![], 3, 0, 8);
    let zero_shape = CosetBatchShape::new(0, 3, 0, 8).unwrap();
    let zero_exact = Policy {
        max_numerical_work: zero_shape
            .coefficient_evaluation_work(E::DIMENSION)
            .unwrap(),
        ..exact
    };
    assert_eq!(
        E::vector(&run::<E>(&arguments, &zero_exact, retained).unwrap()[0]).unwrap(),
        vec![E::ZERO; 24]
    );
    assert_eq!(
        run::<E>(
            &arguments,
            &Policy {
                max_numerical_bytes: managed - 1,
                ..zero_exact
            },
            retained
        )
        .unwrap_err()
        .code,
        "exhausted:numerical-bytes"
    );
}

#[test]
fn coefficient_batch_exact_output_workspace_and_work_boundaries() {
    boundary_checks::<KoalaBear>();
    boundary_checks::<KoalaBearExt4>();
    boundary_checks::<KoalaBearExt8>();
}

fn refusal_checks<E: Family>() {
    let policy = Policy::default();
    for (len, columns, height, size, expected) in [
        (1, 0, 0, 0, "refused:coset-batch-shape"),
        (5, 2, 3, 8, "refused:coset-batch-shape"),
        (7, 2, 3, 8, "refused:coset-batch-shape"),
        (0, u64::MAX, 2, 2, "exhausted:size-overflow"),
        (0, u64::MAX, 0, 2, "exhausted:size-overflow"),
        (0, 3, 0, 0, "refused:coset-size"),
        (0, 3, 0, 3, "refused:coset-size"),
    ] {
        assert_eq!(
            run::<E>(
                &args(vec![E::ZERO; len], columns, height, size),
                &policy,
                usize::MAX
            )
            .unwrap_err()
            .code,
            expected
        );
    }
    let mut empty = args::<E>(vec![], 0, u64::MAX, u64::MAX);
    empty[3] = E::field_value(E::ZERO);
    let exact_empty = Policy {
        max_numerical_bytes: 256,
        max_numerical_work: 1,
        ..policy
    };
    assert!(
        E::vector(&run::<E>(&empty, &exact_empty, 256).unwrap()[0])
            .unwrap()
            .is_empty()
    );
    assert_eq!(
        run::<E>(
            &empty,
            &Policy {
                max_numerical_work: 0,
                ..exact_empty
            },
            256
        )
        .unwrap_err()
        .code,
        "exhausted:numerical-work"
    );
    assert_eq!(
        run::<E>(
            &empty,
            &Policy {
                max_numerical_bytes: 255,
                ..exact_empty
            },
            256
        )
        .unwrap_err()
        .code,
        "exhausted:numerical-bytes"
    );
    let mut zero_height = args::<E>(vec![], 3, 0, 8);
    zero_height[3] = E::field_value(E::ZERO);
    assert_eq!(
        run::<E>(&zero_height, &policy, usize::MAX)
            .unwrap_err()
            .code,
        "refused:coset-zero-shift"
    );
    // A later column's extension-only high coefficient refuses the whole batch.
    let mut shrinking = vec![E::ZERO; 10];
    shrinking[0] = E::ONE;
    if E::DIMENSION > 1 {
        shrinking[9] = E::from_basis_coefficients_fn(|j| {
            if j == E::DIMENSION - 1 {
                KoalaBear::ONE
            } else {
                KoalaBear::ZERO
            }
        });
    } else {
        shrinking[9] = E::ONE;
    }
    let arguments = args(shrinking.clone(), 2, 5, 2);
    let alias = arguments[0].clone();
    // Native output admission still precedes mathematical tail validation;
    // the checked kernel borrow is constructed before numerical work admission.
    assert_eq!(
        run::<E>(&arguments, &policy, 0).unwrap_err().code,
        "exhausted:output-bytes"
    );
    assert_eq!(
        run::<E>(
            &arguments,
            &Policy {
                max_numerical_work: 0,
                ..policy
            },
            usize::MAX
        )
        .unwrap_err()
        .code,
        "refused:coset-coefficient-count"
    );
    assert_eq!(E::vector(&alias).unwrap(), shrinking);
    let mut nominal = args::<E>(vec![], 0, 0, 0);
    nominal[3] = Value::Bn254Field(crate::Bn254Scalar::from(1));
    assert_eq!(
        run::<E>(&nominal, &policy, usize::MAX).unwrap_err().code,
        "refused:kernel-operands"
    );
    nominal = args::<E>(vec![], 0, 0, 0);
    nominal[0] = Value::Bn254Vector(Vec::new().into());
    assert_eq!(
        run::<E>(&nominal, &policy, usize::MAX).unwrap_err().code,
        "refused:kernel-operands"
    );
}

#[test]
fn coefficient_batch_empty_zero_height_shrink_nominal_and_overflow_refusals() {
    refusal_checks::<KoalaBear>();
    refusal_checks::<KoalaBearExt4>();
    refusal_checks::<KoalaBearExt8>();
}
