use super::*;

fn args(values: Vec<F>, columns: u64, height: u64, size: u64) -> Vec<Value> {
    vec![
        Value::Bn254Vector(values.into()),
        Value::Index(columns),
        Value::Index(height),
        Value::Bn254Field(F::from(7)),
        Value::Index(size),
    ]
}

fn run(args: &[Value], policy: &Policy, available: usize) -> Result<Vec<Value>> {
    execute("poly.coset_evaluate_batch", args, available, policy)
}

fn vector(value: &Value) -> &[F] {
    let Value::Bn254Vector(values) = value else {
        panic!("expected BN254 vector")
    };
    values
}

#[test]
fn coefficient_batches_match_pinned_fft_and_scalar_horner() {
    let policy = Policy::default();
    for columns in [1, 3, 16] {
        for (height, size) in [(0, 1), (0, 8), (1, 1), (1, 8), (3, 8), (8, 8), (5, 2)] {
            let domain = domain(size, F::from(7), &policy).unwrap();
            let mut coefficients = Vec::new();
            let mut expected = Vec::new();
            for column in 0..columns {
                let block: Vec<_> = (0..height)
                    .map(|row| {
                        if row >= size || (column == 0 && columns > 1) {
                            F::zero()
                        } else {
                            F::from((19 * column + 7 * row * row + 1) as u64)
                        }
                    })
                    .collect();
                let horner: Vec<_> = domain
                    .elements()
                    .map(|x| block.iter().rev().fold(F::zero(), |value, c| value * x + c))
                    .collect();
                // Pinned ark-poly 0.6.0 provider control, using a separate Vec.
                let mut scalar_fft: Vec<_> = block.iter().take(size).copied().collect();
                domain.fft_in_place(&mut scalar_fft);
                assert_eq!(scalar_fft, horner);
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
            let result = run(&args, &policy, usize::MAX).unwrap();
            assert_eq!(vector(&result[0]), expected);
            for alias in &aliases {
                assert_eq!(vector(alias), coefficients);
                if !coefficients.is_empty() {
                    assert_ne!(vector(alias).as_ptr(), vector(&result[0]).as_ptr());
                }
            }
        }
    }
}

#[test]
fn coefficient_batch_allocation_failures_publish_nothing_and_preserve_inputs() {
    let policy = Policy::default();
    let values: Vec<_> = (1u64..=9).map(F::from).collect();
    let arguments = args(values.clone(), 3, 3, 8);
    let aliases = [arguments[0].clone(), arguments[0].clone()];
    // First the private destination, then the reusable FFT scratch vector.
    for successful in [0, 1] {
        let failure = zkc_kernels::allocation::failure::after(successful);
        assert_eq!(
            run(&arguments, &policy, usize::MAX).unwrap_err().code,
            "exhausted:allocation"
        );
        drop(failure);
        for alias in &aliases {
            assert_eq!(vector(alias), values);
        }
        assert!(run(&arguments, &policy, usize::MAX).is_ok());
    }
}

#[test]
fn coefficient_batch_exact_output_workspace_and_work_boundaries() {
    let policy = Policy::default();
    let values: Vec<_> = (1u64..=9).map(F::from).collect();
    let arguments = args(values.clone(), 3, 3, 8);
    let shape = CosetBatchShape::new(9, 3, 3, 8).unwrap();
    let retained = size(24, 32).unwrap();
    let managed = retained + (24 + 8) * std::mem::size_of::<F>();
    let work = shape.coefficient_evaluation_work(1).unwrap();
    let exact = Policy {
        max_numerical_bytes: managed,
        max_numerical_work: work,
        ..policy
    };
    assert!(run(&arguments, &exact, retained).is_ok());
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
            run(&arguments, &policy, available).unwrap_err().code,
            expected
        );
        assert_eq!(vector(&alias), values);
    }
    let arguments = args(vec![], 3, 0, 8);
    let zero_shape = CosetBatchShape::new(0, 3, 0, 8).unwrap();
    let zero_exact = Policy {
        max_numerical_work: zero_shape.coefficient_evaluation_work(1).unwrap(),
        ..exact
    };
    assert_eq!(
        vector(&run(&arguments, &zero_exact, retained).unwrap()[0]),
        vec![F::zero(); 24]
    );
    assert_eq!(
        run(
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
fn coefficient_batch_empty_zero_height_shrink_nominal_and_overflow_refusals() {
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
            run(
                &args(vec![F::zero(); len], columns, height, size),
                &policy,
                usize::MAX
            )
            .unwrap_err()
            .code,
            expected
        );
    }
    let mut empty = args(vec![], 0, u64::MAX, u64::MAX);
    empty[3] = Value::Bn254Field(F::zero());
    let exact_empty = Policy {
        max_numerical_bytes: 256,
        max_numerical_work: 1,
        ..policy
    };
    assert!(vector(&run(&empty, &exact_empty, 256).unwrap()[0]).is_empty());
    assert_eq!(
        run(
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
        run(
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
    let mut zero_height = args(vec![], 3, 0, 8);
    zero_height[3] = Value::Bn254Field(F::zero());
    assert_eq!(
        run(&zero_height, &policy, usize::MAX).unwrap_err().code,
        "refused:coset-zero-shift"
    );
    // The first block fits; any nonzero tail in a later block prevents publication.
    let mut shrinking = vec![F::zero(); 10];
    shrinking[0] = F::one();
    shrinking[9] = F::one();
    let arguments = args(shrinking.clone(), 2, 5, 2);
    let alias = arguments[0].clone();
    assert_eq!(
        run(
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
    assert_eq!(vector(&alias), shrinking);
    let mut nominal = args(vec![], 0, 0, 0);
    nominal[3] = Value::KoalaBearField(crate::KoalaBear::default());
    assert_eq!(
        run(&nominal, &policy, usize::MAX).unwrap_err().code,
        "refused:kernel-operands"
    );
    nominal = args(vec![], 0, 0, 0);
    nominal[0] = Value::KoalaBearVector(Vec::new().into());
    assert_eq!(
        run(&nominal, &policy, usize::MAX).unwrap_err().code,
        "refused:kernel-operands"
    );
}
