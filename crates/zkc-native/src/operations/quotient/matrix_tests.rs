use super::*;

fn prepared_arguments() -> Vec<Value> {
    vec![
        Value::Indices(vec![1, 2, 3, 4, 5, 6, 7, 8].into()),
        Value::Index(17),
        Value::Index(2),
        Value::Index(2),
        Value::Index(2),
        Value::Index(2),
    ]
}

#[test]
fn prepared_matrix_lifetime_and_limits_cover_preparation_and_repeated_calls() {
    use zkc_kernels::polynomial::quotient::rns::Matrix;
    let args = prepared_arguments();
    let policy = Policy::default();
    let matrix = apply("quotient.prepare_matrix", &args, &policy, usize::MAX)
        .unwrap()
        .remove(0);
    let shared = matrix.validation_backing();
    assert!(shared.is_some());
    assert_eq!(shared, matrix.clone().validation_backing());
    assert!(!crate::has_native_wire(&matrix.physical_type()));
    let calls = [matrix.clone(), Value::Indices(vec![1, 16, 2, 15].into())];
    for _ in 0..3 {
        let out = apply("quotient.matvec", &calls, &policy, usize::MAX).unwrap();
        assert!(matches!(&out[0],Value::Indices(xs) if xs.as_ref()==[0,3,7,3]));
    }
    assert!(matches!(&args[0],Value::Indices(xs) if xs.as_ref()==[1,2,3,4,5,6,7,8]));
    for (operation, inputs) in [
        ("quotient.prepare_matrix", args.clone()),
        ("quotient.matvec", calls.to_vec()),
    ] {
        for (p, available, expected) in [
            (
                Policy {
                    max_numerical_work: 0,
                    ..policy
                },
                usize::MAX,
                "numerical-work",
            ),
            (
                Policy {
                    max_numerical_bytes: 0,
                    ..policy
                },
                usize::MAX,
                "numerical-bytes",
            ),
            (policy, 0, "output-bytes"),
        ] {
            assert_eq!(
                apply(operation, &inputs, &p, available).unwrap_err(),
                exhausted(expected)
            );
        }
        for allocations in 0..2 {
            let _failure = zkc_kernels::allocation::failure::after(allocations);
            assert_eq!(
                apply(operation, &inputs, &policy, usize::MAX).unwrap_err(),
                exhausted("allocation")
            );
        }
    }
    let input = [1, 2, 3, 4, 5, 6, 7, 8];
    let plan = Matrix::new(&input, 17, 2, 2, 2, 2).unwrap();
    let retained = crate::value::quotient_matrix_bytes(plan.storage_elements()).unwrap();
    let work = Matrix::admission_work(input.len()).unwrap() + plan.work().unwrap();
    let exact = Policy {
        max_numerical_work: work,
        max_numerical_bytes: retained + plan.scratch_elements() * 8,
        ..policy
    };
    assert!(apply("quotient.prepare_matrix", &args, &exact, retained).is_ok());
    assert_eq!(
        apply(
            "quotient.prepare_matrix",
            &args,
            &Policy {
                max_numerical_work: work - 1,
                ..exact
            },
            retained
        )
        .unwrap_err(),
        exhausted("numerical-work")
    );
    assert_eq!(
        apply(
            "quotient.prepare_matrix",
            &args,
            &Policy {
                max_numerical_bytes: exact.max_numerical_bytes - 1,
                ..exact
            },
            retained
        )
        .unwrap_err(),
        exhausted("numerical-bytes")
    );
    assert_eq!(
        apply("quotient.prepare_matrix", &args, &exact, retained - 1).unwrap_err(),
        exhausted("output-bytes")
    );
}

#[test]
fn prepared_matrix_admission_checks_actual_signed_digits() {
    let matrix = apply(
        "quotient.prepare_matrix",
        &prepared_arguments(),
        &Policy::default(),
        usize::MAX,
    )
    .unwrap()
    .remove(0);
    for (input, code) in [
        (vec![0; 3], "quotient-shape"),
        (vec![17; 4], "quotient-residue"),
        (vec![3; 4], "quotient-digit-bound"),
        (vec![14; 4], "quotient-digit-bound"),
    ] {
        assert_eq!(
            apply(
                "quotient.matvec",
                &[matrix.clone(), Value::Indices(input.into())],
                &Policy::default(),
                usize::MAX
            )
            .unwrap_err(),
            refused(code)
        );
    }
    assert_eq!(
        apply(
            "quotient.matvec",
            &[
                Value::Indices(vec![0; 8].into()),
                Value::Indices(vec![0; 4].into())
            ],
            &Policy::default(),
            usize::MAX
        )
        .unwrap_err(),
        refused("quotient-operands")
    );
}

#[test]
fn product_work_and_peak_storage_have_exact_boundaries() {
    let matrix = run("quotient.prepare_matrix", &prepared_arguments())
        .unwrap()
        .remove(0);
    let Value::QuotientMatrix(plan) = &matrix else {
        unreachable!()
    };
    let work = plan.work().unwrap() + plan.input_elements() as u64 * 4;
    let retained = size(plan.output_elements(), 8).unwrap();
    let peak = retained + plan.scratch_elements().unwrap() * 8;
    let args = [matrix.clone(), Value::Indices(vec![1, 16, 2, 15].into())];
    let exact = Policy {
        max_numerical_work: work,
        max_numerical_bytes: peak,
        ..Policy::default()
    };
    assert!(apply("quotient.matvec", &args, &exact, retained).is_ok());
    for (policy, available, code) in [
        (
            Policy {
                max_numerical_work: work - 1,
                ..exact
            },
            retained,
            "numerical-work",
        ),
        (
            Policy {
                max_numerical_bytes: peak - 1,
                ..exact
            },
            retained,
            "numerical-bytes",
        ),
        (exact, retained - 1, "output-bytes"),
        (
            Policy {
                max_table_elements: 4,
                ..exact
            },
            retained,
            "element-limit",
        ),
    ] {
        assert_eq!(
            apply("quotient.matvec", &args, &policy, available).unwrap_err(),
            exhausted(code)
        );
    }
    assert!(matches!(&args[1], Value::Indices(xs) if xs.as_ref() == [1,16,2,15]));
}

#[test]
fn reached_work_precedes_scan_refusal_and_checks_every_new_input() {
    let mut args = prepared_arguments();
    args[0] = Value::Indices(vec![17; 8].into());
    let no_work = Policy {
        max_numerical_work: 0,
        ..Policy::default()
    };
    assert_eq!(
        apply("quotient.prepare_matrix", &args, &no_work, usize::MAX).unwrap_err(),
        exhausted("numerical-work")
    );
    assert_eq!(
        run("quotient.prepare_matrix", &args).unwrap_err(),
        refused("quotient-residue")
    );
    let matrix = run("quotient.prepare_matrix", &prepared_arguments())
        .unwrap()
        .remove(0);
    for digit in [1, 3, 16, 14, 0, 17] {
        let args = [matrix.clone(), Value::Indices(vec![digit; 4].into())];
        assert_eq!(
            apply("quotient.matvec", &args, &no_work, usize::MAX).unwrap_err(),
            exhausted("numerical-work")
        );
        let result = run("quotient.matvec", &args);
        match digit {
            3 | 14 => assert_eq!(result.unwrap_err(), refused("quotient-digit-bound")),
            17 => assert_eq!(result.unwrap_err(), refused("quotient-residue")),
            _ => {
                result.unwrap();
            }
        }
    }
}

#[test]
fn prepared_retention_counts_spare_capacity_and_actual_shared_identity() {
    use std::sync::Arc;
    use zkc_kernels::polynomial::quotient::rns::{Matrix, PreparedMatrix};
    let make = || {
        let matrix = Matrix::new(&[1, 2, 3, 4], 17, 2, 1, 2, 1).unwrap();
        let mut storage = Vec::with_capacity(matrix.storage_elements() + 19);
        storage.resize(matrix.storage_elements(), 0);
        Value::QuotientMatrix(Arc::new(matrix.prepare(storage, &mut [0; 2]).unwrap()))
    };
    let value = make();
    let Value::QuotientMatrix(matrix) = &value else {
        unreachable!()
    };
    assert_eq!(
        value.retained_bytes(),
        256 + std::mem::size_of::<PreparedMatrix>()
            + std::mem::size_of::<Value>()
            + matrix.storage_capacity() * 8
    );
    assert_eq!(
        value.validation_backing(),
        value.clone().validation_backing()
    );
    assert_ne!(value.validation_backing(), make().validation_backing());
}

fn run(name: &str, args: &[Value]) -> Result<Vec<Value>> {
    apply(name, args, &Policy::default(), usize::MAX)
}
