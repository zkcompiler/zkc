use super::*;

fn arguments(a: &[u64], b: &[u64], q: u64) -> Vec<Value> {
    vec![
        Value::Indices(a.into()),
        Value::Indices(b.into()),
        Value::Index(q),
    ]
}

#[test]
fn operations_preserve_aliases_and_canonical_output() {
    let a = Value::Indices(vec![1, 1].into());
    let args = [a.clone(), a.clone(), Value::Index(17)];
    for (name, expected) in [("add", [2, 2]), ("subtract", [0, 0]), ("multiply", [0, 2])] {
        let result = apply(
            &format!("quotient.{name}"),
            &args,
            &Policy::default(),
            usize::MAX,
        )
        .unwrap();
        assert!(matches!(&result[0], Value::Indices(xs) if xs.as_ref() == expected));
        assert!(matches!(&a, Value::Indices(xs) if xs.as_ref() == [1, 1]));
    }
    let full = arguments(&[u64::MAX - 1], &[u64::MAX - 1], u64::MAX);
    assert!(
        matches!(&apply("quotient.multiply", &full, &Policy::default(), usize::MAX).unwrap()[0], Value::Indices(xs) if xs.as_ref() == [1])
    );
}

#[test]
fn refusals_precede_output_publication() {
    for (a, b, q, code) in [
        (&[0][..], &[0][..], 0, "quotient-modulus"),
        (&[0][..], &[0][..], 1, "quotient-modulus"),
        (&[][..], &[][..], 17, "quotient-degree"),
        (&[0][..], &[][..], 17, "quotient-shape"),
        (&[17][..], &[0][..], 17, "quotient-residue"),
        (&[0][..], &[17][..], 17, "quotient-residue"),
    ] {
        for name in [
            "quotient.add",
            "quotient.subtract",
            "quotient.multiply",
            "quotient.norm_within",
        ] {
            let mut args = arguments(a, b, q);
            if name == "quotient.norm_within" {
                args.push(Value::Index(0));
            }
            assert_eq!(
                apply(name, &args, &Policy::default(), usize::MAX).unwrap_err(),
                refused(code)
            );
        }
    }
    for (name, args) in [
        ("quotient.unknown", vec![]),
        ("quotient.multiply", vec![Value::Bool(true)]),
        ("quotient.norm_within", arguments(&[0], &[0], 17)),
    ] {
        assert_eq!(
            apply(name, &args, &Policy::default(), usize::MAX).unwrap_err(),
            refused("quotient-operands")
        );
    }
}

#[test]
fn product_respects_exact_work_memory_and_output_admission() {
    let args = arguments(&[1, 1], &[1, 1], 17);
    let policy = Policy {
        max_numerical_work: 37,
        max_numerical_bytes: 288,
        ..Policy::default()
    };
    let call = |p, available| apply("quotient.multiply", &args, &p, available);
    assert!(call(policy, 272).is_ok());
    for (p, available, code) in [
        (
            Policy {
                max_numerical_work: 36,
                ..policy
            },
            272,
            "numerical-work",
        ),
        (
            Policy {
                max_numerical_bytes: 287,
                ..policy
            },
            272,
            "numerical-bytes",
        ),
        (policy, 271, "output-bytes"),
        (
            Policy {
                max_value_bytes: 271,
                ..policy
            },
            272,
            "output-bytes",
        ),
        (
            Policy {
                max_table_elements: 1,
                ..policy
            },
            272,
            "element-limit",
        ),
    ] {
        assert_eq!(call(p, available).unwrap_err(), exhausted(code));
    }
    {
        let _failure = zkc_kernels::allocation::failure::after(0);
        assert_eq!(call(policy, 272).unwrap_err(), exhausted("allocation"));
    }
    assert!(matches!(&call(policy, 272).unwrap()[0], Value::Indices(xs) if xs.as_ref() == [0, 2]));
}

#[test]
fn paired_norm_handles_integer_boundaries_without_large_accumulators() {
    let mut args = arguments(&[0, 8, 9, 16], &[0, 0, 0, 0], 17);
    args.push(Value::Index(129));
    let exact_work = Policy {
        max_numerical_work: 33,
        ..Policy::default()
    };
    assert!(matches!(
        apply("quotient.norm_within", &args, &exact_work, usize::MAX).unwrap()[0],
        Value::Bool(true)
    ));
    args[3] = Value::Index(128);
    assert!(matches!(
        apply("quotient.norm_within", &args, &exact_work, usize::MAX).unwrap()[0],
        Value::Bool(false)
    ));
    assert_eq!(
        apply(
            "quotient.norm_within",
            &args,
            &Policy {
                max_numerical_work: 32,
                ..exact_work
            },
            usize::MAX
        )
        .unwrap_err(),
        exhausted("numerical-work")
    );
    let retained = Value::Bool(false).retained_bytes();
    assert_eq!(
        apply("quotient.norm_within", &args, &exact_work, retained - 1).unwrap_err(),
        exhausted("output-bytes")
    );
    assert_eq!(
        apply(
            "quotient.norm_within",
            &args,
            &Policy {
                max_numerical_bytes: retained - 1,
                ..exact_work
            },
            retained
        )
        .unwrap_err(),
        exhausted("numerical-bytes")
    );
    let mut large = arguments(&[u64::MAX / 2; 8], &[u64::MAX / 2; 8], u64::MAX);
    large.push(Value::Index(u64::MAX));
    assert!(matches!(
        apply(
            "quotient.norm_within",
            &large,
            &Policy::default(),
            usize::MAX
        )
        .unwrap()[0],
        Value::Bool(false)
    ));
}

#[test]
fn projection_and_transform_admission_are_explicit_and_managed() {
    let projection = [
        Value::Indices(vec![17, 18, 19, 20, 21].into()),
        Value::Index(17),
        Value::Index(4),
    ];
    let policy = Policy::default();
    assert!(
        matches!(&apply("quotient.project",&projection,&policy,usize::MAX).unwrap()[0],Value::Indices(xs) if xs.as_ref()==[13,1,2,3])
    );
    let mut invalid = projection.clone();
    invalid[2] = Value::Index(0);
    assert_eq!(
        apply("quotient.project", &invalid, &policy, usize::MAX).unwrap_err(),
        refused("quotient-degree")
    );
    invalid[2] = Value::Index(4);
    invalid[1] = Value::Index(1);
    assert_eq!(
        apply("quotient.project", &invalid, &policy, usize::MAX).unwrap_err(),
        refused("quotient-modulus")
    );
    let input = Value::Indices(vec![1, 2, 3, 4].into());
    let forward = apply(
        "quotient.ntt",
        &[input.clone(), Value::Index(17), Value::Index(2)],
        &policy,
        usize::MAX,
    )
    .unwrap();
    assert!(matches!(&forward[0],Value::Indices(xs) if xs.as_ref()==[15,13,11,16]));
    let inverse = apply(
        "quotient.intt",
        &[forward[0].clone(), Value::Index(17), Value::Index(9)],
        &policy,
        usize::MAX,
    )
    .unwrap();
    assert!(matches!(&inverse[0],Value::Indices(xs) if xs.as_ref()==[1,2,3,4]));
    assert!(matches!(&input,Value::Indices(xs) if xs.as_ref()==[1,2,3,4]));
    for (q, root, values, code) in [
        (17, 1, vec![1, 2, 3, 4], "quotient-transform-root"),
        (65, 2, vec![1, 2, 3, 4], "quotient-transform-profile"),
        (17, 2, vec![17, 2, 3, 4], "quotient-residue"),
        (17, 2, vec![1, 2, 3], "quotient-transform-profile"),
    ] {
        for name in ["quotient.ntt", "quotient.intt"] {
            assert_eq!(
                apply(
                    name,
                    &[
                        Value::Indices(values.clone().into()),
                        Value::Index(q),
                        Value::Index(root)
                    ],
                    &policy,
                    usize::MAX
                )
                .unwrap_err(),
                refused(code)
            );
        }
    }
    for name in ["quotient.project", "quotient.ntt", "quotient.intt"] {
        assert_eq!(
            apply(name, &[Value::Bool(false)], &policy, usize::MAX).unwrap_err(),
            refused("quotient-operands")
        );
    }
}

#[test]
fn unary_operations_refuse_below_exact_memory_and_work_budgets() {
    for (name, parameter, work) in [
        ("quotient.project", 4, 65),
        ("quotient.ntt", 2, 65664),
        ("quotient.intt", 9, 65664),
    ] {
        let args = [
            Value::Indices(vec![1, 2, 3, 4].into()),
            Value::Index(17),
            Value::Index(parameter),
        ];
        let policy = Policy {
            max_numerical_work: work,
            max_numerical_bytes: 320,
            ..Policy::default()
        };
        assert!(apply(name, &args, &policy, 288).is_ok());
        for (policy, available, code) in [
            (
                Policy {
                    max_numerical_work: work - 1,
                    ..policy
                },
                288,
                "numerical-work",
            ),
            (
                Policy {
                    max_numerical_bytes: 319,
                    ..policy
                },
                288,
                "numerical-bytes",
            ),
            (policy, 287, "output-bytes"),
            (
                Policy {
                    max_table_elements: 3,
                    ..policy
                },
                288,
                "element-limit",
            ),
        ] {
            assert_eq!(
                apply(name, &args, &policy, available).unwrap_err(),
                exhausted(code)
            );
        }
        let _failure = zkc_kernels::allocation::failure::after(0);
        assert_eq!(
            apply(name, &args, &policy, 288).unwrap_err(),
            exhausted("allocation")
        );
    }
}
