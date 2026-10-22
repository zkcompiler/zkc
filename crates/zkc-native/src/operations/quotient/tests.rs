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
