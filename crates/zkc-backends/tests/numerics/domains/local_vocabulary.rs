use super::support::*;
use serde_json::json;
use zkc_backends::{Policy, Value};
use zkc_runtime::interactive::{Backend, Value as RuntimeValue, admit_supplied};

#[test]
fn boolean_truth_tables_and_exact_bindings() {
    for a in [false, true] {
        assert_value(
            &call(false, "bool.not", &[], vec![Value::Bool(a)])[0],
            &Value::Bool(!a),
        );
        for b in [false, true] {
            assert_value(
                &call(false, "bool.or", &[], vec![Value::Bool(a), Value::Bool(b)])[0],
                &Value::Bool(a || b),
            );
        }
    }
    for name in ["bool.not", "bool.or"] {
        let b = binding(false, name);
        let backend = backend(Policy::default());
        assert_eq!(backend.binding_signature(&b), Some(b.signature().unwrap()));
        let mut bad = b.clone();
        bad.arguments.push("bls12-381.fr".into());
        assert!(bad.signature().is_err());
        assert!(backend.binding_signature(&bad).is_none());
        bad = b;
        bad.implementation = format!("dalek/{name}");
        assert!(bad.signature().is_err());
        assert!(backend.binding_signature(&bad).is_none());
    }
}

#[test]
fn dynamic_group_access_preserves_order_domains_bounds_and_output_charges() {
    for d in [false, true] {
        for xs in [vec![], vec![5], vec![7, 2, 7, 31]] {
            assert_value(
                &call(d, "curve.length", &[], vec![groups(d, &xs)])[0],
                &Value::Index(xs.len() as u64),
            );
            for (i, _) in xs.iter().enumerate() {
                let dynamic = call(
                    d,
                    "curve.get",
                    &[],
                    vec![groups(d, &xs), Value::Index(i as u64)],
                );
                let static_value = call(d, "curve.at", &[&i.to_string()], vec![groups(d, &xs)]);
                assert_value(&dynamic[0], &static_value[0]);
            }
            for index in [xs.len() as u64, u64::MAX] {
                assert_error(
                    d,
                    "curve.get",
                    &[],
                    vec![groups(d, &xs), Value::Index(index)],
                    "refused:group-index",
                );
            }
        }
        for name in ["curve.get", "curve.length"] {
            let b = binding(d, name);
            let sig = b.signature().unwrap();
            let outputs = (0..sig.outputs.len())
                .map(|j| format!("o{j}"))
                .collect::<Vec<_>>();
            let args = if name == "curve.get" {
                vec![groups(d, &[1]), Value::Index(0)]
            } else {
                vec![groups(d, &[1])]
            };
            let mut controlled = Controlled::new(backend(Policy::default()));
            controlled.output_limit = Some(511); // Existing curve scalar-result preflight.
            assert_eq!(
                one(controlled, b.clone(), &[], args.clone()).0.unwrap_err(),
                "exhausted:output-bytes"
            );
            let mut controlled = Controlled::new(backend(Policy::default()));
            controlled.substitute = Some(groups(!d, &[1]));
            assert_eq!(
                one(controlled, b.clone(), &[], args).0.unwrap_err(),
                "refused:kernel-operands"
            );
            let names = (0..sig.inputs.len())
                .map(|j| format!("a{j}"))
                .collect::<Vec<_>>();
            let bytes = program(
                &[b],
                &sig.inputs,
                vec![json!(["op", "site", "b0", ["0"], names, outputs])],
                &sig.outputs,
                &outputs,
            );
            assert!(admit_supplied(&bytes, &backend(Policy::default())).is_err());
        }
    }
}

#[test]
fn eager_composition_does_not_mask_group_failure_or_skip_the_second_predicate() {
    for d in [false, true] {
        let bindings = [
            binding(d, "curve.get"),
            binding(d, "curve.equal"),
            binding(d, "bool.or"),
        ];
        let args = vec![groups(d, &[7]), Value::Index(1), Value::Bool(true)];
        let bytes = program(
            &bindings,
            &args
                .iter()
                .map(RuntimeValue::physical_type)
                .collect::<Vec<_>>(),
            vec![
                json!(["op", "lookup", "b0", [], ["a0", "a1"], ["p"]]),
                json!(["op", "check", "b1", [], ["p", "p"], ["valid"]]),
                json!(["op", "combine", "b2", [], ["a2", "valid"], ["ok"]]),
            ],
            &[Value::Bool(true).physical_type()],
            &["ok".into()],
        );
        let (result, controlled) = run_program(
            Controlled::new(backend(Policy::default())),
            &bytes,
            args.clone(),
        );
        assert_eq!(result.unwrap_err(), "refused:group-index");
        assert!(controlled.outputs.is_empty());
        let mut good = args;
        good[1] = Value::Index(0);
        let (result, controlled) =
            run_program(Controlled::new(backend(Policy::default())), &bytes, good);
        assert_value(&result.unwrap()[0], &Value::Bool(true));
        assert_eq!(controlled.outputs.len(), 3);
    }
    let mut controlled = Controlled::new(backend(Policy::default()));
    controlled.output_limit = Some(255); // Bool retains the existing 256-byte value charge.
    assert_eq!(
        one(
            controlled,
            binding(false, "bool.not"),
            &[],
            vec![Value::Bool(false)]
        )
        .0
        .unwrap_err(),
        "exhausted:output-bytes"
    );
}

#[test]
fn eager_failure_preserves_already_consumed_randomness() {
    use zkc_runtime::interactive::Identity;
    for d in [false, true] {
        let mut inner = backend(Policy::default());
        let rng = inner
            .issue_rng_for(
                if d {
                    Identity::Ristretto255Scalar
                } else {
                    Identity::Bls12381Fr
                },
                domain(),
                2,
            )
            .unwrap();
        let Value::Rng(token) = &rng else {
            panic!("rng");
        };
        let token = token.clone();
        let bindings = [
            binding(d, "random.draw"),
            binding(d, "curve.get"),
            binding(d, "curve.equal"),
            binding(d, "bool.or"),
        ];
        let args = vec![rng, groups(d, &[]), Value::Index(0), Value::Bool(true)];
        let bytes = program(
            &bindings,
            &args
                .iter()
                .map(RuntimeValue::physical_type)
                .collect::<Vec<_>>(),
            vec![
                json!(["op", "draw", "b0", [], ["a0"], ["drawn", "next"]]),
                json!(["op", "lookup", "b1", [], ["a1", "a2"], ["point"]]),
                json!(["op", "predicate", "b2", [], ["point", "point"], ["eq"]]),
                json!(["op", "combine", "b3", [], ["a3", "eq"], ["ok"]]),
            ],
            &[args[3].physical_type(), args[0].physical_type()],
            &["ok".into(), "next".into()],
        );
        let (result, controlled) = run_program(Controlled::new(inner), &bytes, args);
        assert_eq!(result.unwrap_err(), "refused:group-index");
        assert_eq!(controlled.outputs.len(), 1);
        let state = controlled.inner.observe(&token).unwrap();
        assert_eq!(
            (state.generation, state.draw_count, state.budget),
            (1, 1, 1)
        );
        assert_eq!(controlled.inner.active_frames(), 0);
    }
}
