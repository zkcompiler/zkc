use super::support::*;
use serde_json::json;
use zkc_backends::{Policy, PublicRolePolicy, RistrettoScalar, Value};
use zkc_runtime::interactive::{Backend, OperationBinding, Value as RuntimeValue, admit_supplied};

fn selected() -> OperationBinding {
    OperationBinding {
        implementation: "dalek-vartime/curve.msm".into(),
        ..binding(true, "curve.msm")
    }
}
fn granted() -> zkc_backends::NativeBackend {
    backend(Policy::default()).with_public_role_policy(PublicRolePolicy::new(["P".into()]).unwrap())
}
#[test]
fn public_msm_contract_is_dense_exact_and_default_is_unchanged() {
    let default = binding(true, "curve.msm");
    assert_eq!(
        default.signature().unwrap(),
        selected().signature().unwrap()
    );
    assert_eq!(
        backend(Policy::default()).binding_signature(&selected()),
        Some(default.signature().unwrap())
    );
    for mut bad in [
        binding(false, "curve.msm"),
        binding(true, "curve.scale_each"),
        binding(true, "vector.dot"),
    ] {
        bad.implementation = selected().implementation;
        assert!(bad.signature().is_err());
        assert!(backend(Policy::default()).binding_signature(&bad).is_none());
    }
    assert!(zkc_backends::requires_public_operands(
        &selected().implementation
    ));
    assert!(!zkc_backends::requires_public_operands(
        &default.implementation
    ));
}
#[test]
fn zero_one_many_and_nontrivial_scalars_have_identical_canonical_results() {
    for n in [0, 1, 2, 16, 256, 1024] {
        let scalars: Vec<_> = (0..n)
            .map(|i| {
                if i % 7 == 0 {
                    RistrettoScalar::ZERO
                } else {
                    RistrettoScalar::from_bytes_mod_order_wide(&[i as u8; 64])
                }
            })
            .collect();
        let args = vec![
            Value::ristretto_vector(&scalars, &Policy::default()).unwrap(),
            groups(true, &(0..n as u64).collect::<Vec<_>>()),
        ];
        let a = one(
            backend(Policy::default()),
            binding(true, "curve.msm"),
            &[],
            args.clone(),
        )
        .0
        .unwrap();
        let b = one(granted(), selected(), &[], args).0.unwrap();
        assert_value(&a[0], &b[0]);
    }
}
#[test]
fn default_and_wrong_role_policies_refuse_even_empty_operands() {
    for b in [
        backend(Policy::default()),
        backend(Policy::default())
            .with_public_role_policy(PublicRolePolicy::new(["V".into()]).unwrap()),
    ] {
        assert_eq!(
            one(
                b,
                selected(),
                &[],
                vec![vector(true, &[]), groups(true, &[])]
            )
            .0
            .unwrap_err(),
            "refused:public-operands-required"
        );
    }
    for roles in [vec!["".into()], vec!["x".repeat(257)], vec!["P".into(); 65]] {
        assert_eq!(
            PublicRolePolicy::new(roles).unwrap_err().code,
            "refused:public-role-policy"
        );
    }
}
#[test]
fn shape_output_budget_and_malformed_wire_match_default() {
    for (binding, b) in [
        (binding(true, "curve.msm"), backend(Policy::default())),
        (selected(), granted()),
    ] {
        assert_eq!(
            one(b, binding, &[], vec![vector(true, &[1]), groups(true, &[])])
                .0
                .unwrap_err(),
            "refused:length-mismatch"
        );
    }
    for budget in [0, 511, 512, 513] {
        let args = vec![vector(true, &[3, 5]), groups(true, &[7, 11])];
        let mut a = Controlled::new(backend(Policy::default()));
        a.output_limit = Some(budget);
        let mut b = Controlled::new(granted());
        b.output_limit = Some(budget);
        let x = one(a, binding(true, "curve.msm"), &[], args.clone()).0;
        let y = one(b, selected(), &[], args).0;
        match (x, y) {
            (Ok(x), Ok(y)) => {
                assert!(budget >= 512);
                assert_value(&x[0], &y[0]);
            }
            (Err(x), Err(y)) => {
                assert!(budget < 512);
                assert_eq!(x, y);
                assert_eq!(x, "exhausted:output-bytes");
            }
            _ => panic!("different budget outcome"),
        }
    }
    let value = groups(true, &[1]);
    let mut bytes = granted().encode_value(&value).unwrap();
    bytes[10..].fill(255);
    let default = backend(Policy::default())
        .decode_typed_value(value.physical_type(), &bytes)
        .unwrap_err();
    let selected = granted()
        .decode_typed_value(value.physical_type(), &bytes)
        .unwrap_err();
    assert_eq!(default.code, selected.code);
    assert_eq!(selected.code, "refused:noncanonical-point");
}
#[test]
fn reached_roles_include_shared_functions_and_calls_but_not_zero_trip_bodies() {
    let b = selected();
    let sig = b.signature().unwrap();
    let bytes = program(
        &[b],
        &sig.inputs,
        vec![json!(["op", "msm", "b0", [], ["a0", "a1"], ["out"]])],
        &sig.outputs,
        &["out".into()],
    );
    let mut p: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
    let mut other = p[4][0].clone();
    other[1] = json!("other");
    other[3] = json!("Audit");
    p[4].as_array_mut().unwrap().push(other);
    p[5][0][2]
        .as_array_mut()
        .unwrap()
        .push(json!(["Audit", "other"]));
    let check = |p: &serde_json::Value| {
        admit_supplied(&serde_json::to_vec(p).unwrap(), &granted())
            .unwrap()
            .executable_implementation_roles("main")
            .unwrap()
    };
    let roles = check(&p);
    assert_eq!(
        roles["dalek-vartime/curve.msm"],
        ["Audit".into(), "P".into()].into()
    );
    // Keep the caller's actual role through a nested participant call.
    let mut child = p[4][0].clone();
    child[1] = json!("child");
    child[2] = json!("nested_instance");
    p[4].as_array_mut().unwrap().push(child);
    p[4][0][7][0] = json!(["call", "nested", "child", ["a0", "a1"], ["result0"]]);
    assert_eq!(check(&p), roles);
    for count in ["0", "1"] {
        let mut q = p.clone();
        let mut dead = q[4][1].clone();
        dead[1] = json!("conditional_child");
        dead[2] = json!("conditional_instance");
        q[4].as_array_mut().unwrap().push(dead);
        q[4][1][6] = json!([]);
        q[4][1][7] = json!([
            [
                "loop",
                "repeat",
                count,
                [],
                ["a0", "a1"],
                [
                    [
                        "call",
                        "step",
                        "conditional_child",
                        ["a0", "a1"],
                        ["unused"]
                    ],
                    ["yield", []]
                ],
                []
            ],
            ["return", []]
        ]);
        let uses = check(&q);
        assert_eq!(
            uses["dalek-vartime/curve.msm"].contains("Audit"),
            count == "1"
        );
    }
}

#[test]
fn nominal_verifier_name_does_not_authorize_lower_level_execution() {
    use zkc_backends::{Domain, EntryPolicy, NativeBackend, PublicInputs};
    use zkc_runtime::interactive::{Action, Runner, StopKind};
    let b = selected();
    let sig = b.signature().unwrap();
    let bytes = program(
        &[b],
        &sig.inputs,
        vec![json!(["op", "msm", "b0", [], ["a0", "a1"], ["out"]])],
        &sig.outputs,
        &["out".into()],
    );
    let mut p: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
    p[4][0][3] = json!("V");
    p[5][0][2][0][0] = json!("V");
    let b = NativeBackend::new(
        Policy::default(),
        EntryPolicy::new(
            Domain::new("V", "session", "main", None),
            None,
            PublicInputs::LocalOnly,
        ),
        None,
    )
    .unwrap();
    let admitted = admit_supplied(&serde_json::to_vec(&p).unwrap(), &b).unwrap();
    let mut runner = Runner::new(
        &admitted,
        "main",
        "V",
        "session",
        b,
        vec![vector(true, &[1]), groups(true, &[2])],
    )
    .unwrap_or_else(|e| panic!("{}", e.error));
    let Action::Local(a) = runner.poll() else {
        panic!()
    };
    runner.execute_local(&a.cut).unwrap();
    let Action::Stopped(s) = runner.poll() else {
        panic!()
    };
    let StopKind::Backend(e) = s.kind else {
        panic!()
    };
    assert_eq!(e.code, "refused:public-operands-required");
}

#[test]
fn input_limits_and_wrong_nominal_operands_keep_existing_refusals() {
    for limit in [0, 1, 2] {
        let policy = Policy {
            max_groups: limit,
            ..Policy::default()
        };
        let a = backend(policy);
        let b =
            backend(policy).with_public_role_policy(PublicRolePolicy::new(["P".into()]).unwrap());
        let value = groups(true, &[1]);
        let x = a.validate_value(&value).map_err(|e| e.code);
        let y = b.validate_value(&value).map_err(|e| e.code);
        assert_eq!(x, y);
        if limit == 0 {
            assert_eq!(x.unwrap_err(), "exhausted:group-limit");
        } else {
            x.unwrap();
        }
    }
    let mut b = Controlled::new(granted());
    b.substitute = Some(vector(false, &[1]));
    assert_eq!(
        one(
            b,
            selected(),
            &[],
            vec![vector(true, &[1]), groups(true, &[2])]
        )
        .0
        .unwrap_err(),
        "refused:kernel-operands"
    );
}
