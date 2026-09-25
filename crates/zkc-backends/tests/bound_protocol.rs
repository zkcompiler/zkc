//! Native compiler integration. The compiler is resolved by name, so these run
//! with everything else and fail naming what to build when it is not there.
use std::process::Command;
use zkc_backends::{
    Domain, EntryPolicy, GroupPoint, NativeBackend, Policy, PublicInputs, Scalar, Value,
};
use zkc_runtime::interactive::{Action, Backend, DriverCut, Runner, admit_supplied, drive_cut};

fn backend(role: &str, policy: Policy) -> NativeBackend {
    NativeBackend::new(
        policy,
        EntryPolicy::new(
            Domain::new(role, "test", "main", None),
            None,
            PublicInputs::LocalOnly,
        ),
        None,
    )
    .unwrap()
}

#[test]
fn generic_native_source_executes_mixed_layouts_and_group_operations() {
    let source = zkc_test_support::source("generic-operations.pir");
    let compiled = zkc_test_support::compile("protocol-compile", source);
    let policy = Policy::default();
    let admitted = admit_supplied(&compiled, &backend("P", policy)).unwrap();
    assert!(admitted.checked_source().is_none()); // This test does not install a Lean checker.
    let a = Value::table(&[0u64, 1, 4, 9].map(Scalar::from), &policy).unwrap();
    let b = Value::table(&[2u64, 3, 5, 7].map(Scalar::from), &policy).unwrap();
    let original = a.clone();
    let g = GroupPoint::generator();
    let mut p = Runner::new(
        &admitted,
        "main",
        "P",
        "test",
        backend("P", policy),
        vec![a, b, Value::Curve(g), Value::Bool(true), Value::Bool(false)],
    )
    .unwrap_or_else(|e| panic!("{:?}", e.error));
    let mut v = Runner::new(
        &admitted,
        "main",
        "V",
        "test",
        backend("V", policy),
        vec![Value::Field(Scalar::from(2))],
    )
    .unwrap_or_else(|e| panic!("{:?}", e.error));
    let send = v.poll().cut().unwrap();
    let receive = p.poll().cut().unwrap();
    drive_cut(&mut p, &mut v, &DriverCut::Message { send, receive }).unwrap();
    for site in ["left", "right", "shared", "scale", "both"] {
        let Action::Local(action) = p.poll() else {
            panic!("expected {site}")
        };
        assert_eq!(action.cut.site, site);
        p.execute_local(&action.cut).unwrap();
    }
    let Action::Returned(values) = p.poll() else {
        panic!("participant did not return")
    };
    for (value, expected) in values[..3].iter().zip([[8u64, 17], [8, 11], [8, 17]]) {
        let Value::Table(table) = value else {
            panic!("expected default LSB boundary representation")
        };
        assert_eq!(table.logical_values().unwrap(), expected.map(Scalar::from));
    }
    assert!(matches!(&values[3], Value::Curve(actual) if *actual == g.scale(Scalar::from(2))));
    assert!(matches!(&values[4], Value::Bool(false)));
    let Value::Table(original) = original else {
        unreachable!()
    };
    assert_eq!(
        original.logical_values().unwrap(),
        [0u64, 1, 4, 9].map(Scalar::from)
    );
    assert_eq!(p.backend().active_frames(), 0);
    assert!(matches!(v.poll(), Action::Returned(values) if values.is_empty()));
    // An MSB payload is a distinct intrinsic type; changing only a type label
    // cannot smuggle it into an LSB entry port.
    let wrong = Value::TableMsb(std::sync::Arc::new(
        zkc_arkworks::MsbTable::from_logical(
            &[0u64, 1, 4, 9].map(Scalar::from),
            &policy.ark_bounds(),
        )
        .unwrap(),
    ));
    let result = Runner::new(
        &admitted,
        "main",
        "P",
        "test",
        backend("P", policy),
        vec![
            wrong,
            Value::table(&[0u64, 1, 4, 9].map(Scalar::from), &policy).unwrap(),
            Value::Curve(g),
            Value::Bool(true),
            Value::Bool(false),
        ],
    );
    assert!(result.is_err());
    // The backend advertises the selected implementation independently.
    let unsupported = zkc_runtime::interactive::OperationBinding {
        contract: "poly.fold".into(),
        arguments: vec!["bls12-381.fr".into()],
        implementation: "other/poly.fold".into(),
    };
    assert!(
        backend("P", policy)
            .binding_signature(&unsupported)
            .is_none()
    );
}

#[test]
fn shared_generic_pcs_code_executes_two_authorized_setups_and_ranks() {
    use std::{collections::BTreeMap, sync::Arc};
    use zkc_backends::{Keys, PortConstraint, SetupRegistry};
    use zkc_runtime::interactive::Packet;
    let source = zkc_test_support::source("generic-openings.pir");
    let compiled = Command::new(zkc_test_support::compiler())
        .arg("protocol-compile")
        .arg(source)
        .output()
        .unwrap();
    assert!(
        compiled.status.success(),
        "{}",
        String::from_utf8_lossy(&compiled.stderr)
    );
    let candidate: serde_json::Value = serde_json::from_slice(&compiled.stdout).unwrap();
    assert_eq!(
        candidate[3].as_array().unwrap().len(),
        2,
        "two instances share Prove and Verify bodies"
    );
    let policy = Policy::default();
    let a = Keys::setup_for_development(1, &policy.ark_bounds()).unwrap();
    let b = Keys::setup_for_development(2, &policy.ark_bounds()).unwrap();
    let ma = a.verifier_key().metadata();
    let mb = b.verifier_key().metadata();
    let host = |role: &str| {
        let participant = candidate[4]
            .as_array()
            .unwrap()
            .iter()
            .find(|p| p[3] == role)
            .unwrap();
        // Projection exports canonical SSA names. This fixture's first two
        // ordered role ports correspond to its two explicit key inputs.
        let ports = [
            participant[5][0][0].as_str().unwrap(),
            participant[5][1][0].as_str().unwrap(),
        ];
        let entry = EntryPolicy::new(
            Domain::new(role, "test", "main", None),
            None,
            PublicInputs::LocalOnly,
        )
        .with_ports(BTreeMap::from([
            (
                ports[0].into(),
                PortConstraint {
                    arity: Some(1),
                    setup: Some(ma),
                },
            ),
            (
                ports[1].into(),
                PortConstraint {
                    arity: Some(2),
                    setup: Some(mb),
                },
            ),
        ]));
        NativeBackend::with_setups(
            policy,
            entry,
            SetupRegistry::new(
                vec![a.verifier_key().clone(), b.verifier_key().clone()],
                &policy,
            )
            .unwrap(),
        )
        .unwrap()
    };
    let admitted = admit_supplied(&compiled.stdout, &host("P")).unwrap();
    let mut p = Runner::new(
        &admitted,
        "main",
        "P",
        "test",
        host("P"),
        vec![
            Value::ProverKey(Arc::new(a.prover_key().clone())),
            Value::ProverKey(Arc::new(b.prover_key().clone())),
            Value::table(&[2u64, 5].map(Scalar::from), &policy).unwrap(),
            Value::table(&[0u64, 1, 4, 9].map(Scalar::from), &policy).unwrap(),
        ],
    )
    .unwrap_or_else(|e| panic!("{}", e.error));
    let mut v = Runner::new(
        &admitted,
        "main",
        "V",
        "test",
        host("V"),
        vec![
            Value::VerifierKey(Arc::new(a.verifier_key().clone())),
            Value::VerifierKey(Arc::new(b.verifier_key().clone())),
            Value::point(vec![Scalar::from(2)], &policy).unwrap(),
            Value::point(vec![Scalar::from(2), Scalar::from(3)], &policy).unwrap(),
        ],
    )
    .unwrap_or_else(|e| panic!("{}", e.error));
    let mut messages = 0;
    for _ in 0..32 {
        let pa = p.poll();
        let va = v.poll();
        if let Action::Local(local) = pa {
            p.execute_local(&local.cut).unwrap();
            continue;
        }
        if let Action::Local(local) = va {
            v.execute_local(&local.cut).unwrap();
            continue;
        }
        let (sender, receiver) = match (&pa, &va) {
            (Action::Send(_), Action::Receive(_)) => (&mut p, &mut v),
            (Action::Receive(_), Action::Send(_)) => (&mut v, &mut p),
            (Action::Returned(_), Action::Returned(values)) => {
                assert!(matches!(
                    values.as_slice(),
                    [Value::Bool(true), Value::Bool(true)]
                ));
                assert_eq!(messages, 8);
                assert_eq!(p.backend().active_frames(), 0);
                assert_eq!(v.backend().active_frames(), 0);
                return;
            }
            _ => panic!("unexpected protocol states: {pa:?} / {va:?}"),
        };
        let Action::Send(packet) = sender.poll() else {
            unreachable!()
        };
        let wire = sender.backend().encode_value(&packet.payload).unwrap();
        let setup = match packet.envelope.site.as_str() {
            "commit_a" | "proof_a" => Some(ma),
            "commit_b" | "proof_b" => Some(mb),
            _ => None,
        };
        let decoded = match setup {
            Some(setup) => receiver
                .backend()
                .decode_for_setup(packet.ty.clone(), setup, &wire),
            None => receiver
                .backend()
                .decode_typed_value(packet.ty.clone(), &wire),
        }
        .unwrap();
        let delivered = Packet {
            payload: decoded,
            ..packet.clone()
        };
        receiver.check_delivery(&delivered).unwrap();
        let cut = sender.poll().cut().unwrap();
        sender.take_send(&cut).unwrap();
        receiver.deliver(delivered).unwrap();
        messages += 1;
    }
    panic!("bounded protocol driver did not finish");
}

#[cfg(feature = "test-utils")]
mod stopping {
    use super::*;
    use zkc_runtime::interactive::{
        BackendError, BoundSignature, Frame, FrameExit, Invocation, OperationBinding, StopKind,
    };

    struct Limited {
        inner: NativeBackend,
        fail_conversion: usize,
        conversions: usize,
        attempted: Vec<String>,
    }
    impl Backend for Limited {
        type Value = Value;
        fn binding_signature(&self, b: &OperationBinding) -> Option<BoundSignature> {
            self.inner.binding_signature(b)
        }
        fn validate_value(&self, value: &Value) -> Result<(), BackendError> {
            self.inner.validate_value(value)
        }
        fn enter_frame(&mut self, frame: &Frame, args: &[Value]) -> Result<(), BackendError> {
            self.inner.enter_frame(frame, args)
        }
        fn leave_frame(
            &mut self,
            frame: &Frame,
            exit: FrameExit,
            values: &[Value],
        ) -> Result<(), BackendError> {
            self.inner.leave_frame(frame, exit, values)
        }
        fn apply(
            &mut self,
            invocation: &Invocation<'_>,
            args: &[Value],
        ) -> Result<Vec<Value>, BackendError> {
            self.attempted.push(invocation.kernel.into());
            if invocation.kernel == "arkworks/table.relayout" {
                self.conversions += 1;
                if self.conversions == self.fail_conversion {
                    // Exercise the real adapter's pre-allocation capacity check.
                    return self.inner.apply(
                        &Invocation {
                            max_output_bytes: 0,
                            ..*invocation
                        },
                        args,
                    );
                }
            }
            self.inner.apply(invocation, args)
        }
    }

    #[test]
    fn stops_preserve_consumed_randomness_and_ordered_conversion_prefixes() {
        let source = zkc_test_support::source("generic-stops.pir");
        let compiled = zkc_test_support::compile("protocol-compile", source);
        let policy = Policy::default();
        let admitted = admit_supplied(&compiled, &backend("P", policy)).unwrap();
        for (allowed, fail_conversion, prefix, error) in [
            (
                false,
                0,
                vec!["random.draw", "control.require"],
                Some("rejected:require"),
            ),
            (
                true,
                1,
                vec!["random.draw", "control.require", "table.relayout"],
                Some("exhausted:output-bytes"),
            ),
            (
                true,
                2,
                vec![
                    "random.draw",
                    "control.require",
                    "table.relayout",
                    "poly.fold",
                    "table.relayout",
                ],
                Some("exhausted:output-bytes"),
            ),
            (
                true,
                0,
                vec![
                    "random.draw",
                    "control.require",
                    "table.relayout",
                    "poly.fold",
                    "table.relayout",
                ],
                None,
            ),
        ] {
            let mut inner = backend("P", policy);
            let rng = inner
                .issue_test_tape(
                    Domain::new("P", "test", "main", None),
                    1,
                    vec![Scalar::from(2)],
                )
                .unwrap();
            let Value::Rng(handle) = &rng else {
                unreachable!()
            };
            let handle = handle.clone();
            let untouched = inner
                .issue_test_tape(
                    Domain::new("P", "test", "main", None),
                    1,
                    vec![Scalar::from(7)],
                )
                .unwrap();
            let Value::Rng(other) = untouched else {
                unreachable!()
            };
            let original = Value::table(&[0u64, 1, 4, 9].map(Scalar::from), &policy).unwrap();
            let mut runner = Runner::new(
                &admitted,
                "main",
                "P",
                "test",
                Limited {
                    inner,
                    fail_conversion,
                    conversions: 0,
                    attempted: vec![],
                },
                vec![rng, original.clone(), Value::Bool(allowed)],
            )
            .unwrap_or_else(|e| panic!("{}", e.error));
            let Action::Local(action) = runner.poll() else {
                panic!("expected local")
            };
            runner.execute_local(&action.cut).unwrap();
            match (runner.poll(), error) {
                (Action::Stopped(stop), Some(code)) => {
                    assert!(matches!(stop.kind, StopKind::Backend(ref e) if e.code == code));
                }
                (Action::Returned(values), None) => {
                    let [Value::Table(result), Value::Rng(_)] = values.as_slice() else {
                        panic!("wrong result")
                    };
                    assert_eq!(
                        result.logical_values().unwrap(),
                        [8u64, 17].map(Scalar::from)
                    );
                }
                (state, _) => panic!("unexpected terminal {state:?}"),
            }
            let actual: Vec<_> = runner
                .backend()
                .attempted
                .iter()
                .map(|s| s.split_once('/').unwrap().1)
                .collect();
            assert_eq!(actual, prefix);
            let state = runner.backend().inner.observe(&handle).unwrap();
            assert_eq!(
                (state.generation, state.draw_count, state.budget),
                (1, 1, 0)
            );
            let state = runner.backend().inner.observe(&other).unwrap();
            assert_eq!(
                (state.generation, state.draw_count, state.budget),
                (0, 0, 1)
            );
            assert_eq!(runner.backend().inner.active_frames(), 0);
            let Value::Table(original) = original else {
                unreachable!()
            };
            assert_eq!(
                original.logical_values().unwrap(),
                [0u64, 1, 4, 9].map(Scalar::from)
            );
        }
    }
}
