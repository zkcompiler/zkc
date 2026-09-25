mod common;
use common::*;
use serde_json::json;
use std::{collections::BTreeMap, sync::Arc};
use zkc_backends::*;
use zkc_runtime::interactive::{
    Backend, BackendError, ErrorCode, Frame, FrameExit, Invocation, Runner, Type,
    Value as RuntimeValue, admit_supplied,
};

fn keys(n: usize) -> Keys {
    Keys::setup_for_development(n, &Policy::default().ark_bounds()).unwrap()
}
fn private_state(keys: &Keys, original: &Value) -> Value {
    let Value::Table(t) = original else { panic!() };
    Value::OpeningState(Arc::new(keys.prover_key().commit(t).unwrap()))
}
fn open_program() -> Vec<u8> {
    program(
        None,
        &[("state", "opening_state"), ("p", "point")],
        vec![op(
            "open",
            "arkworks/pcs.open",
            &["state", "p"],
            &["y", "proof"],
        )],
        &["field", "proof"],
        &["y", "proof"],
    )
}

#[test]
fn exact_contracts_and_legacy_candidates_fail_closed() {
    let b = ark_backend(None);
    let binding = |contract: &str| zkc_runtime::interactive::OperationBinding {
        contract: contract.into(),
        arguments: vec!["multilinear.kzg.bls12-381/1".into()],
        implementation: format!("arkworks/{contract}"),
    };
    let commit = b.binding_signature(&binding("pcs.commit")).unwrap();
    let open = b.binding_signature(&binding("pcs.open")).unwrap();
    let kinds = |types: &[zkc_runtime::interactive::PhysicalType]| {
        types.iter().map(|t| t.kind()).collect::<Vec<_>>()
    };
    assert_eq!(kinds(&commit.inputs), [Type::ProverKey, Type::Table]);
    assert_eq!(
        kinds(&commit.outputs),
        [Type::Commitment, Type::OpeningState]
    );
    assert_eq!(kinds(&open.inputs), [Type::OpeningState, Type::Point]);
    assert_eq!(kinds(&open.outputs), [Type::Field, Type::Proof]);
    for name in ["pcs.commit", "pcs.open"] {
        let declaration = binding(name);
        assert_eq!(
            b.binding_signature(&declaration),
            declaration.signature().ok()
        );
    }
    assert_eq!(Type::OpeningState.name(), "opening_state");
    assert!(!Type::OpeningState.is_affine());
    assert!(!Type::OpeningState.is_serializable());
    for old in [
        op("old", "arkworks/pcs.commit", &["pk", "t"], &["c"]),
        op(
            "old",
            "arkworks/pcs.open",
            &["pk", "t", "p"],
            &["y", "proof"],
        ),
    ] {
        let bytes = program(
            None,
            &[("pk", "prover_key"), ("t", "table"), ("p", "point")],
            vec![old],
            &[],
            &[],
        );
        assert_eq!(
            admit_supplied(&bytes, &b).unwrap_err().code,
            ErrorCode::Signature
        );
    }
}

#[test]
fn two_originals_survive_sumcheck_scratch_and_open_at_the_same_reached_point() {
    let k = keys(2);
    let a = table(&[2, 3, 5, 7]);
    let b = table(&[11, 13, 17, 19]);
    let bytes = program(
        Some(2),
        &[
            ("pk", "prover_key"),
            ("vk", "verifier_key"),
            ("a", "table"),
            ("b", "table"),
            ("r0", "field"),
            ("r1", "field"),
        ],
        vec![
            op("ca", "arkworks/pcs.commit", &["pk", "a"], &["ca", "sa"]),
            op("cb", "arkworks/pcs.commit", &["pk", "b"], &["cb", "sb"]),
            op("sum", "arkworks/poly.product_sum", &["a", "b"], &["sum"]),
            op(
                "round0",
                "arkworks/poly.product_round",
                &["a", "b"],
                &["q0"],
            ),
            op(
                "boundary0",
                "arkworks/poly.boundary",
                &["q0"],
                &["boundary0"],
            ),
            op(
                "equal0",
                "arkworks/field.equal",
                &["sum", "boundary0"],
                &["equal0"],
            ),
            op("require0", "arkworks/control.require", &["equal0"], &[]),
            op(
                "eval0",
                "arkworks/poly.round_evaluate",
                &["q0", "r0"],
                &["claim1"],
            ),
            op("a0", "arkworks/poly.fold", &["a", "r0"], &["a0"]),
            op("b0", "arkworks/poly.fold", &["b", "r0"], &["b0"]),
            op(
                "round1",
                "arkworks/poly.product_round",
                &["a0", "b0"],
                &["q1"],
            ),
            op(
                "boundary1",
                "arkworks/poly.boundary",
                &["q1"],
                &["boundary1"],
            ),
            op(
                "equal1",
                "arkworks/field.equal",
                &["claim1", "boundary1"],
                &["equal1"],
            ),
            op("require1", "arkworks/control.require", &["equal1"], &[]),
            op(
                "eval1",
                "arkworks/poly.round_evaluate",
                &["q1", "r1"],
                &["terminal"],
            ),
            op("a1", "arkworks/poly.fold", &["a0", "r1"], &["a1"]),
            op("b1", "arkworks/poly.fold", &["b0", "r1"], &["b1"]),
            op("empty", "arkworks/poly.empty_point", &[], &["empty"]),
            op(
                "p0",
                "arkworks/poly.append_point",
                &["empty", "r0"],
                &["p0"],
            ),
            op(
                "p1",
                "arkworks/poly.append_point",
                &["p0", "r1"],
                &["reached"],
            ),
            op("oa", "arkworks/pcs.open", &["sa", "reached"], &["ya", "pa"]),
            op("ob", "arkworks/pcs.open", &["sb", "reached"], &["yb", "pb"]),
            op(
                "oa_again",
                "arkworks/pcs.open",
                &["sa", "reached"],
                &["ya2", "pa2"],
            ),
            op(
                "checka",
                "arkworks/pcs.check",
                &["vk", "ca", "reached", "ya", "pa"],
                &["oka"],
            ),
            op(
                "checkb",
                "arkworks/pcs.check",
                &["vk", "cb", "reached", "yb", "pb"],
                &["okb"],
            ),
            op(
                "checka2",
                "arkworks/pcs.check",
                &["vk", "ca", "reached", "ya2", "pa2"],
                &["oka2"],
            ),
            op("product", "arkworks/field.mul", &["ya", "yb"], &["product"]),
            op(
                "terminal",
                "arkworks/field.equal",
                &["product", "terminal"],
                &["okterminal"],
            ),
        ],
        &[
            "bool",
            "bool",
            "bool",
            "bool",
            "table",
            "table",
            "opening_state",
            "opening_state",
            "field",
            "field",
        ],
        &[
            "oka",
            "okb",
            "oka2",
            "okterminal",
            "a1",
            "b1",
            "sa",
            "sb",
            "ya",
            "yb",
        ],
    );
    let (out, backend) = run(
        &bytes,
        ark_backend(Some(2)),
        vec![
            Value::ProverKey(Arc::new(k.prover_key().clone())),
            Value::VerifierKey(Arc::new(k.verifier_key().clone())),
            a.clone(),
            b.clone(),
            f(11),
            f(13),
        ],
    );
    let out = out.unwrap();
    assert!(out[..4].iter().all(|v| matches!(v, Value::Bool(true))));
    for (index, original) in [(0, a), (1, b)] {
        let Value::Table(t) = original else { panic!() };
        let Value::Table(scratch) = &out[4 + index] else {
            panic!()
        };
        let Value::OpeningState(state) = &out[6 + index] else {
            panic!()
        };
        assert_eq!(
            state.original().logical_values().unwrap(),
            t.logical_values().unwrap()
        );
        assert_eq!(scratch.arity(), 0);
        assert_eq!(
            scratch.scalar_at_zero_arity().unwrap(),
            scalar(&out[8 + index])
        );
    }
    assert_eq!(backend.active_frames(), 0);
}

#[test]
fn equal_tables_issue_distinct_states_and_backend_retains_no_hidden_state() {
    let k = keys(1);
    let a = table(&[2, 3]);
    let b = table(&[2, 3]);
    let (Value::Table(ta), Value::Table(tb)) = (&a, &b) else {
        panic!()
    };
    assert!(!Arc::ptr_eq(ta, tb));
    let bytes = program(
        None,
        &[("pk", "prover_key"), ("a", "table"), ("b", "table")],
        vec![
            op("a", "arkworks/pcs.commit", &["pk", "a"], &["ca", "sa"]),
            op("b", "arkworks/pcs.commit", &["pk", "b"], &["cb", "sb"]),
            op("again", "arkworks/pcs.commit", &["pk", "a"], &["cc", "sc"]),
        ],
        &[
            "commitment",
            "commitment",
            "opening_state",
            "opening_state",
            "opening_state",
        ],
        &["ca", "cb", "sa", "sb", "sc"],
    );
    let (out, backend) = run(
        &bytes,
        ark_backend(None),
        vec![Value::ProverKey(Arc::new(k.prover_key().clone())), a, b],
    );
    let out = out.unwrap();
    assert_eq!(
        backend.encode_value(&out[0]).unwrap(),
        backend.encode_value(&out[1]).unwrap()
    );
    let states = out[2..]
        .iter()
        .map(|v| {
            let Value::OpeningState(s) = v else { panic!() };
            s
        })
        .collect::<Vec<_>>();
    for i in 0..3 {
        for j in i + 1..3 {
            assert!(!Arc::ptr_eq(states[i], states[j]));
        }
    }
    // A different adapter can open an actual state without any prior cache entry.
    for state in &out[2..] {
        let (opened, _) = run(
            &open_program(),
            ark_backend(None),
            vec![state.clone(), point(&[7])],
        );
        assert_eq!(scalar(&opened.unwrap()[0]), Scalar::from(9u64));
    }
    let weak = states.iter().map(|s| Arc::downgrade(s)).collect::<Vec<_>>();
    drop(out);
    assert!(weak.iter().all(|s| s.upgrade().is_none()));
    assert_eq!(backend.active_frames(), 0);
}

#[test]
fn state_passes_explicit_local_and_child_ports_and_can_be_borrowed_twice() {
    let k = keys(1);
    let state = private_state(&k, &table(&[2, 3]));
    let bytes = participants(json!([
        [[
            "function",
            "open",
            [["s", "opening_state"], ["p", "point"]],
            ["field", "proof"],
            [
                op("open", "arkworks/pcs.open", &["s", "p"], &["y", "proof"]),
                ["return", ["y", "proof"]]
            ]
        ]],
        [
            [
                "participant",
                "root",
                "root_instance",
                "P",
                [],
                [["s", "opening_state"], ["p", "point"]],
                ["field", "field"],
                [
                    ["call", "first", "child", ["s", "p"], ["y1"]],
                    ["call", "second", "child", ["s", "p"], ["y2"]],
                    ["return", ["y1", "y2"]]
                ]
            ],
            [
                "participant",
                "child",
                "opening_instance",
                "P",
                [],
                [["s", "opening_state"], ["p", "point"]],
                ["field"],
                [
                    ["local", "local", "open", ["s", "p"], ["y", "proof"]],
                    ["return", ["y"]]
                ]
            ]
        ],
        [["entry", "main", [["P", "root"]]]]
    ]))
    .unwrap();
    let (out, backend) = run(&bytes, ark_backend(None), vec![state.clone(), point(&[7])]);
    assert!(out.unwrap().iter().all(|v| scalar(v) == Scalar::from(9u64)));
    assert_eq!(backend.active_frames(), 0);
    // No parent variable can be fetched in a child whose port list omits it.
    let mut unpassed: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
    unpassed[4][1][5] = json!([["p", "point:bls12-381.fr@arkworks.point/1"]]);
    unpassed[4][0][7][0][4] = json!(["p"]);
    unpassed[4][0][7][1][4] = json!(["p"]);
    assert_eq!(
        admit_supplied(&serde_json::to_vec(&unpassed).unwrap(), &backend)
            .unwrap_err()
            .code,
        ErrorCode::Ssa
    );
    let aliases = program(
        None,
        &[("a", "opening_state"), ("b", "opening_state")],
        vec![],
        &["opening_state", "opening_state"],
        &["a", "b"],
    );
    assert!(run(&aliases, backend, vec![state.clone(), state]).0.is_ok());
}

#[test]
fn state_host_admission_checks_key_rank_limits_and_private_pins() {
    let k = keys(1);
    let state = private_state(&k, &table(&[2, 3]));
    let other = keys(1);
    let bytes = open_program();
    for (entry_policy, verifier, expected) in [
        (entry(Some(2)), None, "entry-shape"),
        (
            entry(None),
            Some(other.verifier_key().clone()),
            "key-mismatch",
        ),
        (
            EntryPolicy::new(
                domain(),
                None,
                PublicInputs::Exact(BTreeMap::from([("state".into(), state.clone())])),
            ),
            None,
            "nonserializable",
        ),
    ] {
        let backend = NativeBackend::new(Policy::default(), entry_policy, verifier).unwrap();
        let admitted = admit_supplied(&bytes, &backend).unwrap();
        match Runner::new(
            &admitted,
            "main",
            "P",
            "session",
            backend,
            vec![state.clone(), point(&[7])],
        ) {
            Err(e) => {
                assert!(e.error.to_string().contains(expected), "{}", e.error);
                assert_eq!(e.backend.active_frames(), 0);
            }
            Ok(_) => panic!("accepted {expected}"),
        }
    }
    let backend = NativeBackend::new(
        Policy {
            max_arity: 0,
            ..Policy::default()
        },
        entry(None),
        None,
    )
    .unwrap();
    assert_eq!(
        backend.validate_value(&state).unwrap_err().code,
        "exhausted:arity-limit"
    );
    let mixed = program(
        None,
        &[("s", "opening_state"), ("pk", "prover_key")],
        vec![],
        &[],
        &[],
    );
    let backend = ark_backend(None);
    let admitted = admit_supplied(&mixed, &backend).unwrap();
    match Runner::new(
        &admitted,
        "main",
        "P",
        "session",
        backend,
        vec![
            state,
            Value::ProverKey(Arc::new(other.prover_key().clone())),
        ],
    ) {
        Err(e) => assert!(e.error.to_string().contains("entry-key-mismatch")),
        Ok(_) => panic!("accepted state from a different setup"),
    }
}

#[test]
fn only_host_bound_actual_states_are_inputs_and_private_values_never_have_wire_tags() {
    let k = keys(1);
    let original = table(&[2, 3]);
    let state = private_state(&k, &original);
    let mut backend = ark_backend(None);
    let rng = backend.issue_rng(domain(), 2).unwrap();
    // Independently authorized native setup: wrong private custody must fail
    // without consuming an unrelated nonce.
    let other_key = keys(1);
    let mut receiver = NativeBackend::with_setups(
        Policy::default(),
        entry(None),
        SetupRegistry::new(vec![other_key.verifier_key().clone()], &Policy::default()).unwrap(),
    )
    .unwrap();
    let nonce = receiver.issue_nonce(domain(), 2).unwrap();
    for value in [
        state.clone(),
        Value::ProverKey(Arc::new(k.prover_key().clone())),
        Value::VerifierKey(Arc::new(k.verifier_key().clone())),
        rng,
    ] {
        assert_eq!(
            backend.encode_value(&value).unwrap_err().code,
            "refused:nonserializable"
        );
        for forged in [
            &[][..],
            &b"ZKCV\x01\x00"[..],
            &backend.encode_value(&f(2)).unwrap()[..],
        ] {
            assert_eq!(
                backend
                    .decode_typed_value(value.physical_type(), forged)
                    .unwrap_err()
                    .code,
                "refused:nonserializable"
            );
        }
    }
    assert_eq!(
        receiver.encode_value(&nonce).unwrap_err().code,
        "refused:nonserializable"
    );
    let before_nonce = receiver.observe(token(&nonce)).unwrap();
    assert_eq!(
        receiver.validate_value(&state).unwrap_err().code,
        "refused:unauthorized-setup"
    );
    assert_eq!(receiver.observe(token(&nonce)).unwrap(), before_nonce);
    let admitted = admit_supplied(&open_program(), &backend).unwrap();
    let role = admitted.entry("main").unwrap().remove(0);
    let mut host = InputBindings::new();
    host.insert("selected-original", state).unwrap();
    host.insert("scratch", original).unwrap();
    let input = |record| {
        serde_json::to_vec(&json!([
            "zkc.inputs/1",
            [["state", record], ["p", ["point", ["7"]]]]
        ]))
        .unwrap()
    };
    let actual = backend
        .inputs_from_json(&role, &input(json!(["host", "selected-original"])), &host)
        .unwrap();
    assert_eq!(
        scalar(&run(&open_program(), backend, actual).0.unwrap()[0]),
        Scalar::from(9u64)
    );
    let backend = ark_backend(None);
    for (record, error) in [
        (json!(["opening_state", "0"]), "refused:input-tag"),
        (
            json!(["opening_state", {"key_id": "fake", "table": ["2", "3"]}]),
            "refused:input-tag",
        ),
        (json!(["wire", "5a4b43560100"]), "refused:nonserializable"),
        (json!(["host", "scratch"]), "refused:input-type"),
        (json!(["host", "absent"]), "refused:input-host-handle"),
    ] {
        assert_eq!(
            backend
                .inputs_from_json(&role, &input(record), &host)
                .unwrap_err()
                .code,
            error
        );
    }
    for action in [
        json!(["send", "leak", "schema", "V", "state"]),
        json!([
            "receive",
            "forge",
            "schema",
            "V",
            "incoming",
            "opening_state"
        ]),
    ] {
        let mut artifact: serde_json::Value = serde_json::from_slice(&open_program()).unwrap();
        artifact[4][0][7].as_array_mut().unwrap().insert(0, action);
        assert_eq!(
            admit_supplied(&serde_json::to_vec(&artifact).unwrap(), &backend)
                .unwrap_err()
                .code,
            ErrorCode::Type
        );
    }
}

#[test]
fn failed_opening_keeps_rng_prefix_and_unpassed_resources_and_allows_retry() {
    let k = keys(1);
    let state = private_state(&k, &table(&[2, 3]));
    let mut backend = ark_backend(None);
    let first = backend.issue_rng(domain(), 3).unwrap();
    let suffix = backend.issue_rng(domain(), 4).unwrap();
    let outside = backend.issue_rng(domain(), 5).unwrap();
    let suffix_before = backend.observe(token(&suffix)).unwrap();
    let outside_before = backend.observe(token(&outside)).unwrap();
    let bytes = program(
        None,
        &[
            ("state", "opening_state"),
            ("p", "point"),
            ("rng", "rng"),
            ("suffix", "rng"),
        ],
        vec![
            op("prefix", "arkworks/random.draw", &["rng"], &["r", "next"]),
            op(
                "open",
                "arkworks/pcs.open",
                &["state", "p"],
                &["y", "proof"],
            ),
            op(
                "suffix",
                "arkworks/random.draw",
                &["suffix"],
                &["r2", "next2"],
            ),
        ],
        &["rng", "rng"],
        &["next", "next2"],
    );
    let (failed, backend) = run(
        &bytes,
        backend,
        vec![state.clone(), point(&[]), first.clone(), suffix.clone()],
    );
    assert_eq!(code(&failed.unwrap_err()), "refused:arity-mismatch");
    let prefix = backend.observe(token(&first)).unwrap();
    assert_eq!(
        (prefix.generation, prefix.draw_count, prefix.budget),
        (1, 1, 2)
    );
    assert_eq!(backend.observe(token(&suffix)).unwrap(), suffix_before);
    assert_eq!(backend.observe(token(&outside)).unwrap(), outside_before);
    assert_eq!(backend.active_frames(), 0);
    let (out, backend) = run(&open_program(), backend, vec![state, point(&[7])]);
    assert_eq!(scalar(&out.unwrap()[0]), Scalar::from(9u64));
    assert_eq!(backend.observe(token(&outside)).unwrap(), outside_before);
}

struct OutputLimit {
    inner: NativeBackend,
    bytes: usize,
}
impl Backend for OutputLimit {
    type Value = Value;
    fn binding_signature(
        &self,
        binding: &zkc_runtime::interactive::OperationBinding,
    ) -> Option<zkc_runtime::interactive::BoundSignature> {
        self.inner.binding_signature(binding)
    }
    fn validate_value(&self, v: &Value) -> Result<(), BackendError> {
        self.inner.validate_value(v)
    }
    fn enter_frame(&mut self, f: &Frame, args: &[Value]) -> Result<(), BackendError> {
        self.inner.enter_frame(f, args)
    }
    fn leave_frame(&mut self, f: &Frame, e: FrameExit, args: &[Value]) -> Result<(), BackendError> {
        self.inner.leave_frame(f, e, args)
    }
    fn apply(&mut self, i: &Invocation<'_>, args: &[Value]) -> Result<Vec<Value>, BackendError> {
        self.inner.apply(
            &Invocation {
                max_output_bytes: i.max_output_bytes.min(self.bytes),
                ..*i
            },
            args,
        )
    }
}

#[test]
fn retention_includes_original_capacity_and_key_and_preflights_both_commit_outputs() {
    let k = keys(1);
    let mut data = Vec::with_capacity(4096);
    data.extend([2u64, 3].map(Scalar::from));
    let t = Value::Table(Arc::new(
        zkc_arkworks::Table::from_logical_vec(data, &Policy::default().ark_bounds()).unwrap(),
    ));
    let state = private_state(&k, &t);
    let pk = Value::ProverKey(Arc::new(k.prover_key().clone()));
    assert!(t.retained_bytes() >= 4096 * std::mem::size_of::<Scalar>());
    assert!(state.retained_bytes() >= t.retained_bytes() + pk.retained_bytes());
    assert_eq!(state.retained_bytes(), state.clone().retained_bytes());
    let backend = NativeBackend::new(
        Policy {
            max_value_bytes: state.retained_bytes() - 1,
            ..Policy::default()
        },
        entry(None),
        None,
    )
    .unwrap();
    assert_eq!(
        backend.validate_value(&state).unwrap_err().code,
        "exhausted:output-bytes"
    );
    let bytes = program(
        None,
        &[("pk", "prover_key"), ("t", "table")],
        vec![op(
            "commit",
            "arkworks/pcs.commit",
            &["pk", "t"],
            &["c", "s"],
        )],
        &["commitment", "opening_state"],
        &["c", "s"],
    );
    let Value::OpeningState(s) = &state else {
        panic!()
    };
    let required = state.retained_bytes()
        + Value::Commitment(Arc::new(s.commitment().clone())).retained_bytes();
    for available in [required - 1, required] {
        let (out, b) = run(
            &bytes,
            OutputLimit {
                inner: ark_backend(None),
                bytes: available,
            },
            vec![pk.clone(), t.clone()],
        );
        if available < required {
            assert_eq!(code(&out.unwrap_err()), "exhausted:output-bytes");
        } else {
            let out = out.unwrap();
            assert_eq!(
                out.iter().map(RuntimeValue::retained_bytes).sum::<usize>(),
                required
            );
        }
        assert_eq!(b.inner.active_frames(), 0);
    }
    let proof_required = 512 + 256 + 192;
    let (failed, backend) = run(
        &open_program(),
        OutputLimit {
            inner: ark_backend(None),
            bytes: proof_required - 1,
        },
        vec![state.clone(), point(&[7])],
    );
    assert_eq!(code(&failed.unwrap_err()), "exhausted:output-bytes");
    assert_eq!(backend.inner.active_frames(), 0);
    assert!(
        run(&open_program(), ark_backend(None), vec![state, point(&[7])])
            .0
            .is_ok()
    );
}
