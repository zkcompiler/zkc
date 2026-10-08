mod common;
use common::*;
use serde_json::{Value as Json, json};
use zkc_backends::Value;
use zkc_backends::*;
use zkc_runtime::interactive::Identity;
use zkc_runtime::interactive::Value as _;
use zkc_runtime::{interactive::*, logical};

// Independently written fixture encoder; does not use the runtime logical codec.
fn tree(v: &Json) -> Vec<u8> {
    match v {
        Json::String(s) => [
            vec![0],
            (s.len() as u64).to_le_bytes().to_vec(),
            s.as_bytes().to_vec(),
        ]
        .concat(),
        Json::Array(a) => [
            vec![1],
            (a.len() as u64).to_le_bytes().to_vec(),
            a.iter().flat_map(tree).collect(),
        ]
        .concat(),
        _ => panic!("fixture"),
    }
}
fn root() -> Vec<u8> {
    tree(&json!([
        "fixture-root",
        "original-source",
        "descriptor",
        "context",
        "authorized-key"
    ]))
}
fn t(v: &zkc_backends::Value) -> &Capability {
    let zkc_backends::Value::Transcript(t) = v else {
        panic!()
    };
    t
}
fn observe(site: &str, input: &str, output: &str) -> Json {
    json!([
        "op",
        site,
        "transcript.native.indexed.observe.data",
        transcript_attributes("message", "Source", "message", "P", "V"),
        [input, "v", "coordinates"],
        [output]
    ])
}
fn challenge(input: &str, value: &str, output: &str) -> Json {
    json!([
        "op",
        "draw",
        "transcript.native.indexed.challenge",
        transcript_attributes("query", "Source", "draw", "P", "V"),
        [input, "coordinates"],
        [value, output]
    ])
}
fn program1() -> Vec<u8> {
    program(
        &[("t", "transcript"), ("v", "field")],
        vec![observe("observe", "t", "t1"), challenge("t1", "c", "t2")],
        &["field", "transcript"],
        &["c", "t2"],
    )
}
fn origin(path: Json, kind: &str) -> Vec<u8> {
    let event = if kind == "message" {
        json!(["message", "Source", "message", "message", "P", "V"])
    } else {
        json!([
            "query",
            "Source",
            "draw",
            "input_0",
            "random.bls12-381.fr/1",
            "draw",
            "V"
        ])
    };
    let frames = path
        .as_array()
        .unwrap()
        .iter()
        .map(|_| json!(["repeat", "Source", "rounds"]))
        .collect::<Vec<_>>();
    let coordinates = path
        .as_array()
        .unwrap()
        .iter()
        .map(|p| p[2].clone())
        .collect::<Vec<_>>();
    tree(&json!([
        "zkc.native-origin/2",
        "main",
        frames,
        coordinates,
        event
    ]))
}
fn canonical_field(n: u64) -> Vec<u8> {
    let mut b = b"ZKCV\x01\x01".to_vec();
    b.extend(n.to_le_bytes());
    b.extend([0; 24]);
    b
}
fn direct(root: &[u8], paths: &[Json], value: u64) -> Scalar {
    let mut m = merlin::Transcript::new(b"zkc.artifact/1");
    m.append_message(b"binding", root);
    let mut raw = [0; 64];
    for path in paths {
        m.append_message(b"origin", &origin(path.clone(), "message"));
        m.append_message(b"value", &canonical_field(value));
        m.append_message(b"origin", &origin(path.clone(), "challenge"));
        m.challenge_bytes(b"challenge", &mut raw);
    }
    zkc_arkworks::scalar_from_wide_be(&raw)
}
#[test]
fn exact_merlin_runner_match_and_session_role_invariance() {
    let expected = direct(&root(), &[json!([])], 7);
    for (role, session) in [
        ("P", "session"),
        ("V", "other_process"),
        // Nonidentity source-role mapping: formal P/V attrs stay unchanged,
        // while actual frame owner/entry role use these different names.
        ("ActualProver", "producer_worker"),
        ("ActualValidator", "validator_worker"),
    ] {
        let d = Domain::new(role, session, "main", None);
        let mut backend = NativeBackend::new(
            Policy::default(),
            EntryPolicy::new(d.clone(), None),
            Default::default(),
        )
        .unwrap();
        let tok = backend
            .issue_transcript_for(Identity::Merlin3Fr64Be, d, 2, &root())
            .unwrap();
        let old = tok.clone();
        let mut j: Json = serde_json::from_slice(&program1()).unwrap();
        j[4][0][3] = json!(role);
        j[5][0][2][0][0] = json!(role);
        // Generated names have no authority over the source challenge attrs.
        j[3][0][1] = json!("generated_helper");
        j[4][0][7][0][2] = json!("generated_helper");
        let admitted = admit_supplied(&serde_json::to_vec(&j).unwrap(), &backend).unwrap();
        let runner = Runner::new(&admitted, "main", role, session, backend, vec![tok, f(7)])
            .unwrap_or_else(|e| panic!("{}", e.error));
        let (out, backend) = finish(runner);
        let out = out.unwrap();
        assert_eq!(scalar(&out[0]), expected);
        assert_eq!(backend.observe(t(&old)).unwrap().generation, 2);
        assert_eq!(t(&out[1]).generation(), 2);
        assert_eq!(
            backend.validate_value(&old).unwrap_err().code,
            "refused:capability-stale"
        );
        assert_eq!(
            backend
                .encode_native_value(&out[1])
                .unwrap_err()
                .to_string(),
            "native-wire-backend:native-wire-type"
        );
        assert_eq!(
            backend
                .decode_native_value(
                    &zkc_runtime::interactive::PhysicalType::default_for(
                        zkc_runtime::interactive::LogicalType::parse(
                            "transcript:merlin3.bls12-381.fr64be/1"
                        )
                        .unwrap()
                    )
                    .unwrap(),
                    &[]
                )
                .unwrap_err()
                .to_string(),
            "native-wire-backend:native-wire-type"
        );
    }
}
#[test]
fn binding_value_origin_order_reset_and_budget_controls() {
    let expected = direct(&root(), &[json!([])], 7);
    for mutation in 0..8 {
        let mut backend = ark_backend(None);
        let mut root = root();
        let mut j: Json = serde_json::from_slice(&program1()).unwrap();
        let mut value = 7;
        match mutation {
            0 => root = tree(&json!(["other-root"])),
            1 => value = 8,
            2..=6 => {
                let attrs = j[3][0][4][2][3][0].as_str().unwrap();
                let mut template = logical::decode_tree(&zkc_test_support::unhex(attrs)).unwrap();
                let slot = [1, 2, 3, 4, 6][mutation - 2];
                template[4][slot] = json!(match slot {
                    3 => "input_1",
                    4 => "random.ristretto255.scalar/1",
                    _ => "different",
                });
                j[3][0][4][2][3][0] = json!(zkc_test_support::hex(&tree(&template)));
            }
            7 => {
                j[3][0][4][1] = challenge("t", "c", "t1");
                j[3][0][4][2] = observe("after", "t1", "t2");
                j[3][0][4][2][2] = json!(format!(
                    "observe_{}",
                    zkc_test_support::hex(b"field:bls12-381.fr")
                ));
            }
            _ => unreachable!(),
        }
        let tok = backend
            .issue_transcript_for(Identity::Merlin3Fr64Be, domain(), 2, &root)
            .unwrap();
        let (out, _) = run(
            &serde_json::to_vec(&j).unwrap(),
            backend,
            vec![tok, f(value)],
        );
        assert_ne!(scalar(&out.unwrap()[0]), expected);
    }
    let mut backend = ark_backend(None);
    let tok = backend
        .issue_transcript_for(Identity::Merlin3Fr64Be, domain(), 1, &root())
        .unwrap();
    let old = tok.clone();
    let (out, mut backend) = run(&program1(), backend, vec![tok, f(7)]);
    assert_eq!(code(&out.unwrap_err()), "exhausted:resource-budget");
    let state = backend.observe(t(&old)).unwrap();
    assert_eq!(
        (state.generation, state.draw_count, state.budget),
        (2, 2, 0)
    );
    assert_eq!(backend.active_frames(), 0);
    assert!(
        backend
            .issue_transcript_for(
                Identity::Merlin3Fr64Be,
                domain(),
                1,
                b"not a canonical tree"
            )
            .is_err()
    );
}
fn nested() -> Vec<u8> {
    let mut j: Json = serde_json::from_slice(&program1()).unwrap();
    j[4][0][5]
        .as_array_mut()
        .unwrap()
        .push(json!(["n", "index@native.index/1"]));
    j[3][0][2]
        .as_array_mut()
        .unwrap()
        .push(json!(["iteration", "index@native.index/1"]));
    j[1].as_array_mut().unwrap().push(json!([
        "indices.append",
        "indices.append",
        [],
        "native/indices.append"
    ]));
    j[3][0][4][0][5] = json!(["empty_coordinates"]);
    j[3][0][4].as_array_mut().unwrap().insert(
        1,
        json!([
            "op",
            "append_coordinate",
            "indices.append",
            [],
            ["empty_coordinates", "iteration"],
            ["coordinates"]
        ]),
    );
    for index in [2, 3] {
        let mut template = logical::decode_tree(&zkc_test_support::unhex(
            j[3][0][4][index][3][0].as_str().unwrap(),
        ))
        .unwrap();
        template[2] = json!([["repeat", "Source", "rounds"]]);
        j[3][0][4][index][3][0] = json!(zkc_test_support::hex(&tree(&template)));
    }
    j[4][0][7] = json!([
        [
            "loop",
            "rounds",
            ["value", "n", "4", "i"],
            [["cur", "t"], ["answer", "v"]],
            ["v"],
            [
                [
                    "local",
                    "generated_local",
                    "kernel_test",
                    ["cur", "v", "i"],
                    ["c", "next"]
                ],
                ["yield", ["next", "c"]]
            ],
            ["done", "last"]
        ],
        ["return", ["last", "done"]]
    ]);
    serde_json::to_vec(&j).unwrap()
}
#[test]
fn explicit_shared_resources_survive_bounded_loops_and_failures() {
    let mut backend = ark_backend(None);
    let tok = backend
        .issue_transcript_for(Identity::Merlin3Fr64Be, domain(), 8, &root())
        .unwrap();
    let old = tok.clone();
    let paths = (0..4)
        .map(|i| json!([["loop", "rounds", i.to_string()]]))
        .collect::<Vec<_>>();
    let (out, backend) = run(&nested(), backend, vec![tok, f(7), Value::Index(4)]);
    let out = out.unwrap();
    assert_eq!(scalar(&out[0]), direct(&root(), &paths, 7));
    assert_ne!(scalar(&out[0]), direct(&root(), &paths[3..], 7)); // child reset differs
    assert_eq!(backend.observe(t(&old)).unwrap().generation, 8);
    assert_eq!(backend.active_frames(), 0);
    let mut backend = ark_backend(None);
    let tok = backend
        .issue_transcript_for(Identity::Merlin3Fr64Be, domain(), 3, &root())
        .unwrap();
    let old = tok.clone();
    let (out, backend) = run(&nested(), backend, vec![tok, f(7), Value::Index(4)]);
    assert_eq!(code(&out.unwrap_err()), "exhausted:resource-budget");
    assert_eq!(backend.observe(t(&old)).unwrap().generation, 4);
    assert_eq!(backend.active_frames(), 0);
}
#[test]
fn wrong_authority_owner_instance_and_aliases_never_consume() {
    let bytes = program1();
    for wrong in [
        Domain::new("V", "session", "main", None),
        Domain::new("P", "other", "main", None),
        Domain::new("P", "session", "other", None),
        Domain::new("P", "session", "main", Some("other")),
    ] {
        let mut backend = ark_backend(None);
        let tok = backend
            .issue_transcript_for(Identity::Merlin3Fr64Be, wrong, 3, &root())
            .unwrap();
        let old = tok.clone();
        let a = admit_supplied(&bytes, &backend).unwrap();
        let e = Runner::new(&a, "main", "P", "session", backend, vec![tok, f(7)])
            .err()
            .unwrap();
        assert!(matches!(e.error, RuntimeError::Backend(_)));
        assert_eq!(e.backend.observe(t(&old)).unwrap().generation, 0);
        assert_eq!(e.backend.active_frames(), 0);
    }
    let mut issuer = ark_backend(None);
    let tok = issuer
        .issue_transcript_for(Identity::Merlin3Fr64Be, domain(), 3, &root())
        .unwrap();
    let backend = ark_backend(None);
    assert_eq!(
        backend.validate_value(&tok).unwrap_err().code,
        "refused:capability-authority"
    );
    let bytes = program(
        &[("a", "transcript"), ("b", "transcript")],
        vec![],
        &["transcript", "transcript"],
        &["a", "b"],
    );
    let a = admit_supplied(&bytes, &issuer).unwrap();
    let old = tok.clone();
    let e = Runner::new(&a, "main", "P", "session", issuer, vec![tok.clone(), tok])
        .err()
        .unwrap();
    assert_eq!(e.backend.observe(t(&old)).unwrap().generation, 0);
    assert!(
        matches!(e.error,RuntimeError::Backend(BackendError {code}) if code=="refused:capability-alias")
    );
}
#[test]
fn original_rng_remains_separate_and_transcript_is_affine() {
    let mut backend = ark_backend(None);
    let transcript = backend
        .issue_transcript_for(Identity::Merlin3Fr64Be, domain(), 2, &root())
        .unwrap();
    let rng = backend
        .issue_rng_for(Identity::Bls12381Fr, domain(), 3)
        .unwrap();
    let before = backend.observe(token(&rng)).unwrap();
    let (out, backend) = run(&program1(), backend, vec![transcript, f(7)]);
    out.unwrap();
    assert_eq!(backend.observe(token(&rng)).unwrap(), before);
    let mut j: Json = serde_json::from_slice(&program1()).unwrap();
    j[3][0][4][2] = challenge("t", "c", "t2");
    assert_eq!(
        admit_supplied(&serde_json::to_vec(&j).unwrap(), &backend)
            .unwrap_err()
            .code,
        ErrorCode::Ssa
    );
    let mut j: Json = serde_json::from_slice(&program1()).unwrap();
    j[3][0][4][1][3] = json!(["Source"]);
    assert_eq!(
        admit_supplied(&serde_json::to_vec(&j).unwrap(), &backend)
            .unwrap_err()
            .code,
        ErrorCode::Attributes
    );
    assert!(logical::decode_tree(&root()).is_ok()); // syntactic fixture, NOT source correspondence
}

// Trusted test instrumentation gets only Runner-minted Frame values. It probes
// hostile adapter requests without adding a second interpreter or forging frames.
struct Probe {
    inner: NativeBackend,
    hidden: zkc_backends::Value,
    root_frame: Option<Frame>,
    mode: u8,
    checked: bool,
}
impl Backend for Probe {
    type Value = zkc_backends::Value;
    fn binding_signature(
        &self,
        binding: &zkc_runtime::interactive::OperationBinding,
    ) -> Option<zkc_runtime::interactive::BoundSignature> {
        self.inner.binding_signature(binding)
    }
    fn validate_value(&self, v: &Self::Value) -> Result<(), BackendError> {
        self.inner.validate_value(v)
    }
    fn enter_frame(&mut self, f: &Frame, v: &[Self::Value]) -> Result<(), BackendError> {
        if matches!(f.kind(), FrameKind::Entry) {
            self.root_frame = Some(f.clone());
        }
        self.inner.enter_frame(f, v)
    }
    fn leave_frame(
        &mut self,
        f: &Frame,
        e: FrameExit,
        v: &[Self::Value],
    ) -> Result<(), BackendError> {
        self.inner.leave_frame(f, e, v)
    }
    fn apply(
        &mut self,
        i: &Invocation<'_>,
        a: &[Self::Value],
    ) -> Result<Vec<Self::Value>, BackendError> {
        if !i
            .binding
            .declaration()
            .contract
            .starts_with("transcript.native.indexed.")
        {
            return self.inner.apply(i, a);
        }
        if !self.checked {
            self.checked = true;
            if self.mode == 0 {
                let mut hidden = a.to_vec();
                hidden[0] = self.hidden.clone();
                assert_eq!(
                    self.inner.apply(i, &hidden).unwrap_err().code,
                    "refused:capability-out-of-view"
                );
                let wrong_frame = Invocation {
                    frame: self.root_frame.as_ref().unwrap(),
                    ..*i
                };
                assert_eq!(
                    self.inner.apply(&wrong_frame, a).unwrap_err().code,
                    "refused:inactive-frame"
                );
                // The active local frame cannot close its active ancestor.
                let before = self.inner.active_frames();
                assert_eq!(
                    self.inner
                        .leave_frame(self.root_frame.as_ref().unwrap(), FrameExit::Cancelled, &[])
                        .unwrap_err()
                        .code,
                    "refused:frame-exit-order"
                );
                assert_eq!(self.inner.active_frames(), before);
                assert_eq!(
                    self.inner
                        .issue_transcript_for(Identity::Merlin3Fr64Be, domain(), 2, &root())
                        .unwrap_err()
                        .code,
                    "refused:issue-during-frame"
                );
            } else if self.mode == 1 {
                // Output preflight happens BEFORE transcript consumption.
                let small = Invocation {
                    max_output_bytes: 0,
                    ..*i
                };
                return self.inner.apply(&small, a);
            } else {
                // A later backend failure does not undo completed transcript state.
                self.inner.apply(i, a)?;
                return Err(BackendError::new("refused:injected-after-transition"));
            }
        }
        self.inner.apply(i, a)
    }
}
#[test]
fn active_views_preflight_and_post_transition_failure() {
    for mode in 0..3 {
        let mut inner = ark_backend(None);
        let token = inner
            .issue_transcript_for(Identity::Merlin3Fr64Be, domain(), 8, &root())
            .unwrap();
        let old = token.clone();
        let hidden = inner
            .issue_transcript_for(Identity::Merlin3Fr64Be, domain(), 8, &root())
            .unwrap();
        let before = inner.observe(t(&hidden)).unwrap();
        let probe = Probe {
            inner,
            hidden: hidden.clone(),
            root_frame: None,
            mode,
            checked: false,
        };
        let (out, probe) = run(&nested(), probe, vec![token, f(7), Value::Index(4)]);
        let expected = match mode {
            0 => {
                out.unwrap();
                8
            }
            1 => {
                assert_eq!(code(&out.unwrap_err()), "exhausted:output-bytes");
                0
            }
            _ => {
                assert_eq!(code(&out.unwrap_err()), "refused:injected-after-transition");
                1
            }
        };
        assert_eq!(probe.inner.observe(t(&old)).unwrap().generation, expected);
        assert_eq!(probe.inner.observe(t(&hidden)).unwrap(), before);
        assert_eq!(probe.inner.active_frames(), 0);
    }
}
#[test]
fn nested_cancellation_retains_prefix_and_unpassed_resource() {
    let mut backend = ark_backend(None);
    let token = backend
        .issue_transcript_for(Identity::Merlin3Fr64Be, domain(), 8, &root())
        .unwrap();
    let old = token.clone();
    let hidden = backend
        .issue_transcript_for(Identity::Merlin3Fr64Be, domain(), 8, &root())
        .unwrap();
    let before = backend.observe(t(&hidden)).unwrap();
    let mut runner = load(&nested(), backend, vec![token, f(7), Value::Index(4)]);
    while runner.advance_local_control().unwrap() {}
    let Action::Local(local) = runner.poll() else {
        panic!()
    };
    runner.execute_local(&local.cut).unwrap();
    while runner.advance_local_control().unwrap() {}
    let Action::Local(_) = runner.poll() else {
        panic!()
    };
    runner.cancel();
    assert!(matches!(
        runner.poll(),
        Action::Stopped(Stop {
            kind: StopKind::Cancelled,
            ..
        })
    ));
    let backend = runner.into_backend();
    assert_eq!(backend.observe(t(&old)).unwrap().generation, 2);
    assert_eq!(backend.observe(t(&hidden)).unwrap(), before);
    assert_eq!(backend.active_frames(), 0);
}

#[test]
fn public_scalar_group_and_commitment_kinds_observe_ordinary_canonical_wire() {
    // Compare current generated observation bytes with independent Merlin calls.
    // Local-only table, point and round representations cannot be observed.
    let policy = Policy::default();
    let keys = Keys::setup_for_development(1, &policy.ark_bounds()).unwrap();
    let zkc_backends::Value::Table(table_value) = table(&[1, 2]) else {
        panic!()
    };
    let original = keys.prover_key().commit(&table_value).unwrap();
    let (_, proof) = original.open(&[Scalar::from(3)]).unwrap();
    for value in [
        table(&[1, 2]),
        point(&[3]),
        Value::Round([Scalar::from(1); 3]),
    ] {
        let binding = OperationBinding {
            contract: "transcript.native.indexed.observe.data".into(),
            arguments: vec![
                "merlin3.bls12-381.fr64be/1".into(),
                value.physical_type().logical().spelling(),
            ],
            implementation: "arkworks/transcript.native.indexed.observe.data".into(),
        };
        assert!(binding.signature().is_err());
    }
    let values = vec![
        f(7),
        zkc_backends::Value::vector(&[Scalar::from(1), Scalar::from(2)], &policy).unwrap(),
        zkc_backends::Value::Bool(false),
        zkc_backends::Value::Commitment(std::sync::Arc::new(original.commitment().clone())),
        zkc_backends::Value::Proof(std::sync::Arc::new(proof)),
        zkc_backends::Value::Curve(GroupPoint::identity()),
        zkc_backends::Value::groups(&[GroupPoint::generator()], &policy).unwrap(),
    ];
    for value in values {
        let mut backend = NativeBackend::new(
            policy,
            entry(None),
            zkc_backends::SetupRegistry::new(
                vec![keys.verifier_key().clone()],
                &zkc_backends::Policy::default(),
            )
            .unwrap(),
        )
        .unwrap();
        let bytes = backend.encode_native_value(&value).unwrap();
        let tok = backend
            .issue_transcript_for(Identity::Merlin3Fr64Be, domain(), 2, &root())
            .unwrap();
        let mut m = merlin::Transcript::new(b"zkc.artifact/1");
        m.append_message(b"binding", &root());
        m.append_message(b"origin", &origin(json!([]), "message"));
        m.append_message(b"value", &bytes);
        m.append_message(b"origin", &origin(json!([]), "challenge"));
        let mut raw = [0; 64];
        m.challenge_bytes(b"challenge", &mut raw);
        let mut obs = observe("observe", "t", "t1");
        obs[2] = json!("transcript.native.indexed.observe.data");
        let bytes = program(
            &[("t", "transcript"), ("v", value.ty().name())],
            vec![obs, challenge("t1", "c", "t2")],
            &["field", "transcript"],
            &["c", "t2"],
        );
        let (out, _) = run(&bytes, backend, vec![tok, value]);
        assert_eq!(
            scalar(&out.unwrap()[0]),
            zkc_arkworks::scalar_from_wide_be(&raw)
        );
    }
}

#[test]
fn native_contracts_bind_explicit_source_occurrences_not_runtime_frames() {
    fn hex(bytes: &[u8]) -> String {
        bytes.iter().map(|b| format!("{b:02x}")).collect()
    }
    let message = tree(&json!([
        "zkc.native-origin/2",
        "source_entry",
        [["apply", "source_entry", "application"]],
        [],
        ["message", "Round", "commitment", "commitment", "P", "V"]
    ]));
    let query = tree(&json!([
        "zkc.native-origin/2",
        "source_entry",
        [["apply", "source_entry", "application"]],
        [],
        [
            "query",
            "Round",
            "coin",
            "input_0",
            "random.bls12-381.fr/1",
            "draw",
            "V"
        ]
    ]));
    let mut reference = merlin::Transcript::new(b"zkc.artifact/1");
    reference.append_message(b"binding", &root());
    reference.append_message(b"origin", &message);
    reference.append_message(b"value", &canonical_field(7));
    reference.append_message(b"origin", &query);
    let mut wide = [0u8; 64];
    reference.challenge_bytes(b"challenge", &mut wide);
    let expected = zkc_arkworks::scalar_from_wide_be(&wide);
    for role in ["P", "V"] {
        let d = Domain::new(role, "session", "main", None);
        let mut backend = NativeBackend::new(
            Policy::default(),
            EntryPolicy::new(d.clone(), None),
            Default::default(),
        )
        .unwrap();
        let token = backend
            .issue_transcript_for(Identity::Merlin3Fr64Be, d, 2, &root())
            .unwrap();
        let mut program: Json = serde_json::from_slice(&program1()).unwrap();
        for (index, bytes) in [(1, &message), (2, &query)] {
            let mut template = logical::decode_tree(bytes).unwrap();
            template[0] = json!("zkc.native-origin-template/1");
            program[3][0][4][index][3] = json!([hex(&tree(&template))]);
        }
        program[4][0][3] = json!(role);
        program[5][0][2][0][0] = json!(role);
        let admitted = admit_supplied(&serde_json::to_vec(&program).unwrap(), &backend).unwrap();
        let runner = Runner::new(
            &admitted,
            "main",
            role,
            "session",
            backend,
            vec![token, f(7)],
        )
        .unwrap_or_else(|e| panic!("{}", e.error));
        let (outputs, _) = finish(runner);
        assert_eq!(scalar(&outputs.unwrap()[0]), expected);
    }
}
