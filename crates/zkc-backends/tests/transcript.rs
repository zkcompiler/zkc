mod common;
use common::*;
use serde_json::{Value as Json, json};
use zkc_backends::*;
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
        "transcript.observe.field",
        ["Source", "message", "FieldSchema", "P", "V"],
        [input, "v"],
        [output]
    ])
}
fn challenge(input: &str, value: &str, output: &str) -> Json {
    json!([
        "op",
        "draw",
        "transcript.challenge",
        ["Source", "source_call", "OriginalDraw", "source_draw", "V"],
        [input],
        [value, output]
    ])
}
fn program1() -> Vec<u8> {
    program(
        None,
        &[("t", "transcript"), ("v", "field")],
        vec![observe("observe", "t", "t1"), challenge("t1", "c", "t2")],
        &["field", "transcript"],
        &["c", "t2"],
    )
}
fn origin(path: Json, kind: &str) -> Vec<u8> {
    let event = if kind == "message" {
        json!(["message", "Source", "message", "FieldSchema", "P", "V"])
    } else {
        json!([
            "challenge",
            "Source",
            "source_call",
            "OriginalDraw",
            "source_draw",
            "V"
        ])
    };
    tree(&json!([
        "zkc.logical-origin/1",
        "main",
        if path.as_array().unwrap().is_empty() {
            "instance"
        } else {
            "child_instance"
        },
        path,
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
    // Frozen results/fixtures.py: independently encoded trees, direct Merlin,
    // Python big-integer reduction. Does not derive expected bytes via zkc.
    assert_eq!(
        expected,
        parse_decimal(
            "5184094719287578275298844563643071478826837576914294436461907185859582384591"
        )
        .unwrap()
    );

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
            EntryPolicy::new(d.clone(), None, PublicInputs::LocalOnly),
            None,
        )
        .unwrap();
        let tok = backend.issue_transcript(d, 2, &root()).unwrap();
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
            backend.encode_value(&out[1]).unwrap_err().code,
            "refused:nonserializable"
        );
        assert_eq!(
            backend
                .decode_typed_value(
                    zkc_runtime::interactive::PhysicalType::default_for(
                        zkc_runtime::interactive::LogicalType::parse(
                            "transcript:merlin3.bls12-381.fr64be/1"
                        )
                        .unwrap()
                    ),
                    &[]
                )
                .unwrap_err()
                .code,
            "refused:nonserializable"
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
            2..=6 => j[3][0][4][1][3][mutation - 2] = json!("different"),
            7 => {
                j[3][0][4][0] = challenge("t", "c", "t1");
                j[3][0][4][1] = observe("after", "t1", "t2");
            }
            _ => unreachable!(),
        }
        let tok = backend.issue_transcript(domain(), 2, &root).unwrap();
        let (out, _) = run(
            &serde_json::to_vec(&j).unwrap(),
            backend,
            vec![tok, f(value)],
        );
        assert_ne!(scalar(&out.unwrap()[0]), expected);
    }
    let mut backend = ark_backend(None);
    let tok = backend.issue_transcript(domain(), 1, &root()).unwrap();
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
            .issue_transcript(domain(), 1, b"not a canonical tree")
            .is_err()
    );
}
fn nested() -> Vec<u8> {
    let mut j: Json = serde_json::from_slice(&program1()).unwrap();
    j[4] = json!([
        [
            "participant",
            "root",
            "instance",
            "P",
            [],
            [
                ["t", "transcript:merlin3.bls12-381.fr64be/1@host.resource/1"],
                ["v", "field:bls12-381.fr@arkworks.fr/1"]
            ],
            [
                "field:bls12-381.fr@arkworks.fr/1",
                "transcript:merlin3.bls12-381.fr64be/1@host.resource/1"
            ],
            [
                ["call", "first", "child", ["t", "v"], ["c0", "t0"]],
                ["call", "second", "child", ["t0", "v"], ["c1", "t1"]],
                ["return", ["c1", "t1"]]
            ]
        ],
        [
            "participant",
            "child",
            "child_instance",
            "P",
            [],
            [
                ["t", "transcript:merlin3.bls12-381.fr64be/1@host.resource/1"],
                ["v", "field:bls12-381.fr@arkworks.fr/1"]
            ],
            [
                "field:bls12-381.fr@arkworks.fr/1",
                "transcript:merlin3.bls12-381.fr64be/1@host.resource/1"
            ],
            [
                [
                    "loop",
                    "rounds",
                    "2",
                    [["cur", "t"], ["answer", "v"]],
                    ["v"],
                    [
                        [
                            "local",
                            "generated_local",
                            "kernel_test",
                            ["cur", "v"],
                            ["c", "next"]
                        ],
                        ["yield", ["next", "c"]]
                    ],
                    ["done", "last"]
                ],
                ["return", ["last", "done"]]
            ]
        ]
    ]);
    j[5] = json!([["entry", "main", [["P", "root"]]]]);
    serde_json::to_vec(&j).unwrap()
}
#[test]
fn explicit_shared_resources_survive_nested_calls_loops_and_failures() {
    let mut backend = ark_backend(None);
    let tok = backend.issue_transcript(domain(), 8, &root()).unwrap();
    let old = tok.clone();
    let paths = [
        json!([["call", "first", "child_instance"], ["loop", "rounds", "0"]]),
        json!([["call", "first", "child_instance"], ["loop", "rounds", "1"]]),
        json!([
            ["call", "second", "child_instance"],
            ["loop", "rounds", "0"]
        ]),
        json!([
            ["call", "second", "child_instance"],
            ["loop", "rounds", "1"]
        ]),
    ];
    let (out, backend) = run(&nested(), backend, vec![tok, f(7)]);
    let out = out.unwrap();
    assert_eq!(scalar(&out[0]), direct(&root(), &paths, 7));
    assert_ne!(scalar(&out[0]), direct(&root(), &paths[3..], 7)); // child reset differs
    assert_eq!(backend.observe(t(&old)).unwrap().generation, 8);
    assert_eq!(backend.active_frames(), 0);
    let mut backend = ark_backend(None);
    let tok = backend.issue_transcript(domain(), 3, &root()).unwrap();
    let old = tok.clone();
    let (out, backend) = run(&nested(), backend, vec![tok, f(7)]);
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
        let tok = backend.issue_transcript(wrong, 3, &root()).unwrap();
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
    let tok = issuer.issue_transcript(domain(), 3, &root()).unwrap();
    let backend = ark_backend(None);
    assert_eq!(
        backend.validate_value(&tok).unwrap_err().code,
        "refused:capability-authority"
    );
    let bytes = program(
        None,
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
    let transcript = backend.issue_transcript(domain(), 2, &root()).unwrap();
    let rng = backend.issue_rng(domain(), 3).unwrap();
    let before = backend.observe(token(&rng)).unwrap();
    let (out, backend) = run(&program1(), backend, vec![transcript, f(7)]);
    out.unwrap();
    assert_eq!(backend.observe(token(&rng)).unwrap(), before);
    let mut j: Json = serde_json::from_slice(&program1()).unwrap();
    j[3][0][4][1] = challenge("t", "c", "t2");
    assert_eq!(
        admit_supplied(&serde_json::to_vec(&j).unwrap(), &backend)
            .unwrap_err()
            .code,
        ErrorCode::Ssa
    );
    let mut j: Json = serde_json::from_slice(&program1()).unwrap();
    j[3][0][4][0][3] = json!(["Source"]);
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
                        .issue_transcript(domain(), 2, &root())
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
        let token = inner.issue_transcript(domain(), 8, &root()).unwrap();
        let old = token.clone();
        let hidden = inner.issue_transcript(domain(), 8, &root()).unwrap();
        let before = inner.observe(t(&hidden)).unwrap();
        let probe = Probe {
            inner,
            hidden: hidden.clone(),
            root_frame: None,
            mode,
            checked: false,
        };
        let (out, probe) = run(&nested(), probe, vec![token, f(7)]);
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
    let token = backend.issue_transcript(domain(), 8, &root()).unwrap();
    let old = token.clone();
    let hidden = backend.issue_transcript(domain(), 8, &root()).unwrap();
    let before = backend.observe(t(&hidden)).unwrap();
    let mut runner = load(&nested(), backend, vec![token, f(7)]);
    let Action::Local(local) = runner.poll() else {
        panic!()
    };
    runner.execute_local(&local.cut).unwrap();
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
    // Not every observable kind: the registry also offers matrix, vector,
    // polynomial, index, indices and commitments, whose wire is a separate
    // claim. Naming those here would say this test covers them.
    let policy = Policy::default();
    let keys = Keys::setup_for_development(1, &policy.ark_bounds()).unwrap();
    let zkc_backends::Value::Table(table_value) = table(&[1, 2]) else {
        panic!()
    };
    let original = keys.prover_key().commit(&table_value).unwrap();
    let (_, proof) = original.open(&[Scalar::from(3)]).unwrap();
    let values = vec![
        f(7),
        table(&[1, 2]),
        point(&[3]),
        zkc_backends::Value::Round([Scalar::from(1), Scalar::from(2), Scalar::from(3)]),
        zkc_backends::Value::Bool(false),
        zkc_backends::Value::Commitment(std::sync::Arc::new(original.commitment().clone())),
        zkc_backends::Value::Proof(std::sync::Arc::new(proof)),
        zkc_backends::Value::Curve(GroupPoint::identity()),
        zkc_backends::Value::groups(&[GroupPoint::generator()], &policy).unwrap(),
    ];
    for value in values {
        let mut backend =
            NativeBackend::new(policy, entry(None), Some(keys.verifier_key().clone())).unwrap();
        let bytes = backend.encode_value(&value).unwrap();
        let tok = backend.issue_transcript(domain(), 2, &root()).unwrap();
        let mut m = merlin::Transcript::new(b"zkc.artifact/1");
        m.append_message(b"binding", &root());
        m.append_message(b"origin", &origin(json!([]), "message"));
        m.append_message(b"value", &bytes);
        m.append_message(b"origin", &origin(json!([]), "challenge"));
        let mut raw = [0; 64];
        m.challenge_bytes(b"challenge", &mut raw);
        let mut obs = observe("observe", "t", "t1");
        obs[2] = json!(format!("arkworks/transcript.observe.{}", value.ty().name()));
        let bytes = program(
            None,
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
