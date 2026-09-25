use super::*;
use std::sync::Arc;
use zkc_arkworks::{GroupPoint, Keys, Scalar};
use zkc_backends::{Domain, EntryPolicy, NativeBackend, Policy, PublicInputs};

#[test]
fn response_bounds_cover_actual_maximum_public_vectors_and_mixed_outputs() {
    let policy = Policy::default();
    let keys = Keys::setup_for_development(1, &policy.ark_bounds()).unwrap();
    let backend = NativeBackend::new(
        policy,
        EntryPolicy::new(
            Domain::new("V", "s", "main", None),
            Some(1),
            PublicInputs::LocalOnly,
        ),
        Some(keys.verifier_key().clone()),
    )
    .unwrap();
    let table = Value::table(&[Scalar::from(0); 2], &policy).unwrap();
    let Value::Table(t) = &table else {
        unreachable!()
    };
    let committed = keys.prover_key().commit(t).unwrap();
    let (_, proof) = committed.open(&[Scalar::from(0)]).unwrap();
    let values = vec![
        Value::Field(Scalar::from(0)),
        Value::Bool(false),
        Value::Curve(GroupPoint::generator()),
        Value::Round([Scalar::from(0); 3]),
        Value::point(vec![Scalar::from(0); 16], &policy).unwrap(),
        Value::table(&vec![Scalar::from(0); 65536], &policy).unwrap(),
        Value::groups(&vec![GroupPoint::generator(); 4096], &policy).unwrap(),
        Value::Commitment(Arc::new(committed.commitment().clone())),
        Value::Proof(Arc::new(proof)),
        Value::VerifierKey(Arc::new(keys.verifier_key().clone())),
    ];
    let observed = Observed {
        inner: backend,
        validator: "V".into(),
        format: ArtifactFormat::ExplicitBindings,
        origins: BTreeMap::new(),
        source_map: None,
        events: vec![],
        event_bytes: 0,
        trace: TraceMode::Full,
    };
    let req = json!([
        "zkc.logical-origin/2",
        "a\\\"é\n".repeat(128),
        "main",
        [["loop", "x", "99999"]]
    ]);
    for a in &values {
        for b in &values {
            let outputs = vec![a.clone(), b.clone()];
            let bound = response_bound(
                &req,
                &[a.physical_type(), b.physical_type()],
                observed.format,
            )
            .unwrap();
            let actual = json_size(&json!([
                "response",
                req,
                observed
                    .values(&outputs, &[a.physical_type(), b.physical_type()])
                    .unwrap()
            ]))
            .unwrap();
            assert!(
                actual <= bound,
                "{:?} {:?}: {actual}>{bound}",
                a.ty(),
                b.ty()
            );
        }
    }
    for nominal in [
        "rng:bls12-381.fr",
        "nonce:bls12-381.fr",
        "transcript:merlin3.bls12-381.fr64be/1",
        "opening_state:multilinear.kzg.bls12-381/1",
        "prover_key:multilinear.kzg.bls12-381/1",
    ] {
        let ty = PhysicalType::default_for(LogicalType::parse(nominal).unwrap());
        assert!(response_bound(&req, &[ty], observed.format).is_err());
    }
    assert_eq!(
        response_bound(&req, &[], observed.format).unwrap(),
        json_size(&json!(["response", req, []])).unwrap()
    );
}

#[test]
fn reservation_exact_byte_boundary_is_nonmutating_on_refusal() {
    let backend = NativeBackend::new(
        Policy::default(),
        EntryPolicy::new(
            Domain::new("V", "s", "main", None),
            None,
            PublicInputs::LocalOnly,
        ),
        None,
    )
    .unwrap();
    let mut observed = Observed {
        inner: backend,
        validator: "V".into(),
        format: ArtifactFormat::ExplicitBindings,
        origins: BTreeMap::new(),
        source_map: None,
        events: vec![],
        event_bytes: INPUT_LIMIT - 100,
        trace: TraceMode::Full,
    };
    assert!(observed.reserve(100, 3).is_ok());
    assert_eq!(observed.event_bytes, INPUT_LIMIT - 100);
    assert!(observed.events.is_empty());
    assert_eq!(
        observed.reserve(101, 3).unwrap_err().code,
        "exhausted:observer-bytes"
    );
    assert_eq!(observed.event_bytes, INPUT_LIMIT - 100);
    assert!(observed.events.is_empty());
    assert_eq!(
        observed.reserve(usize::MAX, 3).unwrap_err().code,
        "exhausted:observer-bytes"
    );
}

#[test]
fn disabled_trace_preserves_backend_failures_and_custody_but_omits_observer_budget() {
    use zkc_runtime::interactive::{Action, Runner, StopKind, admit_supplied};
    let source = serde_json::to_vec(&json!([
        "zkc.participants/1",
        [["require", "control.require", [], "arkworks/control.require"]],
        "physical",
        [[
            "function",
            "guard",
            [["x", "bool@native.bool/1"]],
            ["bool@native.bool/1"],
            [["op", "check", "require", [], ["x"], []], ["return", ["x"]]],
            ["guard", []]
        ]],
        [[
            "participant",
            "validator",
            "instance",
            "V",
            [],
            [["x", "bool@native.bool/1"]],
            ["bool@native.bool/1"],
            [
                ["local", "step", "guard", ["x"], ["result"]],
                ["return", ["result"]]
            ]
        ]],
        [["entry", "main", [["V", "validator"]]]]
    ]))
    .unwrap();
    for (trace, input, used, expected) in [
        (TraceMode::Full, 1, 0, None),
        (TraceMode::None, 1, 0, None),
        (TraceMode::Full, 0, 0, Some("rejected:require")),
        (TraceMode::None, 0, 0, Some("rejected:require")),
        (
            TraceMode::Full,
            1,
            INPUT_LIMIT,
            Some("exhausted:observer-bytes"),
        ),
        (TraceMode::None, 1, INPUT_LIMIT, None),
    ] {
        let backend = NativeBackend::new(
            Policy::default(),
            EntryPolicy::new(
                Domain::new("V", "s", "main", None),
                None,
                PublicInputs::LocalOnly,
            ),
            None,
        )
        .unwrap();
        let admitted = admit_supplied(&source, &backend).unwrap();
        let observed = Observed {
            inner: backend,
            validator: "V".into(),
            format: ArtifactFormat::ExplicitBindings,
            origins: BTreeMap::from([(
                ("guard".into(), "check".into()),
                SourceOp {
                    origin: vec![
                        "instance".into(),
                        "V".into(),
                        "guard".into(),
                        "check".into(),
                        "".into(),
                    ],
                    kernel: "control.require".into(),
                    attrs: vec![],
                    arguments: vec![],
                    classification: "original".into(),
                },
            )]),
            source_map: Some(zkc_runtime::interactive::SourceMap {
                ports: vec![],
                calls: vec![zkc_runtime::interactive::CallMapping {
                    instance: "instance".into(),
                    role: "V".into(),
                    site: "step".into(),
                    source_function: "guard".into(),
                    function: "guard".into(),
                }],
            }),
            events: vec![],
            event_bytes: used,
            trace,
        };
        let mut runner = Runner::new(
            &admitted,
            "main",
            "V",
            "s",
            observed,
            vec![Value::Bool(input != 0)],
        )
        .unwrap_or_else(|e| panic!("{}", e.error));
        let Action::Local(action) = runner.poll() else {
            panic!("missing local action")
        };
        runner.execute_local(&action.cut).unwrap();
        match (runner.poll(), expected) {
            (Action::Returned(values), None) => {
                assert!(matches!(&values[..], [Value::Bool(true)]));
            }
            (Action::Stopped(stop), Some(code)) => {
                let StopKind::Backend(error) = stop.kind else {
                    panic!("unexpected stop")
                };
                assert_eq!(error.code, code);
            }
            other => panic!("unexpected outcome: {other:?}"),
        }
        assert_eq!(runner.backend().inner().active_frames(), 0);
        if trace == TraceMode::None {
            assert!(runner.backend().events().is_empty());
            assert_eq!(runner.backend().event_bytes, used);
        } else if used == 0 {
            assert_eq!(
                runner.backend().events().len(),
                if input == 0 { 1 } else { 2 }
            );
        }
    }
}

#[test]
fn diagnostic_and_transcript_exhaustion_have_distinct_consumption_boundaries() {
    use zkc_runtime::interactive::{Action, Runner, StopKind, admit_supplied};
    let attrs = ["Source", "step", "Draw", "draw", "V"];
    let source = serde_json::to_vec(&json!([
        "zkc.participants/1",
        [[
            "challenge_binding",
            "transcript.challenge",
            ["merlin3.bls12-381.fr64be/1"],
            "arkworks/transcript.challenge"
        ]],
        "physical",
        [[
            "function",
            "draw",
            [["t", "transcript:merlin3.bls12-381.fr64be/1@host.resource/1"]],
            [
                "field:bls12-381.fr@arkworks.fr/1",
                "transcript:merlin3.bls12-381.fr64be/1@host.resource/1"
            ],
            [
                [
                    "op",
                    "challenge",
                    "challenge_binding",
                    attrs,
                    ["t"],
                    ["r", "next"]
                ],
                ["return", ["r", "next"]]
            ],
            ["draw", []]
        ]],
        [[
            "participant",
            "validator",
            "instance",
            "V",
            [],
            [["t", "transcript:merlin3.bls12-381.fr64be/1@host.resource/1"]],
            [
                "field:bls12-381.fr@arkworks.fr/1",
                "transcript:merlin3.bls12-381.fr64be/1@host.resource/1"
            ],
            [
                ["local", "step", "draw", ["t"], ["result", "next"]],
                ["return", ["result", "next"]]
            ]
        ]],
        [["entry", "main", [["V", "validator"]]]]
    ]))
    .unwrap();
    let root = logical::encode_tree(&json!(["observer-budget-test"])).unwrap();
    for trace in [TraceMode::Full, TraceMode::None] {
        for (used, budget) in [(0, 1), (0, 0), (INPUT_LIMIT - 1, 1)] {
            let domain = Domain::new("V", "s", "main", None);
            let mut backend = NativeBackend::new(
                Policy::default(),
                EntryPolicy::new(domain.clone(), None, PublicInputs::LocalOnly),
                None,
            )
            .unwrap();
            let transcript = backend.issue_transcript(domain, budget, &root).unwrap();
            let Value::Transcript(token) = &transcript else {
                panic!("expected transcript")
            };
            let token = token.clone();
            let admitted = admit_supplied(&source, &backend).unwrap();
            let observed = Observed {
                inner: backend,
                validator: "V".into(),
                format: ArtifactFormat::ExplicitBindings,
                origins: BTreeMap::from([(
                    ("draw".into(), "challenge".into()),
                    SourceOp {
                        origin: vec![],
                        kernel: "transcript.challenge".into(),
                        attrs: attrs.iter().map(|s| (*s).into()).collect(),
                        arguments: vec![],
                        classification: "construction".into(),
                    },
                )]),
                source_map: Some(zkc_runtime::interactive::SourceMap {
                    ports: vec![],
                    calls: vec![zkc_runtime::interactive::CallMapping {
                        instance: "instance".into(),
                        role: "V".into(),
                        site: "step".into(),
                        source_function: "draw".into(),
                        function: "draw".into(),
                    }],
                }),
                events: vec![],
                event_bytes: used,
                trace,
            };
            let mut runner = Runner::new(&admitted, "main", "V", "s", observed, vec![transcript])
                .unwrap_or_else(|e| panic!("{}", e.error));
            let Action::Local(action) = runner.poll() else {
                panic!("missing draw")
            };
            runner.execute_local(&action.cut).unwrap();
            let diagnostic_stop = trace == TraceMode::Full && used != 0;
            let expected = if diagnostic_stop {
                Some("exhausted:observer-bytes")
            } else if budget == 0 {
                Some("exhausted:resource-budget")
            } else {
                None
            };
            match (runner.poll(), expected) {
                (Action::Returned(values), None) => assert_eq!(values.len(), 2),
                (Action::Stopped(stop), Some(code)) => {
                    let StopKind::Backend(error) = stop.kind else {
                        panic!("unexpected stop")
                    };
                    assert_eq!(error.code, code);
                }
                other => panic!("unexpected outcome: {other:?}"),
            }
            let state = runner.backend().inner().observe(&token).unwrap();
            assert_eq!(
                (state.generation, state.draw_count, state.budget),
                if diagnostic_stop {
                    (0, 0, 1)
                } else {
                    (1, 1, 0)
                }
            );
            assert_eq!(runner.backend().inner().active_frames(), 0);
            let events = runner.backend().events();
            if trace == TraceMode::None || diagnostic_stop {
                assert!(events.is_empty());
            } else {
                assert_eq!(events[0][0], "request");
                assert_eq!(events.len(), if budget == 0 { 1 } else { 3 });
                if budget != 0 {
                    assert_eq!(events[1][0], "challenge");
                    assert_eq!(events[2][0], "response");
                }
            }
        }
    }
}

// Capture an internal producer result without admitting a view at a function
// boundary. Stop before the maximum-size consumer: this test measures diagnostic
// bounds, while backend integration tests execute all contractions.
struct Capture {
    inner: NativeBackend,
    view: Option<Value>,
}
impl Backend for Capture {
    type Value = Value;
    fn binding_signature(
        &self,
        binding: &zkc_runtime::interactive::OperationBinding,
    ) -> Option<zkc_runtime::interactive::BoundSignature> {
        self.inner.binding_signature(binding)
    }
    fn validate_value(&self, v: &Value) -> std::result::Result<(), BackendError> {
        self.inner.validate_value(v)
    }
    fn enter_frame(&mut self, f: &Frame, v: &[Value]) -> std::result::Result<(), BackendError> {
        self.inner.enter_frame(f, v)
    }
    fn leave_frame(
        &mut self,
        f: &Frame,
        e: FrameExit,
        v: &[Value],
    ) -> std::result::Result<(), BackendError> {
        self.inner.leave_frame(f, e, v)
    }
    fn apply(
        &mut self,
        i: &Invocation<'_>,
        v: &[Value],
    ) -> std::result::Result<Vec<Value>, BackendError> {
        if self.view.is_some() {
            return Err(BackendError::new("test-diagnostic-stop"));
        }
        let values = self.inner.apply(i, v)?;
        self.view = Some(values[0].clone());
        Ok(values)
    }
}

#[test]
fn diagonal_diagnostics_retain_both_backings_and_never_claim_a_vector_codec() {
    use zkc_runtime::interactive::{Action, OperationBinding, Runner, admit_supplied};
    for dalek in [false, true] {
        let policy = Policy::default();
        let make = || {
            NativeBackend::new(
                policy,
                EntryPolicy::new(
                    Domain::new("V", "s", "main", None),
                    None,
                    PublicInputs::LocalOnly,
                ),
                None,
            )
            .unwrap()
        };
        let n = if dalek {
            policy.max_groups
        } else {
            policy.max_table_elements
        };
        let factors = if dalek {
            Value::ristretto_vector(&vec![zkc_backends::RistrettoScalar::ONE; n], &policy).unwrap()
        } else {
            Value::vector(&vec![Scalar::from(1); n], &policy).unwrap()
        };
        let backing = if dalek {
            Value::ristretto_groups(
                &vec![curve25519_dalek::constants::RISTRETTO_BASEPOINT_POINT; n],
                &policy,
            )
            .unwrap()
        } else {
            Value::vector(&vec![Scalar::from(2); n], &policy).unwrap()
        };
        let contract = if dalek {
            "curve.scale_each"
        } else {
            "vector.mul"
        };
        let binding = OperationBinding {
            contract: contract.into(),
            arguments: vec![
                if dalek {
                    "ristretto255.group"
                } else {
                    "bls12-381.fr"
                }
                .into(),
            ],
            implementation: format!(
                "{}-diagonal/{contract}",
                if dalek { "dalek" } else { "arkworks" }
            ),
        };
        let sig = binding.signature().unwrap();
        let out = sig.outputs[0].clone();
        let consumer = if dalek { "curve.msm" } else { "vector.dot" };
        let result = if dalek {
            "group:ristretto255.group@dalek.ristretto/1"
        } else {
            "field:bls12-381.fr@arkworks.fr/1"
        };
        let ports = json!([
            ["f", factors.physical_type().spelling()],
            ["v", backing.physical_type().spelling()]
        ]);
        let source = json!([
            "zkc.participants/1",
            [
                [
                    "diag",
                    binding.contract,
                    binding.arguments,
                    binding.implementation
                ],
                [
                    "consume",
                    consumer,
                    binding.arguments,
                    format!(
                        "{}-diagonal/{consumer}",
                        if dalek { "dalek" } else { "arkworks" }
                    )
                ]
            ],
            "physical",
            [[
                "function",
                "testfn",
                ports,
                [result],
                [
                    ["op", "producer", "diag", [], ["f", "v"], ["out"]],
                    ["op", "consumer", "consume", [], ["f", "out"], ["result"]],
                    ["return", ["result"]]
                ],
                ["testfn", []]
            ]],
            [[
                "participant",
                "actor",
                "instance",
                "V",
                [],
                ports,
                [result],
                [
                    ["local", "local", "testfn", ["f", "v"], ["out"]],
                    ["return", ["out"]]
                ]
            ]],
            [["entry", "main", [["V", "actor"]]]]
        ]);
        let backend = make();
        let admitted = admit_supplied(&serde_json::to_vec(&source).unwrap(), &backend).unwrap();
        let mut runner = Runner::new(
            &admitted,
            "main",
            "V",
            "s",
            Capture {
                inner: backend,
                view: None,
            },
            vec![factors.clone(), backing.clone()],
        )
        .unwrap_or_else(|e| panic!("{}", e.error));
        let Action::Local(a) = runner.poll() else {
            panic!()
        };
        runner.execute_local(&a.cut).unwrap();
        assert!(matches!(runner.poll(), Action::Stopped(_)));
        let captured = runner.into_backend();
        let value = &captured.view.unwrap();
        let observed = Observed {
            inner: captured.inner,
            validator: "V".into(),
            format: ArtifactFormat::ExplicitBindings,
            origins: BTreeMap::new(),
            source_map: None,
            events: vec![],
            event_bytes: 0,
            trace: TraceMode::Full,
        };
        let diagnostic = observed.value(value, out.logical()).unwrap();
        assert_eq!(
            diagnostic,
            json!([
                "zkc.diagonal-observation/1",
                out.logical().spelling(),
                observed
                    .value(&factors, factors.physical_type().logical())
                    .unwrap(),
                observed
                    .value(&backing, backing.physical_type().logical())
                    .unwrap()
            ])
        );
        assert_eq!(
            observed.inner.encode(value).unwrap_err().code,
            "refused:nonserializable"
        );
        let request = json!(["original", contract]);
        assert!(
            json_size(&json!(["response", request, [diagnostic]])).unwrap()
                <= response_bound(&request, &[out], observed.format).unwrap()
        );
    }
}

#[test]
fn static_observer_refuses_local_control_but_unobserved_artifact_body_executes() {
    use zkc_runtime::interactive::{Action, Runner, admit_supplied};
    let make_backend = || {
        NativeBackend::new(
            Policy::default(),
            EntryPolicy::new(
                Domain::new("V", "s", "main", None),
                None,
                PublicInputs::LocalOnly,
            ),
            None,
        )
        .unwrap()
    };
    let body = json!([
        [
            "if",
            "choose",
            "x",
            ["x"],
            [
                ["op", "yes", "control.require", [], ["x"], []],
                ["yield", ["x"]]
            ],
            [
                ["op", "no", "control.require", [], ["x"], []],
                ["yield", ["x"]]
            ],
            ["answer"]
        ],
        ["return", ["answer"]]
    ]);
    let function = json!([
        "function",
        "guard",
        [["x", "bool@native.bool/1"]],
        ["bool@native.bool/1"],
        body,
        ["guard", []]
    ]);
    let bytes = serde_json::to_vec(&json!([
        "zkc.participants/1",
        [[
            "control.require",
            "control.require",
            [],
            "arkworks/control.require"
        ]],
        "physical",
        [function],
        [[
            "participant",
            "validator",
            "instance",
            "V",
            [],
            [["x", "bool@native.bool/1"]],
            ["bool@native.bool/1"],
            [
                ["local", "run", "guard", ["x"], ["out"]],
                ["return", ["out"]]
            ]
        ]],
        [["entry", "main", [["V", "validator"]]]]
    ]))
    .unwrap();
    let admitted = admit_supplied(&bytes, &make_backend()).unwrap();
    // Construction checking is independently tested at CheckedBundle::load;
    // this fixture exercises the post-check observer admission boundary.
    let bundle = CheckedBundle {
        source: json!([]),
        common: json!(["zkc.protocol/1", [], [function], [], [], []]),
        descriptor: json!([]),
        identity: None,
        manifest: json!([]),
        admitted: admitted.clone(),
        ports: vec![],
        generated_ports: vec![],
        entry: "main".into(),
        producer: "P".into(),
        validator: "V".into(),
        selected_rng: "r".into(),
        acceptance: 0,
    };
    match Observed::new(make_backend(), &bundle, TraceMode::Full) {
        Ok(_) => panic!("static observer accepted dynamic local body"),
        Err(e) => assert_eq!(e, "artifact-observer-local-control-unsupported"),
    }
    let observed = Observed::new(make_backend(), &bundle, TraceMode::None).unwrap();
    let mut runner = Runner::new(
        &admitted,
        "main",
        "V",
        "s",
        observed,
        vec![Value::Bool(true)],
    )
    .unwrap_or_else(|_| panic!());
    let Action::Local(local) = runner.poll() else {
        panic!()
    };
    runner.execute_local(&local.cut).unwrap();
    assert!(matches!(runner.poll(), Action::Returned(_)));
    let observed = runner.into_backend();
    assert!(observed.events().is_empty());
    assert_eq!(observed.inner().active_frames(), 0);
}
