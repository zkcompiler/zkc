//! Selected canonical payloads through independently linked installed handlers.
mod common;
use common::{domain, finish};
use serde_json::{Value as Json, json};
use zkc_cpu::{
    Bls12381G2, Capability, CapabilityObservation, CpuBackend, CpuOperation, EntryPolicy,
    FieldArray, G1, Policy, Scalar, Sequence, Value, cpu_contracts,
};
use zkc_runtime::vm::Value as _;
use zkc_runtime::{interpreter::Runner, vm::*};

const OBSERVE: &str = "transcript.native.indexed.observe.data";
const DRAW: &str = "transcript.native.indexed.challenge";
fn backend(policy: Policy) -> CpuBackend {
    CpuBackend::new(policy, EntryPolicy::new(domain(), None), Default::default()).unwrap()
}
fn token(value: &Value) -> &Capability {
    let Value::Transcript(token) = value else {
        panic!("transcript")
    };
    token
}
fn root() -> Vec<u8> {
    zkc_format::logical::encode_tree(&json!(["installed-transcript-fixture"])).unwrap()
}
fn attributes(suite: Identity, message: bool) -> Vec<String> {
    let event = if message {
        json!(["message", "Source", "message", "Schema", "P", "V"])
    } else {
        json!([
            "query",
            "Source",
            "draw",
            "input_0",
            format!("random.{}/0", suite.scalar_field().unwrap().name()),
            "draw",
            "V"
        ])
    };
    vec![zkc_test_support::hex(
        &zkc_format::logical::encode_tree(&json!([
            "zkc.native-origin-template/0",
            "main",
            [],
            [],
            event
        ]))
        .unwrap(),
    )]
}
fn declaration(suite: Identity, payload: &PhysicalType, selected: bool) -> OperationBinding {
    OperationBinding {
        contract: OBSERVE.into(),
        arguments: vec![suite.name().into(), payload.logical().spelling()],
        implementation: format!("{}/{OBSERVE}", suite.provider().unwrap()),
        physical_arguments: if selected {
            vec![payload.spelling()]
        } else {
            vec![]
        },
    }
}
fn row(name: &str, binding: &OperationBinding) -> Json {
    json!([
        name,
        binding.contract,
        binding.arguments,
        binding.implementation,
        binding.physical_arguments
    ])
}
fn program(suite: Identity, payload: &PhysicalType, selected: bool, draws: bool) -> Program {
    let observe = declaration(suite, payload, selected);
    let signature = cpu_contracts().resolve(observe.clone()).unwrap();
    let actual = backend(Policy::default())
        .prepare_binding(&observe)
        .unwrap();
    assert_eq!(actual.signature(), signature.signature());
    assert_eq!(actual.implementation_id(), signature.implementation_id());
    assert_eq!(actual.requirements(), signature.requirements());
    let ports: Vec<_> = signature
        .signature()
        .inputs
        .iter()
        .zip(["t", "v", "coordinates"])
        .map(|(ty, name)| json!([name, ty.spelling()]))
        .collect();
    let mut rows = vec![row("observe", &observe)];
    let mut body = vec![json!([
        "op",
        "observe",
        "observe",
        attributes(suite, true),
        ["t", "v", "coordinates"],
        ["t1"]
    ])];
    let mut outputs = vec![signature.signature().outputs[0].spelling()];
    let mut names = vec!["t1"];
    if draws {
        let draw = OperationBinding {
            contract: DRAW.into(),
            arguments: vec![suite.name().into()],
            implementation: format!("{}/{DRAW}", suite.provider().unwrap()),
            physical_arguments: vec![],
        };
        let signature = cpu_contracts().resolve(draw.clone()).unwrap();
        rows.push(row("draw", &draw));
        for (site, input, value, output) in
            [("first", "t1", "c1", "t2"), ("second", "t2", "c2", "t3")]
        {
            body.push(json!([
                "op",
                site,
                "draw",
                attributes(suite, false),
                [input, "coordinates"],
                [value, output]
            ]));
        }
        outputs = vec![
            signature.signature().outputs[0].spelling(),
            signature.signature().outputs[0].spelling(),
            signature.signature().outputs[1].spelling(),
        ];
        names = vec!["c1", "c2", "t3"];
    }
    body.push(json!(["return", names]));
    Program::decode(
        &serde_json::to_vec(&json!([
            "zkc.program/0",
            rows,
            [["function", "f", ports, outputs, body, ["f", []]]],
            [[
                "participant",
                "actor",
                "instance",
                "P",
                ports,
                outputs,
                [
                    ["local", "run", "f", ["t", "v", "coordinates"], names],
                    ["return", names]
                ],
                []
            ]],
            [["entry", "main", [["P", "actor"]]]]
        ]))
        .unwrap(),
        cpu_contracts(),
    )
    .unwrap()
}
fn physical(spelling: &str) -> PhysicalType {
    cpu_contracts().physical_type(spelling).unwrap()
}
fn sequence(element: PhysicalType) -> PhysicalType {
    cpu_contracts()
        .aggregate_type(
            LogicalType::sequence(element.logical().clone()).unwrap(),
            Representation::Sequence,
            vec![element],
        )
        .unwrap()
}
fn samples() -> Vec<(Value, PhysicalType)> {
    let mut samples: Vec<_> = [
        Value::Field(Scalar::from(7)),
        Value::Vector(vec![Scalar::from(0), Scalar::from(7)].into()),
        Value::Curve(G1::generator()),
        Value::Groups(vec![G1::identity(), G1::generator()].into()),
        Value::Bls12381G2(Bls12381G2::generator()),
        Value::Bls12381G2Vector(vec![Bls12381G2::identity(), Bls12381G2::generator()].into()),
    ]
    .into_iter()
    .map(|value| {
        let value_type = value.physical_type();
        let logical = value_type.logical();
        let storage = match logical.identity() {
            Identity::Bls12381Fr => "blst/fr",
            Identity::Bls12381G1 => "blst/g1",
            Identity::Bls12381G2 => "blst/g2",
            _ => unreachable!(),
        };
        let selected = physical(&format!("{}@{storage}", logical.spelling()));
        (value, selected)
    })
    .collect();
    samples.push((
        Value::FieldArray(
            FieldArray::new(
                PhysicalType::default_for(
                    LogicalType::parse("field_array<bls12-381.fr,2>").unwrap(),
                )
                .unwrap(),
                vec![Scalar::from(0), Scalar::from(7)].into(),
            )
            .unwrap(),
        ),
        physical("field_array<bls12-381.fr,2>@blst/field-array[blst/fr]"),
    ));
    let children: Vec<_> = samples.iter().map(|(_, ty)| ty.clone()).collect();
    let logical = LogicalType::parse(&zkc_test_support::variants::logical(
        "TranscriptPayload",
        json!([
            ["empty", []],
            [
                "values",
                children
                    .iter()
                    .map(|ty| ty.logical().spelling())
                    .collect::<Vec<_>>()
            ]
        ]),
    ))
    .unwrap();
    let selected = cpu_contracts()
        .aggregate_type(logical.clone(), Representation::Variant, children)
        .unwrap();
    let default = PhysicalType::default_for(logical).unwrap();
    for (alternative, payload) in [
        (0, vec![]),
        (1, samples.iter().map(|(v, _)| v.clone()).collect()),
    ] {
        samples.push((
            Value::pack_variant(default.clone(), alternative, payload).unwrap(),
            selected.clone(),
        ));
    }
    // The active empty arm still carries every inactive resident child layout.
    let nested_default = sequence(sequence(default));
    let empty = Value::Sequence(
        Sequence::new(
            nested_default.sequence_element().unwrap().clone(),
            vec![],
            &Policy::default(),
        )
        .unwrap(),
    );
    let populated = Value::Sequence(
        Sequence::new(
            nested_default.sequence_element().unwrap().clone(),
            vec![samples[7].0.clone(), samples[8].0.clone()],
            &Policy::default(),
        )
        .unwrap(),
    );
    samples.push((
        Value::Sequence(
            Sequence::new(nested_default, vec![empty, populated], &Policy::default()).unwrap(),
        ),
        sequence(sequence(selected)),
    ));
    samples
}

#[derive(Clone, Copy)]
enum Mode {
    Plain,
    Probe,
    OutputFailure,
    OriginFailure,
    AfterTransition,
}
struct Checked {
    inner: CpuBackend,
    hidden: Value,
    root_frame: Option<Frame>,
    mode: Mode,
    history: Vec<CapabilityObservation>,
}
impl Backend for Checked {
    type Call = ();
    type Checkpoint = ();
    type Value = Value;
    type Operation = CpuOperation;
    fn prepare_binding(&self, b: &OperationBinding) -> Option<Self::Operation> {
        self.inner.prepare_binding(b)
    }
    fn validate_value(&self, v: &Value) -> Result<(), BackendError> {
        self.inner.validate_value(v)
    }
    fn enter_frame(&mut self, f: &Frame, a: &[Value]) -> Result<(), BackendError> {
        if matches!(f.kind(), FrameKind::Entry) {
            self.root_frame = Some(f.clone());
        }
        self.inner.enter_frame(f, a)
    }
    fn leave_frame(&mut self, f: &Frame, exit: FrameExit, a: &[Value]) -> Result<(), BackendError> {
        self.inner.leave_frame(f, exit, a)
    }
    fn apply(
        &mut self,
        op: &CpuOperation,
        i: &Invocation<'_>,
        a: &[Value],
    ) -> Result<Vec<Value>, BackendError> {
        let before = self.inner.observe(token(&a[0])).unwrap();
        let small = Invocation {
            max_output_bytes: 0,
            ..*i
        };
        let mut bad_coordinates = a.to_vec();
        *bad_coordinates.last_mut().unwrap() = Value::Indices(vec![0].into());
        if matches!(self.mode, Mode::Probe) {
            assert_eq!(
                self.inner
                    .apply(op, &small, &bad_coordinates)
                    .unwrap_err()
                    .code,
                "exhausted:output-bytes"
            );
            assert_eq!(
                self.inner.apply(op, i, &bad_coordinates).unwrap_err().code,
                "refused:transcript-origin"
            );
            let bad_attributes: Vec<String> = vec![];
            let malformed = Invocation {
                context: CallContext {
                    attributes: &bad_attributes,
                    ..i.context
                },
                ..small
            };
            assert_eq!(
                self.inner.apply(op, &malformed, a).unwrap_err().code,
                "refused:kernel-attributes"
            );
            let mut hidden = a.to_vec();
            hidden[0] = self.hidden.clone();
            assert_eq!(
                self.inner.apply(op, i, &hidden).unwrap_err().code,
                "refused:capability-out-of-view"
            );
            let inactive = Invocation {
                context: CallContext {
                    frame: self.root_frame.as_ref().unwrap(),
                    ..i.context
                },
                ..*i
            };
            assert_eq!(
                self.inner.apply(op, &inactive, a).unwrap_err().code,
                "refused:inactive-frame"
            );
            if i.binding.declaration().contract == OBSERVE {
                let mut wrong_payload = a.to_vec();
                wrong_payload[1] = Value::Bool(false);
                assert_eq!(
                    self.inner
                        .apply(op, &small, &wrong_payload)
                        .unwrap_err()
                        .code,
                    "refused:kernel-operands"
                );
            }
            assert_eq!(self.inner.observe(token(&a[0])).unwrap(), before);
        }
        if matches!(self.mode, Mode::OutputFailure) {
            return self.inner.apply(op, &small, &bad_coordinates);
        }
        if matches!(self.mode, Mode::OriginFailure) {
            return self.inner.apply(op, i, &bad_coordinates);
        }
        let out = self.inner.apply(op, i, a)?;
        self.history.push(self.inner.observe(token(&a[0])).unwrap());
        if matches!(self.mode, Mode::Probe) {
            assert_eq!(
                self.inner.apply(op, &small, a).unwrap_err().code,
                "refused:capability-stale"
            );
            assert_eq!(
                self.inner.observe(token(&a[0])).unwrap(),
                *self.history.last().unwrap()
            );
        }
        if matches!(self.mode, Mode::AfterTransition) {
            return Err(BackendError::new("refused:injected-after-transition"));
        }
        Ok(out)
    }
}
fn execute(
    suite: Identity,
    value: Value,
    selected: bool,
    policy: Policy,
    budget: u64,
    mode: Mode,
) -> (Result<Vec<Value>, Stop>, Checked, Value) {
    let mut inner = backend(policy);
    let root_token = inner
        .issue_transcript_for(suite, domain(), budget, &root())
        .unwrap();
    let hidden = inner
        .issue_transcript_for(suite, domain(), 8, &root())
        .unwrap();
    let program = program(
        suite,
        &value.physical_type(),
        selected,
        matches!(mode, Mode::Plain | Mode::Probe),
    );
    let checked = Checked {
        inner,
        hidden,
        root_frame: None,
        mode,
        history: vec![],
    };
    program.check_installation(&checked).unwrap();
    let runner = Runner::new(
        &program,
        "main",
        "P",
        "session",
        checked,
        vec![root_token.clone(), value, Value::Indices(vec![].into())],
    )
    .unwrap_or_else(|e| panic!("{}", e.error));
    let (out, checked) = finish(runner);
    assert_eq!(checked.inner.active_frames(), 0);
    (out, checked, root_token)
}

#[test]
fn selected_installed_observations_preserve_canonical_bytes_successors_and_repeated_challenges() {
    let codec = backend(Policy::default());
    for suite in [
        Identity::Merlin3Fr64Be,
        Identity::Merlin3Ristretto64Le,
        Identity::Merlin3KoalaBearExt8,
        Identity::Merlin3BabyBearExt4,
        Identity::Merlin3GoldilocksExt2,
        Identity::Spongefish080KeccakFr64Be,
        Identity::HashChainKeccak256Fr64Be,
        Identity::HashChainKeccak256KoalaBearExt8,
        Identity::HashChainKeccak256KoalaBearExt4,
    ] {
        for (default, selected_type) in samples() {
            let bytes = codec.encode_native_value(&default).unwrap();
            let selected = codec.decode_native_value(&selected_type, &bytes).unwrap();
            assert_eq!(selected.physical_type(), selected_type);
            assert_eq!(codec.encode_native_value(&selected).unwrap(), bytes);
            let (a, baseline, old_a) = execute(
                suite,
                default.clone(),
                false,
                Policy::default(),
                3,
                Mode::Plain,
            );
            let (b, selected, old_b) =
                execute(suite, selected, true, Policy::default(), 3, Mode::Probe);
            let a = a.unwrap();
            let b = b.unwrap();
            assert_eq!(baseline.history, selected.history);
            assert_eq!(
                selected
                    .history
                    .iter()
                    .map(|s| (s.generation, s.draw_count, s.budget))
                    .collect::<Vec<_>>(),
                vec![(1, 1, 2), (2, 2, 1), (3, 3, 0)]
            );
            for n in 0..2 {
                assert_eq!(
                    codec.encode_native_value(&a[n]).unwrap(),
                    codec.encode_native_value(&b[n]).unwrap()
                );
            }
            assert_ne!(
                codec.encode_native_value(&b[0]).unwrap(),
                codec.encode_native_value(&b[1]).unwrap()
            );
            for (checked, old, out) in [(&baseline, &old_a, &a), (&selected, &old_b, &b)] {
                checked
                    .inner
                    .verify_successor(token(old), token(&out[2]))
                    .unwrap();
                assert_eq!(
                    checked.inner.validate_value(old).unwrap_err().code,
                    "refused:capability-stale"
                );
                assert_eq!(
                    checked
                        .inner
                        .observe(token(&checked.hidden))
                        .unwrap()
                        .generation,
                    0
                );
            }
            // Explicitly selecting default storage retains []'s existing meaning.
            let (explicit, checked, _) =
                execute(suite, default, true, Policy::default(), 3, Mode::Plain);
            let explicit = explicit.unwrap();
            assert_eq!(checked.history, baseline.history);
            assert_eq!(
                codec.encode_native_value(&explicit[1]).unwrap(),
                codec.encode_native_value(&a[1]).unwrap()
            );
        }
    }
}

#[test]
fn selected_installed_failures_preserve_preflight_consume_order_and_hidden_custody() {
    let codec = backend(Policy::default());
    let (default, selected_type) = samples().remove(8); // active variant exceeds the root byte length
    let selected = codec
        .decode_native_value(
            &selected_type,
            &codec.encode_native_value(&default).unwrap(),
        )
        .unwrap();
    for value in [default, selected] {
        for (mode, policy, budget, code, transitions) in [
            (
                Mode::OutputFailure,
                Policy {
                    max_wire_bytes: root().len(),
                    ..Policy::default()
                },
                0,
                "exhausted:output-bytes",
                0,
            ),
            (
                Mode::OriginFailure,
                Policy {
                    max_wire_bytes: root().len(),
                    ..Policy::default()
                },
                0,
                "refused:transcript-origin",
                0,
            ),
            (
                Mode::Plain,
                Policy {
                    max_wire_bytes: root().len(),
                    ..Policy::default()
                },
                0,
                "exhausted:native-wire-limit",
                0,
            ),
            (
                Mode::Plain,
                Policy::default(),
                0,
                "exhausted:resource-budget",
                1,
            ),
            (
                Mode::AfterTransition,
                Policy::default(),
                2,
                "refused:injected-after-transition",
                1,
            ),
        ] {
            let (out, checked, old) = execute(
                Identity::Merlin3Fr64Be,
                value.clone(),
                true,
                policy,
                budget,
                mode,
            );
            let stop = out.unwrap_err();
            let StopKind::Backend(error) = stop.kind else {
                panic!("backend stop")
            };
            assert_eq!(error.code, code);
            let observed = checked.inner.observe(token(&old)).unwrap();
            assert_eq!(
                (observed.generation, observed.draw_count, observed.budget),
                (transitions, transitions, budget.saturating_sub(transitions))
            );
            assert_eq!(
                checked
                    .inner
                    .observe(token(&checked.hidden))
                    .unwrap()
                    .generation,
                0
            );
        }
    }
}

#[test]
fn actual_and_expected_metadata_refuse_malformed_owner_schema_and_inactive_codec_selections() {
    let native = backend(Policy::default());
    let (_, payload) = samples().remove(7);
    let valid = declaration(Identity::Merlin3Fr64Be, &payload, true);
    let mut cases = vec![];
    let mut wrong = valid.clone();
    wrong.physical_arguments.push(payload.spelling());
    cases.push(wrong);
    let mut wrong = valid.clone();
    wrong.arguments[1] = "field:bls12-381.fr".into();
    cases.push(wrong);
    let mut wrong = valid.clone();
    wrong.arguments[0] = Identity::Spongefish080KeccakFr64Be.name().into();
    cases.push(wrong);
    let mut wrong = valid.clone();
    wrong.implementation = format!("blst/{OBSERVE}");
    cases.push(wrong);
    let mut wrong = valid.clone();
    wrong.physical_arguments[0] = "field:bls12-381.fr@uninstalled/scalar".into();
    cases.push(wrong);
    let mut wrong = valid.clone();
    wrong.physical_arguments[0].push(' ');
    cases.push(wrong);
    let fixed = physical("fixed_vector<field:bls12-381.fr,2>@blst/fixed-vector[blst/fr]");
    cases.push(declaration(Identity::Merlin3Fr64Be, &fixed, true));
    let diagonal = physical("vector:bls12-381.fr@arkworks.fr-diagonal/0");
    let logical = LogicalType::parse(&zkc_test_support::variants::logical(
        "LocalOnlyInactive",
        json!([["empty", []], ["local", ["vector:bls12-381.fr"]]]),
    ))
    .unwrap();
    let inactive = cpu_contracts()
        .aggregate_type(logical, Representation::Variant, vec![diagonal])
        .unwrap();
    cases.push(declaration(Identity::Merlin3Fr64Be, &inactive, true));
    for wrong in cases {
        assert!(
            native.prepare_binding(&wrong).is_none(),
            "actual: {wrong:?}"
        );
        assert!(
            cpu_contracts().resolve(wrong.clone()).is_err(),
            "expected: {wrong:?}"
        );
    }
    for (contract, args, implementation) in [
        ("field.add", vec!["bls12-381.fr"], "arkworks/field.add"),
        (
            DRAW,
            vec![Identity::Merlin3Fr64Be.name()],
            "arkworks/transcript.native.indexed.challenge",
        ),
        (
            "transcript.observe",
            vec![Identity::Merlin3Fr64Be.name()],
            "arkworks/transcript.observe",
        ),
    ] {
        let wrong = OperationBinding {
            contract: contract.into(),
            arguments: args.into_iter().map(str::to_owned).collect(),
            implementation: implementation.into(),
            physical_arguments: valid.physical_arguments.clone(),
        };
        assert!(native.prepare_binding(&wrong).is_none());
        assert!(cpu_contracts().resolve(wrong).is_err());
    }
    assert_eq!(native.active_frames(), 0);
}

#[test]
fn installation_rejects_a_same_spelling_payload_from_an_independent_catalog() {
    let mut builder = ContractsBuilder::standard();
    let foreign = builder
        .add_representation("blst/fr", LogicalType::parse("field:bls12-381.fr").unwrap())
        .unwrap();
    builder
        .add_wire_permission(foreign.clone(), WireCodec::Native)
        .unwrap();
    let contracts = builder.finish(cpu_contracts().policy());
    let local = physical("field:bls12-381.fr@blst/fr");
    assert_eq!(foreign.spelling(), local.spelling());
    assert_ne!(foreign, local);
    let b = declaration(Identity::Merlin3Fr64Be, &foreign, true);
    let expected = contracts.resolve(b.clone()).unwrap();
    let ports: Vec<_> = expected
        .signature()
        .inputs
        .iter()
        .zip(["t", "v", "coordinates"])
        .map(|(ty, name)| json!([name, ty.spelling()]))
        .collect();
    let bytes = serde_json::to_vec(&json!([
        "zkc.program/0",
        [row("observe", &b)],
        [[
            "function",
            "f",
            ports,
            [expected.signature().outputs[0].spelling()],
            [
                [
                    "op",
                    "observe",
                    "observe",
                    attributes(Identity::Merlin3Fr64Be, true),
                    ["t", "v", "coordinates"],
                    ["next"]
                ],
                ["return", ["next"]]
            ],
            ["f", []]
        ]],
        [],
        []
    ]))
    .unwrap();
    let program = Program::decode(&bytes, &contracts).unwrap();
    assert_eq!(
        backend(Policy::default())
            .with_contracts(contracts)
            .err()
            .unwrap()
            .code,
        "refused:installation-contracts"
    );
    let native = backend(Policy::default());
    let actual = native.prepare_binding(&b).unwrap();
    assert_eq!(actual.signature().inputs[1], local);
    assert_ne!(actual.signature().inputs[1], expected.signature().inputs[1]);
    assert_eq!(
        program.check_installation(&native).unwrap_err().code,
        ErrorCode::Backend
    );
    assert_eq!(native.active_frames(), 0);
}
