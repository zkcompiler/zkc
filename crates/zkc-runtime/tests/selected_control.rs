//! Hand-authored Program/schedule controls independent of native production.
#[path = "support/host.rs"]
mod host;
use host::{BOOL, Host, TestValue};
use serde_json::{Value as Json, json};
use zkc_runtime::{
    host::joint::{
        self, Bundle, BundleError, BundleLimits, NoHooks, Outcome, RoleInput, RunLimits,
    },
    interpreter::Runner,
    vm::{Action, Contracts, ErrorCode, ExecutionPolicy, PathElement, PhysicalType, Program},
};

fn contracts() -> Contracts {
    Contracts::standard(ExecutionPolicy::general_purpose())
}
fn step(role: usize, instruction: usize, anchor: Option<usize>) -> Json {
    json!({"role":role,"instruction":instruction,"anchor":anchor})
}
fn fixture(messages: bool) -> Json {
    let participants: Vec<_> = ["P", "V"]
        .iter()
        .enumerate()
        .map(|(role, name)| {
            let mut yes = Vec::new();
            if messages {
                yes.push(if role == 0 {
                    json!(["send", "message", "payload", "V", "x"])
                } else {
                    json!(["receive", "message", "payload", "P", "received", BOOL])
                });
            }
            yes.push(json!([
                "yield",
                [if messages && role == 1 {
                    "received"
                } else {
                    "x"
                }]
            ]));
            json!([
                "participant",
                name,
                "root",
                name,
                [["c", BOOL], ["x", BOOL]],
                [BOOL],
                [
                    [
                        "if",
                        "choice",
                        "c",
                        [["x", "x"]],
                        yes,
                        [["yield", ["x"]]],
                        ["result"]
                    ],
                    ["return", ["result"]]
                ],
                []
            ])
        })
        .collect();
    let offset = usize::from(messages);
    let actions = if messages {
        vec![step(0, 1, Some(1)), step(1, 1, Some(1))]
    } else {
        vec![]
    };
    json!({"format":"zkc.run/0","candidate":json!(["zkc.program/0",[],[],participants,
        [["entry","main",[["P","P"],["V","V"]]]]]).to_string(),"entry":"main","roles":["P","V"],"steps":[
        {"branch":[step(0,0,Some(0)),step(1,0,Some(0))],"arms":[
            {"alternative":"then","body":actions,"yield":[step(0,1+offset,None),step(1,1+offset,None)]},
            {"alternative":"else","body":[],"yield":[step(0,2+offset,None),step(1,2+offset,None)]}]},
        step(0,3+offset,None),step(1,3+offset,None)]})
}
fn admit(raw: &Json) -> Result<Bundle, BundleError> {
    Bundle::admit(
        &serde_json::to_vec(raw).unwrap(),
        &Host::default(),
        &contracts(),
        BundleLimits::default(),
    )
}
fn execute(
    bundle: &Bundle,
    selectors: [TestValue; 2],
    payloads: [bool; 2],
    limits: RunLimits,
) -> joint::Report<Host> {
    let inputs = ["P", "V"]
        .into_iter()
        .zip(selectors)
        .zip(payloads)
        .map(|((role, selector), payload)| RoleInput {
            role: role.into(),
            backend: Host::default(),
            values: vec![selector, TestValue::Bool(payload)],
        })
        .collect();
    joint::run(bundle, "selected", inputs, limits, &mut NoHooks).unwrap()
}

#[test]
fn only_selected_boolean_arm_sends_and_creates_frames() {
    let bundle = admit(&fixture(true)).unwrap();
    for selected in [false, true] {
        let report = execute(
            &bundle,
            [TestValue::Bool(selected), TestValue::Bool(selected)],
            [true, false],
            RunLimits::default(),
        );
        assert!(matches!(report.outcome, Outcome::Completed));
        assert_eq!(report.wire.sends, usize::from(selected));
        assert_eq!(report.wire.receives, usize::from(selected));
        assert_eq!(report.roles[0].outputs, vec![TestValue::Bool(true)]);
        assert_eq!(report.roles[1].outputs, vec![TestValue::Bool(selected)]);
        for (_, backend) in &report.backends {
            assert_eq!(backend.leaves.len(), 2);
        }
        let label = if selected { "then" } else { "else" };
        assert!(
            report
                .reached
                .iter()
                .filter(|r| !r.path.is_empty())
                .all(|r| r.path
                    == vec![PathElement::Branch {
                        site: "choice".into(),
                        alternative: label.into()
                    }])
        );
        assert_eq!(
            report.reached.iter().filter(|r| r.branch_started).count(),
            2
        );
    }
}

/// Rebind the branch captures and route the arms through the given formals.
fn captured(rows: Json, sent: &str, kept: &str) -> Json {
    let mut raw = fixture(true);
    let mut candidate: Json = serde_json::from_str(raw["candidate"].as_str().unwrap()).unwrap();
    for role in 0..2 {
        let branch = &mut candidate[3][role][6][0];
        branch[3] = rows.clone();
        if role == 0 {
            branch[4][0][4] = json!(sent);
            branch[4][1][1] = json!([kept]);
        }
        branch[5][0][1] = json!([kept]);
    }
    raw["candidate"] = json!(candidate.to_string());
    raw
}

#[test]
fn copy_aliases_keep_distinct_branch_formals_and_capture_rows_are_exact() {
    // Two formals bind one Copy parent; each arm uses them independently.
    let rows = json!([["first", "x"], ["second", "x"]]);
    let bundle = admit(&captured(rows, "first", "second")).unwrap();
    for selected in [false, true] {
        let report = execute(
            &bundle,
            [TestValue::Bool(selected), TestValue::Bool(selected)],
            [true, false],
            RunLimits::default(),
        );
        assert!(matches!(report.outcome, Outcome::Completed));
        assert_eq!(report.wire.sends, usize::from(selected));
        assert_eq!(report.roles[0].outputs, vec![TestValue::Bool(true)]);
        assert_eq!(report.roles[1].outputs, vec![TestValue::Bool(selected)]);
    }
    for rows in [
        json!(["x"]),
        json!([["first", "x"], ["first", "x"]]),
        json!([["first", "x", "extra"]]),
        json!([["first", "missing"]]),
    ] {
        assert!(admit(&captured(rows, "first", "first")).is_err());
    }
}

#[test]
fn divergent_selectors_refuse_before_any_arm_including_event_free_control() {
    for messages in [false, true] {
        let report = execute(
            &admit(&fixture(messages)).unwrap(),
            [TestValue::Bool(true), TestValue::Bool(false)],
            [true, false],
            RunLimits::default(),
        );
        assert!(
            matches!(report.outcome,Outcome::DriverFailed(ref f) if f.detail.text == "branch-selector-disagreement")
        );
        assert_eq!(report.reached.len(), 2);
        assert!(report.reached.iter().all(|r| !r.branch_started));
        assert_eq!(report.wire.sends, 0);
        for (_, backend) in &report.backends {
            assert_eq!(backend.leaves.len(), 1);
        }
        for role in &report.roles {
            assert_eq!(role.usage.as_ref().unwrap().instructions, 0);
        }
    }
}

#[test]
fn every_dormant_arm_and_schedule_coordinate_is_admitted() {
    let original = fixture(true);
    let mut candidate: Json =
        serde_json::from_str(original["candidate"].as_str().unwrap()).unwrap();
    candidate[3][0][6][0][5][0][1] = json!(["ambient"]);
    assert_eq!(
        Program::decode(candidate.to_string().as_bytes(), &contracts())
            .unwrap_err()
            .code,
        ErrorCode::Ssa
    );
    for mutate in 0..7 {
        let mut bad = original.clone();
        match mutate {
            0 => bad["steps"][0]["arms"][0]["alternative"] = json!("else"),
            1 => bad["steps"][0]["arms"][1]["yield"][0]["instruction"] = json!(2),
            2 => bad["steps"][0]["arms"][0]["body"][0]["instruction"] = json!(3),
            3 => bad["steps"][0]["arms"][0]["dormant"] = json!(true),
            4 => {
                bad["steps"][0]["arms"].as_array_mut().unwrap().pop();
            }
            5 => bad["steps"][0]["arms"][0]["body"][1]["anchor"] = json!(2),
            _ => bad["steps"][0]["branch"][1]["role"] = json!(0),
        }
        assert!(admit(&bad).is_err(), "mutation {mutate}");
    }
    let limits = BundleLimits {
        steps: 7,
        ..Default::default()
    };
    assert_eq!(
        Bundle::admit(
            &serde_json::to_vec(&original).unwrap(),
            &Host::default(),
            &contracts(),
            limits
        )
        .unwrap_err(),
        BundleError::Limit
    );
}

#[test]
fn independent_control_keeps_selected_origins_and_refuses_wrong_arm() {
    let bundle = admit(&fixture(true)).unwrap();
    let mut runner = Runner::new(
        bundle.admitted(),
        "main",
        "P",
        "independent",
        Host::default(),
        vec![TestValue::Bool(true), TestValue::Bool(true)],
    )
    .map_err(|e| e.error)
    .unwrap();
    let origin = runner.root_origin().clone();
    assert!(runner.enter_branch(&origin, "choice", 1).is_err());
    assert!(runner.enter_branch(&origin, "wrong", 0).is_err());
    assert!(runner.advance_local_control().unwrap());
    let Action::Send(packet) = runner.poll() else {
        panic!("selected send")
    };
    assert_eq!(
        packet.envelope.origin.path,
        vec![PathElement::Branch {
            site: "choice".into(),
            alternative: "then".into()
        }]
    );
    let mut wrong = zkc_runtime::vm::Cut {
        origin: packet.envelope.origin.clone(),
        role: "P".into(),
        site: "message".into(),
        kind: zkc_runtime::vm::CutKind::Send,
    };
    wrong.origin.path.clear();
    assert!(runner.take_send(&wrong).is_err());
}

fn variant_type() -> PhysicalType {
    let spelling = zkc_format::types::variant_spelling(&json!([
        ["selected_control", "Choice"],
        [["some", ["bool"]], ["none", []]]
    ]))
    .unwrap();
    PhysicalType::default_for(zkc_runtime::vm::LogicalType::parse(&spelling).unwrap()).unwrap()
}
fn enum_fixture() -> Json {
    let mut raw = fixture(true);
    let mut candidate: Json = serde_json::from_str(raw["candidate"].as_str().unwrap()).unwrap();
    for role in 0..2 {
        candidate[3][role][4][0][1] = json!(variant_type().spelling());
        let old = candidate[3][role][6][0].clone();
        let mut body = old[4].clone();
        if role == 0 {
            body[0][4] = json!("value");
            body[1][1] = json!(["value"]);
        }
        candidate[3][role][6][0] = json!([
            "match",
            "choice",
            "c",
            [["x", "x"]],
            [["some", ["value"], body], ["none", [], old[5]]],
            ["result"]
        ]);
    }
    raw["candidate"] = json!(candidate.to_string());
    raw["steps"][0]["arms"][0]["alternative"] = json!("some");
    raw["steps"][0]["arms"][1]["alternative"] = json!("none");
    raw
}
fn selector(alternative: usize, payload: bool) -> TestValue {
    TestValue::Variant {
        ty: variant_type(),
        alternative,
        payload: if alternative == 0 {
            vec![TestValue::Bool(payload)]
        } else {
            vec![]
        },
    }
}
#[test]
fn enum_tag_agreement_does_not_claim_payload_agreement() {
    let bundle = admit(&enum_fixture()).unwrap();
    for tag in 0..2 {
        let report = execute(
            &bundle,
            [selector(tag, true), selector(tag, false)],
            [true, false],
            RunLimits::default(),
        );
        assert!(matches!(report.outcome, Outcome::Completed));
        assert_eq!(report.wire.sends, usize::from(tag == 0));
        assert_eq!(report.roles[0].outputs, [TestValue::Bool(true)]);
        assert_eq!(report.roles[1].outputs, [TestValue::Bool(tag == 0)]);
        assert!(
            report
                .reached
                .iter()
                .filter_map(|r| r.branch_alternative)
                .all(|a| a == tag)
        );
    }
    let report = execute(
        &bundle,
        [selector(0, true), selector(1, false)],
        [true, false],
        RunLimits::default(),
    );
    assert!(
        matches!(report.outcome,Outcome::DriverFailed(ref f) if f.detail.text=="branch-selector-disagreement")
    );
    assert_eq!(report.wire.sends, 0);
    let raw = enum_fixture();
    let original: Json = serde_json::from_str(raw["candidate"].as_str().unwrap()).unwrap();
    for mutation in 0..4 {
        let mut bad = original.clone();
        match mutation {
            0 => bad[3][0][6][0][4][0][1] = json!([]),
            1 => bad[3][0][6][0][4][0][0] = json!("none"),
            2 => {
                bad[3][0][6][0][4].as_array_mut().unwrap().pop();
            }
            _ => bad[3][0][6][0][4][1][2][0][1] = json!(["value"]),
        }
        assert!(
            Program::decode(bad.to_string().as_bytes(), &contracts()).is_err(),
            "mutation {mutation}"
        );
    }
}

fn repeated_fixture() -> Json {
    let mut raw = fixture(true);
    let mut candidate: Json = serde_json::from_str(raw["candidate"].as_str().unwrap()).unwrap();
    for role in 0..2 {
        candidate[3][role][4]
            .as_array_mut()
            .unwrap()
            .push(json!(["n", "index@native.index/0"]));
        let branch = candidate[3][role][6][0].clone();
        candidate[3][role][6] = json!([
            [
                "loop",
                "rounds",
                ["value", "n", "3", "i"],
                [],
                [["c", "c"], ["x", "x"]],
                [branch, ["yield", []]],
                []
            ],
            ["return", ["x"]]
        ]);
    }
    raw["candidate"] = json!(candidate.to_string());
    raw["steps"] = json!([
        {"loop":[step(0,0,Some(0)),step(1,0,Some(0))],"body":[
            {"branch":[step(0,1,Some(1)),step(1,1,Some(1))],"arms":[
                {"alternative":"then","body":[step(0,2,Some(2)),step(1,2,Some(2))],"yield":[step(0,3,None),step(1,3,None)]},
                {"alternative":"else","body":[],"yield":[step(0,4,None),step(1,4,None)]}]}],
         "yield":[step(0,5,None),step(1,5,None)]},step(0,6,None),step(1,6,None)]);
    raw
}
#[test]
fn nested_loop_branch_preserves_zero_trip_paths_and_count_checks() {
    let bundle = admit(&repeated_fixture()).unwrap();
    for selected in [false, true] {
        for counts in [[0, 0], [1, 1], [3, 3], [1, 2]] {
            let inputs = ["P", "V"]
                .into_iter()
                .zip(counts)
                .map(|(role, count)| RoleInput {
                    role: role.into(),
                    backend: Host::default(),
                    values: vec![
                        TestValue::Bool(selected),
                        TestValue::Bool(true),
                        TestValue::Index(count),
                    ],
                })
                .collect();
            let report = joint::run(
                &bundle,
                "repeated",
                inputs,
                RunLimits::default(),
                &mut NoHooks,
            )
            .unwrap();
            if counts[0] != counts[1] {
                assert!(
                    matches!(report.outcome,Outcome::DriverFailed(ref f) if f.detail.text=="loop-count-disagreement")
                );
                assert_eq!(report.wire.sends, 0);
                assert!(report.reached.iter().all(|r| !r.loop_started));
            } else {
                assert!(matches!(report.outcome, Outcome::Completed));
                assert_eq!(
                    report.wire.sends,
                    if selected { counts[0] as usize } else { 0 }
                );
                assert_eq!(
                    report.reached.iter().filter(|r| r.branch_started).count(),
                    2 * counts[0] as usize
                );
                for r in report.reached.iter().filter(|r| r.path.len() == 2) {
                    assert!(
                        matches!(r.path.as_slice(),[PathElement::Loop {site,..},PathElement::Branch {site:branch,..}] if site=="rounds" && branch=="choice")
                    );
                }
            }
        }
    }
}

#[test]
fn selected_headers_and_yields_obey_execution_budget() {
    let bundle = admit(&fixture(false)).unwrap();
    for instructions in [0, 1, 2, 3] {
        let mut limits = RunLimits::default();
        limits.work.instructions = instructions;
        let report = execute(
            &bundle,
            [TestValue::Bool(false), TestValue::Bool(false)],
            [true, false],
            limits,
        );
        assert_eq!(
            matches!(report.outcome, Outcome::Completed),
            instructions == 3
        );
        assert_eq!(report.wire.sends, 0);
        assert!(
            report
                .roles
                .iter()
                .all(|r| r.usage.as_ref().unwrap().instructions <= instructions)
        );
    }
}

#[test]
fn one_participant_stopping_or_returning_does_not_complete_an_independent_peer() {
    for early_return in [false, true] {
        let mut raw: Json =
            serde_json::from_str(fixture(false)["candidate"].as_str().unwrap()).unwrap();
        if !early_return {
            raw[2] = json!([[
                "function",
                "stop",
                [],
                [],
                [["stop", "end", "reject"]],
                ["stop", []]
            ]]);
        }
        for role in 0..2 {
            let branch = &mut raw[3][role][6][0];
            branch[3] = json!([["x", "x"], ["c", "c"]]);
            branch[4].as_array_mut().unwrap().insert(
                0,
                if early_return {
                    json!(["return_if", "done", "c", ["x"], []])
                } else {
                    json!(["local", "stop_here", "stop", [], []])
                },
            );
        }
        let program = Program::decode(raw.to_string().as_bytes(), &contracts()).unwrap();
        let mut first = Runner::new(
            &program,
            "main",
            "P",
            "independent",
            Host::default(),
            vec![TestValue::Bool(true), TestValue::Bool(true)],
        )
        .map_err(|e| e.error)
        .unwrap();
        let mut peer = Runner::new(
            &program,
            "main",
            "V",
            "independent",
            Host::default(),
            vec![TestValue::Bool(false), TestValue::Bool(false)],
        )
        .map_err(|e| e.error)
        .unwrap();
        first.advance_local_control().unwrap();
        if early_return {
            first.advance_local_control().unwrap();
            assert_eq!(
                first.returned_values(),
                Some([TestValue::Bool(true)].as_slice())
            );
        } else {
            let Action::Local(local) = first.poll() else {
                panic!("selected stop")
            };
            first.execute_local(&local.cut).unwrap();
            assert!(first.stop().is_some());
        }
        assert!(peer.is_at_entry());
        assert!(!peer.is_terminal());
        assert!(peer.advance_local_control().unwrap());
        assert!(peer.advance_local_control().unwrap());
        assert!(matches!(peer.poll(),Action::Returned(values) if values==[TestValue::Bool(false)]));
    }
}

fn binding_context(
    program: &Program,
    required: &[joint_input::InputRequirement],
    expected: &[Json],
) -> (Vec<u8>, [u8; 32]) {
    use sha2::{Digest, Sha256};
    let rows: Vec<_> = required
        .iter()
        .zip(expected)
        .map(|(r, e)| {
            json!([
                r.components
                    .iter()
                    .map(|c| json!([
                        c.role,
                        c.input.to_string(),
                        c.path
                            .iter()
                            .flat_map(|(a, p)| [a.to_string(), p.to_string()])
                            .collect::<Vec<_>>()
                    ]))
                    .collect::<Vec<_>>(),
                r.ty.spelling(),
                match r.observation {
                    joint_input::Observation::Value => json!("value"),
                    joint_input::Observation::Tag => json!("tag"),
                    joint_input::Observation::Extent { axis } =>
                        json!(["extent", axis.to_string()]),
                },
                e
            ])
        })
        .collect();
    let digest = Sha256::digest(program.bytes())
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect::<String>();
    let tree = json!(["zkc.input-bindings/0", digest, "main", rows]);
    let bytes = zkc_format::logical::encode_tree(&tree).unwrap();
    let pin = Sha256::digest(&bytes).into();
    (bytes, pin)
}
use zkc_runtime::host::input_binding as joint_input;
fn requirement(
    ty: PhysicalType,
    tag_only: bool,
    path: Vec<(usize, usize)>,
) -> joint_input::InputRequirement {
    joint_input::InputRequirement {
        components: ["P", "V"]
            .into_iter()
            .map(|role| joint_input::InputComponent {
                role: role.into(),
                input: 0,
                path: path.clone(),
            })
            .collect(),
        ty,
        observation: if tag_only {
            joint_input::Observation::Tag
        } else {
            joint_input::Observation::Value
        },
    }
}
/// A default-capacity invocation ledger.
fn ledger() -> zkc_runtime::vm::ExecutionLedger {
    zkc_runtime::vm::ExecutionLedger::new(Default::default(), Default::default())
}
fn limited_ledger(logical_bytes: u64, total_bytes: usize) -> zkc_runtime::vm::ExecutionLedger {
    zkc_runtime::vm::ExecutionLedger::new(
        zkc_runtime::vm::ValueBudget {
            total_bytes,
            ..Default::default()
        },
        zkc_runtime::vm::WorkBudget {
            logical_bytes,
            ..Default::default()
        },
    )
}
#[test]
fn inspection_and_encoding_charge_one_invocation_ledger_across_roles() {
    use joint_input::{BindingError as E, InputBindings};
    let bundle = admit(&fixture(false)).unwrap();
    let program = bundle.admitted();
    let required = [requirement(
        PhysicalType::parse(BOOL).unwrap(),
        false,
        vec![],
    )];
    let (bytes, pin) = binding_context(program, &required, &[json!(["active", "5a4b4356000501"])]);
    let context = InputBindings::admit_pinned(program, "main", &required, &bytes, &pin).unwrap();
    use zkc_runtime::vm::Value as _;
    let backend = Host::default();
    let inputs = [TestValue::Bool(true), TestValue::Bool(false)];
    // The observed root is read once as the component root and once as the
    // selected value; its canonical frame is a 7-byte encoding.
    let read = 2 * inputs[0].retained_bytes() as u64;
    let encoded = 7;
    let invocation = ledger();
    context
        .check_role("P", &backend, &inputs, &invocation)
        .unwrap();
    let after_one = invocation.snapshot();
    assert_eq!(after_one.logical_bytes, read + encoded as u64);
    assert_eq!(after_one.total_value_bytes, encoded);
    assert_eq!(after_one.live_reserved_bytes, 0);
    context
        .check_role("V", &backend, &inputs, &invocation)
        .unwrap();
    let after_two = invocation.snapshot();
    assert_eq!(after_two.logical_bytes, 2 * after_one.logical_bytes);
    assert_eq!(after_two.total_value_bytes, 2 * encoded);
    // One role fits the allowance; the second role draws on what remains
    // instead of a fresh per-role allowance.
    let one_role = limited_ledger(after_one.logical_bytes, usize::MAX);
    context
        .check_role("P", &backend, &inputs, &one_role)
        .unwrap();
    assert_eq!(
        context.check_role("V", &backend, &inputs, &one_role),
        Err(E::Limit)
    );
    assert_eq!(backend.encodes.get(), 3);
    // Inspection reads charge logical work before the value is encoded.
    let short_read = limited_ledger(read - 1, usize::MAX);
    assert_eq!(
        context.check_role("P", &backend, &inputs, &short_read),
        Err(E::Limit)
    );
    assert_eq!(backend.encodes.get(), 3);
    // Canonical encoding charges its bound as fresh allocation before encoding.
    let short_fresh = limited_ledger(u64::MAX, encoded - 1);
    assert_eq!(
        context.check_role("P", &backend, &inputs, &short_fresh),
        Err(E::Limit)
    );
    assert_eq!(backend.encodes.get(), 3);
    assert_eq!(short_fresh.snapshot().live_reserved_bytes, 0);
    context
        .check_role("P", &backend, &inputs, &limited_ledger(u64::MAX, encoded))
        .unwrap();
}
#[test]
fn independent_input_bindings_require_exact_externally_pinned_context() {
    use joint_input::{BindingError as E, InputBindings};
    let bundle = admit(&fixture(false)).unwrap();
    let program = bundle.admitted();
    let required = [requirement(
        PhysicalType::parse(BOOL).unwrap(),
        false,
        vec![],
    )];
    // Trusted application provisioning supplies this pin, separately from bytes.
    let (bytes, pin) = binding_context(program, &required, &[json!(["active", "5a4b4356000501"])]);
    let context = InputBindings::admit_pinned(program, "main", &required, &bytes, &pin).unwrap();
    let backend = Host::default();
    for role in ["P", "V"] {
        context
            .check_role(
                role,
                &backend,
                &[TestValue::Bool(true), TestValue::Bool(false)],
                &ledger(),
            )
            .unwrap();
        assert_eq!(
            context.check_role(
                role,
                &backend,
                &[TestValue::Bool(false), TestValue::Bool(false)],
                &ledger()
            ),
            Err(E::Value)
        );
    }
    assert_eq!(
        context.check_role(
            "P",
            &backend,
            &vec![TestValue::Bool(true); zkc_runtime::vm::Limits::PORTS + 1],
            &ledger()
        ),
        Err(E::Limit)
    );
    let yes = TestValue::Bool(true);
    // Preparation has holes for capabilities that have not been issued. Only
    // an unobserved slot can be absent; required data must already be present.
    context
        .check_role_prepared("P", &backend, &[Some(&yes), None], &ledger())
        .unwrap();
    assert_eq!(
        context.check_role_prepared("P", &backend, &[None, Some(&yes)], &ledger()),
        Err(E::Input)
    );
    assert_eq!(
        context.check_role_prepared("P", &backend, &[Some(&yes)], &ledger()),
        Err(E::Input)
    );
    assert_eq!(
        context.check_role_prepared("absent", &backend, &[Some(&yes), None], &ledger()),
        Err(E::Input)
    );
    assert!(backend.frames.is_empty());
    let disabled = Host {
        wire_disabled: true,
        ..Host::default()
    };
    assert_eq!(
        context.check_role(
            "P",
            &disabled,
            &[TestValue::Bool(true), TestValue::Bool(false)],
            &ledger()
        ),
        Err(E::Codec)
    );
    assert_eq!(
        InputBindings::admit_pinned(
            program,
            "main",
            &required,
            &vec![0; zkc_runtime::vm::Limits::ARTIFACT_BYTES + 1],
            &pin
        )
        .unwrap_err(),
        E::Limit
    );
    let mut deep = required.clone();
    deep[0].components[0].path = vec![(0, 0); zkc_runtime::vm::TYPE_DEPTH_LIMIT + 1];
    let (deep_bytes, deep_pin) = binding_context(program, &deep, &[json!(["inactive"])]);
    assert_eq!(
        InputBindings::admit_pinned(program, "main", &deep, &deep_bytes, &deep_pin).unwrap_err(),
        E::Limit
    );

    assert_eq!(
        InputBindings::admit_pinned(program, "main", &required, &bytes, &[0; 32]).unwrap_err(),
        E::Identity
    );
    assert_eq!(
        InputBindings::admit_pinned(program, "wrong", &required, &bytes, &pin).unwrap_err(),
        E::Subject
    );
    assert_eq!(
        InputBindings::admit_pinned(program, "main", &[], &bytes, &pin).unwrap_err(),
        E::Requirements
    );
    let mut wrong = required.clone();
    wrong[0].components[1].input = 1;
    assert_eq!(
        InputBindings::admit_pinned(program, "main", &wrong, &bytes, &pin).unwrap_err(),
        E::Requirements
    );
    wrong = required.clone();
    wrong[0].components[1].role = "outsider".into();
    assert_eq!(
        InputBindings::admit_pinned(program, "main", &wrong, &bytes, &pin).unwrap_err(),
        E::Requirements
    );
    let mut candidate = program.bytes().to_vec();
    candidate.push(b' ');
    let different = Program::decode(&candidate, &contracts()).unwrap();
    assert_eq!(
        InputBindings::admit_pinned(&different, "main", &required, &bytes, &pin).unwrap_err(),
        E::Subject
    );
    assert_eq!(
        context.check_role(
            "P",
            &backend,
            &[TestValue::Index(1), TestValue::Bool(true)],
            &ledger()
        ),
        Err(E::Input)
    );
    let mut changed = zkc_format::logical::decode_tree(&bytes).unwrap();
    changed.as_array_mut().unwrap().push(json!([]));
    let changed = zkc_format::logical::encode_tree(&changed).unwrap();
    use sha2::{Digest, Sha256};
    assert_eq!(
        InputBindings::admit_pinned(
            program,
            "main",
            &required,
            &changed,
            &Sha256::digest(&changed).into()
        )
        .unwrap_err(),
        E::Requirements
    );
}

#[test]
fn trusted_binding_keeps_variant_tags_payload_paths_and_inactive_paths_distinct() {
    use joint_input::{BindingError as E, InputBindings};
    let bundle = admit(&enum_fixture()).unwrap();
    let program = bundle.admitted();
    let tags = [requirement(variant_type(), true, vec![])];
    let (bytes, pin) = binding_context(program, &tags, &[json!(["active", "30"])]); // ordinal 0
    let context = InputBindings::admit_pinned(program, "main", &tags, &bytes, &pin).unwrap();
    for invalid in ["32", "3030", "2d31"] {
        let (bytes, pin) = binding_context(program, &tags, &[json!(["active", invalid])]);
        assert_eq!(
            InputBindings::admit_pinned(program, "main", &tags, &bytes, &pin).unwrap_err(),
            E::Requirements
        );
    }
    for payload in [false, true] {
        context
            .check_role(
                "P",
                &Host::default(),
                &[selector(0, payload), TestValue::Bool(false)],
                &ledger(),
            )
            .unwrap();
    }
    assert_eq!(
        context.check_role(
            "P",
            &Host::default(),
            &[selector(1, false), TestValue::Bool(false)],
            &ledger()
        ),
        Err(E::Value)
    );
    let payloads = [requirement(
        PhysicalType::parse(BOOL).unwrap(),
        false,
        vec![(0, 0)],
    )];
    let (bytes, pin) = binding_context(program, &payloads, &[json!(["active", "5a4b4356000501"])]);
    let context = InputBindings::admit_pinned(program, "main", &payloads, &bytes, &pin).unwrap();
    context
        .check_role(
            "P",
            &Host::default(),
            &[selector(0, true), TestValue::Bool(false)],
            &ledger(),
        )
        .unwrap();
    assert_eq!(
        context.check_role(
            "P",
            &Host::default(),
            &[selector(0, false), TestValue::Bool(false)],
            &ledger()
        ),
        Err(E::Value)
    );
    let (bytes, pin) = binding_context(program, &payloads, &[json!(["inactive"])]);
    let context = InputBindings::admit_pinned(program, "main", &payloads, &bytes, &pin).unwrap();
    context
        .check_role(
            "P",
            &Host::default(),
            &[selector(1, false), TestValue::Bool(false)],
            &ledger(),
        )
        .unwrap();
    assert_eq!(
        context.check_role(
            "P",
            &Host::default(),
            &[selector(0, true), TestValue::Bool(false)],
            &ledger()
        ),
        Err(E::Value)
    );
    assert_eq!(
        context.check_role(
            "P",
            &Host::default(),
            &[selector(99, false), TestValue::Bool(false)],
            &ledger()
        ),
        Err(E::Value)
    );
    let mut wrong = payloads.clone();
    wrong[0].components[1].path = vec![(1, 0)];
    let (bytes, pin) = binding_context(program, &wrong, &[json!(["inactive"])]);
    assert_eq!(
        InputBindings::admit_pinned(program, "main", &wrong, &bytes, &pin).unwrap_err(),
        E::Requirements
    );
}

fn ordinary_input_program(ty: &str) -> Program {
    let participants: Vec<_> = ["P", "V"]
        .iter()
        .map(|role| {
            json!([
                "participant",
                role,
                "root",
                role,
                [["a", ty], ["b", ty]],
                [],
                [["return", []]],
                []
            ])
        })
        .collect();
    Program::decode(
        json!([
            "zkc.program/0",
            [],
            [],
            participants,
            [["entry", "main", [["P", "P"], ["V", "V"]]]]
        ])
        .to_string()
        .as_bytes(),
        &contracts(),
    )
    .unwrap()
}

#[test]
fn extent_binding_observes_exact_axis_without_encoding_contents_including_zero() {
    use joint_input::{BindingError as E, InputBindings, Observation};
    let program = ordinary_input_program(host::BYTES);
    let mut required = [requirement(
        PhysicalType::parse(host::BYTES).unwrap(),
        false,
        vec![],
    )];
    required[0].observation = Observation::Extent { axis: 0 };
    for (contents, expected) in [(vec![1, 2], "32"), (vec![], "30")] {
        let (bytes, pin) = binding_context(&program, &required, &[json!(["active", expected])]);
        let context =
            InputBindings::admit_pinned(&program, "main", &required, &bytes, &pin).unwrap();
        let backend = Host {
            wire_disabled: true,
            ..Host::default()
        };
        for role in ["P", "V"] {
            let actual = if role == "P" {
                contents.clone()
            } else {
                vec![9; contents.len()]
            };
            context
                .check_role(
                    role,
                    &backend,
                    &[
                        TestValue::Bytes(actual.into()),
                        TestValue::Bytes(vec![].into()),
                    ],
                    &ledger(),
                )
                .unwrap();
        }
        assert_eq!(
            context.check_role(
                "P",
                &backend,
                &[
                    TestValue::Bytes(vec![0; contents.len() + 1].into()),
                    TestValue::Bytes(vec![].into())
                ],
                &ledger()
            ),
            Err(E::Value)
        );
        assert_eq!(backend.encodes.get(), 0);
        assert!(backend.frames.is_empty());
        assert_eq!(format!("{context:?}"), "InputBindings { groups: 1, .. }");
    }
    for observation in [Observation::Extent { axis: 1 }, Observation::Tag] {
        let mut invalid = required.clone();
        invalid[0].observation = observation;
        let (bytes, pin) = binding_context(&program, &invalid, &[json!(["active", "30"])]);
        assert_eq!(
            InputBindings::admit_pinned(&program, "main", &invalid, &bytes, &pin).unwrap_err(),
            E::Requirements
        );
    }
    for expected in [
        json!(["active", "3031"]),
        json!(["inactive"]),
        json!(["active", "2d31"]),
    ] {
        let (bytes, pin) = binding_context(&program, &required, &[expected]);
        assert_eq!(
            InputBindings::admit_pinned(&program, "main", &required, &bytes, &pin).unwrap_err(),
            E::Requirements
        );
    }
    let too_large = (zkc_runtime::vm::Limits::VALUE_BYTES + 1)
        .to_string()
        .bytes()
        .map(|b| format!("{b:02x}"))
        .collect::<String>();
    let (bytes, pin) = binding_context(&program, &required, &[json!(["active", too_large])]);
    assert_eq!(
        InputBindings::admit_pinned(&program, "main", &required, &bytes, &pin).unwrap_err(),
        E::Limit
    );
}

#[test]
fn inventories_are_exact_even_when_components_have_equal_types() {
    use joint_input::{BindingError as E, InputBindings};
    let program = ordinary_input_program(BOOL);
    let required = [requirement(
        PhysicalType::parse(BOOL).unwrap(),
        false,
        vec![],
    )];
    let (bytes, pin) = binding_context(&program, &required, &[json!(["active", "5a4b4356000501"])]);
    for change in ["role", "input", "extra", "observation"] {
        let mut changed = required.to_vec();
        match change {
            "role" => changed[0].components.swap(0, 1),
            "input" => changed[0].components[0].input = 1,
            "extra" => changed.push(changed[0].clone()),
            _ => changed[0].observation = joint_input::Observation::Tag,
        }
        assert_eq!(
            InputBindings::admit_pinned(&program, "main", &changed, &bytes, &pin).unwrap_err(),
            E::Requirements,
            "{change}"
        );
    }
    let context = InputBindings::admit_pinned(&program, "main", &required, &bytes, &pin).unwrap();
    let actual = [TestValue::Bool(true), TestValue::Bool(false)];
    for (fault, expected) in [
        (host::Fault::EncodeOversizeBound, E::Limit),
        (host::Fault::EncodeOverrun, E::Codec),
    ] {
        let backend = Host {
            fault,
            ..Host::default()
        };
        assert_eq!(
            context.check_role("P", &backend, &actual, &ledger()),
            Err(expected)
        );
        assert!(backend.frames.is_empty());
        if matches!(fault, host::Fault::EncodeOversizeBound) {
            assert_eq!(backend.encodes.get(), 0);
        }
    }
}

#[test]
fn equal_typed_variant_paths_and_inactive_extent_paths_keep_exact_associations() {
    use joint_input::{BindingError as E, InputBindings, Observation};
    let spelling = zkc_format::types::variant_spelling(&json!([
        ["input_bindings", "Collections"],
        [["left", ["bytes"]], ["right", ["bytes"]]]
    ]))
    .unwrap();
    let ty =
        PhysicalType::default_for(zkc_runtime::vm::LogicalType::parse(&spelling).unwrap()).unwrap();
    let program = ordinary_input_program(&ty.spelling());
    let mut required = [requirement(
        PhysicalType::parse(host::BYTES).unwrap(),
        false,
        vec![(0, 0)],
    )];
    required[0].observation = Observation::Extent { axis: 0 };
    let (bytes, pin) = binding_context(&program, &required, &[json!(["inactive"])]);
    let context = InputBindings::admit_pinned(&program, "main", &required, &bytes, &pin).unwrap();
    let dormant = TestValue::Variant {
        ty: ty.clone(),
        alternative: 1,
        payload: vec![TestValue::Bytes(vec![1, 2, 3].into())],
    };
    context
        .check_role(
            "P",
            &Host::default(),
            &[dormant.clone(), dormant],
            &ledger(),
        )
        .unwrap();
    let active_empty = TestValue::Variant {
        ty,
        alternative: 0,
        payload: vec![TestValue::Bytes(vec![].into())],
    };
    assert_eq!(
        context.check_role(
            "P",
            &Host::default(),
            &[active_empty.clone(), active_empty],
            &ledger()
        ),
        Err(E::Value)
    );
    let mut swapped = required.clone();
    swapped[0].components[1].path = vec![(1, 0)];
    assert_eq!(
        InputBindings::admit_pinned(&program, "main", &swapped, &bytes, &pin).unwrap_err(),
        E::Requirements
    );
}

#[test]
fn self_selected_inventory_and_pin_do_not_independently_certify_source_coverage() {
    // The actual Program has a shared selector. Runtime does not derive source
    // requirements: a caller choosing both an empty list and its pin can pass
    // these utility checks. Only external inventory/association authority can
    // close that omission boundary; this is deliberately not a source test.
    let bundle = admit(&fixture(false)).unwrap();
    let program = bundle.admitted();
    let (bytes, self_selected_pin) = binding_context(program, &[], &[]);
    let context =
        joint_input::InputBindings::admit_pinned(program, "main", &[], &bytes, &self_selected_pin)
            .unwrap();
    for (role, selector) in [("P", true), ("V", false)] {
        context
            .check_role(
                role,
                &Host::default(),
                &[TestValue::Bool(selector), TestValue::Bool(false)],
                &ledger(),
            )
            .unwrap();
    }
}

#[test]
fn value_bindings_require_the_complete_installed_wire_permission() {
    use joint_input::{BindingError as E, InputBindings};
    let ty = PhysicalType::default_for(
        zkc_runtime::vm::LogicalType::parse("fixed_vector<field:koala-bear,0>").unwrap(),
    )
    .unwrap();
    let program = ordinary_input_program(&ty.spelling());
    let required = [requirement(ty, false, vec![])];
    let (bytes, pin) = binding_context(&program, &required, &[json!(["active", ""])]);
    assert_eq!(
        InputBindings::admit_pinned(&program, "main", &required, &bytes, &pin).unwrap_err(),
        E::Requirements
    );
}

#[test]
fn joint_branch_completion_retires_only_the_actual_returning_role() {
    let mut raw = fixture(false);
    let mut candidate: Json = serde_json::from_str(raw["candidate"].as_str().unwrap()).unwrap();
    for role in 0..2 {
        candidate[3][role][6][0][4]
            .as_array_mut()
            .unwrap()
            .insert(0, json!(["return_if", "finish_role", "x", ["x"], []]));
    }
    raw["candidate"] = json!(candidate.to_string());
    raw["steps"] = json!([
        {"branch":[step(0,0,Some(0)),step(1,0,Some(0))],"arms":[
            {"alternative":"then","body":[step(0,1,Some(1)),step(1,1,Some(2))],"yield":[step(0,2,None),step(1,2,None)]},
            {"alternative":"else","body":[],"yield":[step(0,3,None),step(1,3,None)]}]},step(0,4,None),step(1,4,None)]);
    let report = execute(
        &admit(&raw).unwrap(),
        [TestValue::Bool(true), TestValue::Bool(true)],
        [true, false],
        RunLimits::default(),
    );
    assert!(matches!(report.outcome, Outcome::Completed));
    assert_eq!(report.roles[0].outputs, [TestValue::Bool(true)]);
    assert_eq!(report.roles[1].outputs, [TestValue::Bool(false)]);
    assert!(report.roles[0].return_at.is_some());
    assert!(report.roles[1].return_at.is_none());
    assert!(
        !report
            .reached
            .iter()
            .any(|r| r.step.role == 0 && r.step.instruction >= 2)
    );
    assert!(
        report
            .reached
            .iter()
            .any(|r| r.step.role == 1 && r.step.instruction == 2)
    );
}
