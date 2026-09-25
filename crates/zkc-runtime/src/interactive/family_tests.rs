//! Native admission/role isolation controls independent of a source checker.
use super::*;
use serde_json::{Value as Json, json};
use std::collections::BTreeMap;

#[derive(Clone, Debug)]
struct Index(u64);
impl Value for Index {
    fn control_index(&self) -> Result<u64, BackendError> {
        Ok(self.0)
    }
    fn type_name(&self) -> &str {
        "index"
    }
    fn physical_type(&self) -> PhysicalType {
        PhysicalType::parse("index@native.index/1").unwrap()
    }
    fn validate_serializable(&self) -> Result<(), BackendError> {
        Ok(())
    }
    fn retained_bytes(&self) -> usize {
        8
    }
}
#[derive(Default, Debug)]
struct Host {
    frames: Vec<(FrameId, BTreeMap<String, u64>)>,
    fail_local_enter: bool,
    fail_cleanup: bool,
    exits: Vec<(FrameKind, FrameExit)>,
}
impl Backend for Host {
    type Value = Index;
    fn validate_value(&self, _: &Index) -> Result<(), BackendError> {
        Ok(())
    }
    fn enter_frame(&mut self, frame: &Frame, _: &[Index]) -> Result<(), BackendError> {
        if self.fail_local_enter && matches!(frame.kind(), FrameKind::Local { .. }) {
            return Err(BackendError::new("fatal:selector-entry"));
        }
        assert_eq!(frame.parent(), self.frames.last().map(|p| p.0));
        self.frames.push((frame.id(), frame.parameters().clone()));
        Ok(())
    }
    fn leave_frame(
        &mut self,
        frame: &Frame,
        exit: FrameExit,
        _: &[Index],
    ) -> Result<(), BackendError> {
        // Entered frame identities cannot be rewritten after selecting counts.
        assert_eq!(
            self.frames.pop(),
            Some((frame.id(), frame.parameters().clone()))
        );
        self.exits.push((frame.kind().clone(), exit));
        if self.fail_cleanup {
            return Err(BackendError::new(match frame.kind() {
                FrameKind::Local { .. } => "fatal:local-cleanup",
                _ => "fatal:entry-cleanup",
            }));
        }
        Ok(())
    }
    fn apply(&mut self, _: &Invocation<'_>, _: &[Index]) -> Result<Vec<Index>, BackendError> {
        panic!("identity selector has no primitive operations")
    }
}
fn family() -> Json {
    let binding = json!([[
        "rounds",
        [
            "ingress",
            "10",
            [["P", "Select", ["n"]], ["V", "Select", ["n"]]]
        ]
    ]]);
    let role = |name: &str| {
        json!([
            "participant",
            name,
            "root",
            name,
            binding,
            [["n", "index@native.index/1"]],
            ["index@native.index/1"],
            [
                [
                    "loop",
                    "round",
                    ["parameter", "rounds"],
                    [["a", "n"]],
                    [],
                    [["yield", ["a"]]],
                    ["out"]
                ],
                ["return", ["out"]]
            ]
        ])
    };
    json!([
        "zkc.participants/1",
        [],
        "physical",
        [[
            "function",
            "Select",
            [["x", "index@native.index/1"]],
            ["index@native.index/1"],
            [["return", ["x"]]],
            ["Select", []]
        ]],
        [role("P"), role("V")],
        [["entry", "main", [["P", "P"], ["V", "V"]]]]
    ])
}
fn admit(value: &Json) -> Result<Admitted, AdmissionError> {
    admit_supplied(&serde_json::to_vec(value).unwrap(), &Host::default())
}

#[test]
fn family_roles_select_only_their_own_actual_inputs() {
    let program = admit(&family()).unwrap();
    for (p, v) in [(0, 0), (1, 3), (10, 2)] {
        for (role, count) in [("P", p), ("V", v)] {
            let mut runner = Runner::new(
                &program,
                "main",
                role,
                "family",
                Host::default(),
                vec![Index(count)],
            )
            .unwrap_or_else(|e| panic!("{:?}", e.error));
            assert_eq!(runner.selected_parameters()["rounds"], count);
            assert!(matches!(runner.poll(), Action::Returned(values) if values[0].0 == count));
            assert_eq!(runner.usage().iterations, count);
            assert!(runner.into_backend().frames.is_empty());
        }
    }
}

#[test]
fn family_bound_failure_unwinds_ingress_without_running_body() {
    let program = admit(&family()).unwrap();
    for count in [11, u64::MAX] {
        let mut runner = Runner::new(
            &program,
            "main",
            "P",
            "family",
            Host::default(),
            vec![Index(count)],
        )
        .unwrap_or_else(|e| panic!("execution must be observable: {:?}", e.error));
        assert!(runner.is_terminal());
        let Action::Stopped(stop) = runner.poll() else {
            panic!("expected stopped ingress")
        };
        assert_eq!(stop.role, "P");
        assert_eq!(stop.site.as_deref(), Some("ingress.rounds"));
        assert_eq!(
            stop.kind,
            StopKind::Backend(BackendError::new("interactive-family-bound"))
        );
        assert!(stop.cleanup_errors.is_empty());
        assert!(runner.selected_parameters().is_empty());
        assert_eq!(runner.ingress_actions().len(), 1);
        assert_eq!(runner.usage().instructions, 1);
        assert_eq!(runner.usage().iterations, 0);
        assert_eq!(runner.usage().live_values, 0);
        assert_eq!(runner.usage().total_value_bytes, 16);
        let usage = runner.usage();
        runner.cancel();
        assert!(matches!(runner.poll(), Action::Stopped(s) if s == stop));
        assert_eq!(runner.usage(), usage);
        let backend = runner.into_backend();
        assert!(backend.frames.is_empty());
        assert_eq!(backend.exits.len(), 2);
        assert_eq!(backend.exits[0].1, FrameExit::Returned);
        assert_eq!(backend.exits[1].1, FrameExit::Stopped);
    }
}

#[test]
fn family_failed_input_admission_returns_backend_custody() {
    let program = admit(&family()).unwrap();
    let failure = Runner::new(&program, "main", "P", "family", Host::default(), vec![])
        .err()
        .expect("missing actual input is a load error");
    assert_eq!(failure.error, RuntimeError::Inputs);
    assert!(failure.backend.frames.is_empty());
    assert!(failure.backend.exits.is_empty());
}

#[test]
fn family_value_budget_distinguishes_admission_from_ingress_execution() {
    let program = admit(&family()).unwrap();
    let make = |live_bytes| {
        Runner::new_with_value_budget(
            &program,
            "main",
            "P",
            "family",
            Host::default(),
            vec![Index(1)],
            ValueBudget {
                live_bytes,
                total_bytes: 32,
            },
        )
    };
    let failure = make(7).err().expect("entry value cannot be admitted");
    assert_eq!(failure.error, RuntimeError::Limit);
    assert!(failure.backend.exits.is_empty());
    let mut runner = make(8).unwrap_or_else(|e| panic!("{:?}", e.error));
    assert!(matches!(runner.poll(), Action::Stopped(s)
        if s.kind == StopKind::Limit && s.site.as_deref() == Some("ingress.rounds")));
    assert_eq!(runner.ingress_actions().len(), 1);
    assert_eq!(runner.usage().instructions, 0);
    assert_eq!(runner.usage().total_value_bytes, 8);
    assert_eq!(runner.usage().live_values, 0);
    assert_eq!(
        runner.into_backend().exits,
        [(FrameKind::Entry, FrameExit::Stopped)]
    );
}

#[test]
fn family_partial_selection_retains_order_and_immutable_frame_identity() {
    let mut value = family();
    for role in [0, 1] {
        // Serialized order is deliberately opposite to lexical execution order.
        let binding = value[4][role][4][0][1].clone();
        let mut later = binding.clone();
        later[1] = json!("2");
        value[4][role][4] = json!([["rounds", later], ["earlier", binding]]);
    }
    let program = admit(&value).unwrap();
    let mut runner = Runner::new(
        &program,
        "main",
        "V",
        "family",
        Host::default(),
        vec![Index(3)],
    )
    .unwrap_or_else(|e| panic!("{:?}", e.error));
    assert!(
        matches!(runner.poll(), Action::Stopped(s) if s.site.as_deref() == Some("ingress.rounds"))
    );
    assert_eq!(
        runner.selected_parameters(),
        &BTreeMap::from([("earlier".into(), 3)])
    );
    assert_eq!(
        runner
            .ingress_actions()
            .iter()
            .map(|a| a.cut.site.as_str())
            .collect::<Vec<_>>(),
        ["ingress.earlier", "ingress.rounds"]
    );
    assert_eq!(runner.usage().instructions, 2);
    assert_eq!(runner.usage().iterations, 0);
    assert_eq!(runner.usage().live_values, 0);
    assert!(runner.into_backend().frames.is_empty());
}

#[test]
fn family_fatal_selector_entry_and_cleanup_remain_stopped() {
    let program = admit(&family()).unwrap();
    for fail_local_enter in [false, true] {
        let host = Host {
            fail_local_enter,
            fail_cleanup: true,
            ..Host::default()
        };
        let mut runner = Runner::new(&program, "main", "P", "family", host, vec![Index(1)])
            .unwrap_or_else(|e| panic!("{:?}", e.error));
        let Action::Stopped(stop) = runner.poll() else {
            panic!("expected fatal stop")
        };
        assert_eq!(stop.site.as_deref(), Some("ingress.rounds"));
        assert_eq!(
            stop.kind,
            StopKind::Backend(BackendError::new(if fail_local_enter {
                "fatal:selector-entry"
            } else {
                "fatal:local-cleanup"
            }))
        );
        assert_eq!(
            stop.cleanup_errors,
            [BackendError::new("fatal:entry-cleanup")]
        );
        assert!(runner.selected_parameters().is_empty());
        assert_eq!(runner.usage().live_values, 0);
        let backend = runner.into_backend();
        assert!(backend.frames.is_empty());
        assert_eq!(backend.exits.len(), if fail_local_enter { 1 } else { 2 });
    }
}

#[test]
fn family_selector_failure_keeps_primary_error_and_all_cleanup_errors() {
    let mut value = family();
    value[3][0][4] = json!([
        ["for", "scan", "i", "x", "x", [], [], [["yield", []]], []],
        ["return", ["x"]]
    ]);
    let program = admit(&value).unwrap();
    let host = Host {
        fail_cleanup: true,
        ..Host::default()
    };
    let mut runner = Runner::new(&program, "main", "P", "family", host, vec![Index(u64::MAX)])
        .unwrap_or_else(|e| panic!("{:?}", e.error));
    let Action::Stopped(stop) = runner.poll() else {
        panic!("expected selector stop")
    };
    assert_eq!(stop.site.as_deref(), Some("ingress.rounds"));
    assert_eq!(
        stop.kind,
        StopKind::Backend(BackendError::new("exhausted:local-bound-limit"))
    );
    assert_eq!(
        stop.cleanup_errors,
        [
            BackendError::new("fatal:local-cleanup"),
            BackendError::new("fatal:entry-cleanup")
        ]
    );
    assert_eq!(runner.usage().instructions, 1);
    assert_eq!(runner.usage().iterations, 0);
    assert_eq!(runner.usage().live_values, 0);
    let backend = runner.into_backend();
    assert!(backend.frames.is_empty());
    assert_eq!(backend.exits.len(), 2);
    assert!(
        backend
            .exits
            .iter()
            .all(|(_, exit)| *exit == FrameExit::Stopped)
    );
}

/// The identifier a malformed family control is refused with, by the name of
/// the rule it breaks. The compiler and the Lean reader are held to the same
/// table over source mutations; these controls mutate compiled participants.
fn refusal(rule: &str) -> String {
    let rows: Vec<(String, String)> = serde_json::from_str(include_str!(
        "../../../../tests/fixtures/input-families/refusals.json"
    ))
    .expect("the shared family refusal table");
    rows.into_iter()
        .find_map(|(name, identifier)| (name == rule).then_some(identifier))
        .unwrap_or_else(|| panic!("no shared refusal for {rule}"))
}

#[test]
fn family_native_admission_rejects_malformed_controls() {
    let mut cases: Vec<(Json, ErrorCode, String)> = Vec::new();
    let mut case = |mutate: &dyn Fn(&mut Json), code, detail: String| {
        let mut p = family();
        mutate(&mut p);
        cases.push((p, code, detail));
    };
    use ErrorCode::Parameters;
    // The loop counts by a name that is not a family of this instance.
    case(
        &|p| p[4][0][7][0][2][1] = json!("unknown"),
        Parameters,
        refusal("count"),
    );
    case(
        &|p| p[4][0][4][0][1][1] = json!("1048577"),
        Parameters,
        refusal("bound"),
    );
    case(
        &|p| p[4][0][4][0][1][1] = json!("18446744073709551616"),
        Parameters,
        refusal("bound"),
    );
    case(
        &|p| p[4][0][4][0][1][1] = json!("1".repeat(79)),
        Parameters,
        refusal("wide-bound"),
    );
    case(
        &|p| p[4][0][4][0][1][1] = json!("01"),
        Parameters,
        refusal("noncanonical-bound"),
    );
    // A selector for P alone, although the instance also has V.
    case(
        &|p| p[4][0][4][0][1][2] = json!([["P", "Select", ["n"]]]),
        Parameters,
        refusal("missing-role"),
    );
    case(
        &|p| p[4][0][4][0][1][2] = json!([["P", "Select", ["n"]], ["P", "Select", ["n"]]]),
        Parameters,
        refusal("duplicate-role"),
    );
    case(
        &|p| p[4][0][4][0][1][2][0][1] = json!("missing"),
        Parameters,
        refusal("selector"),
    );
    // A static binding leaves the counted loop with no family to count by.
    case(
        &|p| p[4][0][4][0][1] = json!("3"),
        Parameters,
        refusal("count"),
    );
    // A well-formed selector that returns nothing rather than one index.
    case(
        &|p| {
            p[3][0][3] = json!([]);
            p[3][0][4] = json!([["return", []]]);
        },
        Parameters,
        refusal("signature"),
    );
    // A family participant that calls a same-role participant of another
    // instance: the call is admissible, the dependency is not.
    case(
        &|p| {
            p[4].as_array_mut().unwrap().push(json!([
                "participant",
                "child",
                "other",
                "P",
                [],
                [["n", "index@native.index/1"]],
                ["index@native.index/1"],
                [["return", ["n"]]]
            ]));
            p[4][0][7] = json!([
                ["call", "call", "child", ["n"], ["out"]],
                ["return", ["out"]]
            ]);
        },
        Parameters,
        "interactive-family-dependency".into(),
    );
    case(
        &|p| p[4][0][4][0][1][2][0][2] = json!(["missing"]),
        Parameters,
        refusal("unknown-input"),
    );
    case(
        &|p| p[4][0][4][0][1][2][0][2] = json!(["n", "n"]),
        Parameters,
        refusal("duplicate-input"),
    );
    case(
        &|p| p[4][0][4][0][1][2][0][2] = json!([]),
        Parameters,
        refusal("missing-input"),
    );
    // A family whose selectors omit the participant's own role.
    case(
        &|p| p[4][0][4][0][1][2] = json!([["V", "Select", ["n"]]]),
        Parameters,
        refusal("missing-role"),
    );
    case(
        &|p| p[4][0][4][0][1][2] = json!([]),
        Parameters,
        refusal("missing-role"),
    );
    case(
        &|p| p[4][0][4][0][1][2][0] = json!(["P", "Select"]),
        Parameters,
        "interactive-family-binding".into(),
    );
    for (index, (value, code, detail)) in cases.iter().enumerate() {
        let error = admit(value).unwrap_err();
        assert_eq!(
            (error.code, error.detail.as_str()),
            (*code, detail.as_str()),
            "malformed family case {index}"
        );
    }
}

/// A backend whose values carry no variants refuses one at run time, whatever
/// admission accepted.
#[test]
fn values_without_variants_refuse_to_pack_or_unpack() {
    let descriptor = LogicalType::parse(&zkc_test_support::variants::logical(
        "S",
        json!([["zero", []]]),
    ))
    .unwrap()
    .variant_descriptor()
    .unwrap()
    .clone();
    assert_eq!(
        <Index as Value>::pack_variant(descriptor, 0, vec![])
            .unwrap_err()
            .code,
        "variant-unsupported"
    );
    assert_eq!(
        Index(0).unpack_variant().unwrap_err().code,
        "variant-unsupported"
    );
}

#[test]
fn local_variant_cannot_become_a_family_selector() {
    let ty = format!(
        "{}@logical.variant/1",
        zkc_test_support::variants::logical("Selector", json!([["zero", []]]))
    );
    let mut j = family();
    j[3][0][4]
        .as_array_mut()
        .unwrap()
        .insert(0, json!(["variant", "pack", ty, "zero", [], "v"]));
    let error = admit_supplied(&serde_json::to_vec(&j).unwrap(), &Host::default()).unwrap_err();
    assert_eq!(error.code, ErrorCode::Parameters);
    assert_eq!(error.detail, "variant-family-selector");
}
