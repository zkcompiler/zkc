//! Independent runtime admission and allocation of native Boolean literals.
mod common;
use common::ark_backend;
use serde_json::{Value as Json, json};
use zkc_backends::Value;
use zkc_runtime::interactive::{Action, Runner, StopKind, ValueBudget, admit_supplied};

fn candidate(value: bool) -> Json {
    json!([
        "zkc.program/0",
        [],
        [[
            "function",
            "literal",
            [],
            ["bool@native.bool/0"],
            [
                ["bool_constant", "make", "result", value],
                ["return", ["result"]]
            ],
            ["literal", []]
        ]],
        [[
            "participant",
            "root",
            "instance",
            "P",
            [],
            ["bool@native.bool/0"],
            [
                ["local", "run", "literal", [], ["out"]],
                ["return", ["out"]]
            ],
            []
        ]],
        [["entry", "main", [["P", "root"]]]]
    ])
}
fn bytes(value: &Json) -> Vec<u8> {
    serde_json::to_vec(value).unwrap()
}

#[test]
fn literal_charges_a_step_and_returns_the_exact_boolean() {
    for value in [false, true] {
        let backend = ark_backend(None);
        let admitted = admit_supplied(&bytes(&candidate(value)), &backend).unwrap();
        let mut runner = Runner::new(&admitted, "main", "P", "session", backend, vec![])
            .unwrap_or_else(|_| panic!("entry"));
        let Action::Local(local) = runner.poll() else {
            panic!("local call")
        };
        runner.execute_local(&local.cut).unwrap();
        let Action::Returned(values) = runner.poll() else {
            panic!("return")
        };
        assert!(matches!(values.as_slice(), [Value::Bool(v)] if *v == value));
        assert_eq!(runner.usage().instructions, 4);
        assert!(runner.usage().total_value_bytes > 0);
        assert_eq!(runner.backend().active_frames(), 0);
        assert!(matches!(runner.poll(), Action::Returned(_)));
    }
}

#[test]
fn allocation_failure_has_the_literal_site_and_cleans_frames() {
    let backend = ark_backend(None);
    let admitted = admit_supplied(&bytes(&candidate(true)), &backend).unwrap();
    let mut runner = Runner::new_with_value_budget(
        &admitted,
        "main",
        "P",
        "session",
        backend,
        vec![],
        ValueBudget {
            live_bytes: 0,
            total_bytes: 0,
        },
    )
    .unwrap_or_else(|_| panic!("empty entry"));
    let Action::Local(local) = runner.poll() else {
        panic!("local call")
    };
    runner.execute_local(&local.cut).unwrap();
    let Action::Stopped(stop) = runner.poll() else {
        panic!("limit")
    };
    assert_eq!(stop.kind, StopKind::Limit);
    assert_eq!(stop.site.as_deref(), Some("make"));
    assert_eq!(runner.usage().instructions, 2);
    assert_eq!(runner.usage().live_values, 0);
    assert_eq!(runner.usage().live_value_bytes, 0);
    assert_eq!(runner.backend().active_frames(), 0);
    assert!(stop.cleanup_errors.is_empty());
    let Action::Stopped(again) = runner.poll() else {
        panic!("stable stop")
    };
    assert_eq!(again, stop);
}

#[test]
fn formats_shapes_context_and_names_are_independently_checked() {
    let backend = ark_backend(None);
    let refused =
        |value: Json| assert!(admit_supplied(&bytes(&value), &backend).is_err(), "{value}");
    let mut unknown_format = candidate(true);
    unknown_format[0] = json!("invalid.program");
    refused(unknown_format);
    let mut missing_services = candidate(true);
    missing_services[3][0].as_array_mut().unwrap().pop();
    refused(missing_services);
    for literal in [json!("true"), json!(1), Json::Null, json!([]), json!({})] {
        let mut value = candidate(true);
        value[2][0][4][0][3] = literal;
        refused(value);
    }
    let mut value = candidate(true);
    value.as_array_mut().unwrap().insert(2, json!("logical"));
    refused(value);
    let mut value = candidate(true);
    value[2][0][4][0]
        .as_array_mut()
        .unwrap()
        .push(json!("extra"));
    refused(value);
    let mut value = candidate(true);
    value[2][0][4][0][1] = json!("");
    refused(value);
    let mut value = candidate(true);
    value[2][0][4][0][2] = json!("bad/name");
    refused(value);
    let mut value = candidate(true);
    let duplicate = value[2][0][4][0].clone();
    value[2][0][4].as_array_mut().unwrap().insert(1, duplicate);
    refused(value);
    let mut value = candidate(true);
    value[3][0][6]
        .as_array_mut()
        .unwrap()
        .insert(0, json!(["bool_constant", "root_literal", "v", true]));
    refused(value);
    let mut value = candidate(true);
    value[2][0][3] = json!(["index@native.index/0"]);
    refused(value);
}

#[derive(Clone, Debug)]
struct WrongBoolean;
impl zkc_runtime::interactive::Value for WrongBoolean {
    fn from_control_bool(_: bool) -> Result<Self, zkc_runtime::interactive::BackendError> {
        Ok(Self)
    }
    fn physical_type(&self) -> zkc_runtime::interactive::PhysicalType {
        zkc_runtime::interactive::PhysicalType::parse("index@native.index/0").unwrap()
    }
    fn validate_serializable(&self) -> Result<(), zkc_runtime::interactive::BackendError> {
        Ok(())
    }
    fn retained_bytes(&self) -> usize {
        8
    }
}
struct LiteralAdapter {
    installed: bool,
    entered: usize,
    active: usize,
}
impl zkc_runtime::interactive::Backend for LiteralAdapter {
    type Value = WrongBoolean;
    fn supports_boolean_literals(&self) -> bool {
        self.installed
    }
    fn validate_value(
        &self,
        _: &WrongBoolean,
    ) -> Result<(), zkc_runtime::interactive::BackendError> {
        Ok(())
    }
    fn enter_frame(
        &mut self,
        _: &zkc_runtime::interactive::Frame,
        _: &[WrongBoolean],
    ) -> Result<(), zkc_runtime::interactive::BackendError> {
        self.entered += 1;
        self.active += 1;
        Ok(())
    }
    fn leave_frame(
        &mut self,
        _: &zkc_runtime::interactive::Frame,
        _: zkc_runtime::interactive::FrameExit,
        _: &[WrongBoolean],
    ) -> Result<(), zkc_runtime::interactive::BackendError> {
        self.active -= 1;
        Ok(())
    }
    fn apply(
        &mut self,
        _: &zkc_runtime::interactive::Invocation<'_>,
        _: &[WrongBoolean],
    ) -> Result<Vec<WrongBoolean>, zkc_runtime::interactive::BackendError> {
        unreachable!()
    }
}
#[test]
fn unsupported_adapter_is_refused_before_any_prefix_and_rechecked_on_entry() {
    let mut value = candidate(true);
    value[2].as_array_mut().unwrap().push(json!([
        "function",
        "prefix",
        [],
        [],
        [["return", []]],
        ["prefix", []]
    ]));
    value[3][0][6]
        .as_array_mut()
        .unwrap()
        .insert(0, json!(["local", "before", "prefix", [], []]));
    let bytes = bytes(&value);
    let adapter = LiteralAdapter {
        installed: false,
        entered: 0,
        active: 0,
    };
    let error = admit_supplied(&bytes, &adapter).expect_err("unsupported installation");
    assert_eq!(error.code, zkc_runtime::interactive::ErrorCode::Backend);
    assert!(error.detail.contains("native-boolean-unsupported"));
    assert_eq!(adapter.entered, 0);
    let admitted = admit_supplied(&bytes, &ark_backend(None)).unwrap();
    assert!(admitted.requires_boolean_literals());
    let failure = Runner::new(&admitted, "main", "P", "session", adapter, vec![])
        .err()
        .expect("entry rechecks installation");
    assert_eq!(failure.backend.entered, 0);
    assert_eq!(failure.backend.active, 0);
}
#[test]
fn a_false_adapter_promise_does_not_bypass_runtime_type_validation() {
    let adapter = LiteralAdapter {
        installed: true,
        entered: 0,
        active: 0,
    };
    let admitted = admit_supplied(&bytes(&candidate(true)), &adapter).unwrap();
    let mut runner = Runner::new(&admitted, "main", "P", "session", adapter, vec![])
        .unwrap_or_else(|_| panic!("entry"));
    let Action::Local(local) = runner.poll() else {
        panic!("local call")
    };
    runner.execute_local(&local.cut).unwrap();
    let Action::Stopped(stop) = runner.poll() else {
        panic!("invalid literal")
    };
    assert_eq!(stop.site.as_deref(), Some("make"));
    assert_eq!(
        stop.kind,
        StopKind::Backend(zkc_runtime::interactive::BackendError::new(
            "runtime-contract:Payload"
        ))
    );
    assert_eq!(runner.backend().active, 0);
    assert_eq!(runner.usage().live_values, 0);
}
#[test]
fn only_the_selected_nested_literal_executes() {
    for condition in [false, true] {
        let mut value = candidate(condition);
        value[2][0][4] = json!([
            ["bool_constant", "make", "condition", condition],
            [
                "if",
                "choose",
                "condition",
                [],
                [
                    ["bool_constant", "true_value", "yes", true],
                    ["yield", ["yes"]]
                ],
                [
                    ["bool_constant", "false_value", "no", false],
                    ["yield", ["no"]]
                ],
                ["result"]
            ],
            ["return", ["result"]]
        ]);
        let backend = ark_backend(None);
        let admitted = admit_supplied(&bytes(&value), &backend).unwrap();
        let mut runner = Runner::new(&admitted, "main", "P", "session", backend, vec![])
            .unwrap_or_else(|_| panic!("entry"));
        let Action::Local(local) = runner.poll() else {
            panic!("local")
        };
        runner.execute_local(&local.cut).unwrap();
        let Action::Returned(values) = runner.poll() else {
            panic!("return")
        };
        assert!(matches!(values.as_slice(), [Value::Bool(value)] if *value == condition));
        assert_eq!(runner.usage().instructions, 7);
        assert_eq!(runner.backend().active_frames(), 0);
    }
}

#[test]
fn unused_literal_definitions_are_admitted_and_require_backend_support() {
    let mut value = candidate(true);
    // The endpoint never calls the retained literal function.
    value[3][0][5] = json!([]);
    value[3][0][6] = json!([["return", []]]);
    assert!(
        admit_supplied(&bytes(&value), &ark_backend(None))
            .unwrap()
            .requires_boolean_literals()
    );
    let adapter = LiteralAdapter {
        installed: false,
        entered: 0,
        active: 0,
    };
    let error = admit_supplied(&bytes(&value), &adapter)
        .expect_err("unused literal still requires support");
    assert!(error.detail.contains("native-boolean-unsupported"));
    value[2][0][4][0][3] = json!("malformed");
    assert!(admit_supplied(&bytes(&value), &ark_backend(None)).is_err());
}

#[test]
fn native_endpoint_stops_are_not_local_stops() {
    for terminal in [
        json!(["stop", "end", "reject"]),
        json!(["incomplete", "end"]),
    ] {
        let mut value = candidate(true);
        value[3][0][6] = json!([terminal]);
        let error = admit_supplied(&bytes(&value), &ark_backend(None))
            .err()
            .unwrap();
        assert_eq!(error.detail, "unknown participant instruction");
    }
}

#[cfg(feature = "test-utils")]
#[test]
fn program_service_query_executes_and_releases_its_lease() {
    use zkc_backends::{Scalar, services::ServiceRegistry};
    use zkc_runtime::interactive::{Action, Runner};
    let registry = ServiceRegistry::new(zkc_backends::Policy::default());
    let root = registry
        .issue_test_tape("P", 1, vec![Scalar::from(17)])
        .unwrap();
    let backend = ark_backend(None)
        .with_services(
            registry.clone(),
            std::collections::BTreeMap::from([("coins".into(), root.clone())]),
        )
        .unwrap();
    let field = "field:bls12-381.fr@arkworks.fr/0";
    let carrier = json!([
        "zkc.program/0",
        [],
        [],
        [[
            "participant",
            "p",
            "root",
            "P",
            [],
            [field],
            [
                ["query", "sample", "coins", "draw", [], ["x"]],
                ["return", ["x"]]
            ],
            [["coins", "random.bls12-381.fr/0", "0"]]
        ]],
        [["entry", "main", [["P", "p"]]]]
    ]);
    let admitted = admit_supplied(&bytes(&carrier), &backend).unwrap();
    let mut runner = Runner::new(&admitted, "main", "P", "session", backend, vec![])
        .unwrap_or_else(|e| panic!("{}", e.error));
    let Action::Query(query) = runner.poll() else {
        panic!("query")
    };
    runner.execute_query(&query.cut).unwrap();
    let Action::Returned(values) = runner.poll() else {
        panic!("return")
    };
    assert!(matches!(&values[..], [Value::Field(x)] if *x == Scalar::from(17)));
    let observation = registry.observe(&root).unwrap();
    assert!(!observation.leased && !observation.poisoned);
    let state = observation.state.unwrap();
    assert_eq!(
        (state.generation, state.draw_count, state.budget),
        (1, 1, 0)
    );
    let mut unknown_format = carrier;
    unknown_format[0] = json!("invalid.program");
    let error = admit_supplied(&bytes(&unknown_format), runner.backend())
        .err()
        .unwrap();
    assert_eq!(error.code, zkc_runtime::interactive::ErrorCode::Record);
    assert_eq!(error.detail, "unknown participant module format");
}

#[test]
fn program_iteration_exhaustion_preserves_the_attempted_loop_coordinate() {
    use zkc_runtime::interactive::{PathElement, WorkBudget};
    let carrier = json!([
        "zkc.program/0",
        [],
        [],
        [[
            "participant",
            "p",
            "root",
            "P",
            [["n", "index@native.index/0"]],
            [],
            [
                [
                    "loop",
                    "rounds",
                    ["value", "n", "8", "i"],
                    [],
                    [],
                    [["yield", []]],
                    []
                ],
                ["return", []]
            ],
            []
        ]],
        [["entry", "main", [["P", "p"]]]]
    ]);
    let admitted =
        admit_supplied(&serde_json::to_vec(&carrier).unwrap(), &ark_backend(None)).unwrap();
    for iterations in [0, 1] {
        let mut runner = Runner::new_with_budgets(
            &admitted,
            "main",
            "P",
            "session",
            ark_backend(None),
            vec![Value::Index(3)],
            ValueBudget::default(),
            WorkBudget {
                iterations,
                ..WorkBudget::default()
            },
        )
        .unwrap_or_else(|e| panic!("{}", e.error));
        let root = runner.root_origin().clone();
        runner.enter_loop(&root, "rounds", 3).unwrap();
        if iterations == 1 {
            let mut child = root.clone();
            child.path.push(PathElement::Loop {
                site: "rounds".into(),
                iteration: 0,
            });
            runner.yield_loop(&child).unwrap();
        }
        let stop = runner.stop().unwrap();
        assert_eq!(stop.kind, StopKind::Limit);
        assert_eq!(stop.site.as_deref(), Some("rounds"));
        assert_eq!(
            stop.origin.path,
            vec![PathElement::Loop {
                site: "rounds".into(),
                iteration: iterations
            }]
        );
        assert_eq!(runner.usage().iterations, iterations);
    }
}
