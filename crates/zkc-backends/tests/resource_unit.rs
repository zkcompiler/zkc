//! Independent physical admission and real native logical resource execution.
mod common;
use common::*;
use serde_json::{Value as Json, json};
use zkc_backends::Value;
use zkc_runtime::interactive::{
    AdmissionError, Backend, ErrorCode, LogicalType, PhysicalType, Runner, Type, admit_supplied,
};

fn ty(domain: &str) -> String {
    format!("resource_unit:{domain}@logical.resource_unit/1")
}
fn fixture(ports: Json, results: Json, body: Json, args: Json, names: Json) -> Json {
    json!([
        "zkc.participants/1",
        [
            [
                "make",
                "resource_unit.create",
                ["Slot.A"],
                "logical/resource_unit.create"
            ],
            [
                "pass",
                "resource_unit.pass",
                ["Slot.A"],
                "logical/resource_unit.pass"
            ],
            [
                "consume",
                "resource_unit.consume",
                ["Slot.A"],
                "logical/resource_unit.consume"
            ]
        ],
        "physical",
        [["function", "Local", ports, results, body, ["Local", []]]],
        [[
            "participant",
            "root_P",
            "root",
            "P",
            [],
            ports,
            results,
            [["local", "work", "Local", args, names], ["return", names]]
        ]],
        [["entry", "main", [["P", "root_P"]]]]
    ])
}
fn make() -> Json {
    fixture(
        json!([]),
        json!([ty("Slot.A")]),
        json!([["op", "make", "make", [], [], ["x"]], ["return", ["x"]]]),
        json!([]),
        json!(["x"]),
    )
}
fn bytes(j: &Json) -> Vec<u8> {
    serde_json::to_vec(j).unwrap()
}
fn refusal<T: std::fmt::Debug>(result: Result<T, AdmissionError>) -> (ErrorCode, String) {
    let error = result.unwrap_err();
    (error.code, error.detail)
}
fn refused_as<T: std::fmt::Debug>(
    result: Result<T, AdmissionError>,
    code: ErrorCode,
    detail: &str,
) {
    assert_eq!(refusal(result), (code, detail.to_owned()));
}

#[test]
fn exact_nominal_formation_and_no_wire_permission() {
    let a = LogicalType::parse("resource_unit:Slot.A").unwrap();
    let b = LogicalType::parse("resource_unit:Slot.B").unwrap();
    assert_ne!(a, b);
    assert_eq!(a.spelling(), "resource_unit:Slot.A");
    assert!(a.kind().is_affine());
    assert!(!a.kind().is_duplicable());
    assert!(a.kind().is_discardable());
    assert!(a.codec().is_none());
    assert!(!PhysicalType::default_for(a.clone()).is_serializable());
    assert_eq!(a.kind(), Type::ResourceUnit);
    for (bad, detail) in [
        ("resource_unit", "explicit nominal identity required"),
        ("resource_unit:", "explicit nominal identity required"),
        ("resource_unit:0abc", "resource-unit-domain"),
        ("resource_unit:A:B", "resource-unit-domain"),
        ("resource_unit:A@x", "resource-unit-domain"),
        ("field:Slot.A", "uninstalled nominal identity"),
        ("resource_unit:é", "resource-unit-domain"),
    ] {
        assert_eq!(
            refusal(LogicalType::parse(bad)),
            (ErrorCode::Type, detail.to_owned()),
            "{bad}"
        );
    }
    refused_as(
        PhysicalType::parse("resource_unit:Slot.A@host.resource/1"),
        ErrorCode::Type,
        "representation does not implement logical type",
    );
    let domain = format!("A{}", "b".repeat(127));
    assert!(LogicalType::parse(&format!("resource_unit:{domain}")).is_ok());
    refused_as(
        LogicalType::parse(&format!("resource_unit:{domain}b")),
        ErrorCode::Type,
        "resource-unit-domain",
    );
}

#[test]
fn create_pass_consume_and_host_alias_refusal() {
    let (values, backend) = run(&bytes(&make()), ark_backend(None), vec![]);
    let value = values.unwrap().remove(0);
    assert!(matches!(value, Value::ResourceUnit(_)));
    assert_eq!(
        backend.encode_value(&value).unwrap_err().code,
        "refused:nonserializable"
    );
    let unrelated = ark_backend(None);
    assert_eq!(
        unrelated.validate_value(&value).unwrap_err().code,
        "refused:capability-authority"
    );
    let mut dup = fixture(
        json!([["a", ty("Slot.A")], ["b", ty("Slot.A")]]),
        json!([]),
        json!([["return", []]]),
        json!(["a", "b"]),
        json!([]),
    );
    let admitted = admit_supplied(&bytes(&dup), &backend).unwrap();
    let error = Runner::new(
        &admitted,
        "main",
        "P",
        "session",
        backend,
        vec![value.clone(), value.clone()],
    )
    .err()
    .expect("alias refused");
    assert!(error.error.to_string().contains("capability-alias"));
    let backend = error.backend;
    let pass = fixture(
        json!([["a", ty("Slot.A")]]),
        json!([ty("Slot.A")]),
        json!([["op", "step", "pass", [], ["a"], ["b"]], ["return", ["b"]]]),
        json!(["a"]),
        json!(["b"]),
    );
    let (values, backend) = run(&bytes(&pass), backend, vec![value.clone()]);
    let next = values.unwrap().remove(0);
    assert_eq!(
        backend.validate_value(&value).unwrap_err().code,
        "refused:capability-stale"
    );
    let consume = fixture(
        json!([["a", ty("Slot.A")]]),
        json!([]),
        json!([["op", "use", "consume", [], ["a"], []], ["return", []]]),
        json!(["a"]),
        json!([]),
    );
    let (values, backend) = run(&bytes(&consume), backend, vec![next.clone()]);
    assert!(values.unwrap().is_empty());
    // Consumption removes the slot, so the token no longer names an issued one.
    assert_eq!(
        backend.validate_value(&next).unwrap_err().code,
        "refused:capability-unissued"
    );
    // Independent source-like structural forgeries cannot acquire a copy permission.
    dup[3][0][4] = json!([
        ["op", "use", "consume", [], ["a"], []],
        ["op", "again", "consume", [], ["a"], []],
        ["return", []]
    ]);
    assert!(
        admit_supplied(&bytes(&dup), &backend)
            .unwrap_err()
            .to_string()
            .contains("consumed operand")
    );
}

#[test]
fn duplicate_result_wrong_domain_codec_and_implementation_refused() {
    let backend = ark_backend(None);
    let mut bad = make();
    bad[3][0][3] = json!([ty("Slot.A"), ty("Slot.A")]);
    bad[3][0][4][1] = json!(["return", ["x", "x"]]);
    assert!(
        admit_supplied(&bytes(&bad), &backend)
            .unwrap_err()
            .to_string()
            .contains("consumed operand")
    );
    let mut bad = make();
    bad[3][0][3] = json!([ty("Slot.B")]);
    refused_as(
        admit_supplied(&bytes(&bad), &backend),
        ErrorCode::Signature,
        "function-return-types: operand type x",
    );
    // A slot that is not a domain, refused under the binding's own rule as
    // the compiler and the Lean reader refuse it.
    let mut bad = make();
    bad[1][0][2] = json!(["0invalid"]);
    refused_as(
        admit_supplied(&bytes(&bad), &backend),
        ErrorCode::Type,
        "binding-resource-unit-domain",
    );
    let mut bad = make();
    bad[1][0][3] = json!("arkworks/resource_unit.create");
    refused_as(
        admit_supplied(&bytes(&bad), &backend),
        ErrorCode::Signature,
        "binding-implementation",
    );
    let mut bad = make();
    bad[3][0][4][0][3] = json!(["bytes"]);
    refused_as(
        admit_supplied(&bytes(&bad), &backend),
        ErrorCode::Attributes,
        "interactive-kernel-parameters: exact kernel attributes required",
    );
    let mut bad = make();
    bad[4][0][7] = json!([
        ["local", "work", "Local", [], ["x"]],
        ["send", "wire", "unit", "V", "x"],
        ["return", ["x"]]
    ]);
    refused_as(
        admit_supplied(&bytes(&bad), &backend),
        ErrorCode::Type,
        "nonserializable message type",
    );
}

#[test]
fn fresh_occurrences_are_distinct_and_unused_permissions_may_drop() {
    let program = fixture(
        json!([]),
        json!([ty("Slot.A"), ty("Slot.A")]),
        json!([
            ["op", "first", "make", [], [], ["a"]],
            ["op", "second", "make", [], [], ["b"]],
            ["return", ["a", "b"]]
        ]),
        json!([]),
        json!(["a", "b"]),
    );
    let (values, backend) = run(&bytes(&program), ark_backend(None), vec![]);
    let values = values.unwrap();
    let (Value::ResourceUnit(a), Value::ResourceUnit(b)) = (&values[0], &values[1]) else {
        panic!("unit results");
    };
    assert_ne!(a.capability().issued_id(), b.capability().issued_id());
    assert_eq!(a.domain(), b.domain());
    let drop = fixture(
        json!([["a", ty("Slot.A")], ["b", ty("Slot.A")]]),
        json!([]),
        json!([["return", []]]),
        json!(["a", "b"]),
        json!([]),
    );
    let (out, backend) = run(&bytes(&drop), backend, values.clone());
    assert!(out.unwrap().is_empty());
    // Dropping an unused permission at frame exit retires its slot.
    for value in &values {
        assert_eq!(
            backend.validate_value(value).unwrap_err().code,
            "refused:capability-unissued"
        );
    }
}

#[test]
fn logical_permission_cannot_cross_role_or_escape_a_selected_branch() {
    let (values, backend) = run(&bytes(&make()), ark_backend(None), vec![]);
    let value = values.unwrap().remove(0);
    let mut other = fixture(
        json!([["a", ty("Slot.A")]]),
        json!([]),
        json!([["return", []]]),
        json!(["a"]),
        json!([]),
    );
    other[4][0][3] = json!("V");
    other[5][0][2][0][0] = json!("V");
    let admitted = admit_supplied(&bytes(&other), &backend).unwrap();
    let error = Runner::new(
        &admitted,
        "main",
        "V",
        "session",
        backend,
        vec![value.clone()],
    )
    .err()
    .expect("role refusal");
    assert!(
        error.error.to_string().contains("entry-domain"),
        "{}",
        error.error
    );
    let backend = error.backend;
    let branch = json!([
        ["op", "advance", "pass", [], ["a"], ["next"]],
        ["yield", ["next"]]
    ]);
    let mut other_branch = branch.clone();
    other_branch[0][1] = json!("advance_else");
    let program = fixture(
        json!([["a", ty("Slot.A")], ["choose", "bool@native.bool/1"]]),
        json!([ty("Slot.A")]),
        json!([
            [
                "if",
                "branch",
                "choose",
                ["a"],
                branch,
                other_branch,
                ["out"]
            ],
            ["return", ["out"]]
        ]),
        json!(["a", "choose"]),
        json!(["out"]),
    );
    let mut program = program;
    let (out, backend) = run(
        &bytes(&program),
        backend,
        vec![value.clone(), Value::Bool(true)],
    );
    assert_eq!(out.unwrap().len(), 1);
    assert_eq!(
        backend.validate_value(&value).unwrap_err().code,
        "refused:capability-stale"
    );
    // Both arms must check; the unselected arm cannot duplicate the capture.
    program[3][0][4][0][5]
        .as_array_mut()
        .unwrap()
        .insert(1, json!(["op", "reuse", "consume", [], ["a"], []]));
    refused_as(
        admit_supplied(&bytes(&program), &backend),
        ErrorCode::Ssa,
        "interactive-resource-reuse: consumed operand a",
    );
}
