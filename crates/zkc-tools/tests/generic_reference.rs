//! Differential execution of original generic source and actual native output.
//! Successful relayouts are erased from logical traces, not from native execution.

#![cfg(feature = "test-utils")]

use serde_json::{Value as Json, json};
use std::collections::BTreeMap;
use zkc_backends::{GroupPoint, Policy, Scalar, Value};
use zkc_runtime::interactive::{Action, Packet, Runner, StopKind, admit_physical};
use zkc_tools::protocol::{JointOutcome, ParticipantChecker, Schedule, drive};

#[path = "generic_reference/boundaries.rs"]
mod boundaries;
#[path = "generic_reference/commitments.rs"]
mod commitments;
#[path = "generic_reference/multiple_resources.rs"]
mod multiple_resources;
#[path = "generic_reference/nonces.rs"]
mod nonces;
#[path = "generic_reference/origins.rs"]
mod origins;
#[path = "generic_reference/physical.rs"]
mod physical;
#[path = "generic_reference/public_inputs.rs"]
mod public_inputs;
#[path = "generic_reference/receiving_setups.rs"]
mod receiving_setups;
#[path = "generic_reference/resource_boundaries.rs"]
mod resource_boundaries;
#[path = "generic_reference/support.rs"]
mod support;
#[path = "generic_reference/transcripts.rs"]
mod transcripts;
use support::*;

#[test]
fn generic_source_matches_native_values_origins_and_consumed_resources() {
    let fixture = Fixture::new();
    for rank in 1..=4 {
        for seed in 0..4u64 {
            let cells: Vec<_> = (0..1 << rank)
                .map(|i| (i * i + seed * (i + 3)) % 101)
                .collect();
            fixture.compare(&cells, &[seed * 7], 2, true, 2);
        }
    }
    fixture.compare(&[0, 1, 4, 9], &[2], 2, false, 0);
    fixture.compare(&[9], &[2], 2, true, 1);
    fixture.compare(&[0, 1, 4, 9], &[2], 0, true, 0);
    fixture.compare(&[0, 1, 4, 9], &[], 2, true, 0);
}

#[test]
fn generic_reference_retains_loop_and_child_origins() {
    let mut fixture = Fixture::new();
    let mut source: Json = serde_json::from_slice(&fixture.source).unwrap();
    let common = &mut source[3];
    let child = common[3][0].clone();
    let mut root = child.clone();
    root[1] = json!("Repeated");
    root[6] = json!([["child", "OneStep", []]]);
    root[7] = json!([
        [
            "loop",
            "rounds",
            ["constant", "2"],
            [["r", "rng"], ["t", "table"]],
            ["allowed"],
            [
                [
                    "call",
                    "child_step",
                    "child",
                    ["r", "t", "allowed"],
                    ["folded", "next"]
                ],
                ["yield", ["next", "folded"]]
            ],
            ["last", "result"]
        ],
        ["return", ["result", "last"]]
    ]);
    common[3] = json!([child, root]);
    common[4] = json!([
        [
            "instance",
            "child_instance",
            "OneStep",
            [],
            [],
            [["P", "P"]]
        ],
        [
            "instance",
            "concrete",
            "Repeated",
            [],
            [["child", "child_instance"]],
            [["P", "P"]]
        ]
    ]);
    fixture.set_source(&source);
    fixture.compare(&[0, 1, 4, 9], &[2, 3], 2, true, 4);
    fixture.compare(&[0, 1, 4, 9], &[2], 2, true, 2);
    fixture.compare(&[0, 1, 4, 9], &[2, 3], 1, true, 2);
    fixture.compare(&[0, 1, 4, 9], &[2, 3], 2, false, 0);
}

#[test]
fn mixed_instances_use_independent_math_and_explicit_group_contracts() {
    let fixture = Fixture::from_fixture("generic-operations.pir");
    let checker = ParticipantChecker::new(&fixture.checker_path).unwrap();
    let admitted =
        admit_physical(&fixture.source, &fixture.candidate, &backend(), &checker).unwrap();
    let table = |cells: &[u64]| {
        Value::table(
            &cells.iter().copied().map(Scalar::from).collect::<Vec<_>>(),
            &Policy::default(),
        )
        .unwrap()
    };
    let p_inputs = vec![
        table(&[0, 1, 4, 9]),
        table(&[2, 3, 5, 7]),
        Value::Curve(GroupPoint::generator()),
        Value::Bool(true),
        Value::Bool(false),
    ];
    let v_inputs = vec![Value::Field(Scalar::from(2))];
    let p_ports: Vec<_> = ["a", "b", "g", "x", "y"]
        .into_iter()
        .zip(&p_inputs)
        .map(|(n, v)| json!([n, value_json(v)]))
        .collect();
    let mut inputs = json!([
        "zkc.reference-inputs/1",
        "main",
        "test",
        [["P", p_ports], ["V", [["r", value_json(&v_inputs[0])]]]],
        [],
        [],
        []
    ]);
    let mut runners = BTreeMap::new();
    let mut trace = Trace::new(&fixture.source);
    for (role, values) in [("P", p_inputs), ("V", v_inputs)] {
        let observer = Observed {
            inner: backend_for(role),
            source_map: admitted.source_map().unwrap().clone(),
            events: trace.clone(),
            conversions: 0,
        };
        runners.insert(
            role.to_owned(),
            Runner::new(&admitted, "main", role, "test", observer, values)
                .unwrap_or_else(|e| panic!("{}", e.error)),
        );
    }
    let mut schedule = Schedule::new(&admitted, "main", "test").unwrap();
    let report = drive(&mut schedule, &mut runners, &mut trace);
    let JointOutcome::Returned(values) = report.outcome else {
        panic!("native failed")
    };
    assert_eq!(report.wire.messages, 1);
    let native = trace.snapshot();
    assert_eq!(runners["P"].backend().conversions, 2);

    // A real G1 input is unresolved until its exact validation request is filled.
    let missing = fixture.reference(&inputs);
    assert_eq!(missing[3][0], "pending-primitive");
    let validate = missing[4][0][1].clone();
    assert_eq!(validate[2], "validate");
    assert_eq!(validate[5][0], inputs[3][0][1][2][1]);
    inputs[5] = json!([[validate, ["ok", []]]]);
    let missing = fixture.reference(&inputs);
    assert_eq!(missing[3][0], "pending-primitive");
    let request = missing[4].as_array().unwrap().last().unwrap()[1].clone();
    assert_eq!(request[2], "curve.scale");
    let response = native
        .iter()
        .find(|e| e[0] == "response" && e[1] == request)
        .unwrap();
    // Conditional group evidence: the backend supplies this mathematical answer.
    // Matching the full source request independently checks the actual operands,
    // nominal identity and origin; this is not an independent G1 implementation.
    inputs[5]
        .as_array_mut()
        .unwrap()
        .push(json!([request, ["ok", response[2]]]));
    let result = fixture.reference(&inputs);
    assert_eq!(
        result[3],
        json!([
            "returned",
            values["P"].iter().map(value_json).collect::<Vec<_>>()
        ])
    );
    let logical: Vec<_> = result[4]
        .as_array()
        .unwrap()
        .iter()
        .filter(|e| e[0] != "external")
        .cloned()
        .collect();
    assert_eq!(logical, native);
    assert_eq!(
        result[4]
            .as_array()
            .unwrap()
            .iter()
            .filter(|e| e[0] == "send")
            .count(),
        1
    );
    assert_eq!(
        result[4]
            .as_array()
            .unwrap()
            .iter()
            .filter(|e| e[0] == "receive")
            .count(),
        1
    );
    assert!(
        runners
            .values()
            .all(|r| r.backend().inner.active_frames() == 0)
    );

    let mut wrong = inputs.clone();
    wrong[5][1][0][1][5] = json!("different-operation-site");
    assert_eq!(fixture.reference(&wrong)[3][0], "pending-primitive");
    let mut wrong = inputs.clone();
    wrong[5][1][1] = json!(["ok", [["bool", "true"]]]);
    assert_eq!(fixture.reference(&wrong)[3][1], "runtime-kernel-results");
    let mut extra = inputs.clone();
    extra[5]
        .as_array_mut()
        .unwrap()
        .push(json!(["unrequested", ["ok", []]]));
    assert_eq!(fixture.reference(&extra)[3][1], "unused-primitive-replies");
}

#[test]
fn generic_open_role_reads_only_its_ports_and_exact_peer_replies() {
    let mut fixture = Fixture::from_fixture("generic-operations.pir");
    let mut source: Json = serde_json::from_slice(&fixture.source).unwrap();
    let protocol = &mut source[3][3][0];
    protocol[4] = json!([["a", "P", "bool"], ["b", "V", "bool"]]);
    protocol[5] = json!([["P", "bool"], ["V", "bool"]]);
    protocol[7] = json!([
        ["message", "offer", "flag", "P", "V", "a", "received"],
        [
            "local",
            "combine",
            "V",
            "Boolean",
            ["received", "b"],
            ["combined"]
        ],
        [
            "message", "answer", "result", "V", "P", "combined", "answer"
        ],
        ["return", ["a", "combined"]]
    ]);
    fixture.set_source(&source);
    let checker = ParticipantChecker::new(&fixture.checker_path).unwrap();
    let admitted =
        admit_physical(&fixture.source, &fixture.candidate, &backend(), &checker).unwrap();
    let mut runners = BTreeMap::new();
    let mut trace = Trace::new(&fixture.source);
    for (role, flag) in [("P", true), ("V", false)] {
        let observed = Observed {
            inner: backend_for(role),
            source_map: admitted.source_map().unwrap().clone(),
            events: trace.clone(),
            conversions: 0,
        };
        runners.insert(
            role.to_owned(),
            Runner::new(
                &admitted,
                "main",
                role,
                "test",
                observed,
                vec![Value::Bool(flag)],
            )
            .unwrap_or_else(|e| panic!("{}", e.error)),
        );
    }
    let mut schedule = Schedule::new(&admitted, "main", "test").unwrap();
    let report = drive(&mut schedule, &mut runners, &mut trace);
    let JointOutcome::Returned(values) = report.outcome else {
        panic!("native terminal")
    };
    let inputs = json!([
        "zkc.reference-inputs/1",
        "main",
        "test",
        [
            ["P", [["a", ["bool", "true"]]]],
            ["V", [["b", ["bool", "false"]]]]
        ],
        [],
        [],
        []
    ]);
    let joint = fixture.reference(&inputs);
    assert_eq!(
        joint[3],
        json!([
            "returned",
            [value_json(&values["P"][0]), value_json(&values["V"][0])]
        ])
    );
    assert_eq!(report.wire.messages, 2);
    let events: Vec<_> = joint[4]
        .as_array()
        .unwrap()
        .iter()
        .filter(|e| e[0] != "external")
        .cloned()
        .collect();
    assert_eq!(events, trace.snapshot());

    let mut role = inputs.clone();
    role[3] = json!([["V", [["b", ["bool", "false"]]]]]);
    let (ok, pending) = fixture.reference_as(&role, Some("V"));
    assert!(ok);
    assert_eq!(pending[3][0], "pending");
    assert_eq!(pending[4], json!([]));
    let reply_key = json!(["receive", pending[3][2], "flag", "P", "bool"]);
    role[6] = json!([[reply_key, ["bool", "true"]]]);
    let (ok, complete) = fixture.reference_as(&role, Some("V"));
    assert!(ok);
    assert_eq!(
        complete[3],
        json!(["returned", [value_json(&values["V"][0])]])
    );
    assert_eq!(
        complete[4]
            .as_array()
            .unwrap()
            .iter()
            .filter(|e| e[0] == "send")
            .count(),
        1
    );

    let mut wrong = role.clone();
    wrong[6][0][0][2] = json!("different-schema");
    let (_, result) = fixture.reference_as(&wrong, Some("V"));
    assert_eq!(result[3][1], "reply-origin");
    assert_eq!(result[6], "1");
    assert_eq!(result[4], json!([]));
    let mut wrong = role.clone();
    wrong[6][0][1] = json!(["field:bls12-381.fr", "1"]);
    assert_eq!(
        fixture.reference_as(&wrong, Some("V")).1[3][1],
        "reply-type"
    );
    assert_eq!(
        fixture.reference_as(&inputs, Some("V")),
        (false, json!(["refused", "input-roles"]))
    );
    let mut duplicate = role.clone();
    duplicate[6]
        .as_array_mut()
        .unwrap()
        .push(role[6][0].clone());
    assert_eq!(
        fixture.reference_as(&duplicate, Some("V")),
        (false, json!(["refused", "duplicate-reference-request"]))
    );
}

#[test]
fn generic_reference_rejects_aliases_and_malformed_nominal_inputs() {
    let mut fixture = Fixture::new();
    let mut inputs = json!([
        "zkc.reference-inputs/1",
        "main",
        "test",
        [[
            "P",
            [
                ["rng", ["rng:bls12-381.fr", ["draws", "0"]]],
                ["table", ["table:bls12-381.fr", ["1", ["0", "1"]]]],
                ["allowed", ["bool", "true"]]
            ]
        ]],
        [["draws", "P", [], "2", ["rng", ["2"]]]],
        [],
        []
    ]);
    let mut old = inputs.clone();
    old[4][0][4] = json!(["2"]);
    assert_eq!(
        fixture.reference_as(&old, None),
        (false, json!(["refused", "resource-initializer"]))
    );
    let mut wrong_kind = inputs.clone();
    wrong_kind[4][0][4] = json!(["nonce", "2"]);
    assert_eq!(
        fixture.reference_as(&wrong_kind, None),
        (false, json!(["refused", "capability-kind"]))
    );
    let mut forged_stage = inputs.clone();
    forged_stage[4][0][4] = json!(["committed-nonce", "2"]);
    assert_eq!(
        fixture.reference_as(&forged_stage, None),
        (false, json!(["refused", "resource-kind"]))
    );
    let mut wrong = inputs.clone();
    wrong[3][0][1][1][1][0] = json!("table:bls12-381.fr@arkworks.mle-lsb/1");
    assert_eq!(
        fixture.reference_as(&wrong, None),
        (false, json!(["refused", "binding-type"]))
    );
    let mut wrong = inputs.clone();
    wrong[3][0][1][0][1][1][1] = json!("1");
    assert_eq!(
        fixture.reference_as(&wrong, None),
        (false, json!(["refused", "capability-stale"]))
    );
    let mut source: Json = serde_json::from_slice(&fixture.source).unwrap();
    source[3][3][0][4]
        .as_array_mut()
        .unwrap()
        .push(json!(["second", "P", "rng:bls12-381.fr"]));
    fixture.set_source(&source);
    inputs[3][0][1]
        .as_array_mut()
        .unwrap()
        .push(json!(["second", ["rng:bls12-381.fr", ["draws", "0"]]]));
    assert_eq!(
        fixture.reference_as(&inputs, None),
        (false, json!(["refused", "capability-alias"]))
    );
}

#[test]
fn generic_nested_algorithms_execute_in_two_nominal_fields() {
    let fixture = Fixture::from_fixture("generic-composition.pir");
    for value in [0u64, 1, 19, 536_870_913, 2_130_706_432] {
        let result = compare_pure(
            &fixture,
            &[
                ("x", Value::Field(Scalar::from(value))),
                (
                    "y",
                    Value::KoalaBearField(
                        zkc_backends::parse_koala_bear_decimal(&value.to_string()).unwrap(),
                    ),
                ),
            ],
            "generic-composition",
        );
        assert_eq!(
            result[3],
            json!([
                "returned",
                [
                    ["field:bls12-381.fr", (4 * value).to_string()],
                    [
                        "field:koala-bear",
                        ((4 * value) % 2_130_706_433).to_string()
                    ]
                ]
            ])
        );
    }
}
