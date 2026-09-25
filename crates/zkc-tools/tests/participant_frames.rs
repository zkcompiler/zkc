//! Each participant's own frame closes with that participant's outcome
//! (docs/spec/domains/values.md): a participant that returned keeps the units
//! it returned even when another participant stops afterwards. This checks
//! the native rule directly; tests/execution/test_participant_lifecycle.py
//! also compares it with independent resumable Lean source execution.

use serde_json::json;
use std::collections::BTreeMap;
use zkc_runtime::interactive::{Action, Runner, StopKind, admit_physical};
use zkc_tools::protocol::{JointOutcome, LocalTransport, ParticipantChecker, Schedule, drive};

#[path = "common/backend.rs"]
mod fixture;
use fixture::backend_for as backend;

/// P creates a unit and returns it. V's only remaining work is a child
/// protocol that P takes no part in: a loop with no scheduled step whose
/// count exceeds the runner's iteration limit. The driver completes the
/// scheduled steps, then P, then asks V to finish, and V stops there.
fn source() -> serde_json::Value {
    json!([
        "zkc.protocol/1",
        [["create", "resource_unit.create", ["Slot.A"], ""]],
        [[
            "function",
            "Make",
            [],
            ["resource_unit:Slot.A"],
            [["op", "make", "create", [], [], ["x"]], ["return", ["x"]]],
            ["Make", []]
        ]],
        [
            [
                "protocol",
                "Spin",
                ["V"],
                [],
                [],
                [],
                [],
                [
                    [
                        "loop",
                        "spin",
                        ["constant", "100001"],
                        [],
                        [],
                        [["yield", []]],
                        []
                    ],
                    ["return", []]
                ]
            ],
            [
                "protocol",
                "Root",
                ["P", "V"],
                [],
                [],
                [["P", "resource_unit:Slot.A"]],
                [["child", "Spin", []]],
                [
                    ["local", "make", "P", "Make", [], ["x"]],
                    ["call", "spin", "child", [], []],
                    ["return", ["x"]]
                ]
            ]
        ],
        [
            ["instance", "spin", "Spin", [], [], [["V", "V"]]],
            [
                "instance",
                "root",
                "Root",
                [],
                [["child", "spin"]],
                [["P", "P"], ["V", "V"]]
            ]
        ],
        [["entry", "main", "root"]]
    ])
}

#[test]
fn a_returned_participant_keeps_its_units_when_another_stops_later() {
    let directory = zkc_test_support::evidence(module_path!());
    let path = directory.path().join("source.json");
    std::fs::write(&path, serde_json::to_vec(&source()).unwrap()).unwrap();
    let source = zkc_test_support::compile("protocol-source", &path);
    let candidate = zkc_test_support::compile("protocol-compile", &path);
    let checker =
        ParticipantChecker::new(zkc_test_support::checker("interactive-protocol")).unwrap();
    let admitted = admit_physical(&source, &candidate, &backend("P"), &checker).unwrap();

    let mut schedule = Schedule::new(&admitted, "main", "test").unwrap();
    let mut runners = BTreeMap::new();
    for role in ["P", "V"] {
        let runner = Runner::new(&admitted, "main", role, "test", backend(role), vec![])
            .unwrap_or_else(|e| panic!("{:?}", e.error));
        runners.insert(role.to_owned(), runner);
    }
    let report = drive(&mut schedule, &mut runners, &mut LocalTransport);
    assert!(
        matches!(&report.outcome, JointOutcome::Stopped(stop)
            if stop.role == "V" && stop.kind == StopKind::Limit),
        "the protocol stops when V reaches its iteration limit: {:?}",
        report.outcome
    );
    assert!(
        report.cancelled.is_empty(),
        "no participant was left running"
    );

    let p = runners.get_mut("P").unwrap();
    assert!(
        matches!(p.poll(), Action::Returned(values) if values.len() == 1),
        "P completed with its unit before V stopped"
    );
    assert_eq!(
        p.backend().live_resource_units(),
        1,
        "P keeps the unit it returned"
    );
    let v = runners.get_mut("V").unwrap();
    assert!(matches!(v.poll(), Action::Stopped(stop) if stop.kind == StopKind::Limit));
    assert_eq!(v.backend().live_resource_units(), 0);
}
