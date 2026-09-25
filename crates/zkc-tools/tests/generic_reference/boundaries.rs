//! Error domains, resource-safe control traversal and terminal observations.

use super::*;

#[test]
fn polynomial_contract_boundaries_match_both_layouts() {
    let table = |cells: &[u64]| {
        Value::table(
            &cells.iter().copied().map(Scalar::from).collect::<Vec<_>>(),
            &Policy::default(),
        )
        .unwrap()
    };
    for implementation in ["arkworks", "arkworks-msb"] {
        for (contract, bty, result_ty, cases) in [
            (
                "product_sum",
                "table",
                "field",
                vec![(table(&[9]), table(&[2])), (table(&[9]), table(&[2, 3]))],
            ),
            (
                "product_round",
                "table",
                "round",
                vec![
                    (table(&[9]), table(&[2])),
                    (table(&[9]), table(&[2, 3])),
                    (table(&[2, 3]), table(&[9])),
                    (table(&[0, 1]), table(&[2, 3])),
                ],
            ),
            (
                "fold",
                "field",
                "table",
                vec![
                    (table(&[9]), Value::Field(Scalar::from(2))),
                    (table(&[2, 3]), Value::Field(Scalar::from(2))),
                ],
            ),
            (
                "evaluate",
                "point",
                "field",
                vec![
                    (table(&[9]), Value::Point(vec![Scalar::from(2)].into())),
                    (table(&[2, 3]), Value::Point(vec![].into())),
                    (table(&[9]), Value::Point(vec![].into())),
                    (table(&[2, 3]), Value::Point(vec![Scalar::from(2)].into())),
                ],
            ),
        ] {
            let (b_generic, r_generic) = (written(bty, "F"), written(result_ty, "F"));
            let concrete = "\"bls12-381.fr\"";
            let (b_concrete, r_concrete) = (written(bty, concrete), written(result_ty, concrete));
            let source = format!(
                r#"module {{
                fn Check<F: domain Field>(a: Table<F>, b: {b_generic}) -> ({r_generic}) requires (CommRing(F)) {{
                    [work] let (result) = poly::{contract}::<F>(a, b);
                    return (result);
                }}
                configure Bound = Check(F = bls12-381.fr) using (work = "{implementation}/poly.{contract}");
                protocol CheckProtocol {{
                    roles (P);
                    inputs (P a: Table<{concrete}>, P b: {b_concrete});
                    outputs (P {r_concrete});
                    local [run] P: let (result) = Bound(a, b);
                    return (result);
                }}
                instance root: CheckProtocol {{ roles (P = P); }}
                entry main = root;
            }}"#
            );
            let fixture = Fixture::from_text(&source);
            for (a, b) in cases {
                compare_pure(&fixture, &[("a", a), ("b", b)], "test");
            }
        }
    }
}

#[test]
fn host_sessions_are_distinct_from_source_symbols() {
    let mut fixture = Fixture::new();
    fixture.set_source(&json!([
        "zkc.protocol/1",
        [],
        [],
        [["protocol", "Root", ["P"], [], [], [], [], [["return", []]]]],
        [["instance", "root", "Root", [], [], [["P", "P"]]]],
        [["entry", "main", "root"]]
    ]));
    for session in [
        "2026-09-15".to_owned(),
        ".session".into(),
        "-session".into(),
        "_".into(),
        "0".repeat(128),
    ] {
        compare_pure(&fixture, &[], &session);
    }
    let checker = ParticipantChecker::new(&fixture.checker_path).unwrap();
    let admitted =
        admit_physical(&fixture.source, &fixture.candidate, &backend(), &checker).unwrap();
    for session in [
        "".to_owned(),
        "bad/session".into(),
        "é".into(),
        "0".repeat(129),
    ] {
        let input = json!([
            "zkc.reference-inputs/1",
            "main",
            session,
            [["P", []]],
            [],
            [],
            []
        ]);
        assert_eq!(
            fixture.reference_as(&input, None),
            (false, json!(["refused", "invalid-session"]))
        );
        let result = Runner::new(&admitted, "main", "P", &session, backend(), vec![]);
        let Err(error) = result else {
            panic!("invalid session admitted")
        };
        assert_eq!(error.error, zkc_runtime::interactive::RuntimeError::Session);
    }
}

#[test]
fn unused_loop_iterations_do_not_affect_first_stop() {
    let mut fixture = Fixture::new();
    for depth in [1, 4, 8, 16] {
        let mut expected = None;
        for count in [1, 1_048_576] {
            let mut body = json!([["stop", "halt", "P", "abort"]]);
            for i in 0..depth {
                body = json!([
                    [
                        "loop",
                        format!("L{i}"),
                        ["constant", count.to_string()],
                        [],
                        [],
                        body,
                        []
                    ],
                    ["yield", []]
                ]);
            }
            *body.as_array_mut().unwrap().last_mut().unwrap() = json!(["return", []]);
            fixture.set_source(&json!([
                "zkc.protocol/1",
                [],
                [],
                [["protocol", "Root", ["P"], [], [], [], [], body]],
                [["instance", "root", "Root", [], [], [["P", "P"]]]],
                [["entry", "main", "root"]]
            ]));
            let observation = compare_pure(&fixture, &[], "test");
            assert_eq!(observation[3][0], "abort");
            if let Some(expected) = &expected {
                assert_eq!(&observation, expected);
            }
            expected = Some(observation);
        }
    }
}

#[test]
fn explicit_and_foreign_stops_preserve_message_prefix() {
    let mut fixture = Fixture::new();
    fixture.set_source(&json!([
        "zkc.protocol/1",
        [],
        [],
        [[
            "protocol",
            "Root",
            ["P", "V"],
            [],
            [["a", "P", "bool"]],
            [],
            [],
            [
                ["message", "offer", "flag", "P", "V", "a", "received"],
                ["stop", "halt", "P", "abort"]
            ]
        ]],
        [["instance", "root", "Root", [], [], [["P", "P"], ["V", "V"]]]],
        [["entry", "main", "root"]]
    ]));
    let checker = ParticipantChecker::new(&fixture.checker_path).unwrap();
    let admitted =
        admit_physical(&fixture.source, &fixture.candidate, &backend(), &checker).unwrap();
    let mut trace = Trace::new(&fixture.source);
    let mut runners = BTreeMap::new();
    for (role, inputs) in [("P", vec![Value::Bool(true)]), ("V", vec![])] {
        let observer = Observed {
            inner: backend_for(role),
            source_map: admitted.source_map().unwrap().clone(),
            events: trace.clone(),
            conversions: 0,
        };
        runners.insert(
            role.to_owned(),
            Runner::new(&admitted, "main", role, "test", observer, inputs)
                .unwrap_or_else(|e| panic!("{}", e.error)),
        );
    }
    let mut schedule = Schedule::new(&admitted, "main", "test").unwrap();
    let report = drive(&mut schedule, &mut runners, &mut trace);
    let JointOutcome::Stopped(stop) = report.outcome else {
        panic!("explicit stop")
    };
    let inputs = json!([
        "zkc.reference-inputs/1",
        "main",
        "test",
        [["P", [["a", ["bool", "true"]]]], ["V", []]],
        [],
        [],
        []
    ]);
    let joint = fixture.reference(&inputs);
    assert_eq!(stop.kind, StopKind::Explicit("abort".into()));
    assert_eq!(joint[3][0], "abort");
    assert_eq!(joint[3][1], "source-stop");
    assert_stop_location(&trace, &stop, &joint[3][2], false);
    assert_eq!(joint[4], json!(trace.snapshot()));
    assert!(
        runners
            .values()
            .all(|r| r.backend().inner.active_frames() == 0)
    );

    // Run V on its own. The source's foreign stop projects to a local incomplete
    // leaf, distinct from host cancellation during the joint execution above.
    let observer = Observed {
        inner: backend_for("V"),
        source_map: admitted.source_map().unwrap().clone(),
        events: Trace::new(&fixture.source),
        conversions: 0,
    };
    let mut v = Runner::new(&admitted, "main", "V", "test", observer, vec![])
        .unwrap_or_else(|e| panic!("{}", e.error));
    let Action::Receive(receive) = v.poll() else {
        panic!("receive")
    };
    let packet = Packet {
        envelope: receive.envelope,
        ty: receive.ty,
        payload: Value::Bool(true),
    };
    v.deliver(packet.clone()).unwrap();
    v.backend().events.message(&packet, true);
    let Action::Stopped(stop) = v.poll() else {
        panic!("foreign stop")
    };
    assert_eq!(stop.kind, StopKind::Incomplete);
    v.backend().events.check_origin(&stop.origin);
    assert!(stop.site.is_none());
    let message = joint[4][1].clone();
    let mut role = inputs.clone();
    role[3] = json!([["V", []]]);
    role[6] = json!([[
        ["receive", message[1], "flag", "P", "bool"],
        ["bool", "true"]
    ]]);
    let (ok, result) = fixture.reference_as(&role, Some("V"));
    assert!(ok);
    assert_eq!(result[3][0], "incomplete");
    assert_eq!(result[3][1], "foreign-stop-leaf");
    let location = &result[3][2];
    assert_eq!(location[1], stop.origin.session);
    assert_eq!(location[2], stop.origin.entry);
    assert_eq!(location[3], stop.origin.instance);
    assert_eq!(location[4], json!(source_path(&stop.origin)));
    assert_eq!(location[5], "");
    assert_eq!(location[6], stop.role);
    assert_eq!(result[4], json!(v.backend().events.snapshot()));
    assert_eq!(v.backend().inner.active_frames(), 0);
}
