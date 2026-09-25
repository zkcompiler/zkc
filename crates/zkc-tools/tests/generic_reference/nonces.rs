//! Nonce state belongs to the reference; group equations are explicit services.
use super::*;
use zkc_backends::Domain;

fn compare(fixture: &Fixture, bases: usize, seed: u64, budget: u64, before: bool, after: bool) {
    let checker = ParticipantChecker::new(&fixture.checker_path).unwrap();
    let admitted =
        admit_physical(&fixture.source, &fixture.candidate, &backend(), &checker).unwrap();
    let mut inner = backend();
    let nonce = inner
        .issue_test_nonce(
            Domain::new("P", "test", "main", None),
            budget,
            Scalar::from(seed),
        )
        .unwrap();
    let Value::Nonce(token) = &nonce else {
        unreachable!()
    };
    let token = token.clone();
    let untouched = inner
        .issue_test_tape(
            Domain::new("P", "test", "main", None),
            3,
            vec![Scalar::from(7)],
        )
        .unwrap();
    let Value::Rng(untouched) = untouched else {
        unreachable!()
    };
    let base_values = Value::Groups(
        (0..bases)
            .map(|i| GroupPoint::generator().scale(Scalar::from((i + 1) as u64)))
            .collect::<Vec<_>>()
            .into(),
    );
    let values = vec![
        base_values,
        nonce,
        Value::Field(Scalar::from(3)),
        Value::Field(Scalar::from(7)),
        Value::Bool(before),
        Value::Bool(after),
    ];
    let ports: Vec<_> = ["bases", "nonce", "secret", "challenge", "before", "after"]
        .into_iter()
        .zip(&values)
        .map(|(n, v)| json!([n, value_json(v)]))
        .collect();
    let mut inputs = json!([
        "zkc.reference-inputs/1",
        "main",
        "test",
        [["P", ports]],
        [
            [
                "nonce",
                "P",
                [],
                budget.to_string(),
                ["nonce", seed.to_string()]
            ],
            ["untouched", "P", [], "3", ["rng", ["7"]]]
        ],
        [],
        []
    ]);
    let observer = Observed {
        inner,
        source_map: admitted.source_map().unwrap().clone(),
        events: Trace::new(&fixture.source),
        conversions: 0,
    };
    let mut runner = Runner::new(&admitted, "main", "P", "test", observer, values)
        .unwrap_or_else(|e| panic!("{}", e.error));
    let terminal = loop {
        match runner.poll() {
            Action::Local(local) => runner.execute_local(&local.cut).unwrap(),
            action @ (Action::Returned(_) | Action::Stopped(_)) => break action,
            action => panic!("unexpected {action:?}"),
        }
    };
    let native = runner.backend().events.snapshot();
    let mut group_request = None;
    let mut result = fixture.reference(&inputs);
    while result[3][0] == "pending-primitive" {
        assert!(
            inputs[5].as_array().unwrap().len() < 2,
            "unexpected extra service request"
        );
        let request = result[4].as_array().unwrap().last().unwrap()[1].clone();
        let outputs = match request[2].as_str().unwrap() {
            "validate" => {
                // Native entry validation has checked this exact original input.
                assert_eq!(request[5], json!([inputs[3][0][1][0][1]]));
                assert_eq!(request[3], json!(["bls12-381.g1"]));
                json!([])
            }
            "curve.scale_many" => {
                assert_eq!(request[3], json!(["bls12-381.g1"]));
                assert_eq!(request[4], json!([]));
                assert_eq!(
                    request[5],
                    json!([
                        inputs[3][0][1][0][1],
                        value_json(&Value::Field(Scalar::from(seed)))
                    ])
                );
                let response = native
                    .iter()
                    .find(|e| {
                        e[0] == "response"
                            && e[1][1] == request[1]
                            && e[1][2] == "curve.commit"
                            && e[1][5][0] == request[5][0]
                    })
                    .expect("same native commit request");
                group_request = Some(request.clone());
                json!([response[2][0]])
            }
            name => panic!("unexpected service {name}"),
        };
        inputs[5]
            .as_array_mut()
            .unwrap()
            .push(json!([request, ["ok", outputs]]));
        result = fixture.reference(&inputs);
    }
    let logical: Vec<_> = result[4]
        .as_array()
        .unwrap()
        .iter()
        .filter(|e| e[0] != "external")
        .cloned()
        .collect();
    assert_eq!(logical, native);
    match terminal {
        Action::Returned(values) => {
            assert_eq!(
                result[3],
                json!([
                    "returned",
                    values.iter().map(value_json).collect::<Vec<_>>()
                ])
            );
            let Value::Field(response) = &values[1] else {
                panic!("response type")
            };
            assert_eq!(*response, Scalar::from(seed + 21));
        }
        Action::Stopped(stop) => {
            let StopKind::Backend(error) = &stop.kind else {
                panic!("nonce backend stop")
            };
            let (reason, detail) = error.code.split_once(':').unwrap();
            assert_eq!(
                result[3][0],
                if reason == "rejected" {
                    "reject"
                } else {
                    reason
                }
            );
            assert_eq!(result[3][1], detail);
            assert_stop_location(&runner.backend().events, &stop, &result[3][2], true);
            let last = native.iter().rev().find(|e| e[0] == "request").unwrap();
            assert_eq!(result[3][2], last[1][1]);
            assert_eq!(runner.usage().live_value_bytes, 0);
        }
        _ => unreachable!(),
    }
    let observations: Vec<_> = [("nonce", &token), ("untouched", &untouched)]
        .into_iter()
        .map(|(name, token)| {
            let state = runner.backend().inner.observe(token).unwrap();
            json!([
                name,
                "P",
                [],
                state.generation.to_string(),
                state.draw_count.to_string(),
                state.budget.to_string(),
                state.stage
            ])
        })
        .collect();
    assert_eq!(result[5], json!(observations));
    assert_eq!(runner.backend().inner.active_frames(), 0);

    if let Some(request) = group_request {
        // Same source/handle/generation but different issued secret needs a new
        // exact mathematical answer; the old cache must not silently apply.
        let mut different = inputs.clone();
        different[4][0][4][1] = json!((seed + 1).to_string());
        let pending = fixture.reference(&different);
        assert_eq!(pending[3][0], "pending-primitive");
        assert_eq!(
            pending[4].as_array().unwrap().last().unwrap()[1][2],
            "curve.scale_many"
        );
        assert_eq!(pending[5][0][6], "committed");

        let wrong_groups = Value::Groups(vec![GroupPoint::generator(); bases + 1].into());
        let mut wrong = inputs.clone();
        let answer = wrong[5]
            .as_array_mut()
            .unwrap()
            .iter_mut()
            .find(|r| r[0] == request)
            .unwrap();
        answer[1] = json!(["ok", [value_json(&wrong_groups)]]);
        let failed = fixture.reference(&wrong);
        assert_eq!(failed[3][1], "group-count");
        assert_eq!(failed[5][0][3], "1");
        assert_eq!(failed[5][0][6], "committed");
    }
}

#[test]
fn nonce_stages_and_consuming_failures_match_native_execution() {
    let fixture = Fixture::from_fixture("generic-nonces.pir");
    for bases in 0..=2 {
        for seed in [0, 5, 13] {
            compare(&fixture, bases, seed, 2, true, true);
        }
    }
    compare(&fixture, 2, 5, 0, true, true);
    compare(&fixture, 2, 5, 1, true, true);
    compare(&fixture, 2, 5, 2, false, true);
    compare(&fixture, 2, 5, 2, true, false);

    let mut fixture = Fixture::from_fixture("generic-nonces.pir");
    let original: Json = serde_json::from_slice(&fixture.source).unwrap();
    let mut source = original.clone();
    let body = &mut source[3][3][0][7];
    *body = json!([
        [
            "local",
            "respond",
            "P",
            "Response",
            ["secret", "challenge", "nonce"],
            ["response"]
        ],
        ["return", ["bases", "response"]]
    ]);
    fixture.set_source(&source);
    compare(&fixture, 2, 5, 2, true, true);

    let mut source = original;
    source[3][3][0][7] = json!([
        [
            "local",
            "commit",
            "P",
            "Commitment",
            ["bases", "nonce"],
            ["first", "ready"]
        ],
        [
            "local",
            "commit_again",
            "P",
            "Commitment",
            ["first", "ready"],
            ["second", "again"]
        ],
        [
            "local",
            "respond",
            "P",
            "Response",
            ["secret", "challenge", "again"],
            ["response"]
        ],
        ["return", ["second", "response"]]
    ]);
    fixture.set_source(&source);
    compare(&fixture, 2, 5, 2, true, true);
}

#[test]
fn local_algorithm_nonce_composition_preserves_failures_origins_and_budgets() {
    let fixture = Fixture::from_fixture("local-authentication.pir");
    for bases in 0..=2 {
        for seed in [0, 5, 13] {
            compare(&fixture, bases, seed, 2, true, true);
        }
    }
    compare(&fixture, 2, 5, 0, true, true);
    compare(&fixture, 2, 5, 1, true, true);
    compare(&fixture, 2, 5, 2, false, true);
    compare(&fixture, 2, 5, 2, true, false);
}
