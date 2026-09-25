//! Joined native/Lean/Rust local-control regression. Binaries are supplied by
//! the coordinating build; this test never builds or modifies other lanes.
use serde_json::{Value as Json, json};
use std::{fs, process::Command};
use zkc_backends::{Domain, EntryPolicy, NativeBackend, Policy, PublicInputs, Value};
use zkc_runtime::interactive::{Action, Runner, admit_physical, admit_supplied};
use zkc_tools::protocol::ParticipantChecker;

#[path = "common/backend.rs"]
mod fixture;

fn backend() -> NativeBackend {
    fixture::backend_at("Alice", "s", "Main")
}
#[path = "common/observed.rs"]
mod observed;
use observed::PhysicalObserved;

fn count_tag(value: &Json, tag: &str) -> usize {
    match value {
        Json::Array(a) => {
            usize::from(a.first().and_then(Json::as_str) == Some(tag))
                + a.iter().map(|v| count_tag(v, tag)).sum::<usize>()
        }
        _ => 0,
    }
}
fn swap_first_branches(value: &mut Json) -> bool {
    if let Json::Array(a) = value {
        if a.first().and_then(Json::as_str) == Some("if") {
            a.swap(4, 5);
            return true;
        }
        return a.iter_mut().any(swap_first_branches);
    }
    false
}
#[test]
fn ordinary_and_generic_helpers_preserve_regions_and_candidate_semantics() {
    let lean = zkc_test_support::checker("interactive-protocol");
    let checker = ParticipantChecker::new(&lean).unwrap();
    for source in [
        include_bytes!("fixtures/local-control/source.json").as_slice(),
        include_bytes!("fixtures/local-control/generic.json").as_slice(),
    ] {
        let dir = zkc_test_support::evidence(module_path!());
        let path = dir.path().join("source.json");
        fs::write(&path, source).unwrap();
        let output = zkc_test_support::compile("protocol-compile", &path);
        let physical: Json = serde_json::from_slice(&output).unwrap();
        assert!(count_tag(&physical, "if") > 0);
        assert!(count_tag(&physical, "for") > 0);
        assert_eq!(count_tag(&physical, "apply"), 0);
        let admitted = admit_physical(source, &output, &backend(), &checker).unwrap();
        for (condition, lower, upper, initial, expected, trips) in [
            (true, 0, 4, 0, 6, 4),
            (false, 0, 4, 7, 7, 0),
            (true, 2, 2, 7, 7, 0),
            (true, 4, 2, 7, 7, 0),
        ] {
            let roles = admitted.entry("Main").unwrap();
            let role = roles.iter().find(|r| r.role == "Alice").unwrap();
            let map = admitted.source_map().unwrap();
            let inputs = role
                .inputs
                .iter()
                .map(|(name, _)| {
                    if map.port("main", "Alice", "c") == Some(name) {
                        Value::Bool(condition)
                    } else if map.port("main", "Alice", "lo") == Some(name) {
                        Value::Index(lower)
                    } else if map.port("main", "Alice", "hi") == Some(name) {
                        Value::Index(upper)
                    } else {
                        assert_eq!(map.port("main", "Alice", "x"), Some(name.as_str()));
                        Value::Index(initial)
                    }
                })
                .collect();
            let mut runner = Runner::new(
                &admitted,
                "Main",
                "Alice",
                "s",
                PhysicalObserved {
                    inner: backend(),
                    steps: vec![],
                    requests: vec![],
                },
                inputs,
            )
            .unwrap_or_else(|e| panic!("{}", e.error));
            loop {
                match runner.poll() {
                    Action::Local(local) => runner.execute_local(&local.cut).unwrap(),
                    Action::Returned(v) => {
                        assert!(matches!(v.as_slice(),[Value::Index(n)] if *n==expected));
                        break;
                    }
                    other => panic!("unexpected {other:?}"),
                }
            }
            assert_eq!(runner.usage().iterations, trips);
            let inputs = json!([
                "zkc.reference-inputs/1",
                "Main",
                "s",
                [[
                    "Alice",
                    [
                        ["c", ["bool", condition.to_string()]],
                        ["lo", ["index", lower.to_string()]],
                        ["hi", ["index", upper.to_string()]],
                        ["x", ["index", initial.to_string()]]
                    ]
                ]],
                [],
                [],
                []
            ]);
            let candidate_path = dir.path().join("physical.json");
            let input_path = dir.path().join("inputs.json");
            let storage_path = dir.path().join("storage.json");
            fs::write(&candidate_path, &output).unwrap();
            fs::write(&input_path, serde_json::to_vec(&inputs).unwrap()).unwrap();
            fs::write(
                &storage_path,
                serde_json::to_vec(&json!([
                    "zkc.local-resources/1",
                    (64 * 1024 * 1024).to_string(),
                    []
                ]))
                .unwrap(),
            )
            .unwrap();
            let reference = Command::new(&lean)
                .arg("--physical-local-reference")
                .args([&path, &candidate_path, &input_path, &storage_path])
                .output()
                .unwrap();
            assert!(
                reference.status.success(),
                "{}{}",
                String::from_utf8_lossy(&reference.stdout),
                String::from_utf8_lossy(&reference.stderr)
            );
            let reference: Json = serde_json::from_slice(&reference.stdout).unwrap();
            assert_eq!(
                reference[1],
                json!(["returned", [["index", expected.to_string()]]])
            );
            let usage = runner.usage();
            assert_eq!(
                reference[4],
                json!([
                    usage.instructions.to_string(),
                    usage.live_values.to_string(),
                    usage.live_value_bytes.to_string(),
                    usage.total_value_bytes.to_string(),
                    "0"
                ])
            );
            assert_eq!(reference[5], json!(runner.backend().steps));
            let requests = reference[2]
                .as_array()
                .unwrap()
                .iter()
                .filter(|e| e[0] == "request")
                .map(|e| {
                    let path = e[1][1][4].as_array().unwrap();
                    json!([e[1][1][5], &path[1..], e[1][2]])
                })
                .collect::<Vec<_>>();
            assert_eq!(requests, runner.backend().requests);
            assert_eq!(runner.into_backend().inner.active_frames(), 0);
        }
        let mut mutated = physical;
        assert!(swap_first_branches(&mut mutated));
        let mutated = serde_json::to_vec(&mutated).unwrap();
        admit_supplied(&mutated, &backend()).unwrap();
        assert!(admit_physical(source, &mutated, &backend(), &checker).is_err());
    }
}

#[cfg(feature = "test-utils")]
#[test]
fn nested_affine_regions_match_independent_physical_accounting_and_failure_prefixes() {
    use zkc_backends::Scalar;
    use zkc_runtime::interactive::StopKind;
    let compiler = zkc_test_support::compiler();
    let lean = zkc_test_support::checker("interactive-protocol");
    let checker = ParticipantChecker::new(&lean).unwrap();
    let dir = zkc_test_support::evidence(module_path!());
    let source = include_bytes!("fixtures/local-control/resources.json");
    let source_path = dir.path().join("source.json");
    let candidate_path = dir.path().join("physical.json");
    let input_path = dir.path().join("inputs.json");
    let storage_path = dir.path().join("storage.json");
    fs::write(&source_path, source).unwrap();
    let candidate = Command::new(&compiler)
        .arg("protocol-compile")
        .arg(&source_path)
        .output()
        .unwrap();
    assert!(
        candidate.status.success(),
        "{}",
        String::from_utf8_lossy(&candidate.stderr)
    );
    fs::write(&candidate_path, &candidate.stdout).unwrap();
    let cases = [
        (true, false, 0, 3, 8, 64 * 1024 * 1024), // untaken rejecting guard; three advancing draws
        (false, true, 0, 3, 0, 64 * 1024 * 1024), // no draw despite zero resource budget
        (false, false, 0, 3, 8, 64 * 1024 * 1024), // selected failing guard
        (true, false, 0, 0, 0, 64 * 1024 * 1024),
        (true, false, 3, 0, 0, 64 * 1024 * 1024),
        (true, false, 0, 3, 1, 64 * 1024 * 1024), // one successful draw then resource exhaustion
        (true, false, 0, 3, 8, 512),              // output ceiling AFTER consuming one draw
        (true, false, 0, 1_048_577, 8, 64 * 1024 * 1024), // deterministic bound rejection
    ];
    for (condition, ok, lo, hi, budget, ceiling) in cases {
        let domain = Domain::new("P", "test", "main", None);
        let mut native = NativeBackend::new(
            Policy {
                max_value_bytes: ceiling,
                ..Policy::default()
            },
            EntryPolicy::new(domain.clone(), None, PublicInputs::LocalOnly),
            None,
        )
        .unwrap();
        let rng = native
            .issue_test_tape(
                domain,
                budget,
                vec![Scalar::from(2), Scalar::from(3), Scalar::from(5)],
            )
            .unwrap();
        let Value::Rng(token) = &rng else { panic!() };
        let token = token.clone();
        let values = vec![
            rng,
            Value::Bool(condition),
            Value::Bool(ok),
            Value::Index(lo),
            Value::Index(hi),
        ];
        let admitted = admit_physical(source, &candidate.stdout, &native, &checker).unwrap();
        let observed = PhysicalObserved {
            inner: native,
            steps: vec![],
            requests: vec![],
        };
        let mut runner = Runner::new(&admitted, "main", "P", "test", observed, values)
            .unwrap_or_else(|e| panic!("{}", e.error));
        let terminal = loop {
            match runner.poll() {
                Action::Local(a) => runner.execute_local(&a.cut).unwrap(),
                v => break v,
            }
        };
        let inputs = json!([
            "zkc.reference-inputs/1",
            "main",
            "test",
            [[
                "P",
                [
                    ["r", ["rng:bls12-381.fr", ["draws", "0"]]],
                    ["cond", ["bool", condition.to_string()]],
                    ["ok", ["bool", ok.to_string()]],
                    ["lo", ["index", lo.to_string()]],
                    ["hi", ["index", hi.to_string()]]
                ]
            ]],
            [[
                "draws",
                "P",
                [],
                budget.to_string(),
                ["rng", ["2", "3", "5"]]
            ]],
            [],
            []
        ]);
        fs::write(&input_path, serde_json::to_vec(&inputs).unwrap()).unwrap();
        fs::write(
            &storage_path,
            serde_json::to_vec(&json!(["zkc.local-resources/1", ceiling.to_string(), []])).unwrap(),
        )
        .unwrap();
        let output = Command::new(&lean)
            .arg("--physical-local-reference")
            .args([&source_path, &candidate_path, &input_path, &storage_path])
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{}{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        let reference: Json = serde_json::from_slice(&output.stdout).unwrap();
        match terminal {
            Action::Returned(v) => {
                let [Value::Rng(t)] = v.as_slice() else {
                    panic!()
                };
                assert_eq!(
                    reference[1],
                    json!([
                        "returned",
                        [["rng:bls12-381.fr", ["draws", t.generation().to_string()]]]
                    ])
                );
            }
            Action::Stopped(stop) => match stop.kind {
                StopKind::Backend(e) => {
                    let reason = if reference[1][0] == "reject" {
                        "rejected"
                    } else {
                        reference[1][0].as_str().unwrap()
                    };
                    assert_eq!(
                        e.code,
                        format!("{reason}:{}", reference[1][1].as_str().unwrap())
                    );
                    assert_eq!(stop.site.as_deref(), reference[1][2][5].as_str());
                }
                StopKind::Limit => assert_eq!(reference[1][0], "limit"),
                kind => panic!("unexpected {kind:?}"),
            },
            other => panic!("unexpected {other:?}"),
        }
        let usage = runner.usage();
        assert_eq!(
            reference[4],
            json!([
                usage.instructions.to_string(),
                usage.live_values.to_string(),
                usage.live_value_bytes.to_string(),
                usage.total_value_bytes.to_string(),
                "0"
            ]),
            "case {condition} {ok} {lo} {hi} {budget} {ceiling}"
        );
        assert_eq!(reference[5], json!(runner.backend().steps));
        let state = runner.backend().inner.observe(&token).unwrap();
        assert_eq!(reference[3][0][3], state.generation.to_string());
        assert_eq!(reference[3][0][4], state.draw_count.to_string());
        assert_eq!(reference[3][0][5], state.budget.to_string());
        let requests = reference[2]
            .as_array()
            .unwrap()
            .iter()
            .filter(|e| e[0] == "request")
            .map(|e| {
                let path = e[1][1][4].as_array().unwrap();
                json!([e[1][1][5], &path[1..], e[1][2]])
            })
            .collect::<Vec<_>>();
        assert_eq!(requests, runner.backend().requests);
        assert_eq!(runner.into_backend().inner.active_frames(), 0);
    }
}
