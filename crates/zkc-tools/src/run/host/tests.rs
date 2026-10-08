use super::*;
use sha2::{Digest, Sha256};
use std::sync::Arc;
use zkc_runtime::interactive::{LogicalType, PhysicalType};

fn fixture(logical: &str) -> (Vec<u8>, Json) {
    let ty = PhysicalType::default_for(LogicalType::parse(logical).unwrap())
        .unwrap()
        .spelling();
    let carrier = json!([
        "zkc.program/1",
        [],
        "physical",
        [],
        [
            [
                "participant",
                "a",
                "root",
                "Alice",
                [],
                [["x", ty]],
                [ty],
                [["return", ["x"]]],
                []
            ],
            [
                "participant",
                "b",
                "root",
                "Bob",
                [],
                [["x", ty]],
                [ty],
                [["return", ["x"]]],
                []
            ]
        ],
        [["entry", "main", [["Alice", "a"], ["Bob", "b"]]]]
    ]);
    let raw = json!({"format":"zkc.run/1","candidate":carrier.to_string(),"entry":"main","roles":["Alice","Bob"],
        "steps":[{"role":0,"instruction":0,"anchor":null},{"role":1,"instruction":0,"anchor":null}]}).to_string().into_bytes();
    let spec = if logical == "bool" {
        json!(["wire", "5a4b4356010500"])
    } else {
        json!([logical.split(':').next().unwrap(), "2"])
    };
    (
        raw,
        json!([
            "zkc.bundle-inputs/1",
            "session",
            [
                ["Alice", [["0", ty, spec]], []],
                ["Bob", [["0", ty, spec]], []]
            ],
            []
        ]),
    )
}
fn host(raw: &[u8], limits: HostLimits) -> RunHost {
    RunHost::admit(
        raw,
        &Sha256::digest(raw).into(),
        limits,
        SetupAuthority::default(),
    )
    .unwrap()
}
#[test]
fn false_output_and_bounded_work_keep_complete_reports() {
    let (raw, input) = fixture("bool");
    let host = host(&raw, HostLimits::default());
    let report = host
        .prepare(input.to_string().as_bytes())
        .unwrap()
        .execute();
    assert_eq!(
        report.execution.as_ref().unwrap().outcome,
        Outcome::Completed
    );
    assert_eq!(report.json()["roles"][0]["outputs"][0][2], "5a4b4356010500");
    assert!(report.cleanup_errors.is_empty());
    let mut limits = HostLimits::default();
    limits.capacity.work.instructions = 0;
    let host = self::host(&raw, limits);
    let report = host
        .prepare(input.to_string().as_bytes())
        .unwrap()
        .execute();
    assert!(matches!(
        report.execution.as_ref().unwrap().outcome,
        Outcome::ParticipantStopped { role: 0 }
    ));
    assert_eq!(report.json()["limits"]["capacity"][5][0], "0");
    assert!(
        report.json()["roles"]
            .as_array()
            .unwrap()
            .iter()
            .all(|r| r["active_frames"] == 0)
    );
}
#[test]
fn partial_issuance_retires_earlier_roots_without_entering_frames() {
    let (raw, input) = fixture("rng:bls12-381.fr");
    let host = host(&raw, HostLimits::default());
    let mut attempts = 0;
    let report = host
        .prepare(input.to_string().as_bytes())
        .unwrap()
        .execute_with(|| {
            attempts += 1;
            if attempts == 2 {
                Err("injected-entropy-failure".into())
            } else {
                Ok(())
            }
        });
    assert_eq!(attempts, 2);
    assert_eq!(report.phase, "issuance");
    assert_eq!(report.json()["status"], "setup-failed");
    assert_eq!(report.failure.as_deref(), Some("injected-entropy-failure"));
    assert!(report.execution.is_none());
    assert_eq!(report.resources.len(), 1);
    assert_eq!(report.resources[0]["state"]["transitions"], 0);
    assert!(report.cleanup_errors.is_empty());
    assert!(
        report
            .unstarted
            .iter()
            .all(|(_, b)| b.active_frames() == 0 && b.live_resource_units() == 0)
    );
    // A prepared call is consumed; a fresh call gets independent resources.
    let recovered = host
        .prepare(input.to_string().as_bytes())
        .unwrap()
        .execute();
    assert_eq!(
        recovered.execution.as_ref().unwrap().outcome,
        Outcome::Completed
    );
    assert_eq!(recovered.resources.len(), 2);
    assert!(recovered.cleanup_errors.is_empty());
}
#[test]
fn later_input_failure_and_shared_capacity_refuse_before_issuance() {
    let (raw, mut input) = fixture("nonce:bls12-381.fr");
    let host = host(&raw, HostLimits::default());
    input[2][1][1][0][0] = json!("1");
    assert!(
        matches!(host.prepare(input.to_string().as_bytes()),Err(code) if code=="bundle-input-port")
    );
    input[2][1][1][0][0] = json!("0");
    let mut limits = HostLimits::default();
    limits.capacity.values.live_bytes = Value::capability_retained_bytes();
    let host = self::host(&raw, limits);
    assert!(
        host.prepare(input.to_string().as_bytes()).is_err(),
        "capacity is shared across roles"
    );
}
#[test]
fn transcript_roots_and_extra_authority_are_refused() {
    let (raw, input) = fixture("transcript:merlin3.bls12-381.fr64be/1");
    let host = host(&raw, HostLimits::default());
    assert!(
        matches!(host.prepare(input.to_string().as_bytes()),Err(code) if code=="bundle-transcript-input-unsupported")
    );
    let mut authority = SetupAuthority::default();
    authority.keys.insert("bad name".into(), [0; 32]);
    assert!(
        RunHost::admit(
            &raw,
            &Sha256::digest(&raw).into(),
            HostLimits::default(),
            authority
        )
        .is_err()
    );
    assert!(
        SetupAuthority::parse(br#"["zkc.bundle-setups/1",[],[["Alice","0","missing"]]]"#).is_ok()
    );
    let authority = SetupAuthority {
        inputs: BTreeMap::from([(("Alice".into(), 0), "missing".into())]),
        ..Default::default()
    };
    assert!(
        RunHost::admit(
            &raw,
            &Sha256::digest(&raw).into(),
            HostLimits::default(),
            authority
        )
        .is_err()
    );
}

#[test]
fn key_files_are_authenticated_and_captured_before_execution() {
    let policy = zkc_backends::Policy::default();
    let keys = zkc_arkworks::Keys::setup_for_development(1, &policy.ark_bounds()).unwrap();
    let directory = zkc_test_support::evidence(module_path!());
    let path = directory.path().join("prover.key");
    std::fs::write(
        &path,
        keys.prover_key().to_bytes(&policy.ark_bounds()).unwrap(),
    )
    .unwrap();
    for logical in [
        "prover_key:multilinear.kzg.bls12-381/1",
        "verifier_key:multilinear.kzg.bls12-381/1",
    ] {
        let (raw, mut input) = fixture(logical);
        input[3] = json!([[
            "setup",
            hex(&keys.verifier_key().to_bytes(&policy.ark_bounds()).unwrap())
        ]]);
        let authority = SetupAuthority {
            keys: BTreeMap::from([("setup".into(), keys.verifier_key().metadata().key_id())]),
            inputs: BTreeMap::from([
                (("Alice".into(), 0), "setup".into()),
                (("Bob".into(), 0), "setup".into()),
            ]),
        };
        let host = RunHost::admit(
            &raw,
            &Sha256::digest(&raw).into(),
            HostLimits::default(),
            authority,
        )
        .unwrap();
        let spec = if logical.starts_with("prover") {
            json!([
                "prover_key_file",
                [path, hex(&keys.prover_key().material_fingerprint())]
            ])
        } else {
            json!(["verifier_key", "setup"])
        };
        input[2][0][1][0][2] = spec.clone();
        input[2][1][1][0][2] = spec;
        let prepared = host.prepare(input.to_string().as_bytes()).unwrap();
        if logical.starts_with("prover") {
            std::fs::write(&path, b"changed after capture").unwrap();
            assert!(host.prepare(input.to_string().as_bytes()).is_err());
        }
        let report = prepared.execute();
        assert_eq!(
            report.execution.as_ref().unwrap().outcome,
            Outcome::Completed
        );
        assert!(report.cleanup_errors.is_empty());
        input[3][0][1] = json!("00");
        assert!(host.prepare(input.to_string().as_bytes()).is_err());
    }
}

#[test]
fn all_native_wire_charges_precede_payload_decoding() {
    let (raw, input) = fixture("bool");
    let mut limits = HostLimits::default();
    limits.capacity.values.live_bytes = 512;
    let host = host(&raw, limits);
    crate::host::admission::DECODE_COUNT.set(0);
    assert!(
        matches!(host.prepare(input.to_string().as_bytes()),Err(code) if code=="artifact-input-bytes-limit")
    );
    assert_eq!(crate::host::admission::DECODE_COUNT.get(), 0);
}
#[test]
fn partial_managed_service_issuance_retires_unleased_roots() {
    let (raw, _) = fixture("bool");
    let mut outer: Json = serde_json::from_slice(&raw).unwrap();
    let mut candidate: Json = serde_json::from_str(outer["candidate"].as_str().unwrap()).unwrap();
    for role in candidate[4].as_array_mut().unwrap() {
        role[8] = json!([["coins", "random.bls12-381.fr/1", "0"]]);
    }
    outer["candidate"] = json!(candidate.to_string());
    let raw = outer.to_string();
    let host = host(raw.as_bytes(), HostLimits::default());
    let (_, mut input) = fixture("bool");
    for role in input[2].as_array_mut().unwrap() {
        role[2] = json!([["0", "random.bls12-381.fr/1", "2"]]);
    }
    let mut issued = 0;
    let report = host
        .prepare(input.to_string().as_bytes())
        .unwrap()
        .execute_with(|| {
            issued += 1;
            if issued == 2 {
                Err("injected-service-failure".into())
            } else {
                Ok(())
            }
        });
    assert_eq!(report.failure.as_deref(), Some("injected-service-failure"));
    assert_eq!(report.resources.len(), 1);
    assert_eq!(report.resources[0]["kind"], "service");
    assert_eq!(report.resources[0]["leased"], false);
    assert!(report.cleanup_errors.is_empty());
}

#[test]
fn returned_unit_is_result_custody_not_a_cleanup_failure() {
    let ty = "resource_unit:Slot.A@logical.resource_unit/1";
    let candidate = json!([
        "zkc.program/1",
        [[
            "create",
            "resource_unit.create",
            ["Slot.A"],
            "logical/resource_unit.create"
        ]],
        "physical",
        [[
            "function",
            "make",
            [],
            [ty],
            [["op", "create", "create", [], [], ["u"]], ["return", ["u"]]],
            ["make", []]
        ]],
        [[
            "participant",
            "a",
            "root",
            "Alice",
            [],
            [],
            [ty],
            [["local", "make", "make", [], ["u"]], ["return", ["u"]]],
            []
        ]],
        [["entry", "main", [["Alice", "a"]]]]
    ]);
    for stop_peer in [false, true] {
        let mut candidate = candidate.clone();
        let mut roles = vec!["Alice"];
        let mut steps = vec![
            json!({"role":0,"instruction":0,"anchor":null}),
            json!({"role":0,"instruction":1,"anchor":null}),
        ];
        let mut inputs = vec![json!(["Alice", [], []])];
        if stop_peer {
            candidate[3].as_array_mut().unwrap().push(json!([
                "function",
                "reject",
                [],
                [],
                [["stop", "stop", "reject"]],
                ["reject", []]
            ]));
            candidate[4].as_array_mut().unwrap().push(json!([
                "participant",
                "b",
                "root",
                "Bob",
                [],
                [],
                [],
                [["local", "reject", "reject", [], []], ["return", []]],
                []
            ]));
            candidate[5][0][2]
                .as_array_mut()
                .unwrap()
                .push(json!(["Bob", "b"]));
            roles.push("Bob");
            steps.push(json!({"role":1,"instruction":0,"anchor":null}));
            steps.push(json!({"role":1,"instruction":1,"anchor":null}));
            inputs.push(json!(["Bob", [], []]));
        }
        let raw=json!({"format":"zkc.run/1","candidate":candidate.to_string(),"entry":"main","roles":roles,"steps":steps}).to_string();
        let host = host(raw.as_bytes(), HostLimits::default());
        let input = json!(["zkc.bundle-inputs/1", "session", inputs, []]);
        let mut report = host
            .prepare(input.to_string().as_bytes())
            .unwrap()
            .execute();
        assert_eq!(report.json()["status"], "executed");
        assert_eq!(report.json()["roles"][0]["retained_output_units"], 1);
        assert_eq!(report.json()["roles"][0]["live_resource_units"], 1);
        assert!(report.cleanup_errors.is_empty());
        let execution = report.execution.as_mut().unwrap();
        assert_eq!(
            execution.outcome,
            if stop_peer {
                Outcome::ParticipantStopped { role: 1 }
            } else {
                Outcome::Completed
            }
        );
        if stop_peer {
            assert_eq!(execution.backends[1].1.live_resource_units(), 0);
        }
        let Value::ResourceUnit(unit) = &execution.roles[0].outputs[0] else {
            panic!("returned unit")
        };
        // The finalization check rejects aliases and stale/retired result roots,
        // even if a raw count alone could match a different live resource.
        let duplicate = vec![execution.roles[0].outputs[0].clone(); 2];
        assert_eq!(
            super::report::check_units(
                &execution.backends[0].1,
                &duplicate,
                &mut Default::default()
            )
            .unwrap_err(),
            "bundle-returned-unit-alias"
        );
        execution.backends[0].1.retire(unit.capability()).unwrap();
        assert_eq!(execution.backends[0].1.live_resource_units(), 0);
        assert_eq!(
            super::report::check_units(
                &execution.backends[0].1,
                &execution.roles[0].outputs,
                &mut Default::default()
            )
            .unwrap_err(),
            "refused:capability-unissued"
        );
        let expected = execution.outcome.clone();
        let names: Vec<_> = execution
            .backends
            .iter()
            .map(|(name, _)| name.clone())
            .collect();
        let caps = names
            .iter()
            .map(|name| (name.clone(), Vec::new()))
            .collect();
        let services = names
            .iter()
            .map(|name| (name.clone(), Vec::new()))
            .collect();
        report.finalize(&ServiceRegistry::new(Default::default()), &caps, &services);
        assert_eq!(report.json()["status"], "diagnostic-failed");
        assert!(
            report
                .cleanup_errors
                .iter()
                .any(|d| d["kind"] == "returned-unit")
        );
        assert_eq!(report.execution.as_ref().unwrap().outcome, expected);
    }
}

#[test]
fn external_work_is_bounded_and_reported_by_the_installed_host() {
    let indices = PhysicalType::default_for(LogicalType::parse("indices").unwrap())
        .unwrap()
        .spelling();
    let index = PhysicalType::default_for(LogicalType::parse("index").unwrap())
        .unwrap()
        .spelling();
    let candidate = json!([
        "zkc.program/1",
        [
            [
                "init",
                "external.openvm.init",
                [],
                "native/external.openvm.init"
            ],
            [
                "sample",
                "external.openvm.sample",
                [],
                "native/external.openvm.sample"
            ]
        ],
        "physical",
        [[
            "function",
            "draw",
            [],
            [indices, index],
            [
                ["op", "init", "init", [], [], ["state"]],
                ["op", "sample", "sample", [], ["state"], ["next", "value"]],
                ["return", ["next", "value"]]
            ],
            ["draw", []]
        ]],
        [[
            "participant",
            "a",
            "root",
            "Alice",
            [],
            [],
            [indices, index],
            [
                ["local", "draw", "draw", [], ["next", "value"]],
                ["return", ["next", "value"]]
            ],
            []
        ]],
        [["entry", "main", [["Alice", "a"]]]]
    ]);
    let raw = json!({"format":"zkc.run/1", "candidate":candidate.to_string(), "entry":"main", "roles":["Alice"],
        "steps":[{"role":0,"instruction":0,"anchor":null},{"role":0,"instruction":1,"anchor":null}]}).to_string();
    let input = json!(["zkc.bundle-inputs/1", "session", [["Alice", [], []]], []]).to_string();
    for ceiling in [0, NativeBackend::DEFAULT_EXTERNAL_WORK_LIMIT] {
        let host = host(
            raw.as_bytes(),
            HostLimits {
                external_work: ceiling,
                ..HostLimits::default()
            },
        );
        let report = host.prepare(input.as_bytes()).unwrap().execute();
        let record = report.json();
        assert_eq!(
            record["limits"]["execution"]["external_work_per_role"],
            ceiling
        );
        assert!(report.cleanup_errors.is_empty());
        if ceiling == 0 {
            assert!(matches!(
                report.execution.as_ref().unwrap().outcome,
                Outcome::ParticipantStopped { .. }
            ));
            assert!(record.to_string().contains("external-work-limit"));
            assert_eq!(record["roles"][0]["external_work"], 0);
        } else {
            assert_eq!(
                report.execution.as_ref().unwrap().outcome,
                Outcome::Completed
            );
            assert!(record["roles"][0]["external_work"].as_u64().unwrap() > 0);
        }
    }
}

#[test]
fn capability_reports_use_input_positions_with_interleaved_data() {
    let (raw, mut input) = fixture("rng:bls12-381.fr");
    let mut bundle: Json = serde_json::from_slice(&raw).unwrap();
    let mut candidate: Json = serde_json::from_str(bundle["candidate"].as_str().unwrap()).unwrap();
    for role in candidate[4].as_array_mut().unwrap() {
        role[5]
            .as_array_mut()
            .unwrap()
            .insert(0, json!(["unused", "bool@native.bool/1"]));
    }
    for role in input[2].as_array_mut().unwrap() {
        role[1][0][0] = json!("1");
        role[1].as_array_mut().unwrap().insert(
            0,
            json!(["0", "bool@native.bool/1", ["wire", "5a4b4356010500"]]),
        );
    }
    bundle["candidate"] = json!(candidate.to_string());
    let host = host(bundle.to_string().as_bytes(), HostLimits::default());
    let report = host
        .prepare(input.to_string().as_bytes())
        .unwrap()
        .execute();
    assert_eq!(report.json()["outcome"], json!(["completed"]));
    assert_eq!(report.resources.len(), 2);
    for resource in &report.resources {
        assert_eq!(resource["kind"], "capability");
        assert_eq!(resource["index"], 1);
        assert_eq!(resource["state"]["transitions"], 0);
    }
}

#[test]
fn native_construction_failure_keeps_load_usage_and_retires_all_roles() {
    let (raw, input) = fixture("rng:bls12-381.fr");
    let host = host(&raw, HostLimits::default());
    let mut plan = host.prepare(input.to_string().as_bytes()).unwrap();
    // A private test mutates the prepared backend's domain. No test policy or
    // failure hook is exposed by the public installed host.
    plan.roles[1].backend = NativeBackend::new(
        zkc_backends::Policy::default(),
        EntryPolicy::new(
            Domain::new("Bob", "wrong-session", "main", Some("root")),
            None,
        ),
        Default::default(),
    )
    .unwrap();
    let report = plan.execute();
    assert_eq!(report.phase, "construction");
    assert_eq!(report.json()["status"], "setup-failed");
    assert!(
        matches!(&report.execution.as_ref().unwrap().outcome, Outcome::DriverFailed(f) if f.kind == FailureKind::Setup)
    );
    assert!(report.execution.as_ref().unwrap().roles[1].usage.is_some());
    assert_eq!(report.resources.len(), 2);
    assert!(
        report
            .resources
            .iter()
            .all(|r| r["state"]["transitions"] == 0)
    );
    assert!(report.cleanup_errors.is_empty());
}

mod typed;
