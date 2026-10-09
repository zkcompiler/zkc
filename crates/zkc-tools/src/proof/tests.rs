use super::*;
mod admission;
#[test]
fn nested_wire_permission_is_exact() {
    for spelling in [
        "matrix:bls12-381.fr",
        "matrix:bn254.fr",
        "sequence<matrix:bn254.fr>",
        "sequence<index>",
        "sequence<matrix:bls12-381.fr>",
    ] {
        let logical = wire_type(spelling, false).unwrap();
        let physical = PhysicalType::default_for(logical.clone()).unwrap();
        assert_eq!(wire_codec(&logical).as_deref(), Some("zkc.native-data/1"));
        assert_eq!(input_kind(&physical).unwrap(), "wire");
    }
    for spelling in [
        "polynomial:bn254.fr",
        "sequence<polynomial:bn254.fr>",
        "sequence<prover_key:multilinear.kzg.bls12-381/1>",
    ] {
        assert!(wire_type(spelling, false).is_err());
    }
}
#[test]
fn proof_host_admits_internal_units_but_refuses_unexportable_custody() {
    for handling in ["consume", "discard", "return"] {
        let returned = handling == "return";
        let binding = zkc_runtime::interactive::OperationBinding {
            contract: "resource_unit.create".into(),
            arguments: vec!["Slot.A".into()],
            implementation: "logical/resource_unit.create".into(),
        };
        let unit = binding.signature().unwrap().outputs[0].clone();
        let mut outputs = if returned {
            vec![unit.spelling()]
        } else {
            vec![]
        };
        outputs.push("bool@native.bool/1".into());
        let mut values = if returned { vec!["u"] } else { vec![] };
        values.push("done");
        let mut body = vec![json!(["op", "create", "create", [], [], ["u"]])];
        if handling == "consume" {
            body.push(json!(["op", "consume", "consume", [], ["u"], []]));
        }
        body.push(json!(["bool_constant", "done", "done", true]));
        body.push(json!(["return", values]));
        let candidate = json!([
            "zkc.program/1",
            [
                [
                    "create",
                    "resource_unit.create",
                    ["Slot.A"],
                    "logical/resource_unit.create"
                ],
                [
                    "consume",
                    "resource_unit.consume",
                    ["Slot.A"],
                    "logical/resource_unit.consume"
                ]
            ],
            "physical",
            [
                ["function", "unit", [], outputs, body, ["unit", []]],
                [
                    "function",
                    "accept",
                    [],
                    ["bool@native.bool/1"],
                    [
                        ["bool_constant", "accept", "yes", true],
                        ["return", ["yes"]]
                    ],
                    ["accept", []]
                ]
            ],
            [
                [
                    "participant",
                    "prover",
                    "main",
                    "P",
                    [],
                    [],
                    outputs,
                    [["local", "unit", "unit", [], values], ["return", values]],
                    []
                ],
                [
                    "participant",
                    "verifier",
                    "main",
                    "V",
                    [],
                    [],
                    ["bool@native.bool/1"],
                    [
                        ["local", "accept", "accept", [], ["yes"]],
                        ["return", ["yes"]]
                    ],
                    []
                ]
            ],
            [["entry", "main", [["P", "prover"], ["V", "verifier"]]]]
        ])
        .to_string();
        let descriptor = json!([
            "zkc.native-proof-descriptor/4",
            [
                "zkc.native-proof-policy/4",
                "main",
                "P",
                "V",
                "0",
                "",
                "",
                [],
                []
            ],
            "zkc.native-origin/2",
            [],
            [],
            []
        ]);
        let output_map = if returned {
            json!([["0", unit.logical().spelling()], ["1", "bool"]])
        } else {
            json!([["1", "bool"]])
        };
        let deployment = json!([
            "zkc.native-proof/4",
            "0".repeat(64),
            descriptor,
            hash(&logical::encode_tree(&descriptor).unwrap()),
            candidate,
            hash(candidate.as_bytes()),
            [
                ["P", "prover", [], output_map, [], ""],
                ["V", "verifier", [], [["0", "bool"]], [], "0"]
            ],
            ["true", "false"],
            []
        ])
        .to_string();
        if handling == "consume" {
            let current: Json = serde_json::from_str(&deployment).unwrap();
            for version in ["1", "2", "3", "5"] {
                for (field, expected) in [
                    (0, "native-proof-format"),
                    (1, "native-proof-descriptor"),
                    (2, "native-proof-policy"),
                ] {
                    let mut old = current.clone();
                    match field {
                        0 => old[0] = json!(format!("zkc.native-proof/{version}")),
                        1 => old[2][0] = json!(format!("zkc.native-proof-descriptor/{version}")),
                        _ => old[2][1][0] = json!(format!("zkc.native-proof-policy/{version}")),
                    }
                    old[3] = json!(hash(&logical::encode_tree(&old[2]).unwrap()));
                    let bytes = serde_json::to_vec(&old).unwrap();
                    assert_eq!(
                        NativeDeployment::admit(&bytes, &hash(&bytes), Default::default())
                            .err()
                            .unwrap(),
                        expected
                    );
                }
            }
            let mut old = current;
            old[2][2] = json!("zkc.native-origin/1");
            old[3] = json!(hash(&logical::encode_tree(&old[2]).unwrap()));
            let bytes = serde_json::to_vec(&old).unwrap();
            assert_eq!(
                NativeDeployment::admit(&bytes, &hash(&bytes), Default::default())
                    .err()
                    .unwrap(),
                "native-proof-descriptor"
            );
        }
        let admitted = NativeDeployment::admit(
            deployment.as_bytes(),
            &hash(deployment.as_bytes()),
            Default::default(),
        );
        if returned {
            // Both one-shot and attempt execution require this admission.
            // Refusal happens before an invocation can load inputs or issue roots.
            assert_eq!(admitted.err().unwrap(), "native-proof-output-kind");
            // General Program callers can retain returned units. Use that real
            // backend path to inject residual custody into the proof finalizer,
            // independently of the proof deployment's earlier admission gate.
            let backend = NativeBackend::new(
                Policy::default(),
                EntryPolicy::new(Domain::new("P", "s", "main", None), None),
                Default::default(),
            )
            .unwrap();
            let program = admit_supplied(candidate.as_bytes(), &backend).unwrap();
            let mut runner = Runner::new(&program, "main", "P", "s", backend, vec![])
                .unwrap_or_else(|e| panic!("{}", e.error));
            let zkc_runtime::interactive::Action::Local(action) = runner.poll() else {
                panic!("expected local unit creation");
            };
            runner.execute_local(&action.cut).unwrap();
            let zkc_runtime::interactive::Action::Returned(values) = runner.poll() else {
                panic!("expected returned unit");
            };
            assert!(matches!(values[0], Value::ResourceUnit(_)));
            let mut backend = runner.into_backend();
            assert_eq!(backend.active_frames(), 0);
            assert_eq!(backend.live_resource_units(), 1);
            let mut report = cleanup_report(Ok(vec![7, 8, 9]));
            retire_resources(
                &mut backend,
                &ServiceRegistry::new(Policy::default()),
                &[],
                &[],
                &mut report,
            );
            assert_eq!(report.outcome.unwrap_err(), "native-proof-cleanup");
            assert_eq!(report.cleanup_errors, ["native-proof-live-resource-units"]);
            continue;
        }
        let deployment = admitted.unwrap();
        let inputs = json!(["zkc.native-proof-inputs/1", [], [], "", [], "0"]);
        let report = deployment.execute(&inputs, None).unwrap();
        assert!(report.cleanup_errors.is_empty());
        let proof = report.outcome.unwrap();
        assert_eq!(proof.len(), 40);
        let request = inputs::decode(&deployment, &inputs, false).unwrap();
        let prepared =
            inputs::prepare(&deployment, &request, deployment.entry.validator(), false).unwrap();
        let mut root = logical::decode_tree(&prepared.root).unwrap();
        assert_eq!(root[0], "zkc.native-proof-binding/4");
        for version in ["1", "2", "3"] {
            root[0] = json!(format!("zkc.native-proof-binding/{version}"));
            let mut old = proof.clone();
            old[8..40].copy_from_slice(&Sha256::digest(logical::encode_tree(&root).unwrap()));
            assert_eq!(
                deployment
                    .execute(&inputs, Some(&old))
                    .unwrap()
                    .outcome
                    .unwrap_err(),
                "proof-header"
            );
        }
        assert!(
            deployment
                .execute(&inputs, Some(&proof))
                .unwrap()
                .outcome
                .is_ok()
        );
    }
}
fn cleanup_report(outcome: Result<Vec<u8>>) -> NativeProofReport {
    NativeProofReport {
        outputs: outcome
            .as_ref()
            .ok()
            .map(|_| BTreeMap::from([(0, Value::Bool(true))])),
        outcome,
        binding: String::new(),
        messages: 0,
        bytes: 0,
        cancelled: false,
        instructions: 0,
        resources: vec![],
        attempts: vec![],
        return_at: None,
        stop: None,
        attempt_policy: None,
        usage: Default::default(),
        external_work: 0,
        external_work_limit: NativeBackend::DEFAULT_EXTERNAL_WORK_LIMIT,
        cleanup_errors: vec![],
    }
}
#[test]
fn failed_retirement_discards_completed_bytes_and_preserves_a_primary_failure() {
    for primary in [Ok(vec![7, 8, 9]), Err("original-body-failure".to_owned())] {
        let failed_before_cleanup = primary.is_err();
        let mut backend = NativeBackend::new(
            Policy::default(),
            EntryPolicy::new(Domain::new("P", "s", "main", None), None),
            Default::default(),
        )
        .unwrap();
        let Value::Rng(root) = backend
            .issue_rng_for(Identity::Bls12381Fr, Domain::new("P", "s", "main", None), 1)
            .unwrap()
        else {
            panic!("rng");
        };
        let Value::Rng(other) = backend
            .issue_rng_for(Identity::Bls12381Fr, Domain::new("P", "s", "main", None), 1)
            .unwrap()
        else {
            panic!("rng");
        };
        backend.retire(&root).unwrap(); // Simulate an adapter custody error at final cleanup.
        let mut report = cleanup_report(primary);
        retire_resources(
            &mut backend,
            &ServiceRegistry::new(Policy::default()),
            &[root, other.clone()],
            &[],
            &mut report,
        );
        assert_eq!(
            report.outcome.err().unwrap(),
            if failed_before_cleanup {
                "original-body-failure"
            } else {
                "native-proof-cleanup"
            }
        );
        assert!(report.outputs.is_none());
        assert_eq!(report.cleanup_errors.len(), 1);
        assert_eq!(report.resources.len(), 1);
        assert!(
            backend.observe(&other).is_err(),
            "remaining roots still retire after an error"
        );
    }
}

#[test]
fn domain_inputs_use_current_native_codec() {
    for spelling in [
        "field:bn254.fr",
        "group:bn254.g1",
        "group:bn254.g2",
        "field:koala-bear",
        "field:koala-bear.ext8-binomial3",
        "field:ristretto255.scalar",
        "group:ristretto255.group",
        "rng:bn254.fr",
        "rng:koala-bear.ext8-binomial3",
        "rng:ristretto255.scalar",
        "nonce:ristretto255.scalar",
    ] {
        let ty = PhysicalType::default_for(LogicalType::parse(spelling).unwrap()).unwrap();
        assert!(input_kind(&ty).is_ok(), "{spelling}");
    }
}
#[test]
fn setup_authority_parser_rejects_ambiguous_records() {
    let id = "00".repeat(32);
    for value in [
        json!(["zkc.native-setup-authority/1", [["2", id], ["2", id]], []]),
        json!([
            "zkc.native-setup-authority/1",
            [["2", id]],
            [["1", "2"], ["1", "2"]]
        ]),
    ] {
        assert_eq!(
            SetupAuthority::parse(&serde_json::to_vec(&value).unwrap()).unwrap_err(),
            "native-proof-key-authority"
        );
    }
    for value in [
        json!(["zkc.native-setup-authority/1", [["02", id]], []]),
        json!(["zkc.native-setup-authority/1", [["2", "aF".repeat(32)]], []]),
        json!(["zkc.native-setup-authority/2", [], []]),
    ] {
        assert!(SetupAuthority::parse(&serde_json::to_vec(&value).unwrap()).is_err());
    }
}

#[test]
fn native_stop_record_retains_the_local_instruction_namespace() {
    use zkc_runtime::interactive::{LocalContext, Origin, Stop, StopKind};
    let stop = Stop {
        origin: Origin {
            session: "s".into(),
            entry: "main".into(),
            instance: "root".into(),
            path: vec![],
        },
        role: "V".into(),
        site: Some("ingress.rounds".into()),
        local: Some(Box::new(LocalContext {
            site: "ingress.rounds".into(),
            function: "count".into(),
            instruction: Some("scan".into()),
        })),
        kind: StopKind::Limit,
        cleanup_errors: vec![],
    };
    let record = stop_json(&stop);
    assert_eq!(record["site"], "ingress.rounds");
    assert_eq!(
        record["local"],
        json!({"site":"ingress.rounds","function":"count","instruction":"scan"})
    );
    assert_eq!(record["kind"], "Limit");
}
