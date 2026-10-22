use super::*;
use zkc_runtime::interpreter::Runner;
mod admission;
#[test]
fn native_measurement_preserves_proof_decode_stops_with_shared_capacity() {
    use zkc_runtime::vm::{ExecutionLedger, Program, StopKind, ValueBudget};
    let program = Program::decode(
        json!([
            "zkc.program/0",
            [],
            [],
            [[
                "participant",
                "v",
                "root",
                "V",
                [["yes", "bool@native.bool/0"]],
                ["bool@native.bool/0"],
                [
                    [
                        "receive",
                        "message",
                        "message",
                        "P",
                        "payload",
                        "bytes@native.bytes/0"
                    ],
                    ["return", ["yes"]]
                ],
                []
            ]],
            [["entry", "main", [["V", "v"]]]]
        ])
        .to_string()
        .as_bytes(),
    )
    .unwrap();
    let binding = [7; 32];
    let mut writer = ProofWriter::new(ProofFormat::Native, &binding);
    writer.message(b"ZKCV\x00\x46\x01\x00\x00\x00").unwrap();
    let proof = writer.finish().unwrap();
    for shared in [false, true] {
        let ledger = shared.then(|| {
            ExecutionLedger::new(
                ValueBudget {
                    live_bytes: 1024 * 1024,
                    ..Default::default()
                },
                Default::default(),
            )
        });
        let backend = NativeBackend::new(
            Policy::default(),
            EntryPolicy::new(Domain::new("V", "session", "main", None), None),
            Default::default(),
        )
        .unwrap();
        let mut runner = Runner::new_for_role_with_ledger(
            &program,
            "main",
            "V",
            "session",
            backend,
            vec![Value::Bool(true)],
            ValueBudget {
                live_bytes: 4096,
                ..Default::default()
            },
            Default::default(),
            ledger.clone(),
        )
        .unwrap_or_else(|error| panic!("{}", error.error));
        let report = driver::validate_native_shared(
            &mut runner,
            &proof,
            &binding,
            driver::Transport::Messages(ProofFormat::Native),
            0,
            ledger.clone(),
        );
        let Err(ArtifactFailure::Stopped(stop)) = report.outcome else {
            panic!("malformed native message must stop the receive");
        };
        assert!(matches!(
            stop.kind,
            StopKind::Decode(zkc_runtime::vm::DecodeReason::Length)
        ));
        assert_eq!(stop.site.as_deref(), Some("message"));
        assert_eq!(runner.usage().instructions, 1);
        assert_eq!(report.messages, 1);
        assert!(report.cancelled.is_none());
        if let Some(ledger) = ledger {
            assert_eq!(ledger.snapshot().live_reserved_bytes, 0);
        }
    }
}
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
        assert_eq!(wire_codec(&logical).as_deref(), Some("zkc.native-data/0"));
        assert_eq!(input_kind(&physical).unwrap(), "wire");
    }
    for spelling in [
        "polynomial:bn254.fr",
        "sequence<polynomial:bn254.fr>",
        "sequence<prover_key:multilinear.kzg.bls12-381/0>",
    ] {
        assert!(wire_type(spelling, false).is_err());
    }
}
#[test]
fn proof_host_admits_internal_units_but_refuses_unexportable_custody() {
    for handling in ["consume", "discard", "return"] {
        let returned = handling == "return";
        let binding = zkc_runtime::vm::OperationBinding {
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
        outputs.push("bool@native.bool/0".into());
        let mut values = if returned { vec!["u"] } else { vec![] };
        values.push("done");
        let mut body = vec![json!(["op", "create", "create", [], [], ["u"]])];
        if handling == "consume" {
            body.push(json!(["op", "consume", "consume", [], ["u"], []]));
        }
        body.push(json!(["bool_constant", "done", "done", true]));
        body.push(json!(["return", values]));
        let candidate = json!([
            "zkc.program/0",
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
            [
                ["function", "unit", [], outputs, body, ["unit", []]],
                [
                    "function",
                    "accept",
                    [],
                    ["bool@native.bool/0"],
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
                    ["bool@native.bool/0"],
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
            "zkc.native-proof-descriptor/0",
            [
                "zkc.native-proof-policy/0",
                "main",
                "P",
                "V",
                "0",
                "",
                [],
                [],
                [],
                "zkc.framed/0",
                ""
            ],
            "zkc.native-origin/0",
            [],
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
            "zkc.native-proof/0",
            "0".repeat(64),
            descriptor,
            hash(&logical::encode_tree(&descriptor).unwrap()),
            candidate,
            hash(candidate.as_bytes()),
            [
                ["P", "prover", [], output_map, [], ""],
                ["V", "verifier", [], [["0", "bool"]], [], "0"]
            ],
            ["true", "false", "false", "true", "false", "true"],
            []
        ])
        .to_string();
        if handling == "consume" {
            let current: Json = serde_json::from_str(&deployment).unwrap();
            for (field, expected) in [
                (0, "native-proof-format"),
                (1, "native-proof-descriptor"),
                (2, "native-proof-policy"),
                (3, "native-proof-descriptor"),
            ] {
                let mut malformed = current.clone();
                match field {
                    0 => malformed[0] = json!("invalid.native-proof"),
                    1 => malformed[2][0] = json!("invalid.native-proof-descriptor"),
                    2 => malformed[2][1][0] = json!("invalid.native-proof-policy"),
                    _ => malformed[2][2] = json!("invalid.native-origin"),
                }
                malformed[3] = json!(hash(&logical::encode_tree(&malformed[2]).unwrap()));
                let bytes = serde_json::to_vec(&malformed).unwrap();
                assert_eq!(
                    NativeDeployment::admit(
                        &bytes,
                        &Sha256::digest(&bytes).into(),
                        Default::default()
                    )
                    .err()
                    .unwrap(),
                    expected
                );
            }
        }
        let admitted = NativeDeployment::admit(
            deployment.as_bytes(),
            &Sha256::digest(deployment.as_bytes()).into(),
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
            let program = zkc_runtime::vm::Program::decode(candidate.as_bytes())
                .and_then(|program| {
                    program.check_installation(&backend)?;
                    Ok(program)
                })
                .unwrap();
            let mut runner = Runner::new(&program, "main", "P", "s", backend, vec![])
                .unwrap_or_else(|e| panic!("{}", e.error));
            let zkc_runtime::vm::Action::Local(action) = runner.poll() else {
                panic!("expected local unit creation");
            };
            runner.execute_local(&action.cut).unwrap();
            let zkc_runtime::vm::Action::Returned(values) = runner.poll() else {
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
        let deployment_bytes = deployment.clone();
        let deployment = admitted.unwrap();
        let inputs = json!(["zkc.native-proof-inputs/0", [], [], "", [], "0"]);
        let report = crate::proof::tests::execute(
            &deployment,
            &inputs,
            crate::proof::Invocation::one_shot(None),
        )
        .unwrap();
        assert!(report.cleanup_errors.is_empty());
        assert_eq!(report.verification_result(), None);
        let proof = report.outcome.unwrap();
        assert_eq!(proof.len(), 40);
        let request = ProofInputs::decode(&deployment, &inputs, Invocation::Verify(&[])).unwrap();
        let prepared = inputs::prepare(
            &deployment,
            &request,
            deployment.entry.validator().unwrap(),
            false,
            &mut crate::host::setups::VerifierKeys::new(deployment.capacity.backend().ark_bounds()),
        )
        .unwrap();
        // Independently framed, frozen bytes: do not derive this expectation
        // with logical::encode_tree or the Host's binding constructor.
        let vector: Json = serde_json::from_str(include_str!(
            "../../../zkc-test-support/fixtures/native-proof-binding.json"
        ))
        .unwrap();
        assert!(prepared.root.is_empty()); // No managed transcript consumes it.
        assert_eq!(hex(&prepared.binding), vector["sha256"]);
        assert_eq!(hex(&proof[8..40]), vector["sha256"]);
        let encoded = unhex(&vector["encoded_hex"]).unwrap();
        assert_eq!(encoded.len(), vector["bytes"].as_u64().unwrap() as usize);
        let root = logical::decode_tree(&encoded).unwrap();
        assert_eq!(root, vector["tree"]);
        assert_eq!(root[0], "zkc.native-proof-binding/0");
        // Bind the complete current invocation, including its context and arity.
        for field in [0, 3, 4, 10] {
            let mut changed = root.clone();
            match field {
                0 => changed[0] = json!("invalid.native-proof-binding"),
                3 => changed[3] = json!("1".repeat(64)),
                4 => changed[4] = json!("other_entry"),
                _ => changed.as_array_mut().unwrap().push(json!([])),
            }
            let mut changed_proof = proof.clone();
            changed_proof[8..40]
                .copy_from_slice(&Sha256::digest(logical::encode_tree(&changed).unwrap()));
            assert_eq!(
                crate::proof::tests::execute(
                    &deployment,
                    &inputs,
                    crate::proof::Invocation::one_shot(Some(&changed_proof))
                )
                .unwrap()
                .outcome
                .unwrap_err(),
                "proof-header"
            );
        }
        let mut different_context = inputs.clone();
        different_context[3] = json!("01");
        assert_eq!(
            crate::proof::tests::execute(
                &deployment,
                &different_context,
                crate::proof::Invocation::one_shot(Some(&proof))
            )
            .unwrap()
            .outcome
            .unwrap_err(),
            "proof-header"
        );
        let verified = crate::proof::tests::execute(
            &deployment,
            &inputs,
            crate::proof::Invocation::one_shot(Some(&proof)),
        )
        .unwrap();
        assert!(verified.outcome.is_ok());
        assert_eq!(verified.verification_result(), Some(true));
        if handling == "consume" {
            // A normal negative decision is retained structurally before its
            // diagnostic is rendered. Malformed framing remains a failure.
            let mut rejected_program: Json = serde_json::from_str(&candidate).unwrap();
            rejected_program[2][1][4][0][3] = json!(false);
            let rejected_candidate = rejected_program.to_string();
            let mut rejected: Json = serde_json::from_str(&deployment_bytes).unwrap();
            rejected[4] = json!(rejected_candidate);
            rejected[5] = json!(hash(rejected_candidate.as_bytes()));
            let bytes = serde_json::to_vec(&rejected).unwrap();
            let rejected =
                NativeDeployment::admit(&bytes, &Sha256::digest(&bytes).into(), Default::default())
                    .unwrap();
            let produced = execute(&rejected, &inputs, Invocation::Prove).unwrap();
            let rejected_proof = produced.outcome.unwrap();
            let declined =
                execute(&rejected, &inputs, Invocation::Verify(&rejected_proof)).unwrap();
            assert_eq!(declined.verification_result(), Some(false));
            assert!(declined.outputs.is_none());
            let malformed = execute(&rejected, &inputs, Invocation::Verify(&[])).unwrap();
            assert_eq!(malformed.verification_result(), None);

            // Three completed false trials exercise aggregation independently
            // of successful one-shot proving and verification above.
            let mut program: Json = serde_json::from_str(&candidate).unwrap();
            program[2][0][4][2][3] = json!(false);
            let mut repeated: Json = serde_json::from_str(&deployment_bytes).unwrap();
            let candidate = program.to_string();
            repeated[4] = json!(candidate);
            repeated[5] = json!(hash(candidate.as_bytes()));
            let bytes = serde_json::to_vec(&repeated).unwrap();
            let repeated =
                NativeDeployment::admit(&bytes, &Sha256::digest(&bytes).into(), Default::default())
                    .unwrap();
            let policy = AttemptPolicy {
                completion: 1,
                rng: vec![],
                limits: zkc_runtime::attempt::Limits {
                    attempts: 3,
                    proof_bytes: MAX_PROOF_BYTES,
                },
                work: repeated.capacity.work,
                values: repeated.capacity.values,
            };
            let report = execute(&repeated, &inputs, Invocation::Attempts(&policy)).unwrap();
            assert!(report.outcome.is_err());
            assert_eq!(report.attempts.len(), 3);
            assert!(report.attempts.iter().all(|a| a.decision == Ok(false)));
            if let Some(counts) = report.execution_counts.json() {
                assert_eq!(counts["events"]["created_frames"], 6);
                assert_eq!(counts["events"]["backend_enter_calls"], 6);
                assert_eq!(counts["events"]["backend_leave_calls"], 6);
                assert_eq!(counts["operations"]["resource_unit.create"], 3);
                assert_eq!(counts["operations"]["resource_unit.consume"], 3);
                assert_eq!(
                    report.usage.instructions,
                    report
                        .attempts
                        .iter()
                        .map(|a| a.usage.instructions)
                        .sum::<u64>()
                );
            }
        }
    }
}
fn cleanup_report(outcome: Result<Vec<u8>>) -> NativeProofReport {
    NativeProofReport {
        retained: Vec::new(),
        retained_outputs: Vec::new(),
        verification: None,
        execution_counts: Default::default(),
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
        service_draws: 0,
        attempts: vec![],
        return_at: None,
        stop: None,
        attempt_policy: None,
        usage: Default::default(),
        external_work: 0,
        ring_work: 0,
        sequence_work: 0,
        ring_work_limit: zkc_native::ring::DEFAULT_WORK_LIMIT,
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
        report.verification = Some(VerificationDecision::Accepted);
        retire_resources(
            &mut backend,
            &ServiceRegistry::new(Policy::default()),
            &[root, other.clone()],
            &[],
            &mut report,
        );
        assert_eq!(
            report.outcome.as_ref().err().unwrap(),
            if failed_before_cleanup {
                "original-body-failure"
            } else {
                "native-proof-cleanup"
            }
        );
        assert!(report.outputs.is_none());
        assert_eq!(report.cleanup_errors.len(), 1);
        assert_eq!(report.verification_result(), None);
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
        json!(["zkc.native-setup-authority/0", [["2", id], ["2", id]], []]),
        json!([
            "zkc.native-setup-authority/0",
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
        json!(["zkc.native-setup-authority/0", [["02", id]], []]),
        json!(["zkc.native-setup-authority/0", [["2", "aF".repeat(32)]], []]),
        json!(["invalid.native-setup-authority", [], []]),
    ] {
        assert!(SetupAuthority::parse(&serde_json::to_vec(&value).unwrap()).is_err());
    }
}

#[test]
fn native_stop_record_retains_the_local_instruction_namespace() {
    use zkc_runtime::vm::{LocalContext, Origin, Stop, StopKind};
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

fn execute(
    deployment: &crate::proof::NativeDeployment,
    input: &serde_json::Value,
    invocation: crate::proof::Invocation<'_>,
) -> Result<crate::proof::NativeProofReport> {
    let input = crate::proof::ProofInputs::decode(deployment, input, invocation)?;
    let report = deployment.execute(&input, invocation)?;
    if let Some(counts) = report.execution_counts.json()
        && !counts["events"].as_object().unwrap().is_empty()
    {
        assert_eq!(
            counts["events"]["charged_instructions"].as_u64().unwrap()
                + counts["events"]["replayed_instructions"].as_u64().unwrap(),
            report.usage.instructions
        );
        if report.outcome.is_ok() {
            assert_eq!(
                counts["events"]["backend_enter_calls"],
                counts["events"]["backend_leave_calls"]
            );
        }
    }
    Ok(report)
}
