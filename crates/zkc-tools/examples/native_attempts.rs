//! Two independently compiled clients share the native attempt host unchanged.
#[cfg(feature = "test-utils")]
#[path = "support/input_admission.rs"]
mod input_admission;
use serde_json::{Value as Json, json};
use sha2::{Digest, Sha256};
use std::{collections::BTreeMap, path::Path};
use zkc_backends::{Domain, EntryPolicy, GroupPoint, NativeBackend, Policy, Scalar, Value};
use zkc_runtime::{
    attempt::Limits,
    interactive::{ValueBudget, WorkBudget},
};
use zkc_tools::proof::{
    AttemptPolicy, InputValue, NativeCapacity, NativeDeployment, NativeProofReport, ProofInputs,
    hex,
};

fn inputs(envelope: &Json, producing: bool, fold: bool) -> Json {
    let policy = &envelope[2][1];
    let role = &policy[if producing { 2 } else { 3 }];
    let map = envelope[6]
        .as_array()
        .unwrap()
        .iter()
        .find(|row| &row[0] == role)
        .unwrap();
    let codec = NativeBackend::new(
        Policy::default(),
        EntryPolicy::new(Domain::new("P", "test", "main", None), None),
        Default::default(),
    )
    .unwrap();
    let wire = |port: &Json, ty: &Json| {
        let port: usize = port.as_str().unwrap().parse().unwrap();
        let value = match ty.as_str().unwrap() {
            "field:bls12-381.fr" => {
                Value::Field(Scalar::from(if fold && port == 1 { 5 } else { 3 }))
            }
            "group:bls12-381.g1" => {
                Value::Curve(GroupPoint::generator().scale(Scalar::from(if port == 0 {
                    1
                } else {
                    3
                })))
            }
            _ => panic!("unexpected wire input"),
        };
        hex(&codec.encode_native_value(&value).unwrap())
    };
    let public: Vec<_> = envelope[2][4]
        .as_array()
        .unwrap()
        .iter()
        .map(|p| json!([p[0], p[1], wire(&p[1], &p[2])]))
        .collect();
    let data: Vec<_> = map[2]
        .as_array()
        .unwrap()
        .iter()
        .map(|p| {
            json!([
                p[0],
                if p[1].as_str().unwrap().starts_with("rng:") {
                    json!(["rng", "4"])
                } else {
                    json!(["wire", wire(&p[0], &p[1])])
                }
            ])
        })
        .collect();
    let services: Vec<_> = map[4]
        .as_array()
        .unwrap()
        .iter()
        .map(|p| json!([p[0], "4"]))
        .collect();
    json!([
        "zkc.native-proof-inputs/1",
        public,
        data,
        "",
        services,
        "64"
    ])
}
fn policy(fold: bool) -> AttemptPolicy {
    AttemptPolicy {
        completion: 1,
        rng: if fold { vec![(2, 2)] } else { vec![] },
        limits: Limits {
            attempts: 4,
            proof_bytes: 16 * 1024 * 1024,
        },
        work: WorkBudget::default(),
        values: ValueBudget::default(),
    }
}
fn draws(report: &NativeProofReport, fold: bool) -> u64 {
    assert!(
        report.cleanup_errors.is_empty(),
        "{:?}",
        report.cleanup_errors
    );
    assert_eq!(report.resources.len(), 1);
    let resource = &report.resources[0];
    if fold {
        resource["transitions"].as_u64().unwrap()
    } else {
        assert_eq!(resource["leased"], false);
        resource["state"]["transitions"].as_u64().unwrap()
    }
}
fn run(directory: &Path, case: &Json) {
    let name = case["name"].as_str().unwrap();
    let fold = case["family"] == "fold";
    if case["abandonment"] == true {
        abandonment(directory, name, case["silent"] == true);
        return;
    }
    let bytes = std::fs::read(directory.join(format!("{name}.deployment"))).unwrap();
    let envelope: Json = serde_json::from_slice(&bytes).unwrap();
    let deployment =
        NativeDeployment::admit(&bytes, &hex(&Sha256::digest(&bytes)), Default::default()).unwrap();
    let producer = inputs(&envelope, true, fold);
    let validator = inputs(&envelope, false, fold);
    let p = policy(fold);
    #[cfg(feature = "test-utils")]
    if name == "fold_0" {
        input_admission::private_input_admission_boundary(
            &deployment,
            &envelope,
            &producer,
            Some(&p),
        );
    }
    if case["production"] == true {
        let mut p = p;
        p.limits.attempts = 3;
        let report = deployment.execute_attempts(&producer, &p).unwrap();
        assert_eq!(report.outcome.as_ref().unwrap_err(), "native-attempt-limit");
        assert_eq!(report.attempts.len(), 3);
        assert!(report.outputs.is_none());
        assert!(report.attempts.iter().all(|a| a.decision == Ok(false)
            && a.bytes > 40
            && a.stop.is_none()
            && a.return_at.is_none()));
        assert_eq!(draws(&report, fold), 3);
        assert!(!report.cancelled);
        assert_eq!(
            report.messages,
            report.attempts.iter().map(|a| a.messages).sum::<usize>()
        );
        assert_eq!(
            report.bytes,
            report.attempts.iter().map(|a| a.bytes).sum::<usize>()
        );
        assert_eq!(
            report.external_work,
            report.attempts.iter().map(|a| a.external_work).sum::<u64>()
        );
        assert_eq!(
            report.instructions,
            report
                .attempts
                .iter()
                .map(|a| a.usage.instructions)
                .sum::<u64>()
        );
        assert_eq!(
            report.usage.total_value_bytes,
            report
                .attempts
                .iter()
                .map(|a| a.usage.total_value_bytes)
                .sum::<usize>()
        );
        return;
    }
    let entropy_port = if fold { 2 } else { 3 };
    let tapes = |values: &[u64]| {
        BTreeMap::from([(
            entropy_port,
            values.iter().copied().map(Scalar::from).collect(),
        )])
    };
    let execute = |input: &Json, p: &AttemptPolicy, tape: &[u64]| {
        deployment
            .execute_attempts_test(input, p, tapes(tape))
            .unwrap()
    };
    let result = execute(&producer, &p, &[0, 3]);
    if case["fatal"] == true {
        assert!(result.outcome.is_err());
        assert!(result.outputs.is_none());
        assert_eq!(result.attempts.len(), 1);
        assert!(result.attempts[0].decision.is_err());
        assert_eq!(draws(&result, fold), 1);
        assert!(
            result.attempts[0].bytes > 40,
            "fatal client wrote a prefix before stopping"
        );
        return;
    }
    assert!(result.outcome.is_ok(), "{name}: {:?}", result.outcome);
    assert_eq!(result.attempts.len(), 2);
    assert_eq!(result.attempts[0].decision, Ok(false));
    assert_eq!(result.attempts[1].decision, Ok(true));
    let outputs = result.outputs.as_ref().unwrap();
    assert!(matches!(outputs.get(&1), Some(Value::Bool(true))));
    // RNG successors remain with the attempt lifecycle and are retired.
    if fold {
        assert!(!outputs.contains_key(&2));
    }
    assert_eq!(draws(&result, fold), 2);
    // The in-process path keeps the same actual provider advances and final
    // transcript as the positional transport, including RNG successor reuse.
    let codec = NativeBackend::new(
        Policy::default(),
        EntryPolicy::new(Domain::new("P", "test", "main", None), None),
        Default::default(),
    )
    .unwrap();
    let decode_hex = |v: &Json| -> Vec<u8> {
        v.as_str()
            .unwrap()
            .as_bytes()
            .as_chunks::<2>()
            .0
            .iter()
            .map(|pair| u8::from_str_radix(std::str::from_utf8(pair).unwrap(), 16).unwrap())
            .collect()
    };
    let typed = ProofInputs {
        public: producer[1]
            .as_array()
            .unwrap()
            .iter()
            .map(|row| InputValue::Wire(decode_hex(&row[2])))
            .collect(),
        inputs: producer[2]
            .as_array()
            .unwrap()
            .iter()
            .zip(&deployment.entry().producer().inputs)
            .map(|(row, (_, ty))| {
                if row[1][0] == "rng" {
                    InputValue::Resource {
                        budget: row[1][1].as_str().unwrap().parse().unwrap(),
                    }
                } else {
                    codec
                        .decode_native_value(ty, &decode_hex(&row[1][1]))
                        .unwrap()
                        .into()
                }
            })
            .collect(),
        context: Vec::new(),
        services: producer[4]
            .as_array()
            .unwrap()
            .iter()
            .map(|row| row[1].as_str().unwrap().parse().unwrap())
            .collect(),
        transcript_budget: 64,
    };
    let in_process = deployment
        .execute_attempts_typed_test(&typed, &p, tapes(&[0, 3]))
        .unwrap();
    assert_eq!(in_process.outcome, result.outcome);
    assert_eq!(in_process.binding, result.binding);
    assert_eq!(in_process.resources, result.resources);
    assert_eq!(in_process.attempts.len(), result.attempts.len());
    assert_eq!(in_process.instructions, result.instructions);
    assert!(matches!(
        in_process.outputs.as_ref().unwrap().get(&1),
        Some(Value::Bool(true))
    ));
    let proof = result.outcome.as_ref().unwrap();
    assert!(
        deployment
            .execute(&validator, Some(proof))
            .unwrap()
            .outcome
            .is_ok(),
        "{name}"
    );
    // Exact proof equality demonstrates a fresh transcript plus advanced provider,
    // not merely a verifier that also shares accidentally retained state.
    let reference = deployment
        .execute_test(&producer, None, tapes(&[3]))
        .unwrap();
    assert_eq!(reference.outcome.as_ref().unwrap(), proof);
    assert_eq!(
        result.instructions,
        result
            .attempts
            .iter()
            .map(|a| a.usage.instructions)
            .sum::<u64>()
    );
    assert_eq!(
        result.usage.total_value_bytes,
        result
            .attempts
            .iter()
            .map(|a| a.usage.total_value_bytes)
            .sum::<usize>()
    );
    assert_eq!(result.attempts[0].transcript, result.attempts[1].transcript);
    let first = execute(&producer, &p, &[3]);
    assert_eq!(first.attempts.len(), 1);
    assert_eq!(draws(&first, fold), 1);
    assert_eq!(first.outcome.as_ref().unwrap(), proof);

    let last = execute(&producer, &p, &[0, 0, 0, 3]);
    assert_eq!(last.attempts.len(), 4);
    assert_eq!(draws(&last, fold), 4);
    assert_eq!(last.outcome.as_ref().unwrap(), proof);
    let exhausted = execute(&producer, &p, &[0, 0, 0, 0]);
    assert_eq!(exhausted.attempts.len(), 4);
    assert_eq!(draws(&exhausted, fold), 4);
    assert_eq!(exhausted.outcome.err().unwrap(), "native-attempt-limit");
    assert!(exhausted.outputs.is_none());
    if fold {
        let mut limited = p.clone();
        limited.work.iterations = result.attempts[0].usage.iterations;
        let stopped = execute(&producer, &limited, &[0, 3]);
        assert!(stopped.outcome.is_err());
        assert!(stopped.outputs.is_none());
        assert_eq!(stopped.attempts.len(), 2);
        assert_eq!(stopped.usage.iterations, limited.work.iterations);
        assert_eq!(draws(&stopped, fold), 2);
    }
    let mut changed_context = validator.clone();
    changed_context[3] = json!("01");
    assert_eq!(
        deployment
            .execute(&changed_context, Some(proof))
            .unwrap()
            .outcome
            .err()
            .unwrap(),
        "proof-header"
    );
    if name.ends_with("_plain") || name.ends_with("_release") {
        let base = name
            .strip_suffix("_plain")
            .or_else(|| name.strip_suffix("_release"))
            .unwrap();
        let bytes = std::fs::read(directory.join(format!("{base}.deployment"))).unwrap();
        let other =
            NativeDeployment::admit(&bytes, &hex(&Sha256::digest(&bytes)), Default::default())
                .unwrap();
        assert!(
            other
                .execute(&validator, Some(proof))
                .unwrap()
                .outcome
                .is_ok()
        );
    }
    let mut limited = p.clone();
    limited.limits.attempts = 1;
    let exhausted = execute(&producer, &limited, &[0, 3]);
    assert_eq!(exhausted.outcome.unwrap_err(), "native-attempt-limit");
    assert_eq!(exhausted.attempts.len(), 1);
    let mut limited = p.clone();
    limited.work.instructions = result.attempts[0].usage.instructions + 1;
    let stopped = execute(&producer, &limited, &[0, 3]);
    assert!(stopped.outcome.is_err());
    assert!(stopped.outputs.is_none());
    assert_eq!(stopped.instructions, limited.work.instructions);
    assert_eq!(stopped.attempts.len(), 2);
    assert!(stopped.attempts[1].decision.is_err());
    let mut limited = p.clone();
    limited.values.total_bytes = result.attempts[0].usage.total_value_bytes;
    let stopped = execute(&producer, &limited, &[0, 3]);
    assert!(stopped.outcome.is_err());
    assert!(stopped.outputs.is_none());
    assert_eq!(stopped.usage.total_value_bytes, limited.values.total_bytes);
    assert_eq!(stopped.attempts.len(), 2);
    assert_eq!(draws(&stopped, fold), 1);
    let mut limited = p.clone();
    limited.limits.proof_bytes = 40;
    let stopped = execute(&producer, &limited, &[0, 3]);
    assert_eq!(stopped.outcome.as_ref().unwrap_err(), "proof-limit");
    assert_eq!(stopped.attempts.len(), 1);
    assert_eq!(draws(&stopped, fold), 1);
    let mut limited = p.clone();
    limited.limits.proof_bytes = 39;
    let stopped = execute(&producer, &limited, &[0, 3]);
    assert_eq!(stopped.outcome.as_ref().unwrap_err(), "proof-limit");
    assert_eq!(stopped.attempts.len(), 1);
    assert_eq!(stopped.attempts[0].bytes, 0);
    assert!(stopped.cancelled);
    assert_eq!(draws(&stopped, fold), 0);
    let mut limited = p.clone();
    limited.values.live_bytes = 0;
    let stopped = execute(&producer, &limited, &[0, 3]);
    assert_eq!(stopped.outcome.as_ref().unwrap_err(), "Limit");
    assert_eq!(stopped.attempts.len(), 1);
    assert_eq!(stopped.usage.live_value_bytes, 0);
    assert_eq!(draws(&stopped, fold), 0);
    let mut exhausted_input = producer.clone();
    if fold {
        exhausted_input[2][2][1][1] = json!("1");
    } else {
        exhausted_input[4][0][1] = json!("1");
    }
    let stopped = execute(&exhausted_input, &p, &[0, 3]);
    assert!(stopped.outcome.is_err());
    assert!(stopped.outputs.is_none());
    assert_eq!(stopped.attempts.len(), 2);
    // Scalar failure increments its authoritative generation/debit before refusal.
    assert_eq!(draws(&stopped, fold), 2);
    let mut exhausted_transcript = producer.clone();
    exhausted_transcript[5] = json!("0");
    let stopped = execute(&exhausted_transcript, &p, &[0, 3]);
    assert!(stopped.outcome.is_err());
    assert!(stopped.outputs.is_none());
    assert_eq!(stopped.attempts.len(), 1);
    assert!(stopped.attempts[0].stop.is_some());
    assert_eq!(
        stopped.attempts[0].transcript.as_ref().unwrap()["transitions"],
        1
    );
    assert_eq!(draws(&stopped, fold), 1);
    let mut too_many = p.clone();
    too_many.limits.attempts = 1025;
    assert!(
        deployment
            .execute_attempts_test(&producer, &too_many, tapes(&[3]))
            .is_err()
    );
    let mut too_large = p.clone();
    too_large.limits.proof_bytes += 1;
    assert!(
        deployment
            .execute_attempts_test(&producer, &too_large, tapes(&[3]))
            .is_err()
    );
    let mut bad = p.clone();
    bad.completion = 0;
    assert!(
        deployment
            .execute_attempts_test(&producer, &bad, tapes(&[3]))
            .is_err()
    );
    if fold {
        let mut bad = p.clone();
        bad.rng.clear();
        assert_eq!(
            deployment
                .execute_attempts_test(&producer, &bad, tapes(&[3]))
                .err()
                .unwrap(),
            "native-attempt-rng-map"
        );
        let mut bad = p.clone();
        bad.rng.push((2, 2));
        assert!(
            deployment
                .execute_attempts_test(&producer, &bad, tapes(&[3]))
                .is_err()
        );
    }
    let mut changed = proof.clone();
    changed.pop();
    assert_eq!(
        deployment
            .execute(&validator, Some(&changed))
            .unwrap()
            .outcome
            .err()
            .unwrap(),
        "proof-truncated"
    );
    let mut changed = proof.clone();
    changed.push(0);
    assert_eq!(
        deployment
            .execute(&validator, Some(&changed))
            .unwrap()
            .outcome
            .err()
            .unwrap(),
        "proof-trailing"
    );
    if fold {
        // Keep canonical field bytes but change the received salt absorbed before
        // challenges. The final recurrence is now checked under different coins.
        let mut changed = proof.clone();
        changed[54] ^= 1;
        let error = deployment
            .execute(&validator, Some(&changed))
            .unwrap()
            .outcome
            .unwrap_err();
        assert!(
            error == "artifact-rejected" || error.starts_with("artifact-stopped:Explicit("),
            "{error}"
        );
        // Both frames remain canonical scalars; only their observation order changes.
        let mut changed = proof.clone();
        let first = changed[40..86].to_vec();
        let second = changed[86..132].to_vec();
        changed[40..86].copy_from_slice(&second);
        changed[86..132].copy_from_slice(&first);
        let error = deployment
            .execute(&validator, Some(&changed))
            .unwrap()
            .outcome
            .unwrap_err();
        assert!(
            error == "artifact-rejected" || error.starts_with("artifact-stopped:Explicit("),
            "{error}"
        );
    }
    std::fs::write(
        directory.join(format!("{name}.producer.json")),
        serde_json::to_vec(&producer).unwrap(),
    )
    .unwrap();
    std::fs::write(
        directory.join(format!("{name}.validator.json")),
        serde_json::to_vec(&validator).unwrap(),
    )
    .unwrap();
    std::fs::write(directory.join(format!("{name}.proof")), proof).unwrap();
}
fn variable_proofs(directory: &Path) {
    for i in 0..2 {
        let bytes = std::fs::read(directory.join(format!("varying_{i}.deployment"))).unwrap();
        let envelope: Json = serde_json::from_slice(&bytes).unwrap();
        let deployment =
            NativeDeployment::admit(&bytes, &hex(&Sha256::digest(&bytes)), Default::default())
                .unwrap();
        let input = inputs(&envelope, true, true);
        let p = policy(true);
        let tapes = |values: &[u64]| {
            BTreeMap::from([(2, values.iter().copied().map(Scalar::from).collect())])
        };
        let produced = deployment
            .execute_attempts_test(&input, &p, tapes(&[0, 0, 0, 3]))
            .unwrap();
        assert_eq!(produced.attempts.len(), 4);
        let proof = produced.outcome.as_ref().unwrap();
        assert!(produced.attempts[..3].iter().all(|r| r.bytes > proof.len()));
        assert_eq!(produced.attempts[3].bytes, proof.len());
        assert_eq!(draws(&produced, true), 4);
        assert!(
            deployment
                .execute(&inputs(&envelope, false, true), Some(proof))
                .unwrap()
                .outcome
                .is_ok()
        );
        let reference = deployment.execute_test(&input, None, tapes(&[3])).unwrap();
        assert_eq!(reference.outcome.as_ref().unwrap(), proof);
    }
}
fn custody_controls(directory: &Path) {
    let bytes = std::fs::read(directory.join("swapped.deployment")).unwrap();
    let envelope: Json = serde_json::from_slice(&bytes).unwrap();
    let deployment =
        NativeDeployment::admit(&bytes, &hex(&Sha256::digest(&bytes)), Default::default()).unwrap();
    let input = inputs(&envelope, true, true);
    let tapes = |values: &[u64]| {
        BTreeMap::from([
            (2, values.iter().copied().map(Scalar::from).collect()),
            (4, vec![]),
        ])
    };
    let mut wrong = policy(true);
    wrong.rng = vec![(2, 2), (4, 3)];
    // Wrong roots are refused on both the complete and retry decisions.
    for tape in [&[3][..], &[0, 3][..]] {
        let refused = deployment
            .execute_attempts_test(&input, &wrong, tapes(tape))
            .unwrap();
        assert_eq!(
            refused.outcome.err().unwrap(),
            "refused:capability-successor-root"
        );
        assert_eq!(refused.attempts.len(), 1);
        assert!(refused.cleanup_errors.is_empty());
        assert_eq!(refused.resources[0]["transitions"], 1);
        assert_eq!(refused.resources[1]["transitions"], 0);
    }
    let mut correct = wrong;
    correct.rng = vec![(2, 3), (4, 2)];
    let produced = deployment
        .execute_attempts_test(&input, &correct, tapes(&[0, 3]))
        .unwrap();
    assert_eq!(produced.attempts.len(), 2);
    assert!(
        deployment
            .execute(
                &inputs(&envelope, false, true),
                Some(&produced.outcome.unwrap())
            )
            .unwrap()
            .outcome
            .is_ok()
    );
    let bytes = std::fs::read(directory.join("nonce.deployment")).unwrap();
    let deployment =
        NativeDeployment::admit(&bytes, &hex(&Sha256::digest(&bytes)), Default::default()).unwrap();
    assert_eq!(
        deployment
            .execute_attempts_test(&Json::Null, &policy(false), BTreeMap::new())
            .err()
            .unwrap(),
        "native-attempt-one-shot-input"
    );
}
fn empty_attempts(directory: &Path) {
    let bytes = std::fs::read(directory.join("empty.deployment")).unwrap();
    let deployment =
        NativeDeployment::admit(&bytes, &hex(&Sha256::digest(&bytes)), Default::default()).unwrap();
    let codec = NativeBackend::new(
        Policy::default(),
        EntryPolicy::new(Domain::new("P", "test", "main", None), None),
        Default::default(),
    )
    .unwrap();
    let input = |complete| {
        json!([
            "zkc.native-proof-inputs/1",
            [],
            [[
                "0",
                [
                    "wire",
                    hex(&codec.encode_native_value(&Value::Bool(complete)).unwrap())
                ]
            ]],
            "",
            [],
            "0"
        ])
    };
    let mut policy = policy(false);
    policy.completion = 2; // The selected output is after another producer Boolean.
    policy.limits.proof_bytes = 40;
    policy.work.iterations = 0;
    let complete = deployment.execute_attempts(&input(true), &policy).unwrap();
    assert_eq!(complete.attempts.len(), 1);
    assert_eq!(complete.messages, 0);
    assert_eq!(complete.bytes, 40);
    assert_eq!(complete.external_work, 0);
    assert!(complete.resources.is_empty());
    assert!(complete.cleanup_errors.is_empty());
    assert!(complete.attempts[0].transcript.is_none());
    let proof = complete.outcome.unwrap();
    assert_eq!(proof.len(), 40);
    let validator = json!(["zkc.native-proof-inputs/1", [], [], "", [], "0"]);
    assert!(
        deployment
            .execute(&validator, Some(&proof))
            .unwrap()
            .outcome
            .is_ok()
    );
    // No-progress retries have no implicit entropy or transcript requirements.
    policy.limits.attempts = 1024;
    let exhausted = deployment.execute_attempts(&input(false), &policy).unwrap();
    assert_eq!(
        exhausted.outcome.as_ref().unwrap_err(),
        "native-attempt-limit"
    );
    assert_eq!(exhausted.attempts.len(), 1024);
    assert_eq!(exhausted.bytes, 40 * 1024);
    assert_eq!(exhausted.messages, 0);
    assert!(exhausted.resources.is_empty());
    assert!(exhausted.cleanup_errors.is_empty());
    assert!(
        exhausted
            .attempts
            .iter()
            .all(|r| r.decision == Ok(false) && r.transcript.is_none())
    );
    assert_eq!(
        exhausted.usage.instructions,
        complete.usage.instructions * 1024
    );
    assert_eq!(
        exhausted.usage.total_value_bytes,
        complete.usage.total_value_bytes * 1024
    );
}
fn mixed_custody(directory: &Path) {
    for suite in 0..2 {
        let bytes = std::fs::read(directory.join(format!("mixed_{suite}.deployment"))).unwrap();
        let envelope: Json = serde_json::from_slice(&bytes).unwrap();
        let deployment =
            NativeDeployment::admit(&bytes, &hex(&Sha256::digest(&bytes)), Default::default())
                .unwrap();
        let producer = inputs(&envelope, true, true);
        let tapes = || {
            BTreeMap::from([
                (2, vec![Scalar::from(0), Scalar::from(3)]),
                (4, vec![Scalar::from(5), Scalar::from(7)]),
            ])
        };
        let complete = deployment
            .execute_attempts_test(&producer, &policy(true), tapes())
            .unwrap();
        assert!(complete.outcome.is_ok());
        assert_eq!(complete.attempts.len(), 2);
        assert!(complete.cleanup_errors.is_empty());
        assert_eq!(complete.resources.len(), 2);
        assert_eq!(complete.resources[0]["transitions"], 2);
        assert_eq!(complete.resources[1]["state"]["transitions"], 2);
        assert_eq!(complete.resources[1]["leased"], false);
        assert_eq!(complete.resources[1]["poisoned"], false);
        assert!(
            deployment
                .execute(
                    &inputs(&envelope, false, true),
                    Some(&complete.outcome.unwrap())
                )
                .unwrap()
                .outcome
                .is_ok()
        );
        let mut exhausted_input = producer.clone();
        exhausted_input[4][0][1] = json!("1");
        let failed = deployment
            .execute_attempts_test(&exhausted_input, &policy(true), tapes())
            .unwrap();
        assert_eq!(
            failed.outcome.as_ref().unwrap_err(),
            "exhausted:resource-budget"
        );
        assert_eq!(failed.attempts.len(), 2);
        assert_eq!(failed.resources[0]["transitions"], 2);
        assert_eq!(failed.resources[1]["state"]["transitions"], 2);
        assert_eq!(failed.resources[1]["leased"], false);
        assert_eq!(failed.resources[1]["poisoned"], true);
        assert_eq!(
            failed.attempts[1].decision.as_ref().unwrap_err(),
            "exhausted:resource-budget"
        );
        assert!(failed.attempts[1].stop.is_some());
        assert!(failed.cleanup_errors.is_empty());
        let mut missing_service = tapes();
        missing_service.remove(&4);
        let failed = deployment
            .execute_attempts_test(&producer, &policy(true), missing_service)
            .unwrap();
        assert_eq!(
            failed.outcome.as_ref().unwrap_err(),
            "native-proof-test-entropy-port"
        );
        assert!(failed.attempts.is_empty());
        assert_eq!(failed.attempt_policy.as_ref().unwrap().len(), 64);
        assert_eq!(failed.resources.len(), 1);
        assert_eq!(failed.resources[0]["transitions"], 0);
        assert!(failed.cleanup_errors.is_empty());
    }
}
fn main() {
    let directory = std::env::args().nth(1).unwrap();
    let directory = Path::new(&directory);
    let manifest: Vec<Json> =
        serde_json::from_slice(&std::fs::read(directory.join("manifest.json")).unwrap()).unwrap();
    empty_attempts(directory);
    mixed_custody(directory);
    custody_controls(directory);
    variable_proofs(directory);
    for case in &manifest {
        run(directory, case);
    }
    println!(
        "native attempts: {} client deployments and custody controls passed",
        manifest.len()
    );
}

fn abandonment(directory: &Path, name: &str, silent: bool) {
    let bytes = std::fs::read(directory.join(format!("{name}.deployment"))).unwrap();
    let envelope: Json = serde_json::from_slice(&bytes).unwrap();
    let deployment =
        NativeDeployment::admit(&bytes, &hex(&Sha256::digest(&bytes)), Default::default()).unwrap();
    if !silent {
        check_exit_mutations(&envelope);
    }
    let p = inputs(&envelope, true, true);
    let v = inputs(&envelope, false, true);
    let tape = |xs: &[u64]| BTreeMap::from([(2, xs.iter().copied().map(Scalar::from).collect())]);
    let result = deployment
        .execute_attempts_test(
            &p,
            &policy(true),
            tape(if silent { &[0, 3] } else { &[0, 3, 7, 9] }),
        )
        .unwrap();
    assert!(result.cleanup_errors.is_empty());
    let proof = result.outcome.as_ref().unwrap();
    assert_eq!(result.attempts.len(), 2);
    let retry = &result.attempts[0];
    let done = &result.attempts[1];
    assert_eq!(retry.decision, Ok(false));
    assert_eq!(done.decision, Ok(true));
    assert_eq!(retry.messages, if silent { 1 } else { 2 });
    assert_eq!(done.messages, 4);
    assert_eq!(retry.usage.iterations, if silent { 2 } else { 1 });
    assert_eq!(done.usage.iterations, if silent { 6 } else { 2 });
    assert_eq!(retry.return_at.as_ref().unwrap().1, "abandon");
    assert_eq!(
        retry.return_at.as_ref().unwrap().0.path.len(),
        if silent { 2 } else { 1 }
    );
    assert!(done.return_at.is_none());
    assert_eq!(draws(&result, true), if silent { 2 } else { 4 });
    // Invocation capacity bounds the entire attempt session, including the
    // consumed prefix of an early return. An attempt policy cannot raise it.
    let mut capacity = NativeCapacity::default();
    capacity.work.iterations = retry.usage.iterations;
    let bounded = deployment.clone().with_capacity(capacity).unwrap();
    assert_eq!(
        bounded
            .execute_attempts_test(&p, &policy(true), tape(&[0, 3]))
            .err()
            .unwrap(),
        "native-attempt-limits"
    );
    let mut within = policy(true);
    within.work.iterations = capacity.work.iterations;
    let exhausted = bounded
        .execute_attempts_test(&p, &within, tape(&[0, 3]))
        .unwrap();
    assert!(exhausted.outcome.is_err());
    assert_eq!(exhausted.attempts.len(), 2);
    assert_eq!(exhausted.attempts[0].decision, Ok(false));
    assert!(matches!(
        exhausted.attempts[1].stop.as_ref().unwrap().kind,
        zkc_runtime::interactive::StopKind::Limit
    ));
    assert_eq!(exhausted.usage.iterations, capacity.work.iterations);
    assert!(exhausted.cleanup_errors.is_empty());
    deployment
        .execute(&v, Some(proof))
        .unwrap()
        .outcome
        .unwrap();
    let reference = deployment
        .execute_test(&p, None, tape(if silent { &[3] } else { &[3, 7, 9] }))
        .unwrap();
    assert_eq!(reference.outcome.unwrap(), *proof);
    // A prefix is not accepted merely because the producer returned normally.
    let truncated = deployment.execute_test(&p, None, tape(&[0])).unwrap();
    assert_eq!(truncated.return_at.as_ref().unwrap().1, "abandon");
    assert_eq!(truncated.return_at, retry.return_at);
    assert!(truncated.cleanup_errors.is_empty());
    let truncated = truncated.outcome.unwrap();
    assert!(
        deployment
            .execute(&v, Some(&truncated))
            .unwrap()
            .outcome
            .is_err()
    );
}

// Check the independent Rust boundary after deliberately re-pinning a candidate.
// Malformed affine state is already rejected by ordinary admission; event order
// additionally needs the proof-specific checker.
fn check_exit_mutations(envelope: &Json) {
    use zkc_runtime::interactive::admit_supplied;
    let codec = NativeBackend::new(
        Policy::default(),
        EntryPolicy::new(Domain::new("P", "test", "main", None), None),
        Default::default(),
    )
    .unwrap();
    let original: Json = serde_json::from_str(envelope[4].as_str().unwrap()).unwrap();
    let refuse = |candidate: &Json| {
        let mut e = envelope.clone();
        let c = serde_json::to_string(candidate).unwrap();
        e[5] = json!(hex(&Sha256::digest(c.as_bytes())));
        e[4] = json!(c);
        let bytes = serde_json::to_vec(&e).unwrap();
        NativeDeployment::admit(&bytes, &hex(&Sha256::digest(&bytes)), Default::default())
            .unwrap_err()
    };
    for missing in [false, true] {
        let mut candidate = original.clone();
        let body = candidate[4][0][7]
            .as_array_mut()
            .unwrap()
            .iter_mut()
            .find(|i| i[0] == "loop")
            .unwrap()[5]
            .as_array_mut()
            .unwrap();
        let n = body.iter().position(|i| i[0] == "return_if").unwrap();
        if missing {
            body[n][4].as_array_mut().unwrap().pop();
        } else {
            let stale = body
                .iter()
                .take(n)
                .rfind(|i| i[0] == "local" && i[1].as_str().unwrap().starts_with("_transcript"))
                .unwrap()[3][0]
                .clone();
            *body[n][3].as_array_mut().unwrap().last_mut().unwrap() = stale;
        }
        let error = admit_supplied(&serde_json::to_vec(&candidate).unwrap(), &codec).unwrap_err();
        assert_eq!(
            error.code,
            if missing {
                zkc_runtime::interactive::ErrorCode::Signature
            } else {
                zkc_runtime::interactive::ErrorCode::Ssa
            }
        );
        assert_eq!(refuse(&candidate), error.to_string());
    }
    let mut candidate = original.clone();
    let body = candidate[4][0][7]
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|i| i[0] == "loop")
        .unwrap()[5]
        .as_array_mut()
        .unwrap();
    let n = body.iter().position(|i| i[0] == "return_if").unwrap();
    let delivery = body
        .iter()
        .take(n)
        .rposition(|i| i[0] == "local" && i[1].as_str().unwrap().starts_with("_transcript"))
        .unwrap();
    let calculation = body.remove(n - 1);
    let mut exit = body.remove(n - 1);
    let pending = body[delivery][3][0].clone();
    let observed = body[delivery][4][0].clone();
    let continued = exit[4].as_array().unwrap().last().unwrap().clone();
    *exit[3].as_array_mut().unwrap().last_mut().unwrap() = pending;
    body[delivery][3][0] = continued;
    let last = body.last_mut().unwrap()[1]
        .as_array_mut()
        .unwrap()
        .last_mut()
        .unwrap();
    *last = observed;
    body.insert(delivery, calculation);
    body.insert(delivery + 1, exit);
    admit_supplied(&serde_json::to_vec(&candidate).unwrap(), &codec)
        .expect("pending-observation mutation must remain typed and affine");
    assert_eq!(refuse(&candidate), "native-proof-observation-order");
}
