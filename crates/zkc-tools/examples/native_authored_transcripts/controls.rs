//! Authority, failure and retained-prefix controls over admitted deployments.
use super::reference::hash_word;
use super::{clean, codec, inputs, messages, policy, replace, unhex, words};
use serde_json::{Value as Json, json};
use std::{collections::BTreeMap, path::Path};
use zkc_backends::{NativeBackend, Scalar, Value, external::openvm};
use zkc_tools::artifact::{hex, native::NativeDeployment};
pub(super) fn prefix_controls(
    directory: &Path,
    name: &str,
    deployment: &NativeDeployment,
    envelope: &Json,
) {
    let values = [words([129; 32]), words([3; 32])];
    let producer = inputs(envelope, &values, true);
    let validator = inputs(envelope, &values, false);
    let mut policy = policy();
    policy.rng = vec![(2, 2)];
    let tapes = |xs: &[u64]| BTreeMap::from([(2, xs.iter().copied().map(Scalar::from).collect())]);
    let report = deployment
        .execute_attempts_test(&producer, &policy, tapes(&[0, 0, 3, 7]))
        .unwrap();
    assert!(report.cleanup_errors.is_empty());
    let proof = report.outcome.as_ref().unwrap();
    deployment
        .execute(&validator, Some(proof))
        .unwrap()
        .outcome
        .unwrap();
    assert_eq!(report.external_work, 260);
    assert_eq!(
        report
            .attempts
            .iter()
            .map(|r| r.external_work)
            .collect::<Vec<_>>(),
        [65, 65, 130]
    );
    assert_eq!(
        report
            .attempts
            .iter()
            .map(|r| r.decision.as_ref().unwrap())
            .collect::<Vec<_>>(),
        [&false, &false, &true]
    );
    if name.starts_with("prefix_abandon") {
        assert_eq!(
            report
                .attempts
                .iter()
                .map(|r| r.messages)
                .collect::<Vec<_>>(),
            [0, 0, 1]
        );
        assert!(report.attempts[..2].iter().all(|r| r.return_at.is_some()));
    } else {
        assert!(report.attempts.iter().all(|r| r.messages == 1));
    }
    assert_eq!(report.resources.len(), 1);
    assert_eq!(report.resources[0]["generation"], 4);
    assert_eq!(report.resources[0]["transitions"], 4);
    let direct = deployment
        .execute_test(&producer, None, tapes(&[3, 7]))
        .unwrap();
    assert_eq!(direct.outcome.unwrap(), *proof);
    let first = hash_word(&[vec![129; 32], vec![3; 32]].concat());
    let second = hash_word(&[first.to_vec(), vec![3; 32]].concat());
    assert_eq!(
        messages(proof),
        [codec()
            .encode_native_value(&words(second.map(u64::from)))
            .unwrap()]
    );
    // Fatal work exhaustion after a consumed RNG draw never becomes retry.
    let limit = deployment.clone().with_external_work_limit(129).unwrap();
    let failed = limit
        .execute_attempts_test(&producer, &policy, tapes(&[0, 3, 7]))
        .unwrap();
    assert_eq!(
        failed.outcome.as_ref().unwrap_err(),
        "exhausted:external-work-limit"
    );
    assert!(failed.cleanup_errors.is_empty());
    assert_eq!(failed.external_work, 65);
    assert_eq!(failed.attempts.len(), 2);
    assert_eq!(failed.attempts[1].external_work, 0);
    assert_eq!(
        failed.attempts[1].decision.as_ref().unwrap_err(),
        "exhausted:external-work-limit"
    );
    assert_eq!(failed.resources[0]["generation"], 2);
    assert_eq!(failed.attempts[1].messages, 0);
    let stop = failed.attempts[1].stop.as_ref().unwrap();
    // Participant stops identify the enclosing local-call site.
    assert_eq!(stop.site.as_deref(), Some("prepare"));
    assert!(
        matches!(&stop.kind, zkc_runtime::interactive::StopKind::Backend(error)
        if error.code == "exhausted:external-work-limit")
    );
    let summary = json!({"external_work":report.external_work,"resources":report.resources,
        "attempts":report.attempts.iter().map(|r| json!({"decision":r.decision,"messages":r.messages,
            "bytes":r.bytes,"instructions":r.usage.instructions,"calls":r.usage.calls,
            "iterations":r.usage.iterations,"external_work":r.external_work})).collect::<Vec<_>>()});
    std::fs::write(
        directory.join(format!("{name}.summary.json")),
        serde_json::to_vec_pretty(&summary).unwrap(),
    )
    .unwrap();
    for (suffix, input) in [("producer.json", &producer), ("validator.json", &validator)] {
        std::fs::write(
            directory.join(format!("{name}.{suffix}")),
            serde_json::to_vec(input).unwrap(),
        )
        .unwrap();
    }
    std::fs::write(directory.join(format!("{name}.proof")), proof).unwrap();
}

pub(super) fn controls(
    deployment: &NativeDeployment,
    envelope: &Json,
    values: &[Value],
    proof: &[u8],
    family: &str,
    snapshot: bool,
) {
    let producer = &inputs(envelope, values, true);
    let validator = &inputs(envelope, values, false);
    for limit in [NativeBackend::DEFAULT_EXTERNAL_WORK_LIMIT + 1, u64::MAX] {
        assert_eq!(
            deployment
                .clone()
                .with_external_work_limit(limit)
                .unwrap_err(),
            "native-proof-external-work-limit"
        );
    }
    deployment
        .clone()
        .with_external_work_limit(NativeBackend::DEFAULT_EXTERNAL_WORK_LIMIT)
        .unwrap();
    let limited = deployment.clone().with_external_work_limit(0).unwrap();
    for (input, proof) in [(producer, None), (validator, Some(proof))] {
        let report = limited.execute(input, proof).unwrap();
        clean(&report);
        assert_eq!(report.outcome.unwrap_err(), "exhausted:external-work-limit");
        assert_eq!(report.external_work, 0);
        assert_eq!(report.external_work_limit, 0);
    }
    let mut changed = validator.clone();
    changed[3] = json!("00");
    let report = deployment.execute(&changed, Some(proof)).unwrap();
    assert_eq!(report.outcome.unwrap_err(), "proof-header");
    // The container root is independent of external bytes. Rewrapping under
    // different ambient context succeeds because the authored program ignores it.
    let mut changed_producer = producer.clone();
    changed_producer[3] = json!("00");
    let alternate = deployment
        .execute(&changed_producer, None)
        .unwrap()
        .outcome
        .unwrap();
    assert_eq!(messages(&alternate), messages(proof));
    let mut rewrapped = proof.to_vec();
    rewrapped[8..40].copy_from_slice(&alternate[8..40]);
    deployment
        .execute(&changed, Some(&rewrapped))
        .unwrap()
        .outcome
        .unwrap();

    // Public data actually observed by source changes the challenge. Rewrapping
    // only the container cannot repair a response computed from the old context.
    let mut altered = values.to_vec();
    let port = usize::from(family == "monero");
    if let Value::Indices(xs) = &values[port] {
        // The next witness overwrites rate word zero in an imported state with
        // absorb cursor zero. Mutate a capacity word that the suffix retains.
        let mut xs = xs.to_vec();
        let at = if snapshot && family == "openvm" {
            11
        } else {
            0
        };
        xs[at] += 1;
        altered[port] = words(xs);
    }
    let new_producer = inputs(envelope, &altered, true);
    let new_validator = inputs(envelope, &altered, false);
    let new_header = deployment.execute(&new_producer, None).unwrap().binding;
    let mut rewrapped = proof.to_vec();
    let header = unhex(&new_header);
    rewrapped[8..40].copy_from_slice(&header);
    let error = deployment
        .execute(&new_validator, Some(&rewrapped))
        .unwrap()
        .outcome
        .unwrap_err();
    assert!(
        error == "artifact-rejected"
            || (family == "openvm" && error == "artifact-stopped:Explicit(\"reject\")"),
        "{family}/snapshot={snapshot}: {error}"
    );

    // A canonical frame can contain invalid primitive data. The reached kernel
    // failure wins over unconsumed later frames, with only the prefix charged.
    let (invalid_message, reason, prefix_work) = if family == "monero" {
        let Value::Indices(context) = &values[1] else {
            unreachable!()
        };
        (
            words([256; 32]),
            "refused:external-byte",
            1 + 32 + context.len() as u64,
        )
    } else {
        let Value::Indices(context) = &values[0] else {
            unreachable!()
        };
        (
            Value::Index(openvm::MODULUS.into()),
            "refused:external-noncanonical-field",
            if snapshot {
                0
            } else {
                (context.len() + context.len() / 8) as u64
            },
        )
    };
    for (payload, reason) in [
        (
            codec().encode_native_value(&invalid_message).unwrap(),
            reason,
        ),
        (vec![0], "artifact-stopped:Decode(Length)"),
    ] {
        let altered = replace(proof, 0, &payload);
        let report = deployment.execute(validator, Some(&altered)).unwrap();
        clean(&report);
        assert_eq!(report.outcome.unwrap_err(), reason);
        assert_eq!(report.messages, 1);
        assert_eq!(report.external_work, prefix_work);
    }
    if family == "openvm" {
        let (Value::Indices(context), Value::Index(difficulty)) = (&values[0], &values[1]) else {
            unreachable!()
        };
        let mut state = if snapshot {
            openvm::Duplex::from_snapshot(openvm::Snapshot {
                state: std::array::from_fn(|i| context[i + 3] as u32),
                absorb_index: context[19] as usize,
                sample_index: context[20] as usize,
            })
            .unwrap()
        } else {
            openvm::Duplex::new()
        };
        if !snapshot {
            state
                .observe(&context.iter().map(|&v| v as u32).collect::<Vec<_>>())
                .unwrap();
        }
        let witness = (0..10000)
            .find(|&w| !state.trial_witness(*difficulty as u32, w).unwrap().value)
            .unwrap();
        let payload = codec()
            .encode_native_value(&Value::Index(witness.into()))
            .unwrap();
        let report = deployment
            .execute(validator, Some(&replace(proof, 0, &payload)))
            .unwrap();
        clean(&report);
        assert_eq!(
            report.outcome.unwrap_err(),
            "artifact-stopped:Explicit(\"reject\")"
        );
        assert_eq!(report.messages, 1);
        assert_eq!(report.external_work, prefix_work + 3);
    }

    // Wire framing is valid here. Primitive input validation owns these stops.
    let invalid = if snapshot {
        vec![
            (words([1514881876, 1, 9]), "refused:external-state-width"),
            (
                words(vec![0; if family == "monero" { 35 } else { 21 }]),
                "refused:external-state-suite",
            ),
        ]
    } else if family == "monero" {
        vec![
            (words([1; 31]), "refused:external-word-width"),
            (words([1; 33]), "refused:external-word-width"),
            (words([256; 32]), "refused:external-byte"),
        ]
    } else {
        vec![
            (
                words([openvm::MODULUS as u64]),
                "refused:external-noncanonical-field",
            ),
            (
                words([1; 8].into_iter().chain([openvm::MODULUS as u64])),
                "refused:external-noncanonical-field",
            ),
        ]
    };
    for (bad, reason) in invalid {
        let mut altered = values.to_vec();
        altered[0] = bad;
        let report = deployment
            .execute(&inputs(envelope, &altered, true), None)
            .unwrap();
        clean(&report);
        assert_eq!(report.outcome.unwrap_err(), reason);
        assert_eq!(report.external_work, 0);
    }
    let mismatch = {
        let mut input = producer.clone();
        input[2][0][1][1] = json!(hex(&codec().encode_native_value(&words([])).unwrap()));
        input
    };
    assert_eq!(
        deployment.execute(&mismatch, None).err().unwrap(),
        "native-proof-shared-public-input"
    );
}
