//! Authored external state through the general compiler, proof host and attempts.
use serde_json::{Value as Json, json};
use sha2::{Digest, Sha256};
use std::path::Path;
use zkc_backends::{Domain, EntryPolicy, NativeBackend, Policy, Value};
use zkc_runtime::{
    attempt::Limits,
    interactive::{ValueBudget, WorkBudget},
};
use zkc_tools::proof::{AttemptPolicy, NativeDeployment, NativeProofReport, hex};

mod controls;
mod reference;

fn codec() -> NativeBackend {
    NativeBackend::new(
        Policy::default(),
        EntryPolicy::new(Domain::new("P", "authored", "main", None), None),
        Default::default(),
    )
    .unwrap()
}
fn words(xs: impl IntoIterator<Item = u64>) -> Value {
    Value::Indices(xs.into_iter().collect::<Vec<_>>().into())
}
fn unhex(value: &str) -> Vec<u8> {
    let (pairs, remainder) = value.as_bytes().as_chunks::<2>();
    assert!(remainder.is_empty());
    pairs
        .iter()
        .map(|pair| u8::from_str_radix(std::str::from_utf8(pair).unwrap(), 16).unwrap())
        .collect()
}
fn inputs(envelope: &Json, values: &[Value], producing: bool) -> Json {
    let codec = codec();
    let wire = |i: usize| hex(&codec.encode_native_value(&values[i]).unwrap());
    let public: Vec<_> = envelope[2][4]
        .as_array()
        .unwrap()
        .iter()
        .map(|p| json!([p[0], p[1], wire(p[1].as_str().unwrap().parse().unwrap())]))
        .collect();
    let role = if producing { "P" } else { "V" };
    let map = envelope[6]
        .as_array()
        .unwrap()
        .iter()
        .find(|r| r[0] == role)
        .unwrap();
    let ports: Vec<_> = map[2]
        .as_array()
        .unwrap()
        .iter()
        .map(|p| {
            if p[1] == "rng:bls12-381.fr" {
                json!([p[0], ["rng", "10"]])
            } else {
                json!([
                    p[0],
                    ["wire", wire(p[0].as_str().unwrap().parse().unwrap())]
                ])
            }
        })
        .collect();
    json!([
        "zkc.native-proof-inputs/0",
        public,
        ports,
        "617574686f726564",
        [],
        "0"
    ])
}
fn messages(proof: &[u8]) -> Vec<&[u8]> {
    assert_eq!(&proof[..8], b"ZKCPRF00");
    let mut rest = &proof[40..];
    let mut result = Vec::new();
    while !rest.is_empty() {
        let n = u64::from_le_bytes(rest[..8].try_into().unwrap()) as usize;
        result.push(&rest[8..8 + n]);
        rest = &rest[8 + n..];
    }
    result
}
fn replace(proof: &[u8], index: usize, payload: &[u8]) -> Vec<u8> {
    let mut result = proof[..40].to_vec();
    for (i, old) in messages(proof).into_iter().enumerate() {
        let p = if i == index { payload } else { old };
        result.extend_from_slice(&(p.len() as u64).to_le_bytes());
        result.extend_from_slice(p);
    }
    result
}
fn clean(report: &NativeProofReport) {
    assert!(
        report.cleanup_errors.is_empty(),
        "{:?}",
        report.cleanup_errors
    );
    assert!(report.resources.is_empty());
}
fn policy() -> AttemptPolicy {
    AttemptPolicy {
        completion: 1,
        rng: vec![],
        limits: Limits {
            attempts: 3,
            proof_bytes: 1 << 20,
        },
        work: WorkBudget::default(),
        values: ValueBudget::default(),
    }
}
fn main() {
    let directory = std::env::args().nth(1).expect("generated directory");
    let directory = Path::new(&directory);
    let manifest: Json =
        serde_json::from_slice(&std::fs::read(directory.join("manifest.json")).unwrap()).unwrap();
    let codec = codec();
    let mut runs = 0;
    for case in manifest.as_array().unwrap() {
        let name = case["name"].as_str().unwrap();
        let family = case["family"].as_str().unwrap();
        let snapshot = case["snapshot"] == true;
        let bytes = std::fs::read(directory.join(format!("{name}.deployment"))).unwrap();
        let deployment =
            NativeDeployment::admit(&bytes, &Sha256::digest(&bytes).into(), Default::default())
                .unwrap();
        let envelope: Json = serde_json::from_slice(&bytes).unwrap();
        if family == "prefix" {
            controls::prefix_controls(directory, name, &deployment, &envelope);
            continue;
        }
        if !snapshot {
            reference::archived_answers(&deployment, &envelope, family);
        }
        for count in [0, 1, 7, 8, 9, 16, 64] {
            let (values, expected, producer_work, validator_work) = if family == "monero" {
                let (values, expected, work) = reference::monero_data(count, snapshot);
                (values, expected, work, work)
            } else {
                reference::openvm_data(
                    count,
                    snapshot,
                    case["duplicate"] == true,
                    if count == 0 { 0 } else { 4 },
                    (count % 31) as u32,
                )
            };
            let producer = inputs(&envelope, &values, true);
            let validator = inputs(&envelope, &values, false);
            let produced = deployment.execute(&producer, None).unwrap();
            clean(&produced);
            let proof = produced.outcome.as_ref().unwrap();
            assert_eq!(produced.external_work, producer_work, "{name}/{count}");
            let expected: Vec<_> = expected
                .iter()
                .map(|v| codec.encode_native_value(v).unwrap())
                .collect();
            assert_eq!(messages(proof), expected, "{name}/{count}");
            let verified = deployment.execute(&validator, Some(proof)).unwrap();
            clean(&verified);
            verified.outcome.unwrap();
            assert_eq!(verified.external_work, validator_work, "{name}/{count}");
            // Literal totals pin the metric independently of adapter helpers.
            if count == 0 {
                assert_eq!(
                    verified.external_work,
                    if family == "monero" { 130 } else { 7 }
                );
            } else if count == 8 {
                assert_eq!(
                    verified.external_work,
                    if family == "monero" {
                        618
                    } else if snapshot {
                        9
                    } else {
                        18
                    }
                );
            }
            if case["early"] == true && count == 0 {
                let mut bounded = policy();
                bounded.work.iterations = 1;
                let short = deployment.execute_attempts(&producer, &bounded).unwrap();
                assert_eq!(short.outcome.unwrap(), *proof);
                assert_eq!(short.usage.iterations, 1);
            }
            let attempted = deployment.execute_attempts(&producer, &policy()).unwrap();
            clean(&attempted);
            assert_eq!(attempted.outcome.unwrap(), *proof);
            assert_eq!(attempted.external_work, producer_work);
            assert_eq!(attempted.attempts[0].external_work, producer_work);
            let changed = replace(
                proof,
                expected.len() - 1,
                &codec
                    .encode_native_value(&if family == "monero" {
                        words([0; 32])
                    } else {
                        Value::Index(u64::MAX)
                    })
                    .unwrap(),
            );
            assert_eq!(
                deployment
                    .execute(&validator, Some(&changed))
                    .unwrap()
                    .outcome
                    .unwrap_err(),
                "artifact-rejected"
            );
            let mut trailing = proof.clone();
            trailing.push(0);
            assert_eq!(
                deployment
                    .execute(&validator, Some(&trailing))
                    .unwrap()
                    .outcome
                    .unwrap_err(),
                "proof-trailing"
            );
            if count == 8 {
                for (suffix, value) in
                    [("producer.json", &producer), ("validator.json", &validator)]
                {
                    std::fs::write(
                        directory.join(format!("{name}.{suffix}")),
                        serde_json::to_vec(value).unwrap(),
                    )
                    .unwrap();
                }
                std::fs::write(directory.join(format!("{name}.proof")), proof).unwrap();
                if family == "monero" {
                    let mut retry = values.clone();
                    retry[4] = Value::Bool(false);
                    let report = deployment
                        .execute_attempts(&inputs(&envelope, &retry, true), &policy())
                        .unwrap();
                    clean(&report);
                    assert_eq!(report.outcome.unwrap_err(), "native-attempt-limit");
                    assert_eq!(report.attempts.len(), 3);
                    assert_eq!(report.external_work, producer_work * 3);
                    assert!(
                        report
                            .attempts
                            .iter()
                            .all(|r| r.external_work == producer_work && r.decision == Ok(false))
                    );
                    let limited = deployment
                        .clone()
                        .with_external_work_limit(producer_work * 2)
                        .unwrap();
                    let stopped = limited
                        .execute_attempts(&inputs(&envelope, &retry, true), &policy())
                        .unwrap();
                    clean(&stopped);
                    assert_eq!(
                        stopped.outcome.unwrap_err(),
                        "exhausted:external-work-limit"
                    );
                    assert_eq!(stopped.external_work, producer_work * 2);
                    assert_eq!(stopped.attempts.len(), 3);
                    assert_eq!(stopped.attempts[2].external_work, 0);
                    assert_eq!(
                        stopped.attempts[2].decision.as_ref().unwrap_err(),
                        "exhausted:external-work-limit"
                    );
                    assert_eq!(stopped.attempts[2].messages, 0);
                }
                controls::controls(&deployment, &envelope, &values, proof, family, snapshot);
            }
            runs += 1;
        }
    }
    println!("{runs} authored transcript executions with exact payload and work checks");
}
