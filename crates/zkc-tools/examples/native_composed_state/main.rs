//! Executable compositions of changing shapes, proof messages and attempt state.
mod joint;
mod reference;
use serde_json::{Value as Json, json};
use sha2::{Digest, Sha256};
use std::{collections::BTreeMap, path::Path};
use zkc_backends::{Domain, EntryPolicy, GroupPoint, NativeBackend, Policy, Scalar, Value};
use zkc_runtime::{
    attempt::Limits,
    interactive::{ValueBudget, WorkBudget},
};
use zkc_tools::proof::{AttemptPolicy, NativeDeployment, NativeProofReport, hex};

fn data(len: usize) -> (Vec<Scalar>, Vec<GroupPoint>) {
    (
        (0..len).map(|i| Scalar::from(i as u64 + 2)).collect(),
        (0..len)
            .map(|i| GroupPoint::generator().scale(Scalar::from((i as u64 + 2).pow(2) + 1)))
            .collect(),
    )
}
fn inputs(envelope: &Json, producing: bool, n: u64, a: &[Scalar], g: &[GroupPoint]) -> Json {
    let codec = NativeBackend::new(
        Policy::default(),
        EntryPolicy::new(Domain::new("P", "test", "composed", None), None),
        Default::default(),
    )
    .unwrap();
    // The batch consumes a prefix; unused witness/base suffixes are legal.
    // Invalid-count controls claim the available prefix, then fail at the
    // reached loop bound/index rather than during test input construction.
    let statement_len = if envelope[2][1][1] == "batch" {
        (n as usize).min(a.len()).min(g.len())
    } else {
        a.len()
    };
    let value = |port: &Json| {
        let value = match port.as_str().unwrap() {
            "0" => Value::Index(n),
            "1" => Value::Groups(g.to_vec().into()),
            "2" => Value::Curve(reference::msm(&a[..statement_len], &g[..statement_len])),
            "3" => Value::Vector(a.to_vec().into()),
            p => panic!("unexpected input {p}"),
        };
        hex(&codec.encode_native_value(&value).unwrap())
    };
    let role = if producing { "P" } else { "V" };
    let map = envelope[6]
        .as_array()
        .unwrap()
        .iter()
        .find(|r| r[0] == role)
        .unwrap();
    let public: Vec<_> = envelope[2][4]
        .as_array()
        .unwrap()
        .iter()
        .map(|p| json!([p[0], p[1], value(&p[1])]))
        .collect();
    let data: Vec<_> = map[2]
        .as_array()
        .unwrap()
        .iter()
        .map(|p| {
            json!([
                p[0],
                if p[0] == "4" {
                    json!(["rng", "256"])
                } else {
                    json!(["wire", value(&p[0])])
                }
            ])
        })
        .collect();
    let services: Vec<_> = map[4]
        .as_array()
        .unwrap()
        .iter()
        .map(|p| json!([p[0], "64"]))
        .collect();
    json!([
        "zkc.native-proof-inputs/0",
        public,
        data,
        "",
        services,
        "256"
    ])
}
fn policy() -> AttemptPolicy {
    AttemptPolicy {
        completion: 1,
        rng: vec![(4, 2)],
        limits: Limits {
            attempts: 4,
            proof_bytes: 16 * 1024 * 1024,
        },
        work: WorkBudget::default(),
        values: ValueBudget::default(),
    }
}
fn tape(salts: &[u64], rounds: u64) -> BTreeMap<usize, Vec<Scalar>> {
    BTreeMap::from([(
        4,
        salts
            .iter()
            .flat_map(|salt| {
                std::iter::once(Scalar::from(*salt)).chain((0..rounds).map(|i| Scalar::from(7 + i)))
            })
            .collect(),
    )])
}
fn clean(r: &NativeProofReport) {
    assert!(r.cleanup_errors.is_empty(), "{:?}", r.cleanup_errors);
    assert!(!r.outcome.as_ref().err().is_some_and(
        |e| e.starts_with("native-proof-cleanup") || e == "native-proof-active-frames"
    ));
}
fn rejected(d: &NativeDeployment, input: &Json, proof: &[u8]) -> String {
    let report = d.execute(input, Some(proof)).unwrap();
    clean(&report);
    report.outcome.expect_err("altered proof accepted")
}
fn run(directory: &Path, case: &Json) {
    let name = case["name"].as_str().unwrap();
    let fold = case["family"] == "fold";
    let bytes = std::fs::read(directory.join(format!("{name}.deployment"))).unwrap();
    let envelope: Json = serde_json::from_slice(&bytes).unwrap();
    let d = NativeDeployment::admit(&bytes, &Sha256::digest(&bytes).into(), Default::default())
        .unwrap();
    for (n, coefficients, bases) in if fold {
        vec![
            (0, 0, 0),
            (0, 1, 1),
            (1, 2, 2),
            (2, 8, 8),
            (4, 16, 16),
            (8, 256, 256),
        ]
    } else {
        vec![
            (0, 0, 0),
            (0, 3, 2),
            (1, 1, 1),
            (1, 4, 3),
            (1, 3, 4),
            (2, 2, 2),
            (7, 7, 7),
            (32, 32, 32),
        ]
    } {
        // Capacity is checked once; the smaller cases compare all execution modes.
        if n == (if fold { 8 } else { 32 }) && !(case["mode"] == "normal" && case["suite"] == 0) {
            continue;
        }
        let (mut a, mut g) = data(coefficients.max(bases));
        a.truncate(coefficients);
        g.truncate(bases);
        let p = inputs(&envelope, true, n, &a, &g);
        let v = inputs(&envelope, false, n, &a, &g);
        let report = d
            .execute_attempts_test(&p, &policy(), tape(&[0, 3], n))
            .unwrap();
        clean(&report);
        let proof = report
            .outcome
            .as_ref()
            .unwrap_or_else(|e| panic!("{name}/{n}/{coefficients}/{bases}: {e}"));
        assert_eq!(report.attempts.len(), 2);
        assert_eq!(report.attempts[0].decision, Ok(false));
        assert_eq!(report.attempts[1].decision, Ok(true));
        assert_eq!(report.resources.len(), 1);
        assert_eq!(report.resources[0]["transitions"], 2 * (n + 1));
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
        assert_eq!(
            *proof,
            reference::proof(&envelope, &p, n, &a, &g, Scalar::from(3)),
            "{name}/{n}"
        );
        let validator = d.execute(&v, Some(proof)).unwrap();
        clean(&validator);
        assert!(validator.outcome.is_ok(), "{name}: {:?}", validator.outcome);
        let first = d
            .execute_attempts_test(&p, &policy(), tape(&[3], n))
            .unwrap();
        clean(&first);
        assert_eq!(first.outcome.as_ref().unwrap(), proof);
        if n == 2 {
            // Saved inputs let pytest exercise separate producer and validator processes.
            std::fs::write(
                directory.join(format!("{name}.producer.json")),
                serde_json::to_vec(&p).unwrap(),
            )
            .unwrap();
            std::fs::write(
                directory.join(format!("{name}.validator.json")),
                serde_json::to_vec(&v).unwrap(),
            )
            .unwrap();
            let baseline = format!(
                "{}_{}_normal.reference.proof",
                case["family"].as_str().unwrap(),
                case["suite"].as_u64().unwrap()
            );
            if case["mode"] == "normal" {
                std::fs::write(directory.join(baseline), proof).unwrap();
            } else {
                assert_eq!(
                    std::fs::read(directory.join(baseline)).unwrap(),
                    *proof,
                    "optimization changed proof bytes: {name}"
                );
            }
            adversarial(&d, &p, &v, proof, &report, fold, n);
        }
    }
    // Bounds and partial shape failures remain fatal, never retry requests.
    for (n, len) in if fold {
        vec![(1, 0), (1, 3), (2, 2), (9, 2)]
    } else {
        vec![(2, 1), (33, 1)]
    } {
        let (a, g) = data(len);
        let p = inputs(&envelope, true, n, &a, &g);
        let r = d
            .execute_attempts_test(&p, &policy(), tape(&[3], n))
            .unwrap();
        clean(&r);
        assert!(r.outcome.is_err(), "{name}: shape {n}/{len} accepted");
        assert_eq!(r.attempts.len(), 1);
        assert!(r.attempts[0].decision.is_err());
        assert_eq!(
            r.resources[0]["transitions"],
            if n == 2 && len > 0 { 2 } else { 1 }
        );
    }
}
fn adversarial(
    d: &NativeDeployment,
    p: &Json,
    v: &Json,
    proof: &[u8],
    successful: &NativeProofReport,
    fold: bool,
    n: u64,
) {
    let exhausted = d
        .execute_attempts_test(p, &policy(), tape(&[0, 0, 0, 0], n))
        .unwrap();
    clean(&exhausted);
    assert_eq!(exhausted.outcome.unwrap_err(), "native-attempt-limit");
    assert_eq!(exhausted.resources[0]["transitions"], 4 * (n + 1));
    for kind in ["instructions", "iterations", "values", "proof"] {
        let mut limited = policy();
        match kind {
            "instructions" => {
                limited.work.instructions = successful.attempts[0].usage.instructions + 1
            }
            "iterations" => limited.work.iterations = successful.attempts[0].usage.iterations,
            "values" => limited.values.total_bytes = successful.attempts[0].usage.total_value_bytes,
            "proof" => limited.limits.proof_bytes = successful.attempts[0].bytes - 1,
            _ => unreachable!(),
        }
        let r = d
            .execute_attempts_test(p, &limited, tape(&[0, 3], n))
            .unwrap();
        clean(&r);
        assert!(r.outcome.is_err(), "{kind}");
        assert_eq!(
            r.attempts.len(),
            if kind == "proof" { 1 } else { 2 },
            "{kind}"
        );
        assert!(r.attempts.last().unwrap().decision.is_err());
    }
    // Keep the public statement fixed while changing the private witness.
    // Producer completion alone must not imply validator acceptance.
    let mut dishonest = p.clone();
    let witness = dishonest[2]
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|row| row[0] == "3")
        .unwrap();
    let wire = witness[1][1].as_str().unwrap().to_owned();
    // Preserve the ten-byte typed vector header, set every coefficient to zero.
    witness[1][1] = json!(format!("{}{}", &wire[..20], "0".repeat(wire.len() - 20)));
    let wrong = d
        .execute_attempts_test(&dishonest, &policy(), tape(&[3], n))
        .unwrap();
    clean(&wrong);
    assert_eq!(
        rejected(d, v, wrong.outcome.as_ref().unwrap()),
        "artifact-rejected"
    );
    let mut context = v.clone();
    context[3] = json!("01");
    rejected(d, &context, proof);
    let mut trailing = proof.to_vec();
    trailing.push(0);
    rejected(d, v, &trailing);
    rejected(d, v, &proof[..proof.len() - 1]);
    let mut position = 40;
    let mut frames = Vec::new();
    while position < proof.len() {
        let length = u64::from_le_bytes(proof[position..position + 8].try_into().unwrap()) as usize;
        frames.push((position, length));
        position += 8 + length;
    }
    for (offset, length) in &frames {
        let mut changed = proof.to_vec();
        changed[offset + 8 + length - 1] ^= 1;
        rejected(d, v, &changed);
    }
    // Shorten the first received group vector canonically, so rejection must
    // come from the authored length check, not only from byte decoding.
    let (offset, length) = frames[if fold { 4 } else { 3 }];
    let mut shorter = proof.to_vec();
    let count = u32::from_le_bytes(shorter[offset + 14..offset + 18].try_into().unwrap());
    assert!(count > 0);
    shorter[offset..offset + 8].copy_from_slice(&((length - 48) as u64).to_le_bytes());
    shorter[offset + 14..offset + 18].copy_from_slice(&(count - 1).to_le_bytes());
    shorter.drain(offset + 8 + length - 48..offset + 8 + length);
    let r = d.execute(v, Some(&shorter)).unwrap();
    clean(&r);
    assert_eq!(
        r.outcome.unwrap_err(),
        "artifact-stopped:Explicit(\"reject\")",
        "shortened received groups must reach the authored guard"
    );
    // A canonical but altered terminal scalar reaches the mathematical check.
    let (offset, length) = *frames.last().unwrap();
    let mut wrong = proof.to_vec();
    wrong[offset + 8 + length - 32..offset + 8 + length].copy_from_slice(&[0; 32]);
    assert_eq!(rejected(d, v, &wrong), "artifact-rejected");
}
fn main() {
    let directory = std::env::args().nth(1).expect("artifact directory");
    let directory = Path::new(&directory);
    let manifest: Json =
        serde_json::from_slice(&std::fs::read(directory.join("manifest.json")).unwrap()).unwrap();
    for case in manifest.as_array().unwrap() {
        run(directory, case);
        if case["suite"] == 0 {
            joint::run(
                directory,
                case["family"].as_str().unwrap(),
                case["mode"].as_str().unwrap(),
            );
        }
    }
    println!(
        "composed state: independent algebra/transcripts, retries, malformed receives and limits passed"
    );
}
