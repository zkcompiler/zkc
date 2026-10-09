//! Compiler-authored sequences through independent proof production and validation.
#[path = "support/native_transcript.rs"]
#[allow(dead_code)]
mod reference;
use serde_json::{Value as Json, json};
use sha2::{Digest, Sha256};
use std::{path::Path, sync::Arc};
use zkc_arkworks::Keys;
use zkc_backends::{Domain, EntryPolicy, NativeBackend, Policy, Scalar, Sequence, Value};
use zkc_runtime::interactive::LogicalType;
use zkc_test_support::hex;
use zkc_tools::proof::NativeDeployment;

fn authority(keys: &Keys) -> zkc_tools::proof::SetupAuthority {
    zkc_tools::proof::SetupAuthority {
        keys: std::collections::BTreeMap::from([(2, keys.verifier_key().metadata().key_id())]),
        inputs: std::collections::BTreeMap::from([(1, 2), (3, 2)]),
    }
}
fn backend(keys: &Keys) -> NativeBackend {
    NativeBackend::new(
        Policy::default(),
        EntryPolicy::new(Domain::new("P", "nested", "main", None), None),
        zkc_backends::SetupRegistry::new(
            vec![keys.verifier_key().clone()],
            &zkc_backends::Policy::default(),
        )
        .unwrap(),
    )
    .unwrap()
}
fn seq(element: &str, values: Vec<Value>) -> Value {
    Value::Sequence(
        Sequence::new(
            LogicalType::parse(element).unwrap(),
            values,
            &Policy::default(),
        )
        .unwrap(),
    )
}
fn vectors(lengths: &[usize]) -> Value {
    seq(
        "vector:bls12-381.fr",
        lengths
            .iter()
            .map(|n| Value::Vector(vec![Scalar::from(1); *n].into()))
            .collect(),
    )
}
fn data(family: &str, count: usize, keys: &Keys) -> Vec<Option<Value>> {
    if family == "matrix" {
        vec![
            Some(Value::matrix(count, count + 1, &[], &Policy::default()).unwrap()),
            Some(Value::Index(count as u64)),
            Some(Value::Index(count as u64 + 1)),
        ]
    } else if family == "batched-openings" {
        let table = zkc_arkworks::Table::from_logical_vec(
            vec![Scalar::from(3), Scalar::from(11)],
            &Policy::default().ark_bounds(),
        )
        .unwrap();
        let state = keys.prover_key().commit(&table).unwrap();
        vec![
            Some(Value::table(&[Scalar::from(3), Scalar::from(11)], &Policy::default()).unwrap()),
            None,
            None,
            Some(Value::Commitment(Arc::new(state.commitment().clone()))),
            Some(Value::Vector(
                (0..count)
                    .map(|i| Scalar::from((i + 2) as u64))
                    .collect::<Vec<_>>()
                    .into(),
            )),
        ]
    } else {
        let shapes: Vec<_> = (0..count).map(|i| ((i * 3) % 5, (i + 2) % 5)).collect();
        let mut sum = Scalar::from(0);
        let matrices = shapes
            .iter()
            .enumerate()
            .map(|(i, &(r, c))| {
                let entries = if r == 0 || c == 0 {
                    vec![]
                } else {
                    let x = Scalar::from((i + 1) as u64);
                    sum += x;
                    vec![((r - 1) as u32, (c - 1) as u32, x)]
                };
                Value::matrix(r, c, &entries, &Policy::default()).unwrap()
            })
            .collect();
        vec![
            Some(seq("matrix:bls12-381.fr", matrices)),
            Some(vectors(&shapes.iter().map(|s| s.0).collect::<Vec<_>>())),
            Some(vectors(&shapes.iter().map(|s| s.1).collect::<Vec<_>>())),
            Some(Value::Field(sum)),
        ]
    }
}
fn inputs(
    envelope: &Json,
    values: &[Option<Value>],
    keys: &Keys,
    path: &Path,
    producing: bool,
) -> Json {
    let codec = backend(keys);
    let wire = |i: usize| {
        if let Some(v) = &values[i] {
            hex(&codec.encode_native_value(v).unwrap())
        } else {
            hex(&keys
                .verifier_key()
                .to_bytes(&Policy::default().ark_bounds())
                .unwrap())
        }
    };
    let public: Vec<_> = envelope[2][4]
        .as_array()
        .unwrap()
        .iter()
        .map(|p| json!([p[0], p[1], wire(p[1].as_str().unwrap().parse().unwrap())]))
        .collect();
    let role = if producing { "P" } else { "V" };
    let mapping = envelope[6]
        .as_array()
        .unwrap()
        .iter()
        .find(|r| r[0] == role)
        .unwrap();
    let ports: Vec<_> = mapping[2]
        .as_array()
        .unwrap()
        .iter()
        .map(|p| {
            let spec = if p[1].as_str().unwrap().starts_with("prover_key:") {
                json!([
                    "prover_key_file",
                    [
                        path.to_str().unwrap(),
                        hex(&keys.prover_key().material_fingerprint())
                    ]
                ])
            } else if p[1].as_str().unwrap().starts_with("verifier_key:") {
                json!(["verifier_key", p[0]])
            } else {
                json!(["wire", wire(p[0].as_str().unwrap().parse().unwrap())])
            };
            json!([p[0], spec])
        })
        .collect();
    let services: Vec<_> = mapping[4]
        .as_array()
        .unwrap()
        .iter()
        .map(|p| json!([p[0], "1"]))
        .collect();
    json!([
        "zkc.native-proof-inputs/0",
        public,
        ports,
        "",
        services,
        if envelope[2][1][5] == "" {
            "0".to_string()
        } else {
            envelope[2][3].as_array().unwrap().len().to_string()
        }
    ])
}
fn execute(
    deployment: &NativeDeployment,
    inputs: &Json,
    proof: Option<&[u8]>,
) -> Result<Vec<u8>, String> {
    checked(deployment, inputs, proof)?.outcome
}
/// Execute once and check that cleanup and service custody completed.
fn checked(
    deployment: &NativeDeployment,
    inputs: &Json,
    proof: Option<&[u8]>,
) -> Result<zkc_tools::proof::NativeProofReport, String> {
    let report = zkc_test_drivers::execute(
        deployment,
        inputs,
        zkc_tools::proof::Invocation::one_shot(proof),
    )?;
    if report.outcome.is_ok() {
        assert!(!report.cancelled);
    }
    assert!(!report.outcome.as_ref().err().is_some_and(
        |e| e.starts_with("native-proof-cleanup") || e == "native-proof-active-frames"
    ));
    assert!(
        report
            .resources
            .iter()
            .all(|r| r["kind"] != "service" || r["leased"] == false)
    );
    Ok(report)
}
fn replaced(proof: &[u8], payload: &[u8]) -> Vec<u8> {
    assert_eq!(&proof[..8], b"ZKCPRF00");
    let mut result = proof[..40].to_vec();
    result.extend_from_slice(&(payload.len() as u64).to_le_bytes());
    result.extend_from_slice(payload);
    let old = u64::from_le_bytes(proof[40..48].try_into().unwrap()) as usize;
    result.extend_from_slice(&proof[48 + old..]);
    result
}
fn main() {
    let directory = std::env::args().nth(1).expect("generated directory");
    let directory = Path::new(&directory);
    let keys = Keys::setup_for_development(1, &Policy::default().ark_bounds()).unwrap();
    std::fs::write(
        directory.join("nested.setups.json"),
        serde_json::to_vec(&json!([
            "zkc.native-setup-authority/0",
            [["2", hex(&keys.verifier_key().metadata().key_id())]],
            [["1", "2"], ["3", "2"]]
        ]))
        .unwrap(),
    )
    .unwrap();
    checked_indexing(directory, &keys);
    let path = directory.join("nested.pk");
    std::fs::write(
        &path,
        keys.prover_key()
            .to_bytes(&Policy::default().ark_bounds())
            .unwrap(),
    )
    .unwrap();
    let manifest: Json =
        serde_json::from_slice(&std::fs::read(directory.join("manifest.json")).unwrap()).unwrap();
    let mut capacity_checked = false;
    for case in manifest.as_array().unwrap() {
        let name = case["name"].as_str().unwrap();
        let family = case["family"].as_str().unwrap();
        let bytes = std::fs::read(directory.join(format!("{name}.deployment"))).unwrap();
        let envelope: Json = serde_json::from_slice(&bytes).unwrap();
        let hash: [u8; 32] = Sha256::digest(&bytes).into();
        let deployment = if family == "batched-openings" {
            assert_eq!(
                NativeDeployment::admit(&bytes, &hash, Default::default())
                    .err()
                    .as_deref(),
                Some("native-proof-key-authority")
            );
            NativeDeployment::admit(&bytes, &hash, authority(&keys))
        } else {
            NativeDeployment::admit(&bytes, &hash, Default::default())
        }
        .unwrap();
        for count in [0, 1, 3, 8, 17] {
            let mut values = data(family, count, &keys);
            if family == "observed" {
                values.truncate(1);
                values.push(None);
            }
            let p = inputs(&envelope, &values, &keys, &path, true);
            let v = inputs(&envelope, &values, &keys, &path, false);
            let proof =
                execute(&deployment, &p, None).unwrap_or_else(|e| panic!("{name}/{count}: {e}"));
            execute(&deployment, &v, Some(&proof))
                .unwrap_or_else(|e| panic!("validate {name}/{count}: {e}"));
            let frame_length = u64::from_le_bytes(proof[40..48].try_into().unwrap()) as usize;
            if family == "observed" {
                let root = reference::root(&envelope, &p);
                assert_eq!(&proof[8..40], &Sha256::digest(&root)[..]);
                let mut t = reference::Transcript::new(envelope[2][1][5].as_str().unwrap(), &root);
                let origin = |event: Json| {
                    reference::tree(&json!(["zkc.native-origin/0", "main", [], [], event]))
                };
                t.absorb(
                    b"origin",
                    &origin(json!(["message", "main", "data", "data", "P", "V"])),
                );
                t.absorb(b"value", &proof[48..48 + frame_length]);
                t.absorb(
                    b"origin",
                    &origin(json!([
                        "query",
                        "main",
                        "draw",
                        "input_1",
                        "random.bls12-381.fr/0",
                        "draw",
                        "V"
                    ])),
                );
                let challenge = t.draw();
                let tail = &proof[48 + frame_length..];
                assert_eq!(&tail[..8], &38u64.to_le_bytes());
                assert_eq!(&tail[8..], reference::scalar_wire(challenge));
            } else {
                assert_eq!(frame_length, proof.len() - 48);
            }
            if family == "matrix" {
                assert_eq!(&proof[48..54], b"ZKCV\x00\x17");
                let mut wrong = proof[48..].to_vec();
                wrong[6..10].copy_from_slice(&((count + 1) as u32).to_le_bytes());
                assert_eq!(
                    execute(&deployment, &v, Some(&replaced(&proof, &wrong))).unwrap_err(),
                    "artifact-rejected"
                );
                publish(directory, name, count, &p, &v, &proof);
                continue;
            }
            assert_eq!(&proof[48..54], b"ZKCV\x00\x45");
            assert_eq!(
                u32::from_le_bytes(proof[54..58].try_into().unwrap()) as usize,
                count
            );
            // Independently frame the batch's child slices. This does not use the native decoder.
            let mut pos = 58;
            let mut children = Vec::new();
            for _ in 0..count {
                let n = u32::from_le_bytes(proof[pos..pos + 4].try_into().unwrap()) as usize;
                children.push(proof[pos..pos + 4 + n].to_vec());
                pos += 4 + n;
            }
            assert_eq!(pos, 48 + frame_length);
            let batch = |items: &[Vec<u8>]| {
                let mut b = b"ZKCV\x00\x45".to_vec();
                b.extend_from_slice(&(items.len() as u32).to_le_bytes());
                for item in items {
                    b.extend_from_slice(item);
                }
                b
            };
            if count > 0 {
                for payload in [batch(&[]), batch(&children[..count - 1])] {
                    assert_eq!(
                        execute(&deployment, &v, Some(&replaced(&proof, &payload))).unwrap_err(),
                        "artifact-rejected",
                        "missing item {name}/{count}"
                    );
                }
                let mut bad = proof[48..48 + frame_length].to_vec();
                bad[6..10].fill(255);
                assert_eq!(
                    execute(&deployment, &v, Some(&replaced(&proof, &bad))).unwrap_err(),
                    "native-wire-limit"
                );
                if family == "batched-openings" && count > 1 {
                    let mut changed = children.clone();
                    changed.swap(0, 1);
                    assert_eq!(
                        execute(&deployment, &v, Some(&replaced(&proof, &batch(&changed))))
                            .unwrap_err(),
                        "artifact-rejected",
                        "reordering must use verifier points"
                    );
                    changed[0] = changed[1].clone();
                    assert_eq!(
                        execute(&deployment, &v, Some(&replaced(&proof, &batch(&changed))))
                            .unwrap_err(),
                        "artifact-rejected",
                        "duplicate proof"
                    );
                }
                if family == "ragged-matrices" {
                    let mut changed = children.clone();
                    // First trace has shape 0 x 2. Change only its empty shape.
                    changed[0][14..18].copy_from_slice(&3u32.to_le_bytes());
                    assert_eq!(
                        execute(&deployment, &v, Some(&replaced(&proof, &batch(&changed))))
                            .unwrap_err(),
                        "refused:matrix-shape",
                        "shape is part of the value"
                    );
                }
            }
            for end in [0, 8, 39, proof.len() - 1] {
                assert_eq!(
                    execute(&deployment, &v, Some(&proof[..end])).unwrap_err(),
                    "proof-truncated"
                );
            }
            let mut extra = proof.clone();
            extra.push(0);
            assert_eq!(
                execute(&deployment, &v, Some(&extra)).unwrap_err(),
                "proof-trailing"
            );
            publish(directory, name, count, &p, &v, &proof);
        }
        if family == "batched-openings" && !capacity_checked {
            capacity_checked = true;
            // The carried batch, opening state and points are charged once however
            // many iterations borrow them, so 256 openings complete. Each append
            // still allocates a new element slice; that quadratic fresh allocation
            // reaches the cumulative ceiling before 1,024 openings, ahead of
            // sequence and logical work. Check the actual composed host boundary.
            for count in [256, 1024] {
                let values = data(family, count, &keys);
                let p = inputs(&envelope, &values, &keys, &path, true);
                let v = inputs(&envelope, &values, &keys, &path, false);
                let report = checked(&deployment, &p, None).unwrap();
                if count == 256 {
                    let proof = report.outcome.unwrap();
                    execute(&deployment, &v, Some(&proof)).unwrap();
                } else {
                    assert_eq!(report.outcome.unwrap_err(), "exhausted:output-bytes");
                    let ceiling = zkc_runtime::interactive::Limits::TOTAL_VALUE_BYTES;
                    assert!(report.usage.total_value_bytes > ceiling - (8 << 20));
                    assert!(
                        report.usage.logical_bytes
                            < zkc_runtime::interactive::Limits::LOGICAL_BYTES
                    );
                }
            }
        }
        println!(
            "{name}: runtime counts 0/1/3/8/17, independent participants, mutations and cleanup passed"
        );
    }
    assert!(
        capacity_checked,
        "opening-record capacity control must execute"
    );
}

fn checked_indexing(directory: &Path, keys: &Keys) {
    use zkc_tools::run::*;
    for suffix in ["", "_plain", "_release"] {
        let bytes = std::fs::read(directory.join(format!("checked{suffix}.bundle"))).unwrap();
        let bundle = Bundle::admit(&bytes, &backend(keys), BundleLimits::default()).unwrap();
        for index in [0, 1, u64::MAX] {
            let report = run(
                &bundle,
                "nested",
                vec![RoleInput {
                    role: "P".into(),
                    backend: backend(keys),
                    values: vec![Value::Index(index)],
                }],
                RunLimits::default(),
                &mut NoHooks,
            )
            .unwrap();
            if index == 0 {
                assert_eq!(report.outcome, Outcome::Completed);
                assert!(matches!(
                    report.roles[0].outputs.as_slice(),
                    [Value::Index(1), Value::Index(0)]
                ));
            } else {
                assert_eq!(report.outcome, Outcome::ParticipantStopped { role: 0 });
                let State::Stopped(stop) = &report.roles[0].before else {
                    panic!("expected indexing stop: {:?}", report.roles[0]);
                };
                assert!(matches!(&stop.cause, StopCause::Backend(error)
                    if error.text == "refused:sequence-index" && error.omitted_bytes == 0));
                assert!(stop.cleanup_errors.is_empty());
            }
        }
    }
}

fn publish(directory: &Path, name: &str, count: usize, p: &Json, v: &Json, proof: &[u8]) {
    if count != 3 {
        return;
    }
    for (suffix, input) in [("producer", p), ("validator", v)] {
        std::fs::write(
            directory.join(format!("{name}.{suffix}.json")),
            serde_json::to_vec(input).unwrap(),
        )
        .unwrap();
    }
    std::fs::write(directory.join(format!("{name}.proof")), proof).unwrap();
}
