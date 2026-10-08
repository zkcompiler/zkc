mod mutations;
mod reference;
mod typed;
use serde_json::{Value as Json, json};
use sha2::{Digest, Sha256};
use std::{collections::BTreeMap, path::Path, sync::Arc};
use zkc_arkworks::Keys;
use zkc_backends::{Domain, EntryPolicy, NativeBackend, Policy, Scalar, Value};
use zkc_tools::proof::{NativeDeployment, hex};

fn authority(keys: &Keys, authored: bool) -> zkc_tools::proof::SetupAuthority {
    let (vk, ports) = if authored {
        (2, vec![1, 3])
    } else {
        (6, vec![5, 7, 8])
    };
    zkc_tools::proof::SetupAuthority {
        keys: BTreeMap::from([(vk, keys.verifier_key().metadata().key_id())]),
        inputs: ports.into_iter().map(|p| (p, vk)).collect(),
    }
}
fn authority_record(keys: &Keys, authored: bool) -> Json {
    let a = authority(keys, authored);
    json!([
        "zkc.native-setup-authority/1",
        a.keys
            .iter()
            .map(|(p, id)| json!([p.to_string(), hex(id)]))
            .collect::<Vec<_>>(),
        a.inputs
            .iter()
            .map(|(p, key)| json!([p.to_string(), key.to_string()]))
            .collect::<Vec<_>>()
    ])
}
fn digest(bytes: &[u8]) -> String {
    hex(&Sha256::digest(bytes))
}
fn backend(keys: &Keys) -> NativeBackend {
    NativeBackend::new(
        Policy::default(),
        EntryPolicy::new(Domain::new("P", "test", "main", None), None),
        zkc_backends::SetupRegistry::new(
            vec![keys.verifier_key().clone()],
            &zkc_backends::Policy::default(),
        )
        .unwrap(),
    )
    .unwrap()
}
fn tables(n: usize) -> (Vec<Scalar>, Vec<Scalar>) {
    (
        (0..1usize << n)
            .map(|i| Scalar::from(i as u64 + 1))
            .collect(),
        (0..1usize << n)
            .map(|i| Scalar::from(2 * i as u64 + 3))
            .collect(),
    )
}
fn inputs(envelope: &Json, family: &str, keys: &Keys, path: &Path, producing: bool) -> Json {
    let n = keys.verifier_key().metadata().arity();
    let (a, b) = tables(n);
    let policy = Policy::default();
    let table = |v: &[Scalar]| {
        zkc_arkworks::Table::from_logical_vec(v.to_vec(), &policy.ark_bounds()).unwrap()
    };
    let root_a = keys
        .prover_key()
        .commit(&table(&a))
        .unwrap()
        .commitment()
        .clone();
    let root_b = keys
        .prover_key()
        .commit(&table(&b))
        .unwrap()
        .commitment()
        .clone();
    let r = Scalar::from(7);
    let claim = if matches!(family, "authored" | "structured") {
        a[0] + r * (a[1] - a[0])
    } else {
        a.iter()
            .zip(&b)
            .map(|(x, y)| {
                if family == "cubic" {
                    *x * *x * *y
                } else {
                    *x * *y
                }
            })
            .sum()
    };
    let codec = backend(keys);
    let value = |p: usize| {
        let p = if matches!(family, "authored" | "structured") {
            match p {
                0 => 1,
                1 => 5,
                2 => 6,
                3 => 7,
                4 => 9,
                5 => 3,
                _ => panic!("port"),
            }
        } else {
            p
        };
        let v = match p {
            0 => Value::Index(n as u64),
            1 => Value::table(&a, &policy).unwrap(),
            2 => Value::table(&b, &policy).unwrap(),
            3 => Value::Field(claim),
            6 => return hex(&keys.verifier_key().to_bytes(&policy.ark_bounds()).unwrap()),
            7 => Value::Commitment(Arc::new(root_a.clone())),
            8 => Value::Commitment(Arc::new(root_b.clone())),
            9 => Value::Field(r),
            _ => panic!("port {p}"),
        };
        hex(&codec.encode_native_value(&v).unwrap())
    };
    let role = if producing { "P" } else { "V" };
    let mapping = envelope[6]
        .as_array()
        .unwrap()
        .iter()
        .find(|r| r[0] == role)
        .unwrap();
    let public: Vec<_> = envelope[2][4]
        .as_array()
        .unwrap()
        .iter()
        .map(|p| json!([p[0], p[1], value(p[1].as_str().unwrap().parse().unwrap())]))
        .collect();
    let data: Vec<_> = mapping[2]
        .as_array()
        .unwrap()
        .iter()
        .map(|p| {
            let index = p[0].as_str().unwrap().parse().unwrap();
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
                json!(["wire", value(index)])
            };
            json!([p[0], spec])
        })
        .collect();
    json!([
        "zkc.native-proof-inputs/1",
        public,
        data,
        "",
        [],
        if matches!(family, "authored" | "structured") {
            "0".to_owned()
        } else {
            (7 + 3 * n).to_string()
        }
    ])
}
fn accepted(deployment: &NativeDeployment, input: &Json, proof: Option<&[u8]>) -> Vec<u8> {
    let report = deployment.execute(input, proof).unwrap();
    assert!(!report.cancelled);
    report.outcome.unwrap()
}
fn key_attempts(directory: &Path, keys: &Keys) {
    use zkc_runtime::attempt::Limits;
    use zkc_tools::proof::AttemptPolicy;

    let path = directory.join("1.pk");
    for complete in [true, false] {
        let bytes =
            std::fs::read(directory.join(format!("key_attempt_{complete}.deployment"))).unwrap();
        let envelope: Json = serde_json::from_slice(&bytes).unwrap();
        let deployment =
            NativeDeployment::admit(&bytes, &digest(&bytes), authority(keys, true)).unwrap();
        let producer = inputs(&envelope, "authored", keys, &path, true);
        let validator = inputs(&envelope, "authored", keys, &path, false);
        let expected = accepted(&deployment, &producer, None);
        let mut policy = AttemptPolicy {
            completion: 1,
            rng: vec![],
            limits: Limits {
                attempts: 1,
                proof_bytes: expected.len(),
            },
            work: Default::default(),
            values: Default::default(),
        };
        typed::policy_before_file(&deployment, &producer, &policy);
        let first = deployment.execute_attempts(&producer, &policy).unwrap();
        let typed = typed::material_request(&producer, keys);
        let reused = deployment.execute_attempts_typed(&typed, &policy).unwrap();
        assert_eq!(reused.outcome, first.outcome);
        assert_eq!(reused.binding, first.binding);
        assert_eq!(
            reused.usage.total_value_bytes,
            first.usage.total_value_bytes
        );
        assert_eq!(reused.usage.instructions, first.usage.instructions);
        assert_eq!(reused.resources, first.resources);
        assert_eq!(reused.attempts.len(), first.attempts.len());
        assert!(reused.cleanup_errors.is_empty());
        assert_eq!(first.attempts.len(), 1);
        assert_eq!(first.attempts[0].decision, Ok(complete));
        assert!(first.cleanup_errors.is_empty());
        if complete {
            let proof = first.outcome.unwrap();
            assert_eq!(proof, expected);
            accepted(&deployment, &validator, Some(&proof));
            reference::verify(&envelope, &validator, &proof, "authored", 1);
        } else {
            assert_eq!(first.outcome.unwrap_err(), "native-attempt-limit");
            policy.limits.attempts = 2;
            let repeated = deployment.execute_attempts(&producer, &policy).unwrap();
            assert_eq!(repeated.outcome.unwrap_err(), "native-attempt-limit");
            assert_eq!(repeated.attempts.len(), 2);
            assert!(repeated.attempts.iter().all(|r| r.decision == Ok(false)));
            assert_eq!(repeated.bytes, expected.len() * 2);
            assert_eq!(
                repeated.usage.total_value_bytes,
                first.usage.total_value_bytes * 2
            );
            assert_eq!(repeated.usage.instructions, first.usage.instructions * 2);
            assert!(repeated.cleanup_errors.is_empty());

            // PK material is loaded once, but every entry is charged for its
            // input bindings. No remaining payload allowance means reentry
            // fails before the second body, even though the backing is shared.
            policy.values.total_bytes = first.usage.total_value_bytes;
            let exhausted = deployment.execute_attempts(&producer, &policy).unwrap();
            assert_eq!(exhausted.outcome.unwrap_err(), "Limit");
            assert_eq!(exhausted.attempts.len(), 2);
            assert_eq!(
                exhausted.attempts[1].decision.as_ref().unwrap_err(),
                "Limit"
            );
            assert_eq!(exhausted.attempts[1].usage.instructions, 0);
            assert_eq!(
                exhausted.usage.total_value_bytes,
                first.usage.total_value_bytes
            );
            assert!(exhausted.cleanup_errors.is_empty());
        }
    }
}
fn main() {
    let directory = std::env::args().nth(1).expect("fixture directory");
    let directory = Path::new(&directory);
    let manifest: Json =
        serde_json::from_slice(&std::fs::read(directory.join("manifest.json")).unwrap()).unwrap();
    let bounds = Policy::default().ark_bounds();
    assert_eq!(
        Keys::setup_for_development(0, &bounds).unwrap_err(),
        zkc_arkworks::Error::PositiveArityRequired
    );
    let keys: BTreeMap<_, _> = [1, 2, 3, 8]
        .into_iter()
        .map(|n| (n, Keys::setup_for_development(n, &bounds).unwrap()))
        .collect();
    for (&n, key) in &keys {
        std::fs::write(
            directory.join(format!("{n}.pk")),
            key.prover_key().to_bytes(&bounds).unwrap(),
        )
        .unwrap();
    }
    key_attempts(directory, &keys[&1]);
    let mut runs = 0;
    let mut proofs = BTreeMap::new();
    for case in manifest.as_array().unwrap() {
        let name = case["name"].as_str().unwrap();
        let family = case["family"].as_str().unwrap();
        let bytes = std::fs::read(directory.join(format!("{name}.deployment"))).unwrap();
        let envelope: Json = serde_json::from_slice(&bytes).unwrap();
        assert!(
            NativeDeployment::admit(&bytes, &digest(&bytes), Default::default())
                .unwrap_err()
                .contains("key-authority")
        );
        for &n in if matches!(family, "authored" | "structured") {
            &[1][..]
        } else {
            &[1, 2, 3, 8][..]
        } {
            let key = &keys[&n];
            let deployment = NativeDeployment::admit(
                &bytes,
                &digest(&bytes),
                authority(key, matches!(family, "authored" | "structured")),
            )
            .unwrap_or_else(|e| panic!("{name}: {e}"));
            let path = directory.join(format!("{n}.pk"));
            let p = inputs(&envelope, family, key, &path, true);
            let v = inputs(&envelope, family, key, &path, false);
            if n == 1 {
                typed::preflight(&deployment, &envelope, &p);
            }
            let proof = accepted(&deployment, &p, None);
            if n == 1 {
                typed::material_parity(&deployment, &p, key, &v, &proof);
            }
            let instance = (
                family.to_owned(),
                envelope[2][1][5].as_str().unwrap().to_owned(),
                n,
            );
            if let Some(expected) = proofs.insert(instance, proof.clone()) {
                assert_eq!(
                    proof, expected,
                    "lowering options changed proof bytes: {name}"
                );
            }
            accepted(&deployment, &v, Some(&proof));
            reference::verify(&envelope, &v, &proof, family, n);
            if n == 1 {
                std::fs::write(
                    directory.join(format!("{name}.setups.json")),
                    serde_json::to_vec(&authority_record(
                        key,
                        matches!(family, "authored" | "structured"),
                    ))
                    .unwrap(),
                )
                .unwrap();
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
                std::fs::write(directory.join(format!("{name}.proof")), &proof).unwrap();
                if family == "structured" {
                    structured_mutations(&deployment, &v, &proof);
                } else if !name.contains("plain") && !name.contains("release") {
                    mutations::check(&deployment, &envelope, (&p, &v), &proof, family, key, &path);
                }
            }
            runs += 1;
        }
    }
    println!("{runs} committed/authored proofs accepted with independent terminal checks");
}

// Replace a present, valid opening with a well-formed absent alternative. The
// envelope/header and later record remain intact; the protocol must reject it.
fn structured_mutations(deployment: &NativeDeployment, input: &Json, proof: &[u8]) {
    let size = u64::from_le_bytes(proof[40..48].try_into().unwrap()) as usize;
    let mut absent = proof[..40].to_vec();
    absent.extend_from_slice(&10u64.to_le_bytes());
    absent.extend_from_slice(b"ZKCV\x01\x41");
    absent.extend_from_slice(&0u32.to_le_bytes());
    absent.extend_from_slice(&proof[48 + size..]);
    assert!(
        deployment
            .execute(input, Some(&absent))
            .unwrap()
            .outcome
            .is_err()
    );
    let mut altered = proof.to_vec();
    // First child frame is a field. Alter the evaluation while retaining valid
    // canonical framing: verification must use the nested proof and this value.
    altered[48 + 10 + 4 + 6] ^= 1;
    assert!(
        deployment
            .execute(input, Some(&altered))
            .unwrap()
            .outcome
            .is_err()
    );
}
