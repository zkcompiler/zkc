//! Contrasting domain clients executed by the general independent proof host.
#[path = "support/domain_transcript.rs"]
mod reference;
use p3_field::PrimeCharacteristicRing;
use serde_json::{Value as Json, json};
use sha2::{Digest, Sha256};
use std::path::Path;
use zkc_backends::{
    Bn254G1, Bn254G2, Bn254Scalar, Domain, EntryPolicy, KoalaBear, KoalaBearExt8, NativeBackend,
    Policy, RistrettoScalar, Value,
};
use zkc_tools::proof::{NativeDeployment, hex};

fn codec() -> NativeBackend {
    NativeBackend::new(
        Policy::default(),
        EntryPolicy::new(Domain::new("P", "domains", "main", None), None),
        Default::default(),
    )
    .unwrap()
}
fn inputs(envelope: &Json, values: &[Value], producing: bool) -> Json {
    let codec = codec();
    let wire = |i: &Json| {
        hex(&codec
            .encode_native_value(&values[i.as_str().unwrap().parse::<usize>().unwrap()])
            .unwrap())
    };
    let public: Vec<_> = envelope[2][4]
        .as_array()
        .unwrap()
        .iter()
        .map(|p| json!([p[0], p[1], wire(&p[1])]))
        .collect();
    let role = envelope[6]
        .as_array()
        .unwrap()
        .iter()
        .find(|r| r[0] == envelope[2][1][if producing { 2 } else { 3 }])
        .unwrap();
    let data: Vec<_> = role[2]
        .as_array()
        .unwrap()
        .iter()
        .map(|p| json!([p[0], ["wire", wire(&p[0])]]))
        .collect();
    let services: Vec<_> = role[4]
        .as_array()
        .unwrap()
        .iter()
        .map(|p| json!([p[0], "16"]))
        .collect();
    json!(["zkc.native-proof-inputs", public, data, "", services, "32"])
}
fn run(
    deployment: &NativeDeployment,
    inputs: &Json,
    proof: Option<&[u8]>,
) -> Result<Vec<u8>, String> {
    let report = deployment.execute(inputs, proof)?;
    assert!(report.cleanup_errors.is_empty());
    if report.outcome.is_ok() {
        assert!(!report.cancelled);
    }
    report.outcome
}
fn main() {
    let directory = std::env::args().nth(1).expect("generated directory");
    let directory = Path::new(&directory);
    let manifest: Json =
        serde_json::from_slice(&std::fs::read(directory.join("manifest.json")).unwrap()).unwrap();
    for case in manifest.as_array().unwrap() {
        let name = case["name"].as_str().unwrap();
        let bytes = std::fs::read(directory.join(format!("{name}.deployment"))).unwrap();
        let envelope: Json = serde_json::from_slice(&bytes).unwrap();
        let deployment =
            NativeDeployment::admit(&bytes, &Sha256::digest(&bytes).into(), Default::default())
                .unwrap();
        check_suite_mutations(&envelope);
        for size in [0u64, 1, 7, 127] {
            let values = if case["family"] == "domain-values" {
                // Non-base extension coordinates detect a fake scalar embedding.
                let extension = KoalaBearExt8::from([
                    KoalaBear::new(size as u32),
                    KoalaBear::new(1),
                    KoalaBear::new(2),
                    KoalaBear::new(3),
                    KoalaBear::new(4),
                    KoalaBear::new(5),
                    KoalaBear::new(6),
                    KoalaBear::new(7),
                ]);
                vec![
                    Value::Bn254Field(Bn254Scalar::from(size)),
                    Value::Bn254G1(Bn254G1::generator()),
                    Value::Bn254G2(Bn254G2::generator()),
                    Value::KoalaBearField(KoalaBear::new(size as u32)),
                    Value::KoalaBearExt8Field(extension),
                ]
            } else {
                let wire = [
                    b"ZKCV\x01\x10".as_slice(),
                    &[
                        0xe2, 0xf2, 0xae, 0x0a, 0x6a, 0xbc, 0x4e, 0x71, 0xa8, 0x84, 0xa9, 0x61,
                        0xc5, 0x00, 0x51, 0x5f, 0x58, 0xe3, 0x0b, 0x6a, 0xa5, 0x82, 0xdd, 0x8d,
                        0xb6, 0xa6, 0x59, 0x45, 0xe0, 0x8d, 0x2d, 0x76,
                    ],
                ]
                .concat();
                let Value::RistrettoGroup(base) = codec()
                    .decode_native_value(
                        &zkc_runtime::interactive::PhysicalType::default_for(
                            zkc_runtime::interactive::LogicalType::parse(
                                "group:ristretto255.group",
                            )
                            .unwrap(),
                        )
                        .unwrap(),
                        &wire,
                    )
                    .unwrap()
                else {
                    panic!("group");
                };
                vec![
                    Value::RistrettoGroup(base),
                    Value::RistrettoField(RistrettoScalar::from(size)),
                    Value::RistrettoGroup(base * RistrettoScalar::from(size)),
                ]
            };
            let producer = inputs(&envelope, &values, true);
            let validator = inputs(&envelope, &values, false);
            // Every typed draw must execute and consume its budget.
            for port in 0..producer[4].as_array().unwrap().len() {
                let mut exhausted = producer.clone();
                exhausted[4][port][1] = json!("0");
                assert!(
                    run(&deployment, &exhausted, None)
                        .unwrap_err()
                        .contains("exhausted")
                );
            }
            let proof = run(&deployment, &producer, None).unwrap();
            run(&deployment, &validator, Some(&proof)).unwrap();
            check_reference(
                &envelope,
                &producer,
                &proof,
                &values,
                case["two_draws"] == true,
            );
            let mut trailing = proof.clone();
            trailing.push(0);
            assert_eq!(
                run(&deployment, &validator, Some(&trailing)).unwrap_err(),
                "proof-trailing"
            );
            assert_eq!(
                run(&deployment, &validator, Some(&proof[..proof.len() - 1])).unwrap_err(),
                "proof-truncated"
            );
            let mut wrong = producer.clone();
            wrong[2][0][1][1] = json!(hex(&codec()
                .encode_native_value(&Value::Bool(true))
                .unwrap()));
            assert!(run(&deployment, &wrong, None).is_err());
            let mut context = validator.clone();
            context[3] = json!("01");
            assert_eq!(
                run(&deployment, &context, Some(&proof)).unwrap_err(),
                "proof-header"
            );
            // Distinguish a valid but false equation from canonical decode failure.
            let mut modified = proof.clone();
            let start = modified.len() - 38;
            if case["family"] == "ristretto-services" {
                let scalar =
                    Option::<RistrettoScalar>::from(RistrettoScalar::from_canonical_bytes(
                        modified[start + 6..].try_into().unwrap(),
                    ))
                    .unwrap();
                modified[start + 6..].copy_from_slice(&(scalar + RistrettoScalar::ONE).to_bytes());
            } else {
                let value = reference::extension_value(&modified[start..]);
                modified[start..]
                    .copy_from_slice(&reference::extension_wire(value + KoalaBearExt8::ONE));
            }
            assert_eq!(
                run(&deployment, &validator, Some(&modified)).unwrap_err(),
                "artifact-rejected"
            );
            modified[start + 6..].fill(255);
            assert_eq!(
                run(&deployment, &validator, Some(&modified)).unwrap_err(),
                "artifact-stopped:Decode(Scalar)"
            );
            let transitions = envelope[2][3].as_array().unwrap().len();
            for (input, incoming) in [(&producer, None), (&validator, Some(proof.as_slice()))] {
                let mut exact = input.clone();
                exact[5] = json!(transitions.to_string());
                run(&deployment, &exact, incoming).unwrap();
                exact[5] = json!((transitions - 1).to_string());
                assert_eq!(
                    run(&deployment, &exact, incoming).unwrap_err(),
                    "exhausted:resource-budget"
                );
            }
            if case["retries"] == true && size == 7 {
                use zkc_runtime::interactive::{ValueBudget, WorkBudget};
                use zkc_tools::proof::AttemptPolicy;
                let report = deployment
                    .execute_attempts(
                        &producer,
                        &AttemptPolicy {
                            completion: 1,
                            rng: vec![],
                            limits: zkc_runtime::attempt::Limits {
                                attempts: 3,
                                proof_bytes: 1048576,
                            },
                            work: WorkBudget::default(),
                            values: ValueBudget::default(),
                        },
                    )
                    .unwrap();
                assert_eq!(report.outcome.as_ref().unwrap_err(), "native-attempt-limit");
                assert_eq!(report.attempts.len(), 3);
                assert!(report.attempts.iter().all(|a| a.decision == Ok(false)));
                assert!(report.cleanup_errors.is_empty());
                assert_eq!(
                    report.resources.len(),
                    producer[4].as_array().unwrap().len()
                );
                for root in &report.resources {
                    assert_eq!(root["state"]["transitions"], 3);
                    assert_eq!(root["leased"], false);
                    assert_eq!(root["poisoned"], false);
                }
            }
            if size == 7 {
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
        }
    }
    println!("typed domain and service executions accepted; malformed inputs and proofs refused");
}

fn check_suite_mutations(envelope: &Json) {
    use zkc_runtime::logical;
    let mut changed = envelope.clone();
    let query = changed[2][3]
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|r| r[0] == "query")
        .unwrap();
    let origin = query[1].as_str().unwrap();
    let bytes: Vec<_> = (0..origin.len())
        .step_by(2)
        .map(|n| u8::from_str_radix(&origin[n..n + 2], 16).unwrap())
        .collect();
    let mut record = logical::decode_tree(&bytes).unwrap();
    record[4][4] = json!("random.bls12-381.fr/1");
    query[1] = json!(hex(&logical::encode_tree(&record).unwrap()));
    changed[3] = json!(hex(&Sha256::digest(
        logical::encode_tree(&changed[2]).unwrap()
    )));
    let bytes = serde_json::to_vec(&changed).unwrap();
    assert_eq!(
        NativeDeployment::admit(&bytes, &Sha256::digest(&bytes).into(), Default::default())
            .unwrap_err(),
        "native-proof-query-origin"
    );
    for format in ["invalid.native-proof", ""] {
        let mut unknown_format = envelope.clone();
        unknown_format[0] = json!(format);
        let bytes = serde_json::to_vec(&unknown_format).unwrap();
        assert_eq!(
            NativeDeployment::admit(&bytes, &Sha256::digest(&bytes).into(), Default::default())
                .unwrap_err(),
            "native-proof-format"
        );
    }
}

// These equations consume a challenge derived from upstream Merlin, never a
// challenge supplied by the proof or by the verifier being tested.
fn check_reference(envelope: &Json, input: &Json, proof: &[u8], values: &[Value], two_draws: bool) {
    if let Value::RistrettoField(secret) = values[1] {
        use curve25519_dalek::{
            constants::RISTRETTO_BASEPOINT_POINT, ristretto::CompressedRistretto, scalar::Scalar,
        };
        let mut r =
            reference::Replay::new(envelope, input, proof, "merlin3.ristretto255.scalar64le/1");
        let wire = r.message("commitment", "Alice", "Bob");
        assert_eq!(&wire[..6], b"ZKCV\x01\x10");
        let commitment = CompressedRistretto(wire[6..].try_into().unwrap())
            .decompress()
            .unwrap();
        r.query("draw_challenge", 4, "random.ristretto255.scalar/1", "Bob");
        let challenge = r.ristretto();
        r.observe(
            "challenge",
            "Bob",
            "Alice",
            &[b"ZKCV\x01\x0d".as_slice(), &challenge.to_bytes()].concat(),
        );
        let challenge = if two_draws {
            r.query("draw2", 4, "random.ristretto255.scalar/1", "Bob");
            let second = r.ristretto();
            r.observe(
                "challenge2",
                "Bob",
                "Alice",
                &[b"ZKCV\x01\x0d".as_slice(), &second.to_bytes()].concat(),
            );
            challenge + second
        } else {
            challenge
        };
        let wire = r.message("response", "Alice", "Bob");
        assert_eq!(&wire[..6], b"ZKCV\x01\x0d");
        let response =
            Option::<Scalar>::from(Scalar::from_canonical_bytes(wire[6..].try_into().unwrap()))
                .unwrap();
        assert_eq!(
            RISTRETTO_BASEPOINT_POINT * response,
            commitment + RISTRETTO_BASEPOINT_POINT * (secret * challenge)
        );
        r.finish();
    } else {
        let mut r = reference::Replay::new(
            envelope,
            input,
            proof,
            "merlin3.koala-bear.ext8-binomial3.rejection31le/1",
        );
        r.message("bn_random", "P", "V");
        let randomness = reference::extension_value(r.message("ext_random", "P", "V"));
        for site in ["a", "b", "scalar", "base"] {
            r.message(site, "P", "V");
        }
        r.query("draw", 5, "random.koala-bear.ext8-binomial3/1", "V");
        let challenge = r.extension();
        r.observe("challenge", "V", "P", &reference::extension_wire(challenge));
        let challenge = if two_draws {
            r.query("draw2", 5, "random.koala-bear.ext8-binomial3/1", "V");
            let second = r.extension();
            r.observe("challenge2", "V", "P", &reference::extension_wire(second));
            challenge + second
        } else {
            challenge
        };
        let result = reference::extension_value(r.message("extension", "P", "V"));
        let Value::KoalaBearExt8Field(value) = values[4] else {
            panic!("extension input")
        };
        assert_eq!(result, value + randomness + challenge);
        r.finish();
    }
}
