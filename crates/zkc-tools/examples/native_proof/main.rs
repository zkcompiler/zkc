//! Protocol arithmetic is test-client code. Every case uses the same compiler,
//! independent-role host, Runner, canonical wire codecs and resource lifecycle.
#[cfg(feature = "test-utils")]
#[path = "../support/input_admission.rs"]
mod input_admission;
mod reference;
use serde_json::{Value as Json, json};
use sha2::{Digest, Sha256};
use std::{collections::BTreeMap, path::Path};
use zkc_backends::{Domain, EntryPolicy, GroupPoint, NativeBackend, Policy, Scalar, Value};
use zkc_runtime::interactive::admit_supplied;
use zkc_tools::proof::{NativeDeployment, NativeProofReport, hex};

fn backend() -> NativeBackend {
    NativeBackend::new(
        Policy::default(),
        EntryPolicy::new(Domain::new("Alice", "test", "main", None), None),
        Default::default(),
    )
    .unwrap()
}
fn digest(bytes: &[u8]) -> String {
    hex(&Sha256::digest(bytes))
}
fn inputs(envelope: &Json, case: &Json, producing: bool) -> Json {
    let policy = &envelope[2][1];
    let role = &policy[if producing { 2 } else { 3 }];
    let map = envelope[6]
        .as_array()
        .unwrap()
        .iter()
        .find(|row| &row[0] == role)
        .unwrap();
    let codec = backend();
    let value = |port: &Json, ty: &Json| {
        let original: usize = port.as_str().unwrap().parse().unwrap();
        let index = case["value_ports"][original]
            .as_u64()
            .unwrap_or(original as u64);
        let value = match ty.as_str().unwrap() {
            "group:bls12-381.g1" => {
                Value::Curve(GroupPoint::generator().scale(Scalar::from(match index {
                    0 => 1,
                    2 => 3,
                    5 => 7,
                    6 => 21,
                    _ => panic!("group input"),
                })))
            }
            "field:bls12-381.fr" => Value::Field(Scalar::from(match index {
                1 => 3,
                4 => 11,
                _ => panic!("field input"),
            })),
            "bool" => Value::Bool(true),
            _ => panic!("wire input"),
        };
        json!(hex(&codec.encode_native_value(&value).unwrap()))
    };
    let public: Vec<_> = envelope[2][4]
        .as_array()
        .unwrap()
        .iter()
        .map(|p| json!([p[0], p[1], value(&p[1], &p[2])]))
        .collect();
    let data: Vec<_> = map[2]
        .as_array()
        .unwrap()
        .iter()
        .map(|p| {
            let spec = if p[1].as_str().unwrap().starts_with("nonce:") {
                json!(["nonce", "2"])
            } else {
                json!(["wire", value(&p[0], &p[1])])
            };
            json!([p[0], spec])
        })
        .collect();
    let services: Vec<_> = map[4]
        .as_array()
        .unwrap()
        .iter()
        .map(|p| json!([p[0], case["rounds"].as_u64().unwrap().to_string()]))
        .collect();
    let budget = if policy[5] == "" {
        0
    } else {
        envelope[2][3].as_array().unwrap().len()
    };
    json!([
        "zkc.native-proof-inputs/1",
        public,
        data,
        "",
        services,
        budget.to_string()
    ])
}
fn cleaned(report: &NativeProofReport) {
    for resource in &report.resources {
        if resource["kind"] == "service" {
            assert_eq!(resource["leased"], false);
        }
    }
    assert!(!report.outcome.as_ref().err().is_some_and(
        |e| e.starts_with("native-proof-cleanup") || e == "native-proof-active-frames"
    ));
}
fn successful_resources(report: &NativeProofReport, envelope: &Json, case: &Json, producer: bool) {
    assert!(report.outcome.is_ok());
    let capabilities: Vec<_> = report
        .resources
        .iter()
        .filter(|r| r["kind"] == "capability")
        .map(|r| r["transitions"].as_u64().unwrap())
        .collect();
    let mut expected = Vec::new();
    if producer && case["family"] == "affine" {
        expected.push(2);
    }
    if envelope[2][1][5] != "" {
        expected.push(envelope[2][3].as_array().unwrap().len() as u64);
    }
    assert_eq!(capabilities, expected);
    for service in report.resources.iter().filter(|r| r["kind"] == "service") {
        assert_eq!(
            service["state"]["transitions"],
            if case["name"] == "affine_setup" {
                json!(0)
            } else {
                case["rounds"].clone()
            }
        );
        assert_eq!(service["poisoned"], false);
        assert_eq!(service["leased"], false);
    }
}
fn rejected(deployment: &NativeDeployment, input: &Json, proof: &[u8]) {
    let report = deployment.execute(input, Some(proof)).unwrap();
    cleaned(&report);
    assert!(report.outcome.is_err());
}
fn rejects_with(deployment: &NativeDeployment, input: &Json, proof: &[u8], expected: &str) {
    let report = deployment.execute(input, Some(proof)).unwrap();
    cleaned(&report);
    let reason = report.outcome.unwrap_err();
    assert!(
        reason.starts_with(expected),
        "expected {expected}, got {reason}"
    );
}
fn repin(envelope: &Json, candidate: &Json) -> Vec<u8> {
    let mut envelope = envelope.clone();
    let candidate = serde_json::to_string(candidate).unwrap();
    envelope[4] = json!(candidate);
    envelope[5] = json!(digest(candidate.as_bytes()));
    serde_json::to_vec(&envelope).unwrap()
}
fn admitted_mutation_refuses(envelope: &Json, candidate: &Json, reason: &str) {
    let candidate_bytes = serde_json::to_vec(candidate).unwrap();
    admit_supplied(&candidate_bytes, &backend())
        .expect("mutation must pass ordinary typed admission");
    // Re-pin solely to exercise the structural checker. A real application must
    // never accept a pin supplied by this candidate or by its proof producer.
    let bytes = repin(envelope, candidate);
    assert_eq!(
        NativeDeployment::admit(&bytes, &digest(&bytes), Default::default()).unwrap_err(),
        reason
    );
}
fn mutations(envelope: &Json, bytes: &[u8], input: &Json, proof: &[u8]) {
    let original: Json = serde_json::from_str(envelope[4].as_str().unwrap()).unwrap();
    // Roles can implement identical transcript semantics with distinct helpers.
    let mut candidate = original.clone();
    let mut names = BTreeMap::new();
    for mut function in original[3].as_array().unwrap().iter().cloned() {
        let old = function[1].as_str().unwrap().to_owned();
        if old.starts_with("_transcript") {
            let name = format!("validator{old}");
            function[1] = json!(name);
            names.insert(old, name);
            candidate[3].as_array_mut().unwrap().push(function);
        }
    }
    for instruction in candidate[4][1][7].as_array_mut().unwrap() {
        if instruction[0] == "local"
            && let Some(name) = names.get(instruction[2].as_str().unwrap())
        {
            instruction[2] = json!(name);
        }
    }
    admit_supplied(&serde_json::to_vec(&candidate).unwrap(), &backend()).unwrap();
    let separate = repin(envelope, &candidate);
    let separate =
        NativeDeployment::admit(&separate, &digest(&separate), Default::default()).unwrap();
    let validated = separate.execute(input, Some(proof)).unwrap();
    cleaned(&validated);
    validated.outcome.unwrap();

    // Keep SSA and affine state use valid while challenging before observing
    // the received commitment. Ordinary typing cannot establish this order.
    let mut candidate = original.clone();
    let body = candidate[4][1][7].as_array_mut().unwrap();
    let observe = body
        .iter()
        .position(|i| i[0] == "local" && i[2].as_str().unwrap().starts_with("_transcript"))
        .unwrap();
    let mut challenge = body.remove(observe + 1);
    let initial = body[observe][3][0].clone();
    let challenge_state = challenge[4].as_array().unwrap().last().unwrap().clone();
    let observed_state = body[observe][4].as_array().unwrap().last().unwrap().clone();
    challenge[3][0] = initial;
    body[observe][3][0] = challenge_state;
    body[observe + 1][3][0] = observed_state;
    body.insert(observe, challenge);
    admitted_mutation_refuses(envelope, &candidate, "native-proof-observation-order");
    let mut candidate = original.clone();
    let body = candidate[4][1][7].as_array_mut().unwrap();
    let observe = body
        .iter_mut()
        .find(|i| i[0] == "local" && i[2].as_str().unwrap().starts_with("_transcript"))
        .unwrap();
    // Observe the public base instead of the actual received commitment.
    observe[3][1] = original[4][1][5][0][0].clone();
    admitted_mutation_refuses(envelope, &candidate, "native-proof-observation-payload");
    let corrupted = repin(envelope, &candidate);
    assert_eq!(
        NativeDeployment::admit(&corrupted, &digest(bytes), Default::default()).unwrap_err(),
        "native-proof-deployment-binding"
    );
    let mut candidate = original.clone();
    let body = candidate[4][1][7].as_array_mut().unwrap();
    let i = body
        .iter()
        .rposition(|i| i[0] == "local" && i[2].as_str().unwrap().starts_with("_transcript"))
        .unwrap();
    let removed = body.remove(i);
    *body.last_mut().unwrap()[1]
        .as_array_mut()
        .unwrap()
        .last_mut()
        .unwrap() = removed[3][0].clone();
    admitted_mutation_refuses(envelope, &candidate, "native-proof-state-chain");
    let mut candidate = original.clone();
    let body = candidate[4][1][7].as_array_mut().unwrap();
    let calls: Vec<_> = body
        .iter()
        .enumerate()
        .filter(|(_, i)| i[0] == "local" && i[2].as_str().unwrap().starts_with("_transcript"))
        .map(|(i, _)| i)
        .collect();
    body[calls[3]][2] = body[calls[2]][2].clone();
    admitted_mutation_refuses(envelope, &candidate, "native-proof-state-chain");
    let mut candidate = original.clone();
    let mut helper = candidate[3]
        .as_array()
        .unwrap()
        .iter()
        .find(|f| f[1].as_str().unwrap().starts_with("_transcript"))
        .unwrap()
        .clone();
    helper[1] = json!("unreachable_transition");
    candidate[3].as_array_mut().unwrap().push(helper);
    admitted_mutation_refuses(envelope, &candidate, "native-proof-state-chain");
    // Retired contracts are no longer well-typed operations. Refuse them at
    // ordinary admission as well as at deployment admission, even after repinning.
    for contract in [
        "transcript.challenge",
        "transcript.native.challenge",
        "transcript.native.indexed.observe.group",
    ] {
        let mut candidate = original.clone();
        let binding = candidate[1]
            .as_array_mut()
            .unwrap()
            .iter_mut()
            .find(|b| b[1] == "transcript.native.indexed.challenge")
            .unwrap();
        binding[1] = json!(contract);
        binding[3] = json!(format!("arkworks/{contract}"));
        let error =
            admit_supplied(&serde_json::to_vec(&candidate).unwrap(), &backend()).unwrap_err();
        assert_eq!(error.code, zkc_runtime::interactive::ErrorCode::Signature);
        let bytes = repin(envelope, &candidate);
        assert!(NativeDeployment::admit(&bytes, &digest(&bytes), Default::default()).is_err());
    }
}
fn envelope_mutations(envelope: &Json) {
    let cases = [
        (vec![1], json!("bad"), "native-proof-digest"),
        (
            vec![3],
            json!("0".repeat(64)),
            "native-proof-descriptor-binding",
        ),
        (
            vec![5],
            json!("0".repeat(64)),
            "native-proof-candidate-binding",
        ),
        (vec![2, 1, 4], json!("1"), "native-proof-acceptance-map"),
        (vec![2, 1, 7], json!(["0"]), "native-proof-public-map"),
        (
            vec![2, 5, 0, 2],
            json!("zkcv.bool/1"),
            "native-proof-message-map",
        ),
        (vec![6, 1, 5], json!("1"), "native-proof-acceptance-map"),
        (vec![6, 0, 4, 0, 0], json!("0"), "native-proof-service-map"),
        (vec![8], json!([]), "native-proof-wire-map"),
    ];
    for (path, value, expected) in cases {
        let mut changed = envelope.clone();
        let mut target = &mut changed;
        for index in &path {
            target = &mut target[*index];
        }
        *target = value;
        if path[0] == 2 {
            changed[3] = json!(hex(&Sha256::digest(reference::tree(&changed[2]))));
        }
        let bytes = serde_json::to_vec(&changed).unwrap();
        assert_eq!(
            NativeDeployment::admit(&bytes, &digest(&bytes), Default::default()).unwrap_err(),
            expected
        );
    }
    // Each role map remains well typed, but one original shared input now has
    // incompatible role types. Refuse the deployment before invocation data.
    let mut changed = envelope.clone();
    changed[6][0][2][1][0] = json!("2");
    changed[6][0][2][2][0] = json!("3");
    changed[6][0][4][0][0] = json!("5");
    let bytes = serde_json::to_vec(&changed).unwrap();
    assert_eq!(
        NativeDeployment::admit(&bytes, &digest(&bytes), Default::default()).unwrap_err(),
        "native-proof-shared-port-type"
    );
    // An unused private value is valid ordinary participant IR, but this proof
    // host has no input constructor for it. Refuse before reading input rows.
    // Keep all old inputs and transcript positions consistent with the map.
    for logical in ["point:bls12-381.fr", "polynomial:bls12-381.fr"] {
        let ty = zkc_runtime::interactive::PhysicalType::default_for(
            zkc_runtime::interactive::LogicalType::parse(logical).unwrap(),
        )
        .unwrap();
        let mut changed = envelope.clone();
        let mut candidate: Json = serde_json::from_str(envelope[4].as_str().unwrap()).unwrap();
        let inputs = candidate[4][0][5].as_array_mut().unwrap();
        inputs.insert(inputs.len() - 1, json!(["unloadable", ty.spelling()]));
        changed[6][0][2]
            .as_array_mut()
            .unwrap()
            .push(json!(["5", logical]));
        admitted_mutation_refuses(&changed, &candidate, "native-proof-role-input-type");
    }
    let mut candidate: Json = serde_json::from_str(envelope[4].as_str().unwrap()).unwrap();
    let mut entry = candidate[5][0].clone();
    entry[1] = json!("other");
    candidate[5].as_array_mut().unwrap().push(entry);
    admitted_mutation_refuses(envelope, &candidate, "native-proof-entry");
}
fn hostile(deployment: &NativeDeployment, envelope: &Json, p: &Json, v: &Json, proof: &[u8]) {
    for len in 0..proof.len() {
        rejects_with(deployment, v, &proof[..len], "proof-truncated");
    }
    let mut malformed = proof.to_vec();
    malformed.push(0);
    rejects_with(deployment, v, &malformed, "proof-trailing");
    let mut malformed = proof.to_vec();
    malformed[40..48].fill(255);
    rejects_with(deployment, v, &malformed, "proof-limit");
    let mut malformed = proof.to_vec();
    malformed[48..54].fill(0);
    rejects_with(deployment, v, &malformed, "artifact-stopped:Decode");
    let mut malformed = proof.to_vec();
    malformed[54..102].fill(255);
    rejects_with(deployment, v, &malformed, "artifact-stopped:Decode");
    let mut malformed = proof.to_vec();
    malformed[110..116].fill(0);
    rejects_with(deployment, v, &malformed, "artifact-stopped:Decode");
    let mut malformed = proof.to_vec();
    malformed[116..148].fill(255);
    rejects_with(deployment, v, &malformed, "artifact-stopped:Decode");
    let mut malformed = proof.to_vec();
    malformed[116..148].fill(0);
    rejects_with(
        deployment,
        v,
        &malformed,
        if envelope[2][1][5] == "" {
            "artifact-stopped:Explicit(\"reject\")"
        } else {
            "artifact-rejected"
        },
    );
    let mut changed = v.clone();
    changed[3] = json!("abcd");
    rejects_with(deployment, &changed, proof, "proof-header");
    let mut rebound = proof.to_vec();
    rebound[8..40].copy_from_slice(&Sha256::digest(reference::root(envelope, &changed)));
    if envelope[2][1][5] == "" {
        // Header integrity alone does not cryptographically bind an authored
        // protocol which never uses its root in the verification equation.
        deployment
            .execute(&changed, Some(&rebound))
            .unwrap()
            .outcome
            .unwrap();
    } else {
        rejected(deployment, &changed, &rebound);
    }
    let mut input = p.clone();
    input[4][0][1] = json!("0");
    let report = deployment.execute(&input, None).unwrap();
    cleaned(&report);
    assert!(report.outcome.is_err());
    if envelope[2][1][5] != "" {
        let mut input = p.clone();
        input[5] = json!("0");
        let report = deployment.execute(&input, None).unwrap();
        cleaned(&report);
        assert!(report.outcome.is_err());
    }
    let mut wrong_witness = p.clone();
    for row in wrong_witness[2].as_array_mut().unwrap() {
        if row[0] == "1" {
            row[1][1] = json!(hex(&backend()
                .encode_native_value(&Value::Field(Scalar::from(4)))
                .unwrap()));
        }
    }
    let invalid = deployment
        .execute(&wrong_witness, None)
        .unwrap()
        .outcome
        .unwrap();
    rejected(deployment, v, &invalid);
    let mut inconsistent = v.clone();
    inconsistent[2][0][1][1] = inconsistent[1][1][2].clone();
    assert_eq!(
        deployment
            .execute(&inconsistent, Some(proof))
            .err()
            .unwrap(),
        "native-proof-shared-public-input"
    );
    let mut changed = p.clone();
    changed[1][0][2] = changed[1][1][2].clone();
    assert_eq!(
        deployment.execute(&changed, None).err().unwrap(),
        "native-proof-shared-public-input"
    );
    let mut changed = v.clone();
    changed[1].as_array_mut().unwrap().pop();
    assert_eq!(
        deployment.execute(&changed, Some(proof)).err().unwrap(),
        "native-proof-public-inputs"
    );
    let mut changed = v.clone();
    changed[3] = json!("00".repeat(4097));
    assert_eq!(
        deployment.execute(&changed, Some(proof)).err().unwrap(),
        "native-proof-context-limit"
    );
    let mut changed = v.clone();
    changed[5] = json!("1000001");
    assert_eq!(
        deployment.execute(&changed, Some(proof)).err().unwrap(),
        "native-proof-budget"
    );
}
fn run(directory: &Path) {
    let cases: Json =
        serde_json::from_slice(&std::fs::read(directory.join("manifest.json")).unwrap()).unwrap();
    let mut portable = BTreeMap::new();
    #[cfg(feature = "test-utils")]
    let mut fixed_proofs = BTreeMap::new();
    for case in cases.as_array().unwrap() {
        let name = case["name"].as_str().unwrap();
        let bytes = std::fs::read(directory.join(format!("{name}.deployment"))).unwrap();
        let envelope: Json = serde_json::from_slice(&bytes).unwrap();
        let deployment = NativeDeployment::admit(&bytes, &digest(&bytes), Default::default())
            .unwrap_or_else(|e| panic!("{name}: {e}"));
        let (p, v) = (
            inputs(&envelope, case, true),
            inputs(&envelope, case, false),
        );
        #[cfg(feature = "test-utils")]
        if name == "schnorr_0" || name == "affine_0" {
            input_admission::private_input_admission_boundary(&deployment, &envelope, &p, None);
        }
        let report = deployment.execute(&p, None).unwrap();
        cleaned(&report);
        let binding = report.binding.clone();
        successful_resources(&report, &envelope, case, true);
        let proof = report.outcome.unwrap_or_else(|e| panic!("{name}: {e}"));
        let report = deployment.execute(&v, Some(&proof)).unwrap();
        cleaned(&report);
        successful_resources(&report, &envelope, case, false);
        report.outcome.unwrap_or_else(|e| panic!("{name}: {e}"));
        reference::verify(case, &envelope, &p, &proof, None);
        #[cfg(feature = "test-utils")]
        {
            let tape = vec![Scalar::from(5); case["rounds"].as_u64().unwrap() as usize];
            let nonce_port = case["nonce_port"].as_u64().unwrap_or(3) as usize;
            let mut tapes = BTreeMap::from([(nonce_port, tape)]);
            if name == "affine_setup" {
                tapes.insert(5, vec![]);
            }
            let result = deployment.execute_test(&p, None, tapes).unwrap();
            cleaned(&result);
            let fixed = result.outcome.unwrap();
            reference::verify(case, &envelope, &p, &fixed, Some(Scalar::from(5)));
            deployment
                .execute(&v, Some(&fixed))
                .unwrap()
                .outcome
                .unwrap();
            if let Some(prior) = fixed_proofs.insert(binding.clone(), fixed.clone()) {
                assert_eq!(prior, fixed);
            }
            if name == "schnorr_0" {
                let failed = deployment
                    .execute_test(&p, None, BTreeMap::from([(3, vec![])]))
                    .unwrap();
                cleaned(&failed);
                assert!(failed.outcome.is_err());
                let service = failed
                    .resources
                    .iter()
                    .find(|r| r["kind"] == "service")
                    .unwrap();
                assert_eq!(service["poisoned"], true);
                assert_eq!(service["state"]["transitions"], 1);
                assert_eq!(service["state"]["budget"], 0);
            }
        }
        if let Some(prior) = portable.insert(binding, proof.clone()) {
            deployment
                .execute(&v, Some(&prior))
                .unwrap()
                .outcome
                .unwrap();
        }
        if name == "schnorr_0" || name == "authored" {
            hostile(&deployment, &envelope, &p, &v, &proof);
        }
        if name == "schnorr_0" {
            mutations(&envelope, &bytes, &v, &proof);
            envelope_mutations(&envelope);
        }
        if name == "dleq_0" {
            let mut candidate: Json = serde_json::from_str(envelope[4].as_str().unwrap()).unwrap();
            for participant in candidate[4].as_array_mut().unwrap() {
                for instruction in participant[7].as_array_mut().unwrap() {
                    if instruction[0] == "send" || instruction[0] == "receive" {
                        for item in instruction.as_array_mut().unwrap().iter_mut().skip(1) {
                            if item == "commitment" {
                                *item = json!("second_commitment");
                            } else if item == "second_commitment" {
                                *item = json!("commitment");
                            }
                        }
                    }
                }
            }
            admitted_mutation_refuses(&envelope, &candidate, "native-proof-wire-map");
        }
        if name.starts_with("bool_") {
            let mut malformed = proof.clone();
            *malformed.last_mut().unwrap() = 2;
            let report = deployment.execute(&v, Some(&malformed)).unwrap();
            cleaned(&report);
            let error = report.outcome.unwrap_err();
            assert!(error.starts_with("artifact-stopped:Decode"), "{error}");
        }
        #[cfg(feature = "test-utils")]
        if name == "affine_setup" {
            // Malformed late inputs refuse before even attempting entropy issuance.
            let mut malformed = p.clone();
            malformed[5] = json!("01");
            assert_eq!(
                deployment
                    .execute_test(&malformed, None, BTreeMap::new())
                    .err()
                    .unwrap(),
                "natural-index"
            );
            // Valid input, but the second provider is unavailable after nonce and
            // transcript issuance. Both roots must still be retired and observed.
            let failed = deployment
                .execute_test(&p, None, BTreeMap::from([(3, vec![Scalar::from(5)])]))
                .unwrap();
            cleaned(&failed);
            assert_eq!(
                failed.outcome.unwrap_err(),
                "native-proof-test-entropy-port"
            );
            assert_eq!(failed.instructions, 0);
            assert_eq!(failed.resources.len(), 2);
            assert!(failed.resources.iter().all(|r| r["transitions"] == 0));
        }
        if name.starts_with("guarded_") {
            for port in ["5", "6"] {
                let mut v = v.clone();
                for row in v[1].as_array_mut().unwrap() {
                    if row[1] == port {
                        row[2] = json!(hex(&backend()
                            .encode_native_value(&Value::Bool(false))
                            .unwrap()));
                    }
                }
                for row in v[2].as_array_mut().unwrap() {
                    if row[0] == port {
                        row[1][1] = json!(hex(&backend()
                            .encode_native_value(&Value::Bool(false))
                            .unwrap()));
                    }
                }
                let mut rebound = proof.clone();
                rebound[8..40].copy_from_slice(&Sha256::digest(reference::root(&envelope, &v)));
                rejected(&deployment, &v, &rebound);
            }
        }
        for (suffix, bytes) in [
            ("producer.json", serde_json::to_vec(&p).unwrap()),
            ("validator.json", serde_json::to_vec(&v).unwrap()),
            ("proof", proof),
        ] {
            std::fs::write(directory.join(format!("{name}.{suffix}")), bytes).unwrap();
        }
        println!("{name}: independent execution, reference and cleanup passed");
    }
}
fn main() {
    run(Path::new(
        &std::env::args().nth(1).expect("generated corpus directory"),
    ));
}
