mod mutations;
mod reference;
// Authored clients exercise the same compiler, host, Runner and crypto kernels.
use serde_json::{Value as Json, json};
use sha2::{Digest, Sha256};
use std::{collections::BTreeMap, path::Path};
use zkc_backends::{
    Domain, EntryPolicy, FieldArray, GroupPoint, NativeBackend, Policy, Scalar, Value,
};
use zkc_runtime::interactive::{Identity, LogicalType};
use zkc_tools::proof::{NativeDeployment, NativeProofReport, hex};
fn backend() -> NativeBackend {
    NativeBackend::new(
        Policy::default(),
        EntryPolicy::new(Domain::new("P", "test", "main", None), None),
        Default::default(),
    )
    .unwrap()
}
fn digest(bytes: &[u8]) -> String {
    hex(&Sha256::digest(bytes))
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
fn transitions(family: &str, n: u64) -> u64 {
    if family == "nested" {
        n + 8 * n * n.saturating_sub(1) / 2
    } else {
        1 + 3 * n
    }
}
fn inputs(envelope: &Json, family: &str, n: u64, producing: bool) -> Json {
    let role = if producing { "P" } else { "V" };
    let mapping = envelope[6]
        .as_array()
        .unwrap()
        .iter()
        .find(|r| r[0] == role)
        .unwrap();
    let codec = backend();
    let (a, b) = tables(n as usize);
    let claim: Scalar = a
        .iter()
        .zip(&b)
        .map(|(x, y)| {
            if family == "cubic" {
                *x * *x * *y
            } else {
                *x * *y
            }
        })
        .sum();
    let value = |port: &Json| {
        let p: usize = port.as_str().unwrap().parse().unwrap();
        let v = if family == "nested" {
            match p {
                0 => Value::Index(n),
                1 => Value::Curve(GroupPoint::generator()),
                2 => Value::Field(Scalar::from(3)),
                3 => Value::Curve(GroupPoint::generator().scale(Scalar::from(3))),
                _ => panic!("port"),
            }
        } else {
            match p {
                0 => Value::Index(n),
                1 => Value::table(&a, &Policy::default()).unwrap(),
                2 => Value::table(&b, &Policy::default()).unwrap(),
                3 => Value::Field(claim),
                5 => Value::FieldArray(
                    FieldArray::new(
                        LogicalType::field_array(Identity::Bls12381Fr, 3).unwrap(),
                        vec![Scalar::from(1), Scalar::from(2), Scalar::from(3)].into(),
                    )
                    .unwrap(),
                ),
                _ => panic!("port"),
            }
        };
        hex(&codec.encode_native_value(&v).unwrap())
    };
    let public: Vec<_> = envelope[2][4]
        .as_array()
        .unwrap()
        .iter()
        .map(|p| json!([p[0], p[1], value(&p[1])]))
        .collect();
    let data: Vec<_> = mapping[2]
        .as_array()
        .unwrap()
        .iter()
        .map(|p| json!([p[0], ["wire", value(&p[0])]]))
        .collect();
    let services: Vec<_> = mapping[4]
        .as_array()
        .unwrap()
        .iter()
        .map(|p| json!([p[0], "1000"]))
        .collect();
    json!([
        "zkc.native-proof-inputs/1",
        public,
        data,
        "",
        services,
        transitions(family, n).to_string()
    ])
}
fn clean(report: &NativeProofReport) {
    for resource in &report.resources {
        if resource["kind"] == "service" {
            assert_eq!(resource["leased"], false);
        }
    }
    assert!(
        !report
            .outcome
            .as_ref()
            .err()
            .is_some_and(|e| e.contains("cleanup") || e.contains("active-frames")),
        "{:?}",
        report.outcome
    );
}
fn execute(
    deployment: &NativeDeployment,
    input: &Json,
    proof: Option<&[u8]>,
    family: &str,
) -> NativeProofReport {
    let tapes = if family == "nested" && proof.is_none() {
        BTreeMap::from([(4, vec![Scalar::from(7); 1000])])
    } else {
        BTreeMap::new()
    };
    let report = deployment.execute_test(input, proof, tapes).unwrap();
    clean(&report);
    report
}
fn main() {
    let directory = std::env::args().nth(1).expect("fixture directory");
    let directory = Path::new(&directory);
    let manifest: Json =
        serde_json::from_slice(&std::fs::read(directory.join("manifest.json")).unwrap()).unwrap();
    let mut runs = 0;
    let mut proofs = BTreeMap::new();
    for case in manifest.as_array().unwrap() {
        let name = case["name"].as_str().unwrap();
        let family = case["family"].as_str().unwrap();
        let bytes = std::fs::read(directory.join(format!("{name}.deployment"))).unwrap();
        let envelope: Json = serde_json::from_slice(&bytes).unwrap();
        let deployment = NativeDeployment::admit(&bytes, &digest(&bytes), Default::default())
            .unwrap_or_else(|e| panic!("{name}: {e}"));
        let counts = case["count"]
            .as_u64()
            .map_or_else(|| vec![0, 1, 2, 3, 8], |n| vec![n]);
        for n in counts {
            let p = inputs(&envelope, family, n, true);
            let v = inputs(&envelope, family, n, false);
            let report = execute(&deployment, &p, None, family);
            assert!(report.outcome.is_ok(), "{name}/{n}: {:?}", report.outcome);
            let expected = transitions(family, n);
            assert_eq!(
                report
                    .resources
                    .iter()
                    .find(|r| r["kind"] == "capability")
                    .unwrap()["transitions"],
                json!(expected),
                "{name}/{n}"
            );
            let messages = if family == "nested" {
                n + 4 * n * n.saturating_sub(1) / 2
            } else {
                1 + n
            };
            assert_eq!(report.messages, messages as usize);
            let proof = report.outcome.unwrap();
            reference::verify(&envelope, &p, &proof, family, n);
            let key = (
                envelope[1].as_str().unwrap().to_owned(),
                family.to_owned(),
                envelope[2][1][5].as_str().unwrap().to_owned(),
                n,
            );
            if let Some(previous) = proofs.insert(key, proof.clone()) {
                assert_eq!(previous, proof, "lowering changed proof bytes");
            }
            mutations::proof(&deployment, &v, &proof, family, n);
            if family != "nested" {
                mutations::false_claim(&deployment, &envelope, &v, &proof);
            }
            if name == "nested_0" && n == 3 {
                mutations::nested(&envelope, &v, &proof);
            }
            let accepted = execute(&deployment, &v, Some(&proof), family);
            assert!(
                accepted.outcome.is_ok(),
                "{name}/{n}: {:?}",
                accepted.outcome
            );
            assert_eq!(
                accepted
                    .resources
                    .iter()
                    .find(|r| r["kind"] == "capability")
                    .unwrap()["transitions"],
                json!(expected)
            );
            assert_eq!(accepted.binding, report.binding);
            for (kind, malformed) in [
                ("truncated", proof[..proof.len() - 1].to_vec()),
                ("trailing", [proof.clone(), vec![0]].concat()),
            ] {
                let rejected = execute(&deployment, &v, Some(&malformed), family);
                assert!(rejected.outcome.is_err(), "{name}/{n}/{kind}");
            }
            if expected > 0 {
                let mut poor = v.clone();
                poor[5] = json!((expected - 1).to_string());
                assert!(
                    execute(&deployment, &poor, Some(&proof), family)
                        .outcome
                        .unwrap_err()
                        .contains("exhausted")
                );
            }
            if n == 3 && !name.contains("plain") && !name.contains("release") {
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
            }
            runs += 1;
        }
        if case["count"].is_null() && (name.ends_with("_0") || name.ends_with("_1")) {
            let too_many = inputs(&envelope, family, 9, true);
            assert!(
                execute(&deployment, &too_many, None, family)
                    .outcome
                    .unwrap_err()
                    .contains("loop-count-bound")
            );
        }
    }
    println!("{runs} independent iterated proof runs and negative controls passed");
}
