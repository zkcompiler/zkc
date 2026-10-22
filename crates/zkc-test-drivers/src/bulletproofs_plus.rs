//! Execute ordinary source Bulletproofs+ with a recorded private coin tape.
use serde_json::{Value as Json, json};
use sha2::{Digest, Sha256};
use std::{collections::BTreeMap, path::Path};
use zkc::proof::{Invocation, NativeDeployment, ProofInputs};
use zkc_native::{Domain, EntryPolicy, NativeBackend, Policy, RistrettoScalar, Value};
use zkc_test_support::{hex, unhex};

fn main() {
    let args: Vec<_> = std::env::args().collect();
    assert_eq!(args.len(), 4, "deployment case-json output-proof");
    let encoded = std::fs::read(&args[1]).unwrap();
    let envelope: Json = serde_json::from_slice(&encoded).unwrap();
    let deployment = NativeDeployment::admit(
        &encoded,
        &Sha256::digest(&encoded).into(),
        Default::default(),
    )
    .unwrap();
    let case: Json = serde_json::from_slice(&std::fs::read(&args[2]).unwrap()).unwrap();
    let codec = NativeBackend::new(
        Policy::default(),
        EntryPolicy::new(Domain::new("P", "test", "main", None), None),
        Default::default(),
    )
    .unwrap();
    let amounts: Vec<_> = case["values"]
        .as_array()
        .unwrap()
        .iter()
        .map(|v| v.as_u64().unwrap())
        .collect();
    let masks: Vec<_> = case["masks"]
        .as_array()
        .unwrap()
        .iter()
        .map(|v| zkc_kernels::dalek::ristretto255::parse_decimal(v.as_str().unwrap()).unwrap())
        .collect();
    let commitments = unhex(case["commitments"].as_str().unwrap());
    let rounds = 6 + amounts.len().next_power_of_two().trailing_zeros() as u64;
    let values = [
        Value::Bytes(commitments.into()),
        Value::Index(rounds),
        Value::Indices(amounts.into()),
        Value::RistrettoVector(masks.into()),
    ];
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
        .find(|r| r[0] == envelope[2][1][2])
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
        .map(|p| json!([p[0], "64"]))
        .collect();
    let input = json!(["zkc.native-proof-inputs/0", public, data, "", services, "0"]);
    let input = ProofInputs::decode(&deployment, &input, Invocation::Prove).unwrap();
    let coins: Vec<RistrettoScalar> = case["coins"]
        .as_array()
        .unwrap()
        .iter()
        .map(|v| zkc_kernels::dalek::ristretto255::parse_decimal(v.as_str().unwrap()).unwrap())
        .collect();
    let expected_draws = coins.len();
    let port = role[4][0][0].as_str().unwrap().parse().unwrap();
    let report = deployment
        .execute_test(&input, Invocation::Prove, BTreeMap::from([(port, coins)]))
        .unwrap();
    assert!(
        report.cleanup_errors.is_empty(),
        "{:?}",
        report.cleanup_errors
    );
    let diagnostics = report.diagnostics();
    assert_eq!(
        diagnostics["resources"][0]["state"]["transitions"],
        expected_draws
    );
    eprintln!("{diagnostics}");
    let proof = match report.outcome {
        Ok(proof) => proof,
        Err(error) => {
            println!(
                "{}",
                json!({"status":"refused", "error":format!("{error:?}")})
            );
            std::process::exit(1);
        }
    };
    std::fs::write(Path::new(&args[3]), &proof).unwrap();
    println!("{}", json!({"bytes":proof.len()}));
}
