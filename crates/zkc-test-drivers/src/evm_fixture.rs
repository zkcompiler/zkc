//! Export native proofs for target-independent, positional codec fixtures.
//! Source compilation and canonical input construction stay in the test harness.
use serde::Deserialize;
use serde_json::{Value as Json, json};
use sha2::{Digest, Sha256};
use std::{collections::BTreeMap, path::PathBuf};
use zkc::{
    execution::PreparedData,
    proof::{Invocation, NativeDeployment, ProofInputs},
};
use zkc_test_support::hex;

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Requests {
    prover: Json,
    verifier: Json,
}

fn run() -> Result<(), Box<dyn std::error::Error>> {
    let mut args = std::env::args_os().skip(1);
    let artifact = PathBuf::from(args.next().ok_or("native deployment file")?);
    let requests = PathBuf::from(args.next().ok_or("positional requests file")?);
    let supplied = args.next().map(PathBuf::from);
    if args.next().is_some() {
        return Err("usage: evm_fixture DEPLOYMENT REQUESTS [PROOF]".into());
    }
    let bytes = std::fs::read(artifact)?;
    let envelope: Json = serde_json::from_slice(&bytes)?;
    let requests: Requests = serde_json::from_slice(&std::fs::read(requests)?)?;
    let identity = Sha256::digest(&bytes).into();
    // Independent admissions prevent producer values or resources from being
    // reused by verification. The digest comes from this fixture's compilation.
    let producer = NativeDeployment::admit(&bytes, &identity, Default::default())?;
    let verifier = NativeDeployment::admit(&bytes, &identity, Default::default())?;
    let (proof, produced) = if let Some(path) = supplied {
        (std::fs::read(path)?, None)
    } else {
        let input = ProofInputs::decode(&producer, &requests.prover, Invocation::Prove)?;
        let report = producer.execute(&input, Invocation::Prove)?;
        let proof = report
            .outcome
            .as_ref()
            .map_err(|e| format!("producer: {e}"))?;
        (proof.clone(), Some(report.diagnostics()))
    };
    let input = ProofInputs::decode(&verifier, &requests.verifier, Invocation::Verify(&proof))?;
    let report = verifier.execute(&input, Invocation::Verify(&proof))?;
    let outputs: BTreeMap<_, _> = report
        .outputs
        .as_ref()
        .into_iter()
        .flatten()
        .map(|(port, value)| {
            PreparedData::from_value(value.clone(), Default::default())
                .map(|data| (port.to_string(), hex(data.canonical_bytes())))
        })
        .collect::<Result<_, _>>()?;
    let public: Vec<_> = requests.verifier[1]
        .as_array()
        .ok_or("public rows")?
        .iter()
        .map(|r| r[2].clone())
        .collect();
    println!(
        "{}",
        json!({
            "format":"zkc.evm-native-fixture/0", "package_sha256":hex(&identity),
            "source":envelope[1], "descriptor":envelope[2],
            "public":public, "context":requests.verifier[3], "proof":hex(&proof),
            "producer":produced, "native":report.diagnostics(),
            "decision":report.verification_result(), "outputs":outputs,
            "native_error":report.outcome.as_ref().err(),
        })
    );
    Ok(())
}

fn main() {
    if let Err(error) = run() {
        eprintln!("{error}");
        std::process::exit(1);
    }
}
