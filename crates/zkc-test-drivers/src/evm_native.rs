//! Produce real SDK proofs and export the exact canonical EVM input tuple.
//! This adapter has no Sumcheck implementation or EVM engine dependency.
use serde_json::{Value as Json, json};
use sha2::{Digest, Sha256};
use std::{collections::BTreeMap, path::PathBuf};
use zkc::{
    entry::{NamedValues, ProofEntry, ProofOptions, ProofRequest},
    evm::{Artifact, Invocation},
    execution::{InputValue, PreparedData},
    project::{Compiler, EntryKind, Project, Selection},
};
use zkc_cpu::{Scalar, Value};
use zkc_test_support::{hex, unhex};

fn main() {
    if let Err(error) = run() {
        eprintln!("{error:?}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), Box<dyn std::error::Error>> {
    let mut args = std::env::args().skip(1);
    let mut options = BTreeMap::new();
    while let Some(key) = args.next() {
        if ![
            "--compiler",
            "--project",
            "--entry",
            "--rounds",
            "--context",
            "--budget",
            "--values",
            "--claim",
            "--proof",
            "--evm-artifact",
            "--evm-sha256",
        ]
        .contains(&key.as_str())
            || options.contains_key(&key)
        {
            return Err(format!("unknown or duplicate option: {key}").into());
        }
        let value = args.next().ok_or_else(|| format!("missing value: {key}"))?;
        options.insert(key, value);
    }
    let required = |name: &str| {
        options
            .get(name)
            .ok_or_else(|| format!("required option: {name}"))
    };
    if options.contains_key("--evm-artifact") != options.contains_key("--evm-sha256") {
        return Err("--evm-artifact and --evm-sha256 must be supplied together".into());
    }
    let compiler = Compiler::new(required("--compiler")?)?;
    let project = Project::load(required("--project")?)?;
    let entry = required("--entry")?;
    let rounds: u32 = required("--rounds")?.parse()?;
    // Include the first one-over-bound control without permitting huge fixtures.
    if rounds > 11 {
        return Err("fixture round limit is 11".into());
    }
    let numbers: Vec<u64> = if let Some(path) = options.get("--values") {
        serde_json::from_slice(&std::fs::read(path)?)?
    } else {
        (1..=(1u64 << rounds)).collect()
    };
    if numbers.len() > 2048 {
        return Err("fixture table limit is 2048".into());
    }
    let fields: Vec<_> = numbers.iter().map(|n| Scalar::from(*n)).collect();
    let claim: Scalar = if let Some(value) = options.get("--claim") {
        Scalar::from(value.parse::<u64>()?)
    } else {
        fields.iter().copied().sum()
    };
    let context = options
        .get("--context")
        .map(|value| {
            if !value.len().is_multiple_of(2) || !value.bytes().all(|c| c.is_ascii_hexdigit()) {
                return Err("invalid context hex");
            }
            Ok(unhex(value))
        })
        .transpose()?
        .unwrap_or_default();
    let budget: u64 = options
        .get("--budget")
        .map(|value| value.parse())
        .transpose()?
        .unwrap_or(64);
    let prepared: BTreeMap<String, PreparedData> = [
        ("values", Value::Vector(fields.into())),
        ("claim", Value::Field(claim)),
        ("rounds", Value::Index(rounds.into())),
    ]
    .into_iter()
    .map(|(name, value)| {
        PreparedData::from_value(value, Default::default()).map(|data| (name.into(), data))
    })
    .collect::<Result<_, _>>()?;
    let package = compiler.compile(
        &project,
        Selection {
            name: Some(entry),
            kind: Some(EntryKind::Proof),
        },
        project.settings(None, &Default::default())?.options(),
    )?;
    let envelope: Json = serde_json::from_str(package.artifact())?;
    let descriptor = &envelope[2];
    if descriptor[1][5] != "hash-chain.keccak256.bls12-381.fr64be/0" {
        return Err("fixture requires the accepted managed Keccak construction".into());
    }
    let public_wires: Vec<_> = ["values", "claim", "rounds"]
        .iter()
        .map(|name| hex(prepared[*name].canonical_bytes()))
        .collect();
    // The accepted fixture declares values, claim, rounds in this exact order.
    let ports = descriptor[4].as_array().ok_or("descriptor public ports")?;
    if ports.len() != 3 {
        return Err("fixture requires exactly three public ports".into());
    }
    for (port, (number, logical)) in ports.iter().zip([
        ("0", "vector:bls12-381.fr"),
        ("1", "field:bls12-381.fr"),
        ("2", "index"),
    ]) {
        if port[0] != descriptor[1][3] || port[1] != number || port[2] != logical {
            return Err(
                "fixture public port order or type differs from values, claim, rounds".into(),
            );
        }
    }
    let public_rows: Vec<_> = ports
        .iter()
        .zip(&public_wires)
        .map(|(port, wire)| json!([port[0], port[1], port[2], wire]))
        .collect();
    let root_tree = json!([
        "zkc.native-proof-binding/0",
        "sha256",
        descriptor[2],
        envelope[1],
        descriptor[1][1],
        descriptor[1][2],
        descriptor[1][3],
        descriptor,
        public_rows,
        hex(&context),
    ]);
    let root = zkc_format::logical::encode_tree(&root_tree)?;
    let package_sha256 = hex(package.identity());
    // Separate admissions: the verifier receives no producer state or witness.
    let prover = ProofEntry::admit(package.clone(), ProofOptions::default(), Default::default())?;
    let verifier = ProofEntry::admit(package, ProofOptions::default(), Default::default())?;
    let request = || ProofRequest {
        public: prepared
            .iter()
            .map(|(name, data)| (name.clone(), InputValue::Prepared(data.clone()).into()))
            .collect::<NamedValues>(),
        private: Default::default(),
        context: context.clone(),
        transcript_budget: Some(budget),
        setups: BTreeMap::new(),
    };
    let (proof, produced) = if let Some(path) = options.get("--proof") {
        (std::fs::read(PathBuf::from(path))?, None)
    } else {
        let report = prover.prove(request())?;
        let diagnostics = report.native.diagnostics();
        if !report.is_success() {
            println!("{}", json!({"phase":"producer", "native":diagnostics}));
            return Ok(());
        }
        (
            report.native.outcome.as_ref().unwrap().clone(),
            Some(diagnostics),
        )
    };
    let checked = verifier.verify(request(), &proof)?;
    let outputs: BTreeMap<_, _> = checked
        .outputs
        .as_ref()
        .map(|outputs| {
            outputs
                .iter()
                .map(|(name, value)| (name.clone(), format!("{value:?}")))
                .collect()
        })
        .unwrap_or_default();
    let binding = hex(&Sha256::digest(&root));
    if checked.native.binding != binding {
        return Err("exported invocation root differs from native binding".into());
    }
    if proof.len() >= 40
        && &proof[..8] == b"ZKCPRF00"
        && checked.verification_result() == Some(true)
        && proof[8..40] != Sha256::digest(&root)[..]
    {
        return Err("exported invocation root differs from native binding".into());
    }
    let evm = if let Some(directory) = options.get("--evm-artifact") {
        let artifact = Artifact::capture(directory, required("--evm-sha256")?)?;
        let source = artifact.source()?;
        if source.metadata()["source_sha256"] != envelope[1]
            || source.metadata()["descriptor"] != *descriptor
            || source.entry() != entry
        {
            return Err("native and captured EVM subjects differ".into());
        }
        let public_bytes: Vec<_> = public_wires.iter().map(|wire| unhex(wire)).collect();
        let public_inputs: Vec<_> = public_bytes.iter().map(Vec::as_slice).collect();
        let calldata = artifact.calldata(Invocation {
            public_inputs: &public_inputs,
            context: &context,
            proof: &proof,
        })?;
        Some(json!({
            "manifest_sha256": artifact.identity(), "manifest": artifact.manifest(),
            "creation_sha256": hex(&Sha256::digest(artifact.creation_bytecode())),
            "runtime_sha256": hex(&Sha256::digest(artifact.runtime_bytecode())),
            "creation": hex(artifact.creation_bytecode()),
            "runtime": hex(artifact.runtime_bytecode()), "calldata": hex(&calldata),
        }))
    } else {
        None
    };
    println!(
        "{}",
        json!({
            "format":"zkc.evm-native-fixture/0", "package_sha256":package_sha256,
            "source":envelope[1], "descriptor":descriptor, "public":public_wires,
            "public_rows":public_rows, "context":hex(&context), "proof":hex(&proof),
            "invocation_root":hex(&root), "invocation_tree":root_tree,
            "binding_sha256":binding, "rounds":rounds, "transcript_budget":budget,
            "producer":produced, "native":checked.native.diagnostics(),
            "native_error":checked.native.outcome.as_ref().err().map(ToString::to_string),
            "output_error":checked.output_error,
            "decision":checked.verification_result(), "outputs":outputs,
            "evm":evm,
        })
    );
    Ok(())
}
