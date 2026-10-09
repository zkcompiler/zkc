//! Setup-bearing file jobs use the same named Host and checked native key loading.
use serde_json::{Value as Json, json};
use sha2::{Digest, Sha256};
use std::path::Path;
use zkc_tools::{
    entry::{self, NamedValues, ProofRequest, SetupAuthority},
    proof::NativeCapacity,
};
fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}
fn named(values: &NamedValues, registry: &zkc_backends::SetupRegistry) -> Json {
    let bytes =
        entry::files::proof_outputs(values, NativeCapacity::default(), registry.clone()).unwrap();
    serde_json::from_slice::<Json>(&bytes).unwrap()["values"].take()
}
fn save(directory: &Path, name: &str, value: &Json) -> String {
    let path = directory.join(name);
    std::fs::write(&path, value.to_string()).unwrap();
    path.to_string_lossy().into_owned()
}
pub(super) fn setups(
    directory: &Path,
    mut producer: ProofRequest,
    verifier: ProofRequest,
    authority: SetupAuthority,
    keys: Vec<(Vec<u8>, [u8; 32])>,
) {
    let registry =
        entry::files::output_setups(&producer.setups, &authority, NativeCapacity::default())
            .unwrap();
    let mut imports = Vec::new();
    for (i, (bytes, pin)) in keys.into_iter().enumerate() {
        let name = format!("pk{i}");
        producer.private.inputs.remove(&name).unwrap();
        let path = directory.join(format!("cli-pk-{i}.bin"));
        std::fs::write(&path, bytes).unwrap();
        imports.push((name, json!({"path":path,"sha256":hex(&pin)})));
    }
    let mut producer_values = named(&producer.private.inputs, &registry);
    for (name, value) in imports {
        producer_values[&name] = value;
    }
    let material: serde_json::Map<_, _> = producer
        .setups
        .iter()
        .map(|(k, v)| (k.clone(), json!(hex(v))))
        .collect();
    let public = named(&producer.public, &registry);
    for name in public.as_object().unwrap().keys() {
        producer_values.as_object_mut().unwrap().remove(name);
    }
    let mut verifier_values = named(&verifier.private.inputs, &registry);
    let producer_file = save(
        directory,
        "cli-producer.json",
        &json!({"format":"zkc.entry-proof","public":public,"inputs":producer_values,"setups":material}),
    );
    let verifier_file = save(
        directory,
        "cli-verifier.json",
        &json!({"format":"zkc.entry-proof","public":public,"setups":material}),
    );
    let authority_file = save(
        directory,
        "cli-authority.json",
        &json!({"format":"zkc.entry-setups","keys":authority.keys.iter().map(|(k,v)|(k.clone(),hex(v))).collect::<std::collections::BTreeMap<_,_>>()}),
    );
    let package = directory.join("pcs-setup-Prove.entry");
    let bytes = std::fs::read(&package).unwrap();
    let proof = directory.join("cli-pcs-proof.bin");
    let mut args = vec![
        package.to_string_lossy().into_owned(),
        hex(&Sha256::digest(bytes)),
        producer_file,
        proof.to_string_lossy().into_owned(),
        format!("--setups={authority_file}"),
        "--allow-header-only".into(),
    ];
    let produced = zkc_tools::cli::run("prove", &args);
    assert_eq!(produced["status"], "produced", "{produced}");
    args[2] = verifier_file;
    let checked = zkc_tools::cli::run("verify", &args);
    assert_eq!(checked["status"], "accepted", "{checked}");
    // Output setup preparation precedes private-key loading when results are
    // requested. Repairing the first failure exposes the independent input pin.
    let valid: Json =
        serde_json::from_slice(&std::fs::read(directory.join("cli-producer.json")).unwrap())
            .unwrap();
    let mut bad = valid.clone();
    bad["setups"]["first"] = json!("00");
    bad["inputs"]["pk0"]["sha256"] = json!("00".repeat(32));
    let results = directory.join("cli-precedence-results.json");
    std::fs::write(&results, b"previous results").unwrap();
    let previous_proof = std::fs::read(&proof).unwrap();
    let mut check_args = args.clone();
    check_args.push(format!("--results={}", results.display()));
    for code in ["invalid-encoding", "key-mismatch"] {
        check_args[2] = save(directory, "cli-precedence-inputs.json", &bad);
        let refused = zkc_tools::cli::run("prove", &check_args);
        assert_eq!(refused["code"], code, "{refused}");
        assert_eq!(refused["phase"], "inputs");
        assert_eq!(std::fs::read(&proof).unwrap(), previous_proof);
        assert_eq!(std::fs::read(&results).unwrap(), b"previous results");
        bad["setups"] = valid["setups"].clone();
    }
    check_args[2] = save(directory, "cli-precedence-inputs.json", &valid);
    let repaired = zkc_tools::cli::run("prove", &check_args);
    assert_eq!(repaired["status"], "produced", "{repaired}");
    assert_eq!(
        repaired["publication"]["published"],
        json!(["proof", "results"])
    );
    producer_values
        .as_object_mut()
        .unwrap()
        .extend(public.as_object().unwrap().clone());
    verifier_values
        .as_object_mut()
        .unwrap()
        .extend(public.as_object().unwrap().clone());
    let request = save(
        directory,
        "cli-run.json",
        &json!({"format":"zkc.entry-run","session":"setup_files","roles":{"P":{"inputs":producer_values},"V":{"inputs":verifier_values}},"setups":material}),
    );
    let package = directory.join("pcs-setup-Run.entry");
    let bytes = std::fs::read(&package).unwrap();
    let result = zkc_tools::cli::run(
        "run",
        &[
            package.to_string_lossy().into_owned(),
            hex(&Sha256::digest(bytes)),
            request,
            format!("--setups={authority_file}"),
        ],
    );
    assert_eq!(result["status"], "executed", "{result}");
    let mut wrong: Json = serde_json::from_slice(&std::fs::read(&authority_file).unwrap()).unwrap();
    wrong["keys"]["first"] = json!("00".repeat(32));
    std::fs::write(&authority_file, wrong.to_string()).unwrap();
    let refused = zkc_tools::cli::run("verify", &args);
    assert_eq!(refused["code"], "key-mismatch", "{refused}");
    wrong["keys"]["first"] = json!(hex(&authority.keys["first"]));
    std::fs::write(&authority_file, wrong.to_string()).unwrap();
}
