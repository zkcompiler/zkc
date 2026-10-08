//! Setup-bearing file jobs use the same named Host and checked native key loading.
use serde_json::{Value as Json, json};
use sha2::{Digest, Sha256};
use std::path::Path;
use zkc_tools::{
    artifact::native::NativeCapacity,
    entry::{self, NamedValues, ProofRequest, SetupAuthority},
};
fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}
fn named(values: &NamedValues) -> Json {
    let bytes = entry::files::proof_outputs(values, NativeCapacity::default()).unwrap();
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
    let mut imports = Vec::new();
    for (i, (bytes, pin)) in keys.into_iter().enumerate() {
        let name = format!("pk{i}");
        producer.inputs.inputs.remove(&name).unwrap();
        let path = directory.join(format!("cli-pk-{i}.bin"));
        std::fs::write(&path, bytes).unwrap();
        imports.push((name, json!({"path":path,"sha256":hex(&pin)})));
    }
    let mut producer_values = named(&producer.inputs.inputs);
    for (name, value) in imports {
        producer_values[&name] = value;
    }
    let material: serde_json::Map<_, _> = producer
        .setups
        .iter()
        .map(|(k, v)| (k.clone(), json!(hex(v))))
        .collect();
    let public = named(&producer.public);
    for name in public.as_object().unwrap().keys() {
        producer_values.as_object_mut().unwrap().remove(name);
    }
    let verifier_values = named(&verifier.inputs.inputs);
    let producer_file = save(
        directory,
        "cli-producer.json",
        &json!({"format":"zkc.entry-proof/1","public":public,"inputs":producer_values,"setups":material}),
    );
    let verifier_file = save(
        directory,
        "cli-verifier.json",
        &json!({"format":"zkc.entry-proof/1","public":public,"setups":material}),
    );
    let authority_file = save(
        directory,
        "cli-authority.json",
        &json!({"format":"zkc.entry-setups/1","keys":authority.keys.iter().map(|(k,v)|(k.clone(),hex(v))).collect::<std::collections::BTreeMap<_,_>>()}),
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
    let produced = entry::cli::run("prove", &args);
    assert_eq!(produced["status"], "produced", "{produced}");
    args[2] = verifier_file;
    let checked = entry::cli::run("verify", &args);
    assert_eq!(checked["status"], "accepted", "{checked}");
    producer_values
        .as_object_mut()
        .unwrap()
        .extend(public.as_object().unwrap().clone());
    let request = save(
        directory,
        "cli-run.json",
        &json!({"format":"zkc.entry-run/1","session":"setup_files","roles":{"P":{"inputs":producer_values},"V":{"inputs":verifier_values}},"setups":material}),
    );
    let package = directory.join("pcs-setup-Run.entry");
    let bytes = std::fs::read(&package).unwrap();
    let result = entry::cli::run(
        "run-entry",
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
    let refused = entry::cli::run("verify", &args);
    assert_eq!(refused["code"], "key-mismatch", "{refused}");
    wrong["keys"]["first"] = json!(hex(&authority.keys["first"]));
    std::fs::write(&authority_file, wrong.to_string()).unwrap();
}
