//! Setup-bearing file inputs use the same Host and authenticated key loading.
use serde_json::{Value as Json, json};
use sha2::{Digest, Sha256};
use std::path::Path;
use zkc_tools::{
    entry::{self, NamedValues, ProofRequest, SetupAuthority},
    execution::Capacity,
};
fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}
fn named(values: &NamedValues, registry: &zkc_backends::SetupRegistry) -> Json {
    let bytes = entry::files::proof_outputs(values, Capacity::default(), registry.clone()).unwrap();
    serde_json::from_slice::<Json>(&bytes).unwrap()["values"].take()
}
fn save(directory: &Path, name: &str, value: &Json) -> String {
    let path = directory.join(name);
    std::fs::write(&path, value.to_string()).unwrap();
    path.to_string_lossy().into_owned()
}
fn target(directory: &Path, name: &str) -> Vec<String> {
    let package = directory.join(name);
    vec![
        format!("--package={}", package.display()),
        format!(
            "--sha256={}",
            hex(&Sha256::digest(std::fs::read(package).unwrap()))
        ),
    ]
}
pub(super) fn setups(
    directory: &Path,
    mut producer: ProofRequest,
    verifier: ProofRequest,
    authority: SetupAuthority,
    keys: Vec<(Vec<u8>, [u8; 32])>,
) {
    let registry =
        entry::files::output_setups(&producer.setups, &authority, Capacity::default()).unwrap();
    let mut imports = Vec::new();
    for (i, (bytes, pin)) in keys.into_iter().enumerate() {
        let name = format!("pk{i}");
        producer.private.inputs.remove(&name).unwrap();
        let file = format!("cli-pk-{i}.bin");
        std::fs::write(directory.join(&file), bytes).unwrap();
        imports.push((name, json!({"file":file,"fingerprint":hex(&pin)})));
    }
    let mut producer_values = named(&producer.private.inputs, &registry);
    for (name, value) in imports {
        producer_values[&name] = value;
    }
    let public = named(&producer.public, &registry);
    for name in public.as_object().unwrap().keys() {
        producer_values.as_object_mut().unwrap().remove(name);
    }
    let mut verifier_values = named(&verifier.private.inputs, &registry);
    let public_file = save(directory, "cli-public.json", &public);
    let witness_file = save(directory, "cli-witness.json", &producer_values);
    let authority_file = save(
        directory,
        "cli-authority.json",
        &json!({"format":"zkc.entry-setups/0","keys":authority.keys.iter().map(|(k,v)|(k.clone(),hex(v))).collect::<std::collections::BTreeMap<_,_>>()}),
    );
    let mut settings = vec![format!("--setups={authority_file}")];
    for (slot, bytes) in &producer.setups {
        let path = directory.join(format!("cli-vk-{slot}.bin"));
        std::fs::write(&path, bytes).unwrap();
        settings.push(format!("--key={slot}={}", path.display()));
    }
    let proof = directory.join("cli-pcs-proof.bin");
    let mut common = target(directory, "pcs-setup-Prove.zkpkg");
    common.extend(settings.clone());
    common.extend([
        format!("--public={public_file}"),
        "--allow-header-only".into(),
    ]);
    let mut proving = common.clone();
    proving.extend([
        format!("--witness={witness_file}"),
        format!("--output={}", proof.display()),
    ]);
    let mut verifying = common;
    verifying.push(format!("--proof={}", proof.display()));
    let produced = zkc_tools::cli::run("prove", &proving);
    assert_eq!(produced["status"], "produced", "{produced}");
    let checked = zkc_tools::cli::run("verify", &verifying);
    assert_eq!(checked["status"], "accepted", "{checked}");

    // Output setup preparation precedes private-key loading when exporting results.
    let mut bad = producer_values.clone();
    bad["pk0"]["fingerprint"] = json!("00".repeat(32));
    save(directory, "cli-witness.json", &bad);
    let vk = directory.join("cli-vk-first.bin");
    let valid_vk = std::fs::read(&vk).unwrap();
    std::fs::write(&vk, [0]).unwrap();
    let results = directory.join("cli-precedence-results.json");
    std::fs::write(&results, b"previous results").unwrap();
    let previous_proof = std::fs::read(&proof).unwrap();
    let mut checked_args = proving.clone();
    checked_args.push(format!("--results={}", results.display()));
    for code in ["invalid-encoding", "key-mismatch"] {
        let refused = zkc_tools::cli::run("prove", &checked_args);
        assert_eq!(refused["code"], code, "{refused}");
        assert_eq!(refused["phase"], "inputs");
        assert_eq!(std::fs::read(&proof).unwrap(), previous_proof);
        assert_eq!(std::fs::read(&results).unwrap(), b"previous results");
        std::fs::write(&vk, &valid_vk).unwrap();
    }
    save(directory, "cli-witness.json", &producer_values);
    let repaired = zkc_tools::cli::run("prove", &checked_args);
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
    let p = save(directory, "cli-P.json", &producer_values);
    let v = save(directory, "cli-V.json", &verifier_values);
    let mut running = target(directory, "pcs-setup-Run.zkpkg");
    running.extend(settings);
    running.extend([
        "--session=setup_files".into(),
        format!("--input=P={p}"),
        format!("--input=V={v}"),
    ]);
    let result = zkc_tools::cli::run("run", &running);
    assert_eq!(result["status"], "executed", "{result}");
    let mut wrong: Json = serde_json::from_slice(&std::fs::read(&authority_file).unwrap()).unwrap();
    wrong["keys"]["first"] = json!("00".repeat(32));
    std::fs::write(&authority_file, wrong.to_string()).unwrap();
    let refused = zkc_tools::cli::run("verify", &verifying);
    assert_eq!(refused["code"], "key-mismatch", "{refused}");
    wrong["keys"]["first"] = json!(hex(&authority.keys["first"]));
    std::fs::write(&authority_file, wrong.to_string()).unwrap();
}
