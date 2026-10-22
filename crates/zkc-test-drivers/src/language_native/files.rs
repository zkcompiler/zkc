//! Setup-bearing file inputs use the same Host and authenticated key loading.
use serde_json::{Value as Json, json};
use sha2::{Digest, Sha256};
use std::path::Path;
use zkc_tools::{
    entry::{self, FunctionInterface, NamedValues, Package, ProofRequest, SetupAuthority},
    execution::Capacity,
};
fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}
fn named(values: &NamedValues, registry: &zkc_native::SetupRegistry) -> Json {
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
    common.extend([format!("--public={public_file}"), "--allow-authored".into()]);
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
    save(directory, "cli-P.json", &producer_values);
    save(directory, "cli-V.json", &verifier_values);
    let bytes = std::fs::read(directory.join("pcs-setup-Run.zkpkg")).unwrap();
    let package =
        Package::capture(&bytes, &Sha256::digest(&bytes).into(), Package::MAX_BYTES).unwrap();
    let interface = FunctionInterface::read(&package).unwrap();
    let mut arguments = serde_json::Map::new();
    let mut external = serde_json::Map::new();
    for role in &interface.signature().parameters[0].schema.fields {
        let mut supplied = match role.name.as_str() {
            "P" => producer_values.as_object().unwrap().clone(),
            "V" => verifier_values.as_object().unwrap().clone(),
            _ => panic!("unexpected setup role"),
        };
        let data = role
            .schema
            .fields
            .iter()
            .map(|field| (field.name.clone(), supplied.remove(&field.name).unwrap()))
            .collect::<serde_json::Map<_, _>>();
        arguments.insert(role.name.clone(), json!(data));
        external.insert(role.name.clone(), json!(supplied));
    }
    let arguments_file = save(
        directory,
        "cli-run-arguments.json",
        &json!({"inputs": arguments}),
    );
    let requirements = FunctionInterface::deployment_interfaces(&package).unwrap();
    let [deployment] = requirements.as_slice() else {
        panic!("expected one setup-bearing joint child");
    };
    assert_eq!(deployment.operation(), "run");
    let id = deployment.id();
    let setup_files = producer
        .setups
        .keys()
        .map(|slot| (slot.clone(), format!("cli-vk-{slot}.bin")))
        .collect::<std::collections::BTreeMap<_, _>>();
    let context_file = save(
        directory,
        "cli-run-invocations.json",
        &json!({
            "format": "zkc.entry-invocations/0",
            "deployments": {id: {
                "operation": "run",
                "session": "setup_files",
                "authority": serde_json::from_slice::<Json>(&std::fs::read(&authority_file).unwrap()).unwrap(),
                "services": {}, "setups": setup_files, "inputs": external,
            }},
        }),
    );
    let mut running = target(directory, "pcs-setup-Run.zkpkg");
    running.extend([
        format!("--input={arguments_file}"),
        format!("--invocations={context_file}"),
        "--no-results".into(),
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
