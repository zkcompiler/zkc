//! Observe the executing backend's own registry and physical signatures.
use serde_json::{Value, json};
use zkc_backends::{Domain, EntryPolicy, NativeBackend, Policy, PublicInputs};
use zkc_runtime::interactive::{Backend, OperationBinding, PhysicalType};

fn respond(native: &NativeBackend, line: &[u8]) -> Option<Value> {
    let request = zkc_test_support::json_lines::request(line)?;
    if request.len() == 1 && request.get("implementations") == Some(&Value::Bool(true)) {
        let entries: Vec<_> = native.installed_implementations().into_iter()
            .map(|(implementation, contract)| json!({"contract":contract, "implementation":implementation})).collect();
        return Some(
            json!({"accepted":true, "discovery":"physical-registry", "implementations":entries}),
        );
    }
    // The backend does not own logical formation or logical-stage admission.
    if request.len() != 4 || !request.get("physical")?.as_bool()? {
        return None;
    }
    let arguments = request.get("arguments")?.as_array()?;
    if arguments.len() > 16 {
        return None;
    }
    let binding = OperationBinding {
        contract: request.get("contract")?.as_str()?.into(),
        implementation: request.get("implementation")?.as_str()?.into(),
        arguments: arguments
            .iter()
            .map(|v| v.as_str().map(str::to_owned))
            .collect::<Option<_>>()?,
    };
    let signature = native.binding_signature(&binding)?;
    Some(json!({"accepted":true, "physical":true,
        "inputs":signature.inputs.iter().map(PhysicalType::spelling).collect::<Vec<_>>(),
        "outputs":signature.outputs.iter().map(PhysicalType::spelling).collect::<Vec<_>>()}))
}
fn main() -> std::io::Result<()> {
    if std::env::args_os().len() != 1 {
        eprintln!("usage: backend_contract_conformance");
        std::process::exit(2);
    }
    let native = NativeBackend::new(
        Policy::default(),
        EntryPolicy::new(
            Domain::new("P", "session", "main", None),
            None,
            PublicInputs::LocalOnly,
        ),
        None,
    )
    .map_err(|error| std::io::Error::other(error.code))?;
    zkc_test_support::json_lines::run(|line| respond(&native, line))
}
