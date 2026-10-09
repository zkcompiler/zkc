//! Bounded JSON-lines observations of independent runtime admission/signatures.
use serde_json::{Value, json};
use sha2::{Digest, Sha256};
use std::io;
use zkc_backends::{Domain, EntryPolicy, NativeBackend, Policy};
use zkc_runtime::interactive::{
    AdmissionError, KernelSignature, LogicalType, OperationBinding, PhysicalType, admit_supplied,
};
use zkc_tools::entry::{Interface, Package};

type LogicalResolver =
    fn(&OperationBinding) -> Result<KernelSignature<LogicalType>, AdmissionError>;

// Test-only resolver drift; no declaration, admission rule or serialized result
// is replaced. Physical resolution continues through the installed runtime.
fn divergent_logical_resolver(
    binding: &OperationBinding,
) -> Result<KernelSignature<LogicalType>, AdmissionError> {
    let mut signature = binding.logical_signature()?;
    if binding.contract == "field.add" {
        signature.outputs = vec![LogicalType::parse("bool")?];
    }
    Ok(signature)
}

// Construct only SSA plumbing. Production admission owns attribute syntax,
// ranges, field selection, affine uses and installed backend agreement.
fn operation_program(binding: &OperationBinding, attributes: &[Value]) -> Option<Vec<u8>> {
    let signature = binding.signature().ok()?;
    let inputs: Vec<_> = signature
        .inputs
        .iter()
        .enumerate()
        .map(|(i, ty)| json!([format!("in_{i}"), ty.spelling()]))
        .collect();
    let arguments: Vec<_> = (0..inputs.len()).map(|i| format!("in_{i}")).collect();
    let outputs: Vec<_> = signature
        .outputs
        .iter()
        .map(PhysicalType::spelling)
        .collect();
    let results: Vec<_> = (0..outputs.len()).map(|i| format!("out_{i}")).collect();
    serde_json::to_vec(&json!([
        "zkc.program/2",
        [[
            "probe_binding",
            binding.contract,
            binding.arguments,
            binding.implementation
        ]],
        [[
            "function",
            "probe",
            inputs,
            outputs,
            [
                [
                    "op",
                    "operation",
                    "probe_binding",
                    attributes,
                    arguments,
                    results
                ],
                ["return", results]
            ],
            ["Probe", []]
        ]],
        [[
            "participant",
            "mainP",
            "root",
            "P",
            [],
            [],
            [["return", []]],
            []
        ]],
        [["entry", "main", [["P", "mainP"]]]]
    ]))
    .ok()
}

fn observed(result: Result<(), impl std::fmt::Display>) -> Value {
    match result {
        Ok(()) => json!({"accepted": true, "admitted": true}),
        Err(error) => json!({"accepted": true, "admitted": false, "error": error.to_string()}),
    }
}

fn entry_interface(text: &str) -> Value {
    // Authentication binds this exact inert package. Interface::read validates
    // metadata only; these bytes make no source/artifact correspondence claim.
    let bytes = serde_json::to_vec(&json!({
        "format": "zkc.entry/1", "original": "conformance original",
        "interface": text, "artifact": "conformance metadata only",
        "options": {"simplify": true, "release_storage": false}
    }))
    .expect("inert package serialization");
    let package = Package::capture(&bytes, &Sha256::digest(&bytes).into(), Package::MAX_BYTES)
        .expect("well-formed authenticated test package");
    observed(Interface::read(&package).map(|_| ()))
}

fn respond(native: &NativeBackend, line: &[u8], resolve: LogicalResolver) -> Option<Value> {
    let request = zkc_test_support::json_lines::request(line)?;
    if request.len() == 1 && request.contains_key("entry_interface") {
        return Some(entry_interface(request.get("entry_interface")?.as_str()?));
    }
    if request.len() == 1 && request.get("implementations") == Some(&Value::Bool(true)) {
        let entries: Vec<_> = OperationBinding::installed_implementations()
            .ok()?
            .into_iter()
            .map(|(implementation, contract)| json!({"contract": contract, "implementation": implementation}))
            .collect();
        return Some(
            json!({"accepted": true, "discovery": "physical-registry", "implementations": entries}),
        );
    }
    if request.len() == 1 && request.contains_key("physical_type") {
        let ty = PhysicalType::parse(request.get("physical_type")?.as_str()?).ok()?;
        return Some(json!({"accepted": true, "canonical": ty.spelling()}));
    }
    if request.len() == 1 {
        let logical = LogicalType::parse(request.get("type")?.as_str()?).ok()?;
        let physical = PhysicalType::default_for(logical.clone())
            .ok()
            .map(|ty| ty.spelling());
        return Some(json!({"accepted": true, "canonical": logical.spelling(),
            "copy": logical.is_duplicable(), "drop": logical.is_discardable(),
            "serializable": logical.kind().is_serializable(), "default_physical": physical}));
    }
    let facet_query = request.len() == 2 && request.contains_key("facets");
    let attribute_query = request.len() == 5 && request.contains_key("attributes");
    if !facet_query && !attribute_query && request.len() != 4 {
        return None;
    }
    let arguments = request.get("arguments")?.as_array()?;
    if arguments.len() > 16 {
        return None;
    }
    let binding = OperationBinding {
        contract: request
            .get(if facet_query { "facets" } else { "contract" })?
            .as_str()?
            .to_owned(),
        arguments: arguments
            .iter()
            .map(|value| value.as_str().map(str::to_owned))
            .collect::<Option<_>>()?,
        implementation: if facet_query {
            String::new()
        } else {
            request.get("implementation")?.as_str()?.to_owned()
        },
    };
    if facet_query {
        resolve(&binding).ok()?;
        return Some(json!({"accepted": true,
            "facets": {"history": binding.observes_history().ok()?},
            "unsupported": ["publicReplay", "sampling", "observation", "acceptanceGuard",
                            "conjunction", "unclassifiedProviderEffect"]}));
    }
    let physical = request.get("physical")?.as_bool()?;
    if attribute_query {
        if !physical {
            return None;
        }
        let attributes = request.get("attributes")?.as_array()?;
        if !attributes.iter().all(Value::is_string) {
            return None;
        }
        let bytes = operation_program(&binding, attributes)?;
        return Some(observed(
            admit_supplied(&bytes, native)
                .map(|_| ())
                .map_err(|e| e.code),
        ));
    }
    let (inputs, outputs): (Vec<_>, Vec<_>) = if physical {
        let signature = binding.signature().ok()?;
        (
            signature
                .inputs
                .iter()
                .map(PhysicalType::spelling)
                .collect(),
            signature
                .outputs
                .iter()
                .map(PhysicalType::spelling)
                .collect(),
        )
    } else {
        let signature = resolve(&binding).ok()?;
        (
            signature.inputs.iter().map(LogicalType::spelling).collect(),
            signature
                .outputs
                .iter()
                .map(LogicalType::spelling)
                .collect(),
        )
    };
    Some(json!({"accepted": true, "physical": physical, "inputs": inputs, "outputs": outputs}))
}

fn main() -> io::Result<()> {
    let arguments: Vec<_> = std::env::args().skip(1).collect();
    let resolve: LogicalResolver = match arguments.as_slice() {
        [] => OperationBinding::logical_signature,
        [flag] if flag == "--divergent-logical-field-add" => divergent_logical_resolver,
        _ => {
            eprintln!("usage: contract-conformance [--divergent-logical-field-add]");
            std::process::exit(2);
        }
    };
    let native = NativeBackend::new(
        Policy::default(),
        EntryPolicy::new(Domain::new("P", "session", "main", None), None),
        Default::default(),
    )
    .map_err(|error| io::Error::other(error.code))?;
    zkc_test_support::json_lines::run(|line| respond(&native, line, resolve))
}
