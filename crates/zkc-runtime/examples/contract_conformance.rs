//! Bounded JSON-lines observations of independent runtime admission/signatures.
use serde_json::{Value, json};
use std::io;
use zkc_runtime::interactive::{
    AdmissionError, KernelSignature, LogicalType, OperationBinding, PhysicalType,
};

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

fn respond(line: &[u8], resolve: LogicalResolver) -> Option<Value> {
    let request = zkc_test_support::json_lines::request(line)?;
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
    if !facet_query && request.len() != 4 {
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
    zkc_test_support::json_lines::run(|line| respond(line, resolve))
}
