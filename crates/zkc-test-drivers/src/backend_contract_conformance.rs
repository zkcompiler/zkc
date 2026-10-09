//! Observe the executing backend's own registry and physical signatures.
use serde_json::{Value, json};
use zkc_backends::{Domain, EntryPolicy, NativeBackend, Policy};
use zkc_runtime::interactive::{
    AttributeRule, Backend, BackendError, BoundSignature, Frame, FrameExit, Invocation,
    OperationBinding, PhysicalType, admit_supplied,
};

// Admission-only adapter: preserve the native backend's ports and deliberately
// change its attribute contract. Any execution attempt is a harness defect.
struct AttributeDrift<'a>(&'a NativeBackend);
impl Backend for AttributeDrift<'_> {
    type Value = <NativeBackend as Backend>::Value;
    fn binding_signature(&self, binding: &OperationBinding) -> Option<BoundSignature> {
        let mut signature = self.0.binding_signature(binding)?;
        if binding.contract == "field.add" {
            signature.attributes = AttributeRule::Unsigned64;
        }
        Some(signature)
    }
    fn validate_value(&self, _: &Self::Value) -> Result<(), BackendError> {
        unreachable!("admission does not validate runtime values")
    }
    fn enter_frame(&mut self, _: &Frame, _: &[Self::Value]) -> Result<(), BackendError> {
        unreachable!("admission does not enter frames")
    }
    fn leave_frame(
        &mut self,
        _: &Frame,
        _: FrameExit,
        _: &[Self::Value],
    ) -> Result<(), BackendError> {
        unreachable!("admission does not leave frames")
    }
    fn apply(
        &mut self,
        _: &Invocation<'_>,
        _: &[Self::Value],
    ) -> Result<Vec<Self::Value>, BackendError> {
        unreachable!("admission does not execute kernels")
    }
}

fn installation(native: &NativeBackend, drift: bool) -> Option<Value> {
    let binding = OperationBinding {
        contract: "field.add".into(),
        arguments: vec!["bls12-381.fr".into()],
        implementation: "arkworks/field.add".into(),
    };
    // Literal witness independent of either registry's generated inventory.
    let field = "field:bls12-381.fr@arkworks.fr/0";
    let bytes = serde_json::to_vec(&json!([
        "zkc.program/0",
        [[
            "add_binding",
            "field.add",
            ["bls12-381.fr"],
            "arkworks/field.add"
        ]],
        [[
            "function",
            "add",
            [["x", field], ["y", field]],
            [field],
            [
                ["op", "sum", "add_binding", [], ["x", "y"], ["z"]],
                ["return", ["z"]]
            ],
            ["Add", []]
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
    .ok()?;
    let original = native.binding_signature(&binding)?;
    let mutated = AttributeDrift(native).binding_signature(&binding)?;
    let result = if drift {
        admit_supplied(&bytes, &AttributeDrift(native))
    } else {
        admit_supplied(&bytes, native)
    };
    Some(json!({"accepted": true, "admitted": result.is_ok(),
        "error": result.err().map(|error| error.code.as_str()),
        "same_ports": original.inputs == mutated.inputs && original.outputs == mutated.outputs,
        "same_attributes": original.attributes == mutated.attributes}))
}

fn respond(native: &NativeBackend, line: &[u8]) -> Option<Value> {
    let request = zkc_test_support::json_lines::request(line)?;
    if request.len() == 1 && request.contains_key("attribute_drift") {
        return installation(native, request.get("attribute_drift")?.as_bool()?);
    }
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
        EntryPolicy::new(Domain::new("P", "session", "main", None), None),
        Default::default(),
    )
    .map_err(|error| std::io::Error::other(error.code))?;
    zkc_test_support::json_lines::run(|line| respond(&native, line))
}
