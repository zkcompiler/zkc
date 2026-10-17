//! Link only trusted installed implementations of the exact admitted bindings.
use super::*;
type Result<T> = std::result::Result<T, AdmissionError>;
fn err(code: ErrorCode, detail: impl Into<String>) -> AdmissionError {
    AdmissionError::new(code, detail)
}
pub(crate) fn install<B: Backend>(program: &Program, backend: &B) -> Result<Vec<B::Operation>> {
    let p = &program.program;
    let executable = &program.executable;
    if executable.requires_boolean_literals && !backend.supports_boolean_literals() {
        return Err(err(ErrorCode::Backend, "native-boolean-unsupported"));
    }
    for participant in p.participants.values() {
        for port in &participant.services {
            let expected = port.contract.signature("draw").expect("installed method");
            if !backend
                .service_support(port.contract, "draw")
                .is_some_and(|support| {
                    support.signature == expected
                        && support.max_retained_bytes <= Limits::VALUE_BYTES
                })
            {
                return Err(err(
                    ErrorCode::Backend,
                    "installed service signature mismatch",
                ));
            }
        }
    }
    use super::InstalledOperation;
    executable
        .bindings
        .iter()
        .map(|binding| {
            let actual = backend
                .prepare_binding(binding.declaration())
                .filter(|operation| operation.signature() == binding.signature());
            actual.ok_or_else(|| {
                err(
                    ErrorCode::Backend,
                    format!("installed signature mismatch: {}", binding.implementation()),
                )
            })
        })
        .collect()
}
