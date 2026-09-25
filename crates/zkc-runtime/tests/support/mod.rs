//! What these suites share: a program, a state, a binding, a declaration and
//! an endpoint entry.
//!
//! Each integration test binary compiles this module separately, so whatever a
//! given binary does not use is dead code from its point of view.
#![allow(dead_code)]

use serde_json::{Value, json};
use zkc_runtime::{
    AdmittedProgram, CheckFailure, CheckRequest, Checker, EndpointEntry,
    buffer::BufferStore,
    table::{Phase, SmallPrimeKernel, State, TableBindings, TableLibrary, TapeProvider},
};

// Only for dispatcher unit tests. Cross-language tests install the real Lean
// executable and reject altered plans at that independent boundary.
struct DirectEquality;
impl Checker for DirectEquality {
    fn check(&self, request: CheckRequest<'_>) -> Result<(), CheckFailure> {
        assert!(request.phase.is_none());
        let (source, candidate) = (request.source, request.candidate);
        let s: Value = serde_json::from_slice(source).unwrap();
        let p: Value = serde_json::from_slice(candidate).unwrap();
        if s[5] == p[9] {
            Ok(())
        } else {
            Err(CheckFailure::NotEstablished("unchecked-plan".into()))
        }
    }
}
pub fn program(
    body: Value,
    inputs: Value,
    result: Value,
) -> std::sync::Arc<AdmittedProgram<zkc_runtime::table::Operation>> {
    let context = json!(["trace", inputs, result, [["table-protocol", "1"]]]);
    let source = json!(["zkc-request", 1, "finite-source-1", context, [], body]);
    let candidate = json!([
        "zkc-plan",
        1,
        "finite-source-1",
        [],
        "direct-logical-plan",
        "direct-lowering",
        [
            "equality",
            "logical-outcome-state-events",
            "all-inputs-and-handlers"
        ],
        context,
        [],
        body
    ]);
    AdmittedProgram::admit(
        source.to_string().into_bytes(),
        candidate.to_string().into_bytes(),
        None,
        &TableLibrary,
        &DirectEquality,
    )
    .unwrap_or_else(|e| panic!("{}", e.reason))
}
pub fn state() -> State {
    State {
        two: 0,
        seven: 0,
        writes: 0u8.into(),
        sent: vec![],
    }
}
pub fn binding_with<S: BufferStore<u8>>(
    store: S,
) -> TableBindings<SmallPrimeKernel, TapeProvider, S> {
    TableBindings::with_storage(
        SmallPrimeKernel,
        TapeProvider::new(vec![3, 6]).unwrap(),
        state(),
        store,
    )
    .unwrap()
}
pub fn decl(name: &str, ty: Value) -> Value {
    json!([name, ty, ["shared"], "capture"])
}

/// The endpoint entry a prover is at in a given phase.
///
///
/// Two suites wrote this identically: the logical state machine's, and the
/// physical wrapper that delegates `validate_entry` straight to it.
pub fn entry(phase: Phase) -> EndpointEntry {
    EndpointEntry {
        role: "prover".into(),
        phase: json!(phase.name()),
    }
}
