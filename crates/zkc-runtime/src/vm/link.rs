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
    executable
        .bindings
        .iter()
        .map(|binding| {
            let actual = backend
                .prepare_binding(binding.declaration())
                .filter(|operation| compatible(program, binding, operation));
            actual.ok_or_else(|| {
                err(
                    ErrorCode::Backend,
                    format!("installed signature mismatch: {}", binding.implementation()),
                )
            })
        })
        .collect()
}

/// Installation slots preserve admitted indices. An absent slot cannot be
/// reached from the selected root; no caller can choose the slot inventory.
pub(crate) fn install_local<B: Backend>(
    program: &Program,
    function: &str,
    backend: &B,
) -> Result<Vec<Option<B::Operation>>> {
    let function = program
        .program
        .functions
        .get(function)
        .ok_or_else(|| err(ErrorCode::Symbol, "unknown-local-root"))?;
    install_selected(program, backend, [function.as_ref()], &[])
}

pub(crate) fn install_role<B: Backend>(
    program: &Program,
    entry: &str,
    role: &str,
    backend: &B,
) -> Result<Vec<Option<B::Operation>>> {
    let participant = program
        .participant(entry, role)
        .map_err(|_| err(ErrorCode::Symbol, "unknown-role-root"))?;
    let mut names = std::collections::BTreeSet::new();
    fn walk(body: &model::Body, names: &mut std::collections::BTreeSet<String>) {
        for instruction in body.iter() {
            match instruction {
                model::Instruction::Local { function, .. } => {
                    names.insert(function.clone());
                }
                model::Instruction::Loop { body, .. } => walk(body, names),
                _ => {}
            }
        }
    }
    walk(&participant.body, &mut names);
    install_selected(
        program,
        backend,
        names
            .iter()
            .map(|name| program.program.functions[name].as_ref()),
        &participant.services,
    )
}

fn install_selected<'a, B: Backend>(
    program: &Program,
    backend: &B,
    functions: impl IntoIterator<Item = &'a model::Function>,
    services: &[ServicePort],
) -> Result<Vec<Option<B::Operation>>> {
    use model::LocalInstruction;
    let mut declarations = std::collections::BTreeSet::new();
    let mut boolean = false;
    for function in functions {
        // Local helpers have already been inlined into this carrier. Walk all
        // control regions, including unchosen branches and zero-trip loops.
        for instruction in LocalInstruction::walk(&function.body) {
            match instruction {
                LocalInstruction::Op { binding, .. } => {
                    declarations.insert(binding.declaration());
                }
                LocalInstruction::BoolConstant { .. } => boolean = true,
                _ => {}
            }
        }
    }
    if boolean && !backend.supports_boolean_literals() {
        return Err(err(ErrorCode::Backend, "native-boolean-unsupported"));
    }
    for port in services {
        let expected = port.contract.signature("draw").expect("installed method");
        if !backend
            .service_support(port.contract, "draw")
            .is_some_and(|support| {
                support.signature == expected && support.max_retained_bytes <= Limits::VALUE_BYTES
            })
        {
            return Err(err(
                ErrorCode::Backend,
                "installed service signature mismatch",
            ));
        }
    }
    program
        .executable
        .bindings
        .iter()
        .map(|binding| {
            if !declarations.contains(binding.declaration()) {
                return Ok(None);
            }
            backend
                .prepare_binding(binding.declaration())
                .filter(|operation| compatible(program, binding, operation))
                .map(Some)
                .ok_or_else(|| {
                    err(
                        ErrorCode::Backend,
                        format!("installed signature mismatch: {}", binding.implementation()),
                    )
                })
        })
        .collect()
}

fn compatible<O: InstalledOperation>(
    program: &Program,
    expected: &ResolvedBinding,
    actual: &O,
) -> bool {
    // Never obtain the expected ports or premises from the backend advertisement.
    actual.signature() == expected.signature()
        && actual.implementation_id() == expected.implementation_id()
        && actual.requirements() == expected.requirements()
        && program.contracts().permits_implementation(
            expected.declaration(),
            actual.implementation_id(),
            actual.requirements(),
        )
}
