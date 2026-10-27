use zkc_runtime::interpreter::Runner;
mod common;
use common::*;

#[test]
fn heterogeneous_tables_follow_explicit_entry_shapes() {
    let bytes = program(&[("small", "table"), ("large", "table")], vec![], &[], &[]);
    let backend = ark_backend(None);
    let admitted = zkc_runtime::vm::Program::decode(&bytes, zkc_cpu::cpu_contracts())
        .and_then(|program| {
            program.check_installation(&backend)?;
            Ok(program)
        })
        .unwrap();
    assert!(
        Runner::new(
            &admitted,
            "main",
            "P",
            "session",
            backend,
            vec![table(&[1, 2]), table(&[3, 4, 5, 6])]
        )
        .is_ok()
    );
}
