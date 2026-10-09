mod common;
use common::*;
use zkc_runtime::interactive::{Runner, admit_supplied};

#[test]
fn heterogeneous_tables_follow_explicit_entry_shapes() {
    let bytes = program(&[("small", "table"), ("large", "table")], vec![], &[], &[]);
    let backend = ark_backend(None);
    let admitted = admit_supplied(&bytes, &backend).unwrap();
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
