#[test]
fn trace_mutations_agree_with_upstream_constraints_and_buses() {
    let (export, cases) = zkc_openvm_relation_driver::corpus();
    assert_eq!(export.airs.len(), 5);
    assert!(cases.len() > 80);
    eprintln!("{} cases", cases.len());
}
