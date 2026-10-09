//! Both separately built native evaluators must agree with the upstream corpus.
use serde_json::{Value, json};
use std::path::PathBuf;
use zkc_openvm_relation_driver::{check_native, corpus, native_reports};

#[test]
fn native_bundle_evaluators_match_upstream_and_refuse_malformed_carriers() {
    let (_, cases) = corpus();
    let mut lines: Vec<Value> = cases.iter().map(|c| json!(c.carriers)).collect();
    let first = lines[0].clone();
    let mut changed = first.clone();
    changed[2][3][0] = json!(["absent"]);
    lines.push(changed);
    let mut changed = first.clone();
    changed[3][2][2][0].as_array_mut().unwrap().pop();
    lines.push(changed);
    let mut changed = first.clone();
    changed[2][3][2][1] = json!(3);
    lines.push(changed);
    let mut changed = first;
    changed[1][1] = json!("0".repeat(64));
    lines.push(changed);
    let cpp = PathBuf::from(std::env::var_os("ZKC_COMPILER_BIN").expect("set ZKC_COMPILER_BIN"))
        .join("test/zkc-relation_bundle_conformance-test");
    let rust = PathBuf::from(std::env::var_os("ZKC_NATIVE_BIN").expect("set ZKC_NATIVE_BIN"))
        .join("relation_bundle_conformance");
    let reports = native_reports(&cpp, &lines);
    assert_eq!(reports, native_reports(&rust, &lines));
    for (case, report) in cases.iter().zip(&reports) {
        check_native(case, report);
    }
    for report in &reports[cases.len()..] {
        assert_eq!(report["accepted"], false, "{report}");
    }
    eprintln!(
        "{} valid carrier cases and four malformed carriers agree",
        cases.len()
    );
}
