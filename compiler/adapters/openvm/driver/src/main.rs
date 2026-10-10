//! Regenerate inspection artifacts and comparison inputs for the selected slice.
use serde_json::json;
use std::error::Error;
use std::path::PathBuf;
use zkc_openvm_relation_driver::corpus;

fn main() -> Result<(), Box<dyn Error>> {
    let mut arguments = std::env::args_os().skip(1);
    let output = PathBuf::from(
        arguments
            .next()
            .ok_or("usage: zkc-openvm-relation-fixtures OUTPUT")?,
    );
    if arguments.next().is_some() {
        return Err("expected one output directory".into());
    }
    std::fs::create_dir_all(&output)?;
    let (exported, cases) = corpus();
    std::fs::write(output.join("capture.json"), exported.canonical_text()?)?;
    let mut wire = String::new();
    let mut manifest = vec![];
    for case in &cases {
        wire.push_str(&serde_json::to_string(&case.carriers)?);
        wire.push('\n');
        manifest.push(json!({"name":case.name,"satisfied":case.outcome.satisfied(),
            "nonzero_residuals":case.outcome.residuals.len(),"unbalanced_keys":case.outcome.unbalanced.len()}));
    }
    std::fs::write(output.join("candidates.jsonl"), wire)?;
    std::fs::write(
        output.join("expected.json"),
        serde_json::to_string_pretty(&manifest)?,
    )?;
    println!(
        "{} cases, {} satisfying; capture {}",
        cases.len(),
        cases.iter().filter(|c| c.outcome.satisfied()).count(),
        exported.sha256()?
    );
    Ok(())
}
