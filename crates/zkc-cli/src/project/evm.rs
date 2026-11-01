//! EVM compilation adapts the same project/Entry selection to a distinct artifact.
use super::{Artifact, EntryKind, Selection, cli::Source};
use crate::cli::Arguments;
use serde_json::{Value as Json, json};
type Result<T> = std::result::Result<T, String>;

pub(super) fn compile(args: &Arguments<'_>, source: &Source, report: &mut Json) -> Result<()> {
    for flag in [
        "--profile",
        "--cache",
        "--dump",
        "--report",
        "--no-simplify",
        "--release-storage",
        "--fuse-vector-reductions",
        "--fuse-collect-fold",
        "--no-finite-bulk",
        "--no-calculation-batching",
        "--oracle-realization",
    ] {
        if args.has(flag) {
            return Err("evm-option-unsupported".into());
        }
    }
    if source.settings.options() != super::ResolvedSettings::default().options() {
        return Err("evm-option-unsupported".into());
    }
    if args.has("--reuse") != args.has("--reuse-sha256") {
        return Err("cli-usage".into());
    }
    let solc = zkc::evm::Solc::new(
        args.value("--solc").ok_or("evm-solc-required")?,
        args.value("--solc-sha256").ok_or("evm-solc-pin-required")?,
    )
    .map_err(|e| e.to_string())?;
    let reuse = args
        .value("--reuse")
        .map(|path| {
            zkc::evm::Artifact::capture(path, args.value("--reuse-sha256").unwrap())
                .map_err(|e| e.to_string())
        })
        .transpose()?;
    report["target"] = json!("evm");
    report["phase"] = json!("compilation");
    let artifact = source
        .compiler
        .build_evm(
            &source.project,
            Selection {
                name: args.positional.first().copied(),
                kind: Some(EntryKind::Proof),
            },
            &solc,
            reuse.as_ref(),
        )
        .map_err(|e| super::cli::compiler_error(report, e))?;
    let metadata = artifact.source().map_err(|e| e.to_string())?;
    let entry = metadata.entry();
    let output = match args.value("--output") {
        Some(path) => std::path::PathBuf::from(path),
        None => source
            .project
            .layout()
            .ok_or("source-output-required")?
            .artifact(entry, Artifact::Evm)?,
    };
    // The artifact is a fresh directory, so it cannot replace any source,
    // executable or manifest. Only the parent may be created by convention.
    if let Some(parent) = output.parent()
        && !parent.as_os_str().is_empty()
    {
        std::fs::create_dir_all(parent).map_err(|_| "source-output-directory")?;
    }
    report["phase"] = json!("publication");
    let output = artifact.publish(&output).map_err(|e| e.to_string())?;
    report["entry"] = json!(entry);
    report["output"] = json!(output);
    report["manifest_sha256"] = json!(artifact.identity());
    report["solc_sha256"] = json!(solc.identity());
    report["runtime_bytes"] = json!(artifact.runtime_bytecode().len());
    report["creation_bytes"] = json!(artifact.creation_bytecode().len());
    report["evm_version"] = json!("cancun");
    report["status"] = json!("compiled");
    report["phase"] = json!("complete");
    Ok(())
}
