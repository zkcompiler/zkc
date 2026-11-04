//! EVM compilation adapts the same project/Entry selection to a distinct artifact.
use super::{Artifact, EntryKind, Selection, cli::Source};
use crate::cli::Arguments;
use serde_json::{Value as Json, json};
type Result<T> = std::result::Result<T, String>;

fn options(args: &Arguments<'_>, compile: zkc::entry::CompileOptions) -> Result<zkc::evm::Options> {
    for flag in ["--cache", "--dump", "--report", "--release-storage"] {
        if args.has(flag) {
            return Err("evm-option-unsupported".into());
        }
    }
    // Without --evm-version, the declared default fork.
    let options = zkc::evm::Options {
        fork: args
            .value("--evm-version")
            .map(str::parse)
            .transpose()
            .map_err(|e: zkc::evm::Error| e.to_string())?
            .unwrap_or_default(),
        compile,
        limits: args
            .value("--evm-limits")
            .map(zkc::evm::Limits::read)
            .transpose()
            .map_err(|e| e.to_string())?
            .unwrap_or_default(),
    };
    if options.compile.release_storage {
        return Err("evm-option-unsupported".into());
    }
    Ok(options)
}

pub(super) fn compile(args: &Arguments<'_>, source: &Source, report: &mut Json) -> Result<()> {
    let options = options(args, source.settings.options())?;
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
            &options,
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
    report["evm_version"] = json!(artifact.manifest().evm_version);
    report["evm_limits"] = json!(metadata.limits());
    report["status"] = json!("compiled");
    report["phase"] = json!("complete");
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn evm_limits_file_fills_defaults_only_in_sdk() {
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("limits.json");
        let row = &zkc::evm_target::LIMITS[0];
        std::fs::write(&path, json!({row.name: row.minimum}).to_string()).unwrap();
        let args = Arguments {
            positional: vec![],
            options: vec![("--evm-limits", path.to_str())],
        };
        let selected = options(&args, super::super::ResolvedSettings::default().options()).unwrap();
        assert_eq!(
            selected.limits,
            zkc::evm::Limits::default()
                .with(row.name, row.minimum)
                .unwrap()
        );
        let complete: Json = serde_json::from_str(&selected.limits.canonical_json()).unwrap();
        assert_eq!(
            complete.as_object().unwrap().len(),
            zkc::evm_target::LIMITS.len()
        );
        // The file is captured into a value; later file changes cannot alter it.
        std::fs::write(&path, "{}").unwrap();
        assert_eq!(selected.limits.get(row.name), Some(row.minimum));
        assert_eq!(
            options(&args, super::super::ResolvedSettings::default().options())
                .unwrap()
                .limits,
            zkc::evm::Limits::default()
        );
    }

    #[test]
    #[cfg(unix)]
    fn invalid_evm_limits_refuse_before_spawning_compiler_or_solc() {
        use std::os::unix::fs::PermissionsExt;
        let directory = tempfile::tempdir().unwrap();
        let module = directory.path().join("sample.zkc");
        std::fs::write(&module, "module sample;\n").unwrap();
        let tool = directory.path().join("tool");
        let marker = directory.path().join("spawned");
        std::fs::write(
            &tool,
            format!("#!/bin/sh\ntouch '{}'\nexit 99\n", marker.display()),
        )
        .unwrap();
        std::fs::set_permissions(&tool, std::fs::Permissions::from_mode(0o700)).unwrap();
        let limits = directory.path().join("limits.json");
        let args = vec![
            "--target=evm".to_owned(),
            "--source-format=zkc".to_owned(),
            format!("--module=sample={}", module.display()),
            format!("--compiler={}", tool.display()),
            format!("--solc={}", tool.display()),
            format!("--solc-sha256={}", "00".repeat(32)),
            format!("--evm-limits={}", limits.display()),
        ];
        let report = crate::cli::run("compile", &args);
        assert_eq!(report["code"], "evm-limits-read", "{report}");
        let mut refused = vec![
            "[]".to_owned(),
            r#"{"unknown":1}"#.to_owned(),
            r#"{"public_elements":1,"\u0070ublic_elements":2}"#.to_owned(),
            r#"{"public_elements":1.0}"#.to_owned(),
            r#"{"public_elements":1e0}"#.to_owned(),
            r#"{"public_elements":-1}"#.to_owned(),
            r#"{"public_elements":"1"}"#.to_owned(),
            r#"{"public_elements":true}"#.to_owned(),
            r#"{"public_elements":null}"#.to_owned(),
            r#"{"public_elements":18446744073709551616}"#.to_owned(),
        ];
        for row in &zkc::evm_target::LIMITS {
            for value in [row.minimum - 1, row.maximum + 1] {
                refused.push(json!({row.name: value}).to_string());
            }
        }
        for text in refused {
            std::fs::write(&limits, &text).unwrap();
            let report = crate::cli::run("compile", &args);
            assert_eq!(report["code"], "evm-limits", "{text}: {report}");
            assert!(!marker.exists(), "invalid limits started a tool: {text}");
        }
    }

    #[test]
    fn evm_shares_resolved_profile_and_request_options() {
        let directory = tempfile::tempdir().unwrap();
        let manifest = directory.path().join("zkc.toml");
        std::fs::write(
            &manifest,
            r#"format = "zkc.project/0"
source-format = "zkc"
[modules]
sample = "sample.zkc"
[build]
simplify = false
[profile.deployment]
finite-bulk = false
fuse-vector-reductions = true
fuse-collect-fold = true
calculation-batching = false
"#,
        )
        .unwrap();
        let executable = std::env::current_exe().unwrap();
        let args = Arguments {
            positional: vec![],
            options: vec![
                ("--compiler", executable.to_str()),
                ("--project", manifest.to_str()),
                ("--profile", Some("deployment")),
                ("--evm-version", Some("prague")),
            ],
        };
        let source = Source::load(&args).unwrap();
        let options = options(&args, source.settings.options()).unwrap();
        assert_eq!(options.fork, zkc::evm::EvmFork::Prague);
        assert_eq!(options.compile, source.settings.options());
        assert!(!options.compile.simplify);
        assert!(!options.compile.finite_bulk);
        assert!(options.compile.fuse_vector_reductions);
        assert!(options.compile.fuse_collect_fold);
        assert!(!options.compile.calculation_batching);
    }

    #[test]
    fn evm_fork_and_unsupported_options_have_stable_diagnostics() {
        let defaults = super::super::ResolvedSettings::default().options();
        let mut refused: Vec<_> = zkc::evm_target::Fork::ALL
            .iter()
            .map(|fork| fork.row().hardfork.to_owned())
            .collect();
        refused.extend(["shanghai".to_owned(), "latest".to_owned(), String::new()]);
        for fork in &refused {
            let args = Arguments {
                positional: vec![],
                options: vec![("--evm-version", Some(fork.as_str()))],
            };
            assert_eq!(options(&args, defaults.clone()).unwrap_err(), "evm-fork");
        }
        for flag in ["--cache", "--dump", "--report", "--release-storage"] {
            let args = Arguments {
                positional: vec![],
                options: vec![(flag, None)],
            };
            assert_eq!(
                options(&args, defaults.clone()).unwrap_err(),
                "evm-option-unsupported"
            );
        }
        let args = Arguments {
            positional: vec![],
            options: vec![],
        };
        assert_eq!(
            options(&args, defaults.clone()).unwrap().fork,
            zkc::evm_target::DEFAULT_FORK
        );
        let mut released = defaults;
        released.release_storage = true;
        assert_eq!(
            options(&args, released).unwrap_err(),
            "evm-option-unsupported"
        );
    }
}
