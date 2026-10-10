//! Source capture transport and compiler invocation, separate from Entry execution.
mod output;
mod project;
mod selection;
use crate::{
    cli::Arguments,
    entry::{Interface, Package},
    host::{
        inputs::{hex, read_regular as read},
        publication::Outputs,
    },
};
use serde_json::{Value as Json, json};
use sha2::{Digest, Sha256};
use std::{process::Command, time::Duration};
type Result<T> = std::result::Result<T, String>;

pub(crate) fn run(command: &str, args: &Arguments<'_>) -> Json {
    let checking = command == "check";
    let mut report = json!({"format":if checking {"zkc.source-check/0"} else {"zkc.entry-build/0"},"status":"refused","phase":"arguments"});
    let result = (|| -> Result<()> {
        let mut compiler = "zkc-compile";
        let mut output = None;
        let mut flags = Vec::new();
        let entry = args.positional.first().copied();
        if let Some(name) = entry {
            if name.is_empty() {
                return Err("source-entry-selection".into());
            }
            flags.push(format!("--entry={name}"));
        }
        let inputs = project::Inputs::load(args)?;
        for &(key, value) in &args.options {
            let value = value.unwrap_or("");
            match key {
                "--compiler" => compiler = value,
                "--output" => output = Some(value),
                "--no-simplify"
                | "--release-storage"
                | "--fuse-vector-reductions"
                | "--declarations"
                | "--notations"
                | "--notation-private"
                | "--notation-installation" => flags.push(key.to_owned()),
                "--project" | "--module" | "--asset" => {}
                _ => unreachable!("validated source option"),
            }
        }
        flags.extend(inputs.flags.iter().cloned());
        if !checking && output.is_none() && inputs.manifest.is_none() {
            return Err("source-output-required".into());
        }
        if let Some(manifest) = &inputs.manifest {
            report["project"] = json!(manifest);
        }
        let outputs: Vec<_> = output.into_iter().collect();
        let sources: Vec<_> = inputs.paths.iter().map(String::as_str).collect();
        let mut destinations = Outputs::new(&outputs, &sources)?;
        for source in &sources {
            crate::host::io::open_regular(source).map_err(|_| "artifact-io")?;
        }
        let selected_compiler = resolve_compiler(compiler)?;
        let compiler_path = std::path::Path::new(compiler);
        let mut compiler_paths = vec![selected_compiler.to_str().ok_or("source-compiler-io")?];
        if compiler_path.is_absolute() || compiler_path.components().count() > 1 {
            compiler_paths.push(compiler);
        }
        destinations.protect(compiler_paths.iter().copied())?;
        let compiler = &selected_compiler;
        report["compiler"] = json!(compiler);
        report["phase"] = json!("compilation");
        let directory = tempfile::tempdir().map_err(|_| "source-compiler-io")?;
        let captured = crate::host::process::capture(
            Command::new(compiler)
                .args([
                    if checking {
                        "language-check"
                    } else {
                        "language-package"
                    },
                    "--source-format=zkc",
                ])
                .args(flags),
            directory.path(),
            |elapsed| elapsed >= Duration::from_secs(300),
            Package::MAX_BYTES,
            true,
        )
        .map_err(|e| match e {
            crate::host::process::Error::Timeout => "source-compiler-timeout",
            crate::host::process::Error::OutputLimit => "source-compiler-limit",
            _ => "source-compiler-io",
        })?;
        if !captured.status.success() {
            use std::io::Read;
            let mut diagnostics = Vec::new();
            captured
                .stderr
                .as_ref()
                .unwrap()
                .reopen()
                .map_err(|_| "source-compiler-io")?
                .take(64 * 1024 + 1)
                .read_to_end(&mut diagnostics)
                .map_err(|_| "source-compiler-io")?;
            report["diagnostics_truncated"] = json!(diagnostics.len() > 64 * 1024);
            diagnostics.truncate(64 * 1024);
            report["diagnostics"] = json!(String::from_utf8_lossy(&diagnostics));
            return Err("source-compilation".into());
        }
        let bytes = read(captured.stdout.path(), Package::MAX_BYTES)?;
        if checking {
            let checked: Json =
                serde_json::from_slice(&bytes).map_err(|_| "source-check-format")?;
            if checked["format"] != "zkc.source-check/0"
                || checked["status"] != "checked"
                || checked["scope"]
                    != if entry.is_some() {
                        "entry"
                    } else {
                        "definitions"
                    }
                || !selection::valid_check(&checked, entry)
            {
                return Err("source-check-format".into());
            }
            report = checked;
            if let Some(manifest) = &inputs.manifest {
                report["project"] = json!(manifest);
            }
            report["compiler"] = json!(compiler);
            report["status"] = json!("checked");
            report["phase"] = json!("complete");
            return Ok(());
        }
        let pin = Sha256::digest(&bytes).into();
        let package =
            Package::capture(&bytes, &pin, Package::MAX_BYTES).map_err(|e| e.to_string())?;
        let interface = Interface::read(&package).map_err(|e| e.to_string())?;
        if !selection::matches(entry, interface.entry()) {
            return Err("source-entry-selection".into());
        }
        report["entry"] = json!(interface.entry());
        report["toolchain"] = json!(interface.toolchain());
        report["package_sha256"] = json!(hex(&pin));
        report["phase"] = json!("publication");
        let default_output;
        let path = if let Some(path) = output {
            path
        } else {
            default_output = output::default_path(&inputs, interface.entry())?;
            destinations = Outputs::new(&[&default_output], &sources)?;
            destinations.protect(compiler_paths.iter().copied())?;
            &default_output
        };
        report["output"] = json!(path);
        destinations.publish(&[("package", &bytes)], &mut report)?;
        report["status"] = json!("compiled");
        report["phase"] = json!("complete");
        Ok(())
    })();
    if let Err(code) = result {
        let message = match code.as_str() {
            "cli-usage" => {
                Some("supply --project=FILE or explicit --module options; do not combine them")
            }
            "source-project-missing" => Some(
                "no zkc.toml found in this directory or its ancestors; use --project or --module",
            ),
            "source-output-required" => Some("explicit module inputs require --output=FILE"),
            "source-output-collision" => Some(
                "default filename collides with a name differing only in case; choose --output=FILE",
            ),
            "source-entry-selection" => {
                Some("the Entry selector must match the compiler's canonical Entry name")
            }
            "source-output-name" => Some(
                "the canonical Entry name cannot be used as a portable filename; choose --output=FILE",
            ),
            "source-output-directory" => {
                Some("cannot create the project's build/zkc output directory")
            }
            _ => None,
        };
        if let Some(message) = message {
            report["message"] = json!(message);
        }
        report["code"] = json!(if code == "artifact-output-path" {
            "entry-output-path"
        } else {
            &code
        });
    }
    report
}

// Compiler and runtime are separately installed components. Use an explicit
// path, or resolve the caller's trusted PATH once and report the selected file.
fn resolve_compiler(name: &str) -> Result<std::path::PathBuf> {
    use std::path::Path;
    let candidates = if Path::new(name).components().count() > 1 || Path::new(name).is_absolute() {
        vec![name.into()]
    } else {
        std::env::split_paths(&std::env::var_os("PATH").ok_or("source-compiler-missing")?)
            .filter(|p| p.is_absolute())
            .map(|p| p.join(name))
            .collect()
    };
    for path in candidates {
        if !path.is_file() {
            continue;
        }
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            if path
                .metadata()
                .map_err(|_| "source-compiler-io")?
                .permissions()
                .mode()
                & 0o111
                == 0
            {
                continue;
            }
        }
        return path.canonicalize().map_err(|_| "source-compiler-io".into());
    }
    Err("source-compiler-missing".into())
}
