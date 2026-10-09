//! Source capture transport and compiler invocation, separate from Entry execution.
mod project;
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
        let inputs = project::Inputs::load(args)?;
        for &(key, value) in &args.options {
            let value = value.unwrap_or("");
            match key {
                "--compiler" => compiler = value,
                "--output" => output = Some(value),
                "--entry" => flags.push(format!("--entry={value}")),
                "--no-simplify" | "--release-storage" => flags.push(key.to_owned()),
                "--project" | "--module" | "--asset" => {}
                _ => unreachable!("validated source option"),
            }
        }
        flags.extend(inputs.flags);
        let outputs: Vec<_> = output.into_iter().collect();
        let sources: Vec<_> = inputs.paths.iter().map(String::as_str).collect();
        let mut destinations = Outputs::new(&outputs, &sources)?;
        for source in &sources {
            crate::host::io::open_regular(source).map_err(|_| "artifact-io")?;
        }
        let selected_compiler = resolve_compiler(compiler)?;
        let compiler_path = std::path::Path::new(compiler);
        if compiler_path.is_absolute() || compiler_path.components().count() > 1 {
            destinations.protect([compiler])?;
        }
        destinations.protect([selected_compiler.to_str().ok_or("entry-compiler-io")?])?;
        let compiler = selected_compiler;
        report["compiler"] = json!(compiler);
        report["phase"] = json!("compilation");
        let directory = tempfile::tempdir().map_err(|_| "entry-compiler-io")?;
        let captured = crate::host::process::capture(
            Command::new(&compiler)
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
            crate::host::process::Error::Timeout => "entry-compiler-timeout",
            crate::host::process::Error::OutputLimit => "entry-compiler-limit",
            _ => "entry-compiler-io",
        })?;
        if !captured.status.success() {
            use std::io::Read;
            let mut diagnostics = Vec::new();
            captured
                .stderr
                .as_ref()
                .unwrap()
                .reopen()
                .map_err(|_| "entry-compiler-io")?
                .take(64 * 1024 + 1)
                .read_to_end(&mut diagnostics)
                .map_err(|_| "entry-compiler-io")?;
            report["diagnostics_truncated"] = json!(diagnostics.len() > 64 * 1024);
            diagnostics.truncate(64 * 1024);
            report["diagnostics"] = json!(String::from_utf8_lossy(&diagnostics));
            return Err("entry-compilation".into());
        }
        let bytes = read(captured.stdout.path(), Package::MAX_BYTES)?;
        if checking {
            let checked: Json =
                serde_json::from_slice(&bytes).map_err(|_| "source-check-format")?;
            if checked["format"] != "zkc.source-check/0" || checked["status"] != "checked" {
                return Err("source-check-format".into());
            }
            report["check"] = checked;
            report["status"] = json!("checked");
            report["phase"] = json!("complete");
            return Ok(());
        }
        let pin = Sha256::digest(&bytes).into();
        let package =
            Package::capture(&bytes, &pin, Package::MAX_BYTES).map_err(|e| e.to_string())?;
        let interface = Interface::read(&package).map_err(|e| e.to_string())?;
        report["entry"] = json!(interface.entry());
        report["toolchain"] = json!(interface.toolchain());
        report["package_sha256"] = json!(hex(&pin));
        report["phase"] = json!("publication");
        destinations.publish(&[("package", &bytes)], &mut report)?;
        report["status"] = json!("compiled");
        report["phase"] = json!("complete");
        Ok(())
    })();
    if let Err(code) = result {
        if code == "cli-usage" {
            report["message"] =
                json!("supply --project=FILE or explicit --module options; do not combine them");
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
        std::env::split_paths(&std::env::var_os("PATH").ok_or("entry-compiler-missing")?)
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
                .map_err(|_| "entry-compiler-io")?
                .permissions()
                .mode()
                & 0o111
                == 0
            {
                continue;
            }
        }
        return path.canonicalize().map_err(|_| "entry-compiler-io".into());
    }
    Err("entry-compiler-missing".into())
}
