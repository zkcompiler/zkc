//! Command-line file transport over the common named Entry Host.
use super::{
    AttemptOptions, BindingPolicy, BindingScope, Package, ProofEntry, ProofOptions, RunEntry, files,
};
use crate::{
    host::{
        inputs::{digest, hex, read_regular as read},
        io::publish,
    },
    protocol::run::HostLimits,
};
use serde_json::{Value as Json, json};
use sha2::{Digest, Sha256};
use std::{collections::BTreeSet, process::Command, time::Duration};

type Result<T> = std::result::Result<T, String>;
struct Options {
    setups: super::SetupAuthority,
    proof: ProofOptions,
    run: HostLimits,
    attempts: Option<AttemptOptions>,
    results: Option<String>,
    configuration: Vec<String>,
}
impl Options {
    fn parse(args: &[String], command: &str) -> Result<Self> {
        let mut options = Self {
            setups: Default::default(),
            proof: Default::default(),
            run: Default::default(),
            attempts: None,
            results: None,
            configuration: Vec::new(),
        };
        let mut seen = BTreeSet::new();
        for arg in args {
            let (key, value) = arg.split_once('=').unwrap_or((arg, ""));
            if !seen.insert(key) {
                return Err("entry-option".into());
            }
            if matches!(key, "--setups" | "--capacity") {
                options.configuration.push(value.into());
            }
            match key {
                "--setups" => options.setups = files::authority(&read(value, 64 * 1024)?)?,
                "--capacity" => {
                    let capacity =
                        crate::artifact::native::NativeCapacity::parse(&read(value, 4096)?)?;
                    options.proof.capacity = capacity;
                    options.run.capacity = capacity;
                }
                "--allow-header-only" if command != "run-entry" && value.is_empty() => {
                    options.proof.binding = BindingPolicy::AllowHeaderOnly
                }
                "--attempts" if command == "prove" => {
                    let count = value.parse::<u64>().map_err(|_| "entry-option")?;
                    options.attempts = Some(AttemptOptions {
                        count,
                        ..Default::default()
                    });
                }
                "--results" if !value.is_empty() => options.results = Some(value.into()),
                _ => return Err("entry-option".into()),
            }
        }
        Ok(options)
    }
}
/// Exit status is zero only for the requested completed operation.
pub fn succeeded(report: &Json) -> bool {
    matches!(
        report["status"].as_str(),
        Some("compiled" | "executed" | "produced" | "accepted" | "generated")
    )
}
/// Reports preserve reached execution and publication state without returning
/// private values or proof bytes on standard output.
pub fn run(command: &str, args: &[String]) -> Json {
    if command == "compile" {
        return compile(args);
    }
    let mut report = json!({"format":"zkc.entry-result/1","status":"refused","phase":"arguments"});
    let result = (|| -> Result<()> {
        let [path, expected, inputs, rest @ ..] = args else {
            return Err("entry-usage".into());
        };
        if [path, expected, inputs]
            .iter()
            .any(|value| value.starts_with("--"))
        {
            return Err("entry-usage".into());
        }
        let (proof_path, flags) = if matches!(command, "run-entry" | "bindings") {
            (None, rest)
        } else {
            let [proof, flags @ ..] = rest else {
                return Err("entry-usage".into());
            };
            if proof.starts_with("--") {
                return Err("entry-usage".into());
            }
            (Some(proof.as_str()), flags)
        };
        if command == "bindings" && !rest.is_empty() {
            return Err("entry-option".into());
        }
        let pin = digest(expected)?;
        let options = Options::parse(flags, command)?;
        let mut protected = vec![path.as_str()];
        protected.extend(options.configuration.iter().map(String::as_str));
        let mut outputs = Vec::new();
        if command == "bindings" {
            outputs.push(inputs.as_str());
        } else {
            protected.push(inputs.as_str());
            if command == "prove" {
                outputs.extend(proof_path);
            } else {
                protected.extend(proof_path);
            }
            outputs.extend(options.results.as_deref());
        }
        protect_destinations(&outputs, &protected)?;
        report["setups"] = json!(
            options
                .setups
                .keys
                .iter()
                .map(|(name, pin)| (name, hex(pin)))
                .collect::<std::collections::BTreeMap<_, _>>()
        );
        report["phase"] = json!("admission");
        let bytes = read(path, Package::MAX_BYTES)?;
        let package =
            Package::capture(&bytes, &pin, Package::MAX_BYTES).map_err(|e| e.to_string())?;
        report["package_sha256"] = json!(hex(package.identity()));
        if command == "bindings" {
            let source = super::bindings::rust(&package)?;
            report["phase"] = json!("publication");
            publish(inputs, source.as_bytes())?;
            report["status"] = json!("generated");
            report["phase"] = json!("complete");
            return Ok(());
        }
        if command == "run-entry" {
            let host = RunEntry::admit(package, options.run, options.setups)?;
            report["entry"] = json!(host.interface().entry());
            report["capacity"] = host.limits().capacity.record();
            report["phase"] = json!("inputs");
            let request = host
                .interface()
                .run_request(&read(inputs, files::MAX_REQUEST_BYTES)?)?;
            protect_materials(
                &outputs,
                request.roles.values().flat_map(|role| role.inputs.values()),
            )?;
            let result = host.prepare(request)?.execute();
            report["phase"] = json!("execution");
            report["execution"] = result.native.diagnostics();
            if let Some(error) = result.output_error {
                return Err(error);
            }
            let outputs = result.outputs.ok_or("entry-run-incomplete")?;
            if let Some(path) = options.results {
                report["phase"] = json!("results");
                let encoded = files::run_outputs(&outputs, host.limits().capacity)?;
                report["phase"] = json!("publication");
                publish(&path, &encoded)?;
                report["results_published"] = json!(true);
            }
            report["status"] = json!("executed");
        } else if command == "prove" || command == "verify" {
            let producer = command == "prove";
            let host = ProofEntry::admit(package, options.proof, options.setups)?;
            report["entry"] = json!(host.interface().entry());
            report["binding_scope"] = json!(match host.binding_scope() {
                BindingScope::Transcript => "transcript",
                BindingScope::HeaderOnly => "header",
            });
            report["capacity"] = options.proof.capacity.record();
            report["phase"] = json!("inputs");
            let request = host
                .interface()
                .proof_request(&read(inputs, files::MAX_REQUEST_BYTES)?, producer)?;
            protect_materials(&outputs, request.inputs.inputs.values())?;
            let result = if producer {
                if let Some(attempts) = options.attempts {
                    host.prove_attempts(request, attempts)?
                } else {
                    host.prove(request)?
                }
            } else {
                host.verify(
                    request,
                    &read(proof_path.unwrap(), crate::artifact::MAX_PROOF_BYTES)?,
                )?
            };
            report["phase"] = json!("execution");
            report["execution"] = result.native.diagnostics();
            if !result.is_success() {
                return Err(result
                    .output_error
                    .or_else(|| result.native.outcome.err())
                    .unwrap_or_else(|| "entry-proof-incomplete".into()));
            }
            if producer {
                report["phase"] = json!("publication");
                publish(proof_path.unwrap(), result.native.outcome.as_ref().unwrap())?;
                report["proof_bytes"] = json!(result.native.outcome.as_ref().unwrap().len());
                report["proof_published"] = json!(true);
            }
            if let Some(path) = options.results {
                report["phase"] = json!("results");
                let values =
                    files::proof_outputs(result.outputs.as_ref().unwrap(), options.proof.capacity)?;
                report["phase"] = json!("publication");
                publish(&path, &values)?;
                report["results_published"] = json!(true);
            }
            report["status"] = json!(if producer { "produced" } else { "accepted" });
        } else {
            return Err("entry-usage".into());
        }
        report["phase"] = json!("complete");
        Ok(())
    })();
    if let Err(code) = result {
        report["code"] = json!(code);
    }
    report
}
// Publication replaces the directory entry, including a final symlink. Resolve
// the parent only, so aliases of the same destination refuse before execution.
// This is a caller configuration check, not filesystem race isolation.
fn destination(path: &str) -> Result<std::path::PathBuf> {
    let path = std::path::absolute(path).map_err(|_| "entry-output-path")?;
    let parent = path.parent().ok_or("entry-output-path")?;
    let name = path.file_name().ok_or("entry-output-path")?;
    Ok(parent
        .canonicalize()
        .unwrap_or_else(|_| parent.into())
        .join(name))
}
fn protect_destinations(outputs: &[&str], inputs: &[&str]) -> Result<()> {
    let mut selected = BTreeSet::new();
    for output in outputs {
        let output = destination(output)?;
        if !selected.insert(output.clone()) {
            return Err("entry-output-path".into());
        }
        for input in inputs {
            if output == destination(input)?
                || std::fs::canonicalize(input).ok().as_ref() == Some(&output)
            {
                return Err("entry-output-path".into());
            }
        }
    }
    Ok(())
}
// Request decoding has bounded the value tree before this file-reference walk.
fn protect_materials<'a>(
    outputs: &[&str],
    values: impl Iterator<Item = &'a super::Value>,
) -> Result<()> {
    use super::Value;
    use crate::protocol::run::InputValue;
    for value in values {
        match value {
            Value::Leaf(InputValue::ProverKeyFile { path, .. }) => {
                protect_destinations(outputs, &[path])?
            }
            Value::Tuple(values) | Value::Array(values) => {
                protect_materials(outputs, values.iter())?
            }
            Value::Record(values) | Value::Variant { fields: values, .. } => {
                protect_materials(outputs, values.values())?
            }
            Value::Associated(value) => {
                protect_materials(outputs, std::iter::once(value.as_ref()))?
            }
            _ => {}
        }
    }
    Ok(())
}
fn compile(args: &[String]) -> Json {
    let mut report = json!({"format":"zkc.entry-build/1","status":"refused","phase":"arguments"});
    let result = (|| -> Result<()> {
        let mut compiler = "zkc-compile";
        let mut output = None;
        let mut flags = Vec::new();
        let mut sources = Vec::new();
        let mut seen = BTreeSet::new();
        for arg in args {
            let (key, value) = arg.split_once('=').unwrap_or((arg, ""));
            if key != "--module" && key != "--asset" && !seen.insert(key) {
                return Err("entry-option".into());
            }
            match key {
                "--compiler" if !value.is_empty() => compiler = value,
                "--output" if !value.is_empty() => output = Some(value),
                "--entry" | "--module" | "--asset" if !value.is_empty() => {
                    let path = if key == "--module" {
                        value.split_once('=').map(|(_, path)| path)
                    } else if key == "--asset" {
                        value.splitn(3, '=').nth(2)
                    } else {
                        None
                    };
                    if let Some(path) = path {
                        sources.push(path);
                    }
                    flags.push(arg);
                }
                "--no-simplify" | "--release-storage" if value.is_empty() => flags.push(arg),
                _ => return Err("entry-option".into()),
            }
        }
        let output = output.ok_or("entry-usage")?;
        protect_destinations(&[output], &sources)?;
        let selected_compiler = resolve_compiler(compiler)?;
        let compiler_path = std::path::Path::new(compiler);
        if compiler_path.is_absolute() || compiler_path.components().count() > 1 {
            protect_destinations(&[output], &[compiler])?;
        }
        protect_destinations(
            &[output],
            &[selected_compiler.to_str().ok_or("entry-compiler-io")?],
        )?;
        let compiler = selected_compiler;
        report["compiler"] = json!(compiler);
        report["phase"] = json!("compilation");
        let directory = tempfile::tempdir().map_err(|_| "entry-compiler-io")?;
        let captured = crate::host::process::capture(
            Command::new(&compiler)
                .args(["language-package", "--source-format=zkc"])
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
        let pin = Sha256::digest(&bytes).into();
        let package =
            Package::capture(&bytes, &pin, Package::MAX_BYTES).map_err(|e| e.to_string())?;
        let interface = super::Interface::read(&package).map_err(|e| e.to_string())?;
        report["entry"] = json!(interface.entry());
        report["toolchain"] = json!(interface.toolchain());
        report["package_sha256"] = json!(hex(&pin));
        report["phase"] = json!("publication");
        publish(output, &bytes)?;
        report["status"] = json!("compiled");
        report["phase"] = json!("complete");
        Ok(())
    })();
    if let Err(code) = result {
        report["code"] = json!(code);
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
