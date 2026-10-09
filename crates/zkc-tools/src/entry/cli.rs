//! Command-line file transport over the common named Entry Host.
use super::{
    AttemptOptions, BindingPolicy, BindingScope, Package, ProofEntry, ProofOptions, RunEntry, files,
};
use crate::cli::Arguments;
use crate::{
    host::{
        inputs::{digest, hex, read_regular as read},
        publication::Outputs,
    },
    run::HostLimits,
};
use serde_json::{Value as Json, json};
use sha2::{Digest, Sha256};
use std::{process::Command, time::Duration};

type Result<T> = std::result::Result<T, String>;
struct Options {
    evaluators: zkc_backends::ring::Registry,
    setups: super::SetupAuthority,
    proof: ProofOptions,
    run: HostLimits,
    attempts: Option<AttemptOptions>,
    results: Option<String>,
    configuration: Vec<String>,
}
impl Options {
    fn parse(args: &Arguments<'_>) -> Result<Self> {
        let mut options = Self {
            evaluators: Default::default(),
            setups: Default::default(),
            proof: Default::default(),
            run: Default::default(),
            attempts: None,
            results: None,
            configuration: Vec::new(),
        };
        for &(key, value) in &args.options {
            let value = value.unwrap_or("");
            if matches!(key, "--setups" | "--capacity" | "--limits" | "--evaluators") {
                options.configuration.push(value.into());
            }
            match key {
                "--evaluators" => {
                    let bytes = read(value, 64 * 1024)?;
                    let row: (String, Vec<(String, String)>) =
                        serde_json::from_slice(&bytes).map_err(|_| "ring-assets-format")?;
                    if row.0 != "zkc.ring-assets/0" || row.1.len() > 256 {
                        return Err("ring-assets-format".into());
                    }
                    for (digest, path) in row.1 {
                        let bytes = read(&path, zkc_runtime::ring::BYTE_LIMIT)?;
                        let text = std::str::from_utf8(&bytes).map_err(|_| "ring-assets-utf8")?;
                        options
                            .evaluators
                            .insert(&digest, text)
                            .map_err(|e| e.to_string())?;
                        options.configuration.push(path);
                    }
                }
                "--setups" => options.setups = files::authority(&read(value, 64 * 1024)?)?,
                "--capacity" => {
                    let capacity = crate::execution::Capacity::parse(&read(value, 4096)?)?;
                    options.proof.capacity = capacity;
                    options.run.capacity = capacity;
                }
                "--limits" => options.run = options.run.with_work_limits(&read(value, 4096)?)?,
                "--allow-header-only" => options.proof.binding = BindingPolicy::AllowHeaderOnly,
                "--attempts" => {
                    let count = value.parse::<u64>().expect("validated count");
                    options.attempts = Some(AttemptOptions {
                        count,
                        ..Default::default()
                    });
                }
                "--results" => options.results = Some(value.into()),
                _ => unreachable!("validated Entry option"),
            }
        }
        Ok(options)
    }
}
/// Exit status is zero only for the requested completed operation.
pub fn succeeded(report: &Json) -> bool {
    matches!(
        report["status"].as_str(),
        Some("compiled" | "inspected" | "executed" | "produced" | "accepted" | "generated")
    )
}
/// Reports preserve reached execution and publication state without returning
/// private values or proof bytes on standard output.
pub(crate) fn run(command: &str, args: &Arguments<'_>) -> Json {
    if command == "compile" {
        return compile(args);
    }
    if command == "inspect" {
        return inspect(args);
    }
    let mut report = json!({"format":"zkc.entry-result/0","status":"refused","phase":"arguments"});
    let result = (|| -> Result<()> {
        let path = args.positional[0];
        let expected = args.positional[1];
        let inputs = args.positional[2];
        let proof_path = args.positional.get(3).copied();
        let pin = digest(expected)?;
        let options = Options::parse(args)?;
        let mut protected = vec![path];
        protected.extend(options.configuration.iter().map(String::as_str));
        let mut outputs = Vec::new();
        if command == "bindings" {
            outputs.push(inputs);
        } else {
            protected.push(inputs);
            if command == "prove" {
                outputs.extend(proof_path);
            } else {
                protected.extend(proof_path);
            }
            outputs.extend(options.results.as_deref());
        }
        let mut destinations = Outputs::new(&outputs, &protected).map_err(output_error)?;
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
            destinations
                .publish(&[("bindings", source.as_bytes())], &mut report)
                .map_err(output_error)?;
            report["status"] = json!("generated");
            report["phase"] = json!("complete");
            return Ok(());
        }
        if command == "run" {
            let host = RunEntry::admit(package, options.run, options.setups.clone())?
                .with_ring_assets(options.evaluators.clone());
            report["entry"] = json!(host.interface().entry());
            report["capacity"] = host.limits().capacity.record();
            report["phase"] = json!("inputs");
            let request = host
                .interface()
                .run_request(&read(inputs, files::MAX_REQUEST_BYTES)?)?;
            protect_materials(
                &mut destinations,
                request.roles.values().flat_map(|role| role.inputs.values()),
            )?;
            let mut imports = crate::host::setups::VerifierKeys::new(
                host.limits().capacity.backend().ark_bounds(),
            );
            let output_setups = if options.results.is_some() {
                files::output_setups_with(
                    &request.setups,
                    &options.setups,
                    host.limits().capacity,
                    &mut imports,
                )?
            } else {
                Default::default()
            };
            let result = host.prepare_with(request, &mut imports)?.execute();
            report["phase"] = json!("execution");
            report["execution"] = result.native.diagnostics();
            if let Some(error) = result.output_error {
                return Err(error);
            }
            let outputs = result.outputs.ok_or("entry-run-incomplete")?;
            if options.results.is_some() {
                report["phase"] = json!("results");
                let encoded = files::run_outputs(&outputs, host.limits().capacity, output_setups)?;
                report["phase"] = json!("publication");
                destinations
                    .publish(&[("results", &encoded)], &mut report)
                    .map_err(output_error)?;
            }
            report["status"] = json!("executed");
        } else if command == "prove" || command == "verify" {
            let producer = command == "prove";
            let host = ProofEntry::admit(package, options.proof, options.setups.clone())?
                .with_ring_assets(options.evaluators.clone());
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
            protect_materials(&mut destinations, request.private.inputs.values())?;
            let mut imports = crate::host::setups::VerifierKeys::new(
                options.proof.capacity.backend().ark_bounds(),
            );
            let output_setups = if options.results.is_some() {
                files::output_setups_with(
                    &request.setups,
                    &options.setups,
                    options.proof.capacity,
                    &mut imports,
                )?
            } else {
                Default::default()
            };
            let proof = if producer {
                None
            } else {
                Some(read(proof_path.unwrap(), crate::proof::MAX_PROOF_BYTES)?)
            };
            let result =
                host.execute_with(request, proof.as_deref(), options.attempts, &mut imports)?;
            report["phase"] = json!("execution");
            report["execution"] = result.native.diagnostics();
            if !result.is_success() {
                return Err(result
                    .output_error
                    .or_else(|| result.native.outcome.err())
                    .unwrap_or_else(|| "entry-proof-incomplete".into()));
            }
            let proof = producer.then(|| result.native.outcome.as_ref().unwrap().as_slice());
            publish_proof(&destinations, proof, &mut report, || {
                options
                    .results
                    .as_ref()
                    .map(|_| {
                        files::proof_outputs(
                            result.outputs.as_ref().unwrap(),
                            options.proof.capacity,
                            output_setups,
                        )
                    })
                    .transpose()
            })?;
            report["status"] = json!(if producer { "produced" } else { "accepted" });
        } else {
            unreachable!("validated Entry command");
        }
        report["phase"] = json!("complete");
        Ok(())
    })();
    if let Err(code) = result {
        report["code"] = json!(code);
    }
    report
}
// Keep the encoding/publication boundary explicit and independently testable.
fn publish_proof(
    destinations: &Outputs,
    proof: Option<&[u8]>,
    report: &mut Json,
    encode_results: impl FnOnce() -> Result<Option<Vec<u8>>>,
) -> Result<()> {
    report["phase"] = json!("results");
    let values = encode_results()?;
    let mut publications = Vec::new();
    if let Some(proof) = proof {
        report["proof_bytes"] = json!(proof.len());
        publications.push(("proof", proof));
    }
    if let Some(values) = &values {
        publications.push(("results", values.as_slice()));
    }
    if !publications.is_empty() {
        report["phase"] = json!("publication");
        destinations
            .publish(&publications, report)
            .map_err(output_error)?;
    }
    Ok(())
}
fn output_error(code: String) -> String {
    if code == "artifact-output-path" {
        "entry-output-path".into()
    } else {
        code
    }
}
// Request decoding has bounded the value tree before this file-reference walk.
fn protect_materials<'a>(
    outputs: &mut Outputs,
    values: impl Iterator<Item = &'a super::Value>,
) -> Result<()> {
    use super::Value;
    use crate::execution::InputValue;
    for value in values {
        match value {
            Value::Leaf(InputValue::ProverKeyFile { path, .. }) => {
                outputs.protect([path.as_str()]).map_err(output_error)?
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
fn inspect(args: &Arguments<'_>) -> Json {
    let mut report =
        json!({"format":"zkc.entry-inspection/0", "status":"refused", "phase":"arguments"});
    let result = (|| -> Result<()> {
        let pin = digest(args.positional[1])?;
        report["phase"] = json!("admission");
        let bytes = read(args.positional[0], Package::MAX_BYTES)?;
        let package =
            Package::capture(&bytes, &pin, Package::MAX_BYTES).map_err(|e| e.to_string())?;
        let interface = super::Interface::read(&package).map_err(|e| e.to_string())?;
        report["package_sha256"] = json!(hex(package.identity()));
        report["interface"] = interface.describe();
        report["phase"] = json!("complete");
        report["status"] = json!("inspected");
        Ok(())
    })();
    if let Err(code) = result {
        report["code"] = json!(code);
    }
    report
}

fn compile(args: &Arguments<'_>) -> Json {
    let mut report = json!({"format":"zkc.entry-build/0","status":"refused","phase":"arguments"});
    let result = (|| -> Result<()> {
        let mut compiler = "zkc-compile";
        let mut output = None;
        let mut flags = Vec::new();
        let mut sources = Vec::new();
        for &(key, value) in &args.options {
            let flag = value.map_or_else(|| key.to_owned(), |value| format!("{key}={value}"));
            let value = value.unwrap_or("");
            match key {
                "--compiler" => compiler = value,
                "--output" => output = Some(value),
                "--entry" | "--module" | "--asset" => {
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
                    flags.push(flag);
                }
                "--no-simplify" | "--release-storage" => flags.push(flag),
                _ => unreachable!("validated Entry option"),
            }
        }
        let output = output.expect("validated required output");
        let mut destinations = Outputs::new(&[output], &sources).map_err(output_error)?;
        for source in &sources {
            crate::host::io::open_regular(source).map_err(|_| "artifact-io")?;
        }
        let selected_compiler = resolve_compiler(compiler)?;
        let compiler_path = std::path::Path::new(compiler);
        if compiler_path.is_absolute() || compiler_path.components().count() > 1 {
            destinations.protect([compiler]).map_err(output_error)?;
        }
        destinations
            .protect([selected_compiler.to_str().ok_or("entry-compiler-io")?])
            .map_err(output_error)?;
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
        destinations
            .publish(&[("package", &bytes)], &mut report)
            .map_err(output_error)?;
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

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn output_encoding_failure_preserves_existing_proof_and_results() {
        let directory = tempfile::tempdir().unwrap();
        let proof = directory.path().join("proof");
        let results = directory.path().join("results");
        std::fs::write(&proof, b"prior proof").unwrap();
        std::fs::write(&results, b"prior results").unwrap();
        let destinations =
            Outputs::new(&[proof.to_str().unwrap(), results.to_str().unwrap()], &[]).unwrap();
        let capacity = crate::execution::Capacity {
            wire_bytes: 0,
            ..Default::default()
        };
        let values = [(
            "field".into(),
            zkc_backends::Value::Field(zkc_backends::Scalar::from(1)).into(),
        )]
        .into();
        let mut report = json!({"status":"refused"});
        let error = publish_proof(&destinations, Some(b"new proof"), &mut report, || {
            files::proof_outputs(&values, capacity, Default::default()).map(Some)
        })
        .unwrap_err();
        assert_eq!(error, "entry-output-encoding");
        assert_eq!(report["phase"], "results");
        assert_ne!(report["proof_published"], true);
        assert_eq!(std::fs::read(&proof).unwrap(), b"prior proof");
        assert_eq!(std::fs::read(&results).unwrap(), b"prior results");
        assert_eq!(std::fs::read_dir(directory.path()).unwrap().count(), 2);
        publish_proof(&destinations, Some(b"new proof"), &mut report, || {
            Ok(Some(b"new results".to_vec()))
        })
        .unwrap();
        assert_eq!(std::fs::read(&proof).unwrap(), b"new proof");
        assert_eq!(std::fs::read(&results).unwrap(), b"new results");
        assert_eq!(
            report["publication"]["published"],
            json!(["proof", "results"])
        );
    }
}
