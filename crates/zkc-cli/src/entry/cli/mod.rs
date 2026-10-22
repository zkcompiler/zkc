//! Thin command orchestration over project compilation and the shared Entry Host.

mod function;
mod initialize;
mod inputs;
mod invocation;
mod target;
use super::{
    AttemptOptions, BindingPolicy, BindingScope, Interface, Package, ProofEntry, ProofOperation,
    ProofOptions, ProofRequest, RoleInputs, SetupAuthority, files,
};
use crate::{
    cli::Arguments,
    files::{Outputs, digest, hex, read_regular as read},
    run::HostLimits,
};
use inputs::{Operation, Options};
use serde_json::{Value as Json, json};
use sha2::{Digest, Sha256};
use target::Target;
type Result<T> = std::result::Result<T, String>;

pub(crate) fn run(command: &str, args: &Arguments<'_>) -> Json {
    let format = match command {
        "inspect" => "zkc.entry-inspection/0",
        "init" | "new" | "prepare" => "zkc.project-init/0",
        _ => "zkc.entry-result/0",
    };
    let mut report = json!({"format":format,"status":"refused","phase":"arguments"});
    if let Err(code) = execute(command, args, &mut report) {
        report["code"] = json!(output_error(code));
    }
    report
}
/// Inclusive wall times describe existing Host boundaries; they are not additive
/// kernel timings and do not require changing protocol provenance.
fn measured<T>(
    args: &Arguments<'_>,
    report: &mut Json,
    stage: &str,
    action: impl FnOnce(&mut Json) -> T,
) -> T {
    let clock = (args.has("--report") || args.has("--instrument")).then(std::time::Instant::now);
    let result = action(report);
    if let Some(clock) = clock {
        if report.get("host_stages").is_none() {
            report["host_stages"] = json!({});
        }
        report["host_stages"][stage] =
            json!({"inclusive_microseconds": clock.elapsed().as_micros()});
    }
    result
}
fn execute(command: &str, args: &Arguments<'_>, report: &mut Json) -> Result<()> {
    if matches!(command, "init" | "new") {
        return initialize::project(command, args, report);
    }
    Target::validate(args)?;
    if command == "prepare" {
        return initialize::prepare(args, report);
    }
    let checking = args.has("--dry-run");
    if checking {
        report["dry_run"] = json!(true);
    }
    let operation = if matches!(command, "run" | "prove" | "verify") {
        let operation = Operation::parse(command)?;
        operation.validate(args, checking)?;
        Some(operation)
    } else {
        None
    };
    if command == "bindings" && !args.has("--output") {
        return Err("cli-usage".into());
    }
    let target = Target::load(args, report)?;
    let name = args.positional.first().copied();
    if command == "inspect" {
        report["phase"] = json!("interface");
        let interface = target.inspect(name, report)?;
        report["entry"] = json!(interface.entry());
        report["interface"] = interface.describe();
        report["status"] = json!("inspected");
        report["phase"] = json!("complete");
        return Ok(());
    }
    report["phase"] = json!("compilation");
    let package = measured(args, report, "compilation_and_capture", |report| {
        target.compile(name, operation.map(Operation::kind), report)
    })?;
    if command == "bindings" {
        let source = super::bindings::rust(&package)?;
        let mut destinations = Outputs::new(&[args.value("--output").unwrap()], &[])?;
        target.protect(&mut destinations)?;
        invocation::protect_options(args, &mut destinations)?;
        report["phase"] = json!("publication");
        crate::files::publication(
            destinations.publish(&[("bindings", source.as_bytes())]),
            report,
            true,
        )?;
        report["status"] = json!("generated");
        report["phase"] = json!("complete");
        return Ok(());
    }
    let operation = operation.expect("execution command");
    let view = crate::project::CheckedInterface::read(&package)?;
    report["entry"] = json!(view.entry());
    report["phase"] = json!("invocation");
    let layout = match &target {
        Target::Project(source) => source.project.layout(),
        Target::Package { .. } => None,
    };
    let invocation =
        invocation::Invocation::resolve(&view, layout.as_ref(), args, operation, checking, report)?;
    let mut destinations = invocation.destinations(&target, args)?;
    if operation == Operation::Run {
        return function::execute(
            package,
            &view,
            args,
            invocation,
            destinations,
            checking,
            report,
        );
    }
    let mut options = Options::parse(args)?;
    report["setups"] = json!(
        options
            .setups
            .keys
            .iter()
            .map(|(name, pin)| (name, hex(pin)))
            .collect::<std::collections::BTreeMap<_, _>>()
    );
    report["phase"] = json!("admission");
    let mut documents = files::Documents::new(options.proof.capacity)?;
    {
        let host = measured(args, report, "admission", |_| {
            ProofEntry::admit(package, options.proof, options.setups.clone())
        })?;
        if invocation.results.is_some() {
            host.check_result_encoding(if operation == Operation::Prove {
                ProofOperation::Prove
            } else {
                ProofOperation::Verify
            })?;
        }
        report["entry"] = json!(host.interface().entry());
        report["binding_scope"] = json!(match host.binding_scope() {
            BindingScope::Transcript => "transcript",
            BindingScope::HeaderOnly => "header",
            BindingScope::Authored => "authored",
        });
        report["capacity"] = options.proof.capacity.record();
        report["phase"] = json!("inputs");
        report["role_names"] = json!(
            host.interface()
                .role_names()
                .collect::<std::collections::BTreeMap<_, _>>()
        );
        let request = measured(args, report, "input_decoding_and_validation", |report| {
            options.request(
                host.interface(),
                &invocation,
                operation,
                &mut documents,
                report,
            )
        })?;
        documents.protect(&mut destinations)?;
        if checking {
            host.check_inputs(
                request,
                if operation == Operation::Prove {
                    ProofOperation::Prove
                } else {
                    ProofOperation::Verify
                },
                options.attempts,
            )?;
            report["status"] = json!("inputs-checked");
        } else {
            let call = host.prepare_file_call(
                if operation == Operation::Prove {
                    ProofOperation::Prove
                } else {
                    ProofOperation::Verify
                },
                request,
                options.attempts,
                invocation.results.is_some(),
            )?;
            let proof = if operation == Operation::Verify {
                Some(read(
                    invocation
                        .proof
                        .as_ref()
                        .unwrap()
                        .to_str()
                        .ok_or("entry-input-document")?,
                    zkc::proof::MAX_PROOF_BYTES,
                )?)
            } else {
                None
            };
            if let Some(bytes) = &proof {
                report["proof_sha256"] = json!(hex(&Sha256::digest(bytes)));
            }
            let file_result =
                measured(args, report, "sdk_execution_including_preparation", |_| {
                    call.execute(proof.as_deref()).map_err(String::from)
                })?;
            let result = &file_result.report;
            report["phase"] = json!("execution");
            if args.has("--instrument") {
                report["execution_counts"] = json!(result.native.execution_counts.json());
                report["binding_contexts"] =
                    json!(result.native.execution_counts.binding_contexts());
            }
            report["execution"] = measured(args, report, "diagnostic_materialization", |_| {
                result.native.diagnostics()
            });
            if !result.is_success() {
                return Err(result
                    .output_error
                    .clone()
                    .or_else(|| result.native.outcome.as_ref().err().cloned())
                    .unwrap_or_else(|| "entry-proof-incomplete".into()));
            }
            let proof = (operation == Operation::Prove)
                .then(|| result.native.outcome.as_ref().unwrap().as_slice());
            measured(args, report, "output_encoding_and_publication", |report| {
                publish_proof(&destinations, proof, report, || {
                    file_result.encode_results()
                })
            })?;
            report["status"] = json!(if operation == Operation::Prove {
                "produced"
            } else {
                "accepted"
            });
        }
    }
    report["phase"] = json!("complete");
    Ok(())
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
        report["proof_sha256"] = json!(hex(&Sha256::digest(proof)));
        publications.push(("proof", proof));
    }
    if let Some(values) = &values {
        publications.push(("results", values.as_slice()));
    }
    if !publications.is_empty() {
        report["phase"] = json!("publication");
        crate::files::publication(destinations.publish(&publications), report, true)
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
        let values = [("field".into(), crate::entry::Value::from(true))].into();
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
