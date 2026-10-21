//! Thin command orchestration over project compilation and the shared Entry Host.
mod initialize;
mod inputs;
mod invocation;
mod target;
use super::{
    AttemptOptions, BindingPolicy, BindingScope, BoundInterface, Interface, Package, ProofEntry,
    ProofOperation, ProofOptions, ProofRequest, RoleInputs, RunEntry, RunRequest, SetupAuthority,
    files,
};
use crate::{
    cli::Arguments,
    host::{
        inputs::{digest, hex, read_regular as read},
        publication::Outputs,
    },
    run::HostLimits,
};
use inputs::{Operation, Options, Request};
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
        destinations.publish(&[("bindings", source.as_bytes())], report)?;
        report["status"] = json!("generated");
        report["phase"] = json!("complete");
        return Ok(());
    }
    let operation = operation.expect("execution command");
    let view = BoundInterface::read(&package).map_err(|e| e.to_string())?;
    report["entry"] = json!(view.entry());
    report["role_names"] = json!(
        view.roles()
            .iter()
            .map(|role| (&role.native_name, &role.name))
            .collect::<std::collections::BTreeMap<_, _>>()
    );
    report["phase"] = json!("invocation");
    let layout = match &target {
        Target::Project(source) => source.project.layout(),
        Target::Package { .. } => None,
    };
    let invocation =
        invocation::Invocation::resolve(&view, layout.as_ref(), args, operation, checking, report)?;
    let mut destinations = invocation.destinations(&target, args)?;
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
    if operation == Operation::Run {
        let host = measured(args, report, "admission", |_| {
            RunEntry::admit(package, options.run, options.setups.clone())
        })?;
        invocation.check_results(host.output_types())?;
        report["entry"] = json!(host.interface().entry());
        report["capacity"] = host.limits().capacity.record();
        report["phase"] = json!("inputs");
        let Request::Run(request) =
            measured(args, report, "input_decoding_and_validation", |report| {
                options.request(
                    host.interface(),
                    &invocation,
                    operation,
                    &mut documents,
                    report,
                )
            })?
        else {
            unreachable!()
        };
        documents.protect(&mut destinations)?;
        if checking {
            host.check_inputs(request)?;
            report["status"] = json!("inputs-checked");
        } else {
            let mut imports = crate::host::setups::VerifierKeys::new(
                host.limits().capacity.backend().ark_bounds(),
            );
            let output_setups = if invocation.results.is_some() {
                files::output_setups_with(
                    &request.setups,
                    &options.setups,
                    host.limits().capacity,
                    &mut imports,
                )?
            } else {
                Default::default()
            };
            let prepared = measured(args, report, "preparation", |_| {
                host.prepare_with(request, &mut imports)
            })?;
            let result = measured(args, report, "sdk_execution", |_| prepared.execute());
            report["phase"] = json!("execution");
            if args.has("--instrument") {
                let mut counts = zkc_runtime::vm::ExecutionCounts::default();
                if let Some(execution) = &result.native.execution {
                    for role in &execution.roles {
                        counts.merge(&role.execution_counts);
                    }
                }
                report["execution_counts"] = json!(counts.json());
                report["binding_contexts"] = json!(counts.binding_contexts());
            }
            report["execution"] = measured(args, report, "diagnostic_materialization", |_| {
                result.native.diagnostics()
            });
            if let Some(error) = result.output_error {
                return Err(error);
            }
            let outputs = result.outputs.ok_or_else(|| {
                result
                    .native
                    .failure
                    .unwrap_or_else(|| "entry-run-incomplete".into())
            })?;
            if invocation.results.is_some() {
                measured(args, report, "output_encoding_and_publication", |report| {
                    report["phase"] = json!("results");
                    let encoded =
                        files::run_outputs(&outputs, host.limits().capacity, output_setups)?;
                    report["phase"] = json!("publication");
                    destinations.publish(&[("results", &encoded)], report)
                })?;
            }
            report["status"] = json!("executed");
        }
    } else {
        let host = measured(args, report, "admission", |_| {
            ProofEntry::admit(package, options.proof, options.setups.clone())
        })?;
        invocation.check_results(
            host.output_types(if operation == Operation::Prove {
                ProofOperation::Prove
            } else {
                ProofOperation::Verify
            })
            .iter(),
        )?;
        report["entry"] = json!(host.interface().entry());
        report["binding_scope"] = json!(match host.binding_scope() {
            BindingScope::Transcript => "transcript",
            BindingScope::HeaderOnly => "header",
            BindingScope::Authored => "authored",
        });
        report["capacity"] = options.proof.capacity.record();
        report["phase"] = json!("inputs");
        let Request::Proof(request) =
            measured(args, report, "input_decoding_and_validation", |report| {
                options.request(
                    host.interface(),
                    &invocation,
                    operation,
                    &mut documents,
                    report,
                )
            })?
        else {
            unreachable!()
        };
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
            let mut imports = crate::host::setups::VerifierKeys::new(
                options.proof.capacity.backend().ark_bounds(),
            );
            let output_setups = if invocation.results.is_some() {
                files::output_setups_with(
                    &request.setups,
                    &options.setups,
                    options.proof.capacity,
                    &mut imports,
                )?
            } else {
                Default::default()
            };
            let proof = if operation == Operation::Verify {
                Some(read(
                    invocation
                        .proof
                        .as_ref()
                        .unwrap()
                        .to_str()
                        .ok_or("entry-input-document")?,
                    crate::proof::MAX_PROOF_BYTES,
                )?)
            } else {
                None
            };
            if let Some(bytes) = &proof {
                report["proof_sha256"] = json!(hex(&Sha256::digest(bytes)));
            }
            let result = measured(args, report, "sdk_execution_including_preparation", |_| {
                host.execute_with(request, proof.as_deref(), options.attempts, &mut imports)
            })?;
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
                    .or_else(|| result.native.outcome.err())
                    .unwrap_or_else(|| "entry-proof-incomplete".into()));
            }
            let proof = (operation == Operation::Prove)
                .then(|| result.native.outcome.as_ref().unwrap().as_slice());
            measured(args, report, "output_encoding_and_publication", |report| {
                publish_proof(&destinations, proof, report, || {
                    invocation
                        .results
                        .is_some()
                        .then(|| {
                            files::proof_outputs(
                                result.outputs.as_ref().unwrap(),
                                options.proof.capacity,
                                output_setups,
                            )
                        })
                        .transpose()
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
