//! Thin command orchestration over project compilation and the shared Entry Host.
mod initialize;
mod inputs;
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
use target::Target;
type Result<T> = std::result::Result<T, String>;

pub(crate) fn run(command: &str, args: &Arguments<'_>) -> Json {
    let format = match command {
        "inspect" => "zkc.entry-inspection/0",
        "inputs init" | "init" => "zkc.project-init/0",
        _ => "zkc.entry-result/0",
    };
    let mut report = json!({"format":format,"status":"refused","phase":"arguments"});
    if let Err(code) = execute(command, args, &mut report) {
        report["code"] = json!(output_error(code));
    }
    report
}
fn execute(command: &str, args: &Arguments<'_>, report: &mut Json) -> Result<()> {
    if command == "init" {
        return initialize::project(args, report);
    }
    Target::validate(args)?;
    let checking = command == "inputs check";
    let operation = if checking {
        Some(Operation::parse(
            args.value("--operation").ok_or("cli-usage")?,
        )?)
    } else if matches!(command, "run" | "prove" | "verify") {
        Some(Operation::parse(command)?)
    } else {
        None
    };
    if let Some(operation) = operation {
        operation.validate(args, checking)?;
    }
    if command == "bindings" && !args.has("--output") {
        return Err("cli-usage".into());
    }
    let mut protected = Vec::new();
    for &(key, value) in &args.options {
        let value = value.unwrap_or("");
        match key {
            "--setups" | "--capacity" | "--limits" | "--public" | "--witness" | "--proof" => {
                protected.push(value)
            }
            "--input" | "--key" => protected.push(inputs::assignment(value)?.1),
            _ => {}
        }
    }
    let outputs: Vec<_> = if command == "inputs init" {
        vec![]
    } else {
        [args.value("--output"), args.value("--results")]
            .into_iter()
            .flatten()
            .collect()
    };
    let mut destinations = Outputs::new(&outputs, &protected)?;
    let target = Target::load(args, &mut destinations, report)?;
    let name = args.positional.first().copied();
    if matches!(command, "inspect" | "inputs init") {
        report["phase"] = json!("interface");
        let interface = target.inspect(name, report)?;
        report["entry"] = json!(interface.entry());
        if command == "inputs init" {
            return initialize::inputs(&target, &interface, args, report);
        }
        report["interface"] = interface.describe();
        report["status"] = json!("inspected");
        report["phase"] = json!("complete");
        return Ok(());
    }
    let mut options = Options::parse(args)?;
    report["phase"] = json!("compilation");
    let package = target.compile(name, operation.map(Operation::kind), report)?;
    if command == "bindings" {
        let source = super::bindings::rust(&package)?;
        report["phase"] = json!("publication");
        destinations.publish(&[("bindings", source.as_bytes())], report)?;
        report["status"] = json!("generated");
        report["phase"] = json!("complete");
        return Ok(());
    }
    let operation = operation.expect("execution command");
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
        let host = RunEntry::admit(package, options.run, options.setups.clone())?;
        report["entry"] = json!(host.interface().entry());
        report["capacity"] = host.limits().capacity.record();
        report["phase"] = json!("inputs");
        let Request::Run(request) =
            options.request(host.interface(), args, operation, &mut documents, report)?
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
            let output_setups = if args.has("--results") {
                files::output_setups_with(
                    &request.setups,
                    &options.setups,
                    host.limits().capacity,
                    &mut imports,
                )?
            } else {
                Default::default()
            };
            let prepared = host.prepare_with(request, &mut imports)?;
            let result = prepared.execute();
            report["phase"] = json!("execution");
            report["execution"] = result.native.diagnostics();
            if let Some(error) = result.output_error {
                return Err(error);
            }
            let outputs = result.outputs.ok_or_else(|| {
                result
                    .native
                    .failure
                    .unwrap_or_else(|| "entry-run-incomplete".into())
            })?;
            if args.has("--results") {
                report["phase"] = json!("results");
                let encoded = files::run_outputs(&outputs, host.limits().capacity, output_setups)?;
                report["phase"] = json!("publication");
                destinations.publish(&[("results", &encoded)], report)?;
            }
            report["status"] = json!("executed");
        }
    } else {
        let host = ProofEntry::admit(package, options.proof, options.setups.clone())?;
        report["entry"] = json!(host.interface().entry());
        report["binding_scope"] = json!(match host.binding_scope() {
            BindingScope::Transcript => "transcript",
            BindingScope::HeaderOnly => "header",
        });
        report["capacity"] = options.proof.capacity.record();
        report["phase"] = json!("inputs");
        let Request::Proof(request) =
            options.request(host.interface(), args, operation, &mut documents, report)?
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
            let output_setups = if args.has("--results") {
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
                    args.value("--proof").unwrap(),
                    crate::proof::MAX_PROOF_BYTES,
                )?)
            } else {
                None
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
            let proof = (operation == Operation::Prove)
                .then(|| result.native.outcome.as_ref().unwrap().as_slice());
            publish_proof(&destinations, proof, report, || {
                args.has("--results")
                    .then(|| {
                        files::proof_outputs(
                            result.outputs.as_ref().unwrap(),
                            options.proof.capacity,
                            output_setups,
                        )
                    })
                    .transpose()
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
