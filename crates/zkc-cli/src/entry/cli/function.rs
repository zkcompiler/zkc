//! Function commands delegate admission, preparation and control to FunctionEntry.
use super::*;
use crate::entry::{FunctionEntry, FunctionOptions, FunctionRequest};
use crate::project::CheckedInterface;

pub(super) fn execute(
    package: Package,
    interface: &CheckedInterface,
    args: &Arguments<'_>,
    invocation: invocation::Invocation,
    mut destinations: Outputs,
    cpu: &CpuExecution,
    report: &mut Json,
) -> Result<()> {
    let checking = args.has("--dry-run");
    let CheckedInterface::Function(interface) = interface else {
        return Err("source-entry-selection".into());
    };
    let options = Options::parse(args)?;
    let capacity = options.run.capacity;
    report["capacity"] = capacity.record();
    report["material_limits"] = options.run.material.record();
    report["phase"] = json!("invocation");
    let output_setups = invocation.results.is_some() && interface.result_requires_setup();
    let mut bindings = files::Invocations::load(
        args.value("--invocations").map(std::path::Path::new),
        &options.run,
        output_setups,
    )?;
    bindings.protect(&mut destinations)?;
    // Children are read under the same interface selection that admits them.
    let deployments = crate::entry::FunctionInterface::deployment_interfaces_with(
        &package,
        options.run.interface,
    )?;
    let requirements = json!(
        deployments
            .iter()
            .map(crate::entry::DeploymentInterface::describe)
            .collect::<Vec<_>>()
    );
    describe_roles(&requirements, report);
    report["invocations"] = requirements;
    bindings.complete(&deployments)?;
    let mut documents = files::Documents::new(capacity)?;
    measured(
        args,
        report,
        "invocation_input_decoding_and_validation",
        |report| {
            bindings
                .decode_inputs(&deployments, &mut documents)
                .map_err(|e| {
                    if let Some(path) = e.document {
                        report["input_file"] = json!(path);
                    }
                    if let Some(path) = e.path {
                        report["input_path"] = json!(path);
                    }
                    e.code
                })
        },
    )?;
    report["deployments"] = json!(
        bindings
            .authority()
            .iter()
            .map(|(id, a)| (
                id,
                a.keys
                    .iter()
                    .map(|(slot, pin)| (slot, hex(pin)))
                    .collect::<std::collections::BTreeMap<_, _>>()
            ))
            .collect::<std::collections::BTreeMap<_, _>>()
    );
    let (authority, context, result_encoder) = bindings.into_parts();
    report["phase"] = json!("admission");
    let host = measured(args, report, "admission", |_| {
        FunctionEntry::admit_with_cpu(
            package,
            FunctionOptions {
                limits: options.run,
                binding: options.proof.binding,
                ..Default::default()
            },
            authority,
            cpu.clone(),
        )
    })?;
    if invocation.results.is_some() {
        host.check_result_encoding()?;
    }
    report["phase"] = json!("inputs");
    let path = invocation.inputs.get("arguments");
    let arguments = measured(args, report, "input_decoding_and_validation", |report| {
        documents
            .load(&interface.input_group(), path.map(|p| p.as_path()))
            .map_err(|e| {
                report["input_path"] = json!(e.path);
                if let Some(path) = path {
                    report["input_file"] = json!(path);
                }
                e.code
            })
    })?;
    documents.protect(&mut destinations)?;
    let request = FunctionRequest { arguments, context };
    if checking {
        host.check_inputs(request)?;
        report["status"] = json!("inputs-checked");
    } else {
        let prepared = measured(args, report, "preparation", |_| host.prepare(request))?;
        report["phase"] = json!("execution");
        let result = measured(args, report, "sdk_execution", |_| prepared.execute());
        if args.has("--instrument") {
            report["execution_counts"] = json!(result.execution_counts.json());
            report["binding_contexts"] = json!(result.execution_counts.binding_contexts());
        }
        report["execution"] = measured(args, report, "diagnostic_materialization", |_| {
            result.diagnostics()
        });
        if let Some(failure) = &result.failure {
            return Err(failure.code.clone());
        }
        if result.value.is_none() {
            return Err("entry-function-incomplete".into());
        }
        if invocation.results.is_some() {
            measured(args, report, "output_encoding_and_publication", |report| {
                report["phase"] = json!("results");
                // The invocation ledger that charged execution also charges
                // the encoded buffer, which stays live through publication.
                let encoded = result_encoder.encode_report(&result, cpu.clone())?;
                report["phase"] = json!("publication");
                crate::files::publication(
                    destinations.publish(&[("results", encoded.as_bytes())]),
                    report,
                    true,
                )
            })?;
        }
        report["status"] = json!("executed");
    }
    report["phase"] = json!("complete");
    Ok(())
}

fn describe_roles(requirements: &Json, report: &mut Json) {
    let names = requirements
        .as_array()
        .into_iter()
        .flatten()
        .filter_map(|row| {
            let id = row["id"].as_str()?;
            let roles = row["roles"]
                .as_array()?
                .iter()
                .filter_map(|r| Some((r["native_role"].as_str()?, r["role"].as_str()?)))
                .collect::<std::collections::BTreeMap<_, _>>();
            Some((id, roles))
        })
        .collect::<std::collections::BTreeMap<_, _>>();
    if names.len() == 1 {
        report["role_names"] = json!(names.values().next().unwrap());
    }
    report["invocation_role_names"] = json!(names);
}
