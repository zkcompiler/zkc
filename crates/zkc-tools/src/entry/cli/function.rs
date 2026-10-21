//! Function execution delegates admission, preparation and control to EntryHost.
use super::*;
use crate::entry::{FunctionEntry, FunctionOptions, FunctionRequest};
use crate::project::CheckedInterface;

pub(super) fn execute(
    package: Package,
    interface: &CheckedInterface,
    args: &Arguments<'_>,
    invocation: invocation::Invocation,
    mut destinations: Outputs,
    checking: bool,
    report: &mut Json,
) -> Result<()> {
    let CheckedInterface::Function(interface) = interface else {
        return Err("source-entry-selection".into());
    };
    let options = Options::parse(args)?;
    let capacity = options.run.capacity;
    report["capacity"] = capacity.record();
    report["phase"] = json!("invocation");
    let output_setups = invocation.results.is_some()
        && interface
            .signature()
            .result
            .leaves
            .iter()
            .filter_map(|leaf| interface.logical_type(leaf))
            .any(|ty| zkc_backends::requires_setup(ty.clone()));
    let mut bindings = context::Bindings::load(args, capacity, output_setups)?;
    bindings.protect(&mut destinations)?;
    let deployments = crate::entry::FunctionInterface::deployment_interfaces(&package)?;
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
    bindings.decode_inputs(&deployments, &mut documents, report)?;
    report["deployments"] = json!(
        bindings
            .authority
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
    report["phase"] = json!("admission");
    let host = FunctionEntry::admit(
        package,
        FunctionOptions {
            limits: options.run,
            binding: options.proof.binding,
            ..Default::default()
        },
        std::mem::take(&mut bindings.authority),
    )?;
    bindings.check_operations(host.deployments())?;
    if invocation.results.is_some() {
        let types = interface
            .signature()
            .result
            .leaves
            .iter()
            .map(|leaf| {
                let logical = interface.logical_type(leaf).ok_or("entry-output-codec")?;
                zkc_runtime::vm::PhysicalType::default_for(logical.clone())
                    .map_err(|_| "entry-output-codec")
            })
            .collect::<std::result::Result<Vec<_>, _>>()?;
        invocation.check_results(types.iter())?;
    }
    report["phase"] = json!("inputs");
    let path = invocation.inputs.get("arguments");
    let arguments = documents
        .load(&interface.input_group(), path.map(|p| p.as_path()))
        .map_err(|e| {
            report["input_path"] = json!(e.path);
            if let Some(path) = path {
                report["input_file"] = json!(path);
            }
            e.code
        })?;
    documents.protect(&mut destinations)?;
    let request = FunctionRequest {
        arguments,
        context: bindings.context,
    };
    if checking {
        host.check_inputs(request)?;
        report["status"] = json!("inputs-checked");
    } else {
        let prepared = host.prepare(request)?;
        report["phase"] = json!("execution");
        let result = prepared.execute();
        report["execution"] = result.diagnostics();
        if let Some(failure) = &result.failure {
            return Err(failure.code.clone());
        }
        let value = result.value.ok_or("entry-function-incomplete")?;
        if invocation.results.is_some() {
            report["phase"] = json!("results");
            let encoded =
                files::function_output(&value.into_value(), capacity, bindings.output_setups)?;
            report["phase"] = json!("publication");
            destinations.publish(&[("results", &encoded)], report)?;
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
