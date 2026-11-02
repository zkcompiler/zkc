//! Produce the common-input context of one Run deployment, for distribution
//! under an externally trusted pin. Producing it confers no trust.
use super::*;
use crate::entry::{FunctionInterface, RoleInputs, RunEntry, RunRequest};
use std::collections::BTreeMap;

pub(super) fn produce(
    package: Package,
    target: &Input,
    args: &Arguments<'_>,
    cpu: &CpuExecution,
    report: &mut Json,
) -> Result<()> {
    let id = args.value("--deployment").ok_or("cli-usage")?;
    let output = args.value("--output").ok_or("cli-usage")?;
    let mut paths = BTreeMap::new();
    for &(key, value) in &args.options {
        if key == "--input" {
            let (role, path) = inputs::assignment(value.unwrap_or(""))?;
            if paths.insert(role, path).is_some() {
                return Err("entry-input-roles".into());
            }
        }
    }
    let options = Options::parse(args)?;
    report["deployment"] = json!(id);
    report["phase"] = json!("admission");
    let child =
        FunctionInterface::run_deployment_package_with(&package, id, options.run.interface)?;
    let run = RunEntry::admit_with_cpu(child, options.run.clone(), options.setups, cpu.clone())?;
    report["capacity"] = options.run.capacity.record();
    report["material_limits"] = options.run.material.record();
    report["phase"] = json!("inputs");
    let mut documents =
        files::Documents::with_installation(options.run.capacity, run.installation().clone())?;
    let mut roles = BTreeMap::new();
    for group in run.interface().input_groups() {
        let path = paths.remove(group.name());
        let inputs = documents
            .load(&group, path.map(std::path::Path::new))
            .map_err(|e| {
                report["input_path"] = json!(e.path);
                e.code
            })?;
        roles.insert(
            group.name().to_owned(),
            RoleInputs {
                inputs,
                ..Default::default()
            },
        );
    }
    if !paths.is_empty() {
        return Err("entry-input-roles".into());
    }
    let mut destinations = Outputs::new(&[output], &[])?;
    target.protect(&mut destinations)?;
    documents.protect(&mut destinations)?;
    invocation::protect_options(args, &mut destinations)?;
    destinations.protect(paths_of(args))?;
    report["phase"] = json!("preparation");
    let bytes = run.common_input_context(RunRequest {
        session: "common-inputs".into(),
        roles,
        setups: options.material,
    })?;
    report["context_sha256"] = json!(hex(&Sha256::digest(&bytes)));
    report["context_bytes"] = json!(bytes.len());
    report["phase"] = json!("publication");
    crate::files::publication(destinations.publish(&[("context", &bytes)]), report, true)?;
    report["status"] = json!("produced");
    report["phase"] = json!("complete");
    Ok(())
}
fn paths_of<'a>(args: &'a Arguments<'_>) -> Vec<&'a str> {
    args.options
        .iter()
        .filter(|(key, _)| *key == "--input")
        .filter_map(|(_, value)| inputs::assignment(value.unwrap_or("")).ok())
        .map(|(_, path)| path)
        .collect()
}
