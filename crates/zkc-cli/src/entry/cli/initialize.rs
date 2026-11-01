use super::*;

use crate::project::{
    CheckedInterface, Compiler, EntryKind, Preparation, Project, Template, input_path,
};

pub(super) fn project(command: &str, args: &Arguments<'_>, report: &mut Json) -> Result<()> {
    let directory = std::path::absolute(args.positional.first().copied().unwrap_or("."))
        .map_err(|_| "source-project-io")?;
    directory.to_str().ok_or("source-project-format")?;
    let manifest = directory.join("zkc.toml");
    let compiler = Compiler::new(args.value("--compiler").unwrap_or("zkc-compile"))
        .map_err(|e| crate::project::cli::compiler_error(report, e))?;
    if command == "new" {
        std::fs::create_dir(&directory).map_err(|e| {
            if e.kind() == std::io::ErrorKind::AlreadyExists {
                if manifest.symlink_metadata().is_ok() {
                    "source-project-exists"
                } else if directory.is_dir() {
                    "source-directory-exists"
                } else {
                    "source-project-directory"
                }
            } else {
                "source-project-io"
            }
        })?;
    } else if !directory.is_dir() {
        return Err("source-project-directory".into());
    }
    if manifest.symlink_metadata().is_ok() {
        return Err("source-project-exists".into());
    }
    report["project"] = json!(manifest);
    report["mode"] = json!("project");
    report["compiler"] = json!(compiler.path());
    create(&Template::scaffold(&directory), false, report, |_| Ok(()))?;
    let project = Project::load(&manifest)?;
    report["phase"] = json!("preparation");
    let plan = compiler
        .prepare(&project, None, None)
        .map_err(|e| crate::project::cli::compiler_error(report, e))?;
    create(&plan.templates, true, report, |outputs| {
        outputs.protect(project.paths())
    })?;
    describe_plan(&plan.entries, report);
    report["status"] = json!("initialized");
    report["phase"] = json!("complete");
    Ok(())
}

pub(super) fn prepare(args: &Arguments<'_>, report: &mut Json) -> Result<()> {
    let target = Input::load(args, report)?;
    let output = args.value("--output").map(std::path::Path::new);
    report["phase"] = json!("preparation");
    let plan = match &target {
        Input::Project(source) => source
            .compiler
            .prepare(&source.project, args.positional.first().copied(), output)
            .map_err(|e| crate::project::cli::compiler_error(report, e))?,
        Input::Package { .. } => {
            let directory = output.ok_or("source-output-required")?;
            let interface = target.inspect(None, report)?;
            Preparation {
                templates: Template::inputs(directory, &interface)?,
                entries: vec![interface],
            }
        }
    };
    describe_plan(&plan.entries, report);
    for (interface, entry) in plan
        .entries
        .iter()
        .zip(report["entries"].as_array_mut().unwrap())
    {
        let directory = match output {
            Some(directory) => directory.to_path_buf(),
            None => match &target {
                Input::Project(source) => {
                    source.project.layout().unwrap().inputs(interface.entry())?
                }
                Input::Package { .. } => unreachable!(),
            },
        };
        let commands = commands(&target, interface, &directory)?;
        if interface.kind() == EntryKind::Function {
            if let Input::Package { package, .. } = &target {
                let deployments = crate::entry::FunctionInterface::deployment_interfaces(package)?;
                entry["requirements"] = deployment_requirements(&deployments);
            }
            let mut check = commands[0].as_array().unwrap().clone();
            check.push(json!("--dry-run"));
            entry["requirements"]["check_command"] = json!(check);
        }
        entry["commands"] = commands;
    }
    create(&plan.templates, true, report, |outputs| {
        target.protect(outputs)
    })?;
    report["status"] = json!("prepared");
    report["phase"] = json!("complete");
    Ok(())
}

fn describe_plan(interfaces: &[CheckedInterface], report: &mut Json) {
    report["entries"] = json!(interfaces.iter().map(|interface| json!({
        "name": interface.entry(),
        "kind": interface.kind(),
        "input_groups": interface.input_groups().iter().map(|g| g.describe()).collect::<Vec<_>>(),
        "requirements": requirements(interface),
    })).collect::<Vec<_>>());
}
fn requirements(interface: &CheckedInterface) -> Json {
    match interface {
        CheckedInterface::Proof(v) => json!({
            "allow_authored": v.requires_authored_binding(),
            "setups": v.setup_names().collect::<Vec<_>>(),
        }),
        // The logical function interface has no child policy inventory.
        CheckedInterface::Function(_) => json!({
            "invocations": "--invocations=FILE",
            "allow_authored": null,
            "unresolved": ["child_policies"],
        }),
    }
}
fn deployment_requirements(deployments: &[crate::entry::DeploymentInterface]) -> Json {
    let authored =
        |child: &crate::entry::DeploymentInterface| child.interface().requires_authored_binding();
    json!({
        "invocations": "--invocations=FILE",
        "allow_authored": deployments.iter().any(authored),
        "deployments": deployments.iter().map(|child| json!({
            "id": child.id(),
            "entry": child.interface().entry(),
            "operation": child.operation(),
            "allow_authored": authored(child),
            "setups": child.interface().setup_names().collect::<Vec<_>>(),
        })).collect::<Vec<_>>(),
    })
}
fn commands(
    target: &Input,
    interface: &CheckedInterface,
    directory: &std::path::Path,
) -> Result<Json> {
    let project_defaults =
        matches!(target, Input::Project(source) if source.project.layout().is_some());
    let groups = interface.input_groups();
    let selection: Vec<String> = match target {
        Input::Project(source) => {
            let mut v = vec![
                interface.entry().into(),
                format!("--compiler={}", source.compiler.path().display()),
            ];
            if let Some(manifest) = source.project.manifest() {
                v.push(format!("--project={}", manifest.display()));
            } else {
                v.extend(source.explicit_selection.clone());
            }
            v
        }
        Input::Package { path, pin, .. } => {
            vec![format!("--package={path}"), format!("--sha256={pin}")]
        }
    };
    let file = |name: &str| -> Result<String> {
        Ok(format!(
            "--{}={}",
            name,
            input_path(directory, name)?.display()
        ))
    };
    let mut commands = Vec::new();
    for command in if interface.kind() == EntryKind::Proof {
        vec!["prove", "verify"]
    } else {
        vec!["run"]
    } {
        let mut args = vec!["zkc".to_owned(), command.into()];
        args.extend(selection.clone());
        if interface.kind() == EntryKind::Proof {
            if !groups[0].is_empty() {
                args.push(file("public")?);
            }
            if command == "prove" && !groups[1].is_empty() {
                args.push(file("witness")?);
            }
            if !project_defaults {
                args.push(
                    if command == "prove" {
                        "--output=proof.zkproof"
                    } else {
                        "--proof=proof.zkproof"
                    }
                    .into(),
                );
            }
        } else {
            args.push(format!(
                "--input={}",
                input_path(directory, "arguments")?.display()
            ));
        }
        commands.push(args);
    }
    Ok(json!(commands))
}

fn create(
    templates: &[Template],
    preserve: bool,
    report: &mut Json,
    protect: impl FnOnce(&mut Outputs) -> Result<()>,
) -> Result<()> {
    use std::io::ErrorKind;
    let mut pending = Vec::new();
    let mut preserved = Vec::new();
    let mut names = std::collections::BTreeSet::new();
    for template in templates {
        let path = template.path.to_str().ok_or("entry-output-path")?;
        if !names.insert(path.to_ascii_lowercase()) {
            return Err("source-output-collision".into());
        }
        match template.path.symlink_metadata() {
            Err(e) if e.kind() == ErrorKind::NotFound => pending.push(template),
            Ok(metadata) if preserve && metadata.is_file() => preserved.push(path),
            Ok(_) => {
                report["conflict"] = json!(path);
                return Err("entry-output-exists".into());
            }
            Err(_) => return Err("artifact-publish-io".into()),
        }
    }
    for template in &pending {
        std::fs::create_dir_all(template.path.parent().ok_or("entry-output-path")?)
            .map_err(|_| "entry-output-directory")?;
    }
    let paths = pending
        .iter()
        .map(|t| t.path.to_str().unwrap())
        .collect::<Vec<_>>();
    let mut outputs = Outputs::new(&paths, &[])?;
    protect(&mut outputs)?;
    let bytes = pending
        .iter()
        .map(|t| (t.path.to_str().unwrap(), t.contents.as_bytes()))
        .collect::<Vec<_>>();
    crate::files::publication(outputs.create(&bytes), report, false)?;
    let files = report
        .as_object_mut()
        .unwrap()
        .entry("files")
        .or_insert_with(|| json!([]));
    files
        .as_array_mut()
        .unwrap()
        .extend(paths.iter().map(|p| json!(p)));
    report["preserved"] = json!(preserved);
    Ok(())
}
