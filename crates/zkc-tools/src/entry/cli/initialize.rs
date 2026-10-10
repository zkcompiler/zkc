use super::*;
use std::path::PathBuf;

use crate::project::{Compiler, Project, Template, input_path};

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
        .prepare(&project, None)
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
    let source = crate::project::cli::Source::load(args)?;
    source.describe(report);
    report["phase"] = json!("preparation");
    let plan = source
        .compiler
        .prepare(&source.project, args.positional.first().copied())
        .map_err(|e| crate::project::cli::compiler_error(report, e))?;
    create(&plan.templates, true, report, |outputs| {
        source.protect(outputs)
    })?;
    describe_plan(&plan.entries, report);
    report["status"] = json!("prepared");
    report["phase"] = json!("complete");
    Ok(())
}

fn describe_plan(interfaces: &[Interface], report: &mut Json) {
    report["entries"] = json!(interfaces.iter().map(|interface| json!({
        "name": interface.entry(),
        "input_groups": interface.input_groups().iter().map(|g| g.describe()).collect::<Vec<_>>(),
        "requirements": requirements(interface),
    })).collect::<Vec<_>>());
}
fn requirements(interface: &Interface) -> Json {
    json!({
        "allow_header_only": interface.proof().is_some_and(|p| p.suite.is_none()),
        "setups": interface.setup_names().collect::<Vec<_>>(),
    })
}
pub(super) fn inputs(
    target: &Target,
    interface: &Interface,
    args: &Arguments<'_>,
    report: &mut Json,
) -> Result<()> {
    let directory = match args.value("--output") {
        Some(path) => PathBuf::from(path),
        None => match target {
            Target::Project(source) => source
                .project
                .layout()
                .ok_or("source-output-required")?
                .inputs(interface.entry())?,
            Target::Package { .. } => return Err("source-output-required".into()),
        },
    };
    let project_defaults =
        matches!(target, Target::Project(source) if source.project.layout().is_some());
    let groups = interface.input_groups();
    create(
        &Template::inputs(&directory, interface)?,
        false,
        report,
        |outputs| target.protect(outputs),
    )?;
    report["input_groups"] = json!(groups.iter().map(|g| g.describe()).collect::<Vec<_>>());
    let selection: Vec<String> = match target {
        Target::Project(source) => {
            let mut v = vec![
                interface.entry().into(),
                format!("--compiler={}", source.compiler.path().display()),
            ];
            if let Some(manifest) = source.project.manifest() {
                v.push(format!("--project={}", manifest.display()));
            } else {
                v.extend(source.project.flags.clone());
            }
            v
        }
        Target::Package { path, pin, .. } => {
            vec![format!("--package={path}"), format!("--sha256={pin}")]
        }
    };
    let file = |name: &str| -> Result<String> {
        Ok(format!(
            "--{}={}",
            name,
            input_path(&directory, name)?.display()
        ))
    };
    let mut commands = Vec::new();
    for command in if interface.is_proof() {
        vec!["prove", "verify"]
    } else {
        vec!["run"]
    } {
        let mut args = vec!["zkc".to_owned(), command.into()];
        args.extend(selection.clone());
        if interface.is_proof() {
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
            for group in &groups {
                if !group.is_empty() {
                    args.push(format!(
                        "--input={}={}",
                        group.name(),
                        input_path(&directory, group.name())?.display()
                    ));
                }
            }
        }
        commands.push(args);
    }
    report["commands"] = json!(commands);
    report["requirements"] = requirements(interface);
    report["status"] = json!("initialized");
    report["phase"] = json!("complete");
    Ok(())
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
    outputs.create(&bytes, report)?;
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
