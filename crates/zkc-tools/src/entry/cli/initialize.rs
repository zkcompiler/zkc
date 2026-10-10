use super::*;
use std::path::{Path, PathBuf};

pub(super) fn project(args: &Arguments<'_>, report: &mut Json) -> Result<()> {
    let directory = Path::new(args.positional.first().copied().unwrap_or("."));
    std::fs::create_dir_all(directory).map_err(|_| "entry-output-directory")?;
    let contents = [
        (
            "zkc.toml",
            r#"format = "zkc.project/0"

[modules]
example = "main.zkc"
example_protocol = "protocol.zkc"
"#,
        ),
        (
            "protocol.zkc",
            r#"module example_protocol;

pub protocol Echo roles(P)(value: index @P) -> (result: index @P) {
  return value;
}
"#,
        ),
        (
            "main.zkc",
            r#"module example;
use example_protocol::{Echo};

run Main = Echo;
"#,
        ),
    ];
    create(directory, &contents, report, |_| Ok(()))?;
    let manifest = directory.join("zkc.toml");
    let project = format!("--project={}", manifest.display());
    report["project"] = json!(manifest);
    report["next"] = json!([
        ["zkc", "check", &project],
        ["zkc", "inputs", "init", &project]
    ]);
    report["status"] = json!("initialized");
    report["phase"] = json!("complete");
    Ok(())
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
            Target::Project(source) => {
                let manifest = source.project.manifest().ok_or("source-output-required")?;
                let name = crate::project::output::portable_name(interface.entry(), "")?;
                let parent = manifest
                    .parent()
                    .ok_or("source-project-format")?
                    .join("inputs");
                crate::project::output::check_collision(&parent, &name)?;
                parent.join(name)
            }
            Target::Package { .. } => return Err("source-output-required".into()),
        },
    };
    let groups = interface.input_groups();
    let contents: Vec<_> = groups
        .iter()
        .filter(|g| !g.is_empty())
        .map(|g| {
            (
                format!("{}.json", g.name()),
                serde_json::to_string_pretty(&g.template()).expect("serializable template") + "\n",
            )
        })
        .collect();
    std::fs::create_dir_all(&directory).map_err(|_| "entry-output-directory")?;
    let borrowed: Vec<_> = contents
        .iter()
        .map(|(name, body)| (name.as_str(), body.as_str()))
        .collect();
    create(&directory, &borrowed, report, |outputs| {
        target.protect(outputs)
    })?;
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
    let file = |name: &str| {
        format!(
            "--{}={}",
            name,
            directory.join(format!("{name}.json")).display()
        )
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
                args.push(file("public"));
            }
            if command == "prove" && !groups[1].is_empty() {
                args.push(file("witness"));
            }
            args.push(
                if command == "prove" {
                    "--output=proof.zkproof"
                } else {
                    "--proof=proof.zkproof"
                }
                .into(),
            );
        } else {
            args.push("--session=example".into());
            for group in &groups {
                if !group.is_empty() {
                    args.push(format!(
                        "--input={}={}",
                        group.name(),
                        directory.join(format!("{}.json", group.name())).display()
                    ));
                }
            }
        }
        commands.push(args);
    }
    report["commands"] = json!(commands);
    report["requirements"] = json!({
        "allow_header_only": interface.proof().is_some_and(|p| p.suite.is_none()),
        "setups": interface.setup_names().collect::<Vec<_>>(),
    });
    report["status"] = json!("initialized");
    report["phase"] = json!("complete");
    Ok(())
}
fn create(
    directory: &Path,
    contents: &[(&str, &str)],
    report: &mut Json,
    protect: impl FnOnce(&mut Outputs) -> Result<()>,
) -> Result<()> {
    let paths = contents
        .iter()
        .map(|(name, _)| {
            directory
                .join(name)
                .to_str()
                .map(str::to_owned)
                .ok_or("entry-output-path")
        })
        .collect::<std::result::Result<Vec<_>, _>>()?;
    let mut outputs = Outputs::new(&paths.iter().map(String::as_str).collect::<Vec<_>>(), &[])?;
    protect(&mut outputs)?;
    let bytes = contents
        .iter()
        .map(|(name, body)| (*name, body.as_bytes()))
        .collect::<Vec<_>>();
    outputs.create(&bytes, report)?;
    report["files"] = json!(paths);
    Ok(())
}
