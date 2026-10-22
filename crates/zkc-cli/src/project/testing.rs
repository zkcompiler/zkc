//! Execute checked manifest recipes through the command interface.
use crate::cli::Arguments;
use serde_json::{Value, json};
use zkc::project::{Compiler, Project};

pub(crate) fn run(args: &Arguments<'_>) -> Value {
    let mut report = json!({"format":"zkc.project-tests/0","status":"refused","phase":"selection"});
    let result = (|| -> Result<(), String> {
        let project = match args.value("--project") {
            Some(path) => Project::load(path)?,
            None => Project::discover()?,
        };
        project.settings(args.value("--profile"), &Default::default())?;
        let manifest = project.manifest().ok_or("source-project-required")?;
        let compiler =
            Compiler::new(args.value("--compiler").unwrap_or("zkc-compile")).map_err(|e| e.code)?;
        let selected = args.positional.first().copied();
        if selected.is_some_and(|name| !project.tests().contains_key(name)) {
            return Err("source-test-missing".into());
        }
        if project.tests().is_empty() {
            return Err("source-test-empty".into());
        }
        let mut records = Vec::new();
        let mut passed = true;
        for (name, recipe) in project.tests() {
            if selected.is_some_and(|s| s != name) {
                continue;
            }
            // Relative paths in recipes are resolved beside their owning manifest
            // by the CLI's existing project layout, or explicitly by this adapter.
            let mut arguments = vec![
                recipe.entry.clone(),
                format!("--project={}", manifest.display()),
                format!("--compiler={}", compiler.path().display()),
            ];
            if let Some(profile) = args.value("--profile")
                && recipe.operation != "check"
            {
                arguments.push(format!("--profile={profile}"));
            }
            for argument in &recipe.args {
                let resolved = if let Some((flag, value)) = argument.split_once('=') {
                    if [
                        "--input",
                        "--invocations",
                        "--public",
                        "--witness",
                        "--proof",
                        "--output",
                        "--results",
                        "--setups",
                        "--capacity",
                        "--limits",
                    ]
                    .contains(&flag)
                    {
                        format!(
                            "{flag}={}",
                            manifest.parent().unwrap().join(value).display()
                        )
                    } else if flag == "--key" {
                        let (name, path) = value.split_once('=').ok_or("source-test-format")?;
                        format!(
                            "{flag}={name}={}",
                            manifest.parent().unwrap().join(path).display()
                        )
                    } else {
                        argument.clone()
                    }
                } else {
                    argument.clone()
                };
                arguments.push(resolved);
            }
            let outcome = crate::cli::run(&recipe.operation, &arguments);
            let success = if recipe.expect == "success" {
                crate::cli::succeeded(&outcome)
            } else {
                !crate::cli::succeeded(&outcome) && outcome["code"] == recipe.expect
            };
            passed &= success;
            records.push(
                json!({"name":name,"passed":success,"expect":recipe.expect,"result":outcome}),
            );
        }
        report["tests"] = json!(records);
        report["phase"] = json!("complete");
        if !passed {
            return Err("source-test-failed".into());
        }
        report["status"] = json!("tested");
        Ok(())
    })();
    if let Err(code) = result {
        report["code"] = json!(code);
    }
    report
}
