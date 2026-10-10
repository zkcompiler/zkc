//! CLI adaptation and publication. Project and compiler APIs take no CLI state.
use super::{Asset, CheckOptions, Compiler, NotationOptions, Project, Selection};
use crate::{
    cli::Arguments,
    entry::{BoundInterface, CompileOptions},
    host::{inputs::hex, publication::Outputs},
};
use serde_json::{Value as Json, json};
use std::collections::BTreeMap;
type Result<T> = std::result::Result<T, String>;

pub(crate) struct Source {
    pub project: Project,
    pub compiler: Compiler,
    pub options: CompileOptions,
    pub compiler_argument: String,
}
impl Source {
    pub fn load(args: &Arguments<'_>) -> Result<Self> {
        let mut manifest = None;
        let mut modules = BTreeMap::new();
        let mut assets = BTreeMap::new();
        let mut compiler = "zkc-compile";
        let mut options = CompileOptions {
            simplify: true,
            release_storage: false,
        };
        for &(key, value) in &args.options {
            let value = value.unwrap_or("");
            let duplicate = match key {
                "--project" => {
                    manifest = Some(value);
                    false
                }
                "--compiler" => {
                    compiler = value;
                    false
                }
                "--no-simplify" => {
                    options.simplify = false;
                    false
                }
                "--release-storage" => {
                    options.release_storage = true;
                    false
                }
                "--module" => {
                    let (name, path) = value.split_once('=').ok_or("source-project-format")?;
                    modules.insert(name.into(), path.into()).is_some()
                }
                "--asset" => {
                    let (name, rest) = value.split_once('=').ok_or("source-project-format")?;
                    let (format, path) = rest.split_once('=').ok_or("source-project-format")?;
                    assets
                        .insert(
                            name.into(),
                            Asset {
                                format: format.into(),
                                path: path.into(),
                            },
                        )
                        .is_some()
                }
                _ => false,
            };
            if duplicate {
                return Err("source-project-duplicate".into());
            }
        }
        let explicit = !modules.is_empty() || !assets.is_empty();
        if manifest.is_some() && explicit {
            return Err("cli-usage".into());
        }
        let project = match manifest {
            Some(path) => Project::load(path)?,
            None if explicit => Project::explicit(modules, assets)?,
            None => Project::discover()?,
        };
        Ok(Self {
            project,
            compiler: Compiler::new(compiler).map_err(|e| e.code)?,
            options,
            compiler_argument: compiler.into(),
        })
    }
    pub fn protect(&self, outputs: &mut Outputs) -> Result<()> {
        outputs.protect(self.project.paths())?;
        outputs.protect([self.compiler.path().to_str().ok_or("source-compiler-io")?])?;
        let path = std::path::Path::new(&self.compiler_argument);
        if path.is_absolute() || path.components().count() > 1 {
            outputs.protect([self.compiler_argument.as_str()])?;
        }
        Ok(())
    }
    pub fn describe(&self, report: &mut Json) {
        report["mode"] = json!("project");
        report["compiler"] = json!(self.compiler.path());
        report["options"] = json!({"simplify":self.options.simplify,"release_storage":self.options.release_storage});
        if let Some(path) = self.project.manifest() {
            report["project"] = json!(path);
        }
    }
}
pub(crate) fn compiler_error(report: &mut Json, error: super::Error) -> String {
    if let Some(diagnostics) = error.diagnostics {
        report["diagnostics"] = json!(diagnostics);
        report["diagnostics_truncated"] = json!(error.diagnostics_truncated);
    }
    error.code
}
pub(crate) fn run(command: &str, args: &Arguments<'_>) -> Json {
    let checking = command == "check";
    let mut report = json!({"format":if checking {"zkc.source-check/0"} else {"zkc.entry-build/0"},"status":"refused","phase":"arguments"});
    let result = (|| -> Result<()> {
        let source = Source::load(args)?;
        let entry = args.positional.first().copied();
        let output = args.value("--output");
        if !checking && output.is_none() && source.project.manifest().is_none() {
            return Err("source-output-required".into());
        }
        let mut destinations = Outputs::new(&output.into_iter().collect::<Vec<_>>(), &[])?;
        source.protect(&mut destinations)?;
        source.describe(&mut report);
        report["phase"] = json!("compilation");
        if checking {
            let checked = source
                .compiler
                .check(
                    &source.project,
                    entry,
                    CheckOptions {
                        declarations: args.has("--declarations"),
                        notations: args.has("--notations").then(|| NotationOptions {
                            include_private: args.has("--notation-private"),
                            include_installation: args.has("--notation-installation"),
                        }),
                    },
                )
                .map_err(|e| compiler_error(&mut report, e))?;
            let fields = serde_json::to_value(checked).expect("serializable check result");
            report
                .as_object_mut()
                .unwrap()
                .extend(fields.as_object().unwrap().clone());
            report["scope"] = json!(if entry.is_some() {
                "entry"
            } else {
                "definitions"
            });
            report["status"] = json!("checked");
        } else {
            let package = source
                .compiler
                .compile(
                    &source.project,
                    Selection {
                        name: entry,
                        kind: None,
                    },
                    source.options,
                )
                .map_err(|e| compiler_error(&mut report, e))?;
            let view = BoundInterface::read(&package).map_err(|e| e.to_string())?;
            report["entry"] = json!(view.entry());
            report["toolchain"] = json!(view.toolchain());
            report["package_sha256"] = json!(hex(package.identity()));
            let path = match output {
                Some(path) => path.to_owned(),
                None => {
                    let path = source
                        .project
                        .layout()
                        .ok_or("source-output-required")?
                        .artifact(view.entry(), super::Artifact::Package)?;
                    std::fs::create_dir_all(path.parent().unwrap())
                        .map_err(|_| "source-output-directory")?;
                    path.to_str().ok_or("source-output-name")?.to_owned()
                }
            };
            destinations = Outputs::new(&[&path], &[])?;
            source.protect(&mut destinations)?;
            report["output"] = json!(path);
            report["phase"] = json!("publication");
            destinations.publish(&[("package", package.bytes())], &mut report)?;
            report["status"] = json!("compiled");
        }
        report["phase"] = json!("complete");
        Ok(())
    })();
    if let Err(code) = result {
        report["code"] = json!(if code == "artifact-output-path" {
            "entry-output-path"
        } else {
            &code
        });
    }
    report
}
