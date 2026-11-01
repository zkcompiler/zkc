//! CLI adaptation and publication. Project and compiler APIs take no CLI state.
use super::{Asset, CheckOptions, Compiler, NotationOptions, Project, Selection};
use crate::{
    cli::Arguments,
    files::{Outputs, hex},
};
use serde_json::{Value as Json, json};
use std::collections::BTreeMap;
type Result<T> = std::result::Result<T, String>;

pub(crate) struct Source {
    pub project: Project,
    pub compiler: Compiler,
    pub settings: super::ResolvedSettings,
    pub compiler_argument: String,
    pub explicit_selection: Vec<String>,
    pub observations: Option<super::ObservationRequest>,
    pub cache: Option<super::CompilationCache>,
}
impl Source {
    pub fn load(args: &Arguments<'_>) -> Result<Self> {
        let mut manifest = None;
        let mut modules = BTreeMap::new();
        let mut assets = BTreeMap::new();
        let mut compiler = "zkc-compile";
        let mut overrides = super::BuildSettings::default();
        for &(key, value) in &args.options {
            match key {
                "--oracle-realization" => {
                    overrides.oracle_realization = Some(
                        zkc::entry::OracleSelection::parse(value.unwrap_or(""))
                            .map_err(|e| e.to_string())?,
                    )
                }
                "--no-simplify" => overrides.simplify = Some(false),
                "--release-storage" => overrides.release_storage = Some(true),
                "--no-finite-bulk" => overrides.finite_bulk = Some(false),
                "--fuse-vector-reductions" => overrides.fuse_vector_reductions = Some(true),
                "--fuse-collect-fold" => overrides.fuse_collect_fold = Some(true),
                "--no-calculation-batching" => overrides.calculation_batching = Some(false),
                _ => (),
            }
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
        let settings = project.settings(args.value("--profile"), &overrides)?;
        let dumps = args
            .value("--dump")
            .map(|s| s.split(',').map(str::to_owned).collect::<Vec<_>>())
            .unwrap_or_default();
        if dumps
            .iter()
            .any(|s| !super::observation::PHASES.contains(&s.as_str()))
        {
            return Err("source-dump-phase".into());
        }
        if !dumps.is_empty() && !args.has("--report") {
            return Err("source-report-required".into());
        }
        Ok(Self {
            cache: args
                .value("--cache")
                .map(|p| super::CompilationCache::new(p, 256 * 1024 * 1024))
                .transpose()
                .map_err(|e| e.code)?,
            observations: args
                .has("--report")
                .then_some(super::ObservationRequest { dumps }),
            settings,
            explicit_selection: args
                .options
                .iter()
                .filter(|(k, _)| matches!(*k, "--module" | "--asset"))
                .map(|(k, v)| format!("{k}={}", v.unwrap()))
                .collect(),
            project,
            compiler: Compiler::new(compiler).map_err(|e| e.code)?,
            compiler_argument: compiler.into(),
        })
    }
    pub fn compile(
        &self,
        selection: Selection<'_>,
        report: &mut Json,
    ) -> Result<crate::entry::Package> {
        let started = std::time::Instant::now();
        let result = self
            .compiler
            .build(super::CompilationRequest {
                project: &self.project,
                selection,
                options: self.settings.options(),
                observations: self.observations.as_ref(),
                cache: self.cache.as_ref(),
            })
            .map_err(|e| compiler_error(report, e))?;
        if let Some(cache) = result.cache {
            report["cache"] = cache;
        }
        report["compilation_microseconds"] = json!(started.elapsed().as_micros());
        if let Some(mut observation) = result.observation {
            observation["package_sha256"] = json!(hex(result.package.identity()));
            observation["published_options"] = json!(result.package.options());
            if self.observations.is_some() {
                report["compilation"] = observation;
            }
        }
        if let Some(diagnostics) = result.diagnostics {
            report["diagnostics"] = json!(diagnostics);
            report["diagnostics_truncated"] = json!(result.diagnostics_truncated);
        }
        Ok(result.package)
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
        report["settings"] = json!(self.settings);
        report["mode"] = json!("project");
        report["compiler"] = json!(self.compiler.path());
        report["options"] = json!(self.settings.options());
        if let Some(path) = self.project.manifest() {
            report["project"] = json!(path);
        }
    }
}
pub(crate) fn compiler_error(report: &mut Json, error: super::Error) -> String {
    if let Some(structured) = error.structured {
        report["compiler_diagnostics"] = structured;
    }
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
        let target = args.value("--target").unwrap_or("cpu");
        if !matches!(target, "cpu" | "evm") {
            return Err("cli-target".into());
        }
        if target == "cpu"
            && ["--solc", "--solc-sha256", "--reuse", "--reuse-sha256"]
                .iter()
                .any(|flag| args.has(flag))
        {
            return Err("cli-usage".into());
        }
        let source = Source::load(args)?;
        source.describe(&mut report);
        if !checking && target == "evm" {
            return super::evm::compile(args, &source, &mut report);
        }
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
                .check(&source.project, entry, CheckOptions::default())
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
            let package = source.compile(
                Selection {
                    name: entry,
                    kind: None,
                },
                &mut report,
            )?;
            let view = super::CheckedInterface::read(&package)?;
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
            crate::files::publication(
                destinations.publish(&[("package", package.bytes())]),
                &mut report,
                true,
            )?;
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

/// Read-only views use existing semantic inventories, never a second parser.
pub(crate) fn inspect(args: &Arguments<'_>) -> Json {
    let mut report =
        json!({"format":"zkc.tool-inspection/0","status":"refused","phase":"inspection"});
    let result = (|| -> Result<()> {
        let view = args.value("--view").unwrap();
        if args.has("--package") || args.has("--sha256") {
            return Err("cli-usage".into());
        }
        report["view"] = json!(view);
        if view == "toolchain" {
            if !args.positional.is_empty()
                || args.has("--project")
                || args.has("--module")
                || args.has("--asset")
                || args.has("--profile")
            {
                return Err("cli-usage".into());
            }
            report["toolchain"] = Compiler::new(args.value("--compiler").unwrap_or("zkc-compile"))
                .map_err(|e| e.code)?
                .capabilities()
                .map_err(|e| compiler_error(&mut report, e))?;
        } else {
            let source = Source::load(args)?;
            source.describe(&mut report);
            match view {
                "project" => {
                    if !args.positional.is_empty() {
                        return Err("cli-usage".into());
                    }
                    report["project_graph"] =
                        json!(source.project.graph().ok_or("source-project-required")?);
                }
                "api" | "placement" | "notations" => {
                    let checked = source
                        .compiler
                        .check(
                            &source.project,
                            args.positional.first().copied(),
                            CheckOptions {
                                api: view == "api",
                                declarations: view != "notations",
                                notations: (view == "notations").then(|| NotationOptions {
                                    include_private: args.has("--notation-private"),
                                    include_installation: args.has("--notation-installation"),
                                }),
                            },
                        )
                        .map_err(|e| compiler_error(&mut report, e))?;
                    report["checked"] = json!(checked);
                    if view == "api"
                        && let Some(graph) = source.project.graph()
                    {
                        report["project_graph"] = json!(graph);
                    }
                    if view == "placement" {
                        report["placement_scope"] = json!(
                            "completed callable contracts; local expression placement is retained in Protocol IR dumps"
                        );
                    }
                }
                _ => return Err("cli-view".into()),
            }
        }
        report["status"] = json!("inspected");
        report["phase"] = json!("complete");
        Ok(())
    })();
    if let Err(code) = result {
        report["code"] = json!(code);
    }
    report
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::entry::CompileOptions;

    #[test]
    fn source_policy_and_request_metadata_keep_compilation_choices_independent() {
        // Loading options resolves the executable but does not invoke it.
        let executable = std::env::current_exe().unwrap();
        for finite_bulk in [false, true] {
            for vector_reductions in [false, true] {
                for collect_fold in [false, true] {
                    for calculation_batching in [false, true] {
                        let mut options = vec![
                            ("--compiler", executable.to_str()),
                            ("--module", Some("sample=sample.zkc")),
                        ];
                        if !finite_bulk {
                            options.push(("--no-finite-bulk", None));
                        }
                        if vector_reductions {
                            options.push(("--fuse-vector-reductions", None));
                        }
                        if collect_fold {
                            options.push(("--fuse-collect-fold", None));
                        }
                        if !calculation_batching {
                            options.push(("--no-calculation-batching", None));
                        }
                        let source = Source::load(&Arguments {
                            positional: vec![],
                            options,
                        })
                        .unwrap();
                        assert_eq!(
                            source.settings.options(),
                            CompileOptions {
                                simplify: true,
                                release_storage: false,
                                finite_bulk,
                                fuse_vector_reductions: vector_reductions,
                                fuse_collect_fold: collect_fold,
                                calculation_batching,
                                oracle_realization: Default::default(),
                            }
                        );
                        let mut report = json!({});
                        source.describe(&mut report);
                        assert_eq!(
                            report["options"],
                            json!({
                                "simplify": true,
                                "release_storage": false,
                                "finite_bulk": finite_bulk,
                                "fuse_vector_reductions": vector_reductions,
                                "fuse_collect_fold": collect_fold,
                                "calculation_batching": calculation_batching,
                                "oracle_realization": zkc::entry::OracleSelection::default(),
                            })
                        );
                    }
                }
            }
        }
    }
    #[test]
    fn source_selection_is_typed_and_passed_without_inference() {
        let executable = std::env::current_exe().unwrap();
        let empty = zkc::entry::OracleSelection {
            roots: zkc::entry::OracleRoots::Exact(vec![]),
            ..Default::default()
        };
        for selection in [zkc::entry::OracleSelection::default(), empty] {
            let text = selection.canonical_json().unwrap();
            let source = Source::load(&Arguments {
                positional: vec![],
                options: vec![
                    ("--compiler", executable.to_str()),
                    ("--module", Some("sample=sample.zkc")),
                    ("--oracle-realization", Some(&text)),
                ],
            })
            .unwrap();
            assert_eq!(source.settings.options().oracle_realization, selection);
            assert_eq!(source.settings.origins()["oracle-realization"], "request");
            let mut report = json!({});
            source.describe(&mut report);
            assert_eq!(report["options"]["oracle_realization"], json!(selection));
        }
        for invalid in ["{}", "[]", "null"] {
            let result = Source::load(&Arguments {
                positional: vec![],
                options: vec![("--oracle-realization", Some(invalid))],
            });
            assert_eq!(result.err().unwrap(), "oracle-realization-selection");
        }
    }
}
