//! Resolve the complete invocation before opening inputs or publishing outputs.
use super::{inputs::Operation, *};
use crate::project::{Artifact, Layout, input_path};
use rand::{RngCore, rngs::OsRng};
use std::{collections::BTreeMap, path::PathBuf};

pub(super) struct Invocation {
    pub inputs: BTreeMap<String, PathBuf>,
    pub session: Option<String>,
    pub proof: Option<PathBuf>,
    pub output: Option<PathBuf>,
    pub results: Option<PathBuf>,
    default_outputs: Vec<PathBuf>,
}
impl Invocation {
    pub fn resolve(
        interface: &Interface,
        layout: Option<&Layout>,
        args: &Arguments<'_>,
        operation: Operation,
        checking: bool,
        report: &mut Json,
    ) -> Result<Self> {
        let mut inputs = BTreeMap::new();
        if operation == Operation::Run {
            for (_, value) in args.options.iter().filter(|(key, _)| *key == "--input") {
                let (role, path) = inputs::assignment(value.unwrap())?;
                if !interface.roles().iter().any(|r| r.name == role)
                    || inputs
                        .insert(role.to_owned(), PathBuf::from(path))
                        .is_some()
                {
                    return Err("entry-input-roles".into());
                }
            }
        } else {
            for name in if operation == Operation::Prove {
                &["public", "witness"][..]
            } else {
                &["public"][..]
            } {
                if let Some(path) = args.value(&format!("--{name}")) {
                    inputs.insert((*name).into(), path.into());
                }
            }
        }
        if let Some(layout) = layout {
            let mut paths = std::collections::BTreeSet::new();
            for group in interface.input_groups() {
                if !group.is_empty()
                    && !(operation == Operation::Verify && group.name() == "witness")
                    && !inputs.contains_key(group.name())
                {
                    let path = input_path(&layout.inputs(interface.entry())?, group.name())?;
                    if !paths.insert(path.to_string_lossy().to_ascii_lowercase()) {
                        return Err("source-output-collision".into());
                    }
                    inputs.insert(group.name().into(), path);
                }
            }
        }
        let mut invocation = Self {
            inputs,
            session: None,
            proof: None,
            output: None,
            results: None,
            default_outputs: Vec::new(),
        };
        if operation == Operation::Run {
            invocation.session = Some(match args.value("--session") {
                Some(session) => session.to_owned(),
                None => {
                    let mut bytes = [0; 16];
                    OsRng
                        .try_fill_bytes(&mut bytes)
                        .map_err(|_| "entry-session-random")?;
                    hex(&bytes)
                }
            });
        }
        if !checking {
            let mut output =
                |flag: &str, kind: Artifact, required: bool| -> Result<Option<PathBuf>> {
                    if let Some(path) = args.value(flag) {
                        return Ok(Some(path.into()));
                    }
                    if let Some(layout) = layout {
                        let path = layout.artifact(interface.entry(), kind)?;
                        invocation.default_outputs.push(path.clone());
                        return Ok(Some(path));
                    }
                    if required {
                        return Err("cli-usage".into());
                    }
                    Ok(None)
                };
            if operation == Operation::Prove {
                invocation.output = output("--output", Artifact::Proof, true)?;
            }
            if operation == Operation::Run {
                if !args.has("--no-results") {
                    invocation.results = output("--results", Artifact::Results, false)?;
                }
            } else {
                invocation.results = args.value("--results").map(PathBuf::from);
            }
            if operation == Operation::Verify {
                invocation.proof = Some(match args.value("--proof") {
                    Some(path) => path.into(),
                    None => layout
                        .ok_or("cli-usage")?
                        .artifact(interface.entry(), Artifact::Proof)?,
                });
            }
        }
        report["inputs"] = json!(invocation.inputs);
        for (name, path) in [
            ("output", &invocation.output),
            ("proof", &invocation.proof),
            ("results", &invocation.results),
        ] {
            if let Some(path) = path {
                report[name] = json!(path);
            }
        }
        if let Some(session) = &invocation.session {
            report["session"] = json!(session);
        }
        Ok(invocation)
    }

    pub fn check_results<'a>(
        &self,
        mut types: impl Iterator<Item = &'a zkc_runtime::interactive::PhysicalType>,
    ) -> Result<()> {
        if self.results.is_some() && !types.all(zkc_backends::has_native_wire) {
            return Err("entry-output-codec".into());
        }
        Ok(())
    }

    pub fn destinations(&self, target: &Target, args: &Arguments<'_>) -> Result<Outputs> {
        for path in &self.default_outputs {
            std::fs::create_dir_all(path.parent().ok_or("entry-output-path")?)
                .map_err(|_| "entry-output-directory")?;
        }
        let paths = self
            .output
            .iter()
            .chain(&self.results)
            .map(|p| p.to_str().ok_or("entry-output-path"))
            .collect::<std::result::Result<Vec<_>, _>>()?;
        let mut outputs = Outputs::new(&paths, &[])?;
        target.protect(&mut outputs)?;
        outputs.protect(
            self.inputs
                .values()
                .chain(self.proof.iter())
                .map(|p| p.to_str().ok_or("entry-input-document"))
                .collect::<std::result::Result<Vec<_>, _>>()?,
        )?;
        protect_options(args, &mut outputs)?;
        Ok(outputs)
    }
}

pub(super) fn protect_options(args: &Arguments<'_>, outputs: &mut Outputs) -> Result<()> {
    for &(key, value) in &args.options {
        match key {
            "--setups" | "--capacity" | "--limits" => outputs.protect([value.unwrap()])?,
            "--key" => outputs.protect([inputs::assignment(value.unwrap())?.1])?,
            _ => (),
        }
    }
    Ok(())
}
