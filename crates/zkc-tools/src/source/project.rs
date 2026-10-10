//! Explicit source inputs. Imports never perform filesystem discovery.
use crate::{cli::Arguments, host::io};
use serde::Deserialize;
use std::{
    collections::BTreeMap,
    path::{Path, PathBuf},
};

type Result<T> = std::result::Result<T, String>;
const MANIFEST_BYTES: usize = 1024 * 1024;
const FILES: usize = 256;

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Project {
    format: String,
    modules: BTreeMap<String, String>,
    #[serde(default)]
    assets: BTreeMap<String, Asset>,
}
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Asset {
    format: String,
    path: String,
}

pub(super) struct Inputs {
    pub flags: Vec<String>,
    /// Includes the manifest: publication must not overwrite any input.
    pub paths: Vec<String>,
    pub manifest: Option<PathBuf>,
}
impl Inputs {
    pub fn load(args: &Arguments<'_>) -> Result<Self> {
        let manifest = args
            .options
            .iter()
            .find(|(k, _)| *k == "--project")
            .and_then(|(_, v)| *v);
        let explicit = args
            .options
            .iter()
            .any(|(k, _)| matches!(*k, "--module" | "--asset"));
        if manifest.is_some() && explicit {
            return Err("cli-usage".into());
        }
        let manifest = match manifest {
            Some(path) => Some(PathBuf::from(path)),
            None if explicit => None,
            None => Some(discover()?),
        };
        let mut modules = BTreeMap::new();
        let mut assets = BTreeMap::new();
        let mut result = Self {
            flags: vec![],
            paths: vec![],
            manifest: manifest.clone(),
        };
        if let Some(path) = manifest {
            let bytes = io::read_regular(&path, MANIFEST_BYTES).map_err(|e| match e {
                io::ReadError::Limit => "source-project-limit",
                io::ReadError::Io(_) => "source-project-io",
            })?;
            let project: Project = toml::from_slice(&bytes).map_err(|_| "source-project-format")?;
            if project.format != "zkc.project/0" || project.modules.is_empty() {
                return Err("source-project-format".into());
            }
            let parent = path.parent().ok_or("source-project-format")?;
            for (name, path) in project.modules {
                modules.insert(name, resolve(parent, &path)?);
            }
            for (name, asset) in project.assets {
                assets.insert(
                    name,
                    Asset {
                        format: asset.format,
                        path: resolve(parent, &asset.path)?,
                    },
                );
            }
            result
                .paths
                .push(path.to_str().ok_or("source-project-format")?.into());
        } else {
            for &(key, value) in &args.options {
                let value = value.unwrap_or("");
                let duplicate = match key {
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
        }
        if modules.is_empty() {
            return Err("cli-usage".into());
        }
        if modules.len() + assets.len() > FILES {
            return Err("source-project-limit".into());
        }
        for (name, path) in modules {
            validate_name(&name)?;
            validate_path(&path)?;
            result.flags.push(format!("--module={name}={path}"));
            result.paths.push(path);
        }
        for (name, asset) in assets {
            validate_name(&name)?;
            validate_path(&asset.path)?;
            if !matches!(
                asset.format.as_str(),
                "r1cs-json" | "r1cs-binary" | "air-json" | "ring-json" | "relation-bundle-json"
            ) {
                return Err("source-project-format".into());
            }
            result
                .flags
                .push(format!("--asset={name}={}={}", asset.format, asset.path));
            result.paths.push(asset.path);
        }
        Ok(result)
    }
}
fn validate_name(name: &str) -> Result<()> {
    if name.is_empty() || name.len() > 2048 || name.contains(['=', '\0']) {
        return Err("source-project-format".into());
    }
    Ok(())
}
fn validate_path(path: &str) -> Result<()> {
    if path.is_empty() || path.len() > 4096 || path.contains('\0') {
        return Err("source-project-format".into());
    }
    Ok(())
}
fn resolve(parent: &Path, path: &str) -> Result<String> {
    validate_path(path)?;
    let path = parent.join(path);
    let path = path.to_str().ok_or("source-project-format")?;
    validate_path(path)?;
    Ok(path.into())
}

/// Stop at the nearest directory entry, even if opening it will fail. In
/// particular, a dangling symlink must not silently select a parent's project.
fn discover() -> Result<PathBuf> {
    let cwd = std::env::current_dir().map_err(|_| "source-project-io")?;
    for parent in cwd.ancestors() {
        let candidate = parent.join("zkc.toml");
        match candidate.symlink_metadata() {
            Ok(_) => return Ok(candidate),
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
            Err(_) => return Err("source-project-io".into()),
        }
    }
    Err("source-project-missing".into())
}
