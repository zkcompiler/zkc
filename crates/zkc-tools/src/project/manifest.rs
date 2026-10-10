//! Explicit source inputs. Imports never perform filesystem discovery.
use crate::host::io;
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
struct Manifest {
    format: String,
    modules: BTreeMap<String, String>,
    #[serde(default)]
    assets: BTreeMap<String, Asset>,
}
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Asset {
    pub format: String,
    pub path: String,
}

/// Explicit source paths, made absolute when loaded. Imports are resolved only
/// from these maps; later changes to the working directory do not retarget them.
pub struct Project {
    pub(crate) flags: Vec<String>,
    pub(crate) paths: Vec<String>,
    pub(crate) manifest: Option<PathBuf>,
}
impl Project {
    pub fn discover() -> Result<Self> {
        Self::load(discover()?)
    }
    pub fn load(path: impl AsRef<Path>) -> Result<Self> {
        Self::from_parts(
            Some(path.as_ref().to_owned()),
            BTreeMap::new(),
            BTreeMap::new(),
        )
    }
    pub fn explicit(
        modules: BTreeMap<String, String>,
        assets: BTreeMap<String, Asset>,
    ) -> Result<Self> {
        Self::from_parts(None, modules, assets)
    }
    pub fn manifest(&self) -> Option<&Path> {
        self.manifest.as_deref()
    }
    pub fn paths(&self) -> impl Iterator<Item = &str> {
        self.paths.iter().map(String::as_str)
    }
    fn from_parts(
        manifest: Option<PathBuf>,
        mut modules: BTreeMap<String, String>,
        mut assets: BTreeMap<String, Asset>,
    ) -> Result<Self> {
        let base = std::env::current_dir().map_err(|_| "source-project-io")?;
        let manifest = manifest.map(|path| base.join(path));
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
            let project: Manifest =
                toml::from_slice(&bytes).map_err(|_| "source-project-format")?;
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
        }
        if modules.is_empty() {
            return Err("source-project-format".into());
        }
        if modules.len() + assets.len() > FILES {
            return Err("source-project-limit".into());
        }
        for (name, path) in modules {
            validate_name(&name)?;
            let path = resolve(&base, &path)?;
            result.flags.push(format!("--module={name}={path}"));
            result.paths.push(path);
        }
        for (name, asset) in assets {
            validate_name(&name)?;
            let path = resolve(&base, &asset.path)?;
            if !matches!(
                asset.format.as_str(),
                "r1cs-json" | "r1cs-binary" | "air-json" | "ring-json" | "relation-bundle-json"
            ) {
                return Err("source-project-format".into());
            }
            result
                .flags
                .push(format!("--asset={name}={}={path}", asset.format));
            result.paths.push(path);
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn explicit_paths_keep_their_loading_directory() {
        let base = std::env::current_dir().unwrap();
        let project = Project::explicit(
            BTreeMap::from([("example".into(), "main.zkc".into())]),
            BTreeMap::from([(
                "relation".into(),
                Asset {
                    format: "air-json".into(),
                    path: "air.json".into(),
                },
            )]),
        )
        .unwrap();
        assert_eq!(
            project.paths().map(PathBuf::from).collect::<Vec<_>>(),
            [base.join("main.zkc"), base.join("air.json")]
        );
    }
}
