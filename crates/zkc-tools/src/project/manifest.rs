//! Explicit source inputs. Imports never perform filesystem discovery.
use crate::host::io;
use serde::Deserialize;
use std::{
    collections::{BTreeMap, BTreeSet},
    path::{Path, PathBuf},
};

type Result<T> = std::result::Result<T, String>;
const MANIFEST_BYTES: usize = 1024 * 1024;
const FILES: usize = 256;
const MANIFESTS: usize = 64;
const DEPTH: usize = 32;

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Manifest {
    format: String,
    #[serde(default)]
    modules: BTreeMap<String, String>,
    #[serde(default)]
    dependencies: BTreeMap<String, String>,
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
            let mut capture = Capture::default();
            capture.load(&path)?;
            modules = capture.modules;
            assets = capture.assets;
            result.paths = capture.manifests;
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
            validate_asset_format(&asset.format)?;
            result
                .flags
                .push(format!("--asset={name}={}={path}", asset.format));
            result.paths.push(path);
        }
        Ok(result)
    }
}
/// Resolve explicitly selected local families into one nominal source map.
/// A visible manifest context determines relative paths, even when the file
/// itself is a symlink. Directory aliases share a context; file aliases may not.
#[derive(Default)]
struct Capture {
    modules: BTreeMap<String, String>,
    assets: BTreeMap<String, Asset>,
    manifests: Vec<String>,
    active: BTreeSet<PathBuf>,
    visited: BTreeSet<PathBuf>,
}
impl Capture {
    fn load(&mut self, path: &Path) -> Result<()> {
        let parent = path
            .parent()
            .ok_or("source-project-format")?
            .canonicalize()
            .map_err(|_| "source-project-io")?;
        let context = parent.join(path.file_name().ok_or("source-project-format")?);
        if self.active.contains(&context) {
            return Err("source-project-cycle".into());
        }
        if self.visited.contains(&context) {
            return Ok(());
        }
        if self.visited.len() + self.active.len() >= MANIFESTS || self.active.len() >= DEPTH {
            return Err("source-project-limit".into());
        }
        let bytes = io::read_regular(&context, MANIFEST_BYTES).map_err(|e| match e {
            io::ReadError::Limit => "source-project-limit",
            io::ReadError::Io(_) => "source-project-io",
        })?;
        let project: Manifest = toml::from_slice(&bytes).map_err(|_| "source-project-format")?;
        if project.format != "zkc.project/0"
            || (project.modules.is_empty() && project.dependencies.is_empty())
        {
            return Err("source-project-format".into());
        }
        if project.modules.len() + project.assets.len() > FILES
            || project.dependencies.len() > MANIFESTS
        {
            return Err("source-project-limit".into());
        }
        self.active.insert(context.clone());
        self.manifests
            .push(context.to_str().ok_or("source-project-format")?.into());
        for (name, path) in project.modules {
            validate_name(&name)?;
            let path = resolve(&parent, &path)?;
            if let Some(previous) = self.modules.get(&name) {
                if !same_file(previous, &path) {
                    return Err("source-project-conflict".into());
                }
            } else {
                self.modules.insert(name, path);
            }
        }
        for (name, asset) in project.assets {
            validate_name(&name)?;
            validate_asset_format(&asset.format)?;
            let asset = Asset {
                format: asset.format,
                path: resolve(&parent, &asset.path)?,
            };
            if let Some(previous) = self.assets.get(&name) {
                if previous.format != asset.format || !same_file(&previous.path, &asset.path) {
                    return Err("source-project-conflict".into());
                }
            } else {
                self.assets.insert(name, asset);
            }
        }
        if self.modules.len() + self.assets.len() > FILES {
            return Err("source-project-limit".into());
        }
        for (name, path) in project.dependencies {
            validate_name(&name)?;
            let directory = resolve(&parent, &path)?;
            self.load(&Path::new(&directory).join("zkc.toml"))?;
        }
        self.active.remove(&context);
        self.visited.insert(context);
        Ok(())
    }
}

fn same_file(left: &str, right: &str) -> bool {
    if left == right {
        return true;
    }
    match (
        Path::new(left).canonicalize(),
        Path::new(right).canonicalize(),
    ) {
        (Ok(left), Ok(right)) => left == right,
        _ => false,
    }
}

fn validate_asset_format(format: &str) -> Result<()> {
    if !matches!(
        format,
        "r1cs-json" | "r1cs-binary" | "air-json" | "ring-json" | "relation-bundle-json"
    ) {
        return Err("source-project-format".into());
    }
    Ok(())
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

    fn manifest(root: &Path, name: &str, body: &str) -> PathBuf {
        let directory = root.join(name);
        std::fs::create_dir_all(&directory).unwrap();
        let path = directory.join("zkc.toml");
        std::fs::write(&path, format!("format = \"zkc.project/0\"\n{body}")).unwrap();
        path
    }

    #[test]
    fn dependency_diamonds_share_one_capture_and_protect_every_manifest() {
        let directory = tempfile::tempdir().unwrap();
        let root = directory.path();
        let leaf = manifest(root, "leaf", "[modules]\nshared='lib.zkc'\n");
        std::fs::write(root.join("leaf/lib.zkc"), "module shared;").unwrap();
        let left = manifest(root, "left", "[dependencies]\nshared='../leaf'\n");
        let right = manifest(root, "right", "[dependencies]\nshared='../leaf'\n");
        let top = manifest(
            root,
            "top",
            "[dependencies]\nleft='../left'\nright='../right'\n",
        );
        let project = Project::load(&top).unwrap();
        assert_eq!(
            project.flags,
            [format!(
                "--module=shared={}",
                root.join("leaf/lib.zkc").display()
            )]
        );
        for path in [top, left, right, leaf] {
            assert!(project.paths().any(|found| Path::new(found) == path));
        }
        assert_eq!(project.paths().count(), 5);
    }

    #[test]
    fn dependencies_reject_cycles_conflicts_and_invalid_manifests() {
        let directory = tempfile::tempdir().unwrap();
        let root = directory.path();
        let top = manifest(root, "top", "[dependencies]\nleaf='../leaf'\n");
        manifest(root, "leaf", "[dependencies]\ntop='../top'\n");
        assert_eq!(Project::load(&top).err().unwrap(), "source-project-cycle");
        manifest(root, "leaf", "[modules]\nshared='leaf.zkc'\n");
        manifest(
            root,
            "top",
            "[modules]\nshared='own.zkc'\n[dependencies]\nleaf='../leaf'\n",
        );
        assert_eq!(
            Project::load(&top).err().unwrap(),
            "source-project-conflict"
        );
        for (body, expected) in [
            ("[dependencies]\nbad=''\n", "source-project-format"),
            ("[dependencies]\nbad=1\n", "source-project-format"),
            (
                "[dependencies]\nbad={path='../leaf'}\n",
                "source-project-format",
            ),
            ("[dependencies]\nmissing='../absent'\n", "source-project-io"),
        ] {
            manifest(root, "top", body);
            assert_eq!(Project::load(&top).err().unwrap(), expected);
        }
    }

    #[test]
    fn duplicate_bindings_require_the_same_source_and_asset_format() {
        let directory = tempfile::tempdir().unwrap();
        let root = directory.path();
        manifest(
            root,
            "leaf",
            "[modules]\nshared='lib.zkc'\n[assets.r]\nformat='ring-json'\npath='r.json'\n",
        );
        std::fs::write(root.join("leaf/lib.zkc"), "module shared;").unwrap();
        std::fs::write(root.join("leaf/r.json"), "[]").unwrap();
        let body = "[modules]\nshared='../leaf/lib.zkc'\n[dependencies]\nleaf='../leaf'\n[assets.r]\nformat='ring-json'\npath='../leaf/r.json'\n";
        let top = manifest(root, "top", body);
        assert_eq!(Project::load(&top).unwrap().flags.len(), 2);
        manifest(root, "top", &body.replace("ring-json", "air-json"));
        assert_eq!(
            Project::load(&top).err().unwrap(),
            "source-project-conflict"
        );
        manifest(root, "top", &body.replace("../leaf/r.json", "other.json"));
        assert_eq!(
            Project::load(&top).err().unwrap(),
            "source-project-conflict"
        );
    }

    #[test]
    fn dependency_depth_and_total_capture_are_bounded() {
        let directory = tempfile::tempdir().unwrap();
        let root = directory.path();
        for i in 0..DEPTH {
            manifest(
                root,
                &format!("d{i}"),
                &format!("[dependencies]\nnext='../d{}'\n", i + 1),
            );
        }
        manifest(root, &format!("d{DEPTH}"), "[modules]\nleaf='lib.zkc'\n");
        assert_eq!(
            Project::load(root.join("d0/zkc.toml")).err().unwrap(),
            "source-project-limit"
        );
        let mut large = String::from("[modules]\n");
        for i in 0..FILES {
            large.push_str(&format!("m{i}='lib.zkc'\n"));
        }
        manifest(root, "leaf", &large);
        let top = manifest(
            root,
            "top",
            "[modules]\nextra='main.zkc'\n[dependencies]\nleaf='../leaf'\n",
        );
        assert_eq!(Project::load(top).err().unwrap(), "source-project-limit");
    }

    #[test]
    #[cfg(unix)]
    fn a_symlinked_manifest_keeps_its_visible_relative_path_context() {
        let directory = tempfile::tempdir().unwrap();
        let root = directory.path();
        let original = manifest(
            root,
            "original",
            "[modules]\nclient='main.zkc'\n[dependencies]\nlocal='family'\n",
        );
        manifest(root, "visible/family", "[modules]\nlocal='lib.zkc'\n");
        std::os::unix::fs::symlink(original, root.join("visible/zkc.toml")).unwrap();
        let project = Project::load(root.join("visible/zkc.toml")).unwrap();
        assert_eq!(
            project.flags,
            [
                format!(
                    "--module=client={}",
                    root.join("visible/main.zkc").display()
                ),
                format!(
                    "--module=local={}",
                    root.join("visible/family/lib.zkc").display()
                ),
            ]
        );
    }
}
