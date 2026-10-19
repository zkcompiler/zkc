//! Explicit source inputs. Imports never perform filesystem discovery.
use crate::host::io;
use serde::{Deserialize, Serialize};
use std::{
    collections::{BTreeMap, BTreeSet},
    path::{Path, PathBuf},
};

type Result<T> = std::result::Result<T, String>;
const MANIFEST_BYTES: usize = 1024 * 1024;
const FILES: usize = 256;
const MANIFESTS: usize = 64;
const DEPTH: usize = 32;
const CATALOGS: usize = 16;
const CATALOG_ENTRIES: usize = 256;

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Manifest {
    format: String,
    #[serde(default)]
    modules: BTreeMap<String, String>,
    #[serde(default)]
    dependencies: BTreeMap<String, Dependency>,
    #[serde(default)]
    assets: BTreeMap<String, Asset>,
    workspace: Option<Workspace>,
}
#[derive(Deserialize)]
#[serde(untagged)]
enum Dependency {
    Path(String),
    Workspace(WorkspaceSelection),
}
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct WorkspaceSelection {
    workspace: String,
}
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Workspace {
    path: String,
}
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Catalog {
    format: String,
    packages: BTreeMap<String, String>,
}
#[derive(Clone, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct Asset {
    pub format: String,
    pub path: String,
}

/// Filesystem provenance for tooling, separate from the compiler's capture.
/// A dependency identifies its visible manifest context, even for file symlinks.
#[derive(Serialize)]
pub struct ProjectGraph {
    pub format: &'static str,
    pub root: PathBuf,
    pub packages: Vec<ProjectPackage>,
}
#[derive(Serialize)]
pub struct ProjectPackage {
    pub manifest: PathBuf,
    pub modules: BTreeMap<String, String>,
    pub assets: BTreeMap<String, Asset>,
    pub dependencies: BTreeMap<String, PathBuf>,
    pub catalog_dependencies: BTreeMap<String, CatalogDependency>,
}
#[derive(Serialize)]
pub struct CatalogDependency {
    pub catalog: PathBuf,
    pub package: String,
}

/// Explicit source paths, made absolute when loaded. Imports are resolved only
/// from these maps; later changes to the working directory do not retarget them.
pub struct Project {
    pub(crate) flags: Vec<String>,
    pub(crate) paths: Vec<String>,
    pub(crate) manifest: Option<PathBuf>,
    graph: Option<ProjectGraph>,
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
    /// Explicit SDK input maps have no filesystem package graph.
    pub fn graph(&self) -> Option<&ProjectGraph> {
        self.graph.as_ref()
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
            graph: None,
        };
        if let Some(path) = manifest {
            let mut capture = Capture::default();
            let root = capture.load(&path)?;
            result.graph = Some(ProjectGraph {
                format: "zkc.project-graph/0",
                root,
                packages: capture.packages.into_values().collect(),
            });
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
    packages: BTreeMap<PathBuf, ProjectPackage>,
    catalogs: BTreeMap<PathBuf, Catalog>,
}
impl Capture {
    fn load(&mut self, path: &Path) -> Result<PathBuf> {
        let parent = path
            .parent()
            .ok_or("source-project-format")?
            .canonicalize()
            .map_err(|_| "source-project-io")?;
        let context = parent.join(path.file_name().ok_or("source-project-format")?);
        validate_path(context.to_str().ok_or("source-project-format")?)?;
        if self.active.contains(&context) {
            return Err("source-project-cycle".into());
        }
        if self.visited.contains(&context) {
            return Ok(context);
        }
        if self.visited.len() + self.active.len() >= MANIFESTS || self.active.len() >= DEPTH {
            return Err("source-project-limit".into());
        }
        let bytes = io::read_regular(&context, MANIFEST_BYTES).map_err(|e| match e {
            io::ReadError::Limit => "source-project-limit",
            io::ReadError::Io(_) => "source-project-io",
        })?;
        let project: Manifest = toml::from_slice(&bytes).map_err(|_| "source-project-format")?;
        if let Some(workspace) = &project.workspace {
            validate_path(&workspace.path)?;
        }
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
        let mut package = ProjectPackage {
            manifest: context.clone(),
            modules: BTreeMap::new(),
            assets: BTreeMap::new(),
            dependencies: BTreeMap::new(),
            catalog_dependencies: BTreeMap::new(),
        };
        for (name, path) in project.modules {
            validate_name(&name)?;
            let path = resolve(&parent, &path)?;
            package.modules.insert(name.clone(), path.clone());
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
            package.assets.insert(name.clone(), asset.clone());
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
        for (name, selection) in project.dependencies {
            validate_name(&name)?;
            let path = match selection {
                Dependency::Path(path) => Path::new(&resolve(&parent, &path)?).join("zkc.toml"),
                Dependency::Workspace(selection) => {
                    validate_name(&selection.workspace)?;
                    let workspace = project.workspace.as_ref().ok_or("source-project-format")?;
                    let catalog = PathBuf::from(resolve(&parent, &workspace.path)?);
                    let (context, path) = self.select(&catalog, &selection.workspace)?;
                    package.catalog_dependencies.insert(
                        name.clone(),
                        CatalogDependency {
                            catalog: context,
                            package: selection.workspace,
                        },
                    );
                    path
                }
            };
            let dependency = self.load(&path)?;
            package.dependencies.insert(name, dependency);
        }
        self.active.remove(&context);
        self.visited.insert(context.clone());
        self.packages.insert(context.clone(), package);
        Ok(context)
    }

    fn select(&mut self, path: &Path, key: &str) -> Result<(PathBuf, PathBuf)> {
        let parent = path
            .parent()
            .ok_or("source-project-format")?
            .canonicalize()
            .map_err(|_| "source-project-io")?;
        let context = parent.join(path.file_name().ok_or("source-project-format")?);
        validate_path(context.to_str().ok_or("source-project-format")?)?;
        if !self.catalogs.contains_key(&context) {
            if self.catalogs.len() >= CATALOGS {
                return Err("source-project-limit".into());
            }
            let bytes = io::read_regular(&context, MANIFEST_BYTES).map_err(|e| match e {
                io::ReadError::Limit => "source-project-limit",
                io::ReadError::Io(_) => "source-project-io",
            })?;
            let catalog: Catalog = toml::from_slice(&bytes).map_err(|_| "source-project-format")?;
            if catalog.format != "zkc.workspace/0" {
                return Err("source-project-format".into());
            }
            if catalog.packages.len() > CATALOG_ENTRIES {
                return Err("source-project-limit".into());
            }
            for (name, location) in &catalog.packages {
                validate_name(name)?;
                validate_path(location)?;
            }
            self.manifests
                .push(context.to_str().ok_or("source-project-format")?.into());
            self.catalogs.insert(context.clone(), catalog);
        }
        let location = self.catalogs[&context]
            .packages
            .get(key)
            .ok_or("source-project-format")?;
        let mut selected = PathBuf::from(resolve(&parent, location)?);
        if selected.is_dir() {
            selected.push("zkc.toml");
        }
        Ok((context, selected))
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

    fn catalog(root: &Path, name: &str, body: &str) -> PathBuf {
        let path = root.join(name);
        std::fs::write(
            &path,
            format!("format='zkc.workspace/0'\n[packages]\n{body}"),
        )
        .unwrap();
        path
    }

    #[test]
    fn catalog_selection_matches_paths_and_protects_only_used_inputs() {
        let directory = tempfile::tempdir().unwrap();
        let root = &directory.path().canonicalize().unwrap();
        let leaf = manifest(
            root,
            "leaf",
            "[modules]\nshared='lib.zkc'\n[assets.r]\nformat='air-json'\npath='r.json'\n",
        );
        let workspace = catalog(
            root,
            "zkc.workspace.toml",
            "chosen='leaf'\nabsent='never-opened'\n",
        );
        let top = manifest(
            root,
            "top",
            "[workspace]\npath='../zkc.workspace.toml'\n[dependencies]\nlocal={workspace='chosen'}\n",
        );
        let selected = Project::load(&top).unwrap();
        let package = selected
            .graph()
            .unwrap()
            .packages
            .iter()
            .find(|p| p.manifest == top)
            .unwrap();
        assert_eq!(package.dependencies["local"], leaf);
        assert_eq!(package.catalog_dependencies["local"].catalog, workspace);
        assert_eq!(package.catalog_dependencies["local"].package, "chosen");
        assert!(selected.paths().any(|p| Path::new(p) == workspace));
        assert_eq!(selected.paths().count(), 5);
        catalog(root, "zkc.workspace.toml", "chosen='leaf/zkc.toml'\n");
        assert_eq!(Project::load(&top).unwrap().flags, selected.flags);
        manifest(root, "top", "[dependencies]\nlocal='../leaf'\n");
        assert_eq!(Project::load(&top).unwrap().flags, selected.flags);
        // Declaring an unused workspace validates its shape, but does not open it.
        manifest(
            root,
            "top",
            "[workspace]\npath='absent.toml'\n[dependencies]\nlocal='../leaf'\n",
        );
        assert_eq!(Project::load(&top).unwrap().paths().count(), 4);
    }

    #[test]
    fn catalog_edges_do_not_inherit_workspace_and_keep_cycle_and_provider_checks() {
        let directory = tempfile::tempdir().unwrap();
        let root = &directory.path().canonicalize().unwrap();
        let top = manifest(
            root,
            "top",
            "[workspace]\npath='../zkc.workspace.toml'\n[dependencies]\nlocal={workspace='leaf'}\n",
        );
        catalog(root, "zkc.workspace.toml", "leaf='leaf'\ntop='top'\n");
        manifest(root, "leaf", "[dependencies]\nback={workspace='top'}\n");
        assert_eq!(Project::load(&top).err().unwrap(), "source-project-format");
        manifest(
            root,
            "leaf",
            "[workspace]\npath='../zkc.workspace.toml'\n[dependencies]\nback={workspace='top'}\n",
        );
        assert_eq!(Project::load(&top).err().unwrap(), "source-project-cycle");
        manifest(root, "leaf", "[modules]\nshared='lib.zkc'\n");
        manifest(root, "other", "[modules]\nshared='lib.zkc'\n");
        for name in ["leaf", "other"] {
            std::fs::write(root.join(name).join("lib.zkc"), "module shared;").unwrap();
        }
        catalog(root, "zkc.workspace.toml", "leaf='leaf'\nother='other'\n");
        manifest(
            root,
            "top",
            "[workspace]\npath='../zkc.workspace.toml'\n[dependencies]\na={workspace='leaf'}\nb={workspace='other'}\n",
        );
        assert_eq!(
            Project::load(&top).err().unwrap(),
            "source-project-conflict"
        );
    }

    #[test]
    fn catalog_syntax_is_strict_even_for_unselected_locations() {
        let directory = tempfile::tempdir().unwrap();
        let root = &directory.path().canonicalize().unwrap();
        manifest(root, "leaf", "[modules]\nshared='lib.zkc'\n");
        let body =
            "[workspace]\npath='../zkc.workspace.toml'\n[dependencies]\na={workspace='leaf'}\n";
        let top = manifest(root, "top", body);
        for invalid in [
            "leaf='leaf'\nunused=''",
            "leaf='leaf'\nunused=1",
            "leaf='leaf'\nleaf='leaf'",
            "leaf='leaf'\nunused={path='leaf'}",
            "leaf='leaf'\n''='leaf'",
        ] {
            catalog(root, "zkc.workspace.toml", invalid);
            assert_eq!(Project::load(&top).err().unwrap(), "source-project-format");
        }
        catalog(root, "zkc.workspace.toml", "leaf='leaf'\n");
        for invalid in [
            body.replace("workspace='leaf'", "workspace='leaf',path='../leaf'"),
            body.replace("workspace='leaf'", "workspace=''"),
            body.replace("workspace='leaf'", "workspace='missing'"),
            body.replace(
                "path='../zkc.workspace.toml'",
                "path='../zkc.workspace.toml',extra=1",
            ),
            body.replace("path='../zkc.workspace.toml'", "path=''"),
        ] {
            manifest(root, "top", &invalid);
            assert_eq!(Project::load(&top).err().unwrap(), "source-project-format");
        }
        manifest(root, "top", body);
        std::fs::write(
            root.join("zkc.workspace.toml"),
            "format='zkc.workspace/1'\n[packages]\nleaf='leaf'",
        )
        .unwrap();
        assert_eq!(Project::load(&top).err().unwrap(), "source-project-format");
    }

    #[test]
    fn catalog_count_entries_and_bytes_have_separate_ceilings() {
        let directory = tempfile::tempdir().unwrap();
        let root = &directory.path().canonicalize().unwrap();
        let mut entries = String::from("leaf='leaf'\n");
        for i in 1..CATALOG_ENTRIES {
            entries.push_str(&format!("unused{i}='absent'\n"));
        }
        let top = manifest(
            root,
            "top",
            "[workspace]\npath='../zkc.workspace.toml'\n[dependencies]\na={workspace='leaf'}\n",
        );
        manifest(root, "leaf", "[modules]\nshared='lib.zkc'\n");
        catalog(root, "zkc.workspace.toml", &entries);
        assert!(Project::load(&top).is_ok());
        catalog(root, "zkc.workspace.toml", &(entries + "extra='absent'\n"));
        assert_eq!(Project::load(&top).err().unwrap(), "source-project-limit");
        std::fs::write(
            root.join("zkc.workspace.toml"),
            vec![b' '; MANIFEST_BYTES + 1],
        )
        .unwrap();
        assert_eq!(Project::load(&top).err().unwrap(), "source-project-limit");
        for i in 0..=CATALOGS {
            catalog(root, &format!("c{i}.toml"), &format!("next='d{}'\n", i + 1));
            manifest(
                root,
                &format!("d{i}"),
                &format!(
                    "[workspace]\npath='../c{i}.toml'\n[dependencies]\na={{workspace='next'}}\n"
                ),
            );
        }
        manifest(
            root,
            &format!("d{}", CATALOGS + 1),
            "[modules]\nshared='lib.zkc'\n",
        );
        assert_eq!(
            Project::load(root.join("d0/zkc.toml")).err().unwrap(),
            "source-project-limit"
        );
        manifest(
            root,
            &format!("d{CATALOGS}"),
            "[modules]\nshared='lib.zkc'\n",
        );
        assert!(Project::load(root.join("d0/zkc.toml")).is_ok());
    }

    #[test]
    #[cfg(unix)]
    fn catalog_file_symlinks_use_the_visible_parent_and_directory_aliases_share_it() {
        let directory = tempfile::tempdir().unwrap();
        let root = &directory.path().canonicalize().unwrap();
        std::fs::create_dir(root.join("visible")).unwrap();
        let source = catalog(root, "original.toml", "chosen='family'\n");
        std::os::unix::fs::symlink(source, root.join("visible/catalog.toml")).unwrap();
        let leaf = manifest(root, "visible/family", "[modules]\nshared='lib.zkc'\n");
        std::os::unix::fs::symlink(root.join("visible"), root.join("alias")).unwrap();
        let top = manifest(
            root,
            "top",
            "[workspace]\npath='../alias/catalog.toml'\n[dependencies]\na={workspace='chosen'}\n",
        );
        let project = Project::load(top).unwrap();
        assert!(
            project
                .graph()
                .unwrap()
                .packages
                .iter()
                .any(|p| p.manifest == leaf)
        );
        assert!(
            project
                .paths()
                .any(|p| Path::new(p) == root.join("visible/catalog.toml"))
        );
    }

    #[test]
    fn dependency_diamonds_share_one_capture_and_protect_every_manifest() {
        let directory = tempfile::tempdir().unwrap();
        let root = &directory.path().canonicalize().unwrap();
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
        let graph = project.graph().unwrap();
        assert_eq!(graph.format, "zkc.project-graph/0");
        assert_eq!(graph.root, root.join("top/zkc.toml"));
        assert_eq!(graph.packages.len(), 4);
        let top = graph
            .packages
            .iter()
            .find(|p| p.manifest == graph.root)
            .unwrap();
        assert_eq!(top.dependencies["left"], root.join("left/zkc.toml"));
        assert_eq!(top.dependencies["right"], root.join("right/zkc.toml"));
        assert!(top.modules.is_empty());
        let leaf = graph
            .packages
            .iter()
            .find(|p| !p.modules.is_empty())
            .unwrap();
        assert_eq!(
            leaf.modules["shared"],
            root.join("leaf/lib.zkc").to_str().unwrap()
        );
    }

    #[test]
    fn dependencies_reject_cycles_conflicts_and_invalid_manifests() {
        let directory = tempfile::tempdir().unwrap();
        let root = &directory.path().canonicalize().unwrap();
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
        let root = &directory.path().canonicalize().unwrap();
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
        let root = &directory.path().canonicalize().unwrap();
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
        manifest(
            root,
            &format!("d{}", DEPTH - 1),
            "[modules]\nleaf='lib.zkc'\n",
        );
        assert_eq!(
            Project::load(root.join("d0/zkc.toml")).unwrap().flags.len(),
            1
        );
        let mut large = String::from("[modules]\n");
        for i in 0..FILES {
            large.push_str(&format!("m{i}='lib.zkc'\n"));
        }
        manifest(root, "leaf", &large);
        assert_eq!(
            Project::load(root.join("leaf/zkc.toml"))
                .unwrap()
                .flags
                .len(),
            FILES
        );
        let top = manifest(
            root,
            "top",
            "[modules]\nextra='main.zkc'\n[dependencies]\nleaf='../leaf'\n",
        );
        assert_eq!(Project::load(top).err().unwrap(), "source-project-limit");
    }

    #[test]
    fn manifest_count_includes_the_root_and_shared_contexts_once() {
        let directory = tempfile::tempdir().unwrap();
        let root = &directory.path().canonicalize().unwrap();
        let mut dependencies = String::from("[dependencies]\n");
        for i in 0..MANIFESTS {
            manifest(
                root,
                &format!("m{i}"),
                &format!("[modules]\nm{i}='lib.zkc'\n"),
            );
            if i + 1 < MANIFESTS {
                dependencies.push_str(&format!("m{i}='../m{i}'\n"));
            }
        }
        let top = manifest(root, "top", &dependencies);
        assert_eq!(Project::load(&top).unwrap().flags.len(), MANIFESTS - 1);
        dependencies.push_str(&format!("last='../m{}'\n", MANIFESTS - 1));
        manifest(root, "top", &dependencies);
        assert_eq!(Project::load(&top).err().unwrap(), "source-project-limit");
    }

    #[test]
    #[cfg(unix)]
    fn a_symlinked_manifest_keeps_its_visible_relative_path_context() {
        let directory = tempfile::tempdir().unwrap();
        let root = &directory.path().canonicalize().unwrap();
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
