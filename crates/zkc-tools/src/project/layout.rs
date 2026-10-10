//! Standard project paths. Publication remains owned by the Host.
use super::Project;

type Result<T> = std::result::Result<T, String>;

/// Standard paths for one source project. All paths remain rooted at the
/// manifest, independent of the caller's later working directory.
/// Path selection checks portable names and existing case-folded collisions.
#[derive(Clone, Debug)]
pub struct Layout {
    root: std::path::PathBuf,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Artifact {
    Package,
    Proof,
    Results,
}
impl Project {
    pub fn layout(&self) -> Option<Layout> {
        self.manifest()
            .and_then(|p| p.parent())
            .map(|root| Layout { root: root.into() })
    }
}
impl Layout {
    pub fn inputs(&self, entry: &str) -> Result<std::path::PathBuf> {
        self.path("inputs", entry, "")
    }
    pub fn artifact(&self, entry: &str, kind: Artifact) -> Result<std::path::PathBuf> {
        self.path(
            "build/zkc",
            entry,
            match kind {
                Artifact::Package => ".zkpkg",
                Artifact::Proof => ".zkproof",
                Artifact::Results => ".results.json",
            },
        )
    }
    fn path(&self, directory: &str, entry: &str, suffix: &str) -> Result<std::path::PathBuf> {
        if !super::selection::canonical_name(entry) {
            return Err("source-entry-selection".into());
        }
        path(&self.root.join(directory), entry, suffix)
    }
}

/// Select a portable input filename in either a project or an explicit template directory.
pub fn input_path(directory: &std::path::Path, group: &str) -> Result<std::path::PathBuf> {
    if !super::selection::identifier(group) {
        return Err("source-output-name".into());
    }
    path(directory, group, ".json")
}
fn path(parent: &std::path::Path, name: &str, suffix: &str) -> Result<std::path::PathBuf> {
    let name = portable_name(name, suffix)?;
    check_collision(parent, &name)?;
    let path = parent.join(name);
    if path.to_str().is_none_or(|p| p.len() > 4096) {
        return Err("source-output-name".into());
    }
    Ok(path)
}

fn portable_name(entry: &str, suffix: &str) -> Result<String> {
    let name = format!("{}{suffix}", entry.replace("::", "."));
    // Keep the convention usable on common filesystems. Callers can select a
    // shorter explicit output for long source names or reserved device names.
    let stem = name.split('.').next().unwrap().to_ascii_uppercase();
    if name.len() > 255
        || matches!(stem.as_str(), "CON" | "PRN" | "AUX" | "NUL")
        || ((stem.starts_with("COM") || stem.starts_with("LPT"))
            && stem.len() == 4
            && matches!(stem.as_bytes()[3], b'1'..=b'9'))
    {
        return Err("source-output-name".into());
    }
    Ok(name)
}

pub(crate) fn check_collision(parent: &std::path::Path, name: &str) -> Result<()> {
    if !parent.exists() {
        return Ok(());
    }
    // The canonical name owns its exact filename, so obsolete or damaged build
    // output can be regenerated. Refuse case-folded collisions on every host to
    // keep the convention portable without interpreting previous package bytes.
    for existing in std::fs::read_dir(parent).map_err(|_| "source-output-directory")? {
        let existing = existing.map_err(|_| "source-output-directory")?.file_name();
        if existing
            .to_str()
            .is_some_and(|other| other != name && other.eq_ignore_ascii_case(name))
        {
            return Err("source-output-collision".into());
        }
    }
    Ok(())
}
