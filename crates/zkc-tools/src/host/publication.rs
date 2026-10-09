//! Trusted path configuration and per-file atomic publication, without a
//! multi-file transaction or isolation from concurrent filesystem mutation.
use serde_json::{Value as Json, json};
use std::{
    fs,
    io::Write,
    path::{Path, PathBuf},
};

type Result<T> = std::result::Result<T, String>;
const PATH_ERROR: &str = "artifact-output-path";
const IO_ERROR: &str = "artifact-publish-io";

struct Identity {
    location: PathBuf,
    target: Option<PathBuf>,
    #[cfg(unix)]
    inode: Option<(u64, u64)>,
}
impl Identity {
    fn input(path: &Path) -> Result<Self> {
        let absolute = std::path::absolute(path).map_err(|_| PATH_ERROR)?;
        let parent = absolute.parent().ok_or(PATH_ERROR)?;
        let location = parent
            .canonicalize()
            .unwrap_or_else(|_| parent.into())
            .join(absolute.file_name().ok_or(PATH_ERROR)?);
        Ok(Self {
            location,
            target: path.canonicalize().ok(),
            #[cfg(unix)]
            inode: fs::metadata(path).ok().map(|m| {
                use std::os::unix::fs::MetadataExt;
                (m.dev(), m.ino())
            }),
        })
    }
    fn aliases(&self, other: &Self) -> bool {
        if self.location == other.location
            || self.target.as_ref() == Some(&other.location)
            || other.target.as_ref() == Some(&self.location)
            || self.target.is_some() && self.target == other.target
        {
            return true;
        }
        #[cfg(unix)]
        if self.inode.is_some() && self.inode == other.inode {
            return true;
        }
        false
    }
}

/// Canonical parent paths are retained, so subsequent publication uses the same
/// selected directory. Existing output symlinks and nonregular files refuse.
pub(crate) struct Outputs {
    paths: Vec<PathBuf>,
    protected_paths: Vec<PathBuf>,
    protected: Vec<Identity>,
}
impl Outputs {
    pub(crate) fn new(outputs: &[&str], inputs: &[&str]) -> Result<Self> {
        let mut paths = Vec::new();
        for path in outputs {
            let absolute = std::path::absolute(path).map_err(|_| PATH_ERROR)?;
            let parent = absolute
                .parent()
                .ok_or(PATH_ERROR)?
                .canonicalize()
                .map_err(|_| PATH_ERROR)?;
            if !parent.is_dir() {
                return Err(PATH_ERROR.into());
            }
            paths.push(parent.join(absolute.file_name().ok_or(PATH_ERROR)?));
        }
        let mut result = Self {
            paths,
            protected_paths: Vec::new(),
            protected: Vec::new(),
        };
        result.protect(inputs.iter().copied())?;
        Ok(result)
    }
    pub(crate) fn protect<'a>(&mut self, inputs: impl IntoIterator<Item = &'a str>) -> Result<()> {
        if self.paths.is_empty() {
            return Ok(());
        }
        for input in inputs {
            self.protected.push(Identity::input(Path::new(input))?);
            self.protected_paths.push(input.into());
        }
        self.check()
    }
    fn check(&self) -> Result<()> {
        let current = self
            .protected_paths
            .iter()
            .map(|p| Identity::input(p))
            .collect::<Result<Vec<_>>>()?;
        let mut selected = Vec::new();
        for path in &self.paths {
            match fs::symlink_metadata(path) {
                Ok(metadata) if !metadata.is_file() => return Err(PATH_ERROR.into()),
                Err(error) if error.kind() != std::io::ErrorKind::NotFound => {
                    return Err(PATH_ERROR.into());
                }
                _ => {}
            }
            let output = Identity::input(path)?;
            if selected
                .iter()
                .chain(&self.protected)
                .chain(&current)
                .any(|input| output.aliases(input))
            {
                return Err(PATH_ERROR.into());
            }
            selected.push(output);
        }
        Ok(())
    }
    fn stage(&self, bytes: &[(&str, &[u8])]) -> Result<Vec<tempfile::NamedTempFile>> {
        self.check()?;
        if bytes.len() != self.paths.len() {
            return Err(PATH_ERROR.into());
        }
        let mut staged = Vec::new();
        for (path, (_, bytes)) in self.paths.iter().zip(bytes) {
            let mut file = tempfile::NamedTempFile::new_in(path.parent().ok_or(PATH_ERROR)?)
                .map_err(|_| IO_ERROR)?;
            file.write_all(bytes).map_err(|_| IO_ERROR)?;
            file.as_file().sync_all().map_err(|_| IO_ERROR)?;
            staged.push(file);
        }
        Ok(staged)
    }
    /// Every supplied buffer must already be encoded. Stage the entire set before
    /// the first rename, and retain exactly which renames completed on refusal.
    pub(crate) fn publish(&self, bytes: &[(&str, &[u8])], report: &mut Json) -> Result<()> {
        self.publish_with(bytes, report, |file, path| {
            file.persist(path)
                .map(|_| ())
                .map_err(|_| IO_ERROR.to_owned())
        })
    }
    fn publish_with(
        &self,
        bytes: &[(&str, &[u8])],
        report: &mut Json,
        mut persist: impl FnMut(tempfile::NamedTempFile, &Path) -> Result<()>,
    ) -> Result<()> {
        report["publication"] = json!({"requested": bytes.iter().map(|(name, _)| name).collect::<Vec<_>>(),
            "published": [], "stage": "staging"});
        let staged = self.stage(bytes)?;
        // A second check catches changes during staging without promising race isolation.
        self.check()?;
        report["publication"]["stage"] = json!("publication");
        for ((path, file), (name, _)) in self.paths.iter().zip(staged).zip(bytes) {
            if let Err(error) = persist(file, path) {
                report["publication"]["failed"] = json!(name);
                return Err(error);
            }
            report["publication"]["published"]
                .as_array_mut()
                .unwrap()
                .push(json!(name));
            report[format!("{name}_published")] = json!(true);
        }
        report["publication"]["stage"] = json!("complete");
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[cfg(unix)]
    #[test]
    fn publication_keeps_private_tempfile_mode_for_new_and_replaced_files() {
        use std::os::unix::fs::PermissionsExt;
        let dir = tempfile::tempdir().unwrap();
        let new = dir.path().join("new");
        let replaced = dir.path().join("replaced");
        fs::write(&replaced, b"old").unwrap();
        fs::set_permissions(&replaced, fs::Permissions::from_mode(0o644)).unwrap();
        let outputs =
            Outputs::new(&[new.to_str().unwrap(), replaced.to_str().unwrap()], &[]).unwrap();
        let mut report = json!({});
        outputs
            .publish(&[("proof", b"proof"), ("results", b"results")], &mut report)
            .unwrap();
        for (path, bytes) in [
            (&new, b"proof".as_slice()),
            (&replaced, b"results".as_slice()),
        ] {
            assert_eq!(fs::read(path).unwrap(), bytes);
            assert_eq!(
                fs::metadata(path).unwrap().permissions().mode() & 0o777,
                0o600
            );
        }
        assert_eq!(
            report["publication"]["published"],
            json!(["proof", "results"])
        );
    }

    #[test]
    fn aliases_and_nonregular_outputs_refuse_without_modification() {
        let dir = tempfile::tempdir().unwrap();
        let input = dir.path().join("input");
        let output = dir.path().join("output");
        fs::write(&input, b"trusted").unwrap();
        let i = input.to_str().unwrap();
        let o = output.to_str().unwrap();
        assert!(Outputs::new(&[i], &[i]).is_err());
        assert!(Outputs::new(&[o, o], &[i]).is_err());
        fs::hard_link(&input, &output).unwrap();
        assert!(Outputs::new(&[o], &[i]).is_err());
        assert!(Outputs::new(&[o, i], &[]).is_err());
        fs::remove_file(&output).unwrap();
        #[cfg(unix)]
        {
            std::os::unix::fs::symlink(&input, &output).unwrap();
            assert!(Outputs::new(&[o], &[]).is_err());
            assert!(Outputs::new(&[i], &[o]).is_err());
        }
        assert_eq!(fs::read(&input).unwrap(), b"trusted");
        assert!(Outputs::new(&[dir.path().to_str().unwrap()], &[]).is_err());
    }
    #[test]
    fn staging_failure_preserves_every_previous_file() {
        let dir = tempfile::tempdir().unwrap();
        let first = dir.path().join("first");
        let nested = dir.path().join("nested");
        fs::create_dir(&nested).unwrap();
        let second = nested.join("second");
        fs::write(&first, b"old").unwrap();
        let plan = Outputs::new(&[first.to_str().unwrap(), second.to_str().unwrap()], &[]).unwrap();
        fs::remove_dir(&nested).unwrap();
        let mut report = json!({});
        assert!(
            plan.publish(&[("proof", b"new"), ("results", b"values")], &mut report)
                .is_err()
        );
        assert_eq!(fs::read(&first).unwrap(), b"old");
        assert_eq!(report["publication"]["published"], json!([]));
        assert_eq!(fs::read_dir(dir.path()).unwrap().count(), 1);
    }
    #[test]
    fn later_rename_failure_reports_partial_publication() {
        let dir = tempfile::tempdir().unwrap();
        let first = dir.path().join("proof");
        let second = dir.path().join("results");
        fs::write(&first, b"old proof").unwrap();
        fs::write(&second, b"old results").unwrap();
        let plan = Outputs::new(&[first.to_str().unwrap(), second.to_str().unwrap()], &[]).unwrap();
        let mut report = json!({});
        let mut count = 0;
        let error = plan
            .publish_with(
                &[("proof", b"new proof"), ("results", b"new results")],
                &mut report,
                |file, path| {
                    count += 1;
                    if count == 2 {
                        return Err(IO_ERROR.into());
                    }
                    file.persist(path).unwrap();
                    Ok(())
                },
            )
            .unwrap_err();
        assert_eq!(error, IO_ERROR);
        assert_eq!(fs::read(&first).unwrap(), b"new proof");
        assert_eq!(fs::read(&second).unwrap(), b"old results");
        assert_eq!(report["publication"]["published"], json!(["proof"]));
        assert_eq!(report["publication"]["failed"], "results");
        assert_eq!(report["proof_published"], true);
    }
    #[test]
    fn changed_alias_and_parent_symlinks_are_checked_before_staging() {
        let dir = tempfile::tempdir().unwrap();
        let input = dir.path().join("input");
        let output = dir.path().join("output");
        fs::write(&input, b"trusted").unwrap();
        let plan = Outputs::new(&[output.to_str().unwrap()], &[input.to_str().unwrap()]).unwrap();
        fs::hard_link(&input, &output).unwrap();
        assert_eq!(
            plan.publish(&[("proof", b"changed")], &mut json!({}))
                .unwrap_err(),
            PATH_ERROR
        );
        assert_eq!(fs::read(input).unwrap(), b"trusted");
        #[cfg(unix)]
        {
            let link = dir.path().join("directory-alias");
            std::os::unix::fs::symlink(dir.path(), &link).unwrap();
            let alias = link.join("output");
            assert!(
                Outputs::new(&[output.to_str().unwrap(), alias.to_str().unwrap()], &[]).is_err()
            );
        }
    }
}
