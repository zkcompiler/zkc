//! Trusted path configuration and per-file atomic publication, without a
//! multi-file transaction or isolation from concurrent filesystem mutation.
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
pub struct Outputs {
    paths: Vec<PathBuf>,
    protected_paths: Vec<PathBuf>,
    protected: Vec<Identity>,
}
impl Outputs {
    pub fn new(outputs: &[&str], inputs: &[&str]) -> Result<Self> {
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
    pub fn protect<'a>(&mut self, inputs: impl IntoIterator<Item = &'a str>) -> Result<()> {
        if self.paths.is_empty() {
            return Ok(());
        }
        for input in inputs {
            self.protected.push(Identity::input(Path::new(input))?);
            self.protected_paths.push(input.into());
        }
        self.check()
    }
    /// Preserve the identity of an input already opened through a directory
    /// capability. No path lookup can redirect this protection.
    pub(crate) fn protect_metadata(&mut self, metadata: &fs::Metadata) -> Result<()> {
        #[cfg(unix)]
        {
            use std::os::unix::fs::MetadataExt;
            self.protected.push(Identity {
                location: PathBuf::new(),
                target: None,
                inode: Some((metadata.dev(), metadata.ino())),
            });
        }
        #[cfg(not(unix))]
        {
            let _ = metadata;
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
    /// Encode all buffers before calling. Every file is staged and synced before
    /// any replacement; failures retain exactly the completed ordered prefix.
    pub fn publish(
        &self,
        bytes: &[(&str, &[u8])],
    ) -> std::result::Result<Publication, PublicationError> {
        self.publish_with(bytes, |file, path| {
            file.persist(path)
                .map(|_| ())
                .map_err(|_| IO_ERROR.to_owned())
        })
    }
    /// Create missing files without clobbering an existing file, including races.
    pub fn create(
        &self,
        bytes: &[(&str, &[u8])],
    ) -> std::result::Result<Publication, PublicationError> {
        for path in &self.paths {
            match path.symlink_metadata() {
                Err(e) if e.kind() == std::io::ErrorKind::NotFound => (),
                _ => {
                    return Err(PublicationError {
                        code: "entry-output-exists".into(),
                        conflict: Some(path.clone()),
                        receipt: Box::default(),
                    });
                }
            }
        }
        self.publish_with(bytes, |file, path| {
            file.persist_noclobber(path).map(|_| ()).map_err(|e| {
                if e.error.kind() == std::io::ErrorKind::AlreadyExists {
                    "entry-output-exists".into()
                } else {
                    IO_ERROR.into()
                }
            })
        })
    }
    fn publish_with(
        &self,
        bytes: &[(&str, &[u8])],
        mut persist: impl FnMut(tempfile::NamedTempFile, &Path) -> Result<()>,
    ) -> std::result::Result<Publication, PublicationError> {
        let mut receipt = Publication {
            requested: bytes.iter().map(|(name, _)| (*name).into()).collect(),
            stage: PublicationStage::Staging,
            ..Default::default()
        };
        let mut execute = || -> Result<()> {
            let staged = self.stage(bytes)?;
            self.check()?;
            receipt.stage = PublicationStage::Publication;
            for ((path, file), (name, _)) in self.paths.iter().zip(staged).zip(bytes) {
                if let Err(error) = persist(file, path) {
                    receipt.failed = Some((*name).into());
                    return Err(error);
                }
                receipt.published.push((*name).into());
            }
            receipt.stage = PublicationStage::Complete;
            Ok(())
        };
        match execute() {
            Ok(()) => Ok(receipt),
            Err(code) => Err(PublicationError {
                code,
                conflict: None,
                receipt: Box::new(receipt),
            }),
        }
    }
}

/// Ordered progress after a batch enters staging. A creation conflict detected
/// before staging has an empty receipt. Callers retain earlier batches; this
/// does not imply a multi-file transaction or an automatic rerun policy.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Publication {
    pub requested: Vec<String>,
    pub published: Vec<String>,
    pub stage: PublicationStage,
    pub failed: Option<String>,
}
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum PublicationStage {
    #[default]
    Staging,
    Publication,
    Complete,
}
#[derive(Debug)]
pub struct PublicationError {
    pub code: String,
    pub conflict: Option<PathBuf>,
    /// Ordered progress retained on the error path without enlarging success.
    pub receipt: Box<Publication>,
}
impl std::fmt::Display for PublicationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.code)
    }
}
impl std::error::Error for PublicationError {}

#[cfg(test)]
mod tests {
    use super::*;
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
        assert!(Outputs::new(&[dir.path().to_str().unwrap()], &[]).is_err());
        assert_eq!(fs::read(&input).unwrap(), b"trusted");
    }
    #[cfg(unix)]
    #[test]
    fn publication_retains_private_mode_and_order() {
        use std::os::unix::fs::PermissionsExt;
        let dir = tempfile::tempdir().unwrap();
        let first = dir.path().join("new");
        let second = dir.path().join("replace");
        fs::write(&second, b"old").unwrap();
        fs::set_permissions(&second, fs::Permissions::from_mode(0o644)).unwrap();
        let plan = Outputs::new(&[first.to_str().unwrap(), second.to_str().unwrap()], &[]).unwrap();
        let receipt = plan
            .publish(&[("proof", b"proof"), ("results", b"results")])
            .unwrap();
        assert_eq!(receipt.published, ["proof", "results"]);
        assert_eq!(receipt.stage, PublicationStage::Complete);
        for (path, bytes) in [
            (&first, b"proof".as_slice()),
            (&second, b"results".as_slice()),
        ] {
            assert_eq!(fs::read(path).unwrap(), bytes);
            assert_eq!(
                fs::metadata(path).unwrap().permissions().mode() & 0o777,
                0o600
            );
        }
    }
    #[test]
    fn staging_failure_preserves_all_previous_files_and_prior_batch_receipts() {
        let dir = tempfile::tempdir().unwrap();
        let first = dir.path().join("first");
        let initial = Outputs::new(&[first.to_str().unwrap()], &[])
            .unwrap()
            .create(&[("source", b"source")])
            .unwrap();
        let nested = dir.path().join("nested");
        fs::create_dir(&nested).unwrap();
        let second = nested.join("second");
        let plan = Outputs::new(&[first.to_str().unwrap(), second.to_str().unwrap()], &[]).unwrap();
        fs::remove_dir(&nested).unwrap();
        let error = plan
            .publish(&[("proof", b"new"), ("results", b"values")])
            .unwrap_err();
        assert_eq!(error.receipt.requested, ["proof", "results"]);
        assert!(error.receipt.published.is_empty());
        assert_eq!(error.receipt.stage, PublicationStage::Staging);
        assert_eq!(initial.published, ["source"]);
        assert_eq!(fs::read(first).unwrap(), b"source");
        assert_eq!(fs::read_dir(dir.path()).unwrap().count(), 1);
    }
    #[test]
    fn later_rename_failure_returns_exact_partial_prefix() {
        let dir = tempfile::tempdir().unwrap();
        let first = dir.path().join("proof");
        let second = dir.path().join("results");
        fs::write(&first, b"old proof").unwrap();
        fs::write(&second, b"old results").unwrap();
        let plan = Outputs::new(&[first.to_str().unwrap(), second.to_str().unwrap()], &[]).unwrap();
        let mut count = 0;
        let error = plan
            .publish_with(
                &[("proof", b"new proof"), ("results", b"new results")],
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
        assert_eq!(error.code, IO_ERROR);
        assert_eq!(error.receipt.stage, PublicationStage::Publication);
        assert_eq!(error.receipt.published, ["proof"]);
        assert_eq!(error.receipt.failed.as_deref(), Some("results"));
        assert_eq!(fs::read(first).unwrap(), b"new proof");
        assert_eq!(fs::read(second).unwrap(), b"old results");
    }
    #[test]
    fn creation_never_clobbers_and_aliases_are_rechecked_before_staging() {
        let dir = tempfile::tempdir().unwrap();
        let input = dir.path().join("input");
        let output = dir.path().join("output");
        fs::write(&input, b"trusted").unwrap();
        let plan = Outputs::new(&[output.to_str().unwrap()], &[input.to_str().unwrap()]).unwrap();
        fs::hard_link(&input, &output).unwrap();
        assert_eq!(
            plan.publish(&[("proof", b"new")]).unwrap_err().code,
            PATH_ERROR
        );
        let error = plan.create(&[("proof", b"new")]).unwrap_err();
        assert_eq!(error.code, "entry-output-exists");
        assert_eq!(error.conflict.as_deref(), Some(output.as_path()));
        assert!(error.receipt.published.is_empty());
        assert_eq!(fs::read(input).unwrap(), b"trusted");
    }
}
