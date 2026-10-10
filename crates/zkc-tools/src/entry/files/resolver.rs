//! A separate directory capability for each selected JSON document. References
//! cannot escape it or traverse symlinks, and retain the opened descriptor.
use super::super::{
    NamedValues,
    inputs::{Decoder, InputError, InputGroup, Resolver},
};
use crate::{
    execution::{Capacity, InputFile},
    host::io,
};
use std::{
    collections::BTreeMap,
    fs::{File, Metadata},
    path::Path,
};

pub struct Documents {
    decoder: Decoder,
    files: Vec<Metadata>,
}
impl Documents {
    pub fn new(capacity: Capacity) -> Result<Self, String> {
        Ok(Self {
            decoder: Decoder::new(capacity)?,
            files: Vec::new(),
        })
    }
    /// Omission is valid only for an empty map, including required zero-leaf ports.
    pub fn load(
        &mut self,
        group: &InputGroup<'_>,
        path: Option<&Path>,
    ) -> Result<NamedValues, InputError> {
        let Some(path) = path else {
            return if group.is_empty() {
                Ok(NamedValues::new())
            } else {
                Err(InputError {
                    code: "entry-input-missing".into(),
                    path: group.name().into(),
                })
            };
        };
        let error = |e| InputError {
            code: file_error(e, "entry-input-document"),
            path: group.name().into(),
        };
        let directory = Directory::new(path).map_err(error)?;
        let file = directory.document(path).map_err(error)?;
        self.files.push(file.metadata().map_err(error)?);
        let bytes = io::read_from(file, self.decoder.remaining_document_bytes()).map_err(|e| {
            InputError {
                code: match e {
                    io::ReadError::Limit => "entry-request-limit",
                    _ => "entry-input-document",
                }
                .into(),
                path: group.name().into(),
            }
        })?;
        let mut resolver = References {
            directory,
            files: &mut self.files,
            cache: BTreeMap::new(),
        };
        self.decoder.decode(group, &bytes, Some(&mut resolver))
    }
    pub(crate) fn protect(
        &self,
        outputs: &mut crate::host::publication::Outputs,
    ) -> Result<(), String> {
        for metadata in &self.files {
            outputs.protect_metadata(metadata)?;
        }
        Ok(())
    }
}
struct References<'a> {
    directory: Directory,
    files: &'a mut Vec<Metadata>,
    cache: BTreeMap<String, InputFile>,
}
impl Resolver for References<'_> {
    fn resolve(&mut self, path: &str) -> Result<InputFile, String> {
        if let Some(file) = self.cache.get(path) {
            return Ok(file.clone());
        }
        let file = self
            .directory
            .reference(path)
            .map_err(|e| file_error(e, "entry-input-reference"))?;
        self.files.push(
            file.metadata()
                .map_err(|e| file_error(e, "entry-input-reference"))?,
        );
        let file = InputFile::new(file)?;
        self.cache.insert(path.into(), file.clone());
        Ok(file)
    }
}
fn file_error(error: std::io::Error, fallback: &str) -> String {
    #[cfg(unix)]
    if matches!(error.raw_os_error(), Some(libc::EMFILE | libc::ENFILE)) {
        return "entry-input-descriptor-limit".into();
    }
    let _ = error;
    fallback.into()
}
struct Directory {
    #[cfg(unix)]
    root: File,
    #[cfg(not(unix))]
    parent: std::path::PathBuf,
}
impl Directory {
    fn new(path: &Path) -> std::io::Result<Self> {
        let parent = path
            .parent()
            .filter(|p| !p.as_os_str().is_empty())
            .unwrap_or(Path::new("."));
        #[cfg(unix)]
        {
            use rustix::fs::{Mode, OFlags, open};
            Ok(Self {
                root: open(
                    parent,
                    OFlags::RDONLY | OFlags::DIRECTORY | OFlags::CLOEXEC,
                    Mode::empty(),
                )?
                .into(),
            })
        }
        #[cfg(not(unix))]
        {
            Ok(Self {
                parent: parent.to_owned(),
            })
        }
    }
    fn document(&self, path: &Path) -> std::io::Result<File> {
        let name = path.file_name().ok_or_else(invalid)?;
        #[cfg(unix)]
        {
            self.open(name)
        }
        #[cfg(not(unix))]
        {
            io::open_regular(self.parent.join(name)).map_err(|_| invalid())
        }
    }
    #[cfg(unix)]
    fn open(&self, name: &std::ffi::OsStr) -> std::io::Result<File> {
        use rustix::fs::{Mode, OFlags, openat};
        let file: File = openat(
            &self.root,
            name,
            OFlags::RDONLY | OFlags::NOFOLLOW | OFlags::NONBLOCK | OFlags::CLOEXEC,
            Mode::empty(),
        )?
        .into();
        if !file.metadata()?.is_file() {
            return Err(invalid());
        }
        Ok(file)
    }
    fn reference(&self, path: &str) -> std::io::Result<File> {
        if path.is_empty()
            || path.len() > 4096
            || path.contains(['\0', '\\'])
            || path
                .split('/')
                .any(|p| p.is_empty() || p == "." || p == "..")
        {
            return Err(invalid());
        }
        #[cfg(unix)]
        {
            use rustix::fs::{Mode, OFlags, openat};
            let mut parts = path.split('/').peekable();
            let mut dir = self.root.try_clone()?;
            while let Some(part) = parts.next() {
                if parts.peek().is_none() {
                    return Self { root: dir }.open(std::ffi::OsStr::new(part));
                }
                dir = openat(
                    &dir,
                    part,
                    OFlags::RDONLY | OFlags::DIRECTORY | OFlags::NOFOLLOW | OFlags::CLOEXEC,
                    Mode::empty(),
                )?
                .into();
            }
        }
        Err(invalid())
    }
}
fn invalid() -> std::io::Error {
    std::io::Error::new(std::io::ErrorKind::InvalidInput, "input reference")
}

#[cfg(all(test, unix))]
mod tests {
    use super::*;
    #[test]
    fn repeated_references_share_one_descriptor_and_protected_identity() {
        let directory = tempfile::tempdir().unwrap();
        std::fs::write(directory.path().join("value"), b"original").unwrap();
        let mut identities = vec![];
        let mut resolver = References {
            directory: Directory::new(&directory.path().join("inputs.json")).unwrap(),
            files: &mut identities,
            cache: BTreeMap::new(),
        };
        let first = resolver.resolve("value").unwrap();
        for _ in 0..1024 {
            assert!(first.same_source(&resolver.resolve("value").unwrap()));
        }
        assert_eq!(resolver.files.len(), 1);
        for code in [libc::EMFILE, libc::ENFILE] {
            assert_eq!(
                file_error(std::io::Error::from_raw_os_error(code), "invalid"),
                "entry-input-descriptor-limit"
            );
        }
    }
}
