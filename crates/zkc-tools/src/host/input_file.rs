//! Descriptor-backed inputs, read under the Host's cumulative loading budget.
use std::{
    fs::File,
    io::{Seek, SeekFrom},
    sync::{Arc, Mutex},
};

#[derive(Clone, Debug)]
pub struct InputFile(Arc<Mutex<File>>);
impl InputFile {
    pub(crate) fn same_source(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
    pub fn new(file: File) -> Result<Self, String> {
        if !file
            .metadata()
            .map_err(|_| "entry-input-reference")?
            .is_file()
        {
            return Err("entry-input-reference".into());
        }
        Ok(Self(Arc::new(Mutex::new(file))))
    }
    pub(crate) fn read(&self, limit: usize) -> Result<Vec<u8>, super::io::ReadError> {
        let mut file = self
            .0
            .lock()
            .map_err(|_| super::io::ReadError::Io(std::io::Error::other("input lock")))?;
        file.seek(SeekFrom::Start(0))
            .map_err(super::io::ReadError::Io)?;
        super::io::read_from(&mut *file, limit)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn descriptors_are_bounded_reusable_and_independent_of_path_replacement() {
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("input");
        std::fs::write(&path, b"original").unwrap();
        let input = InputFile::new(File::open(&path).unwrap()).unwrap();
        assert!(matches!(
            input.read(7),
            Err(super::super::io::ReadError::Limit)
        ));
        std::fs::rename(&path, directory.path().join("old")).unwrap();
        std::fs::write(&path, b"replacement").unwrap();
        assert_eq!(input.read(8).unwrap(), b"original");
        assert_eq!(input.clone().read(8).unwrap(), b"original");
    }
}
