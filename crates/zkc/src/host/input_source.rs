//! Immutable byte sources, materialized at the ordinary Host loading phase.
use std::sync::Arc;
#[cfg(feature = "files")]
use std::{
    fs::File,
    io::{Seek, SeekFrom},
    sync::Mutex,
};

#[derive(Clone, Debug)]
pub struct InputSource(Source);
#[derive(Clone, Debug)]
enum Source {
    Bytes(Arc<Vec<u8>>),
    #[cfg(feature = "files")]
    File(Arc<Mutex<File>>),
}
impl InputSource {
    /// Retain immutable bytes without importing or granting setup authority.
    pub fn from_bytes(bytes: Arc<Vec<u8>>) -> Self {
        Self(Source::Bytes(bytes))
    }
    pub(crate) fn same_source(&self, other: &Self) -> bool {
        match (&self.0, &other.0) {
            (Source::Bytes(a), Source::Bytes(b)) => Arc::ptr_eq(a, b),
            #[cfg(feature = "files")]
            (Source::File(a), Source::File(b)) => Arc::ptr_eq(a, b),
            #[cfg(feature = "files")]
            _ => false,
        }
    }
    #[cfg(feature = "files")]
    pub fn new(file: File) -> Result<Self, String> {
        if !file
            .metadata()
            .map_err(|_| "entry-input-reference")?
            .is_file()
        {
            return Err("entry-input-reference".into());
        }
        Ok(Self(Source::File(Arc::new(Mutex::new(file)))))
    }
    pub(crate) fn read_shared(
        &self,
        limit: usize,
        ledger: &zkc_runtime::vm::ExecutionLedger,
    ) -> Result<super::io::SharedBytes, String> {
        match &self.0 {
            Source::Bytes(bytes) => {
                if bytes.len() > limit {
                    return Err("entry-input-reference-byte-limit".into());
                }
                let bound = bytes
                    .len()
                    .checked_mul(2)
                    .and_then(|n| n.checked_add(512))
                    .ok_or("artifact-input-work-limit")?;
                let retained = zkc_runtime::host::wire::reserve_allocation(Some(ledger), bound)?;
                let mut captured = Vec::new();
                captured
                    .try_reserve_exact(bytes.len())
                    .map_err(|_| "entry-input-reference")?;
                captured.extend_from_slice(bytes);
                Ok(super::io::SharedBytes {
                    bytes: captured,
                    retained,
                })
            }
            #[cfg(feature = "files")]
            Source::File(file) => {
                let mut file = file.lock().map_err(|_| "entry-input-reference")?;
                file.seek(SeekFrom::Start(0))
                    .map_err(|_| "entry-input-reference")?;
                super::io::read_shared(&mut file, limit, Some(ledger))
            }
        }
    }
    pub(crate) fn read(&self, limit: usize) -> Result<Vec<u8>, super::io::ReadError> {
        match &self.0 {
            Source::Bytes(bytes) => {
                if bytes.len() > limit {
                    return Err(super::io::ReadError::Limit);
                }
                let mut captured = Vec::new();
                captured.try_reserve_exact(bytes.len()).map_err(|_| {
                    super::io::ReadError::Io(std::io::Error::other("input allocation"))
                })?;
                captured.extend_from_slice(bytes);
                Ok(captured)
            }
            #[cfg(feature = "files")]
            Source::File(file) => {
                let mut file = file
                    .lock()
                    .map_err(|_| super::io::ReadError::Io(std::io::Error::other("input lock")))?;
                file.seek(SeekFrom::Start(0))
                    .map_err(super::io::ReadError::Io)?;
                super::io::read_from(&mut *file, limit)
            }
        }
    }
    /// Capture under a byte ceiling and independently expected wire digest.
    pub fn read_verified(&self, sha256: &[u8; 32], limit: usize) -> Result<Vec<u8>, String> {
        let bytes = self.read(limit).map_err(|e| match e {
            super::io::ReadError::Limit => "entry-input-reference-byte-limit",
            _ => "entry-input-reference",
        })?;
        Self::verify(&bytes, sha256)?;
        Ok(bytes)
    }
    pub(crate) fn verify(bytes: &[u8], sha256: &[u8; 32]) -> Result<(), String> {
        use sha2::{Digest, Sha256};
        if <[u8; 32]>::from(Sha256::digest(bytes)) != *sha256 {
            return Err("entry-input-reference-digest".into());
        }
        Ok(())
    }
}
#[cfg(test)]
mod memory_tests {
    use super::*;

    #[test]
    fn memory_capture_checks_bounds_and_retains_its_own_loading_reservation() {
        let source = InputSource::from_bytes(Arc::new(b"material".to_vec()));
        let ledger = zkc_runtime::vm::ExecutionLedger::new(
            zkc_runtime::vm::ValueBudget {
                live_bytes: 1024,
                total_bytes: 2048,
            },
            Default::default(),
        );
        assert_eq!(
            source.read_shared(7, &ledger).err().unwrap(),
            "entry-input-reference-byte-limit"
        );
        assert_eq!(ledger.snapshot().total_value_bytes, 0);
        let capture = source.read_shared(8, &ledger).unwrap();
        drop(source);
        assert_eq!(capture.bytes, b"material");
        let charged = ledger.snapshot().total_value_bytes;
        assert!(charged >= capture.bytes.len());
        assert!(ledger.snapshot().live_reserved_bytes > 0);
        drop(capture);
        assert_eq!(ledger.snapshot().live_reserved_bytes, 0);
        assert_eq!(ledger.snapshot().total_value_bytes, charged);
    }
}
#[cfg(all(test, feature = "files"))]
mod tests {
    use super::*;
    #[test]
    fn descriptors_are_bounded_reusable_and_independent_of_path_replacement() {
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("input");
        std::fs::write(&path, b"original").unwrap();
        let input = InputSource::new(File::open(&path).unwrap()).unwrap();
        assert!(matches!(
            input.read(7),
            Err(super::super::io::ReadError::Limit)
        ));
        std::fs::rename(&path, directory.path().join("old")).unwrap();
        std::fs::write(&path, b"replacement").unwrap();
        assert_eq!(input.read(8).unwrap(), b"original");
        assert_eq!(input.clone().read(8).unwrap(), b"original");
        use sha2::{Digest, Sha256};
        let pin = Sha256::digest(b"original").into();
        assert_eq!(input.read_verified(&pin, 8).unwrap(), b"original");
        assert_eq!(
            input.read_verified(&pin, 7).unwrap_err(),
            "entry-input-reference-byte-limit"
        );
        assert_eq!(
            input.read_verified(&[0; 32], 8).unwrap_err(),
            "entry-input-reference-digest"
        );
    }
}
