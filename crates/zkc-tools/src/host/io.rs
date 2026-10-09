//! Bounded byte ingress used by host adapters and command-line tools.
use std::{
    io::{self, Read},
    path::Path,
};

#[derive(Debug)]
pub(crate) enum ReadError {
    Io(io::Error),
    Limit,
}
impl std::fmt::Display for ReadError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Io(error) => write!(f, "{error}"),
            Self::Limit => f.write_str("input byte limit exceeded"),
        }
    }
}
/// File-based adapters use regular files. Nonblocking open prevents a FIFO swap from
/// hanging before descriptor validation. Symlinks resolve normally; the opened
/// descriptor is checked and read once, so path changes cannot replace it.
pub(crate) fn read_regular(path: impl AsRef<Path>, limit: usize) -> Result<Vec<u8>, ReadError> {
    read_from(open_regular(path)?, limit)
}
pub(crate) fn open_regular(path: impl AsRef<Path>) -> Result<std::fs::File, ReadError> {
    let mut options = std::fs::OpenOptions::new();
    options.read(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt;
        options.custom_flags(libc::O_NONBLOCK);
    }
    let file = options.open(path).map_err(ReadError::Io)?;
    if !file.metadata().map_err(ReadError::Io)?.is_file() {
        return Err(ReadError::Io(io::Error::new(
            io::ErrorKind::InvalidInput,
            "expected a regular file",
        )));
    }
    Ok(file)
}
fn read_from(reader: impl Read, limit: usize) -> Result<Vec<u8>, ReadError> {
    let mut bytes = Vec::new();
    reader
        .take((limit as u64).saturating_add(1))
        .read_to_end(&mut bytes)
        .map_err(ReadError::Io)?;
    if bytes.len() > limit {
        return Err(ReadError::Limit);
    }
    Ok(bytes)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn exact_limit_is_accepted_but_trailing_bytes_are_refused() {
        assert_eq!(read_from(&b"abcd"[..], 4).unwrap(), b"abcd");
        assert!(matches!(read_from(&b"abcde"[..], 4), Err(ReadError::Limit)));
        assert!(matches!(read_from(&b"x"[..], 0), Err(ReadError::Limit)));
        assert!(read_from(&b""[..], 0).unwrap().is_empty());
    }
    #[test]
    fn key_files_are_bounded_regular_descriptors() {
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("key");
        std::fs::write(&path, b"abcd").unwrap();
        assert_eq!(read_regular(&path, 4).unwrap(), b"abcd");
        assert!(matches!(read_regular(&path, 3), Err(ReadError::Limit)));
        assert!(matches!(
            read_regular(directory.path(), 100),
            Err(ReadError::Io(_))
        ));
        assert!(matches!(
            read_regular(directory.path().join("missing"), 100),
            Err(ReadError::Io(_))
        ));
        #[cfg(unix)]
        {
            let link = directory.path().join("link");
            std::os::unix::fs::symlink(&path, &link).unwrap();
            assert_eq!(read_regular(&link, 4).unwrap(), b"abcd");
            let fifo = directory.path().join("fifo");
            assert!(
                std::process::Command::new("mkfifo")
                    .arg(&fifo)
                    .status()
                    .unwrap()
                    .success()
            );
            // There is no writer. Opening must return without waiting for one.
            assert!(matches!(read_regular(&fifo, 100), Err(ReadError::Io(_))));
            assert!(matches!(
                read_regular("/dev/zero", 100),
                Err(ReadError::Io(_))
            ));
        }
    }
}
