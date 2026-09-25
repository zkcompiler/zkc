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
pub(crate) fn read_bounded(path: impl AsRef<Path>, limit: usize) -> Result<Vec<u8>, ReadError> {
    read_from(std::fs::File::open(path).map_err(ReadError::Io)?, limit)
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
}
