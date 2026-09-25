use std::fmt;

pub const MAX_PROOF_BYTES: usize = 16 * 1024 * 1024;
const MAGIC: &[u8; 8] = b"ZKCPRF01";
const HEADER_BYTES: usize = MAGIC.len() + 32;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FormatError {
    Limit,
    Allocation,
    Header,
    Truncated,
    Trailing,
}
impl fmt::Display for FormatError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::Limit => "proof-limit",
            Self::Allocation => "proof-allocation",
            Self::Header => "proof-header",
            Self::Truncated => "proof-truncated",
            Self::Trailing => "proof-trailing",
        })
    }
}
impl std::error::Error for FormatError {}

/// Expected context is supplied by the application, never by the candidate.
pub struct ProofWriter {
    bytes: Vec<u8>,
    messages: usize,
}
impl ProofWriter {
    pub fn new(expected_binding: &[u8; 32]) -> Self {
        let mut bytes = Vec::with_capacity(HEADER_BYTES);
        bytes.extend_from_slice(MAGIC);
        bytes.extend_from_slice(expected_binding);
        Self { bytes, messages: 0 }
    }
    pub fn message(&mut self, payload: &[u8]) -> Result<(), FormatError> {
        let additional = payload.len().checked_add(8).ok_or(FormatError::Limit)?;
        if self.bytes.len().saturating_add(additional) > MAX_PROOF_BYTES {
            return Err(FormatError::Limit);
        }
        self.bytes
            .try_reserve(additional)
            .map_err(|_| FormatError::Allocation)?;
        self.bytes
            .extend_from_slice(&(payload.len() as u64).to_le_bytes());
        self.bytes.extend_from_slice(payload);
        self.messages += 1;
        Ok(())
    }
    pub fn messages(&self) -> usize {
        self.messages
    }
    pub fn bytes_written(&self) -> usize {
        self.bytes.len()
    }
    pub fn finish(self) -> Vec<u8> {
        self.bytes
    }
}

pub struct ProofReader<'a> {
    bytes: &'a [u8],
    position: usize,
    messages: usize,
}
impl<'a> ProofReader<'a> {
    pub fn new(bytes: &'a [u8], expected_binding: &[u8; 32]) -> Result<Self, FormatError> {
        if bytes.len() > MAX_PROOF_BYTES {
            return Err(FormatError::Limit);
        }
        if bytes.len() < HEADER_BYTES {
            return Err(FormatError::Truncated);
        }
        if &bytes[..MAGIC.len()] != MAGIC || &bytes[MAGIC.len()..HEADER_BYTES] != expected_binding {
            return Err(FormatError::Header);
        }
        Ok(Self {
            bytes,
            position: HEADER_BYTES,
            messages: 0,
        })
    }
    fn read(&mut self, count: usize) -> Result<&'a [u8], FormatError> {
        let end = self.position.checked_add(count).ok_or(FormatError::Limit)?;
        let bytes = self
            .bytes
            .get(self.position..end)
            .ok_or(FormatError::Truncated)?;
        self.position = end;
        Ok(bytes)
    }
    /// Length consumption survives payload failure. Decoding is the caller's
    /// next step, so a malformed value also retains its consumed message bytes.
    pub fn message(&mut self) -> Result<&'a [u8], FormatError> {
        let length: [u8; 8] = self
            .read(8)?
            .try_into()
            .map_err(|_| FormatError::Truncated)?;
        let length = usize::try_from(u64::from_le_bytes(length)).map_err(|_| FormatError::Limit)?;
        if length > MAX_PROOF_BYTES {
            return Err(FormatError::Limit);
        }
        let bytes = self.read(length)?;
        self.messages += 1;
        Ok(bytes)
    }
    pub fn messages(&self) -> usize {
        self.messages
    }
    pub fn bytes_read(&self) -> usize {
        self.position
    }
    pub fn finish(&self) -> Result<(), FormatError> {
        if self.position == self.bytes.len() {
            Ok(())
        } else {
            Err(FormatError::Trailing)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn exact_context_and_bounded_payload_consumption() {
        // Independently spelled fixture: one 3-byte payload and one empty
        // payload. Payload framing cannot steal or ignore trailing messages.
        let mut fixture = b"ZKCPRF01".to_vec();
        fixture.extend([9; 32]);
        fixture.extend([3, 0, 0, 0, 0, 0, 0, 0, 4, 5, 6]);
        fixture.extend([0; 8]);
        let mut writer = ProofWriter::new(&[9; 32]);
        writer.message(&[4, 5, 6]).unwrap();
        writer.message(&[]).unwrap();
        assert_eq!(writer.finish(), fixture);
        let mut reader = ProofReader::new(&fixture, &[9; 32]).unwrap();
        assert_eq!(reader.message().unwrap(), [4, 5, 6]);
        assert_eq!(reader.finish(), Err(FormatError::Trailing));
        assert!(reader.message().unwrap().is_empty());
        assert_eq!(reader.finish(), Ok(()));
        assert!(matches!(
            ProofReader::new(&fixture, &[8; 32]),
            Err(FormatError::Header)
        ));
        for end in 0..fixture.len() {
            let result = (|| {
                let mut reader = ProofReader::new(&fixture[..end], &[9; 32])?;
                reader.message()?;
                reader.message()?;
                reader.finish()
            })();
            assert_eq!(result, Err(FormatError::Truncated), "prefix {end}");
        }
        let mut hostile = fixture[..48].to_vec();
        hostile[40..48].fill(255);
        let mut reader = ProofReader::new(&hostile, &[9; 32]).unwrap();
        assert_eq!(reader.message(), Err(FormatError::Limit));
        assert_eq!(reader.bytes_read(), 48);
    }
}
