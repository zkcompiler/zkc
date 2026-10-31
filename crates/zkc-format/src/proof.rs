//! Proof format identities, bounded framing and lazy borrowed cursors.
use std::fmt;

/// Selected by an authenticated deployment, independently of proof contents.
#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Deserialize)]
pub enum ProofFormat {
    #[serde(rename = "zkc.framed/0")]
    Native,
    #[serde(rename = "raw.bytes/0")]
    RawBytes,
}
impl ProofFormat {
    pub fn parse(value: &str) -> Option<Self> {
        match value {
            "zkc.framed/0" => Some(Self::Native),
            "raw.bytes/0" => Some(Self::RawBytes),
            _ => None,
        }
    }
    pub fn name(self) -> &'static str {
        match self {
            Self::Native => "zkc.framed/0",
            Self::RawBytes => "raw.bytes/0",
        }
    }
}

pub const MAX_PROOF_BYTES: usize = 16 * 1024 * 1024;
pub const MAGIC: &[u8; 8] = b"ZKCPRF00";
pub const HEADER_BYTES: usize = MAGIC.len() + 32;
pub const MESSAGE_LENGTH_BYTES: usize = 8;

/// The native header carries the caller's independently supplied binding.
pub fn header(expected_binding: &[u8; 32]) -> [u8; HEADER_BYTES] {
    let mut bytes = [0; HEADER_BYTES];
    bytes[..MAGIC.len()].copy_from_slice(MAGIC);
    bytes[MAGIC.len()..].copy_from_slice(expected_binding);
    bytes
}

pub fn header_size(format: ProofFormat) -> usize {
    match format {
        ProofFormat::Native => HEADER_BYTES,
        ProofFormat::RawBytes => 0,
    }
}

pub fn validate_limit(format: ProofFormat, limit: usize) -> Result<(), FormatError> {
    if !(header_size(format)..=MAX_PROOF_BYTES).contains(&limit) {
        return Err(FormatError::Limit);
    }
    Ok(())
}

/// Check append syntax and size before any live reservation or storage change.
/// This does not reserve memory or grant a runtime budget.
pub fn message_preflight(
    format: ProofFormat,
    bytes_written: usize,
    messages: usize,
    payload_bytes: usize,
    limit: usize,
) -> Result<usize, FormatError> {
    if format == ProofFormat::RawBytes && messages != 0 {
        return Err(FormatError::Trailing);
    }
    let overhead = match format {
        ProofFormat::Native => MESSAGE_LENGTH_BYTES,
        ProofFormat::RawBytes => 0,
    };
    let additional = payload_bytes
        .checked_add(overhead)
        .ok_or(FormatError::Limit)?;
    if bytes_written.saturating_add(additional) > limit {
        return Err(FormatError::Limit);
    }
    Ok(additional)
}

pub fn message_length(payload_bytes: usize) -> [u8; MESSAGE_LENGTH_BYTES] {
    (payload_bytes as u64).to_le_bytes()
}

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

pub struct ProofReader<'a> {
    format: ProofFormat,
    bytes: &'a [u8],
    position: usize,
    messages: usize,
}
impl<'a> ProofReader<'a> {
    pub fn new(
        format: ProofFormat,
        bytes: &'a [u8],
        expected_binding: &[u8; 32],
    ) -> Result<Self, FormatError> {
        if bytes.len() > MAX_PROOF_BYTES {
            return Err(FormatError::Limit);
        }
        if format == ProofFormat::RawBytes {
            return Ok(Self {
                format,
                bytes,
                position: 0,
                messages: 0,
            });
        }
        if bytes.len() < HEADER_BYTES {
            return Err(FormatError::Truncated);
        }
        if &bytes[..MAGIC.len()] != MAGIC || &bytes[MAGIC.len()..HEADER_BYTES] != expected_binding {
            return Err(FormatError::Header);
        }
        Ok(Self {
            format,
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
        if self.format == ProofFormat::RawBytes {
            if self.messages != 0 {
                return Err(FormatError::Truncated);
            }
            self.messages = 1;
            return self.read(self.bytes.len());
        }
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
        if self.format == ProofFormat::RawBytes && self.messages != 1 {
            return Err(FormatError::Truncated);
        }
        if self.position == self.bytes.len() {
            Ok(())
        } else {
            Err(FormatError::Trailing)
        }
    }
}
