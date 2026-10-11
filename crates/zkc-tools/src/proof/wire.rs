use std::{borrow::Cow, fmt};

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
    pub(super) fn encode<'a>(
        self,
        backend: &zkc_backends::NativeBackend,
        value: &'a zkc_backends::Value,
    ) -> Result<Cow<'a, [u8]>, super::ArtifactFailure> {
        match self {
            Self::Native => backend.encode_native_value(value).map(Cow::Owned),
            Self::RawBytes => backend.encode_raw_bytes(value).map(Cow::Borrowed),
        }
        .map_err(super::ArtifactFailure::NativeWire)
    }
    pub(super) fn decode(
        self,
        backend: &zkc_backends::NativeBackend,
        ty: &zkc_runtime::interactive::PhysicalType,
        bytes: &[u8],
    ) -> Result<zkc_backends::Value, zkc_backends::NativeWireError> {
        match self {
            Self::Native => backend.decode_native_value(ty, bytes),
            Self::RawBytes => backend.decode_raw_bytes(ty, bytes),
        }
    }
}

pub const MAX_PROOF_BYTES: usize = 16 * 1024 * 1024;
const MAGIC: &[u8; 8] = b"ZKCPRF00";
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
    format: ProofFormat,
    bytes: Vec<u8>,
    messages: usize,
    limit: usize,
}
impl ProofWriter {
    pub fn new(format: ProofFormat, expected_binding: &[u8; 32]) -> Self {
        let mut bytes = Vec::new();
        if format == ProofFormat::Native {
            bytes.extend_from_slice(MAGIC);
            bytes.extend_from_slice(expected_binding);
        }
        Self {
            format,
            bytes,
            messages: 0,
            limit: MAX_PROOF_BYTES,
        }
    }
    /// A host can lower the buffer ceiling, including the framing header.
    pub fn with_limit(
        format: ProofFormat,
        expected_binding: &[u8; 32],
        limit: usize,
    ) -> Result<Self, FormatError> {
        let minimum = if format == ProofFormat::Native {
            HEADER_BYTES
        } else {
            0
        };
        if !(minimum..=MAX_PROOF_BYTES).contains(&limit) {
            return Err(FormatError::Limit);
        }
        let mut writer = Self::new(format, expected_binding);
        writer.limit = limit;
        Ok(writer)
    }
    pub fn message(&mut self, payload: &[u8]) -> Result<(), FormatError> {
        if self.format == ProofFormat::RawBytes && self.messages != 0 {
            return Err(FormatError::Trailing);
        }
        let overhead = if self.format == ProofFormat::Native {
            8
        } else {
            0
        };
        let additional = payload
            .len()
            .checked_add(overhead)
            .ok_or(FormatError::Limit)?;
        if self.bytes.len().saturating_add(additional) > self.limit {
            return Err(FormatError::Limit);
        }
        self.bytes
            .try_reserve(additional)
            .map_err(|_| FormatError::Allocation)?;
        if self.format == ProofFormat::Native {
            self.bytes
                .extend_from_slice(&(payload.len() as u64).to_le_bytes());
        }
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
    pub fn finish(self) -> Result<Vec<u8>, FormatError> {
        if self.format == ProofFormat::RawBytes && self.messages != 1 {
            return Err(FormatError::Truncated);
        }
        Ok(self.bytes)
    }
}

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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn raw_bytes_are_one_bounded_message_without_content_detection() {
        for payload in [&[][..], b"ZKCPRF00payload", &[0xff, 0, 0x80]] {
            let mut writer =
                ProofWriter::with_limit(ProofFormat::RawBytes, &[1; 32], payload.len()).unwrap();
            writer.message(payload).unwrap();
            assert_eq!(writer.message(&[]), Err(FormatError::Trailing));
            assert_eq!(writer.messages(), 1);
            assert_eq!(writer.finish().unwrap(), payload);
            let mut reader = ProofReader::new(ProofFormat::RawBytes, payload, &[2; 32]).unwrap();
            assert_eq!(reader.finish(), Err(FormatError::Truncated));
            assert_eq!(reader.message().unwrap(), payload);
            assert_eq!(reader.bytes_read(), payload.len());
            assert_eq!(reader.message(), Err(FormatError::Truncated));
            assert_eq!(reader.finish(), Ok(()));
        }
        assert_eq!(
            ProofWriter::new(ProofFormat::RawBytes, &[0; 32]).finish(),
            Err(FormatError::Truncated)
        );
        let mut writer = ProofWriter::with_limit(ProofFormat::RawBytes, &[0; 32], 2).unwrap();
        assert_eq!(writer.message(&[1, 2, 3]), Err(FormatError::Limit));
        assert_eq!(writer.messages(), 0);
        assert_eq!(writer.bytes_written(), 0);
    }

    #[test]
    fn lowered_writer_limit_includes_header_and_refuses_before_buffer_extension() {
        assert!(matches!(
            ProofWriter::with_limit(ProofFormat::Native, &[0; 32], 39),
            Err(FormatError::Limit)
        ));
        assert!(matches!(
            ProofWriter::with_limit(ProofFormat::Native, &[0; 32], MAX_PROOF_BYTES + 1),
            Err(FormatError::Limit)
        ));
        let mut writer = ProofWriter::with_limit(ProofFormat::Native, &[0; 32], 49).unwrap();
        writer.message(&[1]).unwrap();
        assert_eq!(writer.message(&[]), Err(FormatError::Limit));
        assert_eq!(writer.bytes_written(), 49);
        assert_eq!(writer.messages(), 1);
    }
    #[test]
    fn exact_context_and_bounded_payload_consumption() {
        // Independently spelled fixture: one 3-byte payload and one empty
        // payload. Payload framing cannot steal or ignore trailing messages.
        let mut fixture = b"ZKCPRF00".to_vec();
        fixture.extend([9; 32]);
        fixture.extend([3, 0, 0, 0, 0, 0, 0, 0, 4, 5, 6]);
        fixture.extend([0; 8]);
        let mut writer = ProofWriter::new(ProofFormat::Native, &[9; 32]);
        writer.message(&[4, 5, 6]).unwrap();
        writer.message(&[]).unwrap();
        assert_eq!(writer.finish().unwrap(), fixture);
        let mut reader = ProofReader::new(ProofFormat::Native, &fixture, &[9; 32]).unwrap();
        assert_eq!(reader.message().unwrap(), [4, 5, 6]);
        assert_eq!(reader.finish(), Err(FormatError::Trailing));
        assert!(reader.message().unwrap().is_empty());
        assert_eq!(reader.finish(), Ok(()));
        assert!(matches!(
            ProofReader::new(ProofFormat::Native, &fixture, &[8; 32]),
            Err(FormatError::Header)
        ));
        for end in 0..fixture.len() {
            let result = (|| {
                let mut reader = ProofReader::new(ProofFormat::Native, &fixture[..end], &[9; 32])?;
                reader.message()?;
                reader.message()?;
                reader.finish()
            })();
            assert_eq!(result, Err(FormatError::Truncated), "prefix {end}");
        }
        let mut hostile = fixture[..48].to_vec();
        hostile[40..48].fill(255);
        let mut reader = ProofReader::new(ProofFormat::Native, &hostile, &[9; 32]).unwrap();
        assert_eq!(reader.message(), Err(FormatError::Limit));
        assert_eq!(reader.bytes_read(), 48);
    }
}
