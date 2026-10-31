//! Host wire contracts and bounded proof framing, independent of concrete values.
use crate::vm::{
    Backend, BackendError, DecodeReason, ExecutionLedger, LiveReservation, PhysicalType, WorkBudget,
};
use std::{borrow::Cow, fmt};
use zkc_format::proof::{self, FormatError, MAX_PROOF_BYTES, ProofFormat};

/// Invalid input is an accepted receive attempt; capacity and adapter failures
/// occur before the receive completion. Never classify opaque backend strings.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum WireError {
    Invalid(DecodeReason),
    Limit,
    Backend(BackendError),
}
impl fmt::Display for WireError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Invalid(reason) => write!(f, "host-wire-invalid:{}", reason.as_str()),
            Self::Limit => f.write_str("host-wire-limit"),
            Self::Backend(error) => write!(f, "host-wire-backend:{error}"),
        }
    }
}
impl std::error::Error for WireError {}

/// Trusted wire implementation installed independently of artifacts. Support
/// refers to complete physical identities, never merely their logical kinds.
/// Native implements its closed admitted profile; this is not an artifact codec
/// registry. Bounds must precede allocation and cover all codec-owned storage.
pub trait WireBackend: Backend {
    fn supports_wire(&self, ty: &PhysicalType) -> bool;
    /// Exact width when independent of the value; None means variable width.
    fn fixed_wire_size(&self, _ty: &PhysicalType) -> Option<usize> {
        None
    }
    /// Conservative encoding allocation bound, without performing encoding.
    fn encoding_bound(&self, _value: &Self::Value) -> Result<usize, WireError> {
        Err(WireError::Limit)
    }
    /// Conservative decoded retention before materialization. Unsupported
    /// measurement fails closed, including without a shared execution ledger.
    fn decoding_bound(&self, _ty: &PhysicalType, _bytes: &[u8]) -> Result<usize, WireError> {
        Err(WireError::Limit)
    }
    fn encode_wire(&self, value: &Self::Value) -> Result<Vec<u8>, WireError>;
    fn decode_wire(&self, ty: &PhysicalType, bytes: &[u8]) -> Result<Self::Value, WireError>;
}

/// Proof-specific value access. The application selects the acceptance index
/// and authenticated transport; neither is inferred from proof bytes.
pub trait ProofBackend: WireBackend {
    fn acceptance(&self, value: &Self::Value) -> Option<bool>;
    /// Borrow the existing byte payload without allocating or adding framing.
    /// Its size must be bounded by Value::retained_bytes().
    fn raw_bytes<'a>(&self, _value: &'a Self::Value) -> Result<&'a [u8], WireError> {
        Err(WireError::Backend(BackendError::new(
            "raw-bytes-unsupported",
        )))
    }
    fn raw_decoding_bound(&self, _ty: &PhysicalType, _bytes: &[u8]) -> Result<usize, WireError> {
        Err(WireError::Limit)
    }
    fn decode_raw(&self, _ty: &PhysicalType, _bytes: &[u8]) -> Result<Self::Value, WireError> {
        Err(WireError::Backend(BackendError::new(
            "raw-bytes-unsupported",
        )))
    }
}

pub(crate) fn encode_proof_value<'a, B: ProofBackend>(
    format: ProofFormat,
    backend: &B,
    value: &'a B::Value,
) -> Result<Cow<'a, [u8]>, WireError> {
    match format {
        ProofFormat::Native => backend.encode_wire(value).map(Cow::Owned),
        ProofFormat::RawBytes => backend.raw_bytes(value).map(Cow::Borrowed),
    }
}
pub(crate) fn proof_decoding_bound<B: ProofBackend>(
    format: ProofFormat,
    backend: &B,
    ty: &PhysicalType,
    bytes: &[u8],
) -> Result<usize, WireError> {
    match format {
        ProofFormat::Native => backend.decoding_bound(ty, bytes),
        ProofFormat::RawBytes => backend.raw_decoding_bound(ty, bytes),
    }
}
pub(crate) fn decode_proof_value<B: ProofBackend>(
    format: ProofFormat,
    backend: &B,
    ty: &PhysicalType,
    bytes: &[u8],
) -> Result<B::Value, WireError> {
    match format {
        ProofFormat::Native => backend.decode_wire(ty, bytes),
        ProofFormat::RawBytes => backend.decode_raw(ty, bytes),
    }
}

/// Expected context is supplied by the application, never by the candidate.
pub struct ProofWriter {
    format: ProofFormat,
    bytes: Vec<u8>,
    messages: usize,
    limit: usize,
    ledger: Option<crate::vm::ExecutionLedger>,
    retained: Vec<crate::vm::LiveReservation>,
}
impl ProofWriter {
    pub fn new(format: ProofFormat, expected_binding: &[u8; 32]) -> Self {
        let mut bytes = Vec::new();
        if format == ProofFormat::Native {
            bytes.extend_from_slice(&proof::header(expected_binding));
        }
        Self {
            format,
            bytes,
            messages: 0,
            limit: MAX_PROOF_BYTES,
            ledger: None,
            retained: Vec::new(),
        }
    }
    /// A host can lower the buffer ceiling, including the framing header.
    pub fn with_limit(
        format: ProofFormat,
        expected_binding: &[u8; 32],
        limit: usize,
    ) -> Result<Self, FormatError> {
        proof::validate_limit(format, limit)?;
        let mut writer = Self::new(format, expected_binding);
        writer.limit = limit;
        Ok(writer)
    }
    pub(super) fn with_shared_ledger(
        format: ProofFormat,
        expected_binding: &[u8; 32],
        limit: usize,
        ledger: Option<crate::vm::ExecutionLedger>,
    ) -> Result<Self, FormatError> {
        let header = proof::header_size(format);
        let guard = reserve_allocation(ledger.as_ref(), header).map_err(|_| FormatError::Limit)?;
        let mut writer = Self::with_limit(format, expected_binding, limit)?;
        writer.ledger = ledger;
        writer.retained.extend(guard);
        Ok(writer)
    }
    pub fn message(&mut self, payload: &[u8]) -> Result<(), FormatError> {
        let additional = proof::message_preflight(
            self.format,
            self.bytes.len(),
            self.messages,
            payload.len(),
            self.limit,
        )?;
        let guard =
            reserve_allocation(self.ledger.as_ref(), additional).map_err(|_| FormatError::Limit)?;
        self.retained.extend(guard);
        self.bytes
            .try_reserve_exact(additional)
            .map_err(|_| FormatError::Allocation)?;
        if self.format == ProofFormat::Native {
            self.bytes
                .extend_from_slice(&proof::message_length(payload.len()));
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
        self.finish_retained().map(|v| v.0)
    }
    pub(super) fn finish_retained(
        self,
    ) -> Result<(Vec<u8>, Vec<crate::vm::LiveReservation>), FormatError> {
        if self.format == ProofFormat::RawBytes && self.messages != 1 {
            return Err(FormatError::Truncated);
        }
        Ok((self.bytes, self.retained))
    }
}

/// Charge cumulative allocation/work and retain live storage until the guard drops.
pub fn reserve_allocation(
    ledger: Option<&ExecutionLedger>,
    bytes: usize,
) -> Result<Option<LiveReservation>, String> {
    let Some(ledger) = ledger else {
        return Ok(None);
    };
    ledger
        .charge(
            WorkBudget {
                instructions: 0,
                iterations: 0,
                logical_bytes: bytes as u64,
            },
            bytes,
        )
        .map_err(|e| e.to_string())?;
    ledger
        .reserve_live(bytes)
        .map(Some)
        .map_err(|e| e.to_string())
}

#[cfg(test)]
mod tests {
    use super::*;
    use zkc_format::proof::ProofReader;

    fn ledger(live_bytes: usize) -> ExecutionLedger {
        ExecutionLedger::new(
            crate::vm::ValueBudget {
                live_bytes,
                total_bytes: 1024,
            },
            WorkBudget {
                instructions: 0,
                iterations: 0,
                logical_bytes: 1024,
            },
        )
    }

    #[test]
    fn writer_header_reservation_keeps_its_original_refusal_order() {
        let ledger = ledger(40);
        assert!(matches!(
            ProofWriter::with_shared_ledger(
                ProofFormat::Native,
                &[0; 32],
                39,
                Some(ledger.clone())
            ),
            Err(FormatError::Limit)
        ));
        // Header work precedes lowered-limit validation, but the failed writer
        // releases its live reservation without refunding cumulative charges.
        let used = ledger.snapshot();
        assert_eq!(
            (
                used.logical_bytes,
                used.total_value_bytes,
                used.live_reserved_bytes
            ),
            (40, 40, 0)
        );
    }

    #[test]
    fn writer_preflight_precedes_ledger_and_failed_live_reservation_precedes_append() {
        let ledger = ledger(40);
        let mut writer = ProofWriter::with_shared_ledger(
            ProofFormat::Native,
            &[0; 32],
            49,
            Some(ledger.clone()),
        )
        .unwrap();
        let before = ledger.snapshot();
        assert_eq!(writer.message(&[0; 2]), Err(FormatError::Limit));
        assert_eq!(ledger.snapshot(), before);
        assert_eq!((writer.messages(), writer.bytes_written()), (0, 40));
        // Size fits, so cumulative work is charged before live capacity refuses.
        assert_eq!(writer.message(&[0]), Err(FormatError::Limit));
        let used = ledger.snapshot();
        assert_eq!(
            (
                used.logical_bytes,
                used.total_value_bytes,
                used.live_reserved_bytes
            ),
            (49, 49, 40)
        );
        assert_eq!((writer.messages(), writer.bytes_written()), (0, 40));
        drop(writer);
        assert_eq!(ledger.snapshot().live_reserved_bytes, 0);
    }

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
