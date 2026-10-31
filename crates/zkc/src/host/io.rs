//! Reservation-aware native ingress.
#[cfg(feature = "files")]
use crate::io::{ReadError, read_from};
/// Bytes and their outer reservation have one destruction order. The descriptor
/// length bounds a single capture; growth after metadata is refused by the read.
pub(crate) struct SharedBytes {
    pub bytes: Vec<u8>,
    pub retained: Option<zkc_runtime::vm::LiveReservation>,
}
#[cfg(feature = "files")]
pub(crate) fn read_shared(
    file: &mut std::fs::File,
    limit: usize,
    ledger: Option<&zkc_runtime::vm::ExecutionLedger>,
) -> Result<SharedBytes, String> {
    let metadata = file.metadata().map_err(|_| "entry-input-reference")?;
    let length = usize::try_from(metadata.len()).map_err(|_| "artifact-input-work-limit")?;
    if !metadata.is_file() {
        return Err("entry-input-reference".into());
    }
    if length > limit {
        return Err("entry-input-reference-byte-limit".into());
    }
    let bound = length
        .checked_add(1)
        .and_then(|n| n.checked_mul(2))
        .and_then(|n| n.checked_add(512))
        .ok_or("artifact-input-work-limit")?;
    let retained = zkc_runtime::host::wire::reserve_allocation(ledger, bound)?;
    let bytes = read_from(file, length).map_err(|e| match e {
        ReadError::Limit => "entry-input-reference-byte-limit",
        ReadError::Io(_) => "entry-input-reference",
    })?;
    Ok(SharedBytes { bytes, retained })
}
