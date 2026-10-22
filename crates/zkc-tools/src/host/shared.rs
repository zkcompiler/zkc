//! Host allocations outside the VM use the same invocation ledger.
use zkc_runtime::vm::{ExecutionLedger, LiveReservation, WorkBudget};

pub(crate) fn allocation(
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

/// The installed codecs use compressed native frames. Fixed types have exact
/// widths; recursive frames retain at least their compressed payload. Include
/// descriptor/framing slack rather than encoding merely to discover its size.
pub(crate) fn wire_bound(value: &impl zkc_runtime::vm::Value) -> usize {
    zkc_native::native_wire_size(&value.physical_type()).unwrap_or_else(|| {
        value
            .retained_bytes()
            .saturating_mul(4)
            .saturating_add(4096)
    })
}
