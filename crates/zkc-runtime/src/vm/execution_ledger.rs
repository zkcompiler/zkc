//! Invocation-wide policy, separate from instance/backend validation evidence.
use super::{RuntimeError, ValueBudget, WorkBudget};
use std::sync::{Arc, Mutex, MutexGuard};

type Result<T> = std::result::Result<T, RuntimeError>;

/// Cumulative committed work and conservative live payload reservations.
/// These counters describe retained payload policy, never allocator or peak RSS.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct ExecutionLedgerUsage {
    pub instructions: u64,
    pub iterations: u64,
    pub logical_bytes: u64,
    pub total_value_bytes: usize,
    pub live_reserved_bytes: usize,
    /// Capacity withheld before allocating hooks, not yet committed work.
    pub pending_value_bytes: usize,
    pub pending_logical_bytes: u64,
}

struct State {
    values: ValueBudget,
    work: WorkBudget,
    used: ExecutionLedgerUsage,
    pending_fresh: usize,
    pending_logical: u64,
}

/// Clone this handle into every runner and Host scope of one invocation.
/// Per-instance hard limits still apply. This ledger conveys no value validity,
/// backend custody, capability, setup or execution authority.
#[derive(Clone)]
pub struct ExecutionLedger(Arc<Mutex<State>>);
impl ExecutionLedger {
    pub fn new(values: ValueBudget, work: WorkBudget) -> Self {
        Self(Arc::new(Mutex::new(State {
            values,
            work,
            used: ExecutionLedgerUsage::default(),
            pending_fresh: 0,
            pending_logical: 0,
        })))
    }
    fn state(&self) -> MutexGuard<'_, State> {
        // No backend/user hook runs under this mutex. A panic during arithmetic
        // cannot authorize extra capacity; recover the existing counters.
        self.0.lock().unwrap_or_else(|poison| poison.into_inner())
    }
    pub fn snapshot(&self) -> ExecutionLedgerUsage {
        let state = self.state();
        let mut used = state.used;
        used.pending_value_bytes = state.pending_fresh;
        used.pending_logical_bytes = state.pending_logical;
        used
    }
    /// Charge Host control or known storage before its effect. Committed work
    /// and fresh bytes are never refunded, including after failure or unwind.
    pub fn charge(&self, work: WorkBudget, fresh: usize) -> Result<()> {
        let mut state = self.state();
        let used = &state.used;
        let instructions = used
            .instructions
            .checked_add(work.instructions)
            .filter(|n| *n <= state.work.instructions)
            .ok_or(RuntimeError::Limit)?;
        let iterations = used
            .iterations
            .checked_add(work.iterations)
            .filter(|n| *n <= state.work.iterations)
            .ok_or(RuntimeError::Limit)?;
        let logical = used
            .logical_bytes
            .checked_add(work.logical_bytes)
            .filter(|n| {
                n.checked_add(state.pending_logical)
                    .is_some_and(|n| n <= state.work.logical_bytes)
            })
            .ok_or(RuntimeError::Limit)?;
        let fresh = used
            .total_value_bytes
            .checked_add(fresh)
            .filter(|n| {
                n.checked_add(state.pending_fresh)
                    .is_some_and(|n| n <= state.values.total_bytes)
            })
            .ok_or(RuntimeError::Limit)?;
        state.used.instructions = instructions;
        state.used.iterations = iterations;
        state.used.logical_bytes = logical;
        state.used.total_value_bytes = fresh;
        Ok(())
    }
    /// Reserve retained Host storage, or a runner's entire live allowance.
    /// Independent runners conservatively count aliases separately. Instance
    /// retention still reuses real backing identity within its own allowance.
    pub fn reserve_live(&self, bytes: usize) -> Result<LiveReservation> {
        let mut state = self.state();
        state.used.live_reserved_bytes = state
            .used
            .live_reserved_bytes
            .checked_add(bytes)
            .filter(|n| *n <= state.values.live_bytes)
            .ok_or(RuntimeError::Limit)?;
        Ok(LiveReservation {
            ledger: self.clone(),
            bytes,
        })
    }
    /// Atomically withhold capacity before an allocating backend hook. A
    /// successful hook settles to its actual admitted fresh output. A failing
    /// hook conservatively consumes the full allowance: partial allocation is
    /// not observable and committed work must not be rolled back.
    pub(crate) fn reserve_output(&self, maximum: usize, logical: bool) -> AllocationReservation {
        let mut state = self.state();
        let fresh = state.values.total_bytes - state.used.total_value_bytes - state.pending_fresh;
        let work = state.work.logical_bytes - state.used.logical_bytes - state.pending_logical;
        let bytes = maximum.min(fresh).min(if logical {
            usize::try_from(work).unwrap_or(usize::MAX)
        } else {
            usize::MAX
        });
        state.pending_fresh += bytes;
        let logical = if logical { bytes as u64 } else { 0 };
        state.pending_logical += logical;
        AllocationReservation {
            ledger: self.clone(),
            bytes,
            logical,
            settled: false,
        }
    }
}

/// Live policy ownership. Move this guard with retained Host values; dropping
/// it releases only live allowance, never cumulative work or fresh charges.
#[must_use = "keep the live reservation while retaining its payload"]
pub struct LiveReservation {
    ledger: ExecutionLedger,
    bytes: usize,
}
impl LiveReservation {
    pub fn bytes(&self) -> usize {
        self.bytes
    }
}
impl Drop for LiveReservation {
    fn drop(&mut self) {
        self.ledger.state().used.live_reserved_bytes -= self.bytes;
    }
}

pub(crate) struct AllocationReservation {
    ledger: ExecutionLedger,
    bytes: usize,
    logical: u64,
    settled: bool,
}
impl AllocationReservation {
    pub fn bytes(&self) -> usize {
        self.bytes
    }
    pub fn settle(mut self, fresh: usize, logical: u64) -> Result<()> {
        if fresh > self.bytes || logical > self.logical {
            return Err(RuntimeError::Limit);
        }
        let mut state = self.ledger.state();
        state.pending_fresh -= self.bytes;
        state.pending_logical -= self.logical;
        state.used.total_value_bytes += fresh;
        state.used.logical_bytes += logical;
        self.settled = true;
        Ok(())
    }
}
impl Drop for AllocationReservation {
    fn drop(&mut self) {
        if !self.settled {
            let mut state = self.ledger.state();
            state.pending_fresh -= self.bytes;
            state.pending_logical -= self.logical;
            state.used.total_value_bytes += self.bytes;
            state.used.logical_bytes += self.logical;
        }
    }
}

/// Terminal values with their invocation-wide live reservation.
/// Keep this guard while a parent Host retains the result across child calls.
/// Values still require independent validation by any receiving backend.
#[must_use = "keep the output guard while retaining its values"]
pub struct RetainedOutputs<V> {
    pub(crate) values: Vec<V>,
    pub(crate) reservation: Option<LiveReservation>,
}
impl<V> RetainedOutputs<V> {
    pub fn reservation_bytes(&self) -> usize {
        self.reservation.as_ref().map_or(0, LiveReservation::bytes)
    }
}
impl<V> std::ops::Deref for RetainedOutputs<V> {
    type Target = [V];
    fn deref(&self) -> &[V] {
        &self.values
    }
}
