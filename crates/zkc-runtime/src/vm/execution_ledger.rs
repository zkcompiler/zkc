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
    /// Whether the runners that charge this root pool their instruction and
    /// iteration fuel in it. A root that pools no fuel bounds bytes only.
    pools_fuel: bool,
    used: ExecutionLedgerUsage,
    pending_fresh: usize,
    pending_logical: u64,
}
impl State {
    /// Whether `logical` more work, `fresh` more fresh bytes and `live` more
    /// live bytes fit beside the committed and withheld charges.
    fn affords(&self, logical: u64, fresh: usize, live: usize) -> bool {
        let used = &self.used;
        used.logical_bytes
            .checked_add(logical)
            .and_then(|n| n.checked_add(self.pending_logical))
            .is_some_and(|n| n <= self.work.logical_bytes)
            && used
                .total_value_bytes
                .checked_add(fresh)
                .and_then(|n| n.checked_add(self.pending_fresh))
                .is_some_and(|n| n <= self.values.total_bytes)
            && used
                .live_reserved_bytes
                .checked_add(live)
                .is_some_and(|n| n <= self.values.live_bytes)
    }
}

/// Clone this handle into every runner and Host scope of one invocation.
/// Per-instance hard limits still apply. This ledger conveys no value validity,
/// backend custody, capability, setup or execution authority.
///
/// The root bounds the bytes of everything that charges it: Host storage and
/// work, and every runner that shares it, whose logical work, fresh
/// allocation, live retention and withheld output capacity it charges as they
/// occur. Instruction and iteration fuel stays each runner's own unless the
/// root pools it ([`Self::new`]).
#[derive(Clone)]
pub struct ExecutionLedger(Arc<Mutex<State>>);
impl ExecutionLedger {
    /// A root whose runners also pool their instruction and iteration fuel
    /// in it, as a Function's interpreter and children do.
    pub fn new(values: ValueBudget, work: WorkBudget) -> Self {
        Self::with_state(values, work, true)
    }
    /// A root of `values` live and fresh bytes and `logical_bytes` of logical
    /// work that pools no fuel: each runner that shares it keeps its own
    /// instruction and iteration fuel, and a fuel charge to the root refuses.
    pub fn bytes_only(values: ValueBudget, logical_bytes: u64) -> Self {
        Self::with_state(
            values,
            WorkBudget {
                instructions: 0,
                iterations: 0,
                logical_bytes,
            },
            false,
        )
    }
    fn with_state(values: ValueBudget, work: WorkBudget, pools_fuel: bool) -> Self {
        Self(Arc::new(Mutex::new(State {
            values,
            work,
            pools_fuel,
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
    /// Whether runners that share this root pool their fuel in it.
    pub fn pools_fuel(&self) -> bool {
        self.state().pools_fuel
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
    /// Reserve retained Host storage. A runner that shares the root holds its
    /// live retention here as it occurs ([`Self::retain`]); independent
    /// runners conservatively count aliases separately, while one instance's
    /// retention reuses real backing identity.
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
    /// An empty live hold in this root, which a runner's retention grows.
    pub(crate) fn hold(&self) -> LiveReservation {
        LiveReservation {
            ledger: self.clone(),
            bytes: 0,
        }
    }
    /// The live bytes the root can still hold.
    pub(crate) fn live_remaining(&self) -> usize {
        self.remaining().1.live_bytes
    }
    /// The logical work, fresh bytes and live bytes the root can still
    /// afford beside every committed and withheld charge.
    pub(crate) fn remaining(&self) -> (u64, ValueBudget) {
        let state = self.state();
        let used = &state.used;
        (
            state
                .work
                .logical_bytes
                .saturating_sub(used.logical_bytes.saturating_add(state.pending_logical)),
            ValueBudget {
                live_bytes: state
                    .values
                    .live_bytes
                    .saturating_sub(used.live_reserved_bytes),
                total_bytes: state
                    .values
                    .total_bytes
                    .saturating_sub(used.total_value_bytes.saturating_add(state.pending_fresh)),
            },
        )
    }
    /// Whether the root affords `logical` work, `fresh` bytes and `live`
    /// bytes now, beside every committed and withheld charge. This commits
    /// nothing; a later charge checks again.
    pub(crate) fn affords(&self, logical: u64, fresh: usize, live: usize) -> bool {
        self.state().affords(logical, fresh, live)
    }
    /// Whether the pooled meter affords `instructions` and `iterations` more
    /// now. A root that pools no fuel affords none. This commits nothing; a
    /// later charge checks again.
    pub(crate) fn affords_fuel(&self, instructions: u64, iterations: u64) -> bool {
        let state = self.state();
        let used = &state.used;
        used.instructions
            .checked_add(instructions)
            .is_some_and(|n| n <= state.work.instructions)
            && used
                .iterations
                .checked_add(iterations)
                .is_some_and(|n| n <= state.work.iterations)
    }
    /// Charge a runner's retention, all or nothing: `logical` work, `fresh`
    /// bytes, and `live` bytes added to its live hold `held` in this root.
    pub(crate) fn retain(
        &self,
        held: &mut LiveReservation,
        logical: u64,
        fresh: usize,
        live: usize,
    ) -> Result<()> {
        debug_assert!(Arc::ptr_eq(&self.0, &held.ledger.0), "hold of this root");
        let mut state = self.state();
        if !state.affords(logical, fresh, live) {
            return Err(RuntimeError::Limit);
        }
        state.used.logical_bytes += logical;
        state.used.total_value_bytes += fresh;
        state.used.live_reserved_bytes += live;
        held.bytes += live;
        Ok(())
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
    /// Take over `other`'s live bytes, held in the same root, so that this
    /// one guard holds both: nothing is released or charged again.
    ///
    /// # Panics
    ///
    /// When `other` is held in another root.
    pub fn merge(&mut self, mut other: LiveReservation) {
        assert!(
            Arc::ptr_eq(&self.ledger.0, &other.ledger.0),
            "live holds of one root"
        );
        self.bytes += std::mem::take(&mut other.bytes);
    }
    /// Release `bytes` of this hold whose storage is no longer retained.
    pub(crate) fn release(&mut self, bytes: usize) {
        debug_assert!(bytes <= self.bytes, "release within the hold");
        let bytes = bytes.min(self.bytes);
        self.ledger.state().used.live_reserved_bytes -= bytes;
        self.bytes -= bytes;
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
    /// Settle to the admitted output and add its `live` bytes to the runner's
    /// live hold `held`, all or nothing. A refusal settles nothing: dropping
    /// the reservation then commits the whole withheld allowance, as for any
    /// failing call.
    pub(crate) fn settle_held(
        mut self,
        held: &mut LiveReservation,
        fresh: usize,
        logical: u64,
        live: usize,
    ) -> Result<()> {
        debug_assert!(
            Arc::ptr_eq(&self.ledger.0, &held.ledger.0),
            "hold of this root"
        );
        if fresh > self.bytes || logical > self.logical {
            return Err(RuntimeError::Limit);
        }
        {
            let mut state = self.ledger.state();
            if state
                .used
                .live_reserved_bytes
                .checked_add(live)
                .is_none_or(|n| n > state.values.live_bytes)
            {
                // Release the lock before the reservation's drop takes it.
                drop(state);
                return Err(RuntimeError::Limit);
            }
            state.pending_fresh -= self.bytes;
            state.pending_logical -= self.logical;
            state.used.total_value_bytes += fresh;
            state.used.logical_bytes += logical;
            state.used.live_reserved_bytes += live;
        }
        held.bytes += live;
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
    /// Whether a shared root holds these values' live bytes; a runner
    /// without one kept them under its own budget.
    pub fn is_reserved(&self) -> bool {
        self.reservation.is_some()
    }
    /// The values and the live reservation that holds them in the root.
    /// Keep the reservation for as long as the values are retained.
    pub fn into_parts(self) -> (Vec<V>, Option<LiveReservation>) {
        (self.values, self.reservation)
    }
}
impl<V> std::ops::Deref for RetainedOutputs<V> {
    type Target = [V];
    fn deref(&self) -> &[V] {
        &self.values
    }
}
