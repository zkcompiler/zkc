//! Accounting for replay of successful public computations. Public provenance
//! is supplied by the evaluator; the instance checks capacity and backend work.
use super::*;
use crate::vm::code::{LocalCode, Operation};
use crate::vm::preparation::{Available, Evaluation, Key, cumulative_delta};
use std::collections::HashSet;

/// A VM-owned snapshot of the capacity and work before a cacheable body. The
/// evaluator decides public eligibility but cannot assemble accounting evidence.
#[must_use = "finish a successful recording or discard it on failure"]
pub(crate) struct Recording<B: Backend> {
    key: Key,
    available: Available,
    usage: Usage,
    /// The root's committed logical work and fresh bytes before the body.
    charged: Option<(u64, usize)>,
    frames: u64,
    before: B::Checkpoint,
}

fn shared_bytes<V: Value>(values: &[V], retained: crate::vm::Retained<'_>) -> Option<usize> {
    let mut seen = HashSet::new();
    let mut total = Some(0usize);
    for value in values {
        value.retained_parts(&mut |backing| {
            if retained.contains(backing) {
                total = None;
                return false;
            }
            if seen.insert(backing) {
                total = total.and_then(|n| n.checked_add(backing.bytes()));
                true
            } else {
                false
            }
        });
    }
    total
}
impl<B: Backend> Instance<B> {
    /// Reuse replays a computation's charges into this runner and its root.
    /// A root that pools fuel across runners admits none.
    pub(crate) fn owns_preparation(&self, cache: &PreparedComputations<B>) -> bool {
        !self.pooled_fuel && Arc::ptr_eq(&cache.executable, &self.admitted.executable)
    }
    /// The root's committed logical work and fresh bytes, if there is one.
    fn root_charged(&self) -> Option<(u64, usize)> {
        self.shared.as_ref().map(|root| {
            let used = root.snapshot();
            (used.logical_bytes, used.total_value_bytes)
        })
    }
    pub(crate) fn deterministic(&self, code: &LocalCode) -> bool {
        code.instructions.iter().all(|op| match op {
            Operation::Op { call, .. } => self.operations[call.binding.index]
                .as_ref()
                .expect("installed root binding")
                .deterministic(),
            Operation::Conditional {
                then_body,
                else_body,
                ..
            } => self.deterministic(then_body) && self.deterministic(else_body),
            Operation::For { body, .. } => self.deterministic(body),
            Operation::Match { arms, .. } => arms.iter().all(|arm| self.deterministic(&arm.body)),
            Operation::BoolConstant { .. }
            | Operation::Variant { .. }
            | Operation::Stop { .. }
            | Operation::Yield(_)
            | Operation::Release(_)
            | Operation::Return(_) => true,
        })
    }

    /// What remains of the runner's own budgets and, for its bytes, of the
    /// root's allowances.
    fn available(&self) -> Available {
        let mut available = Available {
            work: WorkBudget {
                instructions: self.work_budget.instructions - self.usage.instructions,
                iterations: self.work_budget.iterations - self.usage.iterations,
                logical_bytes: self.work_budget.logical_bytes - self.usage.logical_bytes,
            },
            values: ValueBudget {
                live_bytes: self.value_budget.live_bytes - self.usage.live_value_bytes,
                total_bytes: self.value_budget.total_bytes - self.usage.total_value_bytes,
            },
            bindings: Limits::LIVE_VALUES - self.usage.live_values,
        };
        if let Some(root) = &self.shared {
            let (logical, values) = root.remaining();
            available.work.logical_bytes = available.work.logical_bytes.min(logical);
            available.values.live_bytes = available.values.live_bytes.min(values.live_bytes);
            available.values.total_bytes = available.values.total_bytes.min(values.total_bytes);
        }
        available
    }
    /// Replay a recorded computation. `transfer` is the capacity withheld for
    /// the frame inputs' transfer, which the recorded charges include: a
    /// replay that reaches the root releases it uncommitted first.
    pub(crate) fn reuse_computation(
        &mut self,
        cache: &PreparedComputations<B>,
        key: &Key,
        transfer: &mut Option<crate::vm::execution_ledger::AllocationReservation>,
    ) -> Option<Transfer<B::Value>> {
        debug_assert!(self.owns_preparation(cache));
        let evaluation = cache.get(key)?;
        if !self.available().dominates(evaluation.available) {
            return None;
        }
        let frames = self.next_frame.checked_add(evaluation.frames)?;
        let bytes = shared_bytes(&evaluation.outputs, self.ledger.view())?;
        if bytes != evaluation.pinned {
            return None;
        }
        for value in &evaluation.outputs {
            // Types were checked when this exact executable produced the
            // record. Revalidate the immutable payload under the current backend.
            self.counts.event(Event::BackendValidate);
            if self.backend.validate_value(value).is_err() {
                return None;
            }
        }
        // The replay charges the root what the computation charged it, all
        // or nothing, before the backend advances: the room it dominates
        // admits it.
        if let Some(root) = &self.shared {
            if let Some(withheld) = transfer.take() {
                // Settling nothing never exceeds what was withheld.
                let _ = withheld.settle(0, 0);
            }
            let held = self.live_reservation.get_or_insert_with(|| root.hold());
            let (logical, fresh) = evaluation.charged;
            root.retain(held, logical, fresh, bytes).ok()?;
        }
        if !self
            .backend
            .replay_computation(evaluation.before, evaluation.after)
        {
            // The replayed outputs are not retained; their live bytes go back.
            // The committed work stays, as a failed call's does.
            if let Some(held) = self.shared.as_ref().and(self.live_reservation.as_mut()) {
                held.release(bytes);
            }
            return None;
        }
        self.counts.add(Event::Replay, evaluation.work.instructions);
        self.counts.event(Event::Reuse);
        self.usage.instructions += evaluation.work.instructions;
        self.usage.iterations += evaluation.work.iterations;
        self.usage.logical_bytes += evaluation.work.logical_bytes;
        self.usage.total_value_bytes += evaluation.allocated;
        self.next_frame = frames;
        // Exactly the normal return handoff: shared backing is pinned; scalar
        // bindings and live value count are installed by the caller, not here.
        self.counts
            .add(Event::Retain, evaluation.outputs.len() as u64);
        self.ledger.retain(&evaluation.outputs);
        self.usage.live_value_bytes += bytes;
        cache.hit();
        Some(Transfer::new(evaluation.outputs.clone()))
    }
    pub(crate) fn record_computation(
        &self,
        recording: Recording<B>,
        values: &Transfer<B::Value>,
    ) -> Option<(Key, Evaluation<B>)> {
        let Recording {
            key,
            available,
            usage,
            charged,
            frames,
            before,
        } = recording;
        if values
            .iter()
            .any(|v| !v.preparation_output() || self.validate_backend(v).is_err())
        {
            return None;
        }
        let pinned = shared_bytes(values, crate::vm::Retained::NONE)?;
        // A record may not borrow allocations from the outer environment. With
        // inline arguments, new returned backing is exactly this live delta.
        if self
            .usage
            .live_value_bytes
            .checked_sub(usage.live_value_bytes)?
            != pinned
            || self.usage.live_values != usage.live_values
        {
            return None;
        }
        let (work, allocated) = cumulative_delta(usage, self.usage);
        let charged = match (charged, self.root_charged()) {
            (Some(before), Some(after)) => (after.0 - before.0, after.1 - before.1),
            _ => (work.logical_bytes, allocated),
        };
        Some((
            key,
            Evaluation {
                available,
                work,
                allocated,
                charged,
                pinned,
                frames: self.next_frame - frames,
                before,
                after: self.backend.computation_checkpoint()?,
                outputs: values.to_vec(),
            },
        ))
    }
    pub(crate) fn begin_computation(
        &self,
        cache: &PreparedComputations<B>,
        key: Key,
    ) -> Option<Recording<B>> {
        debug_assert!(self.owns_preparation(cache));
        if !cache.can_record(&key) {
            return None;
        }
        Some(Recording {
            key,
            available: self.available(),
            usage: self.usage,
            charged: self.root_charged(),
            frames: self.next_frame,
            before: self.backend.computation_checkpoint()?,
        })
    }
}
