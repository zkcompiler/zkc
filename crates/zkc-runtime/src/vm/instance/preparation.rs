//! Accounting for replay of successful public computations. Public provenance
//! is supplied by the evaluator; the instance checks capacity and backend work.
use super::*;
use crate::vm::preparation::{Available, Evaluation, Key, cumulative_delta};
use std::collections::HashSet;

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
    fn available(&self) -> Available {
        Available {
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
        }
    }
    pub(crate) fn reuse_computation(
        &mut self,
        cache: &PreparedComputations<B>,
        key: &Key,
    ) -> Option<Vec<B::Value>> {
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
        if !self
            .backend
            .replay_computation(evaluation.before, evaluation.after)
        {
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
        Some(evaluation.outputs.clone())
    }
    pub(crate) fn record_computation(
        &self,
        key: Key,
        available: Available,
        usage: Usage,
        frames: u64,
        before: B::Checkpoint,
        values: &[B::Value],
    ) -> Option<(Key, Evaluation<B>)> {
        if values
            .iter()
            .any(|v| !v.preparation_output() || v.validate_serializable().is_err())
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
        Some((
            key,
            Evaluation {
                available,
                work,
                allocated,
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
        key: &Key,
    ) -> Option<(Available, Usage, u64, B::Checkpoint)> {
        if !cache.can_record(key) {
            return None;
        }
        Some((
            self.available(),
            self.usage,
            self.next_frame,
            self.backend.computation_checkpoint()?,
        ))
    }
}
