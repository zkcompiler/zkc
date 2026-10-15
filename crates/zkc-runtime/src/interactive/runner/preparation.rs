//! Preparation of the deterministic public prefix, before interaction or
//! private control. This does not infer secrecy from participant role or value.
use super::*;
use crate::interactive::preparation::{Available, Evaluation, Key, cumulative_delta};
use crate::interactive::{PreparationStats, PreparedComputations};
use std::collections::{BTreeSet, HashSet};

pub(super) struct Preparation<B: Backend> {
    cache: PreparedComputations<B>,
    public: BTreeSet<String>,
    open: bool,
}
impl<B: Backend> Preparation<B> {
    pub(super) fn close(&mut self) {
        self.open = false;
    }
}
fn deterministic<K: InstalledKernel>(code: &LocalCode, kernels: &[K]) -> bool {
    code.instructions.iter().all(|op| match op {
        Operation::Op { binding, .. } => kernels[binding.index].deterministic(),
        Operation::Conditional {
            then_body,
            else_body,
            ..
        } => deterministic(then_body, kernels) && deterministic(else_body, kernels),
        Operation::For { body, .. } => deterministic(body, kernels),
        Operation::Match { arms, .. } => arms.iter().all(|arm| deterministic(&arm.body, kernels)),
        Operation::BoolConstant { .. }
        | Operation::Variant { .. }
        | Operation::Stop { .. }
        | Operation::Yield(_)
        | Operation::Release(_)
        | Operation::Return(_) => true,
    })
}
fn shared_bytes<V: Value>(values: &[V], retained: super::super::Retained<'_>) -> Option<usize> {
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
impl<B: Backend> Runner<B> {
    /// Enable bounded computation reuse before polling this Runner. The Host
    /// authorizes the specified entry slots as public across invocations. The
    /// runtime checks slots/types, not that application-level authorization.
    /// Receives, services, participant control and private local computations
    /// end this preparation prefix. Only installed deterministic code propagates
    /// public provenance; key equality never does.
    pub fn prepare_computations(
        &mut self,
        cache: PreparedComputations<B>,
        public_inputs: &[usize],
    ) -> Result<()> {
        if !self.is_at_entry()
            || self.usage.instructions != 0
            || self.pending.is_some()
            || self.stack.len() != 1
            || !Arc::ptr_eq(&cache.executable, &self.admitted.executable)
        {
            return Err(BackendError::new("computation-preparation-context").into());
        }
        let entry = &self.stack[0];
        let mut public = BTreeSet::new();
        for &index in public_inputs {
            let (name, ty) = entry
                .frame
                .inputs
                .iter()
                .nth(index)
                .ok_or_else(|| BackendError::new("computation-public-input"))?;
            if !ty.is_serializable() || entry.env[name].validate_serializable().is_err() {
                return Err(BackendError::new("computation-public-input").into());
            }
            public.insert(name.clone());
        }
        if !cache.can_record() {
            self.preparation = None;
            return Ok(());
        }
        self.preparation = Some(Preparation {
            cache,
            public,
            open: true,
        });
        Ok(())
    }
    pub fn preparation_stats(&self) -> Option<PreparationStats> {
        self.preparation.as_ref().map(|p| p.cache.stats())
    }
    pub(super) fn close_preparation(&mut self) {
        if let Some(p) = &mut self.preparation {
            p.open = false;
        }
    }
    pub(super) fn public_computation(&mut self, code: &LocalCode, inputs: &[String]) -> bool {
        let Some(p) = &mut self.preparation else {
            return false;
        };
        // Classify only reached public code; unrelated participants and unused
        // library bodies need no inspection.
        p.open = p.open
            && self.stack.len() == 1
            && inputs.iter().all(|n| p.public.contains(n))
            && deterministic(code, &self.kernels);
        p.open
    }
    pub(super) fn public_results(&mut self, outputs: &[String]) {
        if let Some(p) = &mut self.preparation {
            p.public.extend(outputs.iter().cloned());
        }
    }
    pub(super) fn computation_key(function: &str, args: &[B::Value]) -> Option<Key> {
        if args.len() > 16 {
            return None;
        }
        let parameters: Vec<_> = args
            .iter()
            .map(Value::preparation_parameter)
            .collect::<Option<_>>()?;
        if parameters.iter().map(Vec::len).sum::<usize>() > 512 {
            return None;
        }
        Some(Key {
            function: function.into(),
            parameters,
        })
    }
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
    pub(super) fn reuse_computation(&mut self, key: &Key) -> Option<Vec<B::Value>> {
        let cache = self.preparation.as_ref()?.cache.clone();
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
        self.usage.instructions += evaluation.work.instructions;
        self.usage.iterations += evaluation.work.iterations;
        self.usage.logical_bytes += evaluation.work.logical_bytes;
        self.usage.total_value_bytes += evaluation.allocated;
        self.next_frame = frames;
        // Exactly the normal return handoff: shared backing is pinned; scalar
        // bindings and live value count are installed by the caller, not here.
        self.ledger.retain(&evaluation.outputs);
        self.usage.live_value_bytes += bytes;
        cache.hit();
        Some(evaluation.outputs.clone())
    }
    pub(super) fn record_computation(
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
        let pinned = shared_bytes(values, super::super::Retained::NONE)?;
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
    pub(super) fn begin_computation(&self) -> Option<(Available, Usage, u64, B::Checkpoint)> {
        Some((
            self.available(),
            self.usage,
            self.next_frame,
            self.backend.computation_checkpoint()?,
        ))
    }
    pub(super) fn publish_computation(&self, record: Option<(Key, Evaluation<B>)>) {
        if let (Some(p), Some((key, evaluation))) = (&self.preparation, record) {
            p.cache.insert(key, evaluation);
        }
    }
}
