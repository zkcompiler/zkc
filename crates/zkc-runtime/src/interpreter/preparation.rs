//! Preparation of the deterministic public prefix, before interaction or
//! private control. This does not infer secrecy from participant role or value.
use super::*;
use crate::vm::instance::Recording;
use crate::vm::preparation::{Evaluation, Key};
use crate::vm::{PreparationStats, PreparedComputations};
use std::collections::BTreeSet;

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
            || self.instance.usage().instructions != 0
            || self.pending.is_some()
            || self.stack.len() != 1
            || !self.instance.owns_preparation(&cache)
        {
            return Err(BackendError::new("computation-preparation-context").into());
        }
        let entry = &self.stack[0];
        let mut public = BTreeSet::new();
        for &index in public_inputs {
            let (name, ty) = entry
                .frame
                .inputs()
                .iter()
                .nth(index)
                .ok_or_else(|| BackendError::new("computation-public-input"))?;
            if !ty.is_serializable() || entry.env[name].validate_serializable().is_err() {
                return Err(BackendError::new("computation-public-input").into());
            }
            public.insert(name.clone());
        }
        if !cache.enabled() {
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
            p.close();
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
            && self.instance.deterministic(code);
        p.open
    }
    pub(super) fn public_results(&mut self, outputs: &[String]) {
        if let Some(p) = &mut self.preparation {
            p.public.extend(outputs.iter().cloned());
        }
    }
    pub(super) fn reuse_computation(&mut self, key: &Key) -> Option<Transfer<B::Value>> {
        self.instance
            .reuse_computation(&self.preparation.as_ref()?.cache, key)
    }
    pub(super) fn begin_computation(&self, key: Key) -> Option<Recording<B>> {
        self.instance
            .begin_computation(&self.preparation.as_ref()?.cache, key)
    }
    pub(super) fn publish_computation(&self, record: Option<(Key, Evaluation<B>)>) {
        if let (Some(p), Some((key, evaluation))) = (&self.preparation, record) {
            p.cache.insert(key, evaluation);
        }
    }
}
