//! Bounded, deployment-owned results of successful public computations.
//!
//! The Runner is the only publisher. Entries retain the admitted executable,
//! execution capacity evidence and backend checkpoints; a caller cannot mint a
//! result by asserting that an ordinary value came from a computation.
use super::{Admitted, Backend, Usage, Value, ValueBudget, WorkBudget, executable::Executable};
use std::{
    collections::BTreeMap,
    sync::{Arc, Mutex},
};

/// Separate retained preparation storage; it grants no execution capacity.
#[derive(Clone, Copy, Debug)]
pub struct PreparationLimits {
    pub entries: usize,
    pub bytes: usize,
}
impl Default for PreparationLimits {
    fn default() -> Self {
        Self {
            entries: 128,
            bytes: 8 << 20,
        }
    }
}
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct PreparationStats {
    pub entries: usize,
    pub bytes: usize,
    pub hits: u64,
}
/// Immutable results shared only by runners of the exact admitted executable.
/// Dropping the last clone releases all retained results. Zero limits disable
/// retention. No cache contents or authority are accepted from artifact text.
pub struct PreparedComputations<B: Backend> {
    pub(super) executable: Arc<Executable>,
    shared: Arc<Mutex<Store<B>>>,
}
impl<B: Backend> Clone for PreparedComputations<B> {
    fn clone(&self) -> Self {
        Self {
            executable: self.executable.clone(),
            shared: self.shared.clone(),
        }
    }
}
impl<B: Backend> std::fmt::Debug for PreparedComputations<B> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("PreparedComputations")
            .field("stats", &self.stats())
            .finish()
    }
}
struct Store<B: Backend> {
    limits: PreparationLimits,
    stats: PreparationStats,
    entries: BTreeMap<Key, (usize, Arc<Evaluation<B>>)>,
}
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) struct Key {
    pub function: String,
    pub parameters: Vec<Vec<u8>>,
}
/// A successful execution under these *initial remaining* allowances proves
/// sufficient capacity for the same computation with dominating allowances.
#[derive(Clone, Copy, Debug)]
pub(super) struct Available {
    pub work: WorkBudget,
    pub values: ValueBudget,
    pub bindings: usize,
}
impl Available {
    pub fn dominates(self, recorded: Self) -> bool {
        self.work.instructions >= recorded.work.instructions
            && self.work.iterations >= recorded.work.iterations
            && self.work.logical_bytes >= recorded.work.logical_bytes
            && self.values.live_bytes >= recorded.values.live_bytes
            && self.values.total_bytes >= recorded.values.total_bytes
            && self.bindings >= recorded.bindings
    }
}
/// Keep cumulative work separate from live storage. Exhaustive destructuring
/// makes a new Usage counter require a decision at this replay boundary.
pub(super) fn cumulative_delta(before: Usage, after: Usage) -> (WorkBudget, usize) {
    let Usage {
        instructions,
        iterations,
        logical_bytes,
        total_value_bytes,
        live_values: _,
        live_value_bytes: _,
    } = after;
    (
        WorkBudget {
            instructions: instructions - before.instructions,
            iterations: iterations - before.iterations,
            logical_bytes: logical_bytes - before.logical_bytes,
        },
        total_value_bytes - before.total_value_bytes,
    )
}
pub(super) struct Evaluation<B: Backend> {
    pub available: Available,
    pub work: WorkBudget,
    pub allocated: usize,
    pub pinned: usize,
    pub frames: u64,
    pub before: B::Checkpoint,
    pub after: B::Checkpoint,
    pub outputs: Vec<B::Value>,
}
impl<B: Backend> PreparedComputations<B> {
    pub fn new(admitted: &Admitted, limits: PreparationLimits) -> Self {
        Self {
            executable: admitted.executable.clone(),
            shared: Arc::new(Mutex::new(Store {
                limits,
                stats: PreparationStats::default(),
                entries: BTreeMap::new(),
            })),
        }
    }
    pub fn stats(&self) -> PreparationStats {
        self.shared.lock().unwrap_or_else(|p| p.into_inner()).stats
    }
    pub(super) fn can_record(&self) -> bool {
        let store = self.shared.lock().unwrap_or_else(|p| p.into_inner());
        store.limits.entries != 0 && store.limits.bytes != 0
    }
    pub(super) fn get(&self, key: &Key) -> Option<Arc<Evaluation<B>>> {
        self.shared
            .lock()
            .unwrap_or_else(|p| p.into_inner())
            .entries
            .get(key)
            .map(|(_, record)| record.clone())
    }
    pub(super) fn hit(&self) {
        let mut store = self.shared.lock().unwrap_or_else(|p| p.into_inner());
        store.stats.hits = store.stats.hits.saturating_add(1);
    }
    pub(super) fn insert(&self, key: Key, evaluation: Evaluation<B>) {
        // Conservative payload plus all owned record/key/container metadata.
        // Checkpoints have fixed, inline size by Backend's checkpoint contract.
        let metadata = 512usize
            .checked_add(std::mem::size_of::<Evaluation<B>>())
            .and_then(|n| n.checked_add(key.function.len()))
            .and_then(|n| {
                n.checked_add(
                    key.parameters
                        .len()
                        .checked_mul(std::mem::size_of::<Vec<u8>>())?,
                )
            })
            .and_then(|n| {
                n.checked_add(
                    evaluation
                        .outputs
                        .len()
                        .checked_mul(std::mem::size_of::<B::Value>())?,
                )
            });
        let bytes = key
            .parameters
            .iter()
            .fold(metadata, |n, p| n?.checked_add(p.len()));
        let bytes = evaluation
            .outputs
            .iter()
            .fold(bytes, |n, v| n?.checked_add(v.retained_bytes()));
        let Some(bytes) = bytes else { return };
        let mut store = self.shared.lock().unwrap_or_else(|p| p.into_inner());
        let previous = store.entries.get(&key).map_or(0, |(bytes, _)| *bytes);
        let retained = store.stats.bytes - previous;
        if (previous == 0 && store.entries.len() >= store.limits.entries)
            || bytes > store.limits.bytes.saturating_sub(retained)
        {
            return;
        }
        // A successful fallback refreshes this parameter's execution context.
        // This avoids permanently pinning the first role/policy/capacity without
        // growing a per-key history or introducing another admission algorithm.
        store.entries.insert(key, (bytes, Arc::new(evaluation)));
        store.stats.bytes = retained + bytes;
        store.stats.entries = store.entries.len();
    }
}
