//! Bounded, deployment-owned results of successful public computations.
//!
//! The Runner is the only publisher. Entries retain the admitted executable,
//! execution capacity evidence and backend checkpoints; a caller cannot mint a
//! result by asserting that an ordinary value came from a computation.
use super::{Backend, Program, Usage, Value, ValueBudget, WorkBudget, code::Executable};
use std::{
    collections::BTreeMap,
    sync::{Arc, Mutex},
};

// Include a sparsely occupied map node and the record's Arc header. Charging
// only the occupied key/value slot would miss the node's reserved storage.
const RECORD_OVERHEAD: usize = 1024;
const MAX_PARAMETERS: usize = 16;
const MAX_PARAMETER_BYTES: usize = 512;

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
    limits: PreparationLimits,
    shared: Arc<Mutex<Store<B>>>,
}
impl<B: Backend> Clone for PreparedComputations<B> {
    fn clone(&self) -> Self {
        Self {
            executable: self.executable.clone(),
            limits: self.limits,
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
    bytes: usize,
    hits: u64,
    entries: BTreeMap<Key, (usize, Arc<Evaluation<B>>)>,
}
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct Key {
    function: String,
    parameters: Vec<Vec<u8>>,
}
impl Key {
    pub(crate) fn new<V: Value>(function: &str, args: &[V]) -> Option<Key> {
        if args.len() > MAX_PARAMETERS {
            return None;
        }
        let parameters: Vec<_> = args
            .iter()
            .map(Value::preparation_parameter)
            .collect::<Option<_>>()?;
        if parameters.iter().map(Vec::len).sum::<usize>() > MAX_PARAMETER_BYTES {
            return None;
        }
        Some(Self {
            function: function.into(),
            parameters,
        })
    }

    fn retained_bytes(&self) -> Option<usize> {
        let bytes = self.function.capacity().checked_add(
            self.parameters
                .capacity()
                .checked_mul(std::mem::size_of::<Vec<u8>>())?,
        );
        self.parameters
            .iter()
            .fold(bytes, |n, p| n?.checked_add(p.capacity()))
    }
}
/// A successful execution under these *initial remaining* allowances proves
/// sufficient capacity for the same computation with dominating allowances.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Available {
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
pub(crate) fn cumulative_delta(before: Usage, after: Usage) -> (WorkBudget, usize) {
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
pub(crate) struct Evaluation<B: Backend> {
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
    pub fn new(admitted: &Program, limits: PreparationLimits) -> Self {
        Self {
            executable: admitted.executable.clone(),
            limits,
            shared: Arc::new(Mutex::new(Store {
                bytes: 0,
                hits: 0,
                entries: BTreeMap::new(),
            })),
        }
    }
    pub fn stats(&self) -> PreparationStats {
        let store = self.shared.lock().unwrap_or_else(|p| p.into_inner());
        PreparationStats {
            entries: store.entries.len(),
            bytes: store.bytes,
            hits: store.hits,
        }
    }
    pub(crate) fn enabled(&self) -> bool {
        self.limits.entries != 0 && self.limits.bytes != 0
    }
    fn metadata_bytes(key: &Key) -> Option<usize> {
        // Conservative fixed record and BTreeMap node overhead, plus owned keys.
        RECORD_OVERHEAD
            .checked_add(std::mem::size_of::<Evaluation<B>>())?
            .checked_add(key.retained_bytes()?)
    }
    pub(crate) fn can_record(&self, key: &Key) -> bool {
        let store = self.shared.lock().unwrap_or_else(|p| p.into_inner());
        let previous = store.entries.get(key);
        let retained = store.bytes - previous.map_or(0, |(bytes, _)| *bytes);
        (previous.is_some() || store.entries.len() < self.limits.entries)
            && Self::metadata_bytes(key)
                .is_some_and(|bytes| bytes <= self.limits.bytes.saturating_sub(retained))
    }
    pub(crate) fn get(&self, key: &Key) -> Option<Arc<Evaluation<B>>> {
        self.shared
            .lock()
            .unwrap_or_else(|p| p.into_inner())
            .entries
            .get(key)
            .map(|(_, record)| record.clone())
    }
    pub(crate) fn hit(&self) {
        let mut store = self.shared.lock().unwrap_or_else(|p| p.into_inner());
        store.hits = store.hits.saturating_add(1);
    }
    pub(crate) fn insert(&self, key: Key, evaluation: Evaluation<B>) {
        // Conservative payload plus all owned record/key/container metadata.
        // Checkpoints have fixed, inline size by Backend's checkpoint contract.
        let bytes = Self::metadata_bytes(&key).and_then(|n| {
            n.checked_add(
                evaluation
                    .outputs
                    .capacity()
                    .checked_mul(std::mem::size_of::<B::Value>())?,
            )
        });
        let bytes = evaluation
            .outputs
            .iter()
            .fold(bytes, |n, v| n?.checked_add(v.retained_bytes()));
        let Some(bytes) = bytes else { return };
        let mut store = self.shared.lock().unwrap_or_else(|p| p.into_inner());
        let previous = store.entries.get(&key);
        let retained = store.bytes - previous.map_or(0, |(bytes, _)| *bytes);
        // Repeat the bounded publication check: another Runner may have filled
        // the store since the recording preflight.
        if (previous.is_none() && store.entries.len() >= self.limits.entries)
            || bytes > self.limits.bytes.saturating_sub(retained)
        {
            return;
        }
        // A successful fallback refreshes this parameter's execution context.
        // This avoids permanently pinning the first role/policy/capacity without
        // growing a per-key history or introducing another admission algorithm.
        let replaced = store.entries.insert(key, (bytes, Arc::new(evaluation)));
        store.bytes = retained + bytes;
        drop(store);
        // Releasing a large result must not hold up other invocations.
        drop(replaced);
    }
}
