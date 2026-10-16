//! Optional execution observations, separate from protocol resource charges.
//! Disabled builds have no counter storage, allocation or collection work.
use super::code::Operation;

macro_rules! events {
    ($($variant:ident => $name:literal),* $(,)?) => {
        #[derive(Clone, Copy)]
        pub(crate) enum Event { $($variant),* }
        impl Event {
            #[cfg(feature = "execution-counts")]
            const ALL: &[Self] = &[$(Self::$variant),*];
            #[cfg(feature = "execution-counts")]
            const fn name(self) -> &'static str {
                match self { $(Self::$variant => $name),* }
            }
        }
    };
}
events! {
    Tick => "charged_instructions",
    Replay => "replayed_instructions",
    Frame => "created_frames",
    Enter => "backend_enter_calls",
    Leave => "backend_leave_calls",
    Validate => "value_validation_calls",
    BackendValidate => "backend_validation_calls",
    Plan => "retention_plan_calls",
    PlanValue => "retention_planned_values",
    Retain => "retention_commit_values",
    Release => "retention_release_values",
    Unpin => "retention_unpin_values",
    Reuse => "computation_reuse_hits",
    Operand => "native_operand_values",
    Bool => "local_bool",
    Variant => "local_variant",
    Match => "local_match",
    Stop => "local_stop",
    Conditional => "local_conditional",
    For => "local_for",
    Yield => "local_yield",
    StorageRelease => "local_release",
    Op => "local_op",
    Return => "local_return",
}

/// A host-side observation. Default builds keep this type zero-sized.
/// Counts never authorize execution or replace the resource ledger.
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct ExecutionCounts {
    #[cfg(feature = "execution-counts")]
    events: std::collections::BTreeMap<&'static str, u64>,
    #[cfg(feature = "execution-counts")]
    operations: std::collections::BTreeMap<String, u64>,
}
impl ExecutionCounts {
    /// Reflects the runtime's resolved Cargo features, including unification.
    pub const ENABLED: bool = cfg!(feature = "execution-counts");

    /// Combine participant or attempt observations without retaining values.
    pub fn merge(&mut self, other: &Self) {
        #[cfg(feature = "execution-counts")]
        {
            for (&key, &value) in &other.events {
                let count = self.events.entry(key).or_default();
                *count = count.saturating_add(value);
            }
            for (key, &value) in &other.operations {
                let count = self.operations.entry(key.clone()).or_default();
                *count = count.saturating_add(value);
            }
        }
        #[cfg(not(feature = "execution-counts"))]
        let _ = other;
    }

    /// Materialize only outside measured execution. Labels are operation
    /// contracts and fixed event names, without operands or source names.
    /// Counts can reveal reached control flow.
    pub fn json(&self) -> Option<serde_json::Value> {
        #[cfg(feature = "execution-counts")]
        return Some(serde_json::json!({"events": self.events, "operations": self.operations}));
        #[cfg(not(feature = "execution-counts"))]
        None
    }
}

pub(crate) struct Counts {
    #[cfg(feature = "execution-counts")]
    events: [std::cell::Cell<u64>; Event::ALL.len()],
    #[cfg(feature = "execution-counts")]
    operations: Vec<std::cell::Cell<u64>>,
}
impl Counts {
    pub fn new(bindings: usize) -> Self {
        #[cfg(not(feature = "execution-counts"))]
        let _ = bindings;
        Self {
            #[cfg(feature = "execution-counts")]
            events: std::array::from_fn(|_| std::cell::Cell::new(0)),
            #[cfg(feature = "execution-counts")]
            operations: (0..bindings).map(|_| std::cell::Cell::new(0)).collect(),
        }
    }

    #[inline(always)]
    pub fn add(&self, event: Event, value: u64) {
        #[cfg(feature = "execution-counts")]
        {
            let count = &self.events[event as usize];
            count.set(count.get().saturating_add(value));
        }
        #[cfg(not(feature = "execution-counts"))]
        let _ = (event, value);
    }
    #[inline(always)]
    pub fn event(&self, event: Event) {
        self.add(event, 1);
    }

    #[inline(always)]
    pub fn operation(&self, binding: usize) {
        #[cfg(feature = "execution-counts")]
        {
            let count = &self.operations[binding];
            count.set(count.get().saturating_add(1));
        }
        #[cfg(not(feature = "execution-counts"))]
        let _ = binding;
    }

    #[inline(always)]
    pub fn instruction(&self, op: &Operation) {
        self.event(match op {
            Operation::BoolConstant { .. } => Event::Bool,
            Operation::Variant { .. } => Event::Variant,
            Operation::Match { .. } => Event::Match,
            Operation::Stop { .. } => Event::Stop,
            Operation::Conditional { .. } => Event::Conditional,
            Operation::For { .. } => Event::For,
            Operation::Yield(_) => Event::Yield,
            Operation::Release(_) => Event::StorageRelease,
            Operation::Op { .. } => Event::Op,
            Operation::Return(_) => Event::Return,
        });
    }

    pub fn snapshot(&self, bindings: &[std::sync::Arc<super::ResolvedBinding>]) -> ExecutionCounts {
        #[cfg(feature = "execution-counts")]
        {
            let mut result = ExecutionCounts {
                events: Event::ALL
                    .iter()
                    .map(|&e| (e.name(), self.events[e as usize].get()))
                    .collect(),
                ..ExecutionCounts::default()
            };
            for (binding, count) in bindings.iter().zip(&self.operations) {
                if count.get() != 0 {
                    let entry = result
                        .operations
                        .entry(binding.declaration().contract.clone())
                        .or_default();
                    *entry = entry.saturating_add(count.get());
                }
            }
            result
        }
        #[cfg(not(feature = "execution-counts"))]
        {
            let _ = bindings;
            ExecutionCounts::default()
        }
    }
}
