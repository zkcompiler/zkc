//! Identity-aware retained-value ledger for one Runner.
//!
//! Values report the immutable allocations they retain. The ledger counts each
//! live allocation once, however many bindings, views or containers share it.
//! An allocation's address identifies it only while it is alive; an entry exists
//! only while a live Runner binding holds a strong reference to that allocation,
//! so an address cannot be reused by another allocation while it is recorded.
//! Content is never compared: equal, separately created allocations are distinct.
use super::{PhysicalType, Value};
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

/// One immutable allocation retained by a value, with its conservative charge.
/// The charge includes inline storage held inside the allocation, such as the
/// element slots of a shared collection. Allocations the shared value itself
/// retains are reported separately through [`Value::retained_parts`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Backing {
    address: usize,
    bytes: usize,
}
impl Backing {
    /// Identify the allocation behind `allocation`. Clones of one `Arc` share
    /// an identity; separately created allocations never do while both are
    /// alive, whatever their contents.
    pub fn of<T: ?Sized>(allocation: &Arc<T>, bytes: usize) -> Self {
        Self {
            address: Arc::as_ptr(allocation).cast::<()>().addr(),
            bytes,
        }
    }
    pub fn bytes(&self) -> usize {
        self.bytes
    }
}

/// Charges a retention adds to the live and cumulative ledgers.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(super) struct Charge {
    pub live: usize,
    pub fresh: usize,
}

/// How a binding obtained its value. Only production can create allocations;
/// moving or borrowing an existing value between frames cannot.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Retention {
    /// Arguments, captures, carried values and results crossing frames.
    Transfer,
    /// Entry inputs, received payloads, literals and constructed variants.
    Input,
    /// Kernel and service results. Their newly allocated bytes are also
    /// charged as logical work by the caller.
    Result,
}

struct Entry {
    references: usize,
    /// Physical types under which a bound value with this validation backing
    /// passed backend validation. They disappear with the entry.
    validated: Vec<PhysicalType>,
}

#[derive(Default)]
pub(super) struct Ledger {
    entries: HashMap<Backing, Entry>,
}
impl Ledger {
    /// Charges for retaining `values` without changing the ledger. Shared
    /// allocations already live, or repeated in `values`, add nothing.
    pub fn plan<V: Value>(&self, values: &[V], retention: Retention) -> Option<Charge> {
        let mut planned = HashSet::new();
        // Wide sums cannot overflow; the final conversion refuses oversized totals.
        let (mut shared, mut owned) = (0u128, 0u128);
        for value in values {
            let inline = value.retained_parts(&mut |backing| {
                if self.entries.contains_key(&backing) || !planned.insert(backing) {
                    return false;
                }
                shared += backing.bytes as u128;
                true
            });
            owned += inline as u128;
        }
        let live = usize::try_from(shared + owned).ok()?;
        let fresh = if retention == Retention::Transfer {
            owned as usize
        } else {
            live
        };
        Some(Charge { live, fresh })
    }

    /// Record one binding of each value. The caller has checked `plan`.
    pub fn retain<V: Value>(&mut self, values: &[V]) {
        for value in values {
            value.retained_parts(&mut |backing| {
                if let Some(entry) = self.entries.get_mut(&backing) {
                    entry.references += 1;
                    return false;
                }
                self.entries.insert(
                    backing,
                    Entry {
                        references: 1,
                        validated: Vec::new(),
                    },
                );
                true
            });
            // Every value bound in a Runner environment has passed backend
            // validation at its production site, under this Runner's backend.
            if let Some(backing) = value.validation_backing()
                && let Some(entry) = self.entries.get_mut(&backing)
            {
                let ty = value.physical_type();
                if !entry.validated.contains(&ty) {
                    entry.validated.push(ty);
                }
            }
        }
    }

    /// Drop one binding of each value and return the bytes no longer retained:
    /// shared allocations whose last reference went, plus owned storage.
    pub fn release<'a, V: Value + 'a>(&mut self, values: impl Iterator<Item = &'a V>) -> usize {
        let mut bytes = 0usize;
        for value in values {
            let inline = value.retained_parts(&mut |backing| {
                let Some(entry) = self.entries.get_mut(&backing) else {
                    debug_assert!(false, "released backing was not retained");
                    return false;
                };
                entry.references -= 1;
                if entry.references > 0 {
                    return false;
                }
                self.entries.remove(&backing);
                bytes = bytes.saturating_add(backing.bytes);
                true
            });
            bytes = bytes.saturating_add(inline);
        }
        bytes
    }

    /// Whether an alias of `value` with the same physical type is bound and was
    /// validated by the backend.
    pub fn validated<V: Value>(&self, value: &V, ty: &PhysicalType) -> bool {
        value
            .validation_backing()
            .and_then(|backing| self.entries.get(&backing))
            .is_some_and(|entry| entry.validated.contains(ty))
    }
}
