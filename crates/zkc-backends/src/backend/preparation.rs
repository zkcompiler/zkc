//! Fixed native policy and cumulative work evidence for pure computations.
use super::NativeBackend;
use crate::Policy;

#[derive(Clone, Copy, Debug)]
pub struct ComputationCheckpoint {
    policy: Policy,
    external: Meter,
    sequence: Meter,
    ring: Meter,
}
#[derive(Clone, Copy, Debug)]
struct Meter {
    limit: u64,
    spent: u64,
}
impl Meter {
    fn replay(self, before: Self, after: Self) -> Option<u64> {
        if self.limit.checked_sub(self.spent)? < before.limit.checked_sub(before.spent)? {
            return None;
        }
        self.spent
            .checked_add(after.spent.checked_sub(before.spent)?)
            .filter(|next| *next <= self.limit)
    }
}
impl NativeBackend {
    pub(super) fn checkpoint(&self) -> ComputationCheckpoint {
        ComputationCheckpoint {
            policy: self.core.policy,
            external: Meter {
                limit: self.external_work.limit,
                spent: self.external_work.spent,
            },
            sequence: Meter {
                limit: self.sequence_work.limit,
                spent: self.sequence_work.spent,
            },
            ring: Meter {
                limit: self.ring_work.limit,
                spent: self.ring_work.spent,
            },
        }
    }
    pub(super) fn replay(
        &mut self,
        before: ComputationCheckpoint,
        after: ComputationCheckpoint,
    ) -> bool {
        let current = self.checkpoint();
        if current.policy != before.policy || after.policy != before.policy {
            return false;
        }
        let Some(external) = current.external.replay(before.external, after.external) else {
            return false;
        };
        let Some(sequence) = current.sequence.replay(before.sequence, after.sequence) else {
            return false;
        };
        let Some(ring) = current.ring.replay(before.ring, after.ring) else {
            return false;
        };
        self.external_work.spent = external;
        self.sequence_work.spent = sequence;
        self.ring_work.spent = ring;
        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn work_replay_requires_dominating_initial_allowance() {
        let before = Meter {
            limit: 100,
            spent: 10,
        };
        let after = Meter {
            limit: 100,
            spent: 40,
        };
        assert_eq!(before.replay(before, after), Some(40));
        assert_eq!(
            Meter {
                limit: 100,
                spent: 11
            }
            .replay(before, after),
            None
        );
        assert_eq!(
            Meter {
                limit: 150,
                spent: 60
            }
            .replay(before, after),
            Some(90)
        );
        assert_eq!(before.replay(after, before), None);
    }
    #[test]
    fn checkpoint_refusal_is_atomic_across_work_meters() {
        use crate::{Domain, EntryPolicy, SetupRegistry};
        let policy = Policy::default();
        let mut backend = NativeBackend::new(
            policy,
            EntryPolicy::new(Domain::new("P", "s", "e", None), None),
            SetupRegistry::new(vec![], &policy).unwrap(),
        )
        .unwrap();
        let before = backend.checkpoint();
        let mut after = before;
        after.external.spent += 3;
        after.sequence.spent += 5;
        after.ring.spent += 7;
        backend.sequence_work.spent = 1;
        assert!(!backend.replay(before, after));
        assert_eq!(backend.external_work.spent, 0);
        assert_eq!(backend.sequence_work.spent, 1);
        assert_eq!(backend.ring_work.spent, 0);
        backend.sequence_work.spent = 0;
        assert!(backend.replay(before, after));
        assert_eq!(backend.external_work.spent, 3);
        assert_eq!(backend.sequence_work.spent, 5);
        assert_eq!(backend.ring_work.spent, 7);
    }
}
