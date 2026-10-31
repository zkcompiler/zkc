//! Fixed native policy and cumulative work evidence for pure computations.
use super::CpuBackend;
use crate::Policy;
use zkc_runtime::vm::AuthorizationId;

#[derive(Clone, Copy, Debug)]
pub struct ComputationCheckpoint {
    authorization: AuthorizationId,
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
impl CpuBackend {
    pub(super) fn checkpoint(&self) -> ComputationCheckpoint {
        ComputationCheckpoint {
            authorization: self.contracts.authorization_id(),
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
        if current.authorization != before.authorization
            || after.authorization != before.authorization
            || current.policy != before.policy
            || after.policy != before.policy
        {
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
        let mut backend = CpuBackend::new(
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

    #[test]
    fn replay_preserves_numerical_call_policy() {
        use crate::{Domain, EntryPolicy, SetupRegistry};
        let policy = Policy::default();
        let mut backend = CpuBackend::new(
            policy,
            EntryPolicy::new(Domain::new("P", "s", "e", None), None),
            SetupRegistry::new(vec![], &policy).unwrap(),
        )
        .unwrap();
        let before = backend.checkpoint();
        assert!(backend.replay(before, before));
        backend.core.policy.max_numerical_work -= 1;
        assert!(!backend.replay(before, before));
        backend.core.policy = policy;
        backend.core.policy.max_numerical_bytes -= 1;
        assert!(!backend.replay(before, before));
        backend.core.policy = policy;
        backend.core.policy.max_search_attempts -= 1;
        assert!(!backend.replay(before, before));
    }

    #[test]
    fn replay_requires_the_same_immutable_authorization_view() {
        use crate::{Domain, EntryPolicy, SetupRegistry};
        use zkc_runtime::vm::{ExecutionPolicy, ImplementationRequirements, OperationBinding};
        let mut backend = CpuBackend::new(
            Policy::default(),
            EntryPolicy::new(Domain::new("P", "s", "e", None), None),
            SetupRegistry::default(),
        )
        .unwrap();
        let contracts = backend.contracts.clone();
        let before = backend.checkpoint();
        let mut after = before;
        after.external.spent = 3;
        assert_eq!(
            contracts.authorization_id(),
            contracts.clone().authorization_id()
        );
        assert_eq!(
            contracts.authorization_id(),
            contracts.with_policy(contracts.policy()).authorization_id()
        );
        let granted = contracts
            .with_timing_grant(
                OperationBinding {
                    contract: "field.mul".into(),
                    arguments: vec!["bls12-381.fr".into()],
                    implementation: "arkworks/field.mul".into(),
                    physical_arguments: vec![],
                },
                ImplementationRequirements::default(),
            )
            .unwrap();
        for changed in [
            contracts.with_policy(ExecutionPolicy::general_purpose()),
            granted,
            zkc_runtime::vm::Contracts::standard(contracts.policy()),
        ] {
            backend.contracts = changed;
            assert!(!backend.replay(before, after));
            assert_eq!(backend.external_work.spent, 0);
            assert!(!backend.replay(backend.checkpoint(), after));
        }
        backend.contracts = contracts;
        assert!(backend.replay(before, after));
        assert_eq!(backend.external_work.spent, 3);
    }
}
