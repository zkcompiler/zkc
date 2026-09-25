//! Bounded search over the pinned OpenVM witness predicate.
//!
//! Every trial checks the same transcript seed on a clone. Candidate-provider
//! state and spent work persist across prefixes. Finding a witness does not
//! mutate a live transcript: the caller must check it once on that transcript,
//! for example with the compiled `external.openvm.check_witness` operation.
//! This sequential driver does not reproduce upstream parallel `find_any`
//! scheduling or prescribe a candidate distribution.

use super::{Work, openvm::Duplex};
use crate::{Result, choices::Namespace, exhausted, refused};
use zkc_runtime::interactive::BackendError;

pub trait Candidates {
    fn next(&mut self, namespace: &Namespace) -> Result<u32>;
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Limits {
    /// Actual candidate-provider calls, including a call that fails.
    pub candidates: u64,
    /// Sum of primitive counts under `Work::units`, independently of attempts
    /// and the live backend's external-work budget.
    pub work: u64,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Usage {
    pub candidate_calls: u64,
    pub trials: u64,
    pub work: Work,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Progress {
    Pending,
    Found(u32),
    Stopped(BackendError),
}

pub struct Search<S> {
    source: S,
    namespace: Namespace,
    seed: Duplex,
    bits: u32,
    limits: Limits,
    usage: Usage,
    progress: Progress,
}

impl<S: Candidates> Search<S> {
    pub fn new(
        seed: &Duplex,
        bits: u32,
        namespace: Namespace,
        source: S,
        limits: Limits,
    ) -> Result<Self> {
        super::openvm::validate_bits(bits).map_err(|_| refused("grinding-bit-width"))?;
        Ok(Self {
            source,
            namespace,
            seed: seed.clone(),
            bits,
            limits,
            usage: Usage::default(),
            progress: if bits == 0 {
                Progress::Found(0)
            } else {
                Progress::Pending
            },
        })
    }

    pub fn progress(&self) -> &Progress {
        &self.progress
    }
    pub fn usage(&self) -> Usage {
        self.usage
    }
    pub fn source(&self) -> &S {
        &self.source
    }
    pub fn seed(&self) -> super::openvm::Snapshot {
        self.seed.snapshot()
    }

    /// Fuel pauses between trials. Exhausted deployment budgets and provider
    /// errors stop permanently. A stopped or successful search performs no
    /// further calls; all observations remain available on this object.
    pub fn advance(&mut self, fuel: usize) -> &Progress {
        for _ in 0..fuel {
            if self.progress != Progress::Pending {
                break;
            }
            match self.trial() {
                Ok(Some(witness)) => self.progress = Progress::Found(witness),
                Ok(None) => {}
                Err(error) => self.progress = Progress::Stopped(error),
            }
        }
        &self.progress
    }

    fn trial(&mut self) -> Result<Option<u32>> {
        if self.usage.candidate_calls >= self.limits.candidates {
            return Err(exhausted("grinding-candidates"));
        }
        let work = self
            .seed
            .witness_work(self.bits)
            .map_err(|_| refused("grinding-bit-width"))?;
        let next = self
            .usage
            .work
            .checked_add(work)
            .map_err(|_| exhausted("grinding-work"))?;
        if next.units().map_err(|_| exhausted("grinding-work"))? > self.limits.work {
            return Err(exhausted("grinding-work"));
        }
        self.usage.candidate_calls += 1; // Strictly below the u64 limit above.
        let witness = self.source.next(&self.namespace)?;
        super::openvm::validate_field(witness).map_err(|_| refused("grinding-candidate"))?;
        // Precharge crypto only after the provider returns a canonical value.
        self.usage.work = next;
        self.usage.trials += 1; // At most candidate_calls.
        let checked = self
            .seed
            .trial_witness(self.bits, witness)
            .map_err(|_| refused("grinding-candidate"))?;
        debug_assert_eq!(checked.work, work);
        Ok(checked.value.then_some(witness))
    }
}
