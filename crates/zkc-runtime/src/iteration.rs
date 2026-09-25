//! Resumable iteration over finite bodies. Scheduling fuel leaves a pending
//! continuation; only an explicit deployment policy turns it into exhaustion.
//! Callers supply admitted bodies and retain their actual resources in `S`.
//! This API neither catches failures nor rewinds state between steps.
//! The Lean resumption law assumes a fixed body and complete modeled state.
//! Mutable closure captures and external effects are not stored in this prefix.

use crate::{Outcome, Stop};
use std::ops::ControlFlow;

/// A complete finite prefix, including effects preceding a stop.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Execution<S, E, A> {
    pub outcome: Outcome<A>,
    pub state: S,
    pub events: Vec<E>,
}

impl<S, E, C, A> Execution<S, E, ControlFlow<A, C>> {
    pub fn pending(seed: C, state: S) -> Self {
        Self {
            outcome: Outcome::Returned(ControlFlow::Continue(seed)),
            state,
            events: Vec::new(),
        }
    }

    /// Continue from this prefix for at most `fuel` body invocations. A finished
    /// or stopped prefix is unchanged, even when more fuel is supplied.
    ///
    /// For resumable execution, keep all semantic state in `C`/`S`, or retain
    /// the same stateful callback (for example by passing `&mut body`) and
    /// include its captured state in the realization relation. Recreating a
    /// callback with reset captures is a different execution. Callback panic,
    /// divergence and external effects are not converted into `Stop` records.
    pub fn advance(self, fuel: usize, mut body: impl FnMut(C, S) -> Self) -> Self {
        let mut prefix = self;
        for _ in 0..fuel {
            let Outcome::Returned(ControlFlow::Continue(seed)) = prefix.outcome else {
                break;
            };
            let next = body(seed, prefix.state);
            prefix.events.extend(next.events);
            prefix.state = next.state;
            prefix.outcome = next.outcome;
        }
        prefix
    }

    /// End the selected deployment budget. This consumes the pending handle;
    /// the state and prior events remain available even on exhaustion.
    pub fn close(self) -> Execution<S, E, A> {
        Execution {
            outcome: match self.outcome {
                Outcome::Returned(ControlFlow::Continue(_)) => Outcome::Stopped(Stop::Exhausted),
                Outcome::Returned(ControlFlow::Break(value)) => Outcome::Returned(value),
                Outcome::Stopped(reason) => Outcome::Stopped(reason),
            },
            state: self.state,
            events: self.events,
        }
    }
}
