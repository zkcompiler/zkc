//! Construction attempts with persistent state and unpublished output.
//!
//! Each invocation executes one finite, admitted protocol body. A retry is
//! returned data, not a caught terminal stop. The controller retains the actual
//! successor state and drops only that attempt's tentative output. It never
//! publishes: a completed proof is handed to a separate publication operation.
//! Host callbacks must include their external state in the realization contract;
//! this controller does not establish source admission or cryptographic security.

use crate::{Outcome, Stop, iteration::Execution};
use std::ops::ControlFlow;

/// Deployment limits, independent of the protocol's mathematical retry policy.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Limits {
    pub attempts: u64,
    pub proof_bytes: usize,
}

/// The body explicitly distinguishes a recoverable condition from completion.
#[derive(Debug, PartialEq, Eq)]
pub enum Decision<R, A> {
    Retry(R),
    Complete(A),
}

/// This journal records buffer disposition, not the body's private choices.
/// Actual operation observations and provider counters remain in persistent `S`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Event<R> {
    Started {
        attempt: u64,
    },
    Retried {
        attempt: u64,
        reason: R,
        bytes: usize,
    },
    Produced {
        attempt: u64,
        bytes: usize,
    },
    Stopped {
        attempt: u64,
        reason: Stop,
        bytes: usize,
    },
}

/// Tentative bytes are append-only and cannot be extracted by an attempt body.
/// A failed append poisons this attempt even if the caller ignores its error.
pub struct Context<S> {
    state: S,
    bytes: Vec<u8>,
    limit: usize,
    failure: Option<Stop>,
}

impl<S> Context<S> {
    pub fn state(&self) -> &S {
        &self.state
    }

    /// The same successor state is passed to the next attempt, including on
    /// retry or failure. Attempt-local resources must be retired explicitly by
    /// their owning adapter; a host cannot assume dropping this buffer does so.
    pub fn state_mut(&mut self) -> &mut S {
        &mut self.state
    }

    pub fn append(&mut self, bytes: &[u8]) -> Result<(), Stop> {
        if let Some(reason) = self.failure {
            return Err(reason);
        }
        if bytes.len() > self.limit.saturating_sub(self.bytes.len())
            || self.bytes.try_reserve(bytes.len()).is_err()
        {
            self.failure = Some(Stop::Exhausted);
            return Err(Stop::Exhausted);
        }
        self.bytes.extend_from_slice(bytes);
        Ok(())
    }

    pub fn buffered_bytes(&self) -> usize {
        self.bytes.len()
    }
}

/// A successful, still-unpublished proof. Its codec is chosen by the body;
/// no framework header, domain separator or artifact hash is inserted here.
#[derive(Debug, PartialEq, Eq)]
pub struct Prepared<A> {
    pub value: A,
    pub bytes: Vec<u8>,
    pub attempt: u64,
}

pub type Prefix<S, R, A> = Execution<S, Event<R>, ControlFlow<Prepared<A>, u64>>;

pub struct Controller<S, R, A> {
    limits: Limits,
    prefix: Prefix<S, R, A>,
}

impl<S, R, A> Controller<S, R, A> {
    pub fn new(state: S, limits: Limits) -> Self {
        Self {
            limits,
            prefix: Execution::pending(0, state),
        }
    }

    pub fn prefix(&self) -> &Prefix<S, R, A> {
        &self.prefix
    }

    /// Fuel pauses between attempts; the deployment limit is an actual stop.
    /// Neither changes consumed provider state or turns an ordinary stop into
    /// a retry. Keep the same callback's captures when they carry semantic state.
    pub fn advance(
        self,
        fuel: usize,
        mut body: impl FnMut(u64, &mut Context<S>) -> Result<Decision<R, A>, Stop>,
    ) -> Self {
        let limits = self.limits;
        let prefix = self.prefix.advance(fuel, |attempt, state| {
            if attempt >= limits.attempts {
                return Execution {
                    outcome: Outcome::Stopped(Stop::Exhausted),
                    state,
                    events: vec![Event::Stopped {
                        attempt,
                        reason: Stop::Exhausted,
                        bytes: 0,
                    }],
                };
            }
            let mut context = Context {
                state,
                bytes: Vec::new(),
                limit: limits.proof_bytes,
                failure: None,
            };
            let decision = body(attempt, &mut context);
            let decision = context.failure.map_or(decision, Err);
            let bytes = context.bytes.len();
            let (outcome, event) = match decision {
                Ok(Decision::Retry(reason)) => (
                    Outcome::Returned(ControlFlow::Continue(attempt + 1)),
                    Event::Retried {
                        attempt,
                        reason,
                        bytes,
                    },
                ),
                Ok(Decision::Complete(value)) => (
                    Outcome::Returned(ControlFlow::Break(Prepared {
                        value,
                        bytes: context.bytes,
                        attempt,
                    })),
                    Event::Produced { attempt, bytes },
                ),
                Err(reason) => (
                    Outcome::Stopped(reason),
                    Event::Stopped {
                        attempt,
                        reason,
                        bytes,
                    },
                ),
            };
            Execution {
                outcome,
                state: context.state,
                events: vec![Event::Started { attempt }, event],
            }
        });
        Self { limits, prefix }
    }

    /// Explicitly close a pending deployment. No proof escapes an unfinished,
    /// failed or discarded attempt; all previous state and events are retained.
    pub fn close(self) -> Execution<S, Event<R>, Prepared<A>> {
        self.prefix.close()
    }
}
