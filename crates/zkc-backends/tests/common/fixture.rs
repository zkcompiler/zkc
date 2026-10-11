//! Fresh backend builders and runner polling shared by integration suites.
//!
//! Each integration binary declares this module once. The common BLS helpers
//! and the multi-carrier helpers reuse it while keeping their own vocabulary.
//! Every builder creates a fresh backend; cases do not share runtime state.
#![allow(dead_code)]

use zkc_arkworks::VerifierKey;
use zkc_backends::{Domain, EntryPolicy, NativeBackend, Policy, Value};
use zkc_runtime::interactive::{Action, Backend, Runner, Stop, StopKind};

/// The one execution identity these tests run under.
pub fn domain() -> Domain {
    Domain::new("P", "session", "main", None)
}

/// The entry policy at a chosen homogeneous arity, local inputs only.
pub fn entry(n: Option<usize>) -> EntryPolicy {
    EntryPolicy::new(domain(), n)
}

/// A backend, with the three things a test ever varies given in one place.
///
/// Defaults use no homogeneous arity and no verifier key. Tests of the entry
/// policy itself still construct their subject with `NativeBackend::new`.
pub struct Fixture {
    policy: Policy,
    arity: Option<usize>,
    verifier: Option<VerifierKey>,
}

pub fn backend() -> Fixture {
    Fixture {
        policy: Policy::default(),
        arity: None,
        verifier: None,
    }
}

impl Fixture {
    pub fn policy(mut self, policy: Policy) -> Self {
        self.policy = policy;
        self
    }

    pub fn arity(mut self, n: usize) -> Self {
        self.arity = Some(n);
        self
    }

    pub fn verifier(mut self, key: VerifierKey) -> Self {
        self.verifier = Some(key);
        self
    }

    pub fn build(self) -> NativeBackend {
        NativeBackend::new(
            self.policy,
            entry(self.arity),
            zkc_backends::SetupRegistry::new(
                (self.verifier).into_iter().collect(),
                &zkc_backends::Policy::default(),
            )
            .unwrap(),
        )
        .unwrap()
    }
}

/// Run an admitted program to its end, executing every local cut it asks for.
///
/// The bound is a test-driver limit rather than a property of the language: a
/// program that will not finish should fail the test that runs it instead of
/// hanging the suite. Both module roots wrote this loop; they differ only in
/// what they hand back, which is why that is the caller's business.
pub fn drive<B: Backend<Value = Value>>(
    mut runner: Runner<B>,
) -> (std::result::Result<Vec<Value>, Stop>, B) {
    for _ in 0..100 {
        while runner.advance_local_control().unwrap() {}
        match runner.poll() {
            Action::Local(action) => runner.execute_local(&action.cut).unwrap(),
            Action::Returned(values) => return (Ok(values), runner.into_backend()),
            Action::Stopped(stop) => return (Err(stop), runner.into_backend()),
            other => panic!("unexpected {other:?}"),
        }
    }
    panic!("test driver limit")
}

/// The stable identifier a backend refusal carries.
pub fn code(stop: &Stop) -> &str {
    match &stop.kind {
        StopKind::Backend(e) => &e.code,
        other => panic!("unexpected {other:?}"),
    }
}
