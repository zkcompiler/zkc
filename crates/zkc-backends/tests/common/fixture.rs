//! What every backend test in this crate needs before it can judge anything.
//!
//! This crate's tests arrive through two module roots — `tests/common/mod.rs`
//! for the eleven that drive BLS declarations, `tests/domains/support.rs` for
//! the thirteen that run one suite over several carriers — and no test target
//! includes both. They had grown their own copies of the same three things: a
//! byte-identical `domain`, a backend constructor differing only in which
//! argument it let the caller vary, and the runner's poll loop. Those live
//! here, and each root keeps what is actually its own.
#![allow(dead_code)]

use zkc_arkworks::VerifierKey;
use zkc_backends::{Domain, EntryPolicy, NativeBackend, Policy, PublicInputs, Value};
use zkc_runtime::interactive::{Action, Backend, Runner, Stop, StopKind};

/// The one execution identity these tests run under.
pub fn domain() -> Domain {
    Domain::new("P", "session", "main", None)
}

/// The entry policy at a chosen homogeneous arity, local inputs only.
pub fn entry(n: Option<usize>) -> EntryPolicy {
    EntryPolicy::new(domain(), n, PublicInputs::LocalOnly)
}

/// A backend, with the three things a test ever varies given in one place.
///
/// Sixty call sites constructed this directly and forty-two of them wanted the
/// same thing: the default policy, no arity, no verifier key. The remainder
/// varied exactly one of those, so they vary one here. A test *about* an entry
/// policy or a public-input mode still builds its own subject and passes it to
/// `NativeBackend::new`, because there the argument is what is being judged.
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
        NativeBackend::new(self.policy, entry(self.arity), self.verifier).unwrap()
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
