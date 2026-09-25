//! The backend a test in this crate drives, and the one thing tests vary.
//!
//! Twenty-four sites here constructed this directly, and every one of them
//! asked for the same policy, no homogeneous arity and no verifier key. What
//! they actually chose was the execution identity — which role, which session,
//! which entry — so that is what this takes, and the rest has one spelling.
#![allow(dead_code, unused_imports)]

use zkc_backends::{Domain, EntryPolicy, NativeBackend, Policy, PublicInputs};

/// The prover, in the ordinary test session, at the ordinary entry.
pub fn backend() -> NativeBackend {
    backend_at("P", "test", "main")
}

/// A named role, otherwise ordinary.
pub fn backend_for(role: &str) -> NativeBackend {
    backend_at(role, "test", "main")
}

/// A named role in a named session, which is what separates two runs that
/// would otherwise replay each other.
pub fn backend_in(role: &str, session: &str) -> NativeBackend {
    backend_at(role, session, "main")
}

/// The whole execution identity, for a test whose entry is not `main`.
pub fn backend_at(role: &str, session: &str, entry: &str) -> NativeBackend {
    NativeBackend::new(
        Policy::default(),
        EntryPolicy::new(
            Domain::new(role, session, entry, None),
            None,
            PublicInputs::LocalOnly,
        ),
        None,
    )
    .unwrap()
}
