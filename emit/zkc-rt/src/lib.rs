//! Runtime support for zkc-emitted verifier endpoints.
//!
//! The reference semantics live in the zkc interpreter
//! (`lib/Interpreter/Interpreter.cpp`) and the endpoint specification
//! (`docs/spec/endpoints.md` §4); this crate carries the pieces every
//! emitted crate shares — the verdict vocabulary, the proof cursor, and
//! the profile supplier sets as concrete types. Everything
//! protocol-specific is emitted, not looked up: an emitted crate calls
//! these types directly and monomorphically.
//!
//! The reject classes are the normative set. "I cannot judge this proof"
//! has no arm here at all: supplier resolution happened at emit time, so
//! an emitted verifier either judges a proof or reports malformed caller
//! input — the refusal/reject distinction, discharged early.

/// Normative reject classes (`docs/spec/endpoints.md` §4). An
/// implementation may refine but not collapse them; this one carries the
/// exact set the reference executor reports today.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RejectClass {
    AbiDecodeFailure,
    AbiValidationFailure,
    ProofTrailingData,
    PublicBindingFailure,
    TranscriptFailure,
    CheckFailure,
}

impl RejectClass {
    /// The reference executor's verdict string — the differential gate
    /// compares these exact spellings against the golden vectors.
    pub fn as_str(self) -> &'static str {
        match self {
            RejectClass::AbiDecodeFailure => "abi_decode_failure",
            RejectClass::AbiValidationFailure => "abi_validation_failure",
            RejectClass::ProofTrailingData => "proof_trailing_data",
            RejectClass::PublicBindingFailure => "public_binding_failure",
            RejectClass::TranscriptFailure => "transcript_failure",
            RejectClass::CheckFailure => "check_failure",
        }
    }
}

/// One verifier verdict: acceptance, or a named reject class.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Verdict {
    Accept,
    Reject(RejectClass),
}

impl Verdict {
    pub fn as_str(self) -> &'static str {
        match self {
            Verdict::Accept => "accept",
            Verdict::Reject(class) => class.as_str(),
        }
    }
}

/// One verifier execution's observables: the verdict and the ordered
/// challenge log (one decimal entry per squeeze event; a vector event
/// joins its draws with `|`). The log is how Fiat-Shamir determinism is
/// externally checkable — the same observables the reference executor
/// reports.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Outcome {
    pub verdict: Verdict,
    pub challenges: Vec<String>,
}

impl Outcome {
    pub fn accept(challenges: Vec<String>) -> Self {
        Outcome {
            verdict: Verdict::Accept,
            challenges,
        }
    }
    pub fn reject(class: RejectClass, challenges: Vec<String>) -> Self {
        Outcome {
            verdict: Verdict::Reject(class),
            challenges,
        }
    }
}

/// The verifier proof stream: a cursor over untrusted bytes. Reads are
/// exact-width; an underrun is the caller's reject to report
/// (`abi_decode_failure`), and `expect_end` demands exhaustion
/// (`proof_trailing_data`). The cursor itself never invents a verdict.
pub struct ProofCursor<'a> {
    bytes: &'a [u8],
    position: usize,
}

impl<'a> ProofCursor<'a> {
    pub fn new(bytes: &'a [u8]) -> Self {
        ProofCursor { bytes, position: 0 }
    }

    /// Exactly `width` bytes, or `None` on underrun.
    pub fn take(&mut self, width: usize) -> Option<&'a [u8]> {
        if self.position + width > self.bytes.len() {
            return None;
        }
        let slice = &self.bytes[self.position..self.position + width];
        self.position += width;
        Some(slice)
    }

    /// The `expect_end` question: has the stream been exhausted?
    pub fn at_end(&self) -> bool {
        self.position == self.bytes.len()
    }
}

#[cfg(feature = "toy")]
pub mod toy;

#[cfg(feature = "plonky3")]
pub mod p3;

#[cfg(feature = "kzg")]
pub mod kzg;
