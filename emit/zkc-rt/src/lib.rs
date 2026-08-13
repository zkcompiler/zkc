//! Runtime support for zkc-emitted endpoints.
//!
//! The reference semantics live in the zkc interpreter
//! (`lib/Interpreter/Interpreter.cpp`) and the endpoint specification
//! (`docs/spec/endpoints.md` §§4, 6); this crate carries the pieces every
//! emitted crate shares — the verdict vocabulary, the proof cursor, the
//! prover's observables, and the profile supplier sets as concrete types.
//! Everything protocol-specific is emitted, not looked up: an emitted
//! crate calls these types directly and monomorphically.
//!
//! The reject classes are the normative set. "I cannot judge this proof"
//! has no arm here at all: supplier resolution happened at emit time, so
//! an emitted verifier either judges a proof or reports malformed caller
//! input — the refusal/reject distinction, discharged early. The prover
//! side has no verdict channel at all: acceptance belongs to verifiers,
//! so a prover run either produces bytes or refuses.

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

/// An opaque witness payload: the digest membrane at the execution
/// boundary (`docs/spec/endpoints.md` §6.2). Emitted crates move these
/// values through the hole calls that consume them and never look
/// inside; the bound suppliers own all parsing.
///
/// Deliberately neither `Copy` nor `Clone`. A handle is a linear
/// resource the carrier consumes exactly once (the `zkc-E149` rule), so
/// a move-only type makes rustc the enforcer of that discipline inside
/// emitted code: a payload consumed by one fill cannot be consumed by
/// another. `Debug` prints the length only, so a witness cannot reach a
/// log through a derived format.
pub struct Payload(Vec<u8>);

impl Payload {
    pub fn new(bytes: Vec<u8>) -> Payload {
        Payload(bytes)
    }

    /// The caller-boundary form the reference executor takes on the
    /// command line: lowercase hex, even length. `None` is the emitted
    /// crate's analogue of the reference's malformed-payload refusal —
    /// reported before `prove` is called, never inside it.
    pub fn from_hex(hex: &str) -> Option<Payload> {
        if !hex.len().is_multiple_of(2)
            || !hex
                .bytes()
                .all(|c| c.is_ascii_digit() || (b'a'..=b'f').contains(&c))
        {
            return None;
        }
        let nibble = |byte: u8| -> u8 {
            if byte <= b'9' {
                byte - b'0'
            } else {
                byte - b'a' + 10
            }
        };
        let bytes = hex.as_bytes();
        Some(Payload(
            (0..bytes.len())
                .step_by(2)
                .map(|at| (nibble(bytes[at]) << 4) | nibble(bytes[at + 1]))
                .collect(),
        ))
    }

    pub fn as_bytes(&self) -> &[u8] {
        &self.0
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
}

impl std::fmt::Debug for Payload {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(formatter, "Payload(<{} bytes>)", self.0.len())
    }
}

/// Memory hygiene as a declared option rather than a silent default:
/// zeroing on drop is a claimable property only when the whole call
/// chain cooperates, so the emitted crate says which build it is. The
/// nonclaim in the emitted README stands either way.
#[cfg(feature = "zeroize")]
impl Drop for Payload {
    fn drop(&mut self) {
        use zeroize::Zeroize;
        self.0.zeroize();
    }
}

/// One prover run's observables: the emitted proof bytes and the ordered
/// challenge log of the replica sponge. The log is the same observable
/// the verifier reports, which is what makes the two endpoints
/// comparable entry for entry.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Prove {
    pub proof: Vec<u8>,
    pub challenges: Vec<String>,
}

/// The prover's whole failure surface. There is no verdict here:
/// acceptance belongs to verifiers, so every failure is a refusal.
///
/// Supplier resolution, endpoint kind, and codec routing were settled at
/// emit time, so the reference executor's `zkc-E407`/`zkc-E409` arms have
/// no run-time form; a missing witness payload (`zkc-E410`) is a compile
/// error, since `Witness` names every payload as a field.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProveError {
    /// A statement value outside the range its class admits — the
    /// prover's own input, checked before any event.
    Statement { label: String, message: String },
    /// A fill reported a defect at its own boundary, or produced a value
    /// its class cannot carry on the wire. The value is caught before any
    /// byte is emitted, so a refused run leaves no partial proof.
    Fill { label: String, message: String },
}

impl ProveError {
    /// The stable spelling the conformance vectors compare against.
    pub fn kind(&self) -> &'static str {
        match self {
            ProveError::Statement { .. } => "statement",
            ProveError::Fill { .. } => "fill",
        }
    }

    /// The endpoint ABI label the refusal is about.
    pub fn label(&self) -> &str {
        match self {
            ProveError::Statement { label, .. } | ProveError::Fill { label, .. } => label,
        }
    }

    pub fn message(&self) -> &str {
        match self {
            ProveError::Statement { message, .. } | ProveError::Fill { message, .. } => message,
        }
    }
}

impl std::fmt::Display for ProveError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            formatter,
            "{} refusal at '{}': {}",
            self.kind(),
            self.label(),
            self.message()
        )
    }
}

impl std::error::Error for ProveError {}

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
