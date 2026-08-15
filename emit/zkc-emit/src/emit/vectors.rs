//! The vector-corpus vocabulary: the driver parses a corpus into
//! these types and the conformance emitter consumes them.

pub struct Vectors {
    pub artifact_id: String,
    pub cases: Cases,
}

/// Vector corpora are endpoint-shaped: a verifier replays untrusted
/// bytes to a verdict, a prover replays inputs to bytes. Keeping them
/// distinct at the type means a corpus can never be silently replayed
/// against the endpoint it does not describe.
pub enum Cases {
    Verifier(Vec<VectorCase>),
    Prover(Vec<ProverCase>),
}

pub struct VectorCase {
    pub name: String,
    pub statement: Vec<(String, String)>,
    pub proof_hex: String,
    pub expect: String,
    pub challenges: Vec<String>,
}

pub struct ProverCase {
    pub name: String,
    pub statement: Vec<(String, String)>,
    /// Witness label → lowercase-hex payload.
    pub witness: Vec<(String, String)>,
    /// `"ok"`, or the refusal kind (`"statement"`, `"fill"`).
    pub expect: String,
    /// The endpoint ABI label a refusal names; unused when `expect` is
    /// `"ok"`.
    pub label: String,
    /// The refusal's own sentence. Where a fill wrote it, this is the
    /// same text the reference supplier reports, so the corpus compares
    /// the diagnostic and not only the classification.
    pub message: String,
    pub proof_hex: String,
    pub challenges: Vec<String>,
}
