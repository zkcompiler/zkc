//! In-process invocation data. These descriptions confer no execution authority.
use super::material::ProverMaterial;
use zkc_backends::Value;

/// One native entry operand. Immutable data may be supplied without encoding;
/// private capabilities are declarations and are issued by the admitted host.
#[derive(Debug)]
pub enum InputValue {
    /// Immutable data satisfying its upstream scalar/group library invariants.
    Native(Box<Value>),
    Wire(Vec<u8>),
    /// An active arm of the admitted native variant type. Payloads contain only
    /// immutable data; no key, service, or private capability is issued here.
    Variant {
        alternative: usize,
        payload: Vec<InputValue>,
    },
    Resource {
        budget: u64,
    },
    /// Use the verifier key selected by the admitted input association.
    VerifierKey,
    /// Reuse authenticated material under this invocation's setup and quotas.
    ProverKey(ProverMaterial),
    ProverKeyFile {
        path: String,
        fingerprint: [u8; 32],
    },
}

impl From<Value> for InputValue {
    fn from(value: Value) -> Self {
        Self::Native(Box::new(value))
    }
}
