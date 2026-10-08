//! In-process invocation data. These descriptions confer no execution authority.
use zkc_backends::Value;

/// One native entry operand. Immutable data may be supplied without encoding;
/// private capabilities are declarations and are issued by the admitted host.
#[derive(Debug)]
pub enum InputValue {
    /// Immutable data satisfying its upstream scalar/group library invariants.
    Native(Box<Value>),
    Wire(Vec<u8>),
    Resource {
        budget: u64,
    },
    VerifierKey(String),
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
