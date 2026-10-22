//! Bounded regular-file ingress and per-file atomic artifact publication.
//! Explicit authority paths may resolve symlinks; confined Entry documents use
//! `entry::files::Documents` and its stricter descriptor-based rules.
pub use crate::host::io::{ReadError, read_regular};
pub use crate::host::publication::{Outputs, Publication, PublicationError, PublicationStage};

/// Render canonical hexadecimal bytes used by package and material identities.
pub fn hex(bytes: &[u8]) -> String {
    crate::host::inputs::hex(bytes)
}
/// Parse a canonical package or material SHA-256 identity.
pub fn digest(text: &str) -> Result<[u8; 32], String> {
    crate::host::inputs::digest(text)
}
/// Parse canonical hexadecimal invocation context bytes.
pub fn context_bytes(text: &str) -> Result<Vec<u8>, String> {
    crate::host::inputs::unhex(&serde_json::json!(text))
}
