//! File capabilities and transport for schema-directed Entry inputs.
type Result<T> = std::result::Result<T, String>;
use super::inputs::MAX_REQUEST_BYTES;

mod resolver;
pub use resolver::Documents;

mod invocations;
pub use invocations::{InvocationInputError, Invocations};

/// Read one setup material file of an invocation whose earlier files hold
/// `held` bytes. A file is one wire frame of `capacity`, and the invocation's
/// files together are bounded by `setup_bytes`
/// ([`Allowances::SETUP_BYTES`](crate::run::Allowances::SETUP_BYTES)). A file
/// the remaining setup allowance cannot hold refuses with `entry-setup-limit`.
pub fn read_setup_material(
    path: &std::path::Path,
    capacity: crate::execution::Capacity,
    setup_bytes: usize,
    held: usize,
) -> Result<Vec<u8>> {
    let remaining = setup_bytes.saturating_sub(held);
    crate::io::bytes::read_regular(path, capacity.wire_bytes.min(remaining)).map_err(|code| {
        if code == "artifact-byte-limit" && remaining < capacity.wire_bytes {
            "entry-setup-limit".into()
        } else {
            code
        }
    })
}
