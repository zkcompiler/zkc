//! File capabilities and transport for schema-directed Entry inputs.
type Result<T> = std::result::Result<T, String>;
use super::inputs::MAX_REQUEST_BYTES;

mod resolver;
pub use resolver::Documents;

mod invocations;
pub use invocations::{InvocationInputError, Invocations};
