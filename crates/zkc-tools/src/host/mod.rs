//! Shared host mechanics. Semantic admission and checker response decoding
//! remain with each consumer; the runtime has no filesystem/process dependency.
//! Existing artifact-* and native-proof-* diagnostics are shared external error
//! codes. Their prefixes do not determine this module's dependency direction.
pub(crate) mod io;
pub(crate) mod process;

pub(crate) mod admission;
pub(crate) mod capacity;
pub(crate) mod inputs;
pub(crate) mod json;
pub(crate) mod material;
pub(crate) mod request;
pub(crate) mod setups;

pub(crate) mod document;
