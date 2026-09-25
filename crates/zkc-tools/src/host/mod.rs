//! Shared host mechanics. Semantic admission and checker response decoding
//! remain with each consumer; the runtime has no filesystem/process dependency.
pub(crate) mod io;
pub(crate) mod process;
