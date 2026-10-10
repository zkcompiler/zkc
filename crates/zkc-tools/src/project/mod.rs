//! Reusable project loading and bounded transport to the installed compiler.
mod manifest;
pub use manifest::{Asset, Project};
mod compiler;
pub use compiler::{Checked, Compiler, Entry, EntryKind, Error, Selection};
pub(crate) mod cli;
pub(crate) mod output;
mod selection;
