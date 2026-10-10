//! Reusable project loading and bounded transport to the installed compiler.
mod manifest;
pub use manifest::{Asset, Project};
mod compiler;
pub use compiler::{
    CheckOptions, Checked, Compiler, Entry, EntryKind, Error, NotationOptions, Selection,
};
pub(crate) mod cli;
mod layout;
pub use layout::{Artifact, Layout, input_path};
mod preparation;
pub use preparation::{Preparation, Template};
mod selection;
