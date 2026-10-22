//! Reusable project loading and bounded transport to the installed compiler.
mod manifest;
pub use manifest::{Asset, CatalogDependency, Project, ProjectGraph, ProjectPackage};
mod compiler;
pub use compiler::{
    CheckOptions, Checked, CompilationRequest, CompilationResult, Compiler, Entry, EntryKind,
    Error, NotationOptions, ObservationRequest, Selection,
};
mod layout;
pub use layout::{Artifact, Layout, input_path};
mod preparation;
pub use preparation::{Preparation, Template};
mod inspection;
pub(crate) mod selection;
pub use inspection::CheckedInterface;

mod settings;
pub use settings::{BuildSettings, ResolvedSettings};
mod cache;
pub use cache::CompilationCache;
pub(crate) mod testing;
pub use testing::TestRecipe;
