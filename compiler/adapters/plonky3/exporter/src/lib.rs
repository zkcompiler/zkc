//! Pinned Plonky3 0.5.1 AIR capture, export and import as views over the
//! shared `zkc.ring/0` expression arena.
//!
//! The exporter runs an `Air<SymbolicAirBuilder<KoalaBear>>` through the
//! upstream symbolic builder and lowers its constraints into one arena with a
//! closed slot binding, a source map and a feature inventory. The importer
//! decodes that candidate artifact, rechecks every derived fact and binds it to
//! an authorized instance and a witness. Unsupported upstream features refuse
//! by name. A capture is evidence about the selected source on the pinned
//! upstream; it is not a source-adequacy theorem for arbitrary Rust.

pub mod arena;
pub mod artifact;
pub mod bundle;
pub mod capture;
pub mod field;
pub mod model;
pub mod reference;
pub mod refusal;
pub mod view;

pub use artifact::{Instance, Witness};
pub use capture::export;
pub use model::{Export, SelectorKind, Slot};
pub use refusal::{Refusal, Result};
pub use view::{ClosedView, Openings, SelectorLaw};
