//! Bind the compiler's normalized inventory to the requested selection.
//! Completeness against absent source and installed realizations belong to the
//! compiler. An authenticated deployment supplies that source-relative judgment.
use crate::entry::{OracleRoots, OracleSelection};
use crate::io::bytes::Result;

pub(super) fn check(requested: &OracleSelection, encoded: &str) -> Result<()> {
    let invalid = || "native-proof-oracle-selection".to_owned();
    let normalized = OracleSelection::parse(encoded).map_err(|_| invalid())?;
    if normalized.canonical_json().map_err(|_| invalid())? != encoded
        || normalized.order != requested.order
        || normalized.authentication != requested.authentication
    {
        return Err(invalid());
    }
    let OracleRoots::Exact(entries) = &normalized.roots else {
        return Err(invalid());
    };
    let consistent = match &requested.roots {
        OracleRoots::Uniform(table) => entries.iter().all(|root| {
            root.scheme == table.scheme
                && root.grouping == table.grouping
                && root.order == table.order
        }),
        OracleRoots::Exact(_) => requested == &normalized,
    };
    if !consistent {
        return Err(invalid());
    }
    Ok(())
}
