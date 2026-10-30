//! One table of an immutable Bundle asset: assertion residuals over actual
//! columns, the polynomial view's shape, input descriptors, scopes and point
//! substitutions, and the metadata/interaction view's widths, policy, interaction
//! descriptors and record substitutions.
use super::*;

pub(super) const CONTRIBUTION: Contribution = Contribution {
    contracts: &[
        Installation::new("relation.table_rows").implemented_by(&["plonky3/relation.table_rows"]),
        Installation::new("relation.table_shape").implemented_by(&["plonky3/relation.table_shape"]),
        Installation::new("relation.table_input").implemented_by(&["plonky3/relation.table_input"]),
        Installation::new("relation.table_scope").implemented_by(&["plonky3/relation.table_scope"]),
        Installation::new("relation.table_point").implemented_by(&["plonky3/relation.table_point"]),
        Installation::new("relation.table_points")
            .implemented_by(&["plonky3/relation.table_points"]),
        Installation::new("relation.table_widths")
            .implemented_by(&["plonky3/relation.table_widths"]),
        Installation::new("relation.table_policy")
            .implemented_by(&["plonky3/relation.table_policy"]),
        Installation::new("relation.table_interactions")
            .implemented_by(&["plonky3/relation.table_interactions"]),
        Installation::new("relation.table_interaction")
            .implemented_by(&["plonky3/relation.table_interaction"]),
        Installation::new("relation.table_record_points")
            .implemented_by(&["plonky3/relation.table_record_points"]),
    ],

    select,
    alternatives: &[],
    physical_error: "uninstalled operation binding",
    adapter: None,
};
/// Relation views evaluate integer residue coordinates, so no binary field is
/// implemented, although the logical contract needs only a field.
fn select(
    binding: &OperationBinding,
    logical: &OperationSignature<LogicalType>,
    selection: Selection,
) -> Result<BoundSignature> {
    if !support::primary(binding)?.has_residue_coordinates() {
        return Err(support::failure());
    }
    support::select_nominal(binding, logical, selection)
}
