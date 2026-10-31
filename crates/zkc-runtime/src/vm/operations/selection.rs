//! Exact scalar selection; alternatives are values, not lazy branches.
use super::*;

pub(super) const CONTRACTS: &[Installation] = &[
    Installation::new("bool.select").implemented_by(&["native/bool.select"]),
    Installation::new("index.select").implemented_by(&["native/index.select"]),
    Installation::new("field.select").implemented_by(&[
        "arkworks/field.select",
        "dalek/field.select",
        "plonky3/field.select",
    ]),
    Installation::new("curve.select")
        .implemented_by(&["arkworks/curve.select", "dalek/curve.select"]),
];
pub(super) const CONTRIBUTION: Contribution = Contribution {
    contracts: CONTRACTS,
    select,
    alternatives: &[],
    physical_error: "uninstalled scalar selection",
};

fn select(
    binding: &OperationBinding,
    logical: &OperationSignature<LogicalType>,
    selection: Selection,
) -> Result<BoundSignature> {
    if matches!(binding.contract.as_str(), "field.select" | "curve.select") {
        support::select_nominal(binding, logical, selection)
    } else {
        default_ports(binding, logical, selection)
    }
}
