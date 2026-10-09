//! One present table's assertion residuals from an immutable Bundle asset.
use super::*;

pub(super) const CONTRIBUTION: Contribution = Contribution {
    contracts: &[Contract::new(
        "relation.table_rows",
        (
            &[Type::Vector, Type::Vector, Type::Vector, Type::Index],
            &[Type::Vector],
            AttributeRule::AssetIdentity,
        ),
    )
    .implemented_by(&["plonky3/relation.table_rows"])],
    resolve,
    select: support::select_nominal,
    alternatives: &[],
    physical_error: "uninstalled operation binding",
    physical_only: false,
};
fn resolve(
    binding: &OperationBinding,
    contract: &Contract,
) -> Result<KernelSignature<LogicalType>> {
    let [field, table] = binding.arguments.as_slice() else {
        return Err(support::failure());
    };
    let field = Identity::parse(field)?;
    if field.scalar_field() != Some(field)
        || !crate::logical::natural_index(table).is_ok_and(|n| n <= 1_048_576)
    {
        return Err(support::failure());
    }
    support::instantiate(contract.shape()?, field, |kind| {
        support::field_type(kind, field)
    })
}
