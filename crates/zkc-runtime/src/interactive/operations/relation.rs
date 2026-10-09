//! One present table of an immutable Bundle asset: assertion residuals over
//! actual columns, and the polynomial view's shape, input descriptors, scopes
//! and point substitution.
use super::*;

pub(super) const CONTRIBUTION: Contribution = Contribution {
    contracts: &[
        Contract::new(
            "relation.table_rows",
            (
                &[Type::Vector, Type::Vector, Type::Vector, Type::Index],
                &[Type::Vector],
                AttributeRule::AssetIdentity,
            ),
        )
        .implemented_by(&["plonky3/relation.table_rows"]),
        Contract::new(
            "relation.table_shape",
            (
                &[Type::Index],
                &[Type::Index; 7],
                AttributeRule::AssetIdentity,
            ),
        )
        .implemented_by(&["plonky3/relation.table_shape"]),
        Contract::new(
            "relation.table_input",
            (
                &[Type::Index, Type::Index],
                &[Type::Index; 3],
                AttributeRule::AssetIdentity,
            ),
        )
        .implemented_by(&["plonky3/relation.table_input"]),
        Contract::new(
            "relation.table_scope",
            (
                &[Type::Index, Type::Index],
                &[Type::Index; 2],
                AttributeRule::AssetIdentity,
            ),
        )
        .implemented_by(&["plonky3/relation.table_scope"]),
        Contract::new(
            "relation.table_point",
            (
                &[Type::Vector],
                &[Type::Vector],
                AttributeRule::AssetIdentity,
            ),
        )
        .implemented_by(&["plonky3/relation.table_point"]),
    ],
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
