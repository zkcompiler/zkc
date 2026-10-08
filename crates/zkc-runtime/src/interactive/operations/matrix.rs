//! Independently authored matrix operation contracts and physical policy.
use super::*;
use Type::*;

pub(super) const CONTRACTS: &[Contract] = &[
    Contract::selectable(
        "matrix.mul_vector",
        (&[Matrix, Vector], &[Vector], AttributeRule::None),
    ),
    Contract::selectable(
        "matrix.transpose_mul_vector",
        (&[Matrix, Vector], &[Vector], AttributeRule::None),
    ),
    Contract::selectable(
        "matrix.bilinear",
        (&[Matrix, Vector, Vector], &[Field], AttributeRule::None),
    ),
    Contract::selectable(
        "matrix.identity_check",
        (&[Matrix], &[Bool], AttributeRule::MatrixIdentity),
    ),
    Contract::selectable(
        "matrix.dimension",
        (&[Matrix], &[Index], AttributeRule::Unsigned64),
    ),
    Contract::selectable(
        "matrix.shape_check",
        (&[Matrix], &[Bool], AttributeRule::MatrixDimensions),
    ),
];
pub(super) const CONTRIBUTION: Contribution = Contribution {
    alternatives: &[],
    physical_error: "uninstalled operation binding",
    physical_only: false,

    contracts: CONTRACTS,
    resolve: support::field_signature,
    providers: &["arkworks", "dalek", "plonky3"],
    select: support::select_nominal,
};
