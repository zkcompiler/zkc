//! Independently authored matrix operation contracts and physical policy.
use super::*;
use Type::*;

pub(super) const CONTRACTS: &[Contract] = &[
    Contract::selectable(
        "matrix.row_dot",
        (&[Matrix, Vector, Index], &[Field], AttributeRule::None),
    )
    .implemented_by(&[
        "arkworks/matrix.row_dot",
        "dalek/matrix.row_dot",
        "plonky3/matrix.row_dot",
    ]),
    Contract::selectable(
        "matrix.column_dot",
        (&[Matrix, Vector, Index], &[Field], AttributeRule::None),
    )
    .implemented_by(&[
        "arkworks/matrix.column_dot",
        "dalek/matrix.column_dot",
        "plonky3/matrix.column_dot",
    ]),
    Contract::selectable(
        "matrix.get",
        (&[Matrix, Index, Index], &[Field], AttributeRule::None),
    )
    .implemented_by(&[
        "arkworks/matrix.get",
        "dalek/matrix.get",
        "plonky3/matrix.get",
    ]),
    Contract::selectable(
        "matrix.mul_vector",
        (&[Matrix, Vector], &[Vector], AttributeRule::None),
    )
    .implemented_by(&[
        "arkworks/matrix.mul_vector",
        "dalek/matrix.mul_vector",
        "plonky3/matrix.mul_vector",
    ]),
    Contract::selectable(
        "matrix.transpose_mul_vector",
        (&[Matrix, Vector], &[Vector], AttributeRule::None),
    )
    .implemented_by(&[
        "arkworks/matrix.transpose_mul_vector",
        "dalek/matrix.transpose_mul_vector",
        "plonky3/matrix.transpose_mul_vector",
    ]),
    Contract::selectable(
        "matrix.bilinear",
        (&[Matrix, Vector, Vector], &[Field], AttributeRule::None),
    )
    .implemented_by(&[
        "arkworks/matrix.bilinear",
        "dalek/matrix.bilinear",
        "plonky3/matrix.bilinear",
    ]),
    Contract::selectable(
        "matrix.identity_check",
        (&[Matrix], &[Bool], AttributeRule::MatrixIdentity),
    )
    .implemented_by(&[
        "arkworks/matrix.identity_check",
        "dalek/matrix.identity_check",
        "plonky3/matrix.identity_check",
    ]),
    Contract::selectable(
        "matrix.dimension",
        (&[Matrix], &[Index], AttributeRule::Unsigned64),
    )
    .implemented_by(&[
        "arkworks/matrix.dimension",
        "dalek/matrix.dimension",
        "plonky3/matrix.dimension",
    ]),
    Contract::selectable(
        "matrix.shape_check",
        (&[Matrix], &[Bool], AttributeRule::MatrixDimensions),
    )
    .implemented_by(&[
        "arkworks/matrix.shape_check",
        "dalek/matrix.shape_check",
        "plonky3/matrix.shape_check",
    ]),
];
pub(super) const CONTRIBUTION: Contribution = Contribution {
    alternatives: &[],
    physical_error: "uninstalled operation binding",
    physical_only: false,

    contracts: CONTRACTS,
    resolve: support::field_signature,
    select: support::select_nominal,
};
