//! Installed matrix operation implementations and physical policy.
use super::*;

pub(super) const CONTRACTS: &[Installation] = &[
    Installation::selectable("matrix.row_dot").implemented_by(&[
        "arkworks/matrix.row_dot",
        "dalek/matrix.row_dot",
        "plonky3/matrix.row_dot",
    ]),
    Installation::selectable("matrix.column_dot").implemented_by(&[
        "arkworks/matrix.column_dot",
        "dalek/matrix.column_dot",
        "plonky3/matrix.column_dot",
    ]),
    Installation::selectable("matrix.get").implemented_by(&[
        "arkworks/matrix.get",
        "dalek/matrix.get",
        "plonky3/matrix.get",
    ]),
    Installation::selectable("matrix.mul_vector").implemented_by(&[
        "arkworks/matrix.mul_vector",
        "dalek/matrix.mul_vector",
        "plonky3/matrix.mul_vector",
    ]),
    Installation::selectable("matrix.transpose_mul_vector").implemented_by(&[
        "arkworks/matrix.transpose_mul_vector",
        "dalek/matrix.transpose_mul_vector",
        "plonky3/matrix.transpose_mul_vector",
    ]),
    Installation::selectable("matrix.bilinear").implemented_by(&[
        "arkworks/matrix.bilinear",
        "dalek/matrix.bilinear",
        "plonky3/matrix.bilinear",
    ]),
    Installation::selectable("matrix.identity_check").implemented_by(&[
        "arkworks/matrix.identity_check",
        "dalek/matrix.identity_check",
        "plonky3/matrix.identity_check",
    ]),
    Installation::selectable("matrix.dimension").implemented_by(&[
        "arkworks/matrix.dimension",
        "dalek/matrix.dimension",
        "plonky3/matrix.dimension",
    ]),
    Installation::selectable("matrix.shape_check").implemented_by(&[
        "arkworks/matrix.shape_check",
        "dalek/matrix.shape_check",
        "plonky3/matrix.shape_check",
    ]),
];
pub(super) const CONTRIBUTION: Contribution = Contribution {
    alternatives: &[],
    physical_error: "uninstalled operation binding",

    contracts: CONTRACTS,

    select: support::select_nominal,
};
