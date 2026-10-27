//! Independently authored quotient-ring operation contracts.
use super::*;
use Type::*;

const CONTRACTS: &[Contract] = &[
    Contract::new(
        "quotient.prepare_matrix",
        (
            &[Indices, Index, Index, Index, Index, Index],
            &[QuotientMatrix],
            AttributeRule::None,
        ),
    )
    .implemented_by(&["native/quotient.prepare_matrix"]),
    Contract::new(
        "quotient.matvec",
        (&[QuotientMatrix, Indices], &[Indices], AttributeRule::None),
    )
    .implemented_by(&["native/quotient.matvec"]),
    Contract::new(
        "quotient.project",
        (&[Indices, Index, Index], &[Indices], AttributeRule::None),
    )
    .implemented_by(&["native/quotient.project"]),
    Contract::new(
        "quotient.ntt",
        (&[Indices, Index, Index], &[Indices], AttributeRule::None),
    )
    .implemented_by(&["native/quotient.ntt"]),
    Contract::new(
        "quotient.intt",
        (&[Indices, Index, Index], &[Indices], AttributeRule::None),
    )
    .implemented_by(&["native/quotient.intt"]),
    Contract::new(
        "quotient.pointwise",
        (&[Indices, Indices, Index], &[Indices], AttributeRule::None),
    )
    .implemented_by(&["native/quotient.pointwise"]),
    Contract::new(
        "quotient.add",
        (&[Indices, Indices, Index], &[Indices], AttributeRule::None),
    )
    .implemented_by(&["native/quotient.add"]),
    Contract::new(
        "quotient.subtract",
        (&[Indices, Indices, Index], &[Indices], AttributeRule::None),
    )
    .implemented_by(&["native/quotient.subtract"]),
    Contract::new(
        "quotient.multiply",
        (&[Indices, Indices, Index], &[Indices], AttributeRule::None),
    )
    .implemented_by(&["native/quotient.multiply"]),
    Contract::new(
        "quotient.norm_within",
        (
            &[Indices, Indices, Index, Index],
            &[Bool],
            AttributeRule::None,
        ),
    )
    .implemented_by(&["native/quotient.norm_within"]),
];

pub(super) const CONTRIBUTION: Contribution = Contribution {
    alternatives: &[],
    physical_error: "uninstalled operation binding",
    physical_only: false,
    contracts: CONTRACTS,
    resolve: index::resolve,
    select: default_ports,
};
