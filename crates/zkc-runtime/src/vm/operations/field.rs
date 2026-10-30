//! Installed field operation implementations and physical policy.
use super::*;

pub(super) const CONTRACTS: &[Installation] = &[
    Installation::selectable("field.from_index").implemented_by(&[
        "arkworks/field.from_index",
        "dalek/field.from_index",
        "plonky3/field.from_index",
    ]),
    Installation::selectable("field.sub").implemented_by(&[
        "arkworks/field.sub",
        "dalek/field.sub",
        "plonky3/field.sub",
    ]),
    Installation::selectable("field.neg").implemented_by(&[
        "arkworks/field.neg",
        "dalek/field.neg",
        "plonky3/field.neg",
    ]),
    Installation::selectable("field.inverse").implemented_by(&[
        "arkworks/field.inverse",
        "dalek/field.inverse",
        "plonky3/field.inverse",
    ]),
    Installation::new("field.embed").implemented_by(&["plonky3/field.embed"]),
    Installation::selectable("field.constant").implemented_by(&[
        "arkworks/field.constant",
        "dalek/field.constant",
        "plonky3/field.constant",
    ]),
    Installation::selectable("field.add").implemented_by(&[
        "arkworks/field.add",
        "dalek/field.add",
        "plonky3/field.add",
    ]),
    Installation::selectable("field.mul").implemented_by(&[
        "arkworks/field.mul",
        "dalek/field.mul",
        "plonky3/field.mul",
    ]),
    Installation::selectable("field.equal").implemented_by(&[
        "arkworks/field.equal",
        "dalek/field.equal",
        "plonky3/field.equal",
    ]),
];
pub(super) const CONTRIBUTION: Contribution = Contribution {
    alternatives: &[],
    physical_error: "uninstalled operation binding",

    contracts: CONTRACTS,

    select: support::select_nominal,
};
