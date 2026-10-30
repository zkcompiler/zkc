//! Installed curve operation implementations and physical policy.
use super::*;

pub(super) const CONTRACTS: &[Installation] = &[
    Installation::selectable("curve.identity")
        .implemented_by(&["arkworks/curve.identity", "dalek/curve.identity"]),
    Installation::selectable("curve.neg")
        .implemented_by(&["arkworks/curve.neg", "dalek/curve.neg"]),
    Installation::selectable("curve.nonidentity")
        .implemented_by(&["arkworks/curve.nonidentity", "dalek/curve.nonidentity"]),
    Installation::selectable("curve.msm")
        .implemented_by(&["arkworks/curve.msm", "dalek/curve.msm"]),
    Installation::selectable("curve.scale_each")
        .implemented_by(&["arkworks/curve.scale_each", "dalek/curve.scale_each"]),
    Installation::selectable("curve.vector_add")
        .implemented_by(&["arkworks/curve.vector_add", "dalek/curve.vector_add"]),
    Installation::selectable("curve.concat")
        .implemented_by(&["arkworks/curve.concat", "dalek/curve.concat"]),
    Installation::selectable("curve.vector_scale")
        .implemented_by(&["arkworks/curve.vector_scale", "dalek/curve.vector_scale"]),
    Installation::selectable("curve.split")
        .implemented_by(&["arkworks/curve.split", "dalek/curve.split"]),
    Installation::new("pairing.apply").implemented_by(&["arkworks/pairing.apply"]),
    Installation::selectable("pairing.check").implemented_by(&["arkworks/pairing.check"]),
    Installation::selectable("curve.generator")
        .implemented_by(&["arkworks/curve.generator", "dalek/curve.generator"]),
    Installation::selectable("curve.add")
        .implemented_by(&["arkworks/curve.add", "dalek/curve.add"]),
    Installation::selectable("curve.scale")
        .implemented_by(&["arkworks/curve.scale", "dalek/curve.scale"]),
    Installation::selectable("curve.equal")
        .implemented_by(&["arkworks/curve.equal", "dalek/curve.equal"]),
    Installation::selectable("curve.empty")
        .implemented_by(&["arkworks/curve.empty", "dalek/curve.empty"]),
    Installation::selectable("curve.append")
        .implemented_by(&["arkworks/curve.append", "dalek/curve.append"]),
    Installation::selectable("curve.at").implemented_by(&["arkworks/curve.at", "dalek/curve.at"]),
    Installation::selectable("curve.get")
        .implemented_by(&["arkworks/curve.get", "dalek/curve.get"]),
    Installation::selectable("curve.length")
        .implemented_by(&["arkworks/curve.length", "dalek/curve.length"]),
    Installation::selectable("curve.commit")
        .implemented_by(&["arkworks/curve.commit", "dalek/curve.commit"]),
    Installation::selectable("curve.response")
        .implemented_by(&["arkworks/curve.response", "dalek/curve.response"]),
];
pub(super) const CONTRIBUTION: Contribution = Contribution {
    alternatives: ALTERNATIVES,
    physical_error: "uninstalled operation binding",

    contracts: CONTRACTS,

    select,
};

fn select(
    binding: &OperationBinding,
    logical: &OperationSignature<LogicalType>,
    selection: Selection,
) -> Result<BoundSignature> {
    support::select_nominal(binding, logical, selection)
}

use super::super::Representation;
use super::super::domain_bindings::PortTransform;
const ALTERNATIVES: &[Alternative] = &[
    Alternative {
        timing: TimingRequirement::Unspecified,
        implementation: "dalek-diagonal/curve.scale_each",
        contract: "curve.scale_each",
        domains: &[Identity::Ristretto255Group],
        ports: PortTransform::Diagonal {
            output: true,
            port: 0,
            representation: Representation::RistrettoDiagonal,
        },
    },
    Alternative {
        timing: TimingRequirement::Unspecified,
        implementation: "dalek-diagonal/curve.msm",
        contract: "curve.msm",
        domains: &[Identity::Ristretto255Group],
        ports: PortTransform::Diagonal {
            output: false,
            port: 1,
            representation: Representation::RistrettoDiagonal,
        },
    },
];
