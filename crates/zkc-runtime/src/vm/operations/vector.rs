//! Installed vector operation implementations and physical policy.
use super::*;

pub(super) const CONTRACTS: &[Installation] = &[
    Installation::selectable("multilinear.restrict_prefix").implemented_by(&[
        "arkworks/multilinear.restrict_prefix",
        "dalek/multilinear.restrict_prefix",
        "plonky3/multilinear.restrict_prefix",
    ]),
    Installation::selectable("vector.find_last").implemented_by(&[
        "arkworks/vector.find_last",
        "dalek/vector.find_last",
        "plonky3/vector.find_last",
    ]),
    Installation::selectable("vector.get").implemented_by(&[
        "arkworks/vector.get",
        "dalek/vector.get",
        "plonky3/vector.get",
    ]),
    Installation::selectable("vector.slice").implemented_by(&[
        "arkworks/vector.slice",
        "dalek/vector.slice",
        "plonky3/vector.slice",
    ]),
    Installation::selectable("vector.transpose").implemented_by(&[
        "arkworks/vector.transpose",
        "dalek/vector.transpose",
        "plonky3/vector.transpose",
    ]),
    Installation::selectable("vector.length").implemented_by(&[
        "arkworks/vector.length",
        "dalek/vector.length",
        "plonky3/vector.length",
    ]),
    Installation::selectable("vector.rotate").implemented_by(&[
        "arkworks/vector.rotate",
        "dalek/vector.rotate",
        "plonky3/vector.rotate",
    ]),
    Installation::selectable("vector.bit_reverse").implemented_by(&[
        "arkworks/vector.bit_reverse",
        "dalek/vector.bit_reverse",
        "plonky3/vector.bit_reverse",
    ]),
    Installation::selectable("vector.bit_reverse_rows").implemented_by(&[
        "arkworks/vector.bit_reverse_rows",
        "dalek/vector.bit_reverse_rows",
        "plonky3/vector.bit_reverse_rows",
    ]),
    Installation::selectable("vector.interleave").implemented_by(&[
        "arkworks/vector.interleave",
        "dalek/vector.interleave",
        "plonky3/vector.interleave",
    ]),
    Installation::selectable("vector.prefix_product").implemented_by(&[
        "arkworks/vector.prefix_product",
        "dalek/vector.prefix_product",
        "plonky3/vector.prefix_product",
    ]),
    Installation::selectable("vector.prefix_sum").implemented_by(&[
        "arkworks/vector.prefix_sum",
        "dalek/vector.prefix_sum",
        "plonky3/vector.prefix_sum",
    ]),
    Installation::selectable("vector.inverse").implemented_by(&[
        "arkworks/vector.inverse",
        "dalek/vector.inverse",
        "plonky3/vector.inverse",
    ]),
    Installation::new("vector.embed").implemented_by(&["plonky3/vector.embed"]),
    Installation::selectable("vector.fill").implemented_by(&[
        "arkworks/vector.fill",
        "dalek/vector.fill",
        "plonky3/vector.fill",
    ]),
    Installation::selectable("vector.geometric").implemented_by(&[
        "arkworks/vector.geometric",
        "dalek/vector.geometric",
        "plonky3/vector.geometric",
    ]),
    Installation::selectable("vector.constant").implemented_by(&[
        "arkworks/vector.constant",
        "dalek/vector.constant",
        "plonky3/vector.constant",
    ]),
    Installation::selectable("vector.scatter_sum").implemented_by(&[
        "arkworks/vector.scatter_sum",
        "dalek/vector.scatter_sum",
        "plonky3/vector.scatter_sum",
    ]),
    Installation::selectable("vector.empty").implemented_by(&[
        "arkworks/vector.empty",
        "dalek/vector.empty",
        "plonky3/vector.empty",
    ]),
    Installation::selectable("vector.append").implemented_by(&[
        "arkworks/vector.append",
        "dalek/vector.append",
        "plonky3/vector.append",
    ]),
    Installation::selectable("vector.splat").implemented_by(&[
        "arkworks/vector.splat",
        "dalek/vector.splat",
        "plonky3/vector.splat",
    ]),
    Installation::selectable("vector.powers").implemented_by(&[
        "arkworks/vector.powers",
        "dalek/vector.powers",
        "plonky3/vector.powers",
    ]),
    Installation::selectable("vector.equal").implemented_by(&[
        "arkworks/vector.equal",
        "dalek/vector.equal",
        "plonky3/vector.equal",
    ]),
    Installation::selectable("vector.add").implemented_by(&[
        "arkworks/vector.add",
        "dalek/vector.add",
        "plonky3/vector.add",
    ]),
    Installation::selectable("vector.sub").implemented_by(&[
        "arkworks/vector.sub",
        "dalek/vector.sub",
        "plonky3/vector.sub",
    ]),
    Installation::selectable("vector.mul").implemented_by(&[
        "arkworks/vector.mul",
        "dalek/vector.mul",
        "plonky3/vector.mul",
    ]),
    Installation::selectable("vector.concat").implemented_by(&[
        "arkworks/vector.concat",
        "dalek/vector.concat",
        "plonky3/vector.concat",
    ]),
    Installation::selectable("vector.kronecker").implemented_by(&[
        "arkworks/vector.kronecker",
        "dalek/vector.kronecker",
        "plonky3/vector.kronecker",
    ]),
    Installation::selectable("vector.scale").implemented_by(&[
        "arkworks/vector.scale",
        "dalek/vector.scale",
        "plonky3/vector.scale",
    ]),
    Installation::selectable("vector.sum").implemented_by(&[
        "arkworks/vector.sum",
        "dalek/vector.sum",
        "plonky3/vector.sum",
    ]),
    Installation::selectable("vector.product").implemented_by(&[
        "arkworks/vector.product",
        "dalek/vector.product",
        "plonky3/vector.product",
    ]),
    Installation::selectable("vector.dot").implemented_by(&[
        "arkworks/vector.dot",
        "dalek/vector.dot",
        "plonky3/vector.dot",
    ]),
    Installation::selectable("vector.split").implemented_by(&[
        "arkworks/vector.split",
        "dalek/vector.split",
        "plonky3/vector.split",
    ]),
    Installation::selectable("vector.at").implemented_by(&[
        "arkworks/vector.at",
        "dalek/vector.at",
        "plonky3/vector.at",
    ]),
    Installation::selectable("vector.length_check").implemented_by(&[
        "arkworks/vector.length_check",
        "dalek/vector.length_check",
        "plonky3/vector.length_check",
    ]),
    Installation::selectable("vector.gather").implemented_by(&[
        "arkworks/vector.gather",
        "dalek/vector.gather",
        "plonky3/vector.gather",
    ]),
    Installation::selectable("vector.matvec").implemented_by(&[
        "arkworks/vector.matvec",
        "dalek/vector.matvec",
        "plonky3/vector.matvec",
    ]),
    Installation::selectable("vector.from_point").implemented_by(&["arkworks/vector.from_point"]),
    Installation::selectable("vector.to_point").implemented_by(&["arkworks/vector.to_point"]),
    Installation::selectable("vector.from_table").implemented_by(&["arkworks/vector.from_table"]),
    Installation::selectable("vector.to_table").implemented_by(&["arkworks/vector.to_table"]),
];
pub(super) const CONTRIBUTION: Contribution = Contribution {
    alternatives: ALTERNATIVES,
    physical_error: "uninstalled operation binding",
    adapter: None,

    contracts: CONTRACTS,

    select: support::select_nominal,
};

use super::super::Representation;
use super::super::domain_bindings::PortTransform;
const ALTERNATIVES: &[Alternative] = &[
    Alternative {
        timing: TimingRequirement::Unspecified,
        implementation: "arkworks-msb/vector.from_table",
        contract: "vector.from_table",
        domains: &[Identity::Bls12381Fr],
        ports: PortTransform::Msb,
    },
    Alternative {
        timing: TimingRequirement::Unspecified,
        implementation: "arkworks-msb/vector.to_table",
        contract: "vector.to_table",
        domains: &[Identity::Bls12381Fr],
        ports: PortTransform::Msb,
    },
    Alternative {
        timing: TimingRequirement::Unspecified,
        implementation: "arkworks-diagonal/vector.mul",
        contract: "vector.mul",
        domains: &[Identity::Bls12381Fr],
        ports: PortTransform::Diagonal {
            output: true,
            port: 0,
            representation: Representation::FrDiagonal,
        },
    },
    Alternative {
        timing: TimingRequirement::Unspecified,
        implementation: "arkworks-diagonal/vector.dot",
        contract: "vector.dot",
        domains: &[Identity::Bls12381Fr],
        ports: PortTransform::Diagonal {
            output: false,
            port: 1,
            representation: Representation::FrDiagonal,
        },
    },
    Alternative {
        timing: TimingRequirement::Unspecified,
        implementation: "arkworks-pairwise/vector.dot",
        contract: "vector.dot",
        domains: &[Identity::Bls12381Fr],
        ports: PortTransform::Default,
    },
];
