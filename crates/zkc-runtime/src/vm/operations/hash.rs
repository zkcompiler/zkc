//! Copyable hash snapshots; these operations do not own sampling authority.
use super::*;
use Type::*;
pub(super) const CONTRACTS: &[Contract] = &[
    Contract::new("hash.keccak256", (&[Bytes], &[Bytes], AttributeRule::None))
        .implemented_by(&["native/hash.keccak256"]),
    Contract::new("hash.sha256", (&[Bytes], &[Bytes], AttributeRule::None))
        .implemented_by(&["native/hash.sha256"]),
    Contract::new(
        "hash.poseidon2_16",
        (&[Vector], &[Vector], AttributeRule::None),
    )
    .implemented_by(&["plonky3/hash.poseidon2_16"]),
    Contract::new(
        "shake128.init",
        (&[], &[Shake128State], AttributeRule::None),
    )
    .implemented_by(&["native/shake128.init"]),
    Contract::new(
        "shake128.absorb",
        (
            &[Shake128State, Bytes],
            &[Shake128State],
            AttributeRule::None,
        ),
    )
    .implemented_by(&["native/shake128.absorb"])
    .history(),
    Contract::new(
        "shake128.squeeze",
        (
            &[Shake128State, Index],
            &[Shake128State, Bytes],
            AttributeRule::None,
        ),
    )
    .implemented_by(&["native/shake128.squeeze"])
    .history(),
];
pub(super) const CONTRIBUTION: Contribution = Contribution {
    alternatives: &[],
    physical_error: "uninstalled hash operation binding",
    physical_only: false,
    contracts: CONTRACTS,
    resolve,
    select,
};

/// Field permutations take their field as the one domain argument; byte hashes
/// and snapshots take none.
const FIELD_PERMUTATIONS: &[&str] = &["hash.poseidon2_16"];

fn resolve(
    binding: &OperationBinding,
    contract: &Contract,
) -> Result<OperationSignature<LogicalType>> {
    if !FIELD_PERMUTATIONS.contains(&binding.contract.as_str()) {
        return index::resolve(binding, contract);
    }
    // Any installed field forms the logical signature; implementations are
    // selected per field below.
    let field = support::primary(binding)?
        .scalar_field()
        .ok_or_else(support::failure)?;
    support::require_primary(binding, field)?;
    support::instantiate(contract.shape()?, field, |kind| {
        support::field_type(kind, field)
    })
}

fn select(
    binding: &OperationBinding,
    logical: &OperationSignature<LogicalType>,
    selection: Selection,
) -> Result<BoundSignature> {
    if !FIELD_PERMUTATIONS.contains(&binding.contract.as_str()) {
        return default_ports(binding, logical, selection);
    }
    selection.require_default()?;
    // The installed width-16 parameter set is KoalaBear's.
    if support::primary(binding)? != Identity::KoalaBear {
        return Err(support::failure());
    }
    support::select_nominal(binding, logical, selection)
}
