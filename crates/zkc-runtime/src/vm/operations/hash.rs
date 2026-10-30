//! Copyable hash snapshots; these operations do not own sampling authority.
use super::*;
pub(super) const CONTRACTS: &[Installation] = &[
    Installation::new("hash.keccak256").implemented_by(&["native/hash.keccak256"]),
    Installation::new("hash.sha256").implemented_by(&["native/hash.sha256"]),
    Installation::new("hash.poseidon2_16").implemented_by(&["plonky3/hash.poseidon2_16"]),
    Installation::new("shake128.init").implemented_by(&["native/shake128.init"]),
    Installation::new("shake128.absorb").implemented_by(&["native/shake128.absorb"]),
    Installation::new("shake128.squeeze").implemented_by(&["native/shake128.squeeze"]),
];
pub(super) const CONTRIBUTION: Contribution = Contribution {
    alternatives: &[],
    physical_error: "uninstalled hash operation binding",
    contracts: CONTRACTS,

    select,
};

/// Field permutations take their field as the one domain argument; byte hashes
/// and snapshots take none.
const FIELD_PERMUTATIONS: &[&str] = &["hash.poseidon2_16"];

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
