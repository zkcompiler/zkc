//! Immutable CPU provider composition over the compiled contract catalogue.
use std::collections::BTreeSet;
use zkc_runtime::vm::{
    ContractSupport, Contracts, Identity, OperationBinding, PhysicalType, Representation,
    ServiceContract,
};

/// Provider descriptors select compiled implementations; they do not load code.
pub mod providers {
    #[derive(
        Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, serde::Serialize, serde::Deserialize,
    )]
    #[serde(rename_all = "lowercase")]
    pub enum Provider {
        Arkworks,
        Blst,
        Dalek,
        Halo2Curves,
        Plonky3,
    }
    pub use Provider::{Arkworks, Blst, Dalek, Halo2Curves, Plonky3};
}
use providers::Provider;
const ALL: [Provider; 5] = [
    Provider::Arkworks,
    Provider::Blst,
    Provider::Dalek,
    Provider::Halo2Curves,
    Provider::Plonky3,
];

/// Compiler input describing a restrictive installation, never executable authority.
#[derive(Clone, Debug, serde::Serialize)]
pub struct CpuTarget {
    format: &'static str,
    providers: Vec<Provider>,
}

/// Shareable immutable support. Every view preserves the original catalogue's IDs.
#[derive(Clone, Debug)]
pub struct CpuInstallation {
    contracts: Contracts,
    selected: Selection,
}
impl Default for CpuInstallation {
    fn default() -> Self {
        Self {
            contracts: crate::cpu_contracts().clone(),
            selected: Selection(ALL.into()),
        }
    }
}
impl CpuInstallation {
    pub fn standard() -> crate::Result<Self> {
        crate::backend::registry::installed()?;
        Ok(Self::default())
    }
    pub fn builder() -> CpuInstallationBuilder {
        CpuInstallationBuilder::default()
    }
    pub fn contracts(&self) -> &Contracts {
        &self.contracts
    }
    pub fn supports_type(&self, ty: &PhysicalType) -> bool {
        self.contracts.validate_type(ty).is_ok()
    }
    pub fn supports_wire(&self, ty: &PhysicalType) -> bool {
        self.supports_type(ty) && crate::has_native_wire(ty)
    }
    pub fn supports_setup(&self) -> bool {
        self.selected.0.contains(&Provider::Arkworks)
    }
    pub fn target(&self) -> CpuTarget {
        CpuTarget {
            format: "zkc.cpu-target/0",
            providers: self.selected.0.iter().copied().collect(),
        }
    }
    pub(crate) fn supports_service(&self, contract: ServiceContract) -> bool {
        // The root's draw field matters even when an entry only queries indices.
        crate::services::support(contract, "draw").is_some_and(|support| {
            support
                .signature
                .outputs
                .iter()
                .all(|ty| self.supports_type(ty))
        })
    }
    pub(crate) fn is_standard(&self) -> bool {
        self.selected.0.len() == ALL.len()
    }
    pub(crate) fn check_type(&self, ty: &PhysicalType) -> crate::Result<()> {
        if self.is_standard() || self.supports_type(ty) {
            Ok(())
        } else {
            Err(crate::refused("installation-type"))
        }
    }
}

#[derive(Clone, Debug, Default)]
pub struct CpuInstallationBuilder {
    selected: BTreeSet<Provider>,
}
impl CpuInstallationBuilder {
    /// Inclusion is idempotent and independent of declaration order.
    pub fn include(mut self, provider: Provider) -> Self {
        self.selected.insert(provider);
        self
    }
    pub fn finish(self) -> crate::Result<CpuInstallation> {
        crate::backend::registry::installed()?;
        let selected = Selection(self.selected);
        let contracts = if selected.0.len() == ALL.len() {
            crate::cpu_contracts().clone()
        } else {
            crate::cpu_contracts().restricted(selected.clone())
        };
        Ok(CpuInstallation {
            contracts,
            selected,
        })
    }
}
#[derive(Clone, Debug)]
struct Selection(BTreeSet<Provider>);
impl ContractSupport for Selection {
    fn permits_type(&self, ty: &PhysicalType) -> bool {
        // Layout names are compiler-owned closed catalogue facts, validated by
        // Contracts before use. Nominal identity alone cannot authorize storage.
        let name = ty.representation().name();
        let owner = if name.starts_with("arkworks.") {
            Some(Provider::Arkworks)
        } else if name.starts_with("blst.") || name.starts_with("blst/") {
            Some(Provider::Blst)
        } else if name.starts_with("halo2curves") {
            Some(Provider::Halo2Curves)
        } else if name.starts_with("dalek.") {
            Some(Provider::Dalek)
        } else if name.starts_with("plonky3.") {
            Some(Provider::Plonky3)
        } else if ty.representation() == Representation::Resource {
            identity_owner(ty.logical().identity())
        } else {
            None
        };
        owner.is_none_or(|owner| self.0.contains(&owner))
    }
    fn permits_binding(&self, binding: &OperationBinding) -> bool {
        // Exact port layouts are independently checked by Contracts::resolve.
        // Hidden implementation ownership is checked even for zero-arity calls.
        let implementation = binding.implementation.as_str();
        let family = implementation.split('/').next().unwrap_or("");
        let independent_control = matches!(
            binding.contract.as_str(),
            "bool.and" | "bool.or" | "bool.not" | "control.require"
        ) && implementation == format!("arkworks/{}", binding.contract);
        let owner = match family {
            "arkworks" if independent_control => None,
            "arkworks" | "arkworks-msb" | "arkworks-diagonal" | "arkworks-pairwise"
            | "spongefish" => Some(Provider::Arkworks),
            "blst" => Some(Provider::Blst),
            "dalek" | "dalek-diagonal" => Some(Provider::Dalek),
            "halo2curves-axiom" => Some(Provider::Halo2Curves),
            "plonky3" => Some(Provider::Plonky3),
            "native" if binding.contract.starts_with("external.monero.") => Some(Provider::Dalek),
            "native" if binding.contract.starts_with("external.openvm.") => Some(Provider::Plonky3),
            _ => None,
        };
        if owner.is_some_and(|owner| !self.0.contains(&owner)) {
            return false;
        }
        // Some native service/codec families erase their numerical value from
        // the ports. Static domain arguments still retain that dependency.
        if family == "native"
            && binding.arguments.iter().any(|argument| {
                Identity::parse(argument)
                    .ok()
                    .and_then(identity_owner)
                    .is_some_and(|owner| !self.0.contains(&owner))
            })
        {
            return false;
        }
        true
    }
}
fn identity_owner(identity: Identity) -> Option<Provider> {
    use Identity::*;
    match identity {
        None => Option::None,
        Bls12381Fr
        | Bls12381G1
        | Bls12381G2
        | Bls12381Gt
        | MultilinearKzgBls12381
        | Bn254Fr
        | Bn254G1
        | Bn254G2
        | Bn254Gt
        | Merlin3Fr64Be
        | Spongefish080KeccakFr64Be
        | HashChainKeccak256Fr64Be => Some(Provider::Arkworks),
        Ristretto255Scalar | Ristretto255Group | Edwards25519Prime | Merlin3Ristretto64Le => {
            Some(Provider::Dalek)
        }
        _ => Some(Provider::Plonky3),
    }
}
