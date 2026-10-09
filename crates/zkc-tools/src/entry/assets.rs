//! Compiler-visible expression assets carried by an authenticated package.
//!
//! The package pins asset bodies by content identity. This module admits those
//! bodies through the independent ring reader and registry, then checks that
//! every asset-naming operation the admitted native program can reach names an
//! admitted asset in a compatible carrier field. Both checks happen before an
//! invocation issues inputs or resources, and independently of which branches
//! or loop trips a later execution takes. The resulting registry is the only
//! evaluator source for the Entry's native Hosts.
use super::Package;
use std::sync::Arc;
use zkc_backends::ring::Registry;
use zkc_runtime::{
    interactive::{Admitted, AssetReference, Type},
    ring::Expression,
};

type Result<T> = std::result::Result<T, String>;

/// Admitted packaged assets and the static program references they satisfy.
pub struct EntryAssets {
    registry: Registry,
    references: Vec<AssetReference>,
}
impl EntryAssets {
    pub(super) fn admit(package: &Package, admitted: &Admitted, entry: &str) -> Result<Self> {
        let mut registry = Registry::default();
        for asset in package.assets() {
            registry
                .insert(asset.expected_sha256(), asset.body())
                .map_err(|e| e.to_string())?;
            let expression = registry
                .expression(asset.expected_sha256())
                .expect("inserted under its checked identity");
            // One representation per package: the retained body is exactly
            // the canonical text whose digest the program references.
            if expression.canonical() != asset.body() {
                return Err("entry-asset-canonical".into());
            }
        }
        let references = admitted
            .asset_references(entry)
            .map_err(|_| "entry-asset-references")?;
        for reference in &references {
            check(&registry, reference)?;
        }
        Ok(Self {
            registry,
            references,
        })
    }
    /// Admitted content identities in ascending order, including assets that
    /// no reachable operation references.
    pub fn identities(&self) -> impl ExactSizeIterator<Item = &str> {
        self.registry.identities()
    }
    pub fn expression(&self, identity: &str) -> Option<Arc<Expression>> {
        self.registry.expression(identity)
    }
    /// Every asset-naming operation reachable from the Entry's native program,
    /// each already checked against the admitted assets.
    pub fn references(&self) -> &[AssetReference] {
        &self.references
    }
    /// The immutable registry installed into this Entry's native Hosts.
    pub fn registry(&self) -> &Registry {
        &self.registry
    }
}

/// Each asset family owns its reference rule. A ring operation substitutes its
/// arena over the field of its first vector operand, so that field is the
/// carrier the arena must be interpretable in.
fn check(registry: &Registry, reference: &AssetReference) -> Result<()> {
    match reference.binding.declaration().contract.as_str() {
        "ring.point" | "ring.rows" | "ring.coefficients" | "ring.affine_sum" => {
            let carrier = reference
                .binding
                .signature()
                .inputs
                .first()
                .filter(|ty| ty.kind() == Type::Vector)
                .map(|ty| ty.logical().identity())
                .ok_or("entry-asset-contract")?;
            registry
                .check_reference(&reference.identity, carrier)
                .map_err(|e| match e.code.as_str() {
                    "refused:ring-asset-missing" => "entry-asset-missing".to_owned(),
                    "refused:ring-carrier" => "entry-asset-carrier".to_owned(),
                    _ => e.to_string(),
                })
        }
        _ => Err("entry-asset-contract".into()),
    }
}

#[cfg(test)]
mod tests;
