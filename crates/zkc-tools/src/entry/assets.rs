//! Compiler-visible expression assets carried by an authenticated package.
//!
//! The package pins asset bodies by content identity. This module admits those
//! bodies through independent Ring and Bundle readers and registries, then checks that
//! every asset-naming operation the admitted native program can reach names an
//! admitted asset in a compatible carrier field. Both checks happen before an
//! invocation issues inputs or resources, and independently of which branches
//! or loop trips a later execution takes. The resulting registry is the only
//! evaluator source for the Entry's native Hosts.
use super::interface::raw::Definition;
use super::{Interface, Package};
use std::sync::Arc;
use zkc_backends::{relation::Registry as RelationRegistry, ring::Registry};
use zkc_runtime::{
    interactive::{Admitted, AssetReference, Identity, Type},
    relation::Bundle,
    ring::Expression,
};
mod bundle;

type Result<T> = std::result::Result<T, String>;

/// Admitted packaged assets and the static program references they satisfy.
pub struct EntryAssets {
    registry: Registry,
    relations: RelationRegistry,
    identities: Vec<String>,
    references: Vec<AssetReference>,
}
impl EntryAssets {
    pub(super) fn admit(
        package: &Package,
        interface: &Interface,
        admitted: &Admitted,
        entry: &str,
    ) -> Result<Self> {
        let mut registry = Registry::default();
        let mut relations = RelationRegistry::default();
        let mut identities = Vec::new();
        for asset in package.assets() {
            // Only the exact current canonical carriers are published. The
            // selected family's bounded reader validates the complete body.
            let head = asset
                .body()
                .trim_start()
                .strip_prefix('[')
                .map(str::trim_start)
                .ok_or("entry-asset-format")?;
            let canonical = if head.starts_with("\"zkc.ring/0\"") {
                registry
                    .insert(asset.expected_sha256(), asset.body())
                    .map_err(|e| e.to_string())?;
                registry
                    .expression(asset.expected_sha256())
                    .expect("inserted under its checked identity")
                    .canonical()
            } else if head.starts_with("\"zkc.relation-bundle/0\"") {
                relations
                    .insert(asset.expected_sha256(), asset.body())
                    .map_err(|e| e.to_string())?;
                relations
                    .bundle(asset.expected_sha256())
                    .expect("inserted under its checked identity")
                    .encode()
                    .to_string()
            } else {
                return Err("entry-asset-format".into());
            };
            // One representation per package: the retained body is exactly
            // the canonical text whose digest the program references.
            if canonical != asset.body() {
                return Err("entry-asset-canonical".into());
            }
            if registry
                .admitted_bytes()
                .checked_add(relations.admitted_bytes())
                .is_none_or(|bytes| bytes > zkc_backends::ring::REGISTRY_BYTE_LIMIT)
            {
                return Err("entry-assets-bytes".into());
            }
            identities.push(asset.expected_sha256().to_owned());
        }
        // A declaration-only Bundle remains meaningful even when no runtime
        // operation evaluates it. Its contents determine the formal ABI.
        for relation in &interface.document.relations {
            if let Definition::Bundle { asset } = &relation.definition {
                let definition = relations.bundle(asset).ok_or("entry-asset-missing")?;
                bundle::check(&definition, relation)?;
            }
        }
        let references = admitted
            .asset_references(entry)
            .map_err(|_| "entry-asset-references")?;
        let mut checked = std::collections::BTreeSet::new();
        for reference in &references {
            let binding = reference.binding.declaration();
            // Reachability can repeat one immutable reference many times.
            // Scan its asset once per reference rule and closed binding
            // arguments; the polynomial kernels share one rule.
            let rule = match binding.contract.as_str() {
                contract if POLYNOMIAL.contains(&contract) => POLYNOMIAL[0],
                contract => contract,
            };
            if checked.insert((
                rule,
                binding.arguments.as_slice(),
                reference.identity.as_str(),
            )) {
                check(&registry, &relations, reference)?;
            }
        }
        drop(checked);
        Ok(Self {
            registry,
            relations,
            identities,
            references,
        })
    }
    /// Admitted content identities in ascending order, including assets that
    /// no reachable operation references.
    pub fn identities(&self) -> impl ExactSizeIterator<Item = &str> {
        self.identities.iter().map(String::as_str)
    }
    pub fn expression(&self, identity: &str) -> Option<Arc<Expression>> {
        self.registry.expression(identity)
    }
    pub fn bundle(&self, identity: &str) -> Option<Arc<Bundle>> {
        self.relations.bundle(identity)
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
    pub fn relation_registry(&self) -> &RelationRegistry {
        &self.relations
    }
}

/// Contracts of the Bundle polynomial view, which share one reference rule.
const POLYNOMIAL: &[&str] = &[
    "relation.table_shape",
    "relation.table_input",
    "relation.table_scope",
    "relation.table_point",
    "relation.table_points",
];

/// Each asset family owns its reference rule. A ring operation substitutes its
/// arena over the field of its first vector operand, so that field is the
/// carrier the arena must be interpretable in.
fn check(
    registry: &Registry,
    relations: &RelationRegistry,
    reference: &AssetReference,
) -> Result<()> {
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
        "relation.table_rows" => {
            let carrier = reference
                .binding
                .signature()
                .inputs
                .first()
                .filter(|ty| ty.kind() == Type::Vector)
                .map(|ty| ty.logical().identity())
                .ok_or("entry-asset-contract")?;
            let table = reference
                .binding
                .declaration()
                .arguments
                .get(1)
                .and_then(|index| index.parse().ok())
                .ok_or("entry-asset-contract")?;
            relations
                .table_reference(&reference.identity, table, carrier)
                .map(|_| ())
                .map_err(|e| match e.code.as_str() {
                    "refused:relation-asset-missing" => "entry-asset-missing".into(),
                    "refused:relation-table-carrier" => "entry-asset-carrier".into(),
                    _ => e.to_string(),
                })
        }
        // The polynomial kernels take the carrier from their field argument:
        // only the point substitutions have field-valued operands. The check
        // allocates nothing.
        contract if POLYNOMIAL.contains(&contract) => {
            let declaration = reference.binding.declaration();
            let (Some(carrier), Some(table)) = (
                declaration
                    .arguments
                    .first()
                    .and_then(|field| Identity::parse(field).ok()),
                declaration
                    .arguments
                    .get(1)
                    .and_then(|index| index.parse().ok()),
            ) else {
                return Err("entry-asset-contract".into());
            };
            relations
                .polynomial_reference(&reference.identity, table, carrier)
                .map(|_| ())
                .map_err(|e| match e.code.as_str() {
                    "refused:relation-asset-missing" => "entry-asset-missing".into(),
                    "refused:relation-table-carrier" => "entry-asset-carrier".into(),
                    _ => e.to_string(),
                })
        }
        _ => Err("entry-asset-contract".into()),
    }
}

#[cfg(test)]
mod tests;
