//! Declarative container/source item boundary; nothing is absorbed by insertion.
//!
//! A protocol separately authors ordered transition item lists. Container order
//! is metadata and never selects transcript order. Guard references are explicit
//! obligations to the external checker, not evidence of authentication here.
use super::{Error, Result, monero::Word, openvm::validate_field};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ItemValue {
    Words(Vec<Word>),
    Fields(Vec<u32>),
    Opaque(Vec<u8>),
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WireItem {
    pub id: String,
    pub origin: String,
    /// None for external statement/VK data, or an explicitly derived input.
    pub wire_index: Option<usize>,
    pub value: ItemValue,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Unobserved {
    pub item: String,
    /// Identity of the protocol guard that consumes/binds this item.
    pub guard: String,
}
#[derive(Clone, Debug, Default)]
pub struct WireMap {
    items: BTreeMap<String, WireItem>,
}
impl WireMap {
    pub fn new(items: Vec<WireItem>) -> Result<Self> {
        let mut map = Self::default();
        let mut positions = BTreeSet::new();
        for item in items {
            if item.id.is_empty() || item.origin.is_empty() {
                return Err(Error::MalformedReplay);
            }
            if let ItemValue::Fields(fields) = &item.value {
                for &field in fields {
                    validate_field(field)?;
                }
            }
            if item
                .wire_index
                .is_some_and(|index| !positions.insert(index))
                || map.items.contains_key(&item.id)
            {
                return Err(Error::DuplicateIdentity);
            }
            map.items.insert(item.id.clone(), item);
        }
        Ok(map)
    }
    pub fn get(&self, id: &str) -> Result<&WireItem> {
        self.items.get(id).ok_or(Error::MissingItem)
    }
    /// Every declared item is either explicitly used in the authored event list,
    /// or explicitly assigned to an external guard. Repeated observations are
    /// permitted; the selected protocol, not this primitive, decides legality.
    pub fn validate_mapping(&self, observed: &[String], unobserved: &[Unobserved]) -> Result<()> {
        let mut used = BTreeSet::new();
        for id in observed {
            self.get(id)?;
            used.insert(id.as_str());
        }
        let mut omitted = BTreeSet::new();
        for exclusion in unobserved {
            self.get(&exclusion.item)?;
            if exclusion.guard.trim().is_empty() {
                return Err(Error::MissingGuard);
            }
            if used.contains(exclusion.item.as_str()) || !omitted.insert(exclusion.item.as_str()) {
                return Err(Error::ConflictingMapping);
            }
        }
        if self
            .items
            .keys()
            .any(|id| !used.contains(id.as_str()) && !omitted.contains(id.as_str()))
        {
            return Err(Error::UnmappedItem);
        }
        Ok(())
    }
}
