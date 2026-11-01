//! One strict recursive placement and its redundant, independently checked ABI map.
use serde::Deserialize;

#[derive(Clone, Debug, PartialEq, Eq, Deserialize)]
#[serde(
    remote = "Self",
    tag = "kind",
    rename_all = "snake_case",
    deny_unknown_fields
)]
pub enum Placement {
    Data {
        roles: Vec<u32>,
    },
    Oracle {
        holder: u32,
        receivers: Vec<u32>,
    },
    Product {
        instance: String,
        arguments: Vec<u32>,
        fields: Vec<Placement>,
    },
}
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Deserialize)]
#[serde(remote = "Self", rename_all = "snake_case")]
pub enum Facet {
    Data,
    OracleData,
    OracleAnchor,
    Custody,
}
#[derive(Clone, Debug, PartialEq, Eq, Deserialize)]
#[serde(remote = "Self", deny_unknown_fields)]
pub struct Component {
    pub path: Vec<u32>,
    pub leaf: u32,
    pub role: u32,
    pub facet: Facet,
    pub native: u32,
}
crate::entry::decode::objects!(Placement, Component);
crate::entry::decode::names!(Facet);
