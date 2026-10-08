//! Explicit host-selected entry constraints.
use crate::Domain;
use std::collections::BTreeMap;
use zkc_arkworks::Metadata;

#[derive(Clone, Debug)]
pub struct PortConstraint {
    pub arity: Option<usize>,
    pub setup: Option<Metadata>,
}
#[derive(Clone, Debug)]
pub struct EntryPolicy {
    pub domain: Domain,
    /// Optional homogeneous entry shape, selected by the host. Parameter names
    /// never acquire implicit mathematical meaning at the backend boundary.
    pub arity: Option<usize>,
    /// Host-selected constraints for named entry operands. A setup fingerprint
    /// constrains an already authorized key; it does not authorize new material.
    pub ports: BTreeMap<String, PortConstraint>,
}
impl EntryPolicy {
    pub fn new(domain: Domain, arity: Option<usize>) -> Self {
        Self {
            domain,
            arity,
            ports: BTreeMap::new(),
        }
    }
    pub fn with_ports(mut self, ports: BTreeMap<String, PortConstraint>) -> Self {
        self.ports = ports;
        self
    }
}
