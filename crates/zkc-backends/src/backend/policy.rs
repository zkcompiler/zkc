//! Explicit host-selected entry constraints.
use crate::{Domain, Value};
use std::collections::BTreeMap;
use zkc_arkworks::Metadata;

/// Explicit host policy. Exact pins compare complete public values by canonical
/// encoding. LocalOnly deliberately makes no cross-role public-input claim.
#[derive(Clone, Debug)]
pub enum PublicInputs {
    LocalOnly,
    Exact(BTreeMap<String, Value>),
}
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
    pub parameters: BTreeMap<String, u64>,
    pub public_inputs: PublicInputs,
    /// Host-selected constraints for named entry operands. A setup fingerprint
    /// constrains an already authorized key; it does not authorize new material.
    pub ports: BTreeMap<String, PortConstraint>,
}
impl EntryPolicy {
    pub fn new(domain: Domain, arity: Option<usize>, public_inputs: PublicInputs) -> Self {
        Self {
            domain,
            arity,
            parameters: BTreeMap::new(),
            public_inputs,
            ports: BTreeMap::new(),
        }
    }
    pub fn with_parameters(mut self, parameters: BTreeMap<String, u64>) -> Self {
        self.parameters = parameters;
        self
    }
    pub fn with_ports(mut self, ports: BTreeMap<String, PortConstraint>) -> Self {
        self.ports = ports;
        self
    }
}
