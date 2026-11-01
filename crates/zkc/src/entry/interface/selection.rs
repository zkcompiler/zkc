//! An ordinary child is a bounded supply plan, never whole-root authority.
use super::{Interface, InterfaceError as E, Result, raw::*, require, schemas, validate};

/// A constructible ordinary selection for one exact participant. Supplying this
/// selection does not satisfy any other component of its logical source input.
#[derive(Debug)]
pub struct OrdinaryInput<'a> {
    pub(in crate::entry) interface: &'a Interface,
    port: u32,
    name: Option<&'a str>,
    path: Vec<u32>,
    role: &'a str,
    schema: &'a Schema,
    native: &'a [u32],
}
impl OrdinaryInput<'_> {
    /// Alias in the checked invocation roster, when this exact subtree is a supply item.
    pub fn name(&self) -> Option<&str> {
        self.name
    }
    pub fn port(&self) -> u32 {
        self.port
    }
    pub fn path(&self) -> &[u32] {
        &self.path
    }
    pub fn role(&self) -> &str {
        self.role
    }
    pub fn schema(&self) -> &Schema {
        self.schema
    }
    pub fn requires_setup(&self) -> bool {
        self.schema
            .leaves
            .iter()
            .any(|leaf| self.interface.types[leaf].needs_setup)
    }
    pub fn native(&self) -> &[u32] {
        self.native
    }
}
impl Interface {
    /// Inspect an exact ordinary input selection. This does not admit a logical
    /// root or authorize an invocation with unsupplied handles/custody/siblings.
    pub fn ordinary_input<'a>(
        &'a self,
        port: u32,
        path: &[u32],
        role: &str,
    ) -> Result<OrdinaryInput<'a>> {
        let protocol = self.selected_protocol();
        let index = protocol
            .roles
            .iter()
            .position(|r| r == role)
            .ok_or(E::Selection)?;
        let selected = protocol.inputs.get(port as usize).ok_or(E::Selection)?;
        let (schema, native) = validate::project_role(selected, path, index as u32)?;
        schemas::check_import(schema).map_err(|_| E::Selection)?;
        require(
            schema.leaves.iter().all(|l| self.types[l].message),
            E::Selection,
        )?;
        Ok(OrdinaryInput {
            interface: self,
            port,
            name: self
                .roles()
                .iter()
                .flat_map(|r| self.input_ports(r))
                .find(|p| {
                    p.index == port
                        && p.path == path
                        && self.participants()[p.role as usize] == role
                })
                .map(|p| p.definition.name.as_str()),
            path: path.to_vec(),
            role: &protocol.roles[index],
            schema,
            native,
        })
    }
}

/// Checked source metadata for a complete protocol port. These observations do
/// not supply runtime values, setup authority, or custody/anchor origins.
#[derive(Clone, Copy, Debug)]
pub struct ProtocolPort<'a> {
    pub name: &'a str,
    pub index: u32,
    pub schema: &'a Schema,
    pub placement: &'a Placement,
    pub components: &'a [Component],
    pub native: &'a [u32],
    /// Admission bound for an unsized direct handle; independent of sequence capacity.
    pub maximum_rows: Option<u64>,
}
impl<'a> From<&'a Port> for ProtocolPort<'a> {
    fn from(port: &'a Port) -> Self {
        Self {
            name: &port.name,
            index: port.index,
            schema: &port.schema,
            placement: &port.placement,
            components: &port.components,
            native: &port.native,
            maximum_rows: port
                .maximum_rows
                .get()
                .copied()
                .flatten()
                .map(|bound| bound.0),
        }
    }
}
impl Interface {
    /// Declaration order for interpreting protocol placement/component ordinals.
    pub fn participants(&self) -> &[String] {
        &self.selected_protocol().roles
    }
    pub fn protocol_inputs(&self) -> impl ExactSizeIterator<Item = ProtocolPort<'_>> {
        self.selected_protocol()
            .inputs
            .iter()
            .map(ProtocolPort::from)
    }
    pub fn protocol_outputs(&self) -> impl ExactSizeIterator<Item = ProtocolPort<'_>> {
        self.selected_protocol()
            .outputs
            .iter()
            .map(ProtocolPort::from)
    }
}

impl Interface {
    /// Complete checked ordinary argument roster for one role. Residual authority
    /// is reported separately by outstanding_requirements; this list never admits it.
    pub fn ordinary_inputs<'a>(&'a self, role: &str) -> Result<Vec<OrdinaryInput<'a>>> {
        let index = self
            .participants()
            .iter()
            .position(|r| r == role)
            .ok_or(E::Selection)?;
        self.input_ports(&self.roles()[index])
            .filter(|p| p.key.is_none())
            .map(|p| self.ordinary_input(p.index, p.path, role))
            .collect()
    }
}
