//! One source-owned ordering for argument adapters and native ABI comparison.
//! This view contains no native artifact facts and confers no setup authority.
use super::syntax::Leaf;
use super::{Interface, InterfaceError as E, Result, raw, validate};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Debug)]
pub(in crate::entry) struct RolePorts {
    pub name: String,
    pub native_name: String,
    pub inputs: Vec<usize>,
    pub outputs: Vec<usize>,
    pub services: Vec<usize>,
}
#[derive(Clone, Debug)]
pub(in crate::entry) struct ProofPorts {
    pub prover: usize,
    pub verifier: usize,
    #[cfg(feature = "cpu")]
    pub acceptance: usize,
    #[cfg(any(feature = "cpu", test))]
    pub completion: Option<usize>,
    pub suite: Option<String>,
    #[cfg(feature = "cpu")]
    pub construction: Option<String>,
    #[cfg(feature = "cpu")]
    pub gates: Vec<(String, u8)>,
    pub format: zkc_format::proof::ProofFormat,
    pub replaced_services: Vec<usize>,
}
#[derive(Clone, Copy, Debug, Default)]
struct Input {
    key: Option<&'static str>,
    /// Offset and length in the native public argument vector, including units.
    public: Option<(usize, usize)>,
}
#[derive(Debug)]
pub(super) struct Ports {
    pub roles: Vec<RolePorts>,
    pub public: Vec<usize>,
    pub proof: Option<ProofPorts>,
    inputs: Vec<Input>,
}
/// A checked input's definition and its already resolved source of supply.
#[derive(Clone, Copy)]
pub(in crate::entry) struct InputPort<'a> {
    pub definition: &'a raw::Port,
    pub key: Option<&'static str>,
    pub public: Option<(usize, usize)>,
}
impl std::ops::Deref for InputPort<'_> {
    type Target = raw::Port;
    fn deref(&self) -> &Self::Target {
        self.definition
    }
}
impl InputPort<'_> {
    pub fn named(&self) -> bool {
        self.key != Some("verifier_key")
    }
    pub fn private(&self) -> bool {
        self.named() && self.public.is_none()
    }
}
impl Ports {
    pub fn new(
        document: &raw::Interface,
        selected: usize,
        types: &BTreeMap<String, Leaf>,
        setups: &[super::Setup],
    ) -> Result<Self> {
        let protocol = &document.protocols[selected];
        let indices: BTreeMap<_, _> = protocol
            .roles
            .iter()
            .enumerate()
            .map(|(i, name)| (name.as_str(), i))
            .collect();
        let mut roles: Vec<_> = protocol
            .roles
            .iter()
            .enumerate()
            .map(|(index, name)| RolePorts {
                native_name: crate::source_names::native_role_name(index as u32),
                name: name.clone(),
                inputs: Vec::new(),
                outputs: Vec::new(),
                services: Vec::new(),
            })
            .collect();
        let slots: BTreeSet<_> = setups
            .iter()
            .flat_map(|s| s.inputs.iter().copied())
            .collect();
        let mut inputs = Vec::new();
        for (i, port) in protocol.inputs.iter().enumerate() {
            for role in &port.roles {
                roles[indices[role.as_str()]].inputs.push(i);
            }
            let key = if port.schema.kind == raw::Kind::Builtin
                && !port.schema.custody
                && port.native.len() == 1
                && slots.contains(&(port.native[0] as usize))
            {
                let kind = types[&port.schema.leaves[0]].head;
                matches!(kind, "verifier_key" | "prover_key").then_some(kind)
            } else {
                None
            };
            inputs.push(Input { key, public: None });
        }
        for (i, port) in protocol.outputs.iter().enumerate() {
            for role in &port.roles {
                roles[indices[role.as_str()]].outputs.push(i);
            }
        }
        let mut public_ports = Vec::new();
        let proof = match &document.job {
            raw::Job::Run {} => None,
            raw::Job::Proof {
                prover,
                verifier,
                public,
                acceptance,
                completion,
                construction,
                gates: _gates,
                ..
            } => {
                let mut offset = 0;
                for &i in public {
                    let i = i as usize;
                    // Public statement data cannot import private key custody.
                    super::require(inputs[i].key != Some("prover_key"), E::Selection)?;
                    let len = protocol.inputs[i].native.len();
                    inputs[i].public = Some((offset, len));
                    offset += len;
                    public_ports.push(i);
                }
                let (suite, replaced_services, format, _selected) = match construction.as_ref() {
                    raw::Construction::Authored { format } => (None, Vec::new(), *format, None),
                    raw::Construction::FiatShamir {
                        suite,
                        services,
                        format,
                    } => (
                        Some(suite.clone()),
                        services.iter().map(|&s| s as usize).collect(),
                        *format,
                        None,
                    ),
                    raw::Construction::Derived {
                        symbol,
                        suite,
                        services,
                        format,
                    } => (
                        suite.clone(),
                        services.iter().map(|&s| s as usize).collect(),
                        *format,
                        Some(symbol.clone()),
                    ),
                };
                let _acceptance = validate::select(protocol, acceptance)?.1[0] as usize;
                let _completion = completion
                    .as_ref()
                    .map(|s| validate::select(protocol, s).map(|(_, n)| n[0] as usize))
                    .transpose()?;
                Some(ProofPorts {
                    prover: indices[prover.as_str()],
                    verifier: indices[verifier.as_str()],
                    #[cfg(feature = "cpu")]
                    acceptance: _acceptance,
                    #[cfg(any(feature = "cpu", test))]
                    completion: _completion,
                    suite,
                    #[cfg(feature = "cpu")]
                    construction: _selected,
                    #[cfg(feature = "cpu")]
                    gates: _gates
                        .iter()
                        .map(|gate| {
                            (
                                crate::source_names::native_site_path(&gate.path),
                                gate.bits as u8,
                            )
                        })
                        .collect(),
                    format,
                    replaced_services,
                })
            }
        };
        for (i, service) in protocol.services.iter().enumerate() {
            if !proof
                .as_ref()
                .is_some_and(|p| p.replaced_services.contains(&i))
            {
                roles[indices[service.owner.as_str()]].services.push(i);
            }
        }
        Ok(Self {
            roles,
            public: public_ports,
            proof,
            inputs,
        })
    }
}
impl Interface {
    /// Source/native role names without exposing deployment port internals.
    pub fn role_names(&self) -> impl Iterator<Item = (&str, &str)> {
        self.ports
            .roles
            .iter()
            .map(|role| (role.native_name.as_str(), role.name.as_str()))
    }
    #[cfg(feature = "cpu")]
    pub fn proof_role(&self, operation: crate::entry::ProofOperation) -> Option<&str> {
        let proof = self.proof()?;
        let index = match operation {
            crate::entry::ProofOperation::Prove => proof.prover,
            crate::entry::ProofOperation::Verify => proof.verifier,
        };
        Some(&self.roles()[index].name)
    }
    /// Whether this interface requires explicit permission for authored binding.
    pub fn requires_authored_binding(&self) -> bool {
        self.proof().is_some_and(|proof| proof.suite.is_none())
    }
    pub(in crate::entry) fn roles(&self) -> &[RolePorts] {
        &self.ports.roles
    }

    pub(in crate::entry) fn proof(&self) -> Option<&ProofPorts> {
        self.ports.proof.as_ref()
    }
    pub(in crate::entry) fn input(&self, index: usize) -> InputPort<'_> {
        let facts = self.ports.inputs[index];
        InputPort {
            definition: &self.selected_protocol().inputs[index],
            key: facts.key,
            public: facts.public,
        }
    }
    pub(in crate::entry) fn input_ports<'a>(
        &'a self,
        role: &'a RolePorts,
    ) -> impl Iterator<Item = InputPort<'a>> {
        role.inputs.iter().map(|&i| self.input(i))
    }
    /// Authority-bearing setup inputs are application context, never fields of
    /// generated source constructors. Verifier keys use the separate slot map.
    pub(in crate::entry) fn is_source_data(&self, p: InputPort<'_>) -> bool {
        p.key.is_none()
            && !self
                .setups
                .iter()
                .any(|s| p.native.iter().any(|i| s.inputs.contains(&(*i as usize))))
    }
    pub(in crate::entry) fn context_ports<'a>(
        &'a self,
        role: &'a RolePorts,
    ) -> impl Iterator<Item = InputPort<'a>> {
        self.input_ports(role)
            .filter(|p| !self.is_source_data(*p) && p.key != Some("verifier_key"))
    }
    pub(in crate::entry) fn named_inputs<'a>(
        &'a self,
        role: &'a RolePorts,
    ) -> impl Iterator<Item = InputPort<'a>> {
        self.input_ports(role).filter(InputPort::private)
    }
    pub(in crate::entry) fn public_ports(&self) -> impl Iterator<Item = InputPort<'_>> {
        self.ports.public.iter().map(|&i| self.input(i))
    }
    pub(in crate::entry) fn output_ports<'a>(
        &'a self,
        role: &'a RolePorts,
    ) -> impl Iterator<Item = &'a raw::Port> {
        role.outputs
            .iter()
            .map(|&i| &self.selected_protocol().outputs[i])
    }
    pub(in crate::entry) fn services<'a>(
        &'a self,
        role: &'a RolePorts,
    ) -> impl Iterator<Item = &'a raw::Service> {
        role.services
            .iter()
            .map(|&i| &self.selected_protocol().services[i])
    }
}
