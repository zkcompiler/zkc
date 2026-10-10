//! One source-owned ordering for argument adapters and native ABI comparison.
//! This view contains no native artifact facts and confers no setup authority.
use super::{Interface, InterfaceError as E, Result, raw, validate};
use std::collections::{BTreeMap, BTreeSet};
use zkc_runtime::interactive::{LogicalType, Type};

#[derive(Debug)]
pub(in crate::entry) struct RolePorts {
    pub name: String,
    pub inputs: Vec<usize>,
    pub outputs: Vec<usize>,
    pub services: Vec<usize>,
}
#[derive(Clone, Debug)]
pub(in crate::entry) struct ProofPorts {
    pub prover: usize,
    pub verifier: usize,
    pub acceptance: usize,
    pub completion: Option<usize>,
    pub suite: Option<String>,
    pub transcript: Option<usize>,
}
#[derive(Clone, Copy, Debug, Default)]
struct Input {
    key: Option<Type>,
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
    pub key: Option<Type>,
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
        self.key != Some(Type::VerifierKey)
    }
    pub fn private(&self) -> bool {
        self.named() && self.public.is_none()
    }
}
impl Ports {
    pub fn new(
        document: &raw::Interface,
        selected: usize,
        types: &BTreeMap<String, LogicalType>,
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
            .map(|name| RolePorts {
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
                let kind = types[&port.schema.leaves[0]].kind();
                matches!(kind, Type::VerifierKey | Type::ProverKey).then_some(kind)
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
                ..
            } => {
                let mut offset = 0;
                for &i in public {
                    let i = i as usize;
                    // Public statement data cannot import private key custody.
                    super::require(inputs[i].key != Some(Type::ProverKey), E::Selection)?;
                    let len = protocol.inputs[i].native.len();
                    inputs[i].public = Some((offset, len));
                    offset += len;
                    public_ports.push(i);
                }
                let (suite, transcript) = match construction {
                    raw::Construction::Authored {} => (None, None),
                    raw::Construction::FiatShamir { suite, service } => {
                        (Some(suite.clone()), Some(*service as usize))
                    }
                };
                Some(ProofPorts {
                    prover: indices[prover.as_str()],
                    verifier: indices[verifier.as_str()],
                    acceptance: validate::select(protocol, acceptance)?.1[0] as usize,
                    completion: completion
                        .as_ref()
                        .map(|s| validate::select(protocol, s).map(|(_, n)| n[0] as usize))
                        .transpose()?,
                    suite,
                    transcript,
                })
            }
        };
        for (i, service) in protocol.services.iter().enumerate() {
            if proof.as_ref().and_then(|p| p.transcript) != Some(i) {
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
