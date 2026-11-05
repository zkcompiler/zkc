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
    /// Semantic public membership, including zero-storage selections.
    public: bool,
}
#[derive(Debug)]
pub(super) struct Ports {
    pub roles: Vec<RolePorts>,
    pub public: Vec<usize>,
    pub proof: Option<ProofPorts>,
    inputs: Vec<Input>,
    views: Vec<super::boundary::View>,
    outputs: Vec<super::boundary::View>,
    pub residual: Vec<super::BoundaryRequirement>,
}
/// A checked input's definition and its already resolved source of supply.
#[derive(Clone, Copy)]
pub(in crate::entry) struct InputPort<'a> {
    pub definition: &'a raw::Port,
    pub path: &'a [u32],
    pub role: u32,
    pub key: Option<&'static str>,
    pub public: bool,
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
        self.named() && !self.public
    }
}
impl Ports {
    pub fn new(
        document: &raw::Interface,
        selected: usize,
        types: &BTreeMap<String, Leaf>,
        setups: &[super::Setup],
        limits: super::InterfaceLimits,
    ) -> Result<Self> {
        Self::with_work(
            document,
            selected,
            types,
            setups,
            &mut super::boundary::Work::new(limits),
        )
    }
    pub(super) fn with_work(
        document: &raw::Interface,
        selected: usize,
        types: &BTreeMap<String, Leaf>,
        setups: &[super::Setup],
        work: &mut super::boundary::Work,
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
        let public = match &document.job {
            raw::Job::Proof { public, .. } => public.as_slice(),
            _ => &[],
        };
        let (views, mut residual) = super::boundary::views(protocol, false, public, setups, work)?;
        let (outputs, output_residual) = super::boundary::views(protocol, true, &[], &[], work)?;
        residual.extend(output_residual);
        // Native and semantic completion are separate checks. Even a fully
        // constructible plan must supply every role-local original coordinate
        // exactly once; shared coordinates belong to separate participants.
        // Views, residual requirements and original components are bucketed
        // by role once, so this check grows with their counts, not with the
        // roster times each of them.
        for (originals, roster, output) in [
            (&protocol.inputs, &views, false),
            (&protocol.outputs, &outputs, true),
        ] {
            let count = protocol.roles.len();
            work.charge(count + roster.len() + residual.len())?;
            let mut supplied = vec![Vec::new(); count];
            for view in roster {
                work.charge(view.definition.native.len())?;
                supplied[view.role as usize].extend(view.definition.native.iter().copied());
            }
            let mut blocked = vec![false; count];
            for requirement in residual.iter().filter(|r| r.output == output) {
                work.lookup(indices.len())?;
                blocked[indices[requirement.role.as_str()]] = true;
            }
            work.charge(originals.iter().map(|p| p.components.len()).sum())?;
            let mut expected = vec![BTreeSet::new(); count];
            for component in originals.iter().flat_map(|p| &p.components) {
                expected[component.role as usize].insert(component.native);
            }
            for (role, supplied) in supplied.iter().enumerate() {
                let unique: BTreeSet<_> = supplied.iter().copied().collect();
                super::require(unique.len() == supplied.len(), E::Schema)?;
                if !blocked[role] {
                    super::require(unique == expected[role], E::Schema)?;
                }
            }
        }
        let mut inputs = Vec::new();
        for (i, view) in views.iter().enumerate() {
            let port = &view.definition;
            roles[view.role as usize].inputs.push(i);
            let key = if port.schema.kind == raw::Kind::Builtin
                && port.native.len() == 1
                && slots.contains(&(port.native[0] as usize))
            {
                let kind = types[&port.schema.leaves[0]].head;
                matches!(kind, "verifier_key" | "prover_key").then_some(kind)
            } else {
                None
            };
            work.charge(1)?;
            let is_public = view.public;
            super::require(!is_public || key != Some("prover_key"), E::Selection)?;
            inputs.push(Input {
                key,
                public: is_public,
            });
        }
        for (i, view) in outputs.iter().enumerate() {
            roles[view.role as usize].outputs.push(i);
        }
        let mut public_ports = Vec::new();
        let proof = match &document.job {
            raw::Job::Run {} => None,
            raw::Job::Proof {
                prover,
                verifier,
                acceptance,
                completion,
                construction,
                gates: _gates,
                ..
            } => {
                let verifier_index = indices[verifier.as_str()] as u32;
                for (i, view) in views.iter().enumerate() {
                    work.charge(1)?;
                    if view.role == verifier_index && view.public {
                        public_ports.push(i);
                    }
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
            views,
            outputs,
            residual,
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
            definition: &self.ports.views[index].definition,
            path: &self.ports.views[index].path,
            role: self.ports.views[index].role,
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
            .map(|&i| &self.ports.outputs[i].definition)
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

impl Interface {
    /// Every role's sorted original input coordinates, in roster order, from
    /// one pass over the components rather than one pass per role.
    #[cfg_attr(not(feature = "cpu"), allow(dead_code))]
    pub(in crate::entry) fn native_inputs_by_role(&self) -> Vec<Vec<u32>> {
        let mut roles = vec![BTreeSet::new(); self.roles().len()];
        for component in self
            .selected_protocol()
            .inputs
            .iter()
            .flat_map(|p| &p.components)
        {
            roles[component.role as usize].insert(component.native);
        }
        roles
            .into_iter()
            .map(|natives| natives.into_iter().collect())
            .collect()
    }
    pub(in crate::entry) fn role_native_inputs(&self, role: &RolePorts) -> Vec<u32> {
        let index = self
            .roles()
            .iter()
            .position(|r| std::ptr::eq(r, role))
            .expect("checked role") as u32;
        self.selected_protocol()
            .inputs
            .iter()
            .flat_map(|p| &p.components)
            .filter(|c| c.role == index)
            .map(|c| c.native)
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect()
    }
    #[cfg(feature = "cpu")]
    pub(in crate::entry) fn public_native(&self) -> Vec<u32> {
        self.public_ports()
            .flat_map(|p| p.definition.native.iter().copied())
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect()
    }
}

impl Interface {
    pub(in crate::entry) fn generated_input_names(&self, ports: &[InputPort<'_>]) -> Vec<String> {
        let coordinates: Vec<_> = ports
            .iter()
            .map(|p| (&self.selected_protocol().inputs[p.index as usize], p.path))
            .collect();
        super::boundary::family_aliases(&coordinates)
    }
    pub(in crate::entry) fn generated_output_names(&self, ports: &[&raw::Port]) -> Vec<String> {
        let coordinates: Vec<_> = ports
            .iter()
            .map(|p| {
                let view = self
                    .ports
                    .outputs
                    .iter()
                    .find(|v| std::ptr::eq(&v.definition, *p))
                    .expect("checked output view");
                (
                    &self.selected_protocol().outputs[p.index as usize],
                    view.path.as_slice(),
                )
            })
            .collect();
        super::boundary::family_aliases(&coordinates)
    }
}

impl Interface {
    /// Borrow the admitted roster without allocating policy-association state.
    #[cfg(feature = "evm")]
    pub(crate) fn evm_public_inputs(
        &self,
    ) -> impl ExactSizeIterator<Item = (&str, &raw::Schema, &[u32])> {
        self.ports.public.iter().map(move |&index| {
            let port = &self.ports.views[index].definition;
            (port.name.as_str(), &port.schema, port.native.as_slice())
        })
    }

    /// Independently check policy facts represented by this Interface. Query
    /// schedules and realized codecs remain owned by the compiler descriptor.
    #[cfg(feature = "evm")]
    pub(crate) fn check_evm_policy(&self, policy: &serde_json::Value) -> Result<()> {
        use serde_json::json;
        let raw::Job::Proof {
            acceptance,
            construction,
            gates,
            ..
        } = &self.document.job
        else {
            return Err(E::NativeBinding);
        };
        let protocol = self.selected_protocol();
        let proof = self.proof().ok_or(E::NativeBinding)?;
        let selected_construction = match construction.as_ref() {
            raw::Construction::Derived { symbol, .. } => symbol.as_str(),
            _ => "",
        };
        let services = proof
            .replaced_services
            .iter()
            .map(|&index| protocol.services[index].native.to_string())
            .collect::<Vec<_>>();
        let natural = |value: &serde_json::Value| {
            value
                .as_str()
                .and_then(|text| zkc_format::logical::natural_index(text).ok())
        };
        let gates_match = policy[11].as_array().is_some_and(|rows| {
            rows.len() == gates.len()
                && rows.iter().zip(gates).all(|(row, gate)| {
                    natural(&row[1]) == Some(u64::from(gate.bits))
                        && row[0] == crate::source_names::native_site_path(&gate.path)
                })
        });
        let acceptance = validate::select(protocol, acceptance)?.1;
        super::require(
            policy.as_array().is_some_and(|fields| fields.len() == 12)
                && policy[0] == "zkc.native-proof-policy/0"
                && policy[1] == protocol.symbol
                && policy[2] == self.roles()[proof.prover].native_name
                && policy[3] == self.roles()[proof.verifier].native_name
                && acceptance.len() == 1
                && natural(&policy[4]) == Some(u64::from(acceptance[0]))
                && policy[5] == proof.suite.as_deref().unwrap_or("")
                && policy[6] == json!(services)
                && policy[9] == proof.format.name()
                && policy[10] == selected_construction
                && gates_match,
            E::NativeBinding,
        )
    }

    /// Resolve an original native coordinate to its participant ABI position.
    /// This is an association only; it supplies no common-control agreement.
    pub fn native_input_position(&self, role: &str, original: u32) -> Result<usize> {
        let role = self
            .roles()
            .iter()
            .find(|r| r.name == role)
            .ok_or(E::Selection)?;
        self.role_native_inputs(role)
            .binary_search(&original)
            .map_err(|_| E::Selection)
    }
}
