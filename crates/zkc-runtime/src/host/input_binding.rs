//! Explicit externally pinned admission context. This is neither source
//! requirement derivation nor a certificate that peers used the same pin.
use super::wire::{RootRefusal, WireBackend, reserve_root};
use crate::vm::{
    EntryRole, ExecutionLedger, Limits, LiveReservation, PhysicalType, Program, Type, Value,
};
use serde_json::json;
use sha2::{Digest, Sha256};
use std::collections::BTreeSet;

/// Source/interface ownership resolves logical children to flat participant ABI
/// ports. Each path pair selects a declared variant alternative and payload.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InputComponent {
    pub role: String,
    pub input: usize,
    pub path: Vec<(usize, usize)>,
}
/// The exact property required for shared control. Tag and extent agreement
/// establish no equality of payloads or collection contents.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Observation {
    Value,
    Tag,
    Extent { axis: usize },
}
impl Observation {
    fn encoding(self) -> serde_json::Value {
        match self {
            Self::Value => json!("value"),
            Self::Tag => json!("tag"),
            Self::Extent { axis } => json!(["extent", axis.to_string()]),
        }
    }
    fn admits(self, program: &Program, ty: &PhysicalType) -> bool {
        match self {
            Self::Value => {
                ty.is_duplicable()
                    && program
                        .contracts()
                        .permits_wire(ty, crate::vm::WireCodec::Native)
            }
            Self::Tag => ty.logical().variant_descriptor().is_some(),
            Self::Extent { axis } => {
                let rank = match ty.kind() {
                    Type::Bytes
                    | Type::Sequence
                    | Type::Vector
                    | Type::Groups
                    | Type::Indices
                    | Type::FieldArray
                    | Type::FixedVector => 1,
                    Type::Matrix => 2,
                    _ => 0,
                };
                ty.is_duplicable() && axis < rank
            }
        }
    }
}
/// Complete independently derived or application-trusted obligation, never an
/// artifact-supplied grant. Runtime cannot independently derive source coverage.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InputRequirement {
    pub components: Vec<InputComponent>,
    pub ty: PhysicalType,
    pub observation: Observation,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BindingError {
    /// A ceiling of the context format: its bytes, groups, components, path
    /// depth, an extent, or the number of a role's inputs.
    Limit,
    /// The invocation root's logical work allowance refused inspection or
    /// encoding.
    WorkLimit,
    /// The invocation root's fresh or live byte allowance refused an
    /// encoding.
    BytesLimit,
    Identity,
    Subject,
    Requirements,
    Input,
    Value,
    Codec,
}
impl std::fmt::Display for BindingError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::WorkLimit => f.write_str("input-binding-work-limit"),
            Self::BytesLimit => f.write_str("input-binding-bytes-limit"),
            other => write!(f, "input-binding-{other:?}"),
        }
    }
}
impl std::error::Error for BindingError {}
type Result<T> = std::result::Result<T, BindingError>;
#[derive(Clone)]
struct Group {
    requirement: InputRequirement,
    expected: Option<Vec<u8>>,
}
/// Admitted immutable context for one exact Program/entry. The caller owns the
/// source requirement inventory and the externally trusted pin's provenance.
#[derive(Clone)]
pub struct InputBindings {
    groups: Vec<Group>,
    roles: Vec<crate::vm::EntryRole>,
}
impl std::fmt::Debug for InputBindings {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // Common inputs need not be public. Diagnostics retain no value bytes.
        f.debug_struct("InputBindings")
            .field("groups", &self.groups.len())
            .finish_non_exhaustive()
    }
}
fn hex(bytes: &[u8]) -> String {
    const DIGITS: &[u8] = b"0123456789abcdef";
    let mut out = String::with_capacity(bytes.len() * 2);
    for &b in bytes {
        out.push(DIGITS[(b >> 4) as usize] as char);
        out.push(DIGITS[(b & 15) as usize] as char);
    }
    out
}
fn unhex(text: &str) -> Result<Vec<u8>> {
    if !text.len().is_multiple_of(2)
        || !text
            .bytes()
            .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
    {
        return Err(BindingError::Requirements);
    }
    let digit = |b: u8| if b <= b'9' { b - b'0' } else { b - b'a' + 10 };
    Ok(text
        .as_bytes()
        .as_chunks::<2>()
        .0
        .iter()
        .map(|p| digit(p[0]) * 16 + digit(p[1]))
        .collect())
}
impl InputBindings {
    /// Authenticate exact context bytes against an externally supplied pin,
    /// then check the Program subject and complete independently derived or
    /// application-trusted groups. This utility cannot derive source coverage.
    /// Hashing received context and supplying that hash is not authorization.
    pub fn admit_pinned(
        program: &Program,
        entry: &str,
        required: &[InputRequirement],
        bytes: &[u8],
        expected_sha256: &[u8; 32],
    ) -> Result<Self> {
        if bytes.len() > Limits::ARTIFACT_BYTES || required.len() > Limits::PORTS {
            return Err(BindingError::Limit);
        }
        let actual: [u8; 32] = Sha256::digest(bytes).into();
        if &actual != expected_sha256 {
            return Err(BindingError::Identity);
        }
        let tree =
            zkc_format::logical::decode_tree(bytes).map_err(|_| BindingError::Requirements)?;
        let root = tree
            .as_array()
            .filter(|a| a.len() == 4)
            .ok_or(BindingError::Requirements)?;
        if root[0] != FORMAT || root[1] != hex(&Sha256::digest(program.bytes())) || root[2] != entry
        {
            return Err(BindingError::Subject);
        }
        program.entry(entry).ok_or(BindingError::Subject)?;
        let roles = inventory(program, entry, required)?;
        let bindings = root[3]
            .as_array()
            .filter(|a| a.len() == required.len())
            .ok_or(BindingError::Requirements)?;
        let mut groups = Vec::new();
        for (requirement, binding) in required.iter().zip(bindings) {
            let row = binding
                .as_array()
                .filter(|a| a.len() == 4)
                .ok_or(BindingError::Requirements)?;
            if row[0] != components(requirement)
                || row[1] != requirement.ty.spelling()
                || row[2] != requirement.observation.encoding()
            {
                return Err(BindingError::Requirements);
            }
            let expected = row[3].as_array().ok_or(BindingError::Requirements)?;
            let expected = match expected.as_slice() {
                [tag] if tag == "inactive" => None,
                [tag, value] if tag == "active" => {
                    Some(unhex(value.as_str().ok_or(BindingError::Requirements)?)?)
                }
                _ => return Err(BindingError::Requirements),
            };
            if let Some(bytes) = &expected {
                match requirement.observation {
                    Observation::Value => {}
                    Observation::Tag => {
                        if natural(bytes)?
                            >= requirement
                                .ty
                                .logical()
                                .variant_descriptor()
                                .ok_or(BindingError::Requirements)?
                                .alternatives()
                                .len() as u64
                        {
                            return Err(BindingError::Requirements);
                        }
                    }
                    Observation::Extent { .. } => {
                        if natural(bytes)? > Limits::VALUE_BYTES as u64 {
                            return Err(BindingError::Limit);
                        }
                    }
                }
            } else if requirement.components.iter().any(|c| c.path.is_empty()) {
                return Err(BindingError::Requirements);
            }
            groups.push(Group {
                requirement: requirement.clone(),
                expected,
            });
        }
        Ok(Self { groups, roles })
    }
    /// Start producing the canonical context for one exact Program and entry
    /// from the complete requirement inventory. The inventory is checked
    /// exactly as `admit_pinned` checks it, and the produced bytes are those
    /// `admit_pinned` accepts. Producing a context confers no trust: every
    /// process still pins the bytes through an externally trusted application
    /// context.
    pub fn producer(
        program: &Program,
        entry: &str,
        required: &[InputRequirement],
    ) -> Result<ContextProducer> {
        if required.len() > Limits::PORTS {
            return Err(BindingError::Limit);
        }
        program.entry(entry).ok_or(BindingError::Subject)?;
        let roles = inventory(program, entry, required)?;
        Ok(ContextProducer {
            program: hex(&Sha256::digest(program.bytes())),
            entry: entry.to_owned(),
            groups: required
                .iter()
                .map(|requirement| Production {
                    requirement: requirement.clone(),
                    observed: None,
                    _live: Vec::new(),
                })
                .collect(),
            roles,
        })
    }
    /// Check actual input components before loading a runner. Uses the same
    /// independently installed canonical data codec as public proof binding.
    /// Inspection and encoding are charged to the invocation's ledger.
    /// This never grants service/custody authority or changes Program admission.
    pub fn check_role<B: WireBackend>(
        &self,
        role: &str,
        backend: &B,
        inputs: &[B::Value],
        ledger: &ExecutionLedger,
    ) -> Result<()> {
        if inputs.len() > Limits::PORTS {
            return Err(BindingError::Limit);
        }
        self.check_role_prepared(
            role,
            backend,
            &inputs.iter().map(Some).collect::<Vec<_>>(),
            ledger,
        )
    }

    /// Inspect prepared ordinary inputs before capability/service issuance.
    /// Holes are allowed only outside observed components. This does not admit
    /// missing Runner inputs or confer capability custody.
    ///
    /// Each inspected value charges its retained bytes to the ledger's logical
    /// work before it is validated or selected. A value observation charges its
    /// canonical encoding bound as fresh allocation and holds that live
    /// allowance until the comparison ends. Every role checked for one
    /// invocation shares the same ledger; nothing restarts per role.
    pub fn check_role_prepared<B: WireBackend>(
        &self,
        role: &str,
        backend: &B,
        inputs: &[Option<&B::Value>],
        ledger: &ExecutionLedger,
    ) -> Result<()> {
        check_ports(&self.roles, role, inputs)?;
        for group in &self.groups {
            for component in group
                .requirement
                .components
                .iter()
                .filter(|c| c.role == role)
            {
                let root = inputs[component.input].ok_or(BindingError::Input)?;
                match (
                    observe(&group.requirement, component, root, backend, ledger)?,
                    &group.expected,
                ) {
                    (None, None) => {}
                    (Some(observed), Some(expected)) if &observed.bytes == expected => {}
                    _ => return Err(BindingError::Value),
                }
            }
        }
        Ok(())
    }
}

fn natural(bytes: &[u8]) -> Result<u64> {
    let text = std::str::from_utf8(bytes).map_err(|_| BindingError::Requirements)?;
    zkc_format::logical::natural_index(text).map_err(|_| BindingError::Requirements)
}

const FORMAT: &str = "zkc.input-bindings/0";

/// Check the complete requirement inventory against the actual entry: exact
/// component coordinates and physical types, two or more participants per
/// group and an observation the type admits. Reader and producer share it.
fn inventory(
    program: &Program,
    entry: &str,
    required: &[InputRequirement],
) -> Result<Vec<EntryRole>> {
    let roles = program.entry(entry).ok_or(BindingError::Subject)?;
    let mut components = 0usize;
    for requirement in required {
        components = components
            .checked_add(requirement.components.len())
            .filter(|n| *n <= Limits::ARRAY_LENGTH)
            .ok_or(BindingError::Limit)?;
        let mut coordinates = BTreeSet::new();
        let mut participants = BTreeSet::new();
        for component in &requirement.components {
            if component.path.len() > crate::vm::TYPE_DEPTH_LIMIT {
                return Err(BindingError::Limit);
            }
            let role = roles
                .iter()
                .find(|r| r.role == component.role)
                .ok_or(BindingError::Requirements)?;
            participants.insert(&component.role);
            if !coordinates.insert((&component.role, component.input, &component.path)) {
                return Err(BindingError::Requirements);
            }
            let mut ty = role
                .inputs
                .get(component.input)
                .ok_or(BindingError::Requirements)?
                .1
                .clone();
            for &(alternative, payload) in &component.path {
                ty = ty
                    .variant_payload(alternative)
                    .and_then(|p| p.get(payload))
                    .ok_or(BindingError::Requirements)?
                    .clone();
            }
            if ty != requirement.ty {
                return Err(BindingError::Requirements);
            }
        }
        if participants.len() < 2 || !requirement.observation.admits(program, &requirement.ty) {
            return Err(BindingError::Requirements);
        }
    }
    Ok(roles)
}
/// The canonical component coordinates of one group.
fn components(requirement: &InputRequirement) -> serde_json::Value {
    json!(
        requirement
            .components
            .iter()
            .map(|c| {
                json!([
                    c.role,
                    c.input.to_string(),
                    c.path
                        .iter()
                        .flat_map(|(a, p)| [a.to_string(), p.to_string()])
                        .collect::<Vec<_>>()
                ])
            })
            .collect::<Vec<_>>()
    )
}
/// Exact role inputs in the entry's port order, with holes allowed.
fn check_ports<V: Value>(roles: &[EntryRole], role: &str, inputs: &[Option<&V>]) -> Result<()> {
    let ports = &roles
        .iter()
        .find(|r| r.role == role)
        .ok_or(BindingError::Input)?
        .inputs;
    if ports.len() != inputs.len()
        || ports
            .iter()
            .zip(inputs)
            .any(|((_, ty), v)| v.is_some_and(|v| !v.has_type(ty)))
    {
        return Err(BindingError::Input);
    }
    Ok(())
}
/// Charge inspection or encoding to the invocation root before its effect, all
/// or nothing; a refusal names the root allowance that refused.
fn charge_root(
    ledger: &ExecutionLedger,
    work: u64,
    fresh: usize,
    live: usize,
) -> Result<LiveReservation> {
    reserve_root(ledger, work, fresh, live).map_err(|refusal| match refusal {
        RootRefusal::Work => BindingError::WorkLimit,
        RootRefusal::Bytes => BindingError::BytesLimit,
    })
}
/// One component's canonical observation, holding the live allowance of its
/// encoding while it is retained.
struct Observed {
    bytes: Vec<u8>,
    live: Option<LiveReservation>,
}
/// Select one component of an actual root input and observe its required
/// property: `None` when a variant path is inactive. Each inspected value
/// charges its retained bytes as logical work before it is validated or
/// selected, and a value observation charges its canonical encoding bound as
/// fresh allocation, held live by the returned observation.
fn observe<B: WireBackend>(
    requirement: &InputRequirement,
    component: &InputComponent,
    root: &B::Value,
    backend: &B,
    ledger: &ExecutionLedger,
) -> Result<Option<Observed>> {
    let inspect =
        |value: &B::Value| charge_root(ledger, value.retained_bytes() as u64, 0, 0).map(drop);
    inspect(root)?;
    backend
        .validate_value(root)
        .map_err(|_| BindingError::Value)?;
    let mut selected = Some(root.clone());
    for &(alternative, payload) in &component.path {
        let value = selected.take().ok_or(BindingError::Input)?;
        inspect(&value)?;
        let tag = value
            .control_variant_tag()
            .map_err(|_| BindingError::Value)?;
        if value.physical_type().variant_payload(tag).is_none() {
            return Err(BindingError::Value);
        }
        if tag != alternative {
            break;
        }
        let (ty, tag, values) = value.unpack_variant().map_err(|_| BindingError::Value)?;
        if ty != value.physical_type() || tag != alternative {
            return Err(BindingError::Value);
        }
        selected = Some(values.get(payload).ok_or(BindingError::Value)?.clone());
    }
    let Some(value) = selected else {
        return Ok(None);
    };
    inspect(&value)?;
    if !value.has_type(&requirement.ty) {
        return Err(BindingError::Value);
    }
    backend
        .validate_value(&value)
        .map_err(|_| BindingError::Value)?;
    let mut live = None;
    let bytes = match requirement.observation {
        Observation::Tag => {
            let tag = value
                .control_variant_tag()
                .map_err(|_| BindingError::Value)?;
            if tag
                >= requirement
                    .ty
                    .logical()
                    .variant_descriptor()
                    .ok_or(BindingError::Value)?
                    .alternatives()
                    .len()
            {
                return Err(BindingError::Value);
            }
            tag.to_string().into_bytes()
        }
        Observation::Extent { axis } => {
            let extent = value
                .control_extent(axis)
                .map_err(|_| BindingError::Value)?;
            if extent > Limits::VALUE_BYTES as u64 {
                return Err(BindingError::Limit);
            }
            extent.to_string().into_bytes()
        }
        Observation::Value => {
            if !backend.supports_wire(&requirement.ty) {
                return Err(BindingError::Codec);
            }
            // Complete wire permission was independently admitted with the
            // inventory. The installed codec also supports aggregate frames.
            let bound = backend
                .encoding_bound(&value)
                .map_err(|_| BindingError::Codec)?;
            live = Some(charge_root(ledger, bound as u64, bound, bound)?);
            let bytes = backend
                .encode_wire(&value)
                .map_err(|_| BindingError::Codec)?;
            if bytes.len() > bound {
                return Err(BindingError::Codec);
            }
            bytes
        }
    };
    Ok(Some(Observed { bytes, live }))
}

struct Production {
    requirement: InputRequirement,
    /// Absent until a component is observed; then active bytes or inactive.
    observed: Option<Option<Vec<u8>>>,
    _live: Vec<LiveReservation>,
}
/// Canonical `zkc.input-bindings/0` production for one exact Program and
/// entry. Each observed role contributes its actual components; every
/// observed component of a group must agree, and every group needs one.
pub struct ContextProducer {
    program: String,
    entry: String,
    groups: Vec<Production>,
    roles: Vec<EntryRole>,
}
impl std::fmt::Debug for ContextProducer {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // Common inputs need not be public. Diagnostics retain no value bytes.
        f.debug_struct("ContextProducer")
            .field("groups", &self.groups.len())
            .finish_non_exhaustive()
    }
}
impl ContextProducer {
    /// Observe one role's actual inputs, in the entry's port order. Holes are
    /// allowed only outside required components. Inspection and encoding
    /// charge the ledger exactly as `InputBindings::check_role_prepared`
    /// does; observations stay charged live until `encode` returns.
    pub fn observe_role<B: WireBackend>(
        &mut self,
        role: &str,
        backend: &B,
        inputs: &[Option<&B::Value>],
        ledger: &ExecutionLedger,
    ) -> Result<()> {
        if inputs.len() > Limits::PORTS {
            return Err(BindingError::Limit);
        }
        check_ports(&self.roles, role, inputs)?;
        for group in &mut self.groups {
            for component in group
                .requirement
                .components
                .iter()
                .filter(|c| c.role == role)
            {
                let root = inputs[component.input].ok_or(BindingError::Input)?;
                let observed = observe(&group.requirement, component, root, backend, ledger)?;
                let (bytes, live) = match observed {
                    Some(Observed { bytes, live }) => (Some(bytes), live),
                    None => (None, None),
                };
                match &group.observed {
                    Some(previous) if previous != &bytes => return Err(BindingError::Value),
                    Some(_) => {}
                    None => group.observed = Some(bytes),
                }
                group._live.extend(live);
            }
        }
        Ok(())
    }
    /// Encode the canonical context. Every group must have an observed
    /// component; the bytes are charged to the ledger as fresh allocation.
    pub fn encode(self, ledger: &ExecutionLedger) -> Result<Vec<u8>> {
        let rows = self
            .groups
            .iter()
            .map(|group| {
                let expected = match group.observed.as_ref().ok_or(BindingError::Input)? {
                    Some(bytes) => json!(["active", hex(bytes)]),
                    None => json!(["inactive"]),
                };
                Ok(json!([
                    components(&group.requirement),
                    group.requirement.ty.spelling(),
                    group.requirement.observation.encoding(),
                    expected
                ]))
            })
            .collect::<Result<Vec<_>>>()?;
        let bytes =
            zkc_format::logical::encode_tree(&json!([FORMAT, self.program, self.entry, rows]))
                .map_err(|_| BindingError::Limit)?;
        if bytes.len() > Limits::ARTIFACT_BYTES {
            return Err(BindingError::Limit);
        }
        drop(charge_root(ledger, bytes.len() as u64, bytes.len(), 0)?);
        Ok(bytes)
    }
}
