//! Explicit externally pinned admission context. This is neither source
//! requirement derivation nor a certificate that peers used the same pin.
use super::wire::WireBackend;
use crate::vm::{Limits, PhysicalType, Program, Type, Value};
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
    Limit,
    Identity,
    Subject,
    Requirements,
    Input,
    Value,
    Codec,
}
impl std::fmt::Display for BindingError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "input-binding-{self:?}")
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
        if root[0] != "zkc.input-bindings/0"
            || root[1] != hex(&Sha256::digest(program.bytes()))
            || root[2] != entry
        {
            return Err(BindingError::Subject);
        }
        let roles = program.entry(entry).ok_or(BindingError::Subject)?;
        let bindings = root[3]
            .as_array()
            .filter(|a| a.len() == required.len())
            .ok_or(BindingError::Requirements)?;
        let mut groups = Vec::new();
        let mut components = 0usize;
        for (requirement, binding) in required.iter().zip(bindings) {
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
            let row = binding
                .as_array()
                .filter(|a| a.len() == 4)
                .ok_or(BindingError::Requirements)?;
            let expected_components: Vec<_> = requirement
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
                .collect();
            if row[0] != json!(expected_components)
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
    /// Check actual input components before loading a runner. Uses the same
    /// independently installed canonical data codec as public proof binding.
    /// This never grants service/custody authority or changes Program admission.
    pub fn check_role<B: WireBackend>(
        &self,
        role: &str,
        backend: &B,
        inputs: &[B::Value],
    ) -> Result<()> {
        if inputs.len() > Limits::PORTS {
            return Err(BindingError::Limit);
        }
        self.check_role_prepared(role, backend, &inputs.iter().map(Some).collect::<Vec<_>>())
    }

    /// Inspect prepared ordinary inputs before capability/service issuance.
    /// Holes are allowed only outside observed components. This does not admit
    /// missing Runner inputs or confer capability custody.
    pub fn check_role_prepared<B: WireBackend>(
        &self,
        role: &str,
        backend: &B,
        inputs: &[Option<&B::Value>],
    ) -> Result<()> {
        let ports = &self
            .roles
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
        let mut remaining = Limits::VALUE_BYTES;
        for group in &self.groups {
            for component in group
                .requirement
                .components
                .iter()
                .filter(|c| c.role == role)
            {
                let root = inputs[component.input].ok_or(BindingError::Input)?;
                remaining = remaining
                    .checked_sub(root.retained_bytes())
                    .ok_or(BindingError::Limit)?;
                backend
                    .validate_value(root)
                    .map_err(|_| BindingError::Value)?;
                let mut selected = Some(root.clone());
                for &(alternative, payload) in &component.path {
                    let value = selected.take().ok_or(BindingError::Input)?;
                    remaining = remaining
                        .checked_sub(value.retained_bytes())
                        .ok_or(BindingError::Limit)?;
                    let tag = value
                        .control_variant_tag()
                        .map_err(|_| BindingError::Value)?;
                    if value.physical_type().variant_payload(tag).is_none() {
                        return Err(BindingError::Value);
                    }
                    if tag != alternative {
                        break;
                    }
                    let (ty, tag, values) =
                        value.unpack_variant().map_err(|_| BindingError::Value)?;
                    if ty != value.physical_type() || tag != alternative {
                        return Err(BindingError::Value);
                    }
                    selected = Some(values.get(payload).ok_or(BindingError::Value)?.clone());
                }
                let Some(value) = selected else {
                    if group.expected.is_some() {
                        return Err(BindingError::Value);
                    }
                    continue;
                };
                let expected = group.expected.as_ref().ok_or(BindingError::Value)?;
                remaining = remaining
                    .checked_sub(value.retained_bytes())
                    .ok_or(BindingError::Limit)?;
                if !value.has_type(&group.requirement.ty) {
                    return Err(BindingError::Value);
                }
                backend
                    .validate_value(&value)
                    .map_err(|_| BindingError::Value)?;
                let bytes = match group.requirement.observation {
                    Observation::Tag => {
                        let tag = value
                            .control_variant_tag()
                            .map_err(|_| BindingError::Value)?;
                        if tag
                            >= group
                                .requirement
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
                        if !backend.supports_wire(&group.requirement.ty) {
                            return Err(BindingError::Codec);
                        }
                        // Complete wire permission was independently admitted
                        // above. The installed codec also supports aggregate
                        // frames absent from the legacy common-message profile.
                        let bound = backend
                            .encoding_bound(&value)
                            .map_err(|_| BindingError::Codec)?;
                        remaining = remaining.checked_sub(bound).ok_or(BindingError::Limit)?;
                        let bytes = backend
                            .encode_wire(&value)
                            .map_err(|_| BindingError::Codec)?;
                        if bytes.len() > bound {
                            return Err(BindingError::Codec);
                        }
                        bytes
                    }
                };
                if &bytes != expected {
                    return Err(BindingError::Value);
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
