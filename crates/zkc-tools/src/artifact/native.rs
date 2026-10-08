//! Independent proof execution with an application-pinned deployment.
mod attempts;
mod inputs;
pub use crate::host::capacity::NativeCapacity;
pub use crate::host::material::ProverMaterial;
pub use crate::host::request::InputValue;
pub use inputs::ProofInputs;
mod setups;
use super::{driver, entropy::Entropy, host, io::*, material::MaterialCache};
use crate::host::admission::{Admission, Input, Operand, ResourceInput, entry_values};
pub use attempts::{AttemptPolicy, AttemptRecord};
use serde_json::{Value as Json, json};
pub use setups::SetupAuthority;
use sha2::{Digest, Sha256};
use std::collections::BTreeMap;
use zkc_backends::{
    Capability, Domain, EntryPolicy, NativeBackend, Policy, PublicInputs, Value,
    services::{ServiceReference, ServiceRegistry},
};
use zkc_runtime::{
    interactive::{
        EntryRole, Identity, LogicalType, NativeProofEntry, NativeTranscriptEvent, PhysicalType,
        ProgramAction, Runner, Type, admit_supplied,
    },
    logical,
};

#[derive(Clone, Debug)]
pub(crate) struct Port {
    pub(crate) original: usize,
    pub(crate) logical: LogicalType,
}
#[derive(Clone, Debug)]
pub(crate) struct RoleMap {
    pub(crate) data: Vec<Port>,
    pub(crate) services: Vec<usize>,
    pub(crate) outputs: Vec<Port>,
}
/// Immutable deployment admitted against an independently supplied digest.
#[derive(Clone, Debug)]
pub struct NativeDeployment {
    version: u8,
    publication: String,
    choices: [bool; 2],
    external_work_limit: u64,
    capacity: NativeCapacity,
    setups: SetupAuthority,
    entry: NativeProofEntry,
    source: String,
    descriptor: Json,
    public: Vec<Port>,
    maps: BTreeMap<String, RoleMap>,
}
pub(crate) struct SourceInterface<'a> {
    pub version: u8,
    pub publication: &'a str,
    pub source: &'a str,
    pub choices: [bool; 2],
    pub acceptance: usize,
    pub suite: Option<&'a str>,
    pub service: Option<usize>,
    pub public: &'a [Port],
    pub roles: &'a BTreeMap<String, RoleMap>,
}
enum Mode<'a> {
    Prove,
    Verify(&'a [u8]),
    Attempts(attempts::Plan),
}
impl<'a> Mode<'a> {
    fn one_shot(proof: Option<&'a [u8]>) -> Self {
        proof.map_or(Self::Prove, Self::Verify)
    }
}
#[cfg(feature = "test-utils")]
fn test_entropy(tapes: BTreeMap<usize, Vec<zkc_backends::Scalar>>) -> Result<Entropy> {
    if tapes.len() > 1024 || tapes.values().any(|t| t.len() > 1_000_000) {
        return Err("native-proof-test-entropy-limit".into());
    }
    Ok(Entropy::Tapes(tapes))
}
fn index(value: &Json) -> Result<usize> {
    let n = logical::natural_index(text(value)?).map_err(|e| e.to_string())?;
    if n >= 1024 {
        return Err("native-proof-port".into());
    }
    Ok(n as usize)
}
fn digest(value: &str) -> Result<()> {
    if value.len() != 64
        || !value
            .bytes()
            .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
    {
        return Err("native-proof-digest".into());
    }
    Ok(())
}
fn wire_type(value: &str, version: u8, public: bool) -> Result<LogicalType> {
    let iterated = version >= 2;
    let ty = LogicalType::parse(value).map_err(|e| e.to_string())?;
    let array = ty.field_array_parts().is_some_and(|(f, n)| {
        f == zkc_runtime::interactive::Identity::Bls12381Fr && n <= 1_048_576
    });
    if !matches!(value, "bool" | "field:bls12-381.fr" | "group:bls12-381.g1")
        && !(iterated && (value == "index" || array || public && value == "table:bls12-381.fr"))
        && !(version == 4 && ty.is_native_message_data())
        && !(matches!(version, 3 | 4)
            && (matches!(
                value,
                "commitment:multilinear.kzg.bls12-381/1" | "proof:multilinear.kzg.bls12-381/1"
            ) || public && value == "verifier_key:multilinear.kzg.bls12-381/1"))
    {
        return Err("native-proof-wire-type".into());
    }
    Ok(ty)
}
fn wire_codec(ty: &LogicalType) -> Option<String> {
    if PhysicalType::default_for(ty.clone()).is_ok_and(|t| t.has_native_data_frame()) {
        Some("zkc.native-data/1".into())
    } else if ty.kind() == Type::VerifierKey {
        Some("zkc.native-verifier-key/1".into())
    } else if ty.field_array_parts().is_some() {
        Some("zkc.native-field-array/1".into())
    } else {
        ty.codec()
    }
}

// This host's entry constructors are narrower than ordinary local IR types.
// Share the decision between deployment admission and invocation planning.
fn input_kind(ty: &PhysicalType, version: u8) -> Result<&'static str> {
    if zkc_backends::has_native_wire(ty)
        && (version == 4
            || !ty.has_native_data_frame()
                && matches!(
                    ty.logical().identity(),
                    Identity::Bls12381Fr
                        | Identity::Bls12381G1
                        | Identity::MultilinearKzgBls12381
                        | Identity::None
                ))
    {
        return Ok("wire");
    }
    let logical = ty.logical();
    if PhysicalType::default_for(logical.clone()).ok().as_ref() == Some(ty) {
        match (logical.kind(), logical.identity()) {
            (Type::Nonce, Identity::Bls12381Fr | Identity::Ristretto255Scalar)
                if version == 4 || logical.identity() == Identity::Bls12381Fr =>
            {
                return Ok("nonce");
            }
            (Type::Rng, field)
                if zkc_runtime::interactive::ServiceContract::for_field(field).is_some()
                    && (version == 4 || field == Identity::Bls12381Fr) =>
            {
                return Ok("rng");
            }
            (Type::VerifierKey, Identity::MultilinearKzgBls12381) if matches!(version, 3 | 4) => {
                return Ok("verifier_key");
            }
            (Type::ProverKey, Identity::MultilinearKzgBls12381) if matches!(version, 3 | 4) => {
                return Ok("prover_key_file");
            }
            _ => {}
        }
    }
    Err("native-proof-role-input-type".into())
}

fn ports(value: &Json, actual: &[PhysicalType]) -> Result<Vec<Port>> {
    let mut ports = Vec::new();
    if list(value)?.len() != actual.len() {
        return Err("native-proof-port-map".into());
    }
    for (row, ty) in list(value)?.iter().zip(actual) {
        let row = array(row, 2)?;
        let original = index(&row[0])?;
        let logical = LogicalType::parse(text(&row[1])?).map_err(|e| e.to_string())?;
        if logical != ty.logical() || ports.last().is_some_and(|p: &Port| p.original >= original) {
            return Err("native-proof-port-map".into());
        }
        ports.push(Port { original, logical });
    }
    Ok(ports)
}
fn backend(
    policy: Policy,
    role: &EntryRole,
    entry: &str,
    keys: zkc_backends::SetupRegistry,
    ports: BTreeMap<String, zkc_backends::PortConstraint>,
) -> Result<NativeBackend> {
    NativeBackend::with_setups(
        policy,
        EntryPolicy::new(
            Domain::new(&role.role, "native-proof", entry, Some(&role.instance)),
            None,
            PublicInputs::LocalOnly,
        )
        .with_ports(ports),
        keys,
    )
    .map_err(|e| e.to_string())
}
fn retain_driver_stop<T>(report: &mut NativeProofReport, result: &driver::ArtifactReport<T>) {
    if let Some(stop) = result.stop() {
        report.stop = Some(stop.clone());
        report
            .cleanup_errors
            .extend(stop.cleanup_errors.iter().map(ToString::to_string));
    }
}
impl NativeDeployment {
    /// `expected_sha256` must come from the application's trusted compilation or
    /// deployment configuration, independently of these supplied bytes and proof.
    pub fn admit(bytes: &[u8], expected_sha256: &str) -> Result<Self> {
        Self::admit_configured(bytes, expected_sha256, None, None)
    }
    /// Authorize the one PCS setup independently of invocation inputs and proof.
    /// Obtain `expected_key_id` from trusted application configuration or a
    /// setup export; never copy it from an incoming VK/proof/request header.
    pub fn admit_with_key(
        bytes: &[u8],
        expected_sha256: &str,
        expected_key_id: [u8; 32],
    ) -> Result<Self> {
        Self::admit_configured(bytes, expected_sha256, Some(expected_key_id), None)
    }
    /// Authorize several setups and each setup-bearing input independently of
    /// the invocation. The complete public key values are bound in the root.
    pub fn admit_with_setups(
        bytes: &[u8],
        expected_sha256: &str,
        authority: SetupAuthority,
    ) -> Result<Self> {
        Self::admit_configured(bytes, expected_sha256, None, Some(authority))
    }
    fn admit_configured(
        bytes: &[u8],
        expected_sha256: &str,
        key_id: Option<[u8; 32]>,
        authority: Option<SetupAuthority>,
    ) -> Result<Self> {
        if bytes.len() > INPUT_LIMIT {
            return Err("native-proof-deployment-limit".into());
        }
        digest(expected_sha256)?;
        if hash(bytes) != expected_sha256 {
            return Err("native-proof-deployment-binding".into());
        }
        let value = parse(bytes, INPUT_LIMIT)?;
        let envelope = array(&value, 9)?;
        let version = match text(&envelope[0])? {
            "zkc.native-proof/1" => 1,
            "zkc.native-proof/2" => 2,
            "zkc.native-proof/3" => 3,
            "zkc.native-proof/4" => 4,
            _ => return Err("native-proof-format".into()),
        };
        let iterated = version >= 2;
        let source = text(&envelope[1])?.to_owned();
        digest(&source)?;
        let descriptor = array(&envelope[2], 6)?;
        if text(&descriptor[0])? != format!("zkc.native-proof-descriptor/{version}")
            || text(&descriptor[2])?
                != if iterated {
                    "zkc.native-origin/2"
                } else {
                    "zkc.native-origin/1"
                }
        {
            return Err("native-proof-descriptor".into());
        }
        let descriptor_bytes = logical::encode_tree(&envelope[2]).map_err(|e| e.to_string())?;
        if text(&envelope[3])? != hash(&descriptor_bytes) {
            return Err("native-proof-descriptor-binding".into());
        }
        let candidate = text(&envelope[4])?;
        if text(&envelope[5])? != hash(candidate.as_bytes()) {
            return Err("native-proof-candidate-binding".into());
        }
        let choices = array(&envelope[7], 2)?;
        if choices
            .iter()
            .any(|v| !matches!(v.as_str(), Some("true" | "false")))
        {
            return Err("native-proof-choices".into());
        }
        let policy = array(&descriptor[1], 9)?;
        if text(&policy[0])? != format!("zkc.native-proof-policy/{version}") {
            return Err("native-proof-policy".into());
        }
        let (entry, producer, validator) =
            (text(&policy[1])?, text(&policy[2])?, text(&policy[3])?);
        if producer == validator {
            return Err("native-proof-interface".into());
        }
        let original_acceptance = index(&policy[4])?;
        let suite = text(&policy[5])?;
        let suite = (!suite.is_empty()).then_some(suite);
        let draws = list(&policy[8])?;
        if version == 2 && suite.is_none()
            || draws.len() > 64
            || (suite.is_some() != !draws.is_empty())
            || suite.is_some() != !text(&policy[6])?.is_empty()
        {
            return Err("native-proof-policy".into());
        }
        if suite.is_some() {
            index(&policy[6])?;
        }
        let mut selected_sites = std::collections::BTreeSet::new();
        for draw in draws {
            for site in array(draw, 2)? {
                let site = text(site)?;
                if site.is_empty()
                    || site.len() > 4096
                    || !site.bytes().all(|b| (33..=126).contains(&b))
                    || !selected_sites.insert(site)
                {
                    return Err("native-proof-policy".into());
                }
            }
        }
        let admitted = {
            let dummy = NativeBackend::new(
                Policy::default(),
                EntryPolicy::new(
                    Domain::new(producer, "native-proof", entry, None),
                    None,
                    PublicInputs::LocalOnly,
                ),
                None,
            )
            .map_err(|e| e.to_string())?;
            admit_supplied(candidate.as_bytes(), &dummy).map_err(|e| e.to_string())?
        };
        let mut messages = BTreeMap::new();
        for row in list(&descriptor[5])? {
            let row = array(row, 3)?;
            let origin = text(&row[0])?;
            let ty = wire_type(text(&row[1])?, version, false)?;
            if wire_codec(&ty).as_deref() != Some(text(&row[2])?)
                || messages.insert(origin, ty).is_some()
            {
                return Err("native-proof-message-map".into());
            }
        }
        let mut events = Vec::new();
        let mut origins = std::collections::BTreeSet::new();
        let mut queries = 0;
        let mut observed_messages = 0;
        let mut wire_origins = Vec::new();
        for row in list(&descriptor[3])? {
            let row = array(row, 2)?;
            let (kind, origin) = (text(&row[0])?, text(&row[1])?);
            let bytes = if iterated {
                logical::native_origin_template(&[origin.into()], kind)
            } else {
                logical::native_origin(&[origin.into()], kind)
            }
            .map_err(|e| e.to_string())?;
            let record = logical::decode_tree(&bytes).map_err(|e| e.to_string())?;
            if record[1].as_str() != Some(entry) || !origins.insert(origin) {
                return Err("native-proof-origin-map".into());
            }
            if kind == "query" {
                queries += 1;
                if record[4][4]
                    .as_str()
                    .and_then(|c| zkc_runtime::interactive::ServiceContract::parse(c).ok())
                    .map(|c| c.field())
                    != suite
                        .and_then(|s| LogicalType::parse(&format!("transcript:{s}")).ok())
                        .and_then(|t| t.identity().scalar_field())
                    || record[4][5].as_str() != Some("draw")
                    || record[4][6].as_str() != Some(validator)
                {
                    return Err("native-proof-query-origin".into());
                }
            } else {
                observed_messages += 1;
                if record[4][4].as_str() == Some(producer)
                    && record[4][5].as_str() == Some(validator)
                {
                    wire_origins.push(origin);
                } else if record[4][4].as_str() != Some(validator)
                    || record[4][5].as_str() != Some(producer)
                {
                    return Err("native-proof-message-origin".into());
                }
            }
            let prefix = if iterated {
                "transcript.native.indexed."
            } else {
                "transcript.native."
            };
            let payload = if kind == "message" {
                Some(
                    messages
                        .get(origin)
                        .ok_or("native-proof-message-map")?
                        .clone(),
                )
            } else {
                None
            };
            let contract = match kind {
                "query" => format!("{prefix}challenge"),
                "message" if version == 4 => format!("{prefix}observe.data"),
                "message" => format!(
                    "{prefix}observe.{}",
                    payload
                        .as_ref()
                        .ok_or("native-proof-message-map")?
                        .kind()
                        .name()
                ),
                _ => return Err("native-proof-event".into()),
            };
            if suite.is_some() {
                events.push(NativeTranscriptEvent {
                    contract,
                    origin: origin.into(),
                    payload,
                });
            }
        }
        if queries != draws.len() || observed_messages != messages.len() || origins.len() > 2048 {
            return Err("native-proof-event-map".into());
        }
        let wire_rows = list(&envelope[8])?;
        if wire_rows.len() != wire_origins.len() {
            return Err("native-proof-wire-map".into());
        }
        let mut wire_layout = Vec::new();
        let mut wire_sites = std::collections::BTreeSet::new();
        for (row, origin) in wire_rows.iter().zip(wire_origins) {
            let row = array(row, 2)?;
            let site = text(&row[1])?;
            if text(&row[0])? != origin
                || site.is_empty()
                || site.len() > 4096
                || !wire_sites.insert(site)
            {
                return Err("native-proof-wire-map".into());
            }
            wire_layout.push((
                site,
                messages.get(origin).ok_or("native-proof-message-map")?,
            ));
        }
        for role in admitted.program_entry(entry).map_err(|e| e.to_string())? {
            let actual: Vec<_> = role
                .actions
                .iter()
                .filter_map(|action| match action {
                    ProgramAction::Send {
                        site, schema, ty, ..
                    }
                    | ProgramAction::Receive {
                        site, schema, ty, ..
                    } => Some((site, schema, ty)),
                    _ => None,
                })
                .collect();
            if actual.len() != wire_layout.len()
                || actual.iter().zip(&wire_layout).any(
                    |((site, schema, ty), (expected, logical))| {
                        site.as_str() != *expected
                            || schema.as_str() != *expected
                            || ty.logical() != **logical
                    },
                )
            {
                return Err("native-proof-wire-map".into());
            }
        }
        let roles = admitted.entry(entry).ok_or("native-proof-entry")?;
        let mut acceptance = None;
        let mut maps = BTreeMap::new();
        for row in list(&envelope[6])? {
            let row = array(row, 6)?;
            let role_name = text(&row[0])?;
            let role = roles
                .iter()
                .find(|r| r.role == role_name)
                .ok_or("native-proof-role-map")?;
            if role.participant != text(&row[1])? {
                return Err("native-proof-role-map".into());
            }
            let extra = usize::from(suite.is_some());
            if role.inputs.len() < extra || role.outputs.len() < extra {
                return Err("native-proof-port-map".into());
            }
            let input_types = role.inputs[..role.inputs.len() - extra]
                .iter()
                .map(|(_, t)| t.clone())
                .collect::<Vec<_>>();
            let data = ports(&row[2], &input_types)?;
            for ty in &input_types {
                input_kind(ty, version)?;
            }
            let outputs = ports(&row[3], &role.outputs[..role.outputs.len() - extra])?;
            // This host returns proof bytes and retires its issued roots. It
            // has no caller-owned backend in which other affine outputs could
            // remain live, unlike the general bundle host.
            if role.outputs.iter().any(|ty| {
                ty.is_affine() && !matches!(ty.kind(), Type::Rng | Type::Nonce | Type::Transcript)
            }) {
                return Err("native-proof-output-kind".into());
            }
            let service_rows = list(&row[4])?;
            if service_rows.len() != role.services.len() {
                return Err("native-proof-service-map".into());
            }
            let mut services = Vec::new();
            for (row, service) in service_rows.iter().zip(&role.services) {
                let row = array(row, 4)?;
                let original = index(&row[0])?;
                if text(&row[1])? != service.name
                    || text(&row[2])? != service.contract.name()
                    || index(&row[3])? != service.input_index
                    || data.iter().any(|p| p.original == original)
                    || services.contains(&original)
                {
                    return Err("native-proof-service-map".into());
                }
                services.push(original);
            }
            if role_name == validator {
                let decision = index(&row[5])?;
                if outputs
                    .get(decision)
                    .is_none_or(|p| p.original != original_acceptance)
                {
                    return Err("native-proof-acceptance-map".into());
                }
                acceptance = Some(decision);
            } else if !text(&row[5])?.is_empty() {
                return Err("native-proof-acceptance-map".into());
            }
            if maps
                .insert(
                    role_name.to_owned(),
                    RoleMap {
                        data,
                        services,
                        outputs,
                    },
                )
                .is_some()
            {
                return Err("native-proof-role-map".into());
            }
        }
        if maps.len() != 2 || !maps.contains_key(producer) || !maps.contains_key(validator) {
            return Err("native-proof-role-map".into());
        }
        for port in &maps[producer].data {
            if maps[validator]
                .data
                .iter()
                .any(|other| other.original == port.original && other.logical != port.logical)
            {
                return Err("native-proof-shared-port-type".into());
            }
        }
        let mut public = Vec::new();
        for row in list(&descriptor[4])? {
            let row = array(row, 4)?;
            let original = index(&row[1])?;
            let logical = wire_type(text(&row[2])?, version, true)?;
            if text(&row[0])? != validator
                || wire_codec(&logical).as_deref() != Some(text(&row[3])?)
                || public.last().is_some_and(|p: &Port| p.original >= original)
            {
                return Err("native-proof-public-map".into());
            }
            public.push(Port { original, logical });
        }
        let required = &maps[validator].data;
        let selected = list(&policy[7])?
            .iter()
            .map(index)
            .collect::<Result<Vec<_>>>()?;
        if public.len() != required.len()
            || selected != public.iter().map(|p| p.original).collect::<Vec<_>>()
            || public
                .iter()
                .zip(required)
                .any(|(p, a)| p.original != a.original || p.logical != a.logical)
        {
            return Err("native-proof-public-map".into());
        }
        let keys = public
            .iter()
            .filter(|p| p.logical.kind() == Type::VerifierKey)
            .count();
        let needs_key = maps.values().flat_map(|m| &m.data).any(|p| {
            p.logical.identity() == zkc_runtime::interactive::Identity::MultilinearKzgBls12381
                || zkc_backends::requires_setup(p.logical.clone())
        }) || messages
            .values()
            .any(|t| zkc_backends::requires_setup(t.clone()));
        if (version != 4 && keys > 1) || keys > 64 || needs_key && keys == 0 {
            return Err("native-proof-setup-coverage".into());
        }
        if maps.values().flat_map(|m| &m.data).any(|port| {
            port.logical.kind() == Type::VerifierKey
                && !public
                    .iter()
                    .any(|p| p.original == port.original && p.logical == port.logical)
        }) {
            return Err("native-proof-verifier-key-port".into());
        }
        let setups = if let Some(authority) = authority {
            authority
        } else {
            let mut authority = SetupAuthority::default();
            if let Some(id) = key_id {
                if keys != 1 {
                    return Err("native-proof-key-authority".into());
                }
                let key = public
                    .iter()
                    .find(|p| p.logical.kind() == Type::VerifierKey)
                    .unwrap()
                    .original;
                authority.keys.insert(key, id);
                for port in maps
                    .values()
                    .flat_map(|m| &m.data)
                    .filter(|p| setups::needs_input_setup(&p.logical))
                {
                    authority.inputs.insert(port.original, key);
                }
            }
            authority
        };
        setups.check(&public, &maps)?;
        let admit_entry = if version == 4 {
            NativeProofEntry::new_structured
        } else if version == 3 {
            NativeProofEntry::new_committed
        } else if iterated {
            NativeProofEntry::new_iterated
        } else {
            NativeProofEntry::new
        };
        let proof_entry = admit_entry(
            admitted,
            entry,
            producer,
            validator,
            acceptance.ok_or("native-proof-acceptance-map")?,
            suite,
            &events,
        )
        .map_err(|e| e.to_string())?;
        Ok(Self {
            version,
            publication: expected_sha256.to_owned(),
            choices: [choices[0] == "true", choices[1] == "true"],
            external_work_limit: NativeBackend::DEFAULT_EXTERNAL_WORK_LIMIT,
            capacity: NativeCapacity::default(),
            setups,
            entry: proof_entry,
            source,
            descriptor: envelope[2].clone(),
            public,
            maps,
        })
    }
    /// Select invocation capacity independently of deployment/proof bytes.
    pub fn with_capacity(mut self, capacity: NativeCapacity) -> Result<Self> {
        capacity.check()?;
        self.capacity = capacity;
        Ok(self)
    }
    pub fn capacity(&self) -> NativeCapacity {
        self.capacity
    }
    pub fn entry(&self) -> &NativeProofEntry {
        &self.entry
    }
    // The source Host consumes this admitted view rather than decoding the
    // deployment carrier again or keeping a second interpretation of its ABI.
    pub(crate) fn source_interface(&self) -> SourceInterface<'_> {
        let policy = &self.descriptor[1];
        let suite = policy[5].as_str().expect("admitted policy suite");
        let service = policy[6].as_str().expect("admitted policy service");
        SourceInterface {
            version: self.version,
            publication: &self.publication,
            source: &self.source,
            choices: self.choices,
            acceptance: index(&policy[4]).expect("admitted acceptance"),
            suite: (!suite.is_empty()).then_some(suite),
            service: (!service.is_empty()).then(|| index(&policy[6]).expect("admitted service")),
            public: &self.public,
            roles: &self.maps,
        }
    }

    /// Configure each invocation's external primitive-work cap, up to the
    /// default. This setting applies to every later invocation on this value;
    /// each allowance covers all attempts and successful or failed trial calls.
    /// It changes no program or transcript bytes and is reported separately
    /// from deployment and attempt-policy identities. CLI execution uses the
    /// default cap. Zero permits only transitions with zero primitive work.
    pub fn with_external_work_limit(mut self, limit: u64) -> Result<Self> {
        if limit > NativeBackend::DEFAULT_EXTERNAL_WORK_LIMIT {
            return Err("native-proof-external-work-limit".into());
        }
        self.external_work_limit = limit;
        Ok(self)
    }

    /// Execute one independently admitted role. Public values, including complete
    /// verifier key bytes, must be authorized independently of the proof. This
    /// checks canonicality and consistency, not application authorization.
    pub fn execute(&self, input: &Json, proof: Option<&[u8]>) -> Result<NativeProofReport> {
        self.execute_with_entropy(
            inputs::Request::Encoded(input),
            Mode::one_shot(proof),
            &Entropy::System,
        )
    }
    /// Deterministic provider controls keyed by original input/service port.
    /// No file format or production command selects this test-only path.
    #[cfg(feature = "test-utils")]
    pub fn execute_test(
        &self,
        input: &Json,
        proof: Option<&[u8]>,
        tapes: BTreeMap<usize, Vec<zkc_backends::Scalar>>,
    ) -> Result<NativeProofReport> {
        self.execute_with_entropy(
            inputs::Request::Encoded(input),
            Mode::one_shot(proof),
            &test_entropy(tapes)?,
        )
    }
    /// Run bounded attempts. Policy ports use original common-program indices.
    /// Only a returned Boolean permits retry. The resulting bytes are unpublished.
    pub fn execute_attempts(
        &self,
        input: &Json,
        policy: &AttemptPolicy,
    ) -> Result<NativeProofReport> {
        self.execute_with_entropy(
            inputs::Request::Encoded(input),
            Mode::Attempts(policy.check(self)?),
            &Entropy::System,
        )
    }
    #[cfg(feature = "test-utils")]
    pub fn execute_attempts_test(
        &self,
        input: &Json,
        policy: &AttemptPolicy,
        tapes: BTreeMap<usize, Vec<zkc_backends::Scalar>>,
    ) -> Result<NativeProofReport> {
        let entropy = test_entropy(tapes)?;
        self.execute_with_entropy(
            inputs::Request::Encoded(input),
            Mode::Attempts(policy.check(self)?),
            &entropy,
        )
    }
    /// Execute immutable in-process data and explicit provider declarations.
    /// Public values are authorized independently of the candidate proof.
    pub fn execute_typed(
        &self,
        input: &ProofInputs,
        proof: Option<&[u8]>,
    ) -> Result<NativeProofReport> {
        self.execute_with_entropy(
            inputs::Request::Typed(input),
            Mode::one_shot(proof),
            &Entropy::System,
        )
    }
    pub fn execute_attempts_typed(
        &self,
        input: &ProofInputs,
        policy: &AttemptPolicy,
    ) -> Result<NativeProofReport> {
        self.execute_with_entropy(
            inputs::Request::Typed(input),
            Mode::Attempts(policy.check(self)?),
            &Entropy::System,
        )
    }
    #[cfg(feature = "test-utils")]
    pub fn execute_typed_test(
        &self,
        input: &ProofInputs,
        proof: Option<&[u8]>,
        tapes: BTreeMap<usize, Vec<zkc_backends::Scalar>>,
    ) -> Result<NativeProofReport> {
        self.execute_with_entropy(
            inputs::Request::Typed(input),
            Mode::one_shot(proof),
            &test_entropy(tapes)?,
        )
    }
    #[cfg(feature = "test-utils")]
    pub fn execute_attempts_typed_test(
        &self,
        input: &ProofInputs,
        policy: &AttemptPolicy,
        tapes: BTreeMap<usize, Vec<zkc_backends::Scalar>>,
    ) -> Result<NativeProofReport> {
        let entropy = test_entropy(tapes)?;
        self.execute_with_entropy(
            inputs::Request::Typed(input),
            Mode::Attempts(policy.check(self)?),
            &entropy,
        )
    }
    fn execute_with_entropy(
        &self,
        request: inputs::Request<'_>,
        mode: Mode<'_>,
        entropy: &Entropy,
    ) -> Result<NativeProofReport> {
        let (proof, attempts) = match mode {
            Mode::Prove => (None, None),
            Mode::Verify(proof) => (Some(proof), None),
            Mode::Attempts(plan) => (None, Some(plan)),
        };
        if proof.is_some_and(|p| p.len() > super::MAX_PROOF_BYTES) {
            return Err("native-proof-proof-limit".into());
        }
        let decoded;
        let input = match request {
            inputs::Request::Encoded(input) => {
                decoded = inputs::decode(self, input, proof.is_none())?;
                &decoded
            }
            inputs::Request::Typed(input) => input,
        };
        let role = if proof.is_none() {
            self.entry.producer()
        } else {
            self.entry.validator()
        };
        let mapping = &self.maps[&role.role];
        let inputs::Prepared {
            mut backend,
            loaded,
            planned,
            root,
            binding,
        } = inputs::prepare(self, input, role, proof.is_none())?;
        let policy = self.capacity.backend();
        let transcript_budget = input.transcript_budget;
        let service_budgets = input.services.iter().copied();
        let domain = Domain::new(
            &role.role,
            "native-proof",
            self.entry.entry(),
            Some(&role.instance),
        );
        let registry = ServiceRegistry::new(policy);
        let mut resources: Vec<Capability> = Vec::new();
        let mut services: Vec<ServiceReference> = Vec::new();
        let setup = (|| -> Result<Vec<Value>> {
            let mut values = Vec::new();
            for (item, port) in planned.into_iter().zip(&mapping.data) {
                let value = match item {
                    Operand::Data(index) => loaded[index].clone(),
                    Operand::Resource(ResourceInput {
                        kind,
                        field,
                        budget,
                    }) => entropy.capability(
                        &mut backend,
                        kind,
                        field,
                        port.original,
                        domain.clone(),
                        budget,
                    )?,
                };
                if let Value::Nonce(t) | Value::Rng(t) = &value {
                    resources.push(t.clone());
                }
                values.push(value);
            }
            if let Some(ty) = self.entry.transcript().filter(|_| attempts.is_none()) {
                let state = backend
                    .issue_transcript_for(
                        ty.logical().identity(),
                        domain.clone(),
                        transcript_budget,
                        &root,
                    )
                    .map_err(|e| e.to_string())?;
                if let Value::Transcript(t) = &state {
                    resources.push(t.clone());
                }
                values.push(state);
            }
            let mut service_ports = BTreeMap::new();
            for ((port, budget), service) in mapping
                .services
                .iter()
                .zip(service_budgets)
                .zip(&role.services)
            {
                let reference =
                    entropy.service(&registry, &role.role, service.contract, *port, budget)?;
                service_ports.insert(service.name.clone(), reference.clone());
                services.push(reference);
            }
            if !service_ports.is_empty() && attempts.is_none() {
                backend
                    .install_services(registry.clone(), service_ports)
                    .map_err(|e| e.to_string())?;
            }
            Ok(values)
        })();
        let mut report = NativeProofReport {
            outputs: None,
            outcome: Ok(Vec::new()),
            binding: hex(&binding),
            messages: 0,
            bytes: 0,
            cancelled: false,
            instructions: 0,
            resources: Vec::new(),
            attempts: Vec::new(),
            return_at: None,
            stop: None,
            attempt_policy: attempts.as_ref().map(|plan| plan.policy.identity()),
            usage: Default::default(),
            external_work: 0,
            external_work_limit: self.external_work_limit,
            cleanup_errors: Vec::new(),
        };
        match setup {
            Err(error) => report.outcome = Err(error),
            Ok(values) if attempts.is_some() => {
                let plan = attempts.as_ref().expect("checked attempt policy");
                backend = attempts::execute(
                    self,
                    backend,
                    values,
                    &root,
                    &binding,
                    domain.clone(),
                    transcript_budget,
                    &registry,
                    &services,
                    plan,
                    &mut report,
                );
            }
            Ok(values) => match Runner::new_with_budgets(
                self.entry.admitted(),
                self.entry.entry(),
                &role.role,
                "native-proof",
                backend,
                values,
                self.capacity.values,
                self.capacity.work,
            ) {
                Err(failed) => {
                    report.outcome = Err(failed.error.to_string());
                    report.usage = failed.usage;
                    backend = failed.backend;
                }
                Ok(mut runner) => {
                    match proof {
                        None => {
                            let produced = driver::produce_admitted(
                                &mut runner,
                                &binding,
                                true,
                                |backend, value| {
                                    backend
                                        .encode_native_value(value)
                                        .map_err(driver::ArtifactFailure::NativeWire)
                                },
                            );
                            retain_driver_stop(&mut report, &produced);
                            report.outcome = produced
                                .outcome
                                .map(|p| {
                                    report.outputs = Some(self.original_outputs(role, p.outputs));
                                    p.proof
                                })
                                .map_err(|e| host::failure(&e));
                            report.messages = produced.messages;
                            report.bytes = produced.bytes;
                            report.cancelled = produced.cancelled.is_some();
                        }
                        Some(proof) => {
                            let validated = driver::validate_native(
                                &mut runner,
                                proof,
                                &binding,
                                self.entry.acceptance(),
                            );
                            retain_driver_stop(&mut report, &validated);
                            report.outcome = validated
                                .outcome
                                .map(|values| {
                                    report.outputs = Some(self.original_outputs(role, values));
                                    Vec::new()
                                })
                                .map_err(|e| host::failure(&e));
                            report.messages = validated.messages;
                            report.bytes = validated.bytes;
                            report.cancelled = validated.cancelled.is_some();
                        }
                    }
                    report.usage = runner.usage();
                    report.return_at = runner.early_return().map(|(o, s)| (o.clone(), s.into()));
                    backend = runner.into_backend();
                }
            },
        }
        report.instructions = report.usage.instructions;
        report.external_work = backend.external_work_spent();
        retire_resources(&mut backend, &registry, &resources, &services, &mut report);
        Ok(report)
    }
    /// Native admission has checked the output map against the role signature.
    /// Private successors belong to cleanup, not immutable application results.
    fn original_outputs(&self, role: &EntryRole, values: Vec<Value>) -> BTreeMap<usize, Value> {
        self.maps[&role.role]
            .outputs
            .iter()
            .zip(&role.outputs)
            .zip(values)
            .filter_map(|((port, ty), value)| ty.is_duplicable().then_some((port.original, value)))
            .collect()
    }
}
fn retire_resources(
    backend: &mut NativeBackend,
    registry: &ServiceRegistry,
    resources: &[Capability],
    services: &[ServiceReference],
    report: &mut NativeProofReport,
) {
    let mut observations = Vec::new();
    // Retirement uses the root identity, including after a failed successor
    // transition. It requires all frames and service leases to have ended.
    for resource in resources {
        match backend.retire(resource) {
            Ok(o) => observations.push(json!({"kind":"capability", "generation":o.generation,
                "transitions":o.draw_count, "budget":o.budget, "stage":o.stage})),
            Err(e) => {
                report.cleanup_errors.push(e.to_string());
            }
        }
    }
    for reference in services {
        match registry.retire(reference) {
            Ok(o) => observations.push(json!({"kind":"service", "owner":o.owner,
                "leased":o.leased, "poisoned":o.poisoned,
                "state":o.state.map(|s| json!({"generation":s.generation, "transitions":s.draw_count,
                    "budget":s.budget, "stage":s.stage}))})),
            Err(e) => { report.cleanup_errors.push(e.to_string()); }
        }
    }
    if backend.active_frames() != 0 {
        report
            .cleanup_errors
            .push("native-proof-active-frames".into());
    }
    if backend.live_resource_units() != 0 {
        report
            .cleanup_errors
            .push("native-proof-live-resource-units".into());
    }
    if !report.cleanup_errors.is_empty() && report.outcome.is_ok() {
        report.outcome = Err("native-proof-cleanup".into());
    }
    if report.outcome.is_err() {
        report.outputs = None;
    }
    report.resources = observations;
}
fn budget(value: &Json) -> Result<u64> {
    let n = logical::natural_index(text(value)?).map_err(|e| e.to_string())?;
    inputs::check_budget(n)?;
    Ok(n)
}
pub struct NativeProofReport {
    pub outcome: Result<Vec<u8>>,
    /// Successful copyable results indexed by their original protocol output
    /// port. Absent on rejection, stop, refusal or cleanup failure. Private
    /// successors are retired; CLI diagnostic reports do not serialize outputs.
    pub outputs: Option<BTreeMap<usize, Value>>,
    pub binding: String,
    pub messages: usize,
    pub bytes: usize,
    pub cancelled: bool,
    pub instructions: u64,
    pub resources: Vec<Json>,
    pub attempts: Vec<AttemptRecord>,
    pub attempt_policy: Option<String>,
    /// One-shot owner-local completion. Attempts keep their own coordinates.
    pub return_at: Option<(zkc_runtime::interactive::Origin, String)>,
    /// One-shot execution or host-cancellation stop; attempts retain their own.
    pub stop: Option<zkc_runtime::interactive::Stop>,
    pub usage: zkc_runtime::interactive::Usage,
    pub external_work: u64,
    pub external_work_limit: u64,
    /// Cleanup failures remain separate from the primary body failure.
    pub cleanup_errors: Vec<String>,
}
fn stop_json(s: &zkc_runtime::interactive::Stop) -> Json {
    json!({"origin":s.origin.json(),"role":s.role,"site":s.site,
        "local":s.local.as_ref().map(|l|json!({"site":l.site,"function":l.function,"instruction":l.instruction})),
        "kind":format!("{:?}",s.kind),
        "cleanup_errors":s.cleanup_errors.iter().map(ToString::to_string).collect::<Vec<_>>()})
}
impl NativeProofReport {
    /// Payload-free execution diagnostics, including failed attempts and cleanup.
    pub fn diagnostics(&self) -> Json {
        let mut report = json!({});
        report["binding_sha256"] = json!(self.binding);
        report["messages"] = json!(self.messages);
        report["bytes"] = json!(self.bytes);
        report["cancelled"] = json!(self.cancelled);
        report["instructions"] = json!(self.instructions);
        report["resources"] = json!(self.resources);
        report["attempt_policy_sha256"] = json!(self.attempt_policy);
        report["return_at"] = json!(
            self.return_at
                .as_ref()
                .map(|(o, s)| json!({"origin":o.json(), "site":s}))
        );
        report["stop"] = json!(self.stop.as_ref().map(stop_json));
        report["cleanup_errors"] = json!(self.cleanup_errors);
        report["external_work"] = json!(self.external_work);
        report["external_work_limit"] = json!(self.external_work_limit);
        report["calls"] = json!(self.usage.calls);
        report["iterations"] = json!(self.usage.iterations);
        report["total_value_bytes"] = json!(self.usage.total_value_bytes);
        report["attempts"] = json!(self.attempts.iter().map(|r| json!({
            "attempt":r.attempt, "decision":match &r.decision {
                Ok(true)=>"complete", Ok(false)=>"retry", Err(_)=>"stopped"},
            "error":r.decision.as_ref().err(), "messages":r.messages,"bytes":r.bytes,
            "instructions":r.usage.instructions,"calls":r.usage.calls,"iterations":r.usage.iterations,
            "total_value_bytes":r.usage.total_value_bytes,"transcript":r.transcript,
            "external_work":r.external_work,
            "return_at":r.return_at.as_ref().map(|(o,s)|json!({"origin":o.json(),"site":s})),
            "stop":r.stop.as_ref().map(stop_json)
        })).collect::<Vec<_>>());
        report
    }
}
pub fn run(produce: bool, args: &[String]) -> Json {
    let mut report =
        json!({"format":"zkc.native-proof-run/1", "status":"refused", "phase":"admission"});
    let result = (|| -> Result<()> {
        let [
            deployment_path,
            expected_digest,
            inputs_path,
            proof_path,
            options @ ..,
        ] = args
        else {
            return Err("usage: produce-native-proof|validate-native-proof DEPLOYMENT EXPECTED_SHA256 INPUTS PROOF [--key-id=EXPECTED_KEY_ID | --setups=AUTHORITY] [--attempts=POLICY] [--capacity=LIMITS]".into());
        };
        let mut expected_key = None;
        let mut authority = None;
        let mut attempts = None;
        let mut capacity = None;
        for option in options {
            if let Some(value) = option
                .strip_prefix("--key-id=")
                .filter(|_| expected_key.is_none() && authority.is_none())
            {
                digest(value)?;
                expected_key = Some(
                    unhex(&json!(value))?
                        .try_into()
                        .map_err(|_| "native-proof-key-authority")?,
                );
            } else if let Some(path) = option
                .strip_prefix("--setups=")
                .filter(|_| authority.is_none() && expected_key.is_none())
            {
                authority = Some(SetupAuthority::parse(&read(path, 64 * 1024)?)?);
            } else if let Some(path) = option
                .strip_prefix("--attempts=")
                .filter(|_| produce && attempts.is_none())
            {
                attempts = Some(AttemptPolicy::parse(&read(path, 64 * 1024)?)?);
            } else if let Some(path) = option
                .strip_prefix("--capacity=")
                .filter(|_| capacity.is_none())
            {
                capacity = Some(NativeCapacity::parse(&read(path, 4096)?)?);
            } else {
                return Err("native-proof-option".into());
            }
        }
        let deployment = NativeDeployment::admit_configured(
            &read(deployment_path, INPUT_LIMIT)?,
            expected_digest,
            expected_key,
            authority,
        )?
        .with_capacity(capacity.unwrap_or_default())?;
        report["binding_scope"] = json!(if deployment.entry().transcript().is_some() {
            "transcript"
        } else {
            "header"
        });
        report["capacity"] = deployment.capacity().record();
        report["phase"] = json!("inputs");
        let inputs = parse(&read(inputs_path, INPUT_LIMIT)?, INPUT_LIMIT)?;
        let proof = if produce {
            None
        } else {
            Some(read(proof_path, super::MAX_PROOF_BYTES)?)
        };
        let result = match attempts {
            Some(policy) => deployment.execute_attempts(&inputs, &policy)?,
            None => deployment.execute(&inputs, proof.as_deref())?,
        };
        report["phase"] = json!("execution");
        report
            .as_object_mut()
            .unwrap()
            .extend(result.diagnostics().as_object().unwrap().clone());
        if produce {
            report["proof_bytes"] = json!(result.outcome.as_ref().map_or(0, Vec::len));
        }
        let bytes = result.outcome?;
        if produce {
            crate::host::io::publish(proof_path, &bytes)?;
        }
        report["phase"] = json!("complete");
        report["status"] = json!(if produce { "produced" } else { "accepted" });
        Ok(())
    })();
    if let Err(error) = result {
        report["code"] = json!(error);
    }
    report
}

#[cfg(test)]
mod tests;
