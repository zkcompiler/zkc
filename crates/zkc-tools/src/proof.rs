//! Independent proof execution with an application-pinned deployment.
mod attempts;
mod inputs;
mod interface;
mod messages;
use crate::execution::Capacity;
use crate::execution::InputValue;
pub use inputs::ProofInputs;
mod driver;
mod entropy;
mod setups;
mod wire;
use crate::host::admission::{Admission, Input, Operand, ResourceInput, entry_values};
use crate::host::inputs::*;
pub use attempts::{AttemptPolicy, AttemptRecord};
pub use driver::{ArtifactFailure, ArtifactReport, Produced};
use entropy::Entropy;
use serde_json::{Value as Json, json};
pub use setups::SetupAuthority;
use sha2::{Digest, Sha256};
use std::collections::BTreeMap;
pub use wire::{FormatError, MAX_PROOF_BYTES, ProofReader, ProofWriter};
use zkc_backends::{
    Capability, Domain, EntryPolicy, NativeBackend, Policy, Value,
    services::{ServiceReference, ServiceRegistry},
};
use zkc_runtime::{
    interactive::{
        EntryRole, Identity, LogicalType, NativeProofEntry, PhysicalType, Runner, Type,
        admit_supplied,
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
    ring_assets: zkc_backends::ring::Registry,
    relation_assets: zkc_backends::relation::Registry,
    ring_work_limit: u64,
    publication: String,
    choices: [bool; 2],
    external_work_limit: u64,
    capacity: Capacity,
    setups: SetupAuthority,
    entry: NativeProofEntry,
    source: String,
    descriptor: Json,
    public: Vec<Port>,
    maps: BTreeMap<String, RoleMap>,
}
pub(crate) struct SourceInterface<'a> {
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
/// The operation requested by an independently admitted proof participant.
#[derive(Clone, Copy)]
pub enum Invocation<'a> {
    Prove,
    Verify(&'a [u8]),
    Attempts(&'a AttemptPolicy),
}
impl<'a> Invocation<'a> {
    pub fn one_shot(proof: Option<&'a [u8]>) -> Self {
        proof.map_or(Self::Prove, Self::Verify)
    }
    pub fn is_producer(self) -> bool {
        !matches!(self, Self::Verify(_))
    }
    fn plan(self, host: &NativeDeployment) -> Result<Mode<'a>> {
        Ok(match self {
            Self::Prove => Mode::Prove,
            Self::Verify(proof) => Mode::Verify(proof),
            Self::Attempts(policy) => Mode::Attempts(policy.check(host)?),
        })
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
    crate::host::inputs::digest(value)
        .map(|_| ())
        .map_err(|_| "native-proof-digest".into())
}

fn wire_type(value: &str, public: bool) -> Result<LogicalType> {
    let ty = LogicalType::parse(value).map_err(|e| e.to_string())?;
    if !(ty.is_native_message_data()
        || public
            && matches!(
                value,
                "table:bls12-381.fr" | "verifier_key:multilinear.kzg.bls12-381/0"
            ))
    {
        return Err("native-proof-wire-type".into());
    }
    Ok(ty)
}
fn wire_codec(ty: &LogicalType) -> Option<String> {
    if PhysicalType::default_for(ty.clone()).is_ok_and(|t| t.has_native_data_frame()) {
        Some("zkc.native-data/0".into())
    } else if ty.kind() == Type::VerifierKey {
        Some("zkc.native-verifier-key/0".into())
    } else if ty.field_array_parts().is_some() {
        Some("zkc.native-field-array/0".into())
    } else {
        ty.codec()
    }
}

// This host's entry constructors are narrower than ordinary local IR types.
// Share the decision between deployment admission and invocation planning.
fn input_kind(ty: &PhysicalType) -> Result<&'static str> {
    if zkc_backends::has_native_wire(ty) {
        return Ok("wire");
    }
    let logical = ty.logical();
    if PhysicalType::default_for(logical.clone()).ok().as_ref() == Some(ty) {
        match (logical.kind(), logical.identity()) {
            (Type::Nonce, Identity::Bls12381Fr | Identity::Ristretto255Scalar) => {
                return Ok("nonce");
            }
            (Type::Rng, field)
                if zkc_runtime::interactive::ServiceContract::for_field(field).is_some() =>
            {
                return Ok("rng");
            }
            (Type::VerifierKey, Identity::MultilinearKzgBls12381) => {
                return Ok("verifier_key");
            }
            (Type::ProverKey, Identity::MultilinearKzgBls12381) => {
                return Ok("prover_key_file");
            }
            _ => {}
        }
    }
    Err("native-proof-role-input-type".into())
}

fn backend(
    policy: Policy,
    role: &EntryRole,
    entry: &str,
    keys: zkc_backends::SetupRegistry,
    ports: BTreeMap<String, zkc_backends::PortConstraint>,
) -> Result<NativeBackend> {
    NativeBackend::new(
        policy,
        EntryPolicy::new(
            Domain::new(&role.role, "native-proof", entry, Some(&role.instance)),
            None,
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
    pub fn admit(
        bytes: &[u8],
        expected_sha256: &[u8; 32],
        authority: SetupAuthority,
    ) -> Result<Self> {
        if bytes.len() > INPUT_LIMIT {
            return Err("native-proof-deployment-limit".into());
        }
        let identity: [u8; 32] = Sha256::digest(bytes).into();
        if &identity != expected_sha256 {
            return Err("native-proof-deployment-binding".into());
        }
        Self::admit_payload(bytes, &hex(expected_sha256), authority)
    }
    pub(crate) fn admit_artifact(
        artifact: &crate::entry::AuthenticatedArtifact<'_>,
        authority: SetupAuthority,
    ) -> Result<Self> {
        Self::admit_payload(artifact.bytes(), &hex(artifact.identity()), authority)
    }
    // The public loader checks the caller's deployment pin; the private view
    // borrows exact artifact bytes from a Package captured against its caller's
    // package pin. Callers own the independent trust in either pin. All structural
    // checks remain here.
    fn admit_payload(
        bytes: &[u8],
        expected_sha256: &str,
        authority: SetupAuthority,
    ) -> Result<Self> {
        let value = parse(bytes, INPUT_LIMIT)?;
        let envelope = array(&value, 9)?;
        if text(&envelope[0])? != "zkc.native-proof/0" {
            return Err("native-proof-format".into());
        }
        let source = text(&envelope[1])?.to_owned();
        digest(&source)?;
        let descriptor = array(&envelope[2], 6)?;
        if text(&descriptor[0])? != "zkc.native-proof-descriptor/0"
            || text(&descriptor[2])? != "zkc.native-origin/0"
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
        let policy = interface::DeploymentPolicy::read(&descriptor[1])?;
        let (entry, producer, validator) = (policy.entry, policy.producer, policy.validator);
        let suite = policy.suite;
        let admitted = {
            let dummy = NativeBackend::new(
                Policy::default(),
                EntryPolicy::new(Domain::new(producer, "native-proof", entry, None), None),
                Default::default(),
            )
            .map_err(|e| e.to_string())?;
            admit_supplied(candidate.as_bytes(), &dummy).map_err(|e| e.to_string())?
        };
        let messages = messages::MessageLayout::read(descriptor, &policy)?;
        messages.check_wire(&envelope[8], &admitted, entry)?;
        let interface::RoleInterface {
            maps,
            public,
            acceptance,
        } = interface::RoleInterface::read(&admitted, &policy, &envelope[6], &descriptor[4])?;
        let keys = public
            .iter()
            .filter(|p| p.logical.kind() == Type::VerifierKey)
            .count();
        let needs_key = maps.values().flat_map(|m| &m.data).any(|p| {
            p.logical.identity() == zkc_runtime::interactive::Identity::MultilinearKzgBls12381
                || zkc_backends::requires_setup(p.logical.clone())
        }) || messages
            .payload_types
            .values()
            .any(|t| zkc_backends::requires_setup(t.clone()));
        if keys > 64 || needs_key && keys == 0 {
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
        let setups = authority;
        setups.check(&public, &maps)?;
        let proof_entry = NativeProofEntry::new(
            admitted,
            entry,
            producer,
            validator,
            acceptance.ok_or("native-proof-acceptance-map")?,
            suite,
            &messages.events,
        )
        .map_err(|e| e.to_string())?;
        Ok(Self {
            ring_assets: Default::default(),
            relation_assets: Default::default(),
            ring_work_limit: zkc_backends::ring::DEFAULT_WORK_LIMIT,
            publication: expected_sha256.to_owned(),
            choices: [choices[0] == "true", choices[1] == "true"],
            external_work_limit: NativeBackend::DEFAULT_EXTERNAL_WORK_LIMIT,
            capacity: Capacity::default(),
            setups,
            entry: proof_entry,
            source,
            descriptor: envelope[2].clone(),
            public,
            maps,
        })
    }
    /// Select invocation capacity independently of deployment/proof bytes.
    pub fn with_capacity(mut self, capacity: Capacity) -> Result<Self> {
        capacity.validate()?;
        self.capacity = capacity;
        Ok(self)
    }
    pub fn capacity(&self) -> Capacity {
        self.capacity
    }
    pub fn with_ring_assets(mut self, assets: zkc_backends::ring::Registry) -> Self {
        self.ring_assets = assets;
        self
    }
    pub fn with_relation_assets(mut self, assets: zkc_backends::relation::Registry) -> Self {
        self.relation_assets = assets;
        self
    }
    pub fn with_ring_work_limit(mut self, limit: u64) -> Result<Self> {
        if limit > zkc_backends::ring::DEFAULT_WORK_LIMIT {
            return Err("native-proof-ring-work-limit".into());
        }
        self.ring_work_limit = limit;
        Ok(self)
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

    /// Execute immutable role inputs with an explicit production, verification
    /// or retry request. Public inputs and setups remain application-authorized.
    pub fn execute(
        &self,
        input: &ProofInputs,
        invocation: Invocation<'_>,
    ) -> Result<NativeProofReport> {
        let mut imports =
            crate::host::setups::VerifierKeys::new(self.capacity.backend().ark_bounds());
        self.execute_prepared(input, invocation, &mut imports)
    }
    /// Deterministic provider controls for tests. No production command or file
    /// format selects this feature-gated entry point.
    #[cfg(feature = "test-utils")]
    pub fn execute_test(
        &self,
        input: &ProofInputs,
        invocation: Invocation<'_>,
        tapes: BTreeMap<usize, Vec<zkc_backends::Scalar>>,
    ) -> Result<NativeProofReport> {
        let entropy = test_entropy(tapes)?;
        let mut imports =
            crate::host::setups::VerifierKeys::new(self.capacity.backend().ark_bounds());
        self.execute_with_imports(input, invocation.plan(self)?, &entropy, &mut imports)
    }
    pub(crate) fn execute_prepared(
        &self,
        input: &ProofInputs,
        invocation: Invocation<'_>,
        imports: &mut crate::host::setups::VerifierKeys,
    ) -> Result<NativeProofReport> {
        self.execute_with_imports(input, invocation.plan(self)?, &Entropy::System, imports)
    }
    /// Admit and load a complete invocation without issuing resources or
    /// interpreting proof bytes. Both execution and input checks use this stage.
    pub fn check_inputs(&self, input: &ProofInputs, invocation: Invocation<'_>) -> Result<()> {
        invocation.plan(self)?;
        let mut imports =
            crate::host::setups::VerifierKeys::new(self.capacity.backend().ark_bounds());
        self.prepare_inputs(input, invocation.is_producer(), &mut imports)
            .map(|_| ())
    }
    fn prepare_inputs(
        &self,
        input: &ProofInputs,
        producer: bool,
        imports: &mut crate::host::setups::VerifierKeys,
    ) -> Result<inputs::Prepared> {
        let role = if producer {
            self.entry.producer()
        } else {
            self.entry.validator()
        };
        inputs::prepare(self, input, role, producer, imports)
    }
    fn execute_with_imports(
        &self,
        input: &ProofInputs,
        mode: Mode<'_>,
        entropy: &Entropy,
        imports: &mut crate::host::setups::VerifierKeys,
    ) -> Result<NativeProofReport> {
        let (proof, attempts) = match mode {
            Mode::Prove => (None, None),
            Mode::Verify(proof) => (Some(proof), None),
            Mode::Attempts(plan) => (None, Some(plan)),
        };
        if proof.is_some_and(|p| p.len() > MAX_PROOF_BYTES) {
            return Err("native-proof-proof-limit".into());
        }
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
        } = self.prepare_inputs(input, proof.is_none(), imports)?;
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
            ring_work: 0,
            ring_work_limit: self.ring_work_limit,
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
                                .map_err(|e| driver::failure(&e));
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
                                .map_err(|e| driver::failure(&e));
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
        report.ring_work = backend.ring_work_spent();
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
    pub ring_work: u64,
    pub ring_work_limit: u64,
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
        report["ring_work"] = json!(self.ring_work);
        report["ring_work_limit"] = json!(self.ring_work_limit);
        report["external_work_limit"] = json!(self.external_work_limit);
        report["iterations"] = json!(self.usage.iterations);
        report["total_value_bytes"] = json!(self.usage.total_value_bytes);
        report["logical_bytes"] = json!(self.usage.logical_bytes);
        report["attempts"] = json!(self.attempts.iter().map(|r| json!({
            "attempt":r.attempt, "decision":match &r.decision {
                Ok(true)=>"complete", Ok(false)=>"retry", Err(_)=>"stopped"},
            "error":r.decision.as_ref().err(), "messages":r.messages,"bytes":r.bytes,
            "instructions":r.usage.instructions,"iterations":r.usage.iterations,
            "total_value_bytes":r.usage.total_value_bytes,"logical_bytes":r.usage.logical_bytes,
            "transcript":r.transcript,
            "external_work":r.external_work,
            "ring_work":r.ring_work,
            "return_at":r.return_at.as_ref().map(|(o,s)|json!({"origin":o.json(),"site":s})),
            "stop":r.stop.as_ref().map(stop_json)
        })).collect::<Vec<_>>());
        report
    }
}
pub(crate) mod cli;

#[cfg(test)]
mod tests;
