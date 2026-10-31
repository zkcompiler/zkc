//! Independent proof execution with an application-pinned deployment.
use zkc_runtime::interpreter::Runner;
mod attempts;
mod inputs;
mod interface;
mod messages;
mod selection;
use crate::execution::InputValue;
use crate::execution::{Capacity, CpuExecution};
pub use inputs::ProofInputs;
use zkc_runtime::host::proof::{self as driver, ArtifactFailure, ArtifactReport};
mod entropy;
mod setups;
use crate::host::admission::{Admission, Input, Operand, ResourceInput, entry_values};
use crate::io::bytes::*;
pub use attempts::{AttemptPolicy, AttemptRecord};
use entropy::Entropy;
use serde_json::{Value as Json, json};
pub use setups::SetupAuthority;
use sha2::{Digest, Sha256};
use std::collections::BTreeMap;
use zkc_cpu::{
    Capability, CpuBackend, Domain, EntryPolicy, Policy, Value,
    services::{ServiceReference, ServiceRegistry},
};
use zkc_format::logical;
pub use zkc_format::proof::MAX_PROOF_BYTES;
use zkc_format::proof::ProofFormat;
use zkc_runtime::vm::{
    EntryRole, Identity, LogicalType, NativeProofEntry, PhysicalType, PreparationLimits,
    PreparationStats, PreparedComputations, Type,
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
/// Low-level deployment admitted against an independently supplied digest.
/// This API executes the pinned algorithm, including authored constructions;
/// it does not impose an application binding policy. Use [`crate::entry::ProofEntry`]
/// with [`crate::entry::ProofOptions`] to require managed transcript binding.
#[derive(Clone)]
pub struct NativeDeployment {
    installation: zkc_cpu::CpuInstallation,
    cpu: CpuExecution,
    ring_assets: zkc_cpu::ring::Registry,
    relation_assets: zkc_cpu::relation::Registry,
    ring_work_limit: u64,
    sequence_work_limit: u64,
    shared_ledger: Option<zkc_runtime::vm::ExecutionLedger>,
    retained_inputs: bool,
    operation: Option<bool>,
    proof_bytes_limit: usize,
    publication: String,
    choices: [String; 7],
    external_work_limit: u64,
    capacity: Capacity,
    setups: SetupAuthority,
    entry: NativeProofEntry,
    preparation: PreparedComputations<CpuBackend>,
    source: String,
    descriptor: Json,
    binding_metadata_bytes: usize,
    format: ProofFormat,
    public: Vec<Port>,
    public_types: Vec<PhysicalType>,
    maps: BTreeMap<String, RoleMap>,
}
pub(crate) struct SourceInterface<'a> {
    pub publication: &'a str,
    pub source: &'a str,
    pub choices: &'a [String; 7],
    pub acceptance: usize,
    pub suite: Option<&'a str>,
    pub construction: &'a str,
    pub gates: &'a [Json],
    pub format: ProofFormat,
    pub services: Vec<usize>,
    pub public: &'a [Port],
    pub roles: &'a BTreeMap<String, RoleMap>,
    pub operation: Option<bool>,
    pub producer: &'a str,
    pub validator: &'a str,
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
        if host
            .operation
            .is_some_and(|producer| producer != self.is_producer())
        {
            return Err("native-proof-operation".into());
        }
        Ok(match self {
            Self::Prove => Mode::Prove,
            Self::Verify(proof) => Mode::Verify(proof),
            Self::Attempts(policy) => Mode::Attempts(policy.check(host)?),
        })
    }
}
#[cfg(feature = "test-utils")]
fn test_entropy<T: Into<zkc_cpu::TestTape>>(tapes: BTreeMap<usize, T>) -> Result<Entropy> {
    let tapes: BTreeMap<_, zkc_cpu::TestTape> = tapes
        .into_iter()
        .map(|(port, t)| (port, t.into()))
        .collect();
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
    crate::io::bytes::digest(value)
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
fn input_kind(ty: &PhysicalType, installation: &zkc_cpu::CpuInstallation) -> Result<&'static str> {
    if !installation.supports_type(ty) {
        return Err("native-proof-role-input-type".into());
    }
    if installation.supports_wire(ty) {
        return Ok("wire");
    }
    let logical = ty.logical();
    if PhysicalType::default_for(logical.clone()).ok().as_ref() == Some(ty) {
        match (logical.kind(), logical.identity()) {
            (Type::Nonce, Identity::Bls12381Fr | Identity::Ristretto255Scalar) => {
                return Ok("nonce");
            }
            (Type::Rng, field) if zkc_runtime::vm::ServiceContract::for_field(field).is_some() => {
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
    keys: zkc_cpu::SetupRegistry,
    ports: BTreeMap<String, zkc_cpu::PortConstraint>,
    cpu: CpuExecution,
    installation: zkc_cpu::CpuInstallation,
) -> Result<CpuBackend> {
    CpuBackend::new_with_installation(
        policy,
        EntryPolicy::new(
            Domain::new(&role.role, "native-proof", entry, Some(&role.instance)),
            None,
        )
        .with_ports(ports),
        keys,
        cpu,
        installation,
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
    pub fn installation(&self) -> &zkc_cpu::CpuInstallation {
        &self.installation
    }

    /// `expected_sha256` must come from the application's trusted compilation or
    /// deployment configuration, independently of these supplied bytes and proof.
    pub fn admit(
        bytes: &[u8],
        expected_sha256: &[u8; 32],
        authority: SetupAuthority,
    ) -> Result<Self> {
        Self::admit_with_cpu(
            bytes,
            expected_sha256,
            authority,
            CpuExecution::serial().map_err(|e| e.to_string())?,
        )
    }
    /// Admit with the context retained by preparation and every proof role.
    pub fn admit_with_cpu(
        bytes: &[u8],
        expected_sha256: &[u8; 32],
        authority: SetupAuthority,
        cpu: CpuExecution,
    ) -> Result<Self> {
        Self::admit_with_installation(bytes, expected_sha256, authority, cpu, Default::default())
    }
    /// Select CPU support before decoding or admitting the pinned deployment.
    pub fn admit_with_installation(
        bytes: &[u8],
        expected_sha256: &[u8; 32],
        authority: SetupAuthority,
        cpu: CpuExecution,
        installation: zkc_cpu::CpuInstallation,
    ) -> Result<Self> {
        if bytes.len() > INPUT_LIMIT {
            return Err("native-proof-deployment-limit".into());
        }
        let identity: [u8; 32] = Sha256::digest(bytes).into();
        if &identity != expected_sha256 {
            return Err("native-proof-deployment-binding".into());
        }
        Self::admit_payload(
            bytes,
            &hex(expected_sha256),
            authority,
            None,
            false,
            cpu,
            installation,
        )
    }
    pub(crate) fn admit_artifact(
        artifact: &crate::entry::AuthenticatedArtifact<'_>,
        authority: SetupAuthority,
        cpu: CpuExecution,
        installation: zkc_cpu::CpuInstallation,
    ) -> Result<Self> {
        Self::admit_artifact_operation(artifact, authority, None, cpu, installation)
    }
    pub(crate) fn admit_artifact_operation(
        artifact: &crate::entry::AuthenticatedArtifact<'_>,
        authority: SetupAuthority,
        operation: Option<bool>,
        cpu: CpuExecution,
        installation: zkc_cpu::CpuInstallation,
    ) -> Result<Self> {
        Self::admit_payload(
            artifact.bytes(),
            &hex(artifact.identity()),
            authority,
            operation,
            false,
            cpu,
            installation,
        )
    }
    pub(crate) fn admit_host_operation(
        artifact: &crate::entry::AuthenticatedArtifact<'_>,
        authority: SetupAuthority,
        producer: bool,
        cpu: CpuExecution,
        installation: zkc_cpu::CpuInstallation,
    ) -> Result<Self> {
        Self::admit_payload(
            artifact.bytes(),
            &hex(artifact.identity()),
            authority,
            Some(producer),
            true,
            cpu,
            installation,
        )
    }
    // The public loader checks the caller's deployment pin; the private view
    // borrows exact artifact bytes from a Package captured against its caller's
    // package pin. Callers own the independent trust in either pin. All structural
    // checks remain here.
    fn admit_payload(
        bytes: &[u8],
        expected_sha256: &str,
        authority: SetupAuthority,
        operation: Option<bool>,
        retained_inputs: bool,
        cpu: CpuExecution,
        installation: zkc_cpu::CpuInstallation,
    ) -> Result<Self> {
        let value = parse(bytes, INPUT_LIMIT)?;
        let envelope = array(&value, 9)?;
        if text(&envelope[0])? != "zkc.native-proof/0" {
            return Err("native-proof-format".into());
        }
        let source = text(&envelope[1])?.to_owned();
        digest(&source)?;
        let descriptor = array(&envelope[2], 9)?;
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
        let choices = array(&envelope[7], 7).map_err(|_| "native-proof-choices")?;
        if choices[..6]
            .iter()
            .any(|v| !matches!(v.as_str(), Some("true" | "false")))
        {
            return Err("native-proof-choices".into());
        }
        let selection = choices[6].as_str().ok_or("native-proof-choices")?;
        let requested_selection =
            crate::entry::OracleSelection::parse(selection).map_err(|_| "native-proof-choices")?;
        let canonical_selection = requested_selection
            .canonical_json()
            .map_err(|_| "native-proof-choices")?;
        if selection != canonical_selection {
            return Err("native-proof-choices".into());
        }
        selection::check(
            &requested_selection,
            text(&descriptor[8]).map_err(|_| "native-proof-oracle-selection")?,
        )?;
        let choices = std::array::from_fn(|i| {
            choices[i]
                .as_str()
                .expect("validated compilation choice")
                .to_owned()
        });
        let policy = interface::DeploymentPolicy::read(&descriptor[1])?;
        let (entry, producer, validator) = (policy.entry, policy.producer, policy.validator);
        let suite = policy.suite;
        let construction =
            zkc_runtime::vm::ConstructionPlan::read(&descriptor[6]).map_err(|e| e.to_string())?;
        if construction.as_ref().map_or("", |p| p.symbol()) != policy.construction {
            return Err("native-proof-construction".into());
        }
        if construction
            .as_ref()
            .is_some_and(|plan| plan.has_codec() != (policy.format == ProofFormat::RawBytes))
        {
            return Err("native-proof-format".into());
        }
        let admitted = {
            let dummy = CpuBackend::new_with_installation(
                Policy::default(),
                EntryPolicy::new(Domain::new(producer, "native-proof", entry, None), None),
                Default::default(),
                cpu.clone(),
                installation.clone(),
            )
            .map_err(|e| e.to_string())?;
            let program =
                zkc_runtime::vm::Program::decode(candidate.as_bytes(), installation.contracts())
                    .map_err(|e| e.to_string())?;
            match operation {
                Some(producing) => program.check_role_installation(
                    entry,
                    if producing { producer } else { validator },
                    &dummy,
                ),
                None => program.check_installation(&dummy),
            }
            .map_err(|e| e.to_string())?;
            program
        };
        let messages = messages::MessageLayout::read(descriptor, &policy)?;
        messages.check_wire(&envelope[8], &admitted, entry)?;
        let interface::RoleInterface {
            maps,
            public,
            public_types,
            acceptance,
        } = interface::RoleInterface::read(
            &admitted,
            &policy,
            &envelope[6],
            &descriptor[4],
            construction.as_ref(),
            operation,
            retained_inputs,
            &installation,
        )?;
        let keys = public
            .iter()
            .filter(|p| p.logical.kind() == Type::VerifierKey)
            .count();
        let needs_key = maps.values().flat_map(|m| &m.data).any(|p| {
            p.logical.identity() == zkc_runtime::vm::Identity::MultilinearKzgBls12381
                || zkc_cpu::requires_setup(p.logical.clone())
        }) || messages
            .payload_types
            .values()
            .any(|t| zkc_cpu::requires_setup(t.clone()));
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
        let source_inputs = maps
            .iter()
            .map(|(role, map)| (role.clone(), map.data.iter().map(|p| p.original).collect()))
            .collect();
        let construction = zkc_runtime::vm::ProofConstruction {
            suite,
            events: &messages.events,
            plan: construction.as_ref(),
            source_inputs: &source_inputs,
        };
        let acceptance = if operation == Some(true) {
            acceptance.unwrap_or(policy.original_acceptance)
        } else {
            acceptance.ok_or("native-proof-acceptance-map")?
        };
        let proof_entry = if maps.len() == 1 {
            let operation = match operation {
                Some(true) => zkc_runtime::vm::NativeProofOperation::Prove,
                Some(false) => zkc_runtime::vm::NativeProofOperation::Verify,
                None => return Err("native-proof-role-map".into()),
            };
            NativeProofEntry::new_for_operation(
                admitted,
                entry,
                producer,
                validator,
                acceptance,
                construction,
                operation,
                &public.iter().map(|p| p.original).collect::<Vec<_>>(),
            )
        } else {
            NativeProofEntry::new(
                admitted,
                entry,
                producer,
                validator,
                acceptance,
                construction,
            )
        }
        .map_err(|e| e.to_string())?;
        Ok(Self {
            installation,
            cpu,
            ring_assets: Default::default(),
            relation_assets: Default::default(),
            ring_work_limit: zkc_cpu::ring::DEFAULT_WORK_LIMIT,
            sequence_work_limit: 16_777_216,
            shared_ledger: None,
            retained_inputs,
            operation,
            proof_bytes_limit: MAX_PROOF_BYTES,
            publication: expected_sha256.to_owned(),
            choices,
            external_work_limit: CpuBackend::DEFAULT_EXTERNAL_WORK_LIMIT,
            capacity: Capacity::default(),
            setups,
            preparation: PreparedComputations::new(
                proof_entry.admitted(),
                PreparationLimits::default(),
            ),
            entry: proof_entry,
            source,
            descriptor: envelope[2].clone(),
            binding_metadata_bytes: logical::tree_size(&envelope[2])
                .map_err(|e| e.to_string())?
                .saturating_mul(8)
                .saturating_add(4096),
            format: policy.format,
            public,
            public_types,
            maps,
        })
    }
    /// Share one CPU context across proof roles and repeated attempts.
    pub fn with_cpu(mut self, cpu: CpuExecution) -> Self {
        self.cpu = cpu;
        self
    }
    pub fn cpu(&self) -> &CpuExecution {
        &self.cpu
    }
    /// Bound public computation storage independently of invocation capacity.
    /// Reconfiguration starts a new empty store; clones otherwise share it.
    pub fn with_preparation_limits(mut self, limits: PreparationLimits) -> Self {
        self.preparation = PreparedComputations::new(self.entry.admitted(), limits);
        self
    }
    pub fn preparation_stats(&self) -> PreparationStats {
        self.preparation.stats()
    }
    fn prepared_call<T>(
        &self,
        runner: &mut Runner<CpuBackend>,
        role: &EntryRole,
        call: impl FnOnce(&mut Runner<CpuBackend>) -> ArtifactReport<T>,
    ) -> ArtifactReport<T> {
        // Source-port correspondence and canonical public agreement were
        // checked at admission/input loading. Neither role nor value equality
        // grants publicity to proof bytes, resources or private inputs.
        if self.shared_ledger.is_some() {
            return call(runner);
        }
        let public = self.maps[&role.role]
            .data
            .iter()
            .zip(&role.inputs)
            .enumerate()
            .filter_map(|(index, (port, (_, ty)))| {
                (ty.is_serializable() && self.public.iter().any(|p| p.original == port.original))
                    .then_some(index)
            })
            .collect::<Vec<_>>();
        // Preparation is optional. Any unsupported setup leaves the ordinary
        // execution path intact; no public values are inferred on failure.
        let _ = runner.prepare_computations(self.preparation.clone(), &public);
        call(runner)
    }
    /// Select invocation capacity independently of deployment/proof bytes.
    pub fn with_capacity(mut self, capacity: Capacity) -> Result<Self> {
        capacity.validate()?;
        self.capacity = capacity;
        Ok(self)
    }
    pub fn binding_scope(&self) -> crate::entry::BindingScope {
        if self.entry().binds_invocation() {
            crate::entry::BindingScope::Transcript
        } else if self.format == ProofFormat::Native {
            crate::entry::BindingScope::HeaderOnly
        } else {
            crate::entry::BindingScope::Authored
        }
    }
    pub fn capacity(&self) -> Capacity {
        self.capacity
    }
    pub fn with_ring_assets(mut self, assets: zkc_cpu::ring::Registry) -> Self {
        self.ring_assets = assets;
        self
    }
    pub fn with_relation_assets(mut self, assets: zkc_cpu::relation::Registry) -> Self {
        self.relation_assets = assets;
        self
    }
    pub fn with_ring_work_limit(mut self, limit: u64) -> Result<Self> {
        if limit > zkc_cpu::ring::DEFAULT_WORK_LIMIT {
            return Err("native-proof-ring-work-limit".into());
        }
        self.ring_work_limit = limit;
        Ok(self)
    }
    pub fn entry(&self) -> &NativeProofEntry {
        &self.entry
    }
    pub(crate) fn public_types(&self) -> &[PhysicalType] {
        &self.public_types
    }
    // The source Host consumes this admitted view rather than decoding the
    // deployment carrier again or keeping a second interpretation of its ABI.
    pub(crate) fn source_interface(&self) -> SourceInterface<'_> {
        let policy = &self.descriptor[1];
        let suite = policy[5].as_str().expect("admitted policy suite");
        let services = policy[6].as_array().expect("admitted policy services");
        SourceInterface {
            publication: &self.publication,
            source: &self.source,
            choices: &self.choices,
            acceptance: index(&policy[4]).expect("admitted acceptance"),
            suite: (!suite.is_empty()).then_some(suite),
            construction: policy[10].as_str().expect("admitted construction"),
            gates: policy[11].as_array().expect("admitted gates"),
            format: self.format,
            services: services
                .iter()
                .map(|value| index(value).expect("admitted service"))
                .collect(),
            public: &self.public,
            roles: &self.maps,
            operation: self.operation,
            producer: policy[2].as_str().expect("admitted producer"),
            validator: policy[3].as_str().expect("admitted validator"),
        }
    }

    /// Configure each invocation's external primitive-work cap, up to the
    /// default. This setting applies to every later invocation on this value;
    /// each allowance covers all attempts and successful or failed trial calls.
    /// It changes no program or transcript bytes and is reported separately
    /// from deployment and attempt-policy identities. The CLI exposes the same
    /// cap through `--external-work`. Zero permits only zero-work transitions.
    pub fn with_external_work_limit(mut self, limit: u64) -> Result<Self> {
        if limit > CpuBackend::DEFAULT_EXTERNAL_WORK_LIMIT {
            return Err("native-proof-external-work-limit".into());
        }
        self.external_work_limit = limit;
        Ok(self)
    }

    /// Share invocation-wide charging with every reached runner and attempt.
    pub fn with_shared_ledger(mut self, ledger: zkc_runtime::vm::ExecutionLedger) -> Self {
        self.shared_ledger = Some(ledger);
        self
    }
    pub(crate) fn with_invocation_limits(
        mut self,
        capacity: Capacity,
        external: u64,
        ring: u64,
        sequence: u64,
        proof_bytes: usize,
    ) -> Self {
        self.capacity = capacity;
        self.external_work_limit = external;
        self.ring_work_limit = ring;
        self.sequence_work_limit = sequence;
        self.proof_bytes_limit = proof_bytes.min(MAX_PROOF_BYTES);
        self
    }
    /// Execute immutable role inputs with an explicit production, verification
    /// or retry request. Public inputs and setups remain application-authorized.
    /// Authored execution follows the pinned program's own binding algorithm.
    /// For local/authored RawBytes, context identifies the report only; pass
    /// any context the protocol must authenticate through its public data ports.
    pub fn execute(
        &self,
        input: &ProofInputs,
        invocation: Invocation<'_>,
    ) -> Result<NativeProofReport> {
        let mut imports = crate::host::setups::VerifierKeys::new(
            self.capacity.backend().ark_bounds(),
            self.installation().clone(),
        );
        self.execute_prepared(input, invocation, &mut imports)
    }
    /// Deterministic provider controls for tests. No production command or file
    /// format selects this feature-gated entry point.
    #[cfg(feature = "test-utils")]
    pub fn execute_test<T: Into<zkc_cpu::TestTape>>(
        &self,
        input: &ProofInputs,
        invocation: Invocation<'_>,
        tapes: BTreeMap<usize, T>,
    ) -> Result<NativeProofReport> {
        let entropy = test_entropy(tapes)?;
        let mut imports = crate::host::setups::VerifierKeys::new(
            self.capacity.backend().ark_bounds(),
            self.installation().clone(),
        );
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
        let mut imports = crate::host::setups::VerifierKeys::new(
            self.capacity.backend().ark_bounds(),
            self.installation().clone(),
        );
        self.prepare_inputs(input, invocation.is_producer(), &mut imports)
            .map(|_| ())
    }
    fn selected_role(&self, producing: bool) -> Result<&EntryRole> {
        (if producing {
            self.entry.producer()
        } else {
            self.entry.validator()
        })
        .ok_or_else(|| "native-proof-operation".into())
    }
    fn prepare_inputs(
        &self,
        input: &ProofInputs,
        producer: bool,
        imports: &mut crate::host::setups::VerifierKeys,
    ) -> Result<inputs::Prepared> {
        imports.set_ledger(self.shared_ledger.clone());
        let role = self.selected_role(producer)?;
        self.cpu
            .enter(|| inputs::prepare(self, input, role, producer, imports))
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
        if proof.is_some_and(|p| p.len() > self.proof_bytes_limit) {
            return Err("native-proof-proof-limit".into());
        }
        let role = self.selected_role(proof.is_none())?;
        let mapping = &self.maps[&role.role];
        let inputs::Prepared {
            mut backend,
            loaded,
            planned,
            root,
            binding,
            loading,
            encoding,
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
        let registry = ServiceRegistry::with_installation(policy, self.installation.clone());
        let mut resources: Vec<Capability> = Vec::new();
        let mut services: Vec<ServiceReference> = Vec::new();
        let mut retained = encoding;
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
            if self.entry.has_record_codec()
                && let Some(proof) = proof
            {
                let ty = &role.inputs.last().expect("admitted codec input").1;
                retained.extend(zkc_runtime::host::wire::reserve_allocation(
                    self.shared_ledger.as_ref(),
                    proof.len().saturating_add(512),
                )?);
                values.push(
                    backend
                        .decode_raw_bytes(ty, proof)
                        .map_err(|e| e.to_string())?,
                );
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
            verification: None,
            retained,
            retained_outputs: Vec::new(),
            execution_counts: Default::default(),
            outputs: None,
            outcome: Ok(Vec::new()),
            binding: hex(&binding),
            messages: 0,
            bytes: 0,
            cancelled: false,
            instructions: 0,
            resources: Vec::new(),
            service_draws: 0,
            attempts: Vec::new(),
            return_at: None,
            stop: None,
            attempt_policy: attempts.as_ref().map(|plan| plan.policy.identity()),
            usage: Default::default(),
            external_work: 0,
            ring_work: 0,
            sequence_work: 0,
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
            Ok(values) => match Runner::new_for_role_with_ledger(
                self.entry.admitted(),
                self.entry.entry(),
                &role.role,
                "native-proof",
                backend,
                values,
                zkc_runtime::vm::ValueBudget {
                    live_bytes: self
                        .capacity
                        .values
                        .live_bytes
                        .saturating_sub(loading.as_ref().map_or(0, |v| v.bytes())),
                    ..self.capacity.values
                },
                self.capacity.work,
                self.shared_ledger.clone(),
            ) {
                Err(failed) => {
                    report.outcome = Err(failed.error.to_string());
                    report.usage = failed.usage;
                    backend = failed.backend;
                }
                Ok(mut runner) => {
                    match proof {
                        None => {
                            let produced = self.prepared_call(&mut runner, role, |runner| {
                                driver::produce(
                                    runner,
                                    &binding,
                                    self.transport(),
                                    self.proof_bytes_limit,
                                    self.shared_ledger.clone(),
                                )
                            });
                            retain_driver_stop(&mut report, &produced);
                            report.outcome = produced
                                .outcome
                                .map(|p| {
                                    let (proof, outputs, retained) = p.into_parts();
                                    report.retained.extend(retained);
                                    report.outputs = Some(self.original_outputs(role, outputs));
                                    proof
                                })
                                .map_err(|e| driver_failure(&e));
                            report.messages = produced.messages;
                            report.bytes = produced.bytes;
                            report.cancelled = produced.cancelled.is_some();
                        }
                        Some(proof) => {
                            let validated = self.prepared_call(&mut runner, role, |runner| {
                                driver::validate(
                                    runner,
                                    proof,
                                    &binding,
                                    self.transport(),
                                    self.entry.acceptance(),
                                    self.shared_ledger.clone(),
                                )
                            });
                            retain_driver_stop(&mut report, &validated);
                            report.verification = match &validated.outcome {
                                Ok(_) => Some(VerificationDecision::Accepted),
                                Err(driver::ArtifactFailure::Rejected) => {
                                    Some(VerificationDecision::Rejected)
                                }
                                Err(_) => None,
                            };
                            report.outcome = validated
                                .outcome
                                .map(|values| {
                                    report.outputs = Some(self.original_outputs(role, values));
                                    Vec::new()
                                })
                                .map_err(|e| driver_failure(&e));
                            report.messages = validated.messages;
                            report.bytes = validated.bytes;
                            report.cancelled = validated.cancelled.is_some();
                        }
                    }
                    report.usage = runner.usage();
                    report.execution_counts = runner.execution_counts();
                    report.return_at = runner.early_return().map(|(o, s)| (o.clone(), s.into()));
                    let (returned_backend, outputs) = runner.into_retained_outputs();
                    report.retained_outputs.extend(outputs);
                    backend = returned_backend;
                }
            },
        }
        report.instructions = report.usage.instructions;
        report.external_work = backend.external_work_spent();
        report.ring_work = backend.ring_work_spent();
        report.sequence_work = backend.sequence_work_spent();
        retire_resources(&mut backend, &registry, &resources, &services, &mut report);
        Ok(report)
    }
    /// Native admission has checked the output map against the role signature.
    /// Private successors belong to cleanup, not immutable application results.
    fn transport(&self) -> driver::Transport {
        if self.entry.has_record_codec() {
            driver::Transport::Record
        } else {
            driver::Transport::Messages(self.format)
        }
    }

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
    backend: &mut CpuBackend,
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
            Ok(o) => {
                report.service_draws += o.state.as_ref().map_or(0, |s| s.draw_count);
                observations.push(json!({"kind":"service", "owner":o.owner,
                    "leased":o.leased, "poisoned":o.poisoned,
                    "state":o.state.map(|s| json!({"generation":s.generation, "transitions":s.draw_count,
                        "budget":s.budget, "stage":s.stage}))}));
            }
            Err(e) => {
                report.cleanup_errors.push(e.to_string());
            }
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
/// The verifier's semantic decision after consuming the complete proof.
/// Operational and cleanup failures remain separate in the execution report.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum VerificationDecision {
    Accepted,
    Rejected,
}

pub struct NativeProofReport {
    /// Present only when the verifier returned a Boolean decision after proof
    /// framing completed. A later cleanup failure does not erase that decision.
    pub verification: Option<VerificationDecision>,
    pub execution_counts: zkc_runtime::vm::ExecutionCounts,
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
    /// Known service draws observed during retirement, before JSON rendering.
    pub(crate) service_draws: u64,
    pub attempts: Vec<AttemptRecord>,
    pub attempt_policy: Option<String>,
    /// One-shot owner-local completion. Attempts keep their own coordinates.
    pub return_at: Option<(zkc_runtime::vm::Origin, String)>,
    /// One-shot execution or host-cancellation stop; attempts retain their own.
    pub stop: Option<zkc_runtime::vm::Stop>,
    pub usage: zkc_runtime::vm::Usage,
    pub external_work: u64,
    pub ring_work: u64,
    pub sequence_work: u64,
    pub ring_work_limit: u64,
    pub external_work_limit: u64,
    /// Cleanup failures remain separate from the primary body failure.
    pub cleanup_errors: Vec<String>,
    retained_outputs: Vec<zkc_runtime::vm::RetainedOutputs<Value>>,
    retained: Vec<zkc_runtime::vm::LiveReservation>,
}
fn stop_json(s: &zkc_runtime::vm::Stop) -> Json {
    json!({"origin":s.origin.json(),"role":s.role,"site":s.site,
        "local":s.local.as_ref().map(|l|json!({"site":l.site,"function":l.function,"instruction":l.instruction})),
        "kind":format!("{:?}",s.kind),
        "cleanup_errors":s.cleanup_errors.iter().map(ToString::to_string).collect::<Vec<_>>()})
}
impl NativeProofReport {
    /// A completed verification may reject normally. Never infer that case from
    /// diagnostic strings, and never turn an operational failure into rejection.
    pub fn verification_result(&self) -> Option<bool> {
        if self.cancelled || self.stop.is_some() || !self.cleanup_errors.is_empty() {
            return None;
        }
        self.verification
            .map(|decision| decision == VerificationDecision::Accepted)
    }

    /// Bounded child receipt; no proof bytes, outputs or complete attempt trees.
    pub fn diagnostics_summary(&self) -> Json {
        use crate::host::diagnostics::{message, stop, values};
        json!({"verification_decision":self.verification.map(|d|match d {VerificationDecision::Accepted=>"accepted",VerificationDecision::Rejected=>"rejected"}),
            "usage":{"instructions":self.usage.instructions,"iterations":self.usage.iterations,"total_value_bytes":self.usage.total_value_bytes,"logical_bytes":self.usage.logical_bytes},
            "binding_sha256":self.binding,"messages":self.messages,"bytes":self.bytes,"cancelled":self.cancelled,
            "stop":self.stop.as_ref().map(stop),"cleanup_errors":self.cleanup_errors.iter().take(16).map(|e|message(e)).collect::<Vec<_>>(),
            "cleanup_omitted":self.cleanup_errors.len().saturating_sub(16),"resources":values(self.resources.iter()),
            "resource_count":self.resources.len(),"attempt_count":self.attempts.len(),
            "attempts":self.attempts.iter().take(16).map(|a|json!({"attempt":a.attempt,"decision":a.decision.as_ref().map_err(|e|message(e)),"stop":a.stop.as_ref().map(stop)})).collect::<Vec<_>>()})
    }
    /// Payload-free execution diagnostics, including failed attempts and cleanup.
    pub fn diagnostics(&self) -> Json {
        let mut report = json!({});
        report["verification_decision"] = json!(self.verification.map(|decision| match decision {
            VerificationDecision::Accepted => "accepted",
            VerificationDecision::Rejected => "rejected",
        }));
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
        report["sequence_work"] = json!(self.sequence_work);
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

#[cfg(test)]
mod tests;

impl std::fmt::Debug for NativeDeployment {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("NativeDeployment")
            .field("publication", &self.publication)
            .finish_non_exhaustive()
    }
}

impl std::fmt::Debug for NativeProofReport {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("NativeProofReport")
            .field("verification", &self.verification)
            .field("bytes", &self.bytes)
            .field("stop", &self.stop)
            .field("cleanup_errors", &self.cleanup_errors)
            .finish_non_exhaustive()
    }
}

fn driver_failure(error: &ArtifactFailure) -> String {
    match error {
        ArtifactFailure::StartedRunner => "artifact-runner-started".into(),
        ArtifactFailure::Format(e) => e.to_string(),
        ArtifactFailure::Backend(e) => e.code.clone(),
        ArtifactFailure::Wire(e) => zkc_cpu::NativeWireError::from(e.clone()).to_string(),
        ArtifactFailure::Runtime(e) => e.to_string(),
        ArtifactFailure::Stopped(stop) => match &stop.kind {
            zkc_runtime::vm::StopKind::Backend(e) => e.code.clone(),
            _ => format!("artifact-stopped:{:?}", stop.kind),
        },
        ArtifactFailure::UnexpectedCommunication => "artifact-unexpected-communication".into(),
        ArtifactFailure::AcceptanceType => "artifact-acceptance-type".into(),
        ArtifactFailure::Rejected => "artifact-rejected".into(),
    }
}
