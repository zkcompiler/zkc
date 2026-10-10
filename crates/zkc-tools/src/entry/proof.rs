//! Independent named proof calls over the admitted common native deployment.
use super::errors::{EntryError as E, EntryPhase as P, EntryResult};
use super::{
    EntryAssets, Interface, NamedValues, Package, RoleInputs, SetupAuthority, arguments, setups,
    value,
};
use crate::execution::Capacity;
use crate::proof::{AttemptPolicy, NativeDeployment, NativeProofReport, ProofInputs};
use std::collections::BTreeMap;
use zkc_backends::NativeBackend;

type Result<T> = std::result::Result<T, String>;

/// Authored deployments bind public inputs/context in the artifact header only.
/// Applications must acknowledge that scope explicitly before admitting one.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum BindingPolicy {
    #[default]
    TranscriptRequired,
    AllowHeaderOnly,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BindingScope {
    Transcript,
    HeaderOnly,
}
#[derive(Clone, Copy, Debug)]
pub struct ProofOptions {
    pub capacity: Capacity,
    pub external_work: u64,
    pub binding: BindingPolicy,
}
impl Default for ProofOptions {
    fn default() -> Self {
        Self {
            capacity: Capacity::default(),
            external_work: NativeBackend::DEFAULT_EXTERNAL_WORK_LIMIT,
            binding: BindingPolicy::default(),
        }
    }
}
/// Explicit retry authorization. Count defaults to one; all cumulative work
/// and payload ceilings remain those of the admitted ProofOptions.capacity.
#[derive(Clone, Copy, Debug)]
pub struct AttemptOptions {
    pub count: u64,
    pub proof_bytes: usize,
}
impl Default for AttemptOptions {
    fn default() -> Self {
        Self {
            count: 1,
            proof_bytes: crate::proof::MAX_PROOF_BYTES,
        }
    }
}
/// Select the input side independently of the presence of a witness file.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ProofOperation {
    Prove,
    Verify,
}

/// Public values are the application's independently authorized statement. The
/// private map supplies only the invoked role's nonpublic inputs. The adapter
/// assembles shared operands and native admission checks canonical agreement.
#[derive(Debug, Default)]
pub struct ProofRequest {
    pub public: NamedValues,
    pub private: RoleInputs,
    pub context: Vec<u8>,
    /// None uses the operational default for derivation and zero for authored jobs.
    pub transcript_budget: Option<u64>,
    pub setups: BTreeMap<String, Vec<u8>>,
}
/// An authenticated package, checked interface, admitted deployment and the
/// package's admitted expression assets, which are the deployment's only
/// evaluator source.
pub struct ProofEntry {
    package: Package,
    interface: super::BoundInterface,
    assets: EntryAssets,
    native: NativeDeployment,
    scope: BindingScope,
    completion: Option<usize>,
    roles: (usize, usize),
}
/// The outer call result distinguishes preparation refusal. This report must
/// still be checked for execution success, including rejection and cleanup.
#[must_use = "check is_success() or into_result(); invocation preparation is not proof acceptance"]
pub struct ProofReport {
    pub native: NativeProofReport,
    pub outputs: Option<NamedValues>,
    pub output_error: Option<String>,
    pub binding_scope: BindingScope,
}
impl ProofReport {
    /// For verification, true means the selected acceptance result was true and
    /// complete cleanup/result reconstruction succeeded. Production succeeds
    /// when the complete unpublished proof and its outputs are available.
    #[must_use]
    pub fn is_success(&self) -> bool {
        self.native.outcome.is_ok()
            && self.native.cleanup_errors.is_empty()
            && self.output_error.is_none()
            && self.outputs.is_some()
    }
    /// Preserve the complete report on either branch, including failure usage
    /// and cleanup. Preparation errors remain the outer call's separate result.
    pub fn into_result(self) -> std::result::Result<Self, Box<Self>> {
        if self.is_success() {
            Ok(self)
        } else {
            Err(Box::new(self))
        }
    }
}
impl ProofEntry {
    pub fn with_ring_work_limit(mut self, limit: u64) -> Result<Self> {
        self.native = self.native.with_ring_work_limit(limit)?;
        Ok(self)
    }
    pub fn admit(
        package: Package,
        options: ProofOptions,
        setups: SetupAuthority,
    ) -> EntryResult<Self> {
        let interface =
            crate::entry::BoundInterface::read(&package).map_err(|e| E::new(P::Interface, e))?;
        let proof = interface
            .proof()
            .ok_or_else(|| E::new(P::Admission, "entry-job-kind"))?;
        let roles = (proof.prover, proof.verifier);
        let completion = proof.completion;
        let scope = if proof.suite.is_some() {
            BindingScope::Transcript
        } else {
            BindingScope::HeaderOnly
        };
        if scope == BindingScope::HeaderOnly && options.binding == BindingPolicy::TranscriptRequired
        {
            return Err(E::new(P::Admission, "entry-proof-binding-policy"));
        }
        arguments::check_ports(&interface).map_err(|e| E::new(P::Interface, e))?;
        let native = NativeDeployment::admit_artifact(
            &package.authenticated_artifact(),
            setups::proof_authority(&interface, setups).map_err(|e| E::new(P::Authority, e))?,
        )
        .and_then(|n| n.with_capacity(options.capacity))
        .and_then(|n| n.with_external_work_limit(options.external_work))
        .map_err(|e| E::new(P::Admission, e))?;
        interface
            .check_proof(&native)
            .map_err(|e| E::new(P::Binding, e))?;
        let assets = EntryAssets::admit(
            &package,
            &interface,
            native.entry().admitted(),
            native.entry().entry(),
        )
        .map_err(|e| E::new(P::Assets, e))?;
        let native = native
            .with_ring_assets(assets.registry().clone())
            .with_relation_assets(assets.relation_registry().clone());
        Ok(Self {
            completion,
            roles,
            package,
            interface,
            assets,
            native,
            scope,
        })
    }
    pub fn package(&self) -> &Package {
        &self.package
    }
    pub fn interface(&self) -> &Interface {
        &self.interface
    }
    pub fn assets(&self) -> &EntryAssets {
        &self.assets
    }
    pub fn binding_scope(&self) -> BindingScope {
        self.scope
    }
    pub(crate) fn output_types(
        &self,
        operation: ProofOperation,
    ) -> &[zkc_runtime::interactive::PhysicalType] {
        let role = match operation {
            ProofOperation::Prove => self.native.entry().producer(),
            ProofOperation::Verify => self.native.entry().validator(),
        };
        // The admitted map covers original outputs, excluding any transcript
        // state added by derivation. Only original outputs reach file encoding.
        let count = self.native.source_interface().roles[&role.role]
            .outputs
            .len();
        &role.outputs[..count]
    }
    pub fn prove(&self, request: ProofRequest) -> EntryResult<ProofReport> {
        self.execute(request, None, None)
    }
    pub fn verify(&self, request: ProofRequest, proof: &[u8]) -> EntryResult<ProofReport> {
        self.execute(request, Some(proof), None)
    }
    /// Use the Entry's completion result with explicit application authorization.
    /// The native controller retains actual providers and cumulative work.
    pub fn prove_attempts(
        &self,
        request: ProofRequest,
        options: AttemptOptions,
    ) -> EntryResult<ProofReport> {
        self.execute(request, None, Some(options))
    }
    fn execute(
        &self,
        request: ProofRequest,
        proof: Option<&[u8]>,
        attempts: Option<AttemptOptions>,
    ) -> EntryResult<ProofReport> {
        let mut imports =
            crate::host::setups::VerifierKeys::new(self.native.capacity().backend().ark_bounds());
        self.execute_with(request, proof, attempts, &mut imports)
    }
    pub(crate) fn execute_with(
        &self,
        request: ProofRequest,
        proof: Option<&[u8]>,
        attempts: Option<AttemptOptions>,
        imports: &mut crate::host::setups::VerifierKeys,
    ) -> EntryResult<ProofReport> {
        let producer = proof.is_none();
        let attempts = self.attempt_policy(producer, attempts)?;
        let inputs = self
            .inputs(request, producer)
            .map_err(|e| E::new(P::Request, e))?;
        Ok(self.report(
            self.native
                .execute_prepared(
                    &inputs,
                    attempts.as_ref().map_or_else(
                        || crate::proof::Invocation::one_shot(proof),
                        crate::proof::Invocation::Attempts,
                    ),
                    imports,
                )
                .map_err(|e| E::new(P::Preparation, e))?,
            producer,
        ))
    }
    /// Validate and load inputs under the same setup, shape and capacity rules
    /// as execution. No randomness, transcript or proof parsing occurs here.
    pub fn check_inputs(
        &self,
        request: ProofRequest,
        operation: ProofOperation,
        attempts: Option<AttemptOptions>,
    ) -> EntryResult<()> {
        let producer = operation == ProofOperation::Prove;
        if !producer && attempts.is_some() {
            return Err(E::new(P::Request, "entry-attempt-operation"));
        }
        let attempts = self.attempt_policy(producer, attempts)?;
        let inputs = self
            .inputs(request, producer)
            .map_err(|e| E::new(P::Request, e))?;
        let invocation = attempts.as_ref().map_or_else(
            || {
                if producer {
                    crate::proof::Invocation::Prove
                } else {
                    crate::proof::Invocation::Verify(&[])
                }
            },
            crate::proof::Invocation::Attempts,
        );
        self.native
            .check_inputs(&inputs, invocation)
            .map_err(|e| E::new(P::Preparation, e))
    }
    fn attempt_policy(
        &self,
        producer: bool,
        attempts: Option<AttemptOptions>,
    ) -> EntryResult<Option<AttemptPolicy>> {
        Ok(
            if producer && (attempts.is_some() || self.completion.is_some()) {
                let options = attempts.unwrap_or_default();
                let completion = self
                    .completion
                    .ok_or_else(|| E::new(P::Request, "entry-attempt-completion"))?;
                let capacity = self.native.capacity();
                Some(AttemptPolicy {
                    completion,
                    // Source randomness enters through managed services; no affine RNG ports.
                    rng: Vec::new(),
                    limits: zkc_runtime::attempt::Limits {
                        attempts: options.count,
                        proof_bytes: options.proof_bytes,
                    },
                    work: capacity.work,
                    values: capacity.values,
                })
            } else {
                None
            },
        )
    }
    fn inputs(&self, request: ProofRequest, producer: bool) -> Result<ProofInputs> {
        let role = &self.interface.roles()[if producer { self.roles.0 } else { self.roles.1 }];
        let derived = self.interface.proof().and_then(|p| p.transcript).is_some();
        let keys = setups::public_keys(&self.interface, &request.setups, self.native.capacity())?;
        let public = arguments::values(self.interface.public_ports(), request.public, Some(&keys))?;
        let inputs = arguments::proof_inputs(
            &self.interface,
            role,
            &public,
            request.private.inputs,
            self.native.capacity(),
        )?;
        Ok(ProofInputs {
            public,
            inputs,
            services: arguments::services(self.interface.services(role), request.private.services)?,
            context: request.context,
            transcript_budget: request.transcript_budget.unwrap_or(if derived {
                super::DEFAULT_DRAW_BUDGET
            } else {
                0
            }),
        })
    }
    fn report(&self, native: NativeProofReport, producer: bool) -> ProofReport {
        let mut report = ProofReport {
            native,
            outputs: None,
            output_error: None,
            binding_scope: self.scope,
        };
        if report.native.outcome.is_err() || !report.native.cleanup_errors.is_empty() {
            return report;
        }
        if let Some(outputs) = &report.native.outputs {
            let role = &self.interface.roles()[if producer { self.roles.0 } else { self.roles.1 }];
            let result = (|| -> Result<NamedValues> {
                let mut leaves = outputs.clone();
                let mut values = NamedValues::new();
                for port in self.interface.output_ports(role) {
                    let selected = port
                        .native
                        .iter()
                        .map(|i| leaves.remove(&(*i as usize)).ok_or("entry-output-shape"))
                        .collect::<std::result::Result<Vec<_>, _>>()?;
                    let mut selected = selected.into_iter();
                    values.insert(
                        port.name.clone(),
                        value::collect(&port.schema, &mut selected)?,
                    );
                    if selected.next().is_some() {
                        return Err("entry-output-shape".into());
                    }
                }
                if !leaves.is_empty() {
                    return Err("entry-output-shape".into());
                }
                Ok(values)
            })();
            match result {
                Ok(values) => report.outputs = Some(values),
                Err(code) => report.output_error = Some(code),
            }
        }
        report
    }
}
