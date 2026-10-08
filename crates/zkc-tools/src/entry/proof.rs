//! Independent named proof calls over the admitted common native deployment.
use super::errors::{EntryError as E, EntryPhase as P, EntryResult};
use super::{
    Interface, NamedValues, Package, RoleInputs, SetupAuthority, arguments, setups, value,
};
use crate::artifact::{
    hex,
    native::{AttemptPolicy, NativeCapacity, NativeDeployment, NativeProofReport, ProofInputs},
};
use sha2::{Digest, Sha256};
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
    pub capacity: NativeCapacity,
    pub external_work: u64,
    pub binding: BindingPolicy,
}
impl Default for ProofOptions {
    fn default() -> Self {
        Self {
            capacity: NativeCapacity::default(),
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
            proof_bytes: crate::artifact::MAX_PROOF_BYTES,
        }
    }
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
pub struct ProofEntry {
    package: Package,
    interface: Interface,
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
    pub fn admit(
        package: Package,
        options: ProofOptions,
        setups: SetupAuthority,
    ) -> EntryResult<Self> {
        let interface = Interface::read(&package).map_err(|e| E::new(P::Interface, e))?;
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
        let native = NativeDeployment::admit_with_setups(
            package.artifact().as_bytes(),
            &hex(&Sha256::digest(package.artifact().as_bytes())),
            setups::proof_authority(&interface, setups).map_err(|e| E::new(P::Authority, e))?,
        )
        .and_then(|n| n.with_capacity(options.capacity))
        .and_then(|n| n.with_external_work_limit(options.external_work))
        .map_err(|e| E::new(P::Admission, e))?;
        interface
            .check_proof(&native)
            .map_err(|e| E::new(P::Binding, e))?;
        Ok(Self {
            completion,
            roles,
            package,
            interface,
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
    pub fn binding_scope(&self) -> BindingScope {
        self.scope
    }
    pub fn prove(&self, request: ProofRequest) -> EntryResult<ProofReport> {
        if self.completion.is_some() {
            return self.prove_attempts(request, AttemptOptions::default());
        }
        let inputs = self
            .inputs(request, true)
            .map_err(|e| E::new(P::Request, e))?;
        Ok(self.report(
            self.native
                .execute_typed(&inputs, None)
                .map_err(|e| E::new(P::Preparation, e))?,
            true,
        ))
    }
    pub fn verify(&self, request: ProofRequest, proof: &[u8]) -> EntryResult<ProofReport> {
        let inputs = self
            .inputs(request, false)
            .map_err(|e| E::new(P::Request, e))?;
        Ok(self.report(
            self.native
                .execute_typed(&inputs, Some(proof))
                .map_err(|e| E::new(P::Preparation, e))?,
            false,
        ))
    }
    /// Use the Entry's completion result with explicit application authorization.
    /// The native controller retains actual providers and cumulative work.
    pub fn prove_attempts(
        &self,
        request: ProofRequest,
        options: AttemptOptions,
    ) -> EntryResult<ProofReport> {
        let completion = self
            .completion
            .ok_or_else(|| E::new(P::Request, "entry-attempt-completion"))?;
        let capacity = self.native.capacity();
        let policy = AttemptPolicy {
            completion,
            // Source randomness enters through managed services; this source
            // profile admits no affine RNG input/output constructors.
            rng: Vec::new(),
            limits: zkc_runtime::attempt::Limits {
                attempts: options.count,
                proof_bytes: options.proof_bytes,
            },
            work: capacity.work,
            values: capacity.values,
        };
        let inputs = self
            .inputs(request, true)
            .map_err(|e| E::new(P::Request, e))?;
        Ok(self.report(
            self.native
                .execute_attempts_typed(&inputs, &policy)
                .map_err(|e| E::new(P::Preparation, e))?,
            true,
        ))
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
