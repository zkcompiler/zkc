//! Independent named proof calls over the admitted common native deployment.
use super::{
    Interface, NamedValues, Package, RoleInputs, SetupAuthority, arguments,
    interface::raw::{Construction, Job},
    setups, value,
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
/// Public values are the application's independently authorized statement. The
/// role input map also supplies any shared operands; native admission checks
/// their canonical agreement. A verifier request carries no prover inputs.
#[derive(Debug)]
pub struct ProofRequest {
    pub public: NamedValues,
    pub inputs: RoleInputs,
    pub context: Vec<u8>,
    pub transcript_budget: u64,
    pub setups: BTreeMap<String, Vec<u8>>,
}
pub struct ProofEntry {
    package: Package,
    interface: Interface,
    native: NativeDeployment,
    scope: BindingScope,
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
    pub fn admit(package: Package, options: ProofOptions, setups: SetupAuthority) -> Result<Self> {
        let interface = Interface::read(&package).map_err(|e| e.to_string())?;
        let Job::Proof { construction, .. } = &interface.document.job else {
            return Err("entry-job-kind".into());
        };
        let scope = match construction {
            Construction::Authored {} => BindingScope::HeaderOnly,
            Construction::FiatShamir { .. } => BindingScope::Transcript,
        };
        if scope == BindingScope::HeaderOnly && options.binding == BindingPolicy::TranscriptRequired
        {
            return Err("entry-proof-binding-policy".into());
        }
        for port in &interface.selected_protocol().inputs {
            arguments::check_import(&interface, port)?;
        }
        for port in &interface.selected_protocol().outputs {
            value::check_export(&port.schema)?;
        }
        let native = NativeDeployment::admit_with_setups(
            package.artifact().as_bytes(),
            &hex(&Sha256::digest(package.artifact().as_bytes())),
            setups::proof_authority(&interface, setups)?,
        )?
        .with_capacity(options.capacity)?
        .with_external_work_limit(options.external_work)?;
        interface.check_proof(&native).map_err(|e| e.to_string())?;
        Ok(Self {
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
    pub fn prove(&self, request: ProofRequest) -> Result<ProofReport> {
        let inputs = self.inputs(request, true)?;
        Ok(self.report(self.native.execute_typed(&inputs, None)?, true))
    }
    pub fn verify(&self, request: ProofRequest, proof: &[u8]) -> Result<ProofReport> {
        let inputs = self.inputs(request, false)?;
        Ok(self.report(self.native.execute_typed(&inputs, Some(proof))?, false))
    }
    /// The admitted native policy uses original protocol ports and retains the
    /// actual providers and cumulative work across attempts.
    pub fn prove_attempts(
        &self,
        request: ProofRequest,
        policy: &AttemptPolicy,
    ) -> Result<ProofReport> {
        let inputs = self.inputs(request, true)?;
        Ok(self.report(self.native.execute_attempts_typed(&inputs, policy)?, true))
    }
    fn inputs(&self, request: ProofRequest, producer: bool) -> Result<ProofInputs> {
        let protocol = self.interface.selected_protocol();
        let Job::Proof {
            prover,
            verifier,
            public,
            construction,
            ..
        } = &self.interface.document.job
        else {
            unreachable!("admitted proof Entry")
        };
        let role = if producer { prover } else { verifier };
        let derived = match construction {
            Construction::Authored {} => None,
            Construction::FiatShamir { service, .. } => Some(*service as usize),
        };
        let keys = setups::public_keys(&self.interface, &request.setups, self.native.capacity())?;
        Ok(ProofInputs {
            public: arguments::values(
                &self.interface,
                public.iter().map(|i| &protocol.inputs[*i as usize]),
                request.public,
                Some(&keys),
            )?,
            inputs: arguments::values(
                &self.interface,
                protocol
                    .inputs
                    .iter()
                    .filter(|port| port.roles.contains(role)),
                request.inputs.inputs,
                None,
            )?,
            services: arguments::services(
                protocol
                    .services
                    .iter()
                    .enumerate()
                    .filter(|(i, port)| Some(*i) != derived && &port.owner == role)
                    .map(|(_, port)| port),
                request.inputs.services,
            )?,
            context: request.context,
            transcript_budget: request.transcript_budget,
        })
    }
    fn report(&self, native: NativeProofReport, producer: bool) -> ProofReport {
        let mut report = ProofReport {
            native,
            outputs: None,
            output_error: None,
            binding_scope: self.scope,
        };
        if let Some(outputs) = &report.native.outputs {
            let role = if producer {
                &self.native.entry().producer().role
            } else {
                &self.native.entry().validator().role
            };
            let result = (|| -> Result<NamedValues> {
                let mut leaves = outputs.clone();
                let mut values = NamedValues::new();
                for port in self
                    .interface
                    .selected_protocol()
                    .outputs
                    .iter()
                    .filter(|p| p.roles.contains(role))
                {
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
