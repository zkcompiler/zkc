//! Bind authenticated source metadata to the native owner's admitted ABI.
use super::{BoundInterface, InterfaceError as E, Result, raw::*, require};
use crate::{proof::NativeDeployment, run::RunHost};
use zkc_runtime::vm::LogicalType;

impl BoundInterface {
    /// Logical protocol metadata grants no external handle ingestion authority.
    pub(in crate::entry) fn check_executable_ports(&self) -> Result<()> {
        self.view.check_executable_ports()
    }
    /// Check the exact package artifact and its participant ABI. The authenticated
    /// compiler publication owns source correspondence and run compile options;
    /// run bundles do not carry an independent original or options record.
    pub fn check_run(&self, host: &RunHost) -> Result<()> {
        self.check_run_bundle(host.bundle(), host.identity())
    }
    /// Bind a portable backend Host to the exact authenticated publication.
    /// The logical source ABI is checked independently of backend storage.
    pub(in crate::entry) fn check_run_bundle(
        &self,
        bundle: &zkc_runtime::host::joint::Bundle,
        identity: &str,
    ) -> Result<()> {
        self.check_executable_ports()?;
        let p = &self.document.protocols[self.selected];
        require(
            matches!(self.document.job, Job::Run {})
                && identity == self.artifact
                && bundle.entry() == p.symbol
                && bundle.roles().len() == p.roles.len(),
            E::NativeBinding,
        )?;
        for (role_index, (role, actual)) in self.roles().iter().zip(bundle.roles()).enumerate() {
            let expected = &role.native_name;
            let entry = &actual.entry;
            require(&entry.role == expected, E::NativeBinding)?;
            let inputs = leaves(p.inputs.iter(), Some(role_index as u32))?;
            let outputs = leaves(p.outputs.iter(), Some(role_index as u32))?;
            require(
                inputs.len() == entry.inputs.len() && outputs.len() == entry.outputs.len(),
                E::NativeBinding,
            )?;
            for ((_, ty), (_, actual)) in inputs.iter().zip(&entry.inputs) {
                require(*ty == actual.logical().spelling(), E::NativeBinding)?;
            }
            for ((_, ty), actual) in outputs.iter().zip(&entry.outputs) {
                require(*ty == actual.logical().spelling(), E::NativeBinding)?;
            }
            let services: Vec<_> = self.services(role).collect();
            require(services.len() == entry.services.len(), E::NativeBinding)?;
            for (index, (service, actual)) in services.iter().zip(&entry.services).enumerate() {
                require(
                    service.contract == actual.contract.name()
                        && actual.input_index == inputs.len() + index,
                    E::NativeBinding,
                )?;
            }
        }
        Ok(())
    }
    /// Check the exact deployment, complete original-port mappings and selected
    /// construction. This is admission consistency, not a soundness judgment.
    pub fn check_proof(&self, deployment: &NativeDeployment) -> Result<()> {
        let p = &self.document.protocols[self.selected];
        let proof = self.proof().ok_or(E::NativeBinding)?;
        let prover = &self.roles()[proof.prover].native_name;
        let verifier = &self.roles()[proof.verifier].native_name;
        let native = deployment.source_interface();
        let role = native.operation.map(|producing| {
            &self.roles()[if producing {
                proof.prover
            } else {
                proof.verifier
            }]
            .name
        });
        self.view.check_executable_role(role.map(String::as_str))?;
        let entry = deployment.entry();
        let suite = proof.suite.as_deref();
        let services: Vec<_> = proof
            .replaced_services
            .iter()
            .map(|&i| p.services[i].native as usize)
            .collect();
        let actual_choices: &[String] = native.choices.as_ref();
        let mut expected_choices: Vec<String> = [
            self.options.simplify,
            self.options.release_storage,
            self.options.fuse_vector_reductions,
            self.options.finite_bulk,
            self.options.fuse_collect_fold,
            self.options.calculation_batching,
        ]
        .into_iter()
        .map(|value| value.to_string())
        .collect();
        expected_choices.push(
            self.options
                .oracle_realization
                .canonical_json()
                .map_err(|_| E::NativeBinding)?,
        );
        require(
            native.publication == self.artifact
                && native.source == self.original()
                && actual_choices == expected_choices.as_slice()
                && entry.entry() == p.symbol
                && native.producer == prover
                && native.validator == verifier
                && native.acceptance == proof.acceptance
                && native.suite == suite
                && native.construction == proof.construction.as_deref().unwrap_or("")
                && native.gates
                    == proof
                        .gates
                        .iter()
                        .map(|(site, bits)| serde_json::json!([site, bits.to_string()]))
                        .collect::<Vec<_>>()
                && native.format == proof.format
                && native.services == services
                && native.roles.len()
                    == if native.operation.is_some() && native.roles.len() == 1 {
                        1
                    } else {
                        p.roles.len()
                    },
            E::NativeBinding,
        )?;
        let expected_public: Vec<_> = self
            .public_ports()
            .flat_map(|p| {
                p.definition
                    .native
                    .iter()
                    .zip(&p.definition.schema.leaves)
                    .map(|(&n, t)| (n as usize, t.as_str()))
            })
            .collect::<std::collections::BTreeMap<_, _>>()
            .into_iter()
            .collect();
        self.ports(
            &expected_public,
            native.public.iter().map(|p| (p.original, &p.logical)),
        )?;
        for (role_index, ports) in self.roles().iter().enumerate() {
            let role = &ports.native_name;
            let Some(actual) = native.roles.get(role) else {
                require(
                    native.operation.is_some_and(|producing| {
                        if producing {
                            role == verifier
                        } else {
                            role == prover
                        }
                    }),
                    E::NativeBinding,
                )?;
                continue;
            };
            self.ports(
                &leaves(p.inputs.iter(), Some(role_index as u32))?,
                actual.data.iter().map(|p| (p.original, &p.logical)),
            )?;
            self.ports(
                &leaves(p.outputs.iter(), Some(role_index as u32))?,
                actual.outputs.iter().map(|p| (p.original, &p.logical)),
            )?;
            let services: Vec<_> = self.services(ports).map(|s| s.native as usize).collect();
            require(actual.services == services, E::NativeBinding)?;
            let native_role = if role == prover {
                entry.producer()
            } else {
                entry.validator()
            }
            .ok_or(E::NativeBinding)?;
            let contracts: Vec<_> = self.services(ports).collect();
            require(
                contracts.len() == native_role.services.len(),
                E::NativeBinding,
            )?;
            for (expected, actual) in contracts.into_iter().zip(&native_role.services) {
                require(
                    expected.contract == actual.contract.name(),
                    E::NativeBinding,
                )?;
            }
        }
        Ok(())
    }
    fn ports<'a>(
        &self,
        expected: &[(usize, &str)],
        actual: impl ExactSizeIterator<Item = (usize, &'a LogicalType)>,
    ) -> Result<()> {
        require(expected.len() == actual.len(), E::NativeBinding)?;
        for ((index, ty), (at, actual)) in expected.iter().zip(actual) {
            require(*index == at && *ty == actual.spelling(), E::NativeBinding)?;
        }
        Ok(())
    }
}
pub(super) fn leaves<'a>(
    ports: impl Iterator<Item = &'a Port>,
    role: Option<u32>,
) -> Result<Vec<(usize, &'a str)>> {
    let mut result = std::collections::BTreeMap::new();
    for port in ports {
        for component in &port.components {
            if role.is_some_and(|r| r != component.role) {
                continue;
            }
            let ty =
                super::placement::component_type(port, component).map_err(|_| E::NativeBinding)?;
            let index = component.native as usize;
            if let Some(previous) = result.insert(index, ty) {
                require(previous == ty, E::NativeBinding)?;
            }
        }
    }
    Ok(result.into_iter().collect())
}
