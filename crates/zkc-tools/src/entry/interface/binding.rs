//! Bind authenticated source metadata to the native owner's admitted ABI.
use super::{BoundInterface, InterfaceError as E, Result, raw::*, require};
use crate::{proof::NativeDeployment, run::RunHost};
use zkc_runtime::interactive::LogicalType;

impl BoundInterface {
    /// Check the exact package artifact and its participant ABI. The authenticated
    /// compiler publication owns source correspondence and run compile options;
    /// run bundles do not carry an independent original or options record.
    pub fn check_run(&self, host: &RunHost) -> Result<()> {
        let p = &self.document.protocols[self.selected];
        let bundle = host.bundle();
        require(
            matches!(self.document.job, Job::Run {})
                && host.identity() == self.artifact
                && bundle.entry() == p.symbol
                && bundle.roles().len() == p.roles.len(),
            E::NativeBinding,
        )?;
        for (role, actual) in self.roles().iter().zip(bundle.roles()) {
            let expected = &role.name;
            let entry = &actual.entry;
            require(&entry.role == expected, E::NativeBinding)?;
            let inputs = leaves(self.input_ports(role).map(|p| p.definition));
            let outputs = leaves(self.output_ports(role));
            require(
                inputs.len() == entry.inputs.len() && outputs.len() == entry.outputs.len(),
                E::NativeBinding,
            )?;
            for ((_, ty), (_, actual)) in inputs.iter().zip(&entry.inputs) {
                require(
                    self.logical_type(ty) == Some(&actual.logical()),
                    E::NativeBinding,
                )?;
            }
            for ((_, ty), actual) in outputs.iter().zip(&entry.outputs) {
                require(
                    self.logical_type(ty) == Some(&actual.logical()),
                    E::NativeBinding,
                )?;
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
        let prover = &self.roles()[proof.prover].name;
        let verifier = &self.roles()[proof.verifier].name;
        let native = deployment.source_interface();
        let entry = deployment.entry();
        let suite = proof.suite.as_deref();
        let service = proof.transcript.map(|i| p.services[i].native as usize);
        require(
            native.publication == self.artifact
                && native.source == self.original()
                && native.choices == [self.options.simplify, self.options.release_storage]
                && entry.entry() == p.symbol
                && &entry.producer().role == prover
                && &entry.validator().role == verifier
                && native.acceptance == proof.acceptance
                && native.suite == suite
                && native.service == service
                && native.roles.len() == p.roles.len(),
            E::NativeBinding,
        )?;
        let expected_public = leaves(self.public_ports().map(|p| p.definition));
        self.ports(
            &expected_public,
            native.public.iter().map(|p| (p.original, &p.logical)),
        )?;
        for ports in self.roles() {
            let role = &ports.name;
            let actual = native.roles.get(role).ok_or(E::NativeBinding)?;
            self.ports(
                &leaves(self.input_ports(ports).map(|p| p.definition)),
                actual.data.iter().map(|p| (p.original, &p.logical)),
            )?;
            self.ports(
                &leaves(self.output_ports(ports)),
                actual.outputs.iter().map(|p| (p.original, &p.logical)),
            )?;
            let services: Vec<_> = self.services(ports).map(|s| s.native as usize).collect();
            require(actual.services == services, E::NativeBinding)?;
            let native_role = if role == prover {
                entry.producer()
            } else {
                entry.validator()
            };
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
            require(
                *index == at && self.logical_type(ty) == Some(actual),
                E::NativeBinding,
            )?;
        }
        Ok(())
    }
}
fn leaves<'a>(ports: impl Iterator<Item = &'a Port>) -> Vec<(usize, &'a str)> {
    ports
        .flat_map(|p| {
            p.native
                .iter()
                .zip(&p.schema.leaves)
                .map(|(n, t)| (*n as usize, t.as_str()))
        })
        .collect()
}
