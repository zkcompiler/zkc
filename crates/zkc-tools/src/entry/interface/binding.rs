//! Bind authenticated source metadata to the native owner's admitted ABI.
use super::{Interface, InterfaceError as E, Result, raw::*, require, validate};
use crate::{artifact::native::NativeDeployment, protocol::run::RunHost};
use zkc_runtime::interactive::LogicalType;

impl Interface {
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
        for (expected, actual) in p.roles.iter().zip(bundle.roles()) {
            let entry = &actual.entry;
            require(&entry.role == expected, E::NativeBinding)?;
            let inputs = leaves(&p.inputs, expected);
            let outputs = leaves(&p.outputs, expected);
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
            let services: Vec<_> = p.services.iter().filter(|s| &s.owner == expected).collect();
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
        let Job::Proof {
            prover,
            verifier,
            public,
            acceptance,
            construction,
            ..
        } = &self.document.job
        else {
            return Err(E::NativeBinding);
        };
        let native = deployment.source_interface();
        let entry = deployment.entry();
        let (_, accepted) = validate::select(p, acceptance)?;
        let (suite, service) = match construction {
            Construction::Authored {} => (None, None),
            Construction::FiatShamir { suite, service } => (
                Some(suite.as_str()),
                Some(p.services[*service as usize].native as usize),
            ),
        };
        require(
            native.version == 4
                && native.publication == self.artifact
                && native.source == self.original()
                && native.choices == [self.options.simplify, self.options.release_storage]
                && entry.entry() == p.symbol
                && &entry.producer().role == prover
                && &entry.validator().role == verifier
                && native.acceptance == accepted[0] as usize
                && native.suite == suite
                && native.service == service
                && native.roles.len() == p.roles.len(),
            E::NativeBinding,
        )?;
        let expected_public: Vec<_> = public
            .iter()
            .flat_map(|i| {
                let port = &p.inputs[*i as usize];
                port.native
                    .iter()
                    .zip(&port.schema.leaves)
                    .map(|(i, t)| (*i as usize, t.as_str()))
            })
            .collect();
        self.ports(
            &expected_public,
            native.public.iter().map(|p| (p.original, &p.logical)),
        )?;
        for role in &p.roles {
            let actual = native.roles.get(role).ok_or(E::NativeBinding)?;
            self.ports(
                &leaves(&p.inputs, role),
                actual.data.iter().map(|p| (p.original, &p.logical)),
            )?;
            self.ports(
                &leaves(&p.outputs, role),
                actual.outputs.iter().map(|p| (p.original, &p.logical)),
            )?;
            let services: Vec<_> = p
                .services
                .iter()
                .filter(|s| &s.owner == role && Some(s.native as usize) != service)
                .map(|s| s.native as usize)
                .collect();
            require(actual.services == services, E::NativeBinding)?;
            let native_role = if role == prover {
                entry.producer()
            } else {
                entry.validator()
            };
            let contracts = p
                .services
                .iter()
                .filter(|s| &s.owner == role && Some(s.native as usize) != service);
            require(
                contracts.clone().count() == native_role.services.len(),
                E::NativeBinding,
            )?;
            for (expected, actual) in contracts.zip(&native_role.services) {
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
fn leaves<'a>(ports: &'a [Port], role: &str) -> Vec<(usize, &'a str)> {
    ports
        .iter()
        .filter(|p| p.roles.iter().any(|r| r == role))
        .flat_map(|p| {
            p.native
                .iter()
                .zip(&p.schema.leaves)
                .map(|(n, t)| (*n as usize, t.as_str()))
        })
        .collect()
}
