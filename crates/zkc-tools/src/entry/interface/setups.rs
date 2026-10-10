//! Independent setup-selector admission over checked logical schemas.
use super::{InterfaceError as E, Result, identifier, raw, require, schemas::Schemas, validate};
use std::collections::BTreeSet;
use zkc_runtime::interactive::Type;

#[derive(Debug)]
pub(in crate::entry) struct Setup {
    pub name: String,
    pub native_name: String,
    pub inputs: BTreeSet<usize>,
    pub verifier_keys: BTreeSet<usize>,
}
pub(super) fn check(
    document: &raw::Interface,
    protocol: &raw::Protocol,
    schemas: &mut Schemas<'_>,
) -> Result<Vec<Setup>> {
    require(document.setups.len() <= 64, E::Limit)?;
    let mut expected = BTreeSet::new();
    let mut verifier_keys = BTreeSet::new();
    for port in &protocol.inputs {
        for (native, spelling) in port.native.iter().zip(&port.schema.leaves) {
            schemas.charge(1)?;
            let (kind, needs_setup) = schemas.setup_properties(spelling)?;
            if needs_setup {
                expected.insert(*native as usize);
            }
            if kind == Type::ProverKey
                && let raw::Job::Proof { verifier, .. } = &document.job
            {
                require(!port.roles.contains(verifier), E::Selection)?;
            }
            if kind == Type::VerifierKey {
                require(
                    port.schema.kind == raw::Kind::Builtin && port.native.len() == 1,
                    E::Selection,
                )?;
                verifier_keys.insert(*native as usize);
            }
        }
    }
    if matches!(document.job, raw::Job::Proof { .. }) {
        require(verifier_keys.len() <= 64, E::Limit)?;
    }
    let mut names = BTreeSet::new();
    let mut covered = BTreeSet::new();
    let mut result = Vec::new();
    for (index, slot) in document.setups.iter().enumerate() {
        schemas.charge(1 + slot.name.len() + slot.inputs.len())?;
        require(
            identifier(&slot.name) && names.insert(&slot.name) && !slot.inputs.is_empty(),
            E::Selection,
        )?;
        let mut setup = Setup {
            name: slot.name.clone(),
            native_name: crate::source_names::native_setup_name(index as u32),
            inputs: BTreeSet::new(),
            verifier_keys: BTreeSet::new(),
        };
        for selector in &slot.inputs {
            schemas.charge(1 + selector.path.len())?;
            let port = protocol
                .inputs
                .get(selector.port as usize)
                .ok_or(E::Selection)?;
            let (_, native) = validate::project(port, &selector.path)?;
            let mut nonempty = false;
            for native in native {
                schemas.charge(1)?;
                let index = *native as usize;
                if !expected.contains(&index) {
                    continue;
                }
                nonempty = true;
                require(covered.insert(index), E::Selection)?;
                setup.inputs.insert(index);
                if verifier_keys.contains(&index) {
                    if let raw::Job::Proof {
                        public, verifier, ..
                    } = &document.job
                    {
                        require(
                            public.contains(&port.index) && port.roles.contains(verifier),
                            E::Selection,
                        )?;
                    }
                    setup.verifier_keys.insert(index);
                }
            }
            require(nonempty, E::Selection)?;
        }
        if matches!(document.job, raw::Job::Proof { .. }) {
            require(!setup.verifier_keys.is_empty(), E::Selection)?;
        }
        result.push(setup);
    }
    require(covered.len() == expected.len(), E::Selection)?;
    Ok(result)
}
