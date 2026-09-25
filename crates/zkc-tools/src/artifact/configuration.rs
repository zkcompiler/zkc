//! Application-authorized setup material and exact input/receive selection.
//! Candidate wire bytes cannot extend this authority or choose a setup.
use super::{
    Observed,
    construction::{CheckedBundle, type_spelling},
    io::*,
    material::MaterialCache,
};
use crate::protocol::{MessageDecoder, WireBackend};
use serde_json::Value as Json;
use std::{collections::BTreeMap, sync::Arc};
use zkc_arkworks::{Metadata, VerifierKey};
use zkc_backends::{NativeBackend, Policy, PortConstraint, SetupRegistry, Value};
use zkc_runtime::interactive::{BackendError, EntryRole, PhysicalType, Receive, Type};

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
struct ReceiveSite {
    instance: String,
    role: String,
    site: String,
}
struct ReceiveSetup {
    schema: String,
    ty: PhysicalType,
    setup: Metadata,
}
pub(super) struct Decoder {
    receives: BTreeMap<ReceiveSite, ReceiveSetup>,
}
impl Decoder {
    fn decode(
        &self,
        backend: &NativeBackend,
        receive: &Receive,
        bytes: &[u8],
    ) -> std::result::Result<Value, BackendError> {
        if !zkc_backends::requires_setup(receive.ty.logical()) {
            return backend.decode(receive.ty.clone(), bytes);
        }
        let envelope = &receive.envelope;
        let selected = self
            .receives
            .get(&ReceiveSite {
                instance: envelope.origin.instance.clone(),
                role: envelope.receiver.clone(),
                site: envelope.site.clone(),
            })
            .ok_or_else(|| BackendError::new("refused:artifact-receive-setup"))?;
        if selected.schema != envelope.schema || selected.ty != receive.ty {
            return Err(BackendError::new("refused:artifact-receive-port"));
        }
        backend.decode_for_setup(receive.ty.clone(), selected.setup, bytes)
    }
}
impl MessageDecoder<Observed<NativeBackend>> for Decoder {
    fn decode(
        &self,
        backend: &Observed<NativeBackend>,
        receive: &Receive,
        bytes: &[u8],
    ) -> std::result::Result<Value, BackendError> {
        self.decode(backend.inner(), receive, bytes)
    }
}

pub(super) struct Configuration {
    pub keys: BTreeMap<String, Arc<VerifierKey>>,
    pub registry: SetupRegistry,
    pub decoder: Decoder,
    inputs: BTreeMap<(String, String), Metadata>,
}
impl Configuration {
    pub fn input_setup(&self, role: &str, port: &str) -> Option<Metadata> {
        self.inputs.get(&(role.into(), port.into())).copied()
    }
    /// Carry application selections through the checked construction's input
    /// map into the actual runner entry, independently of public wire headers.
    pub fn entry_ports(
        &self,
        bundle: &CheckedBundle,
        role: &EntryRole,
    ) -> Result<BTreeMap<String, PortConstraint>> {
        let mut constraints = BTreeMap::new();
        let generated = bundle
            .generated_ports
            .iter()
            .filter(|p| p.role == role.role)
            .collect::<Vec<_>>();
        if generated.len() != role.inputs.len() {
            return Err("artifact-input-map-arity".into());
        }
        for (port, (physical, ty)) in generated.into_iter().zip(&role.inputs) {
            if !zkc_backends::requires_setup(ty.logical()) {
                continue;
            }
            let row = list(&bundle.manifest[3])?
                .iter()
                .find(|row| {
                    row.get(0).and_then(Json::as_str) == Some(&role.role)
                        && row.get(1).and_then(Json::as_str) == Some(&port.name)
                })
                .ok_or("artifact-input-map")?;
            let selected = match list(&array(row, 3)?[2])? {
                [tag, name] if tag == "source" => self.input_setup(&role.role, text(name)?),
                [tag, label] if tag == "public" => {
                    let declaration = list(&bundle.descriptor[4])?
                        .iter()
                        .find(|d| d.get(0) == Some(label))
                        .ok_or("artifact-public-map")?;
                    let target = list(&array(declaration, 2)?[1])?
                        .first()
                        .ok_or("artifact-public-port")?;
                    let target = array(target, 2)?;
                    self.input_setup(text(&target[0])?, text(&target[1])?)
                }
                _ => return Err("artifact-input-map".into()),
            }
            .ok_or("artifact-input-setup-coverage")?;
            constraints.insert(
                physical.clone(),
                PortConstraint {
                    arity: Some(selected.arity()),
                    setup: Some(selected),
                },
            );
        }
        Ok(constraints)
    }
    pub fn load(
        bundle: &CheckedBundle,
        value: &Json,
        work: &mut impl FnMut(usize) -> Result<()>,
        policy: &Policy,
        cache: &mut MaterialCache,
    ) -> Result<Self> {
        let format = bundle.admitted.format();
        let config = array(value, 4)?;
        if config[0] != "zkc.public-configuration/1" {
            return Err("artifact-configuration".into());
        }
        let ports = bundle
            .ports
            .iter()
            .filter(|p| p.role == bundle.validator && p.ty.kind() == Type::VerifierKey)
            .collect::<Vec<_>>();
        let records = list(&config[1])?;
        if records.len() != ports.len() {
            return Err("artifact-configuration-ports".into());
        }
        let mut material: BTreeMap<Vec<u8>, Arc<VerifierKey>> = BTreeMap::new();
        let mut keys = BTreeMap::new();
        for (record, port) in records.iter().zip(ports) {
            let r = array(record, 3)?;
            if text(&r[0])? != port.name || text(&r[1])? != type_spelling(port.ty.clone(), format) {
                return Err("artifact-configuration-order".into());
            }
            let bytes = unhex(&r[2])?;
            work(bytes.len())?;
            let key = if let Some(key) = material.get(&bytes) {
                key.clone()
            } else {
                if material.len() >= 64 {
                    return Err("artifact-setup-count".into());
                }
                // Exact bytes, fully validated on the first import. Configuration
                // coverage and setup selection are still checked on every call.
                let key = cache.verifier(&bytes, policy)?;
                material.insert(bytes, key.clone());
                key
            };
            keys.insert(port.name.clone(), key);
        }
        // Only byte-identical repeated keys are shared. Distinct material with
        // the same metadata is rejected by the registry, never silently selected.
        let registry = SetupRegistry::new(
            material.values().map(|k| k.as_ref().clone()).collect(),
            policy,
        )
        .map_err(|e| e.to_string())?;
        let mut inputs = BTreeMap::new();
        let mut receives = BTreeMap::new();
        let mut expected = bundle
            .ports
            .iter()
            .filter(|p| zkc_backends::requires_setup(p.ty.clone()))
            .map(|p| ((p.role.clone(), p.name.clone()), p))
            .collect::<BTreeMap<_, _>>();
        for record in list(&config[2])? {
            let r = array(record, 3)?;
            let at = (text(&r[0])?.to_owned(), text(&r[1])?.to_owned());
            expected
                .remove(&at)
                .ok_or("artifact-input-setup-port-or-duplicate")?;
            let key = keys.get(text(&r[2])?).ok_or("artifact-input-setup-key")?;
            inputs.insert(at, key.metadata());
        }
        if !expected.is_empty() {
            return Err("artifact-input-setup-coverage".into());
        }
        let mut expected = bundle
            .admitted
            .executable_receive_ports(&bundle.entry)
            .ok_or("artifact-entry")?
            .into_iter()
            .filter(|p| zkc_backends::requires_setup(p.ty.logical()))
            .map(|p| {
                (
                    ReceiveSite {
                        instance: p.instance.clone(),
                        role: p.role.clone(),
                        site: p.site.clone(),
                    },
                    p,
                )
            })
            .collect::<BTreeMap<_, _>>();
        for record in list(&config[3])? {
            let r = array(record, 4)?;
            let at = ReceiveSite {
                instance: text(&r[0])?.into(),
                role: text(&r[1])?.into(),
                site: text(&r[2])?.into(),
            };
            let port = expected
                .remove(&at)
                .ok_or("artifact-receive-site-or-duplicate")?;
            let key = keys.get(text(&r[3])?).ok_or("artifact-receive-key")?;
            receives.insert(
                at,
                ReceiveSetup {
                    schema: port.schema,
                    ty: port.ty,
                    setup: key.metadata(),
                },
            );
        }
        if !expected.is_empty() {
            return Err("artifact-receive-coverage".into());
        }
        Ok(Self {
            keys,
            registry,
            decoder: Decoder { receives },
            inputs,
        })
    }
}
