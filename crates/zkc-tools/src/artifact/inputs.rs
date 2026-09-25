//! Application-authorized root, key loading and exact original-source inputs.
use super::{
    configuration::{Configuration, Decoder},
    construction::{CheckedBundle, type_spelling},
    io::*,
    material::MaterialCache,
};
use serde_json::{Value as Json, json};
use sha2::{Digest, Sha256};
use std::collections::BTreeMap;
use zkc_backends::{Capability, Domain, EntryPolicy, NativeBackend, Policy, PublicInputs, Value};
use zkc_runtime::{
    interactive::{Backend, EntryRole, Type},
    logical::encode_tree,
};

pub(super) mod admission;
use admission::{Admission, Input, LoadLimits};

pub(super) struct BoundInputs {
    pub backend: NativeBackend,
    pub values: Vec<Value>,
    pub binding: [u8; 32],
    pub resources: Vec<(String, Capability)>,
    pub decoder: Decoder,
}
impl CheckedBundle {
    pub(super) fn bind(&self, input: &Json, role: &EntryRole, budget: u64) -> Result<BoundInputs> {
        self.bind_with_limits(input, role, budget, LoadLimits::default())
    }

    fn bind_with_limits(
        &self,
        input: &Json,
        role: &EntryRole,
        budget: u64,
        limits: LoadLimits,
    ) -> Result<BoundInputs> {
        self.bind_cached(input, role, budget, limits, &mut MaterialCache::disabled())
    }

    pub(super) fn bind_cached(
        &self,
        input: &Json,
        role: &EntryRole,
        budget: u64,
        limits: LoadLimits,
        cache: &mut MaterialCache,
    ) -> Result<BoundInputs> {
        let mut admission = Admission::new(limits);
        let envelope = array(input, 5)?;
        let format = self.admitted.format();
        if envelope[0] != "zkc.artifact-inputs/1" {
            return Err("artifact-input-version".into());
        }
        unhex(&envelope[1])?;
        let policy = Policy::default();
        let resolved_configuration = self
            .identity
            .as_ref()
            .map(|i| i.configuration(&envelope[4]))
            .transpose()?;
        let configuration = resolved_configuration.as_ref().unwrap_or(&envelope[4]);
        let config = Configuration::load(
            self,
            configuration,
            &mut |n| admission.work(n),
            &policy,
            cache,
        )?;
        let keys = &config.keys;
        let domain = Domain::new(&role.role, "artifact", &self.entry, Some(&role.instance));
        // Resources are scoped to this actual role/session/entry and may flow
        // through its admitted nested instances, only via explicit frame operands.
        let resource_domain = Domain::new(&role.role, "artifact", &self.entry, None);
        let entry = EntryPolicy::new(domain.clone(), None, PublicInputs::LocalOnly)
            .with_parameters(role.parameters.clone())
            .with_ports(config.entry_ports(self, role)?);
        let mut backend = NativeBackend::with_setups(policy, entry, config.registry.clone())
            .map_err(|e| e.to_string())?;
        // load() has checked the complete public artifact profile and every
        // reached restricted implementation. bind() admits exact public roots,
        // configured VKs, one fresh deterministic transcript, and zero-budget
        // selected RNG below, before exposing this backend for execution.
        if role.role == self.validator {
            backend = backend.with_public_role_policy(
                zkc_backends::PublicRolePolicy::new([self.validator.clone()])
                    .map_err(|e| e.to_string())?,
            );
        }
        let declarations = list(&array(&self.descriptor, 9)?[4])?;
        let records = list(&envelope[2])?;
        let mut named_public = BTreeMap::new();
        for record in records {
            let r = array(record, 3)?;
            let label = text(&r[0])?;
            if named_public.insert(label, r).is_some() {
                return Err("artifact-duplicate-public".into());
            }
            if !declarations
                .iter()
                .any(|d| d.get(0).and_then(Json::as_str) == Some(label))
            {
                return Err("artifact-unknown-public".into());
            }
        }
        if named_public.len() != declarations.len() {
            return Err("artifact-public-coverage".into());
        }
        let mut public = BTreeMap::new();
        let mut owned: BTreeMap<String, usize> = BTreeMap::new();
        let mut root_public = Vec::new();
        for declaration in declarations {
            let d = array(declaration, 2)?;
            let r = named_public
                .get(text(&d[0])?)
                .ok_or("artifact-public-coverage")?;
            let targets = list(&d[1])?;
            let mut ty = None;
            let mut setup = None;
            let mut first_target = true;
            for target in targets {
                let t = array(target, 2)?;
                let port = self
                    .ports
                    .iter()
                    .find(|p| {
                        p.role == text(&t[0]).unwrap_or("") && p.name == text(&t[1]).unwrap_or("")
                    })
                    .ok_or("artifact-public-port")?;
                let selected = config.input_setup(&port.role, &port.name);
                if !first_target && setup != selected {
                    return Err("artifact-public-setup".into());
                }
                first_target = false;
                setup = selected;
                if ty
                    .replace(port.ty.clone())
                    .is_some_and(|prev| prev != port.ty)
                    || !port.ty.kind().is_serializable()
                {
                    return Err("artifact-public-type".into());
                }
            }
            let ty = ty.ok_or("artifact-public-port")?;
            if text(&r[1])? != type_spelling(ty.clone(), format) {
                return Err("artifact-public-type".into());
            }
            let value = admission.add(Input::wire(ty.clone(), setup, &r[2])?, &policy)?;
            for target in targets {
                let t = array(target, 2)?;
                if text(&t[0])? == role.role && owned.insert(text(&t[1])?.into(), value).is_some() {
                    return Err("artifact-public-port-reuse".into());
                }
            }
            if public.insert(text(&r[0])?.to_owned(), value).is_some() {
                return Err("artifact-duplicate-public".into());
            }
            root_public.push(json!([r[0], ty.spelling(), r[2]]));
        }
        for (name, vk) in keys {
            if role.role == self.validator {
                owned.insert(
                    name.clone(),
                    admission.add(Input::Ready(Value::VerifierKey(vk.clone())), &policy)?,
                );
            }
        }
        let root = if let Some(identity) = &self.identity {
            identity.binding(&envelope[1], &Json::Array(root_public), configuration)?
        } else {
            encode_tree(&json!([
                "zkc.artifact-binding/1",
                self.source,
                self.descriptor,
                envelope[1],
                root_public,
                envelope[4]
            ]))
            .map_err(|e| e.to_string())?
        };
        let binding = Sha256::digest(&root).into();
        let mut seen = std::collections::BTreeSet::new();
        let mut resources = Vec::new();
        for record in list(&envelope[3])? {
            let r = list(record)?;
            let name = text(r.first().ok_or("artifact-input-record")?)?;
            if !seen.insert(name.to_owned()) {
                return Err("artifact-duplicate-input".into());
            }
            let port = self
                .ports
                .iter()
                .find(|p| p.name == name && p.role == role.role)
                .ok_or("artifact-unknown-input")?;
            if name == self.selected_rng && role.role == self.validator {
                return Err("artifact-injected-selected-rng".into());
            }
            let tag = text(r.get(1).ok_or("artifact-input-record")?)?;
            let value = match tag {
                "prover_key_file" => {
                    array(record, 5)?;
                    if role.role != self.producer || port.ty.kind() != Type::ProverKey {
                        return Err("artifact-private-input".into());
                    }
                    let fingerprint = unhex(&r[3])?
                        .try_into()
                        .map_err(|_| "artifact-material-fingerprint")?;
                    let vk = keys
                        .get(text(&r[4])?)
                        .ok_or("artifact-prover-key-association")?;
                    Input::Key {
                        path: text(&r[2])?,
                        fingerprint,
                        verifier: vk.clone(),
                    }
                }
                "nonce" | "rng" => {
                    array(record, 3)?;
                    if port.ty.kind().name() != tag {
                        return Err("artifact-private-input".into());
                    }
                    let budget = natural(&r[2])?;
                    Input::Ready(
                        if tag == "nonce" {
                            backend.issue_nonce_for(
                                port.ty.identity(),
                                resource_domain.clone(),
                                budget,
                            )
                        } else {
                            backend.issue_rng_for(
                                port.ty.identity(),
                                resource_domain.clone(),
                                budget,
                            )
                        }
                        .map_err(|e| e.to_string())?,
                    )
                }
                tag if tag == type_spelling(port.ty.clone(), format)
                    && port.ty.kind() == Type::VerifierKey =>
                {
                    array(record, 3)?;
                    let expected = keys.get(name).ok_or("artifact-verifier-key-port")?;
                    if role.role != self.validator
                        || port.ty.kind() != Type::VerifierKey
                        || unhex(&r[2])?
                            != expected
                                .to_bytes(&policy.ark_bounds())
                                .map_err(|e| e.to_string())?
                    {
                        return Err("artifact-configuration-equality".into());
                    }
                    Input::Ready(Value::VerifierKey(expected.clone()))
                }
                _ => {
                    array(record, 3)?;
                    if tag != type_spelling(port.ty.clone(), format)
                        || !port.ty.kind().is_serializable()
                    {
                        return Err("artifact-input-type".into());
                    }
                    Input::wire(
                        port.ty.clone(),
                        config.input_setup(&port.role, &port.name),
                        &r[2],
                    )?
                }
            };
            if let Some(&expected) = owned.get(name) {
                // Canonical hex equality suffices here: the selected public
                // value is still decoded and canonicalized below, exactly once.
                if port.ty.kind() != Type::VerifierKey && !admission.same_wire(expected, &value) {
                    return Err("artifact-public-equality".into());
                }
            } else {
                owned.insert(name.to_owned(), admission.add(value, &policy)?);
            }
        }
        let mut operands = Vec::new();
        let mut used = std::collections::BTreeSet::new();
        let mut transcript_count = 0;
        let common_ports = self
            .generated_ports
            .iter()
            .filter(|p| p.role == role.role)
            .collect::<Vec<_>>();
        if common_ports.len() != role.inputs.len() {
            return Err("artifact-input-map".into());
        }
        for (port, (physical, ty)) in common_ports.into_iter().zip(&role.inputs) {
            let generated = &port.name;
            if port.ty != ty.logical() {
                return Err("artifact-input-map-type".into());
            }
            let rows = list(&self.manifest[3])?;
            let row = rows
                .iter()
                .find(|r| {
                    r.get(0).and_then(Json::as_str) == Some(&role.role)
                        && r.get(1).and_then(Json::as_str) == Some(generated)
                })
                .ok_or("artifact-input-map")?;
            let row = array(row, 3)?;
            let map = list(&row[2])?;
            let value = match map {
                [tag] if tag == "transcript" => {
                    transcript_count += 1;
                    admission.add(
                        Input::Ready(
                            backend
                                .issue_transcript_for(
                                    ty.logical().identity(),
                                    resource_domain.clone(),
                                    budget,
                                    &root,
                                )
                                .map_err(|e| e.to_string())?,
                        ),
                        &policy,
                    )?
                }
                [tag, label] if tag == "public" => {
                    *public.get(text(label)?).ok_or("artifact-public-map")?
                }
                [tag, port] if tag == "source" => {
                    let name = text(port)?;
                    if !used.insert(name.to_owned()) {
                        return Err("artifact-input-map-reuse".into());
                    }
                    if name == self.selected_rng && role.role == self.validator {
                        admission.add(
                            Input::Ready(
                                backend
                                    .issue_rng_for(
                                        ty.logical().identity(),
                                        resource_domain.clone(),
                                        0,
                                    )
                                    .map_err(|e| e.to_string())?,
                            ),
                            &policy,
                        )?
                    } else {
                        owned.remove(name).ok_or("artifact-missing-input")?
                    }
                }
                _ => return Err("artifact-input-map".into()),
            };
            admission.operand(value, ty.kind())?;
            operands.push((value, physical, ty));
        }

        // Any explicitly provided source input must actually enter the artifact.
        if seen.iter().any(|s| !used.contains(s)) || !owned.is_empty() {
            return Err("artifact-unused-input".into());
        }
        if transcript_count != 1 {
            return Err("artifact-transcript-map".into());
        }
        // All source/public values and every physical operand are admitted
        // before any PK read or ordinary wire deserialization.
        let loaded = admission.load_cached(&backend, &policy, cache)?;
        let mut values = Vec::new();
        for (index, physical, ty) in operands {
            let value = loaded[index].clone();
            backend.validate_value(&value).map_err(|e| e.to_string())?;
            if let Value::Rng(t) | Value::Nonce(t) | Value::Transcript(t) = &value {
                resources.push((format!("{}:{}", ty.kind().name(), physical), t.clone()));
            }
            values.push(value);
        }
        Ok(BoundInputs {
            backend,
            values,
            binding,
            resources,
            decoder: config.decoder,
        })
    }
}

#[cfg(test)]
pub(super) mod tests;
