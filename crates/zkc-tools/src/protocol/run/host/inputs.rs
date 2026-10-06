use super::*;
use zkc_runtime::interactive::PhysicalType;
/// Trusted setup identities and input assignments. Received PCS headers can
/// select only among these authorized keys; this is not a per-site receive pin.
#[derive(Clone, Debug, Default)]
pub struct SetupAuthority {
    pub keys: BTreeMap<String, [u8; 32]>,
    pub inputs: BTreeMap<(String, usize), String>,
}
impl SetupAuthority {
    pub fn parse(bytes: &[u8]) -> Result<Self> {
        let value = parse(bytes, 64 * 1024)?;
        let row = array(&value, 3)?;
        if text(&row[0])? != "zkc.bundle-setups/1" {
            return Err("bundle-setup-format".into());
        }
        let mut result = Self::default();
        for row in list(&row[1])? {
            let row = array(row, 2)?;
            if result
                .keys
                .insert(identifier(&row[0])?.into(), digest(text(&row[1])?)?)
                .is_some()
            {
                return Err("bundle-setup-duplicate".into());
            }
        }
        for row in list(&row[2])? {
            let row = array(row, 3)?;
            if result
                .inputs
                .insert(
                    (identifier(&row[0])?.into(), index(&row[1])?),
                    identifier(&row[2])?.into(),
                )
                .is_some()
            {
                return Err("bundle-setup-duplicate".into());
            }
        }
        Ok(result)
    }
    pub(super) fn check(&self, bundle: &Bundle) -> Result<()> {
        let expected: std::collections::BTreeSet<_> = bundle
            .roles()
            .iter()
            .flat_map(|r| {
                r.entry
                    .inputs
                    .iter()
                    .enumerate()
                    .filter(|(_, (_, ty))| needs_key(ty))
                    .map(|(i, _)| (r.entry.role.clone(), i))
            })
            .collect();
        if self.keys.keys().any(|name| !valid_identifier(name))
            || self.keys.len() > 64
            || self
                .inputs
                .keys()
                .cloned()
                .collect::<std::collections::BTreeSet<_>>()
                != expected
            || self.inputs.values().any(|key| !self.keys.contains_key(key))
        {
            return Err("bundle-setup-authority".into());
        }
        Ok(())
    }
}
fn needs_key(ty: &PhysicalType) -> bool {
    ty.kind() == Type::VerifierKey || needs_input_setup(&ty.logical())
}
pub(super) fn kind(ty: &PhysicalType) -> &'static str {
    match ty.kind() {
        Type::Rng => "rng",
        Type::Nonce => "nonce",
        Type::ProverKey => "prover_key_file",
        Type::VerifierKey => "verifier_key",
        Type::Transcript => "unsupported-transcript",
        _ if zkc_backends::has_native_wire(ty) => "wire",
        _ => "unsupported",
    }
}
fn index(value: &Json) -> Result<usize> {
    usize::try_from(natural(value)?)
        .ok()
        .filter(|i| *i < 1024)
        .ok_or("bundle-input-index".into())
}
fn identifier(value: &Json) -> Result<&str> {
    let value = text(value)?;
    if !valid_identifier(value) {
        return Err("bundle-input-name".into());
    }
    Ok(value)
}
fn valid_identifier(value: &str) -> bool {
    !value.is_empty()
        && value.len() <= 128
        && value
            .bytes()
            .all(|b| b.is_ascii_alphanumeric() || b"_.-".contains(&b))
}
fn budget(value: &Json) -> Result<u64> {
    let budget = natural(value)?;
    if budget > 1_000_000 {
        return Err("bundle-resource-budget".into());
    }
    Ok(budget)
}
pub(super) fn prepare<'a>(host: &'a RunHost, bytes: &[u8]) -> Result<PreparedRun<'a>> {
    let value = parse(bytes, INPUT_LIMIT)?;
    let root = array(&value, 4)?;
    if text(&root[0])? != "zkc.bundle-inputs/1" {
        return Err("bundle-input-format".into());
    }
    let session = identifier(&root[1])?.to_owned();
    let rows = list(&root[2])?;
    if rows.len() != host.bundle.roles().len() {
        return Err("bundle-input-roles".into());
    }
    let policy = host.limits.capacity.backend();
    let mut keys = BTreeMap::new();
    let mut material = BTreeMap::new();
    for row in list(&root[3])? {
        let row = array(row, 2)?;
        let name = identifier(&row[0])?;
        let pin = host
            .authority
            .keys
            .get(name)
            .ok_or("bundle-setup-authority")?;
        let bytes = host.limits.capacity.wire(&row[1])?;
        let key = zkc_arkworks::VerifierKey::from_bytes(&bytes, *pin, &policy.ark_bounds())
            .map_err(|e| e.to_string())?;
        if key
            .to_bytes(&policy.ark_bounds())
            .map_err(|e| e.to_string())?
            != bytes
        {
            return Err("bundle-canonical-key".into());
        }
        let key = Arc::new(key);
        material.entry(bytes).or_insert_with(|| key.clone());
        if keys.insert(name.to_owned(), key).is_some() {
            return Err("bundle-setup-duplicate".into());
        }
    }
    if !keys.keys().eq(host.authority.keys.keys()) {
        return Err("bundle-setup-material".into());
    }
    let setups = SetupRegistry::new(
        material.values().map(|k| k.as_ref().clone()).collect(),
        &policy,
    )
    .map_err(|e| e.to_string())?;
    let mut roles = Vec::new();
    let mut admission = Admission::new(host.limits.capacity.loading());
    // The authorized registry retains even receive-only keys, independently
    // of whether an entry operand uses them. Charge that material once.
    for key in keys.values() {
        admission.add(Input::Ready(Value::VerifierKey(key.clone())), &policy)?;
    }
    for (row, role) in rows.iter().zip(host.bundle.roles()) {
        let row = array(row, 3)?;
        if text(&row[0])? != role.entry.role {
            return Err("bundle-input-roles".into());
        }
        let data = list(&row[1])?;
        let service_rows = list(&row[2])?;
        if data.len() != role.entry.inputs.len() || service_rows.len() != role.entry.services.len()
        {
            return Err("bundle-input-count".into());
        }
        let mut ports = BTreeMap::new();
        for (i, (name, ty)) in role.entry.inputs.iter().enumerate() {
            if matches!(
                ty.kind(),
                Type::VerifierKey | Type::ProverKey | Type::Commitment | Type::Proof
            ) && let Some(key) = host.authority.inputs.get(&(role.entry.role.clone(), i))
            {
                ports.insert(
                    name.clone(),
                    PortConstraint {
                        arity: None,
                        setup: Some(keys[key].metadata()),
                    },
                );
            }
        }
        let backend = NativeBackend::with_setups(
            policy,
            EntryPolicy::new(
                Domain::new(
                    &role.entry.role,
                    &session,
                    host.bundle.entry(),
                    Some(&role.entry.instance),
                ),
                None,
                PublicInputs::LocalOnly,
            )
            .with_ports(ports),
            setups.clone(),
        )
        .map_err(|e| e.to_string())?
        .with_external_work_limit(host.limits.external_work);
        let mut pending = Vec::new();
        for (i, (row, (_, ty))) in data.iter().zip(&role.entry.inputs).enumerate() {
            let row = array(row, 3)?;
            if index(&row[0])? != i || text(&row[1])? != ty.spelling() {
                return Err("bundle-input-port".into());
            }
            let spec = array(&row[2], 2)?;
            let expected = kind(ty);
            if expected == "unsupported-transcript" {
                return Err("bundle-transcript-input-unsupported".into());
            }
            if expected == "unsupported" || text(&spec[0])? != expected {
                return Err("bundle-input-kind".into());
            }
            let selected = host
                .authority
                .inputs
                .get(&(role.entry.role.clone(), i))
                .map(|k| &keys[k]);
            let item = match expected {
                "rng" | "nonce" => {
                    pending.push(admission.resource(ResourceInput {
                        kind: ty.kind(),
                        field: ty.logical().identity(),
                        budget: budget(&spec[1])?,
                    })?);
                    continue;
                }
                "wire" => {
                    let bytes = host.limits.capacity.wire(&spec[1])?;
                    Input::native_wire(&backend, ty.clone(), bytes, selected.cloned())?
                }
                "verifier_key" => {
                    let name = text(&spec[1])?;
                    if host
                        .authority
                        .inputs
                        .get(&(role.entry.role.clone(), i))
                        .map(String::as_str)
                        != Some(name)
                    {
                        return Err("bundle-setup-input".into());
                    }
                    let value = Value::VerifierKey(keys[name].clone());
                    if value.physical_type() != *ty {
                        return Err("bundle-input-type".into());
                    }
                    Input::Ready(value)
                }
                "prover_key_file" => {
                    let spec = array(&spec[1], 2)?;
                    Input::Key {
                        path: text(&spec[0])?,
                        fingerprint: digest(text(&spec[1])?)?,
                        verifier: selected.ok_or("bundle-setup-input")?.clone(),
                    }
                }
                _ => unreachable!("checked input kind"),
            };
            let id = admission.add(item, &policy)?;
            pending.push(admission.data(id, ty.kind())?);
        }
        let services = service_rows
            .iter()
            .zip(&role.entry.services)
            .enumerate()
            .map(|(i, (row, port))| {
                let row = array(row, 3)?;
                if index(&row[0])? != i || text(&row[1])? != port.contract.name() {
                    return Err("bundle-service-port".into());
                }
                budget(&row[2])
            })
            .collect::<Result<Vec<_>>>()?;
        roles.push((role.entry.clone(), backend, pending, services));
    }
    // Charge the entire invocation, not a separate resettable budget per role.
    // Key files are frozen and imported only after every declaration is checked.
    // All roles share this native codec policy and authorized key registry.
    // There are no source-typed Input::Wire values requiring a role decoder.
    let loaded = admission.load_cached(&roles[0].1, &policy, &mut MaterialCache::disabled())?;
    let roles = roles
        .into_iter()
        .map(
            |(entry, backend, pending, services)| -> Result<PreparedRole> {
                backend
                    .check_entry_values(&entry, &entry_values(&pending, &loaded))
                    .map_err(|e| e.to_string())?;
                Ok(PreparedRole {
                    entry,
                    backend,
                    values: pending,
                    services,
                })
            },
        )
        .collect::<Result<Vec<_>>>()?;
    Ok(PreparedRun {
        host,
        session,
        roles,
        loaded,
    })
}
