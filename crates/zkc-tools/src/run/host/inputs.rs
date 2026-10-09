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
        if text(&row[0])? != "zkc.bundle-setups/0" {
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
    checked_budget(natural(value)?)
}
fn checked_budget(budget: u64) -> Result<u64> {
    if budget > crate::host::inputs::RESOURCE_BUDGET_LIMIT {
        return Err("bundle-resource-budget".into());
    }
    Ok(budget)
}
/// An invocation in admitted role and port order. Setup bytes are checked
/// against independently installed authority, including receive-only keys.
#[derive(Debug)]
pub struct RunInputs {
    pub session: String,
    pub roles: Vec<RoleInputs>,
    pub setups: BTreeMap<String, Vec<u8>>,
}
#[derive(Debug)]
pub struct RoleInputs {
    pub role: String,
    pub inputs: Vec<InputValue>,
    pub services: Vec<u64>,
}

/// Decode only the positional transport. Authority, value preparation and
/// issuance remain common with in-process requests.
pub(super) fn decode(host: &RunHost, bytes: &[u8]) -> Result<RunInputs> {
    let value = parse(bytes, INPUT_LIMIT)?;
    let root = array(&value, 4)?;
    if text(&root[0])? != "zkc.bundle-inputs/0" {
        return Err("bundle-input-format".into());
    }
    let session = identifier(&root[1])?.to_owned();
    let rows = list(&root[2])?;
    if rows.len() != host.bundle.roles().len() {
        return Err("bundle-input-roles".into());
    }
    let mut setups = BTreeMap::new();
    for row in list(&root[3])? {
        let row = array(row, 2)?;
        let name = identifier(&row[0])?;
        if !host.authority.keys.contains_key(name) {
            return Err("bundle-setup-authority".into());
        }
        let bytes = host.limits.capacity.wire(&row[1])?;
        if setups.insert(name.to_owned(), bytes).is_some() {
            return Err("bundle-setup-duplicate".into());
        }
    }
    let mut roles = Vec::new();
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
        let mut inputs = Vec::new();
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
            inputs.push(match expected {
                "rng" | "nonce" => InputValue::Resource {
                    budget: budget(&spec[1])?,
                },
                "wire" => InputValue::Wire(host.limits.capacity.wire(&spec[1])?),
                "verifier_key" => {
                    if host
                        .authority
                        .inputs
                        .get(&(role.entry.role.clone(), i))
                        .map(String::as_str)
                        != Some(text(&spec[1])?)
                    {
                        return Err("bundle-setup-input".into());
                    }
                    InputValue::VerifierKey
                }
                "prover_key_file" => {
                    let spec = array(&spec[1], 2)?;
                    InputValue::ProverKeyFile {
                        path: text(&spec[0])?.to_owned(),
                        fingerprint: digest(text(&spec[1])?)?,
                    }
                }
                _ => unreachable!("checked input kind"),
            });
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
        roles.push(RoleInputs {
            role: role.entry.role.clone(),
            inputs,
            services,
        });
    }
    Ok(RunInputs {
        session,
        roles,
        setups,
    })
}

/// Pure declaration checks need authority names, but no imported key material.
fn check_declaration(
    host: &RunHost,
    role: &str,
    index: usize,
    ty: &PhysicalType,
    value: &InputValue,
) -> Result<()> {
    match (kind(ty), value) {
        ("unsupported-transcript", _) => Err("bundle-transcript-input-unsupported".into()),
        ("rng" | "nonce", InputValue::Resource { budget }) => checked_budget(*budget).map(|_| ()),
        (
            "wire",
            value @ (InputValue::Wire(_) | InputValue::Native(_) | InputValue::Variant { .. }),
        ) => crate::host::admission::check_native_data(ty, value, host.limits.capacity),
        ("rng" | "nonce" | "verifier_key" | "prover_key_file", InputValue::Native(_)) => {
            Err("native-input-private".into())
        }
        ("verifier_key", InputValue::VerifierKey)
        | ("prover_key_file", InputValue::ProverKeyFile { .. } | InputValue::ProverKey(_)) => {
            if !host
                .authority
                .inputs
                .contains_key(&(role.to_owned(), index))
            {
                return Err("bundle-setup-input".into());
            }
            Ok(())
        }
        _ => Err("bundle-input-kind".into()),
    }
}

pub(super) fn prepare<'a>(
    host: &'a RunHost,
    request: &RunInputs,
    imports: &mut crate::host::setups::VerifierKeys,
) -> Result<PreparedRun<'a>> {
    let session = &request.session;
    if !valid_identifier(session) {
        return Err("bundle-input-name".into());
    }
    if request.roles.len() != host.bundle.roles().len() {
        return Err("bundle-input-roles".into());
    }
    if request
        .setups
        .keys()
        .any(|name| !host.authority.keys.contains_key(name))
    {
        return Err("bundle-setup-authority".into());
    }
    if !request.setups.keys().eq(host.authority.keys.keys()) {
        return Err("bundle-setup-material".into());
    }
    for (row, role) in request.roles.iter().zip(host.bundle.roles()) {
        if row.role != role.entry.role {
            return Err("bundle-input-roles".into());
        }
        if row.inputs.len() != role.entry.inputs.len()
            || row.services.len() != role.entry.services.len()
        {
            return Err("bundle-input-count".into());
        }
        for budget in &row.services {
            checked_budget(*budget)?;
        }
        for (i, (value, (_, ty))) in row.inputs.iter().zip(&role.entry.inputs).enumerate() {
            check_declaration(host, &row.role, i, ty, value)?;
        }
    }
    let policy = host.limits.capacity.backend();
    let mut admission = Admission::new(host.limits.capacity.loading())?;
    // Charge setup scans before importing even receive-only material.
    for bytes in request.setups.values() {
        host.limits.capacity.check_wire(bytes.len())?;
        admission.work(bytes.len())?;
    }
    imports.check_bounds(policy.ark_bounds())?;
    let mut keys = BTreeMap::new();
    let mut material = BTreeMap::new();
    for (name, bytes) in &request.setups {
        let pin = &host.authority.keys[name];
        let key = imports.import(bytes, *pin, "bundle-canonical-key")?;
        material.entry(bytes).or_insert_with(|| key.clone());
        keys.insert(name.to_owned(), key);
    }
    let setups = SetupRegistry::new(
        material.values().map(|k| k.as_ref().clone()).collect(),
        &policy,
    )
    .map_err(|e| e.to_string())?;
    let mut roles = Vec::new();
    // The authorized registry retains even receive-only keys, independently
    // of whether an entry operand uses them. Charge that material once.
    for key in keys.values() {
        admission.add(Input::Ready(Value::VerifierKey(key.clone())))?;
    }
    for (row, role) in request.roles.iter().zip(host.bundle.roles()) {
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
        let backend = NativeBackend::new(
            policy,
            EntryPolicy::new(
                Domain::new(
                    &role.entry.role,
                    session,
                    host.bundle.entry(),
                    Some(&role.entry.instance),
                ),
                None,
            )
            .with_ports(ports),
            setups.clone(),
        )
        .map_err(|e| e.to_string())?
        .with_ring_assets(host.ring_assets.clone())
        .map_err(|e| e.to_string())?
        .with_ring_work_limit(host.ring_work_limit)
        .with_external_work_limit(host.limits.external_work);
        let mut pending = Vec::new();
        for (i, (value, (_, ty))) in row.inputs.iter().zip(&role.entry.inputs).enumerate() {
            let selected = host
                .authority
                .inputs
                .get(&(role.entry.role.clone(), i))
                .map(|k| &keys[k]);
            let id = match value {
                InputValue::Resource { budget } => {
                    pending.push(admission.resource(ResourceInput {
                        kind: ty.kind(),
                        field: ty.logical().identity(),
                        budget: *budget,
                    })?);
                    continue;
                }
                InputValue::Variant { .. } | InputValue::Wire(_) | InputValue::Native(_) => {
                    admission.native_data(&backend, ty.clone(), value, selected.cloned())?
                }
                InputValue::VerifierKey => {
                    let value = Value::VerifierKey(selected.ok_or("bundle-setup-input")?.clone());
                    if value.physical_type() != *ty {
                        return Err("bundle-input-type".into());
                    }
                    admission.add(Input::Ready(value))?
                }
                InputValue::ProverKey(material) => admission.add(Input::Ready(
                    material.operand(ty, selected.ok_or("bundle-setup-input")?, &backend)?,
                ))?,
                InputValue::ProverKeyFile { path, fingerprint } => admission.add(Input::Key {
                    path,
                    fingerprint: *fingerprint,
                    verifier: selected.ok_or("bundle-setup-input")?.clone(),
                })?,
            };
            pending.push(admission.data(id, ty.kind())?);
        }
        roles.push((role.entry.clone(), backend, pending, row.services.clone()));
    }
    // Charge the entire invocation, not a separate resettable budget per role.
    // Key files are frozen and imported only after every declaration is checked.
    // All roles share this native codec policy and authorized key registry.
    let loaded = admission.load(&roles[0].1, &policy)?;
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
        session: session.to_owned(),
        roles,
        loaded,
    })
}
