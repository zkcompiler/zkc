//! Positional transport and typed requests share preparation before issuance.
use super::*;

const CONTEXT_LIMIT: usize = 4096;
const RESOURCE_BUDGET_LIMIT: u64 = 1_000_000;

/// Values follow the admitted public, role-input and service order. Public
/// verifier keys use canonical wire bytes; other public data may also use native
/// values. Authority comes from the application, never the candidate proof.
#[derive(Debug)]
pub struct ProofInputs {
    pub public: Vec<InputValue>,
    pub inputs: Vec<InputValue>,
    pub context: Vec<u8>,
    pub services: Vec<u64>,
    pub transcript_budget: u64,
}

pub(super) enum Request<'a> {
    Encoded(&'a Json),
    Typed(&'a ProofInputs),
}

pub(super) fn decode(host: &NativeDeployment, input: &Json, producer: bool) -> Result<ProofInputs> {
    logical::tree_size(input).map_err(|e| e.to_string())?;
    let row = array(input, 6)?;
    if text(&row[0])? != "zkc.native-proof-inputs/1" {
        return Err("native-proof-inputs".into());
    }
    if text(&row[3])?.len() > CONTEXT_LIMIT * 2 {
        return Err("native-proof-context-limit".into());
    }
    let role = if producer {
        host.entry.producer()
    } else {
        host.entry.validator()
    };
    let mapping = &host.maps[&role.role];
    let public_rows = list(&row[1])?;
    let data_rows = list(&row[2])?;
    let service_rows = list(&row[4])?;
    if public_rows.len() != host.public.len() {
        return Err("native-proof-public-inputs".into());
    }
    if data_rows.len() != mapping.data.len() {
        return Err("native-proof-role-inputs".into());
    }
    if service_rows.len() != mapping.services.len() {
        return Err("native-proof-service-inputs".into());
    }
    let public = public_rows
        .iter()
        .zip(&host.public)
        .map(|(row, port)| {
            let row = array(row, 3)?;
            if text(&row[0])? != host.entry.validator().role || index(&row[1])? != port.original {
                return Err("native-proof-public-inputs".into());
            }
            Ok(InputValue::Wire(host.capacity.wire(&row[2])?))
        })
        .collect::<Result<Vec<_>>>()?;
    let inputs = data_rows
        .iter()
        .zip(&mapping.data)
        .zip(&role.inputs)
        .map(|((row, port), (_, ty))| {
            let row = array(row, 2)?;
            if index(&row[0])? != port.original {
                return Err("native-proof-role-inputs".into());
            }
            let spec = array(&row[1], 2)?;
            let kind = text(&spec[0])?;
            if kind != input_kind(ty, host.version)? {
                return Err("native-proof-role-input-kind".into());
            }
            Ok(match kind {
                "wire" => InputValue::Wire(host.capacity.wire(&spec[1])?),
                "nonce" | "rng" => InputValue::Resource {
                    budget: budget(&spec[1])?,
                },
                "verifier_key" => {
                    if index(&spec[1])? != port.original {
                        return Err("native-proof-key-port".into());
                    }
                    InputValue::VerifierKey
                }
                "prover_key_file" if producer => {
                    let material = array(&spec[1], 2)?;
                    InputValue::ProverKeyFile {
                        path: text(&material[0])?.to_owned(),
                        fingerprint: unhex(&material[1])?
                            .try_into()
                            .map_err(|_| "native-proof-material-pin")?,
                    }
                }
                _ => return Err("native-proof-role-input-kind".into()),
            })
        })
        .collect::<Result<Vec<_>>>()?;
    let services = service_rows
        .iter()
        .zip(&mapping.services)
        .map(|(row, port)| {
            let row = array(row, 2)?;
            if index(&row[0])? != *port {
                return Err("native-proof-service-inputs".into());
            }
            budget(&row[1])
        })
        .collect::<Result<Vec<_>>>()?;
    Ok(ProofInputs {
        public,
        inputs,
        context: unhex(&row[3])?,
        services,
        transcript_budget: budget(&row[5])?,
    })
}

pub(super) struct Prepared {
    pub backend: NativeBackend,
    pub loaded: Vec<Value>,
    pub planned: Vec<Operand>,
    pub root: Vec<u8>,
    pub binding: [u8; 32],
}
pub(super) fn check_budget(value: u64) -> Result<()> {
    if value > RESOURCE_BUDGET_LIMIT {
        return Err("native-proof-budget".into());
    }
    Ok(())
}

pub(super) fn prepare(
    host: &NativeDeployment,
    request: &ProofInputs,
    role: &EntryRole,
    producer: bool,
) -> Result<Prepared> {
    let mapping = &host.maps[&role.role];
    if request.context.len() > CONTEXT_LIMIT {
        return Err("native-proof-context-limit".into());
    }
    if request.public.len() != host.public.len() {
        return Err("native-proof-public-inputs".into());
    }
    if request.inputs.len() != mapping.data.len() {
        return Err("native-proof-role-inputs".into());
    }
    if request.services.len() != mapping.services.len() {
        return Err("native-proof-service-inputs".into());
    }
    check_budget(request.transcript_budget)?;
    if host.entry.transcript().is_none() && request.transcript_budget != 0 {
        return Err("native-proof-unselected-transcript".into());
    }
    for value in &request.services {
        check_budget(*value)?;
    }
    // Validate declarations before key imports or data loading. Expected types
    // bound compound traversal in shared Admission; foreign capabilities cannot
    // enter through an immutable data constructor.
    for (input, (_, ty)) in request.inputs.iter().zip(&role.inputs) {
        match (input_kind(ty, host.version)?, input) {
            ("wire", input) => crate::host::admission::check_native_data(ty, input, host.capacity)?,
            ("rng" | "nonce", InputValue::Resource { budget }) => check_budget(*budget)?,
            ("verifier_key", InputValue::VerifierKey) => {}
            ("prover_key_file", InputValue::ProverKeyFile { .. }) if producer => {}
            _ => return Err("native-proof-role-input-kind".into()),
        }
    }
    let policy = host.capacity.backend();
    let mut admission = Admission::new(host.capacity.loading());
    for (input, port) in request.public.iter().zip(&host.public) {
        if port.logical.kind() == Type::VerifierKey {
            let InputValue::Wire(bytes) = input else {
                return Err("native-input-private".into());
            };
            host.capacity.check_wire(bytes.len())?;
            admission.work(bytes.len())?;
        } else {
            let ty = PhysicalType::default_for(port.logical.clone()).map_err(|e| e.to_string())?;
            crate::host::admission::check_native_data(&ty, input, host.capacity)?;
        }
    }
    let mut root = json!([
        format!("zkc.native-proof-binding/{}", host.version),
        "sha256",
        host.descriptor[2],
        host.source,
        host.entry.entry(),
        host.entry.producer().role,
        host.entry.validator().role,
        host.descriptor,
        [],
        hex(&request.context),
        [],
        [],
        []
    ]);
    let mut root_size = logical::tree_size(&root).map_err(|e| e.to_string())?;
    if host.entry.transcript().is_some() {
        host.capacity.check_wire(root_size)?;
    }
    // Import only independently pinned public keys. Even receive-only registry
    // material is charged; a proof header cannot extend this registry.
    let mut keys = BTreeMap::new();
    let mut material = BTreeMap::new();
    let mut public_ids = BTreeMap::new();
    for (input, port) in request.public.iter().zip(&host.public) {
        if port.logical.kind() != Type::VerifierKey {
            continue;
        }
        let InputValue::Wire(bytes) = input else {
            unreachable!("checked public key")
        };
        let key = zkc_arkworks::VerifierKey::from_bytes(
            bytes,
            *host
                .setups
                .keys
                .get(&port.original)
                .ok_or("native-proof-key-authority")?,
            &policy.ark_bounds(),
        )
        .map_err(|e| e.to_string())?;
        if key
            .to_bytes(&policy.ark_bounds())
            .map_err(|e| e.to_string())?
            != *bytes
        {
            return Err("native-proof-canonical-key".into());
        }
        let key = std::sync::Arc::new(key);
        let id = admission.add(Input::Ready(Value::VerifierKey(key.clone())), &policy)?;
        public_ids.insert(port.original, id);
        material.entry(bytes).or_insert_with(|| key.clone());
        keys.insert(port.original, key);
    }
    let registry = zkc_backends::SetupRegistry::new(
        material.values().map(|k| k.as_ref().clone()).collect(),
        &policy,
    )
    .map_err(|e| e.to_string())?;
    let mut constraints = BTreeMap::new();
    for (port, (name, _)) in mapping.data.iter().zip(&role.inputs) {
        let key = if port.logical.kind() == Type::VerifierKey {
            keys.get(&port.original)
        } else if matches!(
            port.logical.kind(),
            Type::ProverKey | Type::Commitment | Type::Proof
        ) {
            host.setups
                .inputs
                .get(&port.original)
                .and_then(|key| keys.get(key))
        } else {
            None
        };
        if let Some(key) = key {
            constraints.insert(
                name.clone(),
                zkc_backends::PortConstraint {
                    arity: None,
                    setup: Some(key.metadata()),
                },
            );
        }
    }
    let backend = backend(policy, role, host.entry.entry(), registry, constraints)?
        .with_external_work_limit(host.external_work_limit);
    let selected = |original| {
        host.setups
            .inputs
            .get(&original)
            .map(|key| keys[key].clone())
    };
    let public_requests: BTreeMap<_, _> = host
        .public
        .iter()
        .zip(&request.public)
        .map(|(port, input)| (port.original, input))
        .collect();
    for (input, port) in request.public.iter().zip(&host.public) {
        if port.logical.kind() == Type::VerifierKey {
            continue;
        }
        let ty = PhysicalType::default_for(port.logical.clone()).map_err(|e| e.to_string())?;
        let id = admission.native_data(&backend, ty, input, selected(port.original))?;
        if !matches!(input, InputValue::Wire(_)) {
            admission.charge_encoding(id)?;
        }
        public_ids.insert(port.original, id);
    }
    let mut planned = Vec::new();
    let mut shared = Vec::new();
    for ((input, port), (_, ty)) in request.inputs.iter().zip(&mapping.data).zip(&role.inputs) {
        let id = match input {
            InputValue::Resource { budget } => {
                planned.push(admission.resource(ResourceInput {
                    kind: ty.kind(),
                    field: ty.logical().identity(),
                    budget: *budget,
                })?);
                continue;
            }
            InputValue::VerifierKey => *public_ids
                .get(&port.original)
                .ok_or("native-proof-key-port")?,
            InputValue::ProverKeyFile { path, fingerprint } => admission.add(
                Input::Key {
                    path,
                    fingerprint: *fingerprint,
                    verifier: selected(port.original).ok_or("native-proof-setup-required")?,
                },
                &policy,
            )?,
            input => {
                // Preserve the wire adapter's exact-byte agreement and reuse.
                let same = match (public_requests.get(&port.original), input) {
                    (Some(InputValue::Wire(a)), InputValue::Wire(b)) => {
                        if a != b {
                            return Err("native-proof-shared-public-input".into());
                        }
                        PhysicalType::default_for(port.logical.clone())
                            .ok()
                            .as_ref()
                            == Some(ty)
                    }
                    _ => false,
                };
                let id = if same {
                    public_ids[&port.original]
                } else {
                    admission.native_data(&backend, ty.clone(), input, selected(port.original))?
                };
                if public_requests.contains_key(&port.original) && !same {
                    if !matches!(input, InputValue::Wire(_)) {
                        admission.charge_encoding(id)?;
                    }
                    shared.push((port.original, id, input));
                }
                id
            }
        };
        planned.push(admission.data(id, ty.kind())?);
    }
    if let Some(ty) = host.entry.transcript() {
        admission.resource(ResourceInput {
            kind: Type::Transcript,
            field: ty.logical().identity(),
            budget: request.transcript_budget,
        })?;
    }
    let loaded = admission.load_cached(&backend, &policy, &mut MaterialCache::disabled())?;
    let mut values = entry_values(&planned, &loaded);
    if host.entry.transcript().is_some() {
        values.push(None);
    }
    backend
        .check_entry_values(role, &values)
        .map_err(|e| e.to_string())?;
    // Only public data needs canonical serialization. Private native inputs stay
    // in process. Wire inputs have already passed the canonical codec loader.
    let mut public_bytes = BTreeMap::new();
    for (port, input) in host.public.iter().zip(&request.public) {
        let bytes = canonical(&backend, &loaded[public_ids[&port.original]], input)?;
        host.capacity.check_wire(bytes.len())?;
        let mut row = json!([
            host.entry.validator().role,
            port.original.to_string(),
            port.logical.spelling(),
            ""
        ]);
        // Bound cumulative hex expansion before allocating binding strings. Typed
        // requests have not passed through the positional JSON tree's byte cap.
        root_size = bytes
            .len()
            .checked_mul(2)
            .and_then(|n| n.checked_add(logical::tree_size(&row).ok()?))
            .and_then(|n| n.checked_add(root_size))
            .filter(|n| *n <= logical::TreeLimits::BYTES)
            .ok_or("tree-limit")?;
        row[3] = json!(hex(&bytes));
        root[8]
            .as_array_mut()
            .expect("binding public rows")
            .push(row);
        public_bytes.insert(port.original, bytes);
    }
    for (original, id, input) in shared {
        if canonical(&backend, &loaded[id], input)? != public_bytes[&original] {
            return Err("native-proof-shared-public-input".into());
        }
    }
    let root = logical::encode_tree(&root).map_err(|e| e.to_string())?;
    if host.entry.transcript().is_some()
        && (root.len() > policy.max_wire_bytes || root.len() > isize::MAX as usize)
    {
        return Err("native-capacity-wire".into());
    }
    let binding = Sha256::digest(&root).into();
    Ok(Prepared {
        backend,
        loaded,
        planned,
        root,
        binding,
    })
}

fn canonical<'a>(
    backend: &NativeBackend,
    value: &Value,
    input: &'a InputValue,
) -> Result<std::borrow::Cow<'a, [u8]>> {
    Ok(match input {
        InputValue::Wire(bytes) => std::borrow::Cow::Borrowed(bytes.as_slice()),
        _ => std::borrow::Cow::Owned(
            backend
                .encode_native_value(value)
                .map_err(|e| e.to_string())?,
        ),
    })
}
