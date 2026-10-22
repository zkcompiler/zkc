//! Positional transport and typed requests share preparation before issuance.
use super::*;

const CONTEXT_LIMIT: usize = 4096;
use crate::host::inputs::RESOURCE_BUDGET_LIMIT;

/// Values follow the admitted public, role-input and service order. Public
/// verifier keys use canonical wire bytes; other public data may also use native
/// values. Authority comes from the application, never the candidate proof.
#[derive(Debug)]
pub struct ProofInputs {
    pub public: Vec<InputValue>,
    pub inputs: Vec<InputValue>,
    /// Host invocation context. Native framing checks it in the header and
    /// managed transcripts bind it in their root. RawBytes with local/authored
    /// state uses it only for the invocation report; protocol-visible context
    /// must be a declared public data input.
    pub context: Vec<u8>,
    pub services: Vec<u64>,
    pub transcript_budget: u64,
}

impl ProofInputs {
    /// Decode the positional transport for a selected invocation. Execution still
    /// validates typed values and prepares all resources before issuing them.
    pub fn decode(
        host: &NativeDeployment,
        input: &Json,
        invocation: Invocation<'_>,
    ) -> Result<Self> {
        // Decode against the selected policy before interpreting positional data.
        // Execution rechecks caller-owned policy and inputs before preparation.
        invocation.plan(host)?;
        let producer = invocation.is_producer();
        logical::tree_size(input).map_err(|e| e.to_string())?;
        let row = array(input, 6)?;
        if text(&row[0])? != "zkc.native-proof-inputs/0" {
            return Err("native-proof-inputs".into());
        }
        if text(&row[3])?.len() > CONTEXT_LIMIT * 2 {
            return Err("native-proof-context-limit".into());
        }
        let role = host.selected_role(producer)?;
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
                if text(&row[0])? != host.entry.validator_role() || index(&row[1])? != port.original
                {
                    return Err("native-proof-public-inputs".into());
                }
                Ok(InputValue::Wire(host.capacity.wire(&row[2])?.into()))
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
                if kind != input_kind(ty)? {
                    return Err("native-proof-role-input-kind".into());
                }
                Ok(match kind {
                    "wire" => InputValue::Wire(host.capacity.wire(&spec[1])?.into()),
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
}

pub(super) struct Prepared {
    pub backend: NativeBackend,
    pub loaded: Vec<Value>,
    pub planned: Vec<Operand>,
    pub root: Vec<u8>,
    pub binding: [u8; 32],
    pub loading: Option<zkc_runtime::vm::LiveReservation>,
    pub encoding: Vec<zkc_runtime::vm::LiveReservation>,
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
    imports: &mut crate::host::setups::VerifierKeys,
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
        if host.retained_inputs
            && !zkc_native::has_native_wire(ty)
            && ty.is_duplicable()
            && !matches!(ty.kind(), Type::ProverKey | Type::VerifierKey)
        {
            crate::host::admission::check_retained_data(ty, input, host.capacity)?;
            continue;
        }
        match (input_kind(ty)?, input) {
            ("wire", input) => crate::host::admission::check_native_data(ty, input, host.capacity)?,
            ("rng" | "nonce", InputValue::Resource { budget }) => check_budget(*budget)?,
            ("verifier_key", InputValue::VerifierKey) => {}
            (
                "prover_key_file",
                InputValue::ProverKeyFile { .. }
                | InputValue::ProverKeyInput { .. }
                | InputValue::ProverKey(_),
            ) if producer => {}
            _ => return Err("native-proof-role-input-kind".into()),
        }
    }
    let policy = host.capacity.backend();
    let mut admission = Admission::new(host.capacity.loading())?
        .with_shared_ledger(host.shared_ledger.clone())
        .with_retained_inputs(host.retained_inputs);
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
    let _root_tree = crate::host::shared::allocation(
        host.shared_ledger.as_ref(),
        host.binding_metadata_bytes
            .saturating_add(request.context.len() * 2),
    )?;
    let root = json!([
        "zkc.native-proof-binding/0",
        "sha256",
        host.descriptor[2],
        host.source,
        host.entry.entry(),
        host.entry.producer_role(),
        host.entry.validator_role(),
        host.descriptor,
        [],
        hex(&request.context)
    ]);
    let mut root_size = logical::tree_size(&root).map_err(|e| e.to_string())?;
    if host.entry.transcript().is_some() {
        host.capacity.check_wire(root_size)?;
    }
    // Import only independently pinned public keys. Even receive-only registry
    // material is charged; a proof header cannot extend this registry.
    imports.check_bounds(policy.ark_bounds())?;
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
        let pin = *host
            .setups
            .keys
            .get(&port.original)
            .ok_or("native-proof-key-authority")?;
        let key = imports.import(bytes, pin, "native-proof-canonical-key")?;
        let id = admission.add(Input::Ready(Value::VerifierKey(key.clone())))?;
        public_ids.insert(port.original, id);
        material
            .entry(bytes.as_slice())
            .or_insert_with(|| key.clone());
        keys.insert(port.original, key);
    }
    let registry = zkc_native::SetupRegistry::new(
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
                zkc_native::PortConstraint {
                    arity: None,
                    setup: Some(key.metadata()),
                },
            );
        }
    }
    let backend = backend(policy, role, host.entry.entry(), registry, constraints)?
        .with_ring_assets(host.ring_assets.clone())
        .map_err(|e| e.to_string())?
        .with_relation_assets(host.relation_assets.clone())
        .map_err(|e| e.to_string())?
        .with_ring_work_limit(host.ring_work_limit)
        .with_external_work_limit(host.external_work_limit)
        .with_sequence_work_limit(host.sequence_work_limit);
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
        if input.wire_bytes().is_none() {
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
            InputValue::ProverKey(material) => admission.add(Input::Ready(
                material.operand(
                    ty,
                    selected(port.original)
                        .as_deref()
                        .ok_or("native-proof-setup-required")?,
                    &backend,
                )?,
            ))?,
            InputValue::ProverKeyInput { file, fingerprint } => admission.add(Input::Key {
                source: crate::host::admission::KeySource::File(file),
                fingerprint: *fingerprint,
                verifier: selected(port.original).ok_or("native-proof-setup-required")?,
            })?,
            InputValue::ProverKeyFile { path, fingerprint } => admission.add(Input::Key {
                source: crate::host::admission::KeySource::Path(path),
                fingerprint: *fingerprint,
                verifier: selected(port.original).ok_or("native-proof-setup-required")?,
            })?,
            input => {
                // Reuse only identical bytes or the same pinned open descriptor.
                let same_source = match (public_requests.get(&port.original), input) {
                    (Some(a), b) if a.wire_bytes().is_some() && b.wire_bytes().is_some() => {
                        let (a, b) = (a.wire_bytes().unwrap(), b.wire_bytes().unwrap());
                        if a != b {
                            return Err("native-proof-shared-public-input".into());
                        }
                        true
                    }
                    (
                        Some(InputValue::WireFile {
                            file: a,
                            sha256: a_pin,
                        }),
                        InputValue::WireFile {
                            file: b,
                            sha256: b_pin,
                        },
                    ) => a.same_source(b) && a_pin == b_pin,
                    _ => false,
                };
                let same = same_source
                    && PhysicalType::default_for(port.logical.clone())
                        .ok()
                        .as_ref()
                        == Some(ty);
                let id = if same {
                    public_ids[&port.original]
                } else {
                    admission.native_data(&backend, ty.clone(), input, selected(port.original))?
                };
                if public_requests.contains_key(&port.original) && !same {
                    if input.wire_bytes().is_none() {
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
    let (loaded, loading) = if let Some(ledger) = &host.shared_ledger {
        let (values, guard) = admission.load_shared(&backend, &policy, ledger, 0)?;
        (values, Some(guard))
    } else {
        (admission.load(&backend, &policy)?, None)
    };
    let mut values = entry_values(&planned, &loaded);
    if host.entry.transcript().is_some() {
        values.push(None);
    }
    // This stage validates caller inputs. The internal proof buffer is acquired
    // separately and checked with the full role signature when the Runner starts.
    let mut input_role = role.clone();
    if host.entry.has_record_codec() && !producer {
        input_role.inputs.pop();
    }
    backend
        .check_entry_values(&input_role, &values)
        .map_err(|e| e.to_string())?;
    // Only public data needs canonical serialization. Private native inputs stay
    // in process. Wire inputs have already passed the canonical codec loader.
    let mut public_bytes = BTreeMap::new();
    let mut encoding_retained = Vec::new();
    for (port, input) in host.public.iter().zip(&request.public) {
        if input.wire_bytes().is_none() {
            encoding_retained.extend(crate::host::shared::allocation(
                host.shared_ledger.as_ref(),
                crate::host::shared::wire_bound(&loaded[public_ids[&port.original]]),
            )?);
        }
        let bytes = canonical(&backend, &loaded[public_ids[&port.original]], input)?;
        host.capacity.check_wire(bytes.len())?;
        // Account for the complete row before retaining its canonical bytes.
        // Hex is a borrowed logical string; it never allocates an intermediate.
        let original = port.original.to_string();
        let spelling = port.logical.spelling();
        let row = [
            logical::Tree::Text(host.entry.validator_role()),
            logical::Tree::Text(&original),
            logical::Tree::Text(&spelling),
            logical::Tree::Hex(&bytes),
        ];
        root_size = logical::Tree::Array(&row)
            .prepare()
            .ok()
            .and_then(|row| root_size.checked_add(row.size()))
            .filter(|n| *n <= logical::TreeLimits::BYTES)
            .ok_or("tree-limit")?;
        public_bytes.insert(port.original, bytes);
    }
    for (original, id, input) in shared {
        let _live = if input.wire_bytes().is_none() {
            crate::host::shared::allocation(
                host.shared_ledger.as_ref(),
                crate::host::shared::wire_bound(&loaded[id]),
            )?
        } else {
            None
        };
        if canonical(&backend, &loaded[id], input)? != public_bytes[&original] {
            return Err("native-proof-shared-public-input".into());
        }
    }
    let labels: Vec<_> = host
        .public
        .iter()
        .map(|port| (port.original.to_string(), port.logical.spelling()))
        .collect();
    let rows: Vec<_> = host
        .public
        .iter()
        .zip(&labels)
        .map(|(port, (index, ty))| {
            [
                logical::Tree::Text(host.entry.validator_role()),
                logical::Tree::Text(index),
                logical::Tree::Text(ty),
                logical::Tree::Hex(&public_bytes[&port.original]),
            ]
        })
        .collect();
    let rows: Vec<_> = rows.iter().map(|row| logical::Tree::Array(row)).collect();
    let mut fields: Vec<_> = root
        .as_array()
        .expect("binding root")
        .iter()
        .map(logical::Tree::Json)
        .collect();
    fields[8] = logical::Tree::Array(&rows);
    let encoding = logical::Tree::Array(&fields)
        .prepare()
        .map_err(|e| e.to_string())?;
    let retain_root = host.entry.transcript().is_some();
    if retain_root {
        host.capacity.check_wire(encoding.size())?;
    }
    encoding_retained.extend(crate::host::shared::allocation(
        host.shared_ledger.as_ref(),
        if retain_root { encoding.size() } else { 0 },
    )?);
    if let Some(ledger) = &host.shared_ledger {
        ledger
            .charge(
                zkc_runtime::vm::WorkBudget {
                    instructions: 0,
                    iterations: 0,
                    logical_bytes: encoding.size() as u64,
                },
                0,
            )
            .map_err(|e| e.to_string())?;
    }
    let (root, binding) = encode_binding(&encoding, retain_root)?;
    Ok(Prepared {
        backend,
        loaded,
        planned,
        root,
        binding,
        loading,
        encoding: encoding_retained,
    })
}

fn canonical<'a>(
    backend: &NativeBackend,
    value: &Value,
    input: &'a InputValue,
) -> Result<std::borrow::Cow<'a, [u8]>> {
    Ok(match input.wire_bytes() {
        Some(bytes) => std::borrow::Cow::Borrowed(bytes),
        None => std::borrow::Cow::Owned(
            backend
                .encode_native_value(value)
                .map_err(|e| e.to_string())?,
        ),
    })
}

// A digest and optional transcript buffer consume one canonical stream. The
// buffer is reserved before writing and is unpublished until encoding finishes.
fn encode_binding(encoding: &logical::Encoding<'_>, retain: bool) -> Result<(Vec<u8>, [u8; 32])> {
    struct Sink {
        bytes: Vec<u8>,
        hash: Sha256,
        retain: bool,
    }
    impl std::io::Write for Sink {
        fn write(&mut self, bytes: &[u8]) -> std::io::Result<usize> {
            self.hash.update(bytes);
            if self.retain {
                self.bytes.extend_from_slice(bytes);
            }
            Ok(bytes.len())
        }
        fn flush(&mut self) -> std::io::Result<()> {
            Ok(())
        }
    }
    let mut sink = Sink {
        bytes: Vec::new(),
        hash: Sha256::new(),
        retain,
    };
    if retain {
        sink.bytes
            .try_reserve_exact(encoding.size())
            .map_err(|_| "tree-allocation")?;
    }
    encoding.write(&mut sink).expect("reserved binding sink");
    Ok((sink.bytes, sink.hash.finalize().into()))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn retained_and_hash_only_bindings_match_the_independent_vector() {
        let vector: Json = serde_json::from_str(include_str!(
            "../../../zkc-test-support/fixtures/native-proof-binding.json"
        ))
        .unwrap();
        let expected = unhex(&vector["encoded_hex"]).unwrap();
        let encoding = logical::Tree::Json(&vector["tree"]).prepare().unwrap();
        for retain in [true, false] {
            let (bytes, digest) = encode_binding(&encoding, retain).unwrap();
            assert_eq!(hex(&digest), vector["sha256"]);
            assert_eq!(bytes, if retain { expected.as_slice() } else { &[] });
        }
        // Exercise the mixed public-row composition too. The JSON spelling
        // takes the Text path; the borrowed row must expand Hex identically.
        for n in [0, 1, 511, 512, 513, 1024] {
            let wire: Vec<_> = (0..n).map(|i| i as u8).collect();
            let mut tree = vector["tree"].clone();
            tree[8] = json!([["V", "0", "bytes", hex(&wire)]]);
            let expected = logical::encode_tree(&tree).unwrap();
            let row = [
                logical::Tree::Text("V"),
                logical::Tree::Text("0"),
                logical::Tree::Text("bytes"),
                logical::Tree::Hex(&wire),
            ];
            let rows = [logical::Tree::Array(&row)];
            let mut fields: Vec<_> = tree
                .as_array()
                .unwrap()
                .iter()
                .map(logical::Tree::Json)
                .collect();
            fields[8] = logical::Tree::Array(&rows);
            let encoding = logical::Tree::Array(&fields).prepare().unwrap();
            assert_eq!(encoding.size(), expected.len());
            for retain in [true, false] {
                let (bytes, digest) = encode_binding(&encoding, retain).unwrap();
                assert_eq!(digest, <[u8; 32]>::from(Sha256::digest(&expected)));
                assert_eq!(bytes, if retain { expected.as_slice() } else { &[] });
            }
        }
    }
}
