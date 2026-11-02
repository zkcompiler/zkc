use super::super::deployment::{check_interface, ordinary};
use super::*;
use crate::entry::interface::InputPort;
pub(super) fn check(
    d: &carrier::Deployment,
    native: &DeploymentKind,
    families: &mut BTreeMap<String, String>,
) -> Result<()> {
    let interface = match native {
        DeploymentKind::Run(n) => n.interface(),
        DeploymentKind::Proof { entry: n, .. } => n.interface(),
    };
    check_interface(d, interface, families)
}
fn named<'a>(
    interface: &crate::entry::Interface,
    ports: impl Iterator<Item = InputPort<'a>>,
    value: &TypedValue,
) -> NamedValues {
    ports
        .filter(|p| ordinary(interface, *p))
        .zip(value.fields())
        .map(|(p, v)| (p.name.clone(), v.to_value()))
        .collect()
}

fn extras<'a>(
    interface: &crate::entry::Interface,
    ports: impl Iterator<Item = InputPort<'a>>,
    extra: &NamedValues,
    mut data: NamedValues,
) -> Result<NamedValues> {
    let allowed = ports
        .filter(|p| !ordinary(interface, *p))
        .map(|p| p.name.clone())
        .collect::<std::collections::BTreeSet<_>>();
    for (name, value) in extra {
        if !allowed.contains(name) || data.contains_key(name) {
            return Err(EntryCondition::InputNames.into());
        }
        data.insert(name.clone(), data::duplicate(value));
    }
    Ok(data)
}
pub(super) fn run_request(
    entry: &crate::entry::RunEntry,
    value: &TypedValue,
    context: &RunContext,
) -> Result<crate::entry::RunRequest> {
    let interface = entry.interface();
    if !context
        .roles
        .keys()
        .all(|n| interface.roles().iter().any(|r| r.name == *n))
    {
        return Err(EntryCondition::InputRoles.into());
    }
    let mut roles = BTreeMap::new();
    for (role, source) in interface.roles().iter().zip(value.fields()) {
        let context = context.roles.get(&role.name);
        let empty = crate::entry::RoleInputs::default();
        let context = context.unwrap_or(&empty);
        roles.insert(
            role.name.clone(),
            crate::entry::RoleInputs {
                inputs: extras(
                    interface,
                    interface.input_ports(role),
                    &context.inputs,
                    named(interface, interface.input_ports(role), source),
                )?,
                services: context.services.clone(),
            },
        );
    }
    Ok(crate::entry::RunRequest {
        session: context
            .session_for_call()
            .map_err(|e| EntryError::new(EntryPhase::Preparation, e))?,
        roles,
        setups: context.setups.clone(),
    })
}
pub(super) fn proof_request(
    entry: &crate::entry::ProofEntry,
    producer: bool,
    values: &[TypedValue],
    context: &ProofContext,
) -> Result<crate::entry::ProofRequest> {
    let interface = entry.interface();
    let proof = interface.proof().expect("admitted proof");
    let role = &interface.roles()[if producer {
        proof.prover
    } else {
        proof.verifier
    }];
    let private = if producer {
        named(interface, interface.named_inputs(role), &values[1])
    } else {
        BTreeMap::new()
    };
    let public_extras = context
        .private
        .inputs
        .iter()
        .filter(|(n, _)| {
            interface
                .input_ports(role)
                .any(|p| p.public && p.name.as_str() == n.as_str())
        })
        .map(|(n, v)| (n.clone(), data::duplicate(v)))
        .collect();
    let private_extras = context
        .private
        .inputs
        .iter()
        .filter(|(n, _)| {
            interface
                .named_inputs(role)
                .any(|p| p.name.as_str() == n.as_str())
        })
        .map(|(n, v)| (n.clone(), data::duplicate(v)))
        .collect();
    Ok(crate::entry::ProofRequest {
        public: extras(
            interface,
            interface.public_ports(),
            &public_extras,
            named(interface, interface.public_ports(), &values[0]),
        )?,
        private: crate::entry::RoleInputs {
            inputs: extras(
                interface,
                interface.named_inputs(role),
                &private_extras,
                private,
            )?,
            services: context.private.services.clone(),
        },
        context: context.context.clone(),
        transcript_budget: context.transcript_budget,
        setups: context.setups.clone(),
    })
}
pub(super) fn proof_bytes(value: &TypedValue) -> Result<&[u8]> {
    let zkc_cpu::Value::Bytes(bytes) = value.fields()[0]
        .native()
        .map_err(|e| EntryError::new(EntryPhase::Request, e))?
    else {
        return Err(error("entry-host-proof-shape"));
    };
    Ok(bytes)
}

// Successful native owners supply these values; source constructors cannot.
pub(super) fn run_value(schema: &Schema, outputs: crate::entry::RoleValues) -> crate::entry::Value {
    let mut outputs = outputs;
    crate::entry::Value::Record(
        schema
            .fields
            .iter()
            .map(|f| {
                (
                    f.name.clone(),
                    crate::entry::Value::Record(outputs.remove(&f.name).expect("checked role")),
                )
            })
            .collect(),
    )
}
pub(super) fn prove_value(outputs: NamedValues, bytes: Vec<u8>) -> crate::entry::Value {
    crate::entry::Value::Record(BTreeMap::from([
        (
            "proof".into(),
            crate::entry::Value::Record(BTreeMap::from([(
                "bytes".into(),
                zkc_cpu::Value::Bytes(bytes.into()).into(),
            )])),
        ),
        ("outputs".into(), crate::entry::Value::Record(outputs)),
    ]))
}
pub(super) fn verify_value(outputs: Option<NamedValues>) -> crate::entry::Value {
    crate::entry::Value::Variant {
        alternative: if outputs.is_some() {
            "Accepted"
        } else {
            "Rejected"
        }
        .into(),
        fields: outputs
            .map(|o| BTreeMap::from([("outputs".into(), crate::entry::Value::Record(o))]))
            .unwrap_or_default(),
    }
}
/// Validate every deployment's context, including dormant ones, before any
/// call. Material is charged to the invocation ledger once, when a reached
/// child loads it; this check has its own allowance with the same capacity,
/// discarded when it returns.
/// Validate every deployment's context, including deployments the call never
/// reaches. The validation decodes and imports real material, so it charges
/// the invocation root; a reached child's later loading is a second real
/// allocation and charges it again.
pub(super) fn context_check(
    host: &EntryHost,
    context: &InvocationContext,
    ledger: &zkc_runtime::vm::ExecutionLedger,
) -> Result<()> {
    /// Request-shape refusals precede the draw-allowance check, exactly as a
    /// standalone run or proof orders them.
    fn check_role(
        interface: &crate::entry::Interface,
        role: &crate::entry::interface::RolePorts,
        context: Option<&crate::entry::RoleInputs>,
    ) -> Result<()> {
        let empty = crate::entry::RoleInputs::default();
        let context = context.unwrap_or(&empty);
        let services =
            crate::entry::arguments::services(interface.services(role), context.services.clone())
                .map_err(|e| EntryError::at(EntryPhase::Request, e))?;
        let allowed = interface.context_ports(role).collect::<Vec<_>>();
        if context.inputs.len() != allowed.len()
            || !allowed.iter().all(|p| context.inputs.contains_key(&p.name))
        {
            return Err(EntryCondition::InputNames.into());
        }
        for p in allowed {
            let value = &context.inputs[&p.name];
            if p.key == Some("prover_key") {
                if !matches!(
                    value,
                    crate::entry::Value::Leaf(
                        crate::execution::InputValue::ProverKey(_)
                            | crate::execution::InputValue::ProverKeyFile { .. }
                            | crate::execution::InputValue::ProverKeyInput { .. }
                    )
                ) {
                    return Err(EntryCondition::InputKey.into());
                }
            } else {
                crate::entry::value::flatten(&p.schema, data::duplicate(value), &mut Vec::new())
                    .map_err(|e| EntryError::at(EntryPhase::Request, e))?;
            }
        }
        crate::entry::arguments::check_draw_budgets(services)
    }
    if context.deployments.len() != host.deployments.len() {
        return Err(EntryError::new(EntryPhase::Request, "entry-host-context"));
    }
    let mut imports = crate::host::setups::VerifierKeys::new(
        host.options.limits.capacity.backend().ark_bounds(),
        host.options.limits.installation.clone(),
    );
    imports.set_ledger(Some(ledger.clone()));
    for (id, deployment) in &host.deployments {
        let value = context
            .deployments
            .get(id)
            .ok_or_else(|| EntryError::new(EntryPhase::Request, "entry-host-context"))?;
        let (interface, material) = match (&deployment.kind, value) {
            (DeploymentKind::Run(entry), InvocationBinding::Run(v)) => {
                let interface = entry.interface();
                if !v
                    .roles
                    .keys()
                    .all(|n| interface.roles().iter().any(|r| r.name == *n))
                {
                    return Err(EntryCondition::InputRoles.into());
                }
                for role in interface.roles() {
                    check_role(interface, role, v.roles.get(&role.name))?;
                }
                if let Some(session) = &v.session {
                    crate::run::RunHost::check_session(session)
                        .map_err(|e| EntryError::at(EntryPhase::Preparation, e))?;
                }
                (interface, &v.setups)
            }
            (DeploymentKind::Proof { entry, operation }, InvocationBinding::Proof(v)) => {
                let interface = entry.interface();
                let proof = interface.proof().expect("admitted proof");
                let producing = *operation == crate::entry::ProofOperation::Prove;
                check_role(
                    interface,
                    &interface.roles()[if producing {
                        proof.prover
                    } else {
                        proof.verifier
                    }],
                    Some(&v.private),
                )?;
                let preparation = |ok: bool, code: &str| {
                    if ok {
                        Ok(())
                    } else {
                        Err(EntryError::new(EntryPhase::Preparation, code))
                    }
                };
                preparation(
                    v.context.len() <= crate::proof::MAX_CONTEXT_BYTES,
                    "native-proof-context-limit",
                )?;
                if let Some(budget) = v.transcript_budget {
                    crate::entry::arguments::check_draw_budgets([budget])?;
                    preparation(
                        entry.binding_scope() == crate::entry::BindingScope::Transcript
                            || budget == 0,
                        "native-proof-unselected-transcript",
                    )?;
                }
                (interface, &v.setups)
            }
            _ => {
                return Err(EntryError::new(
                    EntryPhase::Request,
                    "entry-host-context-operation",
                ));
            }
        };
        let keys = host
            .cpu
            .enter(|| {
                crate::entry::setups::check_pinned_material(
                    interface,
                    &deployment.authority,
                    material,
                    host.options.limits.capacity,
                    &mut imports,
                    &host.options.limits.installation,
                )
            })
            .map_err(|e| EntryError::new(EntryPhase::Preparation, e))?;
        match (&deployment.kind, value) {
            (DeploymentKind::Run(_), InvocationBinding::Run(v)) => {
                for role in interface.roles() {
                    if let Some(context) = v.roles.get(&role.name) {
                        check_context_data(
                            interface,
                            role,
                            context,
                            &keys,
                            host.options.limits.capacity,
                            ledger,
                            host.cpu.clone(),
                            host.options.limits.installation.clone(),
                        )
                        .map_err(|e| EntryError::new(EntryPhase::Preparation, e))?;
                    }
                }
            }
            (DeploymentKind::Proof { operation, .. }, InvocationBinding::Proof(v)) => {
                let proof = interface.proof().expect("checked proof");
                let producing = *operation == crate::entry::ProofOperation::Prove;
                check_context_data(
                    interface,
                    &interface.roles()[if producing {
                        proof.prover
                    } else {
                        proof.verifier
                    }],
                    &v.private,
                    &keys,
                    host.options.limits.capacity,
                    ledger,
                    host.cpu.clone(),
                    host.options.limits.installation.clone(),
                )
                .map_err(|e| EntryError::new(EntryPhase::Preparation, e))?;
            }
            _ => unreachable!("checked invocation binding"),
        }
    }
    Ok(())
}

pub(super) fn context_bytes(context: &InvocationContext) -> usize {
    fn role(context: &crate::entry::RoleInputs) -> usize {
        context
            .inputs
            .iter()
            .map(|(n, v)| n.len() + data::description_bytes(v))
            .sum::<usize>()
            + context.services.len() * 512
    }
    context
        .deployments
        .iter()
        .map(|(id, binding)| {
            let (metadata, material) = match binding {
                InvocationBinding::Run(v) => (
                    v.session.as_ref().map_or(0, String::len)
                        + v.roles.values().map(role).sum::<usize>(),
                    &v.setups,
                ),
                InvocationBinding::Proof(v) => (v.context.len() + role(&v.private), &v.setups),
            };
            id.len()
                + metadata
                + material
                    .iter()
                    .map(|(n, b)| n.len() + b.len())
                    .sum::<usize>()
                + 512
        })
        .sum()
}

/// Authenticate context material independently of unavailable source arguments.
/// This validates declarations and immutable data without issuing resources or
/// asking a child to execute with invented public/witness values.
#[allow(clippy::too_many_arguments)]
fn check_context_data(
    interface: &crate::entry::Interface,
    role: &crate::entry::interface::RolePorts,
    context: &crate::entry::RoleInputs,
    keys: &BTreeMap<String, std::sync::Arc<zkc_kernels::arkworks::bls12_381::VerifierKey>>,
    capacity: crate::execution::Capacity,
    ledger: &zkc_runtime::vm::ExecutionLedger,
    cpu: CpuExecution,
    installation: zkc_cpu::CpuInstallation,
) -> std::result::Result<(), String> {
    use crate::execution::InputValue;
    use crate::host::admission::{Admission, Input, KeySource};
    use zkc_runtime::vm::PhysicalType;
    let registry = zkc_cpu::SetupRegistry::new(
        keys.values().map(|k| k.as_ref().clone()).collect(),
        &capacity.backend(),
    )
    .map_err(|e| e.to_string())?;
    let backend = zkc_cpu::CpuBackend::new_with_installation(
        capacity.backend(),
        zkc_cpu::EntryPolicy::new(
            zkc_cpu::Domain::new(
                &role.native_name,
                "entry-context",
                interface.selected_protocol().symbol.as_str(),
                None,
            ),
            None,
        ),
        registry,
        cpu.clone(),
        installation,
    )
    .map_err(|e| e.to_string())?;
    let ports = interface.context_ports(role).collect::<Vec<_>>();
    let descriptions = ports
        .iter()
        .map(|p| {
            let value = data::duplicate(&context.inputs[&p.name]);
            let mut leaves = Vec::new();
            if p.key == Some("prover_key") {
                let crate::entry::Value::Leaf(value) = value else {
                    return Err("entry-input-key".to_owned());
                };
                leaves.push(value);
            } else {
                crate::entry::value::flatten(&p.schema, value, &mut leaves)?;
            }
            Ok(leaves)
        })
        .collect::<std::result::Result<Vec<_>, String>>()?;
    let mut admission =
        Admission::new(capacity.loading())?.with_shared_ledger(Some(ledger.clone()));
    for (port, inputs) in ports.iter().zip(&descriptions) {
        for ((original, spelling), input) in port.native.iter().zip(&port.schema.leaves).zip(inputs)
        {
            let ty = PhysicalType::default_for(
                zkc_runtime::vm::LogicalType::parse(spelling).map_err(|e| e.to_string())?,
            )
            .map_err(|e| e.to_string())?;
            let selected = interface
                .setups
                .iter()
                .find(|s| s.inputs.contains(&(*original as usize)))
                .map(|s| keys[&s.name].clone());
            let id = match input {
                InputValue::ProverKey(material) => {
                    admission.add(Input::ready(material.operand(
                        &ty,
                        selected.as_deref().ok_or("entry-setup-material")?,
                        &backend,
                    )?))?
                }
                InputValue::ProverKeyFile { path, fingerprint } => admission.add(Input::Key {
                    source: KeySource::Path(path),
                    fingerprint: *fingerprint,
                    verifier: selected.ok_or("entry-setup-material")?,
                })?,
                InputValue::ProverKeyInput { file, fingerprint } => admission.add(Input::Key {
                    source: KeySource::File(file),
                    fingerprint: *fingerprint,
                    verifier: selected.ok_or("entry-setup-material")?,
                })?,
                _ => admission.native_data(&backend, ty.clone(), input, selected)?,
            };
            admission.data(id, ty.kind())?;
        }
    }
    let _checked = cpu.enter(|| admission.load_shared(&backend, &capacity.backend(), ledger, 0))?;
    Ok(())
}
