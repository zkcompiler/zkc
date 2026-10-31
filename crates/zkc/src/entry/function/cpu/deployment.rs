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
fn named(value: &TypedValue) -> NamedValues {
    value
        .schema()
        .fields
        .iter()
        .zip(value.fields())
        .map(|(f, v)| (f.name.clone(), v.to_value()))
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
        require(
            allowed.contains(name) && !data.contains_key(name),
            "entry-host-context-input",
        )?;
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
    require(
        context
            .roles
            .keys()
            .all(|n| interface.roles().iter().any(|r| r.name == *n)),
        "entry-host-context-role",
    )?;
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
                    named(source),
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
        named(&values[1])
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
                .any(|p| p.public.is_some() && p.name.as_str() == n.as_str())
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
            named(&values[0]),
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
pub(super) fn context_check(
    host: &EntryHost,
    context: &InvocationContext,
    ledger: &zkc_runtime::vm::ExecutionLedger,
) -> Result<()> {
    fn check_role(
        interface: &crate::entry::Interface,
        role: &crate::entry::interface::RolePorts,
        context: Option<&crate::entry::RoleInputs>,
    ) -> Result<()> {
        let empty = crate::entry::RoleInputs::default();
        let context = context.unwrap_or(&empty);
        let services =
            crate::entry::arguments::services(interface.services(role), context.services.clone())
                .map_err(|e| EntryError::new(EntryPhase::Request, e))?;
        require(
            services
                .into_iter()
                .all(|n| n <= crate::host::request::RESOURCE_BUDGET_LIMIT),
            "entry-host-service-budget",
        )?;
        let allowed = interface.context_ports(role).collect::<Vec<_>>();
        require(
            context.inputs.len() == allowed.len()
                && allowed.iter().all(|p| context.inputs.contains_key(&p.name)),
            "entry-host-context-input",
        )?;
        for p in allowed {
            let value = &context.inputs[&p.name];
            if p.key == Some("prover_key") {
                require(
                    matches!(
                        value,
                        crate::entry::Value::Leaf(
                            crate::execution::InputValue::ProverKey(_)
                                | crate::execution::InputValue::ProverKeyFile { .. }
                                | crate::execution::InputValue::ProverKeyInput { .. }
                        )
                    ),
                    "entry-input-key",
                )?;
            } else {
                crate::entry::value::flatten(&p.schema, data::duplicate(value), &mut Vec::new())
                    .map_err(|e| EntryError::new(EntryPhase::Request, e))?;
            }
        }
        Ok(())
    }
    require(
        context.deployments.len() == host.deployments.len(),
        "entry-host-context",
    )?;
    let mut imports = crate::host::setups::VerifierKeys::new(
        host.options.limits.capacity.backend().ark_bounds(),
        host.options.limits.installation.clone(),
    );
    imports.set_ledger(Some(ledger.clone()));
    for (id, deployment) in &host.deployments {
        let value = context
            .deployments
            .get(id)
            .ok_or_else(|| error("entry-host-context"))?;
        let (interface, material) = match (&deployment.kind, value) {
            (DeploymentKind::Run(entry), InvocationBinding::Run(v)) => {
                if let Some(session) = &v.session {
                    crate::run::RunHost::check_session(session)
                        .map_err(|e| EntryError::new(EntryPhase::Request, e))?;
                }
                let interface = entry.interface();
                require(
                    v.roles
                        .keys()
                        .all(|n| interface.roles().iter().any(|r| r.name == *n)),
                    "entry-host-context-role",
                )?;
                for role in interface.roles() {
                    check_role(interface, role, v.roles.get(&role.name))?;
                }
                (interface, &v.setups)
            }
            (DeploymentKind::Proof { entry, operation }, InvocationBinding::Proof(v)) => {
                require(v.context.len() <= 4096, "native-proof-context-limit")?;
                if let Some(budget) = v.transcript_budget {
                    require(
                        budget <= crate::host::request::RESOURCE_BUDGET_LIMIT,
                        "native-proof-budget",
                    )?;
                    require(
                        entry.binding_scope() == crate::entry::BindingScope::Transcript
                            || budget == 0,
                        "native-proof-unselected-transcript",
                    )?;
                }
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
                (interface, &v.setups)
            }
            _ => return Err(error("entry-host-context-operation")),
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
