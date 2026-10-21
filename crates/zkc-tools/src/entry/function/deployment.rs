//! Bind generated contracts to independently admitted operation owners.
use super::*;
use crate::entry::interface::{InputPort, raw::Port};

fn nominal(s: &Schema, family: &str, member: &str, constructible: bool) -> Result<()> {
    // Closed type arguments belong after the generated member, as in Layouts.
    let (base, args) = family
        .find('<')
        .map_or((family, ""), |i| (&family[..i], &family[i..]));
    require(
        s.display_type == format!("{base}::{member}{args}")
            && s.constructible == constructible
            && !s.custody,
        "entry-host-nominal",
    )
}
fn record<'a>(s: &Schema, fields: impl Iterator<Item = (&'a str, &'a Schema)>) -> Result<()> {
    require(s.kind == SchemaKind::Record, "entry-host-deployment-shape")?;
    let fields = fields.collect::<Vec<_>>();
    require(
        s.fields.len() == fields.len()
            && s.fields
                .iter()
                .zip(fields)
                .all(|(a, (n, s))| a.name == n && a.schema == *s),
        "entry-host-deployment-shape",
    )
}
fn ordinary(interface: &super::super::Interface, p: InputPort<'_>) -> bool {
    interface.is_source_data(p)
}
fn input_record<'a>(
    s: &Schema,
    interface: &super::super::Interface,
    ports: impl Iterator<Item = InputPort<'a>>,
) -> Result<()> {
    record(
        s,
        ports
            .filter(|p| ordinary(interface, *p))
            .map(|p| (p.definition.name.as_str(), &p.definition.schema)),
    )
}
fn output_record<'a>(s: &Schema, ports: impl Iterator<Item = &'a Port>) -> Result<()> {
    record(s, ports.map(|p| (p.name.as_str(), &p.schema)))
}
pub(super) fn check(
    d: &carrier::Deployment,
    native: &Deployment,
    families: &mut BTreeMap<String, String>,
) -> Result<()> {
    let interface = match native {
        Deployment::Run(n) => n.interface(),
        Deployment::Proof(n) => n.interface(),
    };
    check_interface(d, interface, families)
}
pub(super) fn check_interface(
    d: &carrier::Deployment,
    interface: &super::super::Interface,
    families: &mut BTreeMap<String, String>,
) -> Result<()> {
    require(d.results.len() == 1, "entry-host-deployment-signature")?;
    let r = &d.results[0];
    let source = interface
        .entry()
        .strip_suffix(&format!("::{}", d.operation))
        .unwrap_or(interface.entry());
    let arguments = d
        .parameters
        .first()
        .and_then(|s| s.display_type.find('<').map(|i| &s.display_type[i..]))
        .unwrap_or("");
    let family = format!("{source}{arguments}");
    let family = family.as_str();
    // Identical nominal families cannot be rebound to a different checked source.
    let family_pin = format!(
        "{}:{}:{}",
        interface.capture(),
        interface.toolchain(),
        family
    );
    fn pin(
        s: &Schema,
        prefix: &str,
        family_pin: &str,
        families: &mut BTreeMap<String, String>,
    ) -> Result<()> {
        if s.display_type.starts_with(prefix) {
            for (key, value) in [
                (format!("identity:{}", s.identity), family_pin.to_owned()),
                (
                    format!("type:{}", s.display_type),
                    format!("{family_pin}:{}", s.identity),
                ),
            ] {
                if let Some(old) = families.insert(key, value.clone()) {
                    require(old == value, "entry-host-family")?;
                }
            }
            for f in &s.fields {
                pin(&f.schema, prefix, family_pin, families)?;
            }
            for f in s.alternatives.iter().flat_map(|a| &a.fields) {
                pin(&f.schema, prefix, family_pin, families)?;
            }
        }
        Ok(())
    }
    for s in d.parameters.iter().chain(&d.results) {
        pin(s, &format!("{source}::"), &family_pin, families)?;
    }
    if !interface.is_proof() {
        require(
            d.operation == "run" && d.parameters.len() == 1,
            "entry-host-deployment-signature",
        )?;
        nominal(&d.parameters[0], family, "Inputs", true)?;
        nominal(r, family, "RunResult", false)?;
        require(
            d.parameters[0].fields.len() == interface.roles().len()
                && r.fields.len() == interface.roles().len(),
            "entry-host-role-shape",
        )?;
        for ((input, output), role) in d.parameters[0]
            .fields
            .iter()
            .zip(&r.fields)
            .zip(interface.roles())
        {
            require(
                input.name == role.name && output.name == role.name,
                "entry-host-role-shape",
            )?;
            nominal(
                &input.schema,
                family,
                &format!("Inputs::{}", role.name),
                true,
            )?;
            nominal(
                &output.schema,
                family,
                &format!("RunResult::{}", role.name),
                false,
            )?;
            input_record(&input.schema, interface, interface.input_ports(role))?;
            output_record(&output.schema, interface.output_ports(role))?;
        }
    } else {
        require(d.parameters.len() == 2, "entry-host-deployment-signature")?;
        nominal(&d.parameters[0], family, "Public", true)?;
        input_record(&d.parameters[0], interface, interface.public_ports())?;
        let proof = interface.proof().ok_or_else(|| error("entry-host-stage"))?;
        if d.operation == "prove" {
            nominal(&d.parameters[1], family, "Witness", true)?;
            let role = &interface.roles()[proof.prover];
            input_record(&d.parameters[1], interface, interface.named_inputs(role))?;
            nominal(r, family, "ProveResult", false)?;
            require(
                r.kind == SchemaKind::Record
                    && r.fields.len() == 2
                    && r.fields[0].name == "proof"
                    && r.fields[1].name == "outputs",
                "entry-host-deployment-shape",
            )?;
            candidate(&r.fields[0].schema, family)?;
            nominal(&r.fields[1].schema, family, "ProverOutputs", false)?;
            output_record(&r.fields[1].schema, interface.output_ports(role))?;
        } else {
            require(d.operation == "verify", "entry-host-stage")?;
            candidate(&d.parameters[1], family)?;
            nominal(r, family, "VerifyResult", false)?;
            require(
                r.kind == SchemaKind::Variant && r.alternatives.len() == 2,
                "entry-host-deployment-shape",
            )?;
            let accepted = &r.alternatives[0];
            let rejected = &r.alternatives[1];
            require(
                accepted.name == "Accepted"
                    && accepted.fields.len() == 1
                    && accepted.fields[0].name == "outputs"
                    && rejected.name == "Rejected"
                    && rejected.fields.is_empty(),
                "entry-host-deployment-shape",
            )?;
            nominal(&accepted.fields[0].schema, family, "VerifierOutputs", false)?;
            output_record(
                &accepted.fields[0].schema,
                interface.output_ports(&interface.roles()[proof.verifier]),
            )?;
        }
    }
    Ok(())
}
fn candidate(s: &Schema, family: &str) -> Result<()> {
    nominal(s, family, "Proof", true)?;
    require(
        s.kind == SchemaKind::Record
            && s.fields.len() == 1
            && s.fields[0].name == "bytes"
            && s.fields[0].schema.kind == SchemaKind::Builtin
            && s.fields[0].schema.leaves == ["bytes"],
        "entry-host-proof-shape",
    )
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
    interface: &super::super::Interface,
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
    entry: &super::super::RunEntry,
    value: &TypedValue,
    context: &RunContext,
) -> Result<super::super::RunRequest> {
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
        let empty = super::super::RoleInputs::default();
        let context = context.unwrap_or(&empty);
        roles.insert(
            role.name.clone(),
            super::super::RoleInputs {
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
    Ok(super::super::RunRequest {
        session: context
            .session_for_call()
            .map_err(|e| EntryError::new(EntryPhase::Preparation, e))?,
        roles,
        setups: context.setups.clone(),
    })
}
pub(super) fn proof_request(
    entry: &super::super::ProofEntry,
    producer: bool,
    values: &[TypedValue],
    context: &ProofContext,
) -> Result<super::super::ProofRequest> {
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
    Ok(super::super::ProofRequest {
        public: extras(
            interface,
            interface.public_ports(),
            &public_extras,
            named(&values[0]),
        )?,
        private: super::super::RoleInputs {
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
    let zkc_backends::Value::Bytes(bytes) = value.fields()[0]
        .native()
        .map_err(|e| EntryError::new(EntryPhase::Request, e))?
    else {
        return Err(error("entry-host-proof-shape"));
    };
    Ok(bytes)
}

// Successful native owners supply these values; source constructors cannot.
pub(super) fn run_value(schema: &Schema, outputs: super::super::RoleValues) -> super::super::Value {
    let mut outputs = outputs;
    super::super::Value::Record(
        schema
            .fields
            .iter()
            .map(|f| {
                (
                    f.name.clone(),
                    super::super::Value::Record(outputs.remove(&f.name).expect("checked role")),
                )
            })
            .collect(),
    )
}
pub(super) fn prove_value(outputs: NamedValues, bytes: Vec<u8>) -> super::super::Value {
    super::super::Value::Record(BTreeMap::from([
        (
            "proof".into(),
            super::super::Value::Record(BTreeMap::from([(
                "bytes".into(),
                zkc_backends::Value::Bytes(bytes.into()).into(),
            )])),
        ),
        ("outputs".into(), super::super::Value::Record(outputs)),
    ]))
}
pub(super) fn verify_value(outputs: Option<NamedValues>) -> super::super::Value {
    super::super::Value::Variant {
        alternative: if outputs.is_some() {
            "Accepted"
        } else {
            "Rejected"
        }
        .into(),
        fields: outputs
            .map(|o| BTreeMap::from([("outputs".into(), super::super::Value::Record(o))]))
            .unwrap_or_default(),
    }
}
pub(super) fn context_check(
    host: &EntryHost,
    context: &InvocationContext,
    ledger: &zkc_runtime::vm::ExecutionLedger,
) -> Result<()> {
    fn check_role(
        interface: &super::super::Interface,
        role: &super::super::interface::RolePorts,
        context: Option<&super::super::RoleInputs>,
    ) -> Result<()> {
        let empty = super::super::RoleInputs::default();
        let context = context.unwrap_or(&empty);
        let services =
            super::super::arguments::services(interface.services(role), context.services.clone())
                .map_err(|e| EntryError::new(EntryPhase::Request, e))?;
        require(
            services
                .into_iter()
                .all(|n| n <= crate::host::inputs::RESOURCE_BUDGET_LIMIT),
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
            if p.key == Some(zkc_runtime::vm::Type::ProverKey) {
                require(
                    matches!(
                        value,
                        super::super::Value::Leaf(
                            crate::execution::InputValue::ProverKey(_)
                                | crate::execution::InputValue::ProverKeyFile { .. }
                                | crate::execution::InputValue::ProverKeyInput { .. }
                        )
                    ),
                    "entry-input-key",
                )?;
            } else {
                super::super::value::flatten(&p.schema, data::duplicate(value), &mut Vec::new())
                    .map_err(|e| EntryError::new(EntryPhase::Request, e))?;
            }
        }
        Ok(())
    }
    require(
        context.deployments.len() == host.deployments.len(),
        "entry-host-context",
    )?;
    let mut imports =
        crate::host::setups::VerifierKeys::new(host.options.limits.capacity.backend().ark_bounds());
    imports.set_ledger(Some(ledger.clone()));
    for (id, native) in &host.deployments {
        let value = context
            .deployments
            .get(id)
            .ok_or_else(|| error("entry-host-context"))?;
        let (interface, material) = match (native, value) {
            (Deployment::Run(entry), InvocationBinding::Run(v)) => {
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
            (Deployment::Proof(entry), InvocationBinding::Proof(v)) => {
                require(v.context.len() <= 4096, "native-proof-context-limit")?;
                if let Some(budget) = v.transcript_budget {
                    require(
                        budget <= crate::host::inputs::RESOURCE_BUDGET_LIMIT,
                        "native-proof-budget",
                    )?;
                    require(
                        entry.binding_scope() == super::super::BindingScope::Transcript
                            || budget == 0,
                        "native-proof-unselected-transcript",
                    )?;
                }
                let interface = entry.interface();
                let proof = interface.proof().expect("admitted proof");
                let producing = host
                    .document
                    .deployments
                    .iter()
                    .find(|d| d.id == *id)
                    .expect("admitted deployment")
                    .operation
                    == "prove";
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
        let keys = super::super::setups::check_pinned_material(
            interface,
            &host.authority[id],
            material,
            host.options.limits.capacity,
            &mut imports,
        )
        .map_err(|e| EntryError::new(EntryPhase::Preparation, e))?;
        match value {
            InvocationBinding::Run(v) => {
                for role in interface.roles() {
                    if let Some(context) = v.roles.get(&role.name) {
                        check_context_data(
                            interface,
                            role,
                            context,
                            &keys,
                            host.options.limits.capacity,
                            ledger,
                        )
                        .map_err(|e| EntryError::new(EntryPhase::Preparation, e))?;
                    }
                }
            }
            InvocationBinding::Proof(v) => {
                let proof = interface.proof().expect("checked proof");
                let producing = host
                    .document
                    .deployments
                    .iter()
                    .find(|d| d.id == *id)
                    .expect("checked deployment")
                    .operation
                    == "prove";
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
                )
                .map_err(|e| EntryError::new(EntryPhase::Preparation, e))?;
            }
        }
    }
    Ok(())
}

pub(super) fn context_bytes(context: &InvocationContext) -> usize {
    fn role(context: &super::super::RoleInputs) -> usize {
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
fn check_context_data(
    interface: &super::super::Interface,
    role: &super::super::interface::RolePorts,
    context: &super::super::RoleInputs,
    keys: &BTreeMap<String, std::sync::Arc<zkc_arkworks::VerifierKey>>,
    capacity: crate::execution::Capacity,
    ledger: &zkc_runtime::vm::ExecutionLedger,
) -> std::result::Result<(), String> {
    use crate::execution::InputValue;
    use crate::host::admission::{Admission, Input, KeySource};
    use zkc_runtime::vm::PhysicalType;
    let registry = zkc_backends::SetupRegistry::new(
        keys.values().map(|k| k.as_ref().clone()).collect(),
        &capacity.backend(),
    )
    .map_err(|e| e.to_string())?;
    let backend = zkc_backends::NativeBackend::new(
        capacity.backend(),
        zkc_backends::EntryPolicy::new(
            zkc_backends::Domain::new(
                &role.native_name,
                "entry-context",
                interface.selected_protocol().symbol.as_str(),
                None,
            ),
            None,
        ),
        registry,
    )
    .map_err(|e| e.to_string())?;
    let ports = interface.context_ports(role).collect::<Vec<_>>();
    let descriptions = ports
        .iter()
        .map(|p| {
            let value = data::duplicate(&context.inputs[&p.name]);
            let mut leaves = Vec::new();
            if p.key == Some(zkc_runtime::vm::Type::ProverKey) {
                let super::super::Value::Leaf(value) = value else {
                    return Err("entry-input-key".to_owned());
                };
                leaves.push(value);
            } else {
                super::super::value::flatten(&p.schema, value, &mut leaves)?;
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
                interface
                    .logical_type(spelling)
                    .ok_or("entry-input-type")?
                    .clone(),
            )
            .map_err(|e| e.to_string())?;
            let selected = interface
                .setups
                .iter()
                .find(|s| s.inputs.contains(&(*original as usize)))
                .map(|s| keys[&s.name].clone());
            let id = match input {
                InputValue::ProverKey(material) => {
                    admission.add(Input::Ready(material.operand(
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
    let _checked = admission.load_shared(&backend, &capacity.backend(), ledger, 0)?;
    Ok(())
}
