//! Source-named declarations are checked before development setup or issuance.
use super::*;
use zkc_runtime::interactive::{LogicalType, PhysicalType};

pub(super) enum Service {
    Key {
        label: String,
        setup: String,
        prover: bool,
    },
    Resource {
        label: String,
        input: ResourceInput,
        domain: Domain,
    },
}
pub(super) struct Declarations {
    pub schedule: Schedule,
    pub roles: Vec<Declaration>,
}
pub(super) struct Declaration {
    pub role: EntryRole,
    pub services: Vec<Service>,
    pub types: BTreeMap<String, PhysicalType>,
    pub bytes: Vec<u8>,
}
fn named(value: &Json) -> Result<&str> {
    let value = text(value)?;
    if value.is_empty() || value.len() > 128 {
        return Err("host-name".into());
    }
    Ok(value)
}
fn physical(logical: &str) -> Result<PhysicalType> {
    let logical = match logical {
        "rng" => "rng:bls12-381.fr",
        "nonce" => "nonce:bls12-381.fr",
        "prover_key" => "prover_key:multilinear.kzg.bls12-381/1",
        "verifier_key" => "verifier_key:multilinear.kzg.bls12-381/1",
        other => other,
    };
    PhysicalType::default_for(LogicalType::parse(logical).map_err(|e| e.to_string())?)
        .map_err(|e| e.to_string())
}
pub(super) fn declarations(
    admitted: &Admitted,
    cfg: &Config<'_>,
    ranks: &BTreeMap<String, usize>,
) -> Result<Declarations> {
    if cfg.session.is_empty()
        || cfg.session.len() > 128
        || !cfg
            .session
            .bytes()
            .all(|b| b.is_ascii_alphanumeric() || b"_.-".contains(&b))
    {
        return Err("host-session".into());
    }
    let schedule =
        Schedule::new_with_work_limit(admitted, cfg.entry, cfg.session, cfg.schedule_work)?;
    let source_inputs = schedule.inputs()?;
    if !source_inputs.keys().eq(cfg.roles.keys()) {
        return Err("host-role-set".into());
    }
    let mut result = Vec::new();
    for role in admitted.entry(cfg.entry).ok_or("host-entry")? {
        let record = cfg.roles[&role.role];
        let mut services = Vec::new();
        let mut types = BTreeMap::new();
        for declaration in list(&record[1])? {
            let row = list(declaration)?;
            if row.len() < 2 {
                return Err("host-service".into());
            }
            let kind = text(&row[0])?;
            let label = named(&row[1])?.to_owned();
            let (service, ty) = match kind {
                "prover_key" | "verifier_key" if row.len() == 3 => {
                    let setup = named(&row[2])?;
                    if !ranks.contains_key(setup) {
                        return Err("host-service-setup".into());
                    }
                    (
                        Service::Key {
                            label: label.clone(),
                            setup: setup.into(),
                            prover: kind == "prover_key",
                        },
                        physical(kind)?,
                    )
                }
                "rng" | "nonce" | "rng:ristretto255.scalar" | "nonce:ristretto255.scalar"
                    if row.len() == 4 =>
                {
                    let scope = match text(&row[3])? {
                        "entry" => Some(role.instance.as_str()),
                        "session" => None,
                        _ => return Err("host-resource-scope".into()),
                    };
                    let ty = physical(kind)?;
                    (
                        Service::Resource {
                            label: label.clone(),
                            input: ResourceInput {
                                kind: ty.kind(),
                                field: ty.logical().identity(),
                                budget: natural(&row[2])?,
                            },
                            domain: Domain::new(&role.role, cfg.session, cfg.entry, scope),
                        },
                        ty,
                    )
                }
                _ => return Err("host-service".into()),
            };
            if types.insert(label, ty).is_some() {
                return Err("host-duplicate-service".into());
            }
            services.push(service);
        }
        let mut supplied = BTreeMap::new();
        for pair in list(&record[2])? {
            let pair = array(pair, 2)?;
            if supplied.insert(text(&pair[0])?, &pair[1]).is_some() {
                return Err("host-duplicate-input".into());
            }
        }
        let ports = &source_inputs[&role.role];
        if ports.len() != supplied.len() || ports.len() != role.inputs.len() {
            return Err("host-input-count".into());
        }
        let mut inputs = Vec::new();
        let mut affine = std::collections::BTreeSet::new();
        for ((source_name, ty), (target_name, target_type)) in ports.iter().zip(&role.inputs) {
            if admitted
                .source_map()
                .and_then(|m| m.port(&role.instance, &role.role, source_name))
                != Some(target_name.as_str())
            {
                return Err("host-source-port-map".into());
            }
            if *ty != target_type.logical().spelling() {
                return Err("host-input-type".into());
            }
            let value = supplied
                .get(source_name.as_str())
                .ok_or("host-input-name")?;
            let row = array(value, 2)?;
            if text(&row[0])? == "host" {
                let label = text(&row[1])?;
                if types.get(label) != Some(target_type) {
                    return Err("host-input-type".into());
                }
                if target_type.is_affine() && !affine.insert(label) {
                    return Err("host-input-alias".into());
                }
            }
            inputs.push(json!([target_name, value]));
        }
        result.push(Declaration {
            role,
            services,
            types,
            bytes: serde_json::to_vec(&json!(["zkc.inputs/1", inputs]))
                .map_err(|_| "host-input-json")?,
        });
    }
    Ok(Declarations {
        schedule,
        roles: result,
    })
}

pub(super) struct Prepared<B> {
    pub role: EntryRole,
    pub backend: Option<B>,
    pub plan: Option<zkc_backends::InputPlan>,
    pub services: Vec<Service>,
    pub bindings: InputBindings,
    pub handles: Vec<(String, Capability)>,
    pub values: Vec<Value>,
    pub load_usage: Option<zkc_runtime::interactive::Usage>,
}
pub(super) fn prepare<B: HostBackend>(
    declarations: Vec<Declaration>,
    keys: &BTreeMap<String, Keys>,
    factory: impl Fn(&EntryRole) -> Result<B>,
) -> Result<Vec<Prepared<B>>> {
    declarations
        .into_iter()
        .map(|d| {
            let backend = factory(&d.role)?;
            let plan = backend.prepare(&d.role, &d.bytes, &d.types)?;
            let mut bindings = InputBindings::new();
            for service in &d.services {
                if let Service::Key {
                    label,
                    setup,
                    prover,
                } = service
                {
                    let key = keys.get(setup).ok_or("host-service-setup")?;
                    let value = if *prover {
                        Value::ProverKey(Arc::new(key.prover_key().clone()))
                    } else {
                        Value::VerifierKey(Arc::new(key.verifier_key().clone()))
                    };
                    bindings.insert(label, value).map_err(|e| e.to_string())?;
                }
            }
            backend.check_entry(&plan, &d.role, &bindings)?;
            Ok(Prepared {
                role: d.role,
                backend: Some(backend),
                plan: Some(plan),
                services: d.services,
                bindings,
                handles: Vec::new(),
                values: Vec::new(),
                load_usage: None,
            })
        })
        .collect()
}
pub(super) fn issue<B: HostBackend>(prepared: &mut [Prepared<B>]) -> Result<()> {
    for role in prepared {
        let backend = role.backend.as_mut().expect("prepared backend");
        for service in &role.services {
            let (label, value) = match service {
                Service::Key { .. } => continue,
                Service::Resource {
                    label,
                    input,
                    domain,
                } => {
                    let value = backend.issue(*input, domain.clone())?;
                    if let Value::Rng(token) | Value::Nonce(token) = &value {
                        role.handles.push((label.clone(), token.clone()));
                    }
                    (label, value)
                }
            };
            role.bindings
                .insert(label, value)
                .map_err(|e| e.to_string())?;
        }
        role.values = role
            .plan
            .take()
            .expect("single-use input plan")
            .bind(backend, &role.bindings)
            .map_err(|e| e.to_string())?;
        role.bindings = InputBindings::new();
    }
    Ok(())
}
