//! Explicit setup selection for the local development host. Policy names source
//! ports and static receiving sites; it does not inspect candidate SSA spellings
//! or choose a verification key from a received payload.

use super::*;
use zkc_arkworks::Metadata;
use zkc_backends::{PortConstraint, SetupRegistry};
use zkc_runtime::interactive::{Receive, Type};

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct ReceiveSite {
    instance: String,
    role: String,
    site: String,
}

struct ReceiveSetup {
    schema: String,
    ty: zkc_runtime::interactive::PhysicalType,
    setup: Metadata,
}
struct SetupDecoder(BTreeMap<ReceiveSite, ReceiveSetup>);
impl MessageDecoder<NativeBackend> for SetupDecoder {
    fn decode(
        &self,
        backend: &NativeBackend,
        receive: &Receive,
        bytes: &[u8],
    ) -> std::result::Result<Value, BackendError> {
        if !zkc_backends::requires_setup(receive.ty.logical()) {
            return backend.decode_typed_value(receive.ty.clone(), bytes);
        }
        let e = &receive.envelope;
        let pin = self
            .0
            .get(&ReceiveSite {
                instance: e.origin.instance.clone(),
                role: e.receiver.clone(),
                site: e.site.clone(),
            })
            .ok_or_else(|| BackendError::new("refused:receive-setup-required"))?;
        if pin.schema != e.schema || pin.ty != receive.ty {
            return Err(BackendError::new("refused:receive-setup-port"));
        }
        backend.decode_for_setup(receive.ty.clone(), pin.setup, bytes)
    }
}

fn label(value: &Json) -> Result<&str> {
    let name = text(value)?;
    if name.is_empty() || name.len() > 128 {
        return Err("host-name".into());
    }
    Ok(name)
}

fn setup_ranks(cfg: &Config<'_>, policy: &Policy) -> Result<BTreeMap<String, usize>> {
    if cfg.setup.len() > 64 {
        return Err("host-setup-count".into());
    }
    let mut result = BTreeMap::new();
    let mut total_work = 0usize;
    for declaration in cfg.setup {
        let d = array(declaration, 3)?;
        let name = label(&d[0])?;
        if text(&d[1])? != "development" {
            return Err("host-setup-kind".into());
        }
        let rank = usize::try_from(natural(&d[2])?).map_err(|_| "host-arity")?;
        // Bound the aggregate upstream work before issuing any of the keys.
        if rank == 0 || rank > policy.max_arity {
            return Err("host-setup-rank".into());
        }
        let cells = u32::try_from(rank)
            .ok()
            .and_then(|n| 1usize.checked_shl(n))
            .and_then(|n| n.checked_mul(rank))
            .ok_or("host-setup-work")?;
        total_work = total_work.checked_add(cells).ok_or("host-setup-work")?;
        if total_work > policy.max_setup_cells || result.insert(name.into(), rank).is_some() {
            return Err("host-setup-work-or-duplicate".into());
        }
    }
    Ok(result)
}

fn receiver_selections(
    admitted: &Admitted,
    cfg: &Config<'_>,
    ranks: &BTreeMap<String, usize>,
) -> Result<BTreeMap<ReceiveSite, (zkc_runtime::interactive::ReceivePort, String)>> {
    let mut expected = admitted
        .receive_ports(cfg.entry)
        .ok_or("host-entry")?
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
    let mut selections = BTreeMap::new();
    for declaration in cfg.receives {
        let d = array(declaration, 4)?;
        let site = ReceiveSite {
            instance: label(&d[0])?.into(),
            role: label(&d[1])?.into(),
            site: label(&d[2])?.into(),
        };
        let setup = label(&d[3])?;
        if !ranks.contains_key(setup) {
            return Err("host-receive-setup".into());
        }
        let port = expected
            .remove(&site)
            .ok_or("host-receive-site-or-duplicate")?;
        selections.insert(site, (port, setup.into()));
    }
    if !expected.is_empty() {
        return Err("host-receive-coverage".into());
    }
    Ok(selections)
}

fn entry_ports(
    admitted: &Admitted,
    role: &EntryRole,
    record: &[Json],
    keys: &BTreeMap<String, Keys>,
) -> Result<BTreeMap<String, PortConstraint>> {
    let mapping = admitted.source_map().ok_or("host-source-map")?;
    let mut result = BTreeMap::new();
    for declaration in list(&record[3])? {
        let d = array(declaration, 3)?;
        let source = label(&d[0])?;
        let target = mapping
            .port(&role.instance, &role.role, source)
            .ok_or("host-constraint-port")?;
        let arity = if d[1].is_null() {
            None
        } else {
            Some(usize::try_from(natural(&d[1])?).map_err(|_| "host-arity")?)
        };
        let setup = if d[2].is_null() {
            None
        } else {
            Some(
                keys.get(label(&d[2])?)
                    .ok_or("host-constraint-setup")?
                    .verifier_key()
                    .metadata(),
            )
        };
        if arity.is_none() && setup.is_none() {
            return Err("host-empty-constraint".into());
        }
        let ty = role
            .inputs
            .iter()
            .find(|p| p.0 == target)
            .ok_or("host-constraint-port")?
            .1
            .kind();
        let has_shape = matches!(
            ty,
            Type::Table
                | Type::Point
                | Type::ProverKey
                | Type::VerifierKey
                | Type::Commitment
                | Type::Proof
                | Type::OpeningState
        );
        let has_setup = matches!(
            ty,
            Type::ProverKey
                | Type::VerifierKey
                | Type::Commitment
                | Type::Proof
                | Type::OpeningState
        );
        if arity.is_some() && !has_shape
            || setup.is_some() && !has_setup
            || setup.is_some_and(|s| arity.is_some_and(|n| n != s.arity()))
        {
            return Err("host-constraint-type-or-rank".into());
        }
        if result
            .insert(target.into(), PortConstraint { arity, setup })
            .is_some()
        {
            return Err("host-duplicate-constraint".into());
        }
    }
    Ok(result)
}

pub(super) fn run(
    source: &[u8],
    candidate: &[u8],
    cfg: &Config<'_>,
    checker: &ParticipantChecker,
) -> Result<Json> {
    let policy = Policy::default();
    let start = Instant::now();
    let admission = NativeBackend::with_setups(
        policy,
        EntryPolicy::new(
            Domain::new("admission", "admission", "admission", None),
            None,
            PublicInputs::LocalOnly,
        ),
        SetupRegistry::new(vec![], &policy).map_err(|e| e.to_string())?,
    )
    .map_err(|e| e.to_string())?;
    let admitted =
        admit_physical(source, candidate, &admission, checker).map_err(|e| e.to_string())?;
    let admission_seconds = start.elapsed().as_secs_f64();
    let ranks = setup_ranks(cfg, &policy)?;
    let receives = receiver_selections(&admitted, cfg, &ranks)?;
    let setup_start = Instant::now();
    let keys = ranks
        .iter()
        .map(|(name, rank)| {
            Ok((
                name.clone(),
                Keys::setup_for_development(*rank, &policy.ark_bounds())
                    .map_err(|e| e.to_string())?,
            ))
        })
        .collect::<Result<BTreeMap<_, _>>>()?;
    let registry = SetupRegistry::new(
        keys.values().map(|k| k.verifier_key().clone()).collect(),
        &policy,
    )
    .map_err(|e| e.to_string())?;
    let setup_seconds = setup_start.elapsed().as_secs_f64();
    let decoder = SetupDecoder(
        receives
            .into_iter()
            .map(|(site, (port, name))| {
                (
                    site,
                    ReceiveSetup {
                        schema: port.schema,
                        ty: port.ty,
                        setup: keys[&name].verifier_key().metadata(),
                    },
                )
            })
            .collect(),
    );
    execute(
        &admitted,
        cfg,
        &keys,
        (admission_seconds, setup_seconds),
        |role| {
            let record = cfg.roles.get(&role.role).ok_or("host-role")?;
            let ports = entry_ports(&admitted, role, record, &keys)?;
            NativeBackend::with_setups(
                policy,
                EntryPolicy::new(
                    Domain::new(&role.role, cfg.session, cfg.entry, Some(&role.instance)),
                    None,
                    PublicInputs::LocalOnly,
                )
                .with_ports(ports),
                registry.clone(),
            )
            .map_err(|e| e.to_string())
        },
        &decoder,
    )
}
