use super::{
    JointOutcome, LocalTransport, MessageDecoder, ParticipantChecker, Schedule, WireBackend,
    drive_with_decoder,
};
use serde_json::{Value as Json, json};
use std::{collections::BTreeMap, sync::Arc, time::Instant};
use zkc_backends::{
    Capability, CapabilityObservation, Domain, EntryPolicy, InputBindings, Keys, NativeBackend,
    Policy, PublicInputs, Value,
};
use zkc_runtime::interactive::{
    Action, Admitted, BackendError, EntryRole, Runner, Stop, StopKind, admit_physical,
};

mod setups;

type Result<T> = std::result::Result<T, String>;
fn array(v: &Json, len: usize) -> Result<&[Json]> {
    let a = list(v)?;
    if a.len() == len {
        Ok(a)
    } else {
        Err("host-record".into())
    }
}
fn list(v: &Json) -> Result<&[Json]> {
    v.as_array().map(Vec::as_slice).ok_or("host-array".into())
}
fn text(v: &Json) -> Result<&str> {
    v.as_str().ok_or("host-string".into())
}
fn natural(v: &Json) -> Result<u64> {
    let s = text(v)?;
    let n = s.parse::<u64>().map_err(|_| "host-natural")?;
    if n.to_string() != s {
        return Err("host-natural".into());
    }
    Ok(n)
}
fn read(path: &str) -> Result<Vec<u8>> {
    crate::host::io::read_bounded(path, 1_048_576).map_err(|error| match error {
        crate::host::io::ReadError::Io(_) => "host-io".into(),
        crate::host::io::ReadError::Limit => "host-byte-limit".into(),
    })
}
trait HostBackend: WireBackend<Value = Value> {
    fn external_work_spent(&self) -> u64;
    fn live_resource_units(&self) -> usize;
    fn issue(&mut self, kind: &str, domain: Domain, budget: u64) -> Result<Value>;
    fn inputs(
        &self,
        role: &EntryRole,
        bytes: &[u8],
        bindings: &InputBindings,
    ) -> Result<Vec<Value>>;
    fn observe(
        &self,
        token: &Capability,
    ) -> std::result::Result<CapabilityObservation, BackendError>;
}
impl HostBackend for NativeBackend {
    fn external_work_spent(&self) -> u64 {
        self.external_work_spent()
    }
    fn live_resource_units(&self) -> usize {
        self.live_resource_units()
    }
    fn issue(&mut self, kind: &str, domain: Domain, budget: u64) -> Result<Value> {
        match kind {
            "rng" => self.issue_rng(domain, budget),
            "rng:ristretto255.scalar" => self.issue_rng_for(
                zkc_runtime::interactive::Identity::Ristretto255Scalar,
                domain,
                budget,
            ),
            "nonce:ristretto255.scalar" => self.issue_nonce_for(
                zkc_runtime::interactive::Identity::Ristretto255Scalar,
                domain,
                budget,
            ),
            "nonce" => self.issue_nonce(domain, budget),
            _ => return Err("host-service-profile".into()),
        }
        .map_err(|e| e.to_string())
    }
    fn inputs(
        &self,
        role: &EntryRole,
        bytes: &[u8],
        bindings: &InputBindings,
    ) -> Result<Vec<Value>> {
        self.inputs_from_json(role, bytes, bindings)
            .map_err(|e| e.to_string())
    }
    fn observe(
        &self,
        token: &Capability,
    ) -> std::result::Result<CapabilityObservation, BackendError> {
        self.observe(token)
    }
}
struct Config<'a> {
    entry: &'a str,
    session: &'a str,
    setup: &'a [Json],
    roles: BTreeMap<String, &'a [Json]>,
    receives: &'a [Json],
}
fn config(value: &Json) -> Result<Config<'_>> {
    let root = list(value)?;
    match root.first().and_then(Json::as_str) {
        Some("zkc.run/2") if root.len() == 6 => (),
        _ => return Err("host-version".into()),
    };
    let mut roles = BTreeMap::new();
    for r in list(&root[4])? {
        let record = array(r, 4)?;
        if roles.insert(text(&record[0])?.into(), record).is_some() {
            return Err("host-duplicate-role".into());
        }
    }
    Ok(Config {
        entry: text(&root[1])?,
        session: text(&root[2])?,
        setup: list(&root[3])?,
        roles,
        receives: list(&root[5])?,
    })
}

/// A bounded local development host. Protocol algorithms come exclusively from
/// the independently checked compiler artifact. This command issues OS-random
/// services and explicitly selected development setup; it has no fixture tape.
pub fn run(args: &[String]) -> Result<Json> {
    let [source_path, candidate_path, inputs_path, checker_path] = args else {
        return Err("usage: zkc run-protocol SOURCE PARTICIPANTS INPUTS CHECKER".into());
    };
    let source = read(source_path)?;
    let candidate = read(candidate_path)?;
    let input: Json = serde_json::from_slice(&read(inputs_path)?).map_err(|_| "host-json")?;
    let cfg = config(&input)?;
    let checker = ParticipantChecker::new(checker_path).map_err(|_| "checker-io")?;
    setups::run(&source, &candidate, &cfg, &checker)
}
fn execute<B: HostBackend, D: MessageDecoder<B>>(
    admitted: &Admitted,
    cfg: &Config<'_>,
    keys: &BTreeMap<String, Keys>,
    seconds: (f64, f64),
    factory: impl Fn(&EntryRole) -> Result<B>,
    decoder: &D,
) -> Result<Json> {
    let mut schedule = Schedule::new(admitted, cfg.entry, cfg.session)?;
    let source_inputs = schedule.inputs()?;
    if !source_inputs.keys().eq(cfg.roles.keys()) {
        return Err("host-role-set".into());
    }
    let roles = admitted.entry(cfg.entry).ok_or("host-entry")?;
    let mut runners = BTreeMap::new();
    let mut ingress_stops = BTreeMap::new();
    let mut observed_resources = BTreeMap::new();
    let preparation = Instant::now();
    for role in roles {
        let record = cfg.roles.get(&role.role).ok_or("host-role")?;
        let mut backend = factory(&role)?;
        let mut bindings = InputBindings::new();
        let mut resource_handles = Vec::new();
        for service in list(&record[1])? {
            let s = list(service)?;
            let (kind, label) = if s.len() >= 2 {
                (text(&s[0])?, text(&s[1])?)
            } else {
                return Err("host-service".into());
            };
            let value = match kind {
                "prover_key" | "verifier_key" if s.len() == 3 => {
                    let setup = text(&s[2])?;
                    let keys = keys.get(setup).ok_or("host-service-setup")?;
                    if kind == "prover_key" {
                        Value::ProverKey(Arc::new(keys.prover_key().clone()))
                    } else {
                        Value::VerifierKey(Arc::new(keys.verifier_key().clone()))
                    }
                }
                "rng" | "nonce" | "rng:ristretto255.scalar" | "nonce:ristretto255.scalar"
                    if s.len() == 4 =>
                {
                    let scope = match text(&s[3])? {
                        "entry" => Some(role.instance.as_str()),
                        "session" => None,
                        _ => return Err("host-resource-scope".into()),
                    };
                    backend.issue(
                        kind,
                        Domain::new(&role.role, cfg.session, cfg.entry, scope),
                        natural(&s[2])?,
                    )?
                }
                _ => return Err("host-service".into()),
            };
            if matches!(value, Value::Rng(_) | Value::Nonce(_)) {
                resource_handles.push((label.to_owned(), value.clone()));
            }
            bindings.insert(label, value).map_err(|e| e.to_string())?;
        }
        let mut supplied = BTreeMap::new();
        for pair in list(&record[2])? {
            let p = array(pair, 2)?;
            if supplied.insert(text(&p[0])?, &p[1]).is_some() {
                return Err("host-duplicate-input".into());
            }
        }
        let ports = source_inputs.get(&role.role).ok_or("host-inputs")?;
        if ports.len() != supplied.len() || ports.len() != role.inputs.len() {
            return Err("host-input-count".into());
        }
        let mut inputs = Vec::new();
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
            inputs.push(json!([
                target_name,
                supplied
                    .get(source_name.as_str())
                    .ok_or("host-input-name")?
            ]));
        }
        let bytes =
            serde_json::to_vec(&json!(["zkc.inputs/1", inputs])).map_err(|_| "host-input-json")?;
        let inputs = backend.inputs(&role, &bytes, &bindings)?;
        let mut runner = Runner::new(
            admitted,
            cfg.entry,
            &role.role,
            cfg.session,
            backend,
            inputs,
        )
        .map_err(|e| e.error.to_string())?;
        // Capture construction's actual terminal observation before the driver
        // can execute a member or cancel a peer. No site-name inference needed.
        let ingress_stop = if runner.is_terminal()
            && let Action::Stopped(stop) = runner.poll()
        {
            Some(stop_details(&stop))
        } else {
            None
        };
        ingress_stops.insert(role.role.clone(), ingress_stop);
        observed_resources.insert(role.role.clone(), resource_handles);
        runners.insert(role.role, runner);
    }
    let preparation_seconds = preparation.elapsed().as_secs_f64();
    let start = Instant::now();
    let report = drive_with_decoder(&mut schedule, &mut runners, &mut LocalTransport, decoder);
    let execution_seconds = start.elapsed().as_secs_f64();
    let stopped = match &report.outcome {
        JointOutcome::Stopped(stop) => Some(stop_details(stop)),
        _ => None,
    };
    let outcome = match report.outcome {
        JointOutcome::Returned(values) => {
            let mut outputs = BTreeMap::new();
            for (role, values) in values {
                outputs.insert(
                    role.clone(),
                    values
                        .iter()
                        .map(|v| public_output(runners[&role].backend(), v))
                        .collect::<Result<Vec<_>>>()?,
                );
            }
            json!(["returned", outputs])
        }
        JointOutcome::Stopped(stop) => {
            json!(["stopped", stop.role, stop.site, format!("{:?}", stop.kind)])
        }
        JointOutcome::Failed(error) => json!(["failed", error]),
    };
    let mut resources = Vec::new();
    let mut usage = BTreeMap::new();
    let mut ingress = BTreeMap::new();
    for (role, runner) in &runners {
        ingress.insert(
            role,
            json!({
                "selected_parameters": runner.selected_parameters(),
                "stop": ingress_stops[role],
                "events": runner.ingress_actions().iter().map(|action| json!({
                    "origin": action.cut.origin.json(), "role": action.cut.role,
                    "site": action.cut.site, "function": action.function
                })).collect::<Vec<_>>()
            }),
        );
        for (name, value) in &observed_resources[role] {
            if let Value::Rng(token) | Value::Nonce(token) = value {
                let state = runner.backend().observe(token).map_err(|e| e.to_string())?;
                resources.push(json!([
                    role,
                    name,
                    state.generation,
                    state.draw_count,
                    state.budget,
                    state.stage
                ]));
            }
        }
        let u = runner.usage();
        usage.insert(
            role,
            json!({"instructions":u.instructions,"calls":u.calls,"iterations":u.iterations,
            "live_value_bytes":u.live_value_bytes,"total_value_bytes":u.total_value_bytes,
            "external_work_spent":runner.backend().external_work_spent(),
            "live_resource_units":runner.backend().live_resource_units()}),
        );
    }
    Ok(
        json!({"format":"zkc.run-result/1", "profile":Json::Null,"entry":cfg.entry,"session":cfg.session,
        "outcome":outcome,"resources":resources,"usage":usage,"ingress":ingress,"cancelled_roles":report.cancelled.iter().map(|s| &s.role).collect::<Vec<_>>(),
        "stop":stopped,"cancellations":report.cancelled.iter().map(stop_details).collect::<Vec<_>>(),
        "wire":{"messages":report.wire.messages,"payload_bytes":report.wire.payload_bytes,"envelope_bytes":report.wire.envelope_bytes},
        "seconds":{"admission":seconds.0,"development_setup":seconds.1,"input_preparation":preparation_seconds,"execution":execution_seconds},
        "assurance":["generic-structural-correspondence","local-host-driver","external-backend-contracts","not-production-setup"]}),
    )
}
fn stop_details(stop: &Stop) -> Json {
    let (kind, detail) = match &stop.kind {
        StopKind::Incomplete => ("incomplete", None),
        StopKind::Explicit(reason) => ("explicit", Some(reason.as_str())),
        StopKind::Backend(error) => ("backend", Some(error.code.as_str())),
        StopKind::Limit => ("limit", None),
        StopKind::Cancelled => ("cancelled", None),
    };
    json!({"origin":stop.origin.json(), "role":stop.role, "site":stop.site,
        "kind":kind,"detail":detail,
        "cleanup_errors":stop.cleanup_errors.iter().map(|e| &e.code).collect::<Vec<_>>()})
}
fn public_output<B: HostBackend>(backend: &B, value: &Value) -> Result<Json> {
    match value {
        // Diagnostic private result, never a wire or ingress encoding.
        Value::ResourceUnit(unit) => Ok(json!([
            "private",
            format!("resource_unit:{}", unit.domain().name())
        ])),
        Value::Bool(b) => Ok(json!(["bool", b])),
        Value::Index(n) => Ok(json!(["index", n])),
        Value::Indices(ns) => Ok(json!(["indices", ns.as_ref()])),
        Value::Field(v) => Ok(json!([value.ty().name(), v.to_string()])),
        Value::Rng(_)
        | Value::Nonce(_)
        | Value::ProverKey(_)
        | Value::VerifierKey(_)
        | Value::OpeningState(_)
        | Value::OracleState(_)
        | Value::OracleStates(..) => Ok(json!(["private", value.ty().name()])),
        _ => Ok(json!([
            "wire",
            value.ty().name(),
            backend
                .encode(value)
                .map_err(|e| e.to_string())?
                .iter()
                .map(|b| format!("{b:02x}"))
                .collect::<String>()
        ])),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use zkc_runtime::interactive::{ArtifactFormat, Origin, PathElement};

    #[test]
    fn stop_record_retains_dynamic_origin_and_cleanup_failures() {
        let stop = Stop {
            origin: Origin {
                format: ArtifactFormat::ExplicitBindings,
                session: "session".into(),
                entry: "main".into(),
                instance: "child".into(),
                path: vec![
                    PathElement::Loop {
                        site: "round".into(),
                        iteration: 3,
                    },
                    PathElement::Call {
                        site: "check".into(),
                        instance: "child".into(),
                    },
                ],
            },
            role: "V".into(),
            site: Some("guard".into()),
            kind: StopKind::Backend(BackendError::new("rejected:require")),
            cleanup_errors: vec![
                BackendError::new("leave-local"),
                BackendError::new("leave-parent"),
            ],
        };
        assert_eq!(
            stop_details(&stop),
            json!({
                "origin":["zkc.origin/2","session","main","child",[["loop","round","3"],["call","check","child"]]],
                "role":"V","site":"guard","kind":"backend","detail":"rejected:require",
                "cleanup_errors":["leave-local","leave-parent"]
            })
        );
    }
}
