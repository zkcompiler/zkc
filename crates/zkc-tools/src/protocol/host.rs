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
    Action, Admitted, BackendError, EntryRole, Identity, Runner, Stop, StopKind, admit_physical,
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
    fn issue_root(&mut self, identity: Identity, domain: Domain, budget: u64) -> Result<Value>;
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
    fn issue_root(&mut self, identity: Identity, domain: Domain, budget: u64) -> Result<Value> {
        self.issue_rng_for(identity, domain, budget)
            .map_err(|e| e.to_string())
    }
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
    roots: BTreeMap<String, (String, u64)>,
}
fn config(value: &Json) -> Result<Config<'_>> {
    let root = list(value)?;
    match root.first().and_then(Json::as_str) {
        Some("zkc.run/2") if matches!(root.len(), 6 | 7) => (),
        _ => return Err("host-version".into()),
    };
    let mut roles = BTreeMap::new();
    for r in list(&root[4])? {
        let record = array(r, 4)?;
        if roles.insert(text(&record[0])?.into(), record).is_some() {
            return Err("host-duplicate-role".into());
        }
    }
    let mut roots = BTreeMap::new();
    if root.len() == 7 {
        let records = list(&root[6])?;
        if records.is_empty() || records.len() > 4096 {
            return Err("host-root-records".into());
        }
        for value in records {
            let record = array(value, 3)?;
            let owner = text(&record[0])?;
            let name = text(&record[1])?;
            if !roles.contains_key(owner) || name.is_empty() || name.len() > 128 {
                return Err("host-root-binding".into());
            }
            if roots
                .insert(name.into(), (owner.into(), natural(&record[2])?))
                .is_some()
            {
                return Err("host-duplicate-root".into());
            }
        }
    }
    Ok(Config {
        entry: text(&root[1])?,
        session: text(&root[2])?,
        setup: list(&root[3])?,
        roles,
        receives: list(&root[5])?,
        roots,
    })
}

/// A bounded local development host. Protocol algorithms come exclusively from
/// the independently checked compiler artifact. This command issues OS-random
/// services and explicitly selected development setup; it has no fixture tape.
pub fn run(args: &[String]) -> Result<Json> {
    let (source_args, subject_pin) = match args {
        [_, _, _, _] => (args, None),
        [_, _, _, _, pin] => (&args[..4], Some(pin)),
        _ => {
            return Err(
                "usage: zkc run-protocol SOURCE PARTICIPANTS INPUTS CHECKER [SUBJECT_SHA256]"
                    .into(),
            );
        }
    };
    let [source_path, candidate_path, inputs_path, checker_path] = source_args else {
        unreachable!()
    };
    let mut source = read(source_path)?;
    let candidate = read(candidate_path)?;
    let input: Json = serde_json::from_slice(&read(inputs_path)?).map_err(|_| "host-json")?;
    let cfg = config(&input)?;
    let mut checker = ParticipantChecker::new(checker_path).map_err(|_| "checker-io")?;
    let mut mathematical_identity = None;
    if source.iter().find(|b| !b.is_ascii_whitespace()) == Some(&b'{') {
        let pin = subject_pin.ok_or("host-mathematical-source-pin-required")?;
        let capture: Json = serde_json::from_slice(&source).map_err(|_| "host-json")?;
        if capture.get("format").and_then(Json::as_str) != Some("zkc.mathematical-placement/1") {
            return Err("host-mathematical-capture".into());
        }
        let located =
            serde_json::to_vec(capture.get("located").ok_or("host-mathematical-capture")?)
                .map_err(|_| "host-json")?;
        mathematical_identity = Some(json!({
            "source": pin,
            "target": capture.get("witness").and_then(|w| w.get("target"))
                .ok_or("host-mathematical-capture")?,
        }));
        checker = checker.with_mathematical_capture(source, pin.clone());
        source = located;
    } else if subject_pin.is_some() {
        return Err("host-mathematical-source-pin-unexpected".into());
    }
    let mut result = setups::run(&source, &candidate, &cfg, &checker)?;
    // Admission completed the source/target hash obligations before execution.
    if let Some(identity) = mathematical_identity {
        result["mathematical"] = identity;
        result["assurance"][0] = json!("mathematical-structural-correspondence");
    }
    Ok(result)
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
    let mapping = admitted.source_map().ok_or("host-source-map")?;
    if cfg.roots.len() != mapping.roots.len()
        || mapping.roots.iter().any(|root| {
            cfg.roots
                .get(&root.root)
                .is_none_or(|(owner, _)| owner != &root.role)
        })
    {
        return Err("host-root-set".into());
    }
    let mut runners = BTreeMap::new();
    let mut ingress_stops = BTreeMap::new();
    let mut observed_resources = BTreeMap::new();
    let mut root_handles = BTreeMap::new();
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
        let roots: Vec<_> = mapping
            .roots
            .iter()
            .filter(|root| root.instance == role.instance && root.role == role.role)
            .collect();
        if ports.len() != supplied.len() || ports.len() + roots.len() != role.inputs.len() {
            return Err("host-input-count".into());
        }
        let mut inputs = Vec::new();
        for ((source_name, ty), (target_name, target_type)) in
            ports.iter().zip(&role.inputs[..ports.len()])
        {
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
        let mut value_role = role.clone();
        value_role.inputs.truncate(ports.len());
        let mut inputs = backend.inputs(&value_role, &bytes, &bindings)?;
        let mut issued = BTreeMap::new();
        for root in roots {
            let (_, budget) = cfg.roots.get(&root.root).ok_or("host-root-set")?;
            // Direct issuance cannot be referenced by a user input's host label.
            let value = backend.issue_root(
                root.state_type.logical().identity(),
                Domain::new(&role.role, cfg.session, cfg.entry, Some(&role.instance)),
                *budget,
            )?;
            issued.insert(root.root.clone(), value.clone());
            inputs.push(value);
        }
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
        root_handles.insert(role.role.clone(), issued);
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
            let outputs = (|| -> Result<BTreeMap<String, Vec<Json>>> {
                let mut outputs = BTreeMap::new();
                for (role, values) in values {
                    let runner = runners.get(&role).ok_or("host-result-role")?;
                    let roots: Vec<_> = mapping
                        .roots
                        .iter()
                        .filter(|root| {
                            root.role == role && root.instance == runner.root_origin().instance
                        })
                        .collect();
                    for root in &roots {
                        let Some(Value::Rng(successor)) = values.get(root.output) else {
                            return Err("host-root-successor".into());
                        };
                        let Some(Value::Rng(initial)) =
                            root_handles.get(&role).and_then(|rs| rs.get(&root.root))
                        else {
                            return Err("host-root-issuance".into());
                        };
                        let state = runner
                            .backend()
                            .observe(successor)
                            .map_err(|e| e.to_string())?;
                        if successor.issued_id() != initial.issued_id()
                            || successor.generation() != state.generation
                        {
                            return Err("host-root-successor".into());
                        }
                    }
                    outputs.insert(
                        role.clone(),
                        values
                            .iter()
                            .enumerate()
                            .filter(|(i, _)| !roots.iter().any(|root| root.output == *i))
                            .map(|(_, v)| public_output(runner.backend(), v))
                            .collect::<Result<Vec<_>>>()?,
                    );
                }
                Ok(outputs)
            })();
            match outputs {
                Ok(outputs) => json!(["returned", outputs]),
                Err(error) => json!(["failed", error]),
            }
        }
        JointOutcome::Stopped(stop) => {
            json!(["stopped", stop.role, stop.site, format!("{:?}", stop.kind)])
        }
        JointOutcome::Failed(error) => json!(["failed", error]),
    };
    let mut resources = Vec::new();
    let mut root_resources = Vec::new();
    let mut observation_errors = Vec::new();
    let mut usage = BTreeMap::new();
    let mut ingress = BTreeMap::new();
    for (role, runner) in &runners {
        for (name, value) in &root_handles[role] {
            let state = match value {
                Value::Rng(token) => runner.backend().observe(token),
                _ => Err(BackendError::new("host-root-issuance")),
            };
            record_observation(
                &mut root_resources,
                &mut observation_errors,
                "root",
                role,
                name,
                state,
            );
        }
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
                record_observation(
                    &mut resources,
                    &mut observation_errors,
                    "resource",
                    role,
                    name,
                    runner.backend().observe(token),
                );
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
    let outcome = if !observation_errors.is_empty() && outcome[0] == "returned" {
        json!(["failed", "host-resource-observation"])
    } else {
        outcome
    };
    Ok(
        json!({"format":"zkc.run-result/1", "profile":Json::Null,"entry":cfg.entry,"session":cfg.session,
        "outcome":outcome,"resources":resources,"root_resources":root_resources,"observation_errors":observation_errors,"usage":usage,"ingress":ingress,"cancelled_roles":report.cancelled.iter().map(|s| &s.role).collect::<Vec<_>>(),
        "stop":stopped,"cancellations":report.cancelled.iter().map(stop_details).collect::<Vec<_>>(),
        "wire":{"messages":report.wire.messages,"payload_bytes":report.wire.payload_bytes,"envelope_bytes":report.wire.envelope_bytes},
        "seconds":{"admission":seconds.0,"development_setup":seconds.1,"input_preparation":preparation_seconds,"execution":execution_seconds},
        "assurance":["generic-structural-correspondence","local-host-driver","external-backend-contracts","not-production-setup"]}),
    )
}
// Observe every retained issuer handle even if another observation or returned
// value projection failed. An unavailable observation is explicit, never zero.
fn record_observation(
    values: &mut Vec<Json>,
    errors: &mut Vec<Json>,
    kind: &str,
    role: &str,
    name: &str,
    state: std::result::Result<CapabilityObservation, BackendError>,
) {
    match state {
        Ok(state) => values.push(json!([
            role,
            name,
            state.generation,
            state.draw_count,
            state.budget,
            state.stage
        ])),
        Err(error) => errors.push(json!([kind, role, name, error.to_string()])),
    }
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
    fn observation_failure_keeps_other_issuer_states() {
        let mut states = Vec::new();
        let mut errors = Vec::new();
        record_observation(
            &mut states,
            &mut errors,
            "root",
            "P",
            "failed",
            Err(BackendError::new("issuer-unavailable")),
        );
        record_observation(
            &mut states,
            &mut errors,
            "root",
            "P",
            "completed",
            Ok(CapabilityObservation {
                issued_id: 7,
                generation: 2,
                draw_count: 2,
                budget: 0,
                stage: "rng",
            }),
        );
        assert_eq!(states, vec![json!(["P", "completed", 2, 2, 0, "rng"])]);
        assert_eq!(errors.len(), 1);
        assert_eq!(
            &errors[0].as_array().unwrap()[..3],
            &[json!("root"), json!("P"), json!("failed")]
        );
        assert!(
            errors[0][3]
                .as_str()
                .unwrap()
                .contains("issuer-unavailable")
        );
    }

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
