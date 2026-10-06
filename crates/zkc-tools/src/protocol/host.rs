use super::{
    DriverLimits, JointOutcome, JointReport, LocalTransport, MessageDecoder, ParticipantChecker,
    Schedule, WireBackend, drive_with_decoder,
};
use crate::host::admission::ResourceInput;
use serde_json::{Value as Json, json};
use std::{collections::BTreeMap, sync::Arc, time::Instant};
use zkc_backends::{
    Capability, CapabilityObservation, Domain, EntryPolicy, InputBindings, Keys, NativeBackend,
    Policy, PublicInputs, Value,
};
use zkc_runtime::interactive::{
    Action, Admitted, BackendError, EntryRole, Runner, Stop, StopKind, admit_physical,
};

mod inputs;
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
    fn issue(&mut self, input: ResourceInput, domain: Domain) -> Result<Value>;
    fn prepare(
        &self,
        role: &EntryRole,
        bytes: &[u8],
        types: &BTreeMap<String, zkc_runtime::interactive::PhysicalType>,
    ) -> Result<zkc_backends::InputPlan>;
    fn check_entry(
        &self,
        plan: &zkc_backends::InputPlan,
        role: &EntryRole,
        bindings: &InputBindings,
    ) -> Result<()>;
    fn retire(
        &mut self,
        token: &Capability,
    ) -> std::result::Result<CapabilityObservation, BackendError>;
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
    fn issue(&mut self, input: ResourceInput, domain: Domain) -> Result<Value> {
        match input.kind {
            zkc_runtime::interactive::Type::Rng => {
                self.issue_rng_for(input.field, domain, input.budget)
            }
            zkc_runtime::interactive::Type::Nonce => {
                self.issue_nonce_for(input.field, domain, input.budget)
            }
            _ => return Err("host-service-profile".into()),
        }
        .map_err(|e| e.to_string())
    }
    fn prepare(
        &self,
        role: &EntryRole,
        bytes: &[u8],
        types: &BTreeMap<String, zkc_runtime::interactive::PhysicalType>,
    ) -> Result<zkc_backends::InputPlan> {
        self.prepare_inputs(role, bytes, types)
            .map_err(|e| e.to_string())
    }
    fn check_entry(
        &self,
        plan: &zkc_backends::InputPlan,
        role: &EntryRole,
        bindings: &InputBindings,
    ) -> Result<()> {
        plan.check_entry(self, role, bindings)
            .map_err(|e| e.to_string())
    }
    fn retire(
        &mut self,
        token: &Capability,
    ) -> std::result::Result<CapabilityObservation, BackendError> {
        self.retire(token)
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
    schedule_work: u64,
    driver_limits: DriverLimits,
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
        schedule_work: 1_000_000,
        driver_limits: DriverLimits::default(),
    })
}

/// A bounded local development host. Protocol algorithms come exclusively from
/// the independently checked compiler artifact. This command issues OS-random
/// services and explicitly selected development setup; it has no fixture tape.
pub fn run(args: &[String]) -> Result<Json> {
    let [
        source_path,
        candidate_path,
        inputs_path,
        checker_path,
        options @ ..,
    ] = args
    else {
        return Err(
            "usage: zkc run-protocol SOURCE PARTICIPANTS INPUTS CHECKER [--limits=LIMITS]".into(),
        );
    };
    let source = read(source_path)?;
    let candidate = read(candidate_path)?;
    let input: Json = serde_json::from_slice(&read(inputs_path)?).map_err(|_| "host-json")?;
    let mut cfg = config(&input)?;
    if !options.is_empty() {
        let [option] = options else {
            return Err("host-option".into());
        };
        let path = option.strip_prefix("--limits=").ok_or("host-option")?;
        let bytes = crate::host::io::read_bounded(path, 4096).map_err(|_| "host-limits-read")?;
        let value: Json = serde_json::from_slice(&bytes).map_err(|_| "host-json")?;
        let row = array(&value, 4)?;
        if text(&row[0])? != "zkc.source-run-limits/1" {
            return Err("host-limits-format".into());
        }
        let size = |v| usize::try_from(natural(v)?).map_err(|_| "host-limits".to_owned());
        cfg.schedule_work = natural(&row[1])?;
        cfg.driver_limits = DriverLimits {
            message_bytes: size(&row[2])?,
            total_wire_bytes: size(&row[3])?,
        };
        if cfg.schedule_work > 1_000_000 || cfg.driver_limits != cfg.driver_limits.effective() {
            return Err("host-limits".into());
        }
    }
    let checker = ParticipantChecker::new(checker_path).map_err(|_| "checker-io")?;
    setups::run(&source, &candidate, &cfg, &checker)
}
fn execute<B: HostBackend, D: MessageDecoder<B>>(
    admitted: &Admitted,
    cfg: &Config<'_>,
    keys: &BTreeMap<String, Keys>,
    seconds: (f64, f64),
    declarations: inputs::Declarations,
    factory: impl Fn(&EntryRole) -> Result<B>,
    decoder: &D,
) -> Result<Json> {
    let inputs::Declarations {
        mut schedule,
        roles,
    } = declarations;
    let preparation = Instant::now();
    let mut prepared = inputs::prepare(roles, keys, factory)?;
    let mut runners = BTreeMap::new();
    let mut ingress_stops = BTreeMap::new();
    let mut phase = "issuance";
    let mut failure = inputs::issue(&mut prepared).err();
    if failure.is_none() {
        phase = "construction";
        for role in &mut prepared {
            let backend = role.backend.take().expect("prepared backend");
            match Runner::new(
                admitted,
                cfg.entry,
                &role.role.role,
                cfg.session,
                backend,
                std::mem::take(&mut role.values),
            ) {
                Ok(mut runner) => {
                    // Preserve the source host's existing ingress contract: an
                    // ingress stop does not skip construction of later roles.
                    let stop = if runner.is_terminal() {
                        match runner.poll() {
                            Action::Stopped(stop) => Some(stop_details(&stop)),
                            _ => None,
                        }
                    } else {
                        None
                    };
                    ingress_stops.insert(role.role.role.clone(), stop);
                    runners.insert(role.role.role.clone(), runner);
                }
                Err(error) => {
                    role.load_usage = Some(error.usage);
                    role.backend = Some(error.backend);
                    failure = Some(error.error.to_string());
                    break;
                }
            }
        }
    }
    let preparation_seconds = preparation.elapsed().as_secs_f64();
    let start = Instant::now();
    let report = if let Some(error) = failure {
        let mut cancelled = Vec::new();
        for runner in runners.values_mut() {
            if !runner.is_terminal() {
                runner.cancel();
                if let Action::Stopped(stop) = runner.poll() {
                    cancelled.push(stop);
                }
            }
        }
        JointReport {
            outcome: JointOutcome::Failed(error),
            wire: Default::default(),
            limits: cfg.driver_limits,
            cancelled,
        }
    } else {
        phase = "execution";
        drive_with_decoder(
            &mut schedule,
            &mut runners,
            &mut LocalTransport,
            decoder,
            cfg.driver_limits,
        )
    };
    let execution_seconds = start.elapsed().as_secs_f64();
    let stopped = match &report.outcome {
        JointOutcome::Stopped(stop) => Some(stop_details(stop)),
        _ => None,
    };
    let mut diagnostics = Vec::new();
    let outcome = match report.outcome {
        JointOutcome::Returned(values) => {
            let mut outputs = BTreeMap::new();
            for (role, values) in values {
                outputs.insert(
                    role.clone(),
                    values
                        .iter()
                        .enumerate().map(|(index, v)| match public_output(runners[&role].backend(), v) {
                            Ok(value) => value,
                            Err(error) => {
                                diagnostics.push(json!({"role":role,"output":index,"kind":"output","code":error}));
                                json!(["unavailable",error])
                            }
                        }).collect::<Vec<_>>(),
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
            role.clone(),
            json!({
                "selected_parameters": runner.selected_parameters(),
                "stop": ingress_stops[role],
                "events": runner.ingress_actions().iter().map(|action| json!({
                    "origin": action.cut.origin.json(), "role": action.cut.role,
                    "site": action.cut.site, "function": action.function
                })).collect::<Vec<_>>()
            }),
        );
        let u = runner.usage();
        usage.insert(
            role.clone(),
            json!({"instructions":u.instructions,"calls":u.calls,"iterations":u.iterations,
            "live_value_bytes":u.live_value_bytes,"total_value_bytes":u.total_value_bytes,
            "external_work_spent":runner.backend().external_work_spent(),
            "live_resource_units":runner.backend().live_resource_units()}),
        );
    }
    let mut backends: BTreeMap<_, _> = runners
        .into_iter()
        .map(|(name, runner)| (name, runner.into_backend()))
        .collect();
    let mut retired = Vec::new();
    let mut roles = BTreeMap::new();
    for role in &mut prepared {
        let name = &role.role.role;
        roles.insert(name.clone(), json!({"started":backends.contains_key(name)}));
        let backend = match backends.get_mut(name) {
            Some(backend) => backend,
            None => role.backend.as_mut().expect("unstarted custody"),
        };
        if !usage.contains_key(name) {
            let u = role.load_usage.unwrap_or_default();
            usage.insert(name.clone(), json!({"instructions":u.instructions,"calls":u.calls,"iterations":u.iterations,
                "live_value_bytes":u.live_value_bytes,"total_value_bytes":u.total_value_bytes,
                "external_work_spent":backend.external_work_spent(),"live_resource_units":backend.live_resource_units()}));
        }
        for (label, token) in &role.handles {
            match backend.observe(token) {
                Ok(state) => resources.push(json!([
                    name,
                    label,
                    state.generation,
                    state.draw_count,
                    state.budget,
                    state.stage
                ])),
                Err(error) => {
                    resources.push(json!([name, label, "observation-unavailable", error.code]));
                    diagnostics.push(json!({"role":name,"resource":label,"kind":"observation","code":error.code}));
                }
            }
            match backend.retire(token) {
                Ok(state) => retired.push(json!([
                    name,
                    label,
                    state.generation,
                    state.draw_count,
                    state.budget,
                    state.stage
                ])),
                Err(error) => diagnostics.push(
                    json!({"role":name,"resource":label,"kind":"retirement","code":error.code}),
                ),
            }
        }
    }
    Ok(
        json!({"format":"zkc.run-result/2", "status":if phase!="execution" {"setup-failed"} else if !diagnostics.is_empty() {"diagnostic-failed"} else {"executed"}, "phase":phase,"roles":roles,"diagnostics":diagnostics,"retired_resources":retired, "profile":Json::Null,"entry":cfg.entry,"session":cfg.session,
        "outcome":outcome,"resources":resources,"usage":usage,"ingress":ingress,"cancelled_roles":report.cancelled.iter().map(|s| &s.role).collect::<Vec<_>>(),
        "stop":stopped,"cancellations":report.cancelled.iter().map(stop_details).collect::<Vec<_>>(),
        "limits":{"schedule_work":cfg.schedule_work,"message_bytes":report.limits.message_bytes,"total_wire_bytes":report.limits.total_wire_bytes},
        "wire":{"sends":report.wire.sends,"encoded_bytes":report.wire.encoded_bytes,"transferred_bytes":report.wire.transferred_bytes,"messages":report.wire.messages,"payload_bytes":report.wire.payload_bytes,"envelope_bytes":report.wire.envelope_bytes},
        "seconds":{"admission":seconds.0,"development_setup":seconds.1,"input_preparation":preparation_seconds,"execution":execution_seconds},
        "assurance":["generic-structural-correspondence","local-host-driver","external-backend-contracts","not-production-setup"]}),
    )
}
fn stop_details(stop: &Stop) -> Json {
    let (kind, detail) = match &stop.kind {
        StopKind::Incomplete => ("incomplete", None),
        StopKind::Decode(reason) => ("decode", Some(reason.as_str())),
        StopKind::Explicit(reason) => ("explicit", Some(reason.as_str())),
        StopKind::Backend(error) => ("backend", Some(error.code.as_str())),
        StopKind::Limit => ("limit", None),
        StopKind::Cancelled => ("cancelled", None),
    };
    json!({"origin":stop.origin.json(), "role":stop.role, "site":stop.site, "local":stop.local.as_ref().map(|l| json!({"site":l.site,"function":l.function,"instruction":l.instruction})),
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
            local: Some(Box::new(zkc_runtime::interactive::LocalContext {
                site: "check".into(),
                function: "verify".into(),
                instruction: Some("guard".into()),
            })),
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
                "cleanup_errors":["leave-local","leave-parent"],"local":{"site":"check","function":"verify","instruction":"guard"}
            })
        );
    }
}

#[cfg(test)]
mod lifecycle;
