use super::*;
/// Complete ordinary outcome, including backend custody after cleanup. Failures
/// in observations, retirement or output encoding never replace execution state.
pub struct HostReport {
    pub execution: Option<Report<NativeBackend>>,
    pub unstarted: Vec<(String, NativeBackend)>,
    pub phase: &'static str,
    pub failure: Option<String>,
    pub resources: Vec<Json>,
    pub cleanup_errors: Vec<Json>,
    identity: String,
    session: String,
    limits: Json,
    layout: Json,
}
impl HostReport {
    pub(super) fn new(host: &RunHost, session: &str) -> Self {
        Self {
            execution: None,
            unstarted: Vec::new(),
            phase: "issuance",
            failure: None,
            resources: Vec::new(),
            cleanup_errors: Vec::new(),
            identity: host.identity.clone(),
            session: session.into(),
            limits: host.limits.record(),
            layout: host.layout(),
        }
    }
    pub(super) fn finalize(
        &mut self,
        registry: &ServiceRegistry,
        capabilities: &BTreeMap<String, Vec<(usize, Capability)>>,
        services: &BTreeMap<String, Vec<ServiceReference>>,
    ) {
        if let Some(execution) = &self.execution {
            for role in &execution.roles {
                let backend = &execution
                    .backends
                    .iter()
                    .find(|(name, _)| name == &role.role)
                    .expect("role custody")
                    .1;
                if let Err(code) = check_units(backend, &role.outputs, &mut Default::default()) {
                    self.cleanup_errors
                        .push(json!({"role":role.role,"kind":"returned-unit","code":code}));
                }
            }
        }
        let retained: BTreeMap<_, _> = self
            .execution
            .as_ref()
            .map(|r| {
                r.roles
                    .iter()
                    .map(|role| (role.role.clone(), unit_count(&role.outputs)))
                    .collect()
            })
            .unwrap_or_default();
        let backends = match &mut self.execution {
            Some(r) => &mut r.backends,
            None => &mut self.unstarted,
        };
        for (role, backend) in backends {
            for (i, token) in &capabilities[role] {
                match backend.retire(token) {
                    Ok(state) => self.resources.push(json!({"role":role,"kind":"capability","index":i,
                        "state":{"generation":state.generation,"transitions":state.draw_count,"budget":state.budget,"stage":state.stage}})),
                    Err(error)=>self.cleanup_errors.push(json!({"role":role,"kind":"capability","index":i,"code":error.code})),
                }
            }
            for (i, reference) in services[role].iter().enumerate() {
                match registry.retire(reference) {
                    Ok(state)=>self.resources.push(json!({"role":role,"kind":"service","index":i,
                        "leased":state.leased,"poisoned":state.poisoned,"state":state.state.map(|s|json!({
                        "generation":s.generation,"transitions":s.draw_count,"budget":s.budget,"stage":s.stage}))})),
                    Err(error)=>self.cleanup_errors.push(json!({"role":role,"kind":"service","index":i,"code":error.code})),
                }
            }
            if backend.active_frames() != 0
                || backend.live_resource_units() != retained.get(role).copied().unwrap_or(0)
            {
                self.cleanup_errors
                    .push(json!({"role":role,"code":"bundle-incomplete-cleanup"}));
            }
        }
    }
    pub fn json(&self) -> Json {
        self.json_with_outputs(true)
    }
    /// Resource and control observations without encoding returned values.
    pub fn diagnostics(&self) -> Json {
        self.json_with_outputs(false)
    }
    fn json_with_outputs(&self, include_outputs: bool) -> Json {
        let mut diagnostics = self.cleanup_errors.clone();
        let mut result = json!({"format":"zkc.bundle-result/0","status":if self.phase=="execution"{"executed"}else{"setup-failed"},"phase":self.phase,"acceptance":null,
            "bundle_sha256":self.identity,"session":self.session,"limits":self.limits,"layout":self.layout,
            "failure":self.failure,"resources":self.resources,"roles":[],"outcome":null,
            "assurance":["authenticated-supplied-schedule","session-freshness-host-obligation","local-only-public-inputs","registry-selected-receive-keys"]});
        if let Some(execution) = &self.execution {
            result["outcome"] = match &execution.outcome {
                Outcome::Completed => json!(["completed"]),
                Outcome::ParticipantStopped { role } => json!(["participant-stopped", role]),
                Outcome::ReturnedEarly { role, blocked } => {
                    json!(["returned-early", role, blocked])
                }
                Outcome::DriverFailed(failure) => json!([
                    "driver-failed",
                    format!("{:?}", failure.kind),
                    bounded(&failure.detail)
                ]),
                Outcome::HostCancelled(reason) => json!(["host-cancelled", bounded(reason)]),
            };
            result["wire"] = json!({"sends":execution.wire.sends,"receives":execution.wire.receives,
                "sent_bytes":execution.wire.sent_bytes,"replacement_bytes":execution.wire.replacement_bytes});
            result["reached"] = json!(execution.reached.iter().map(|r|json!({"role":r.step.role,"instruction":r.step.instruction,
                "anchor":r.step.anchor,"iterations":r.iterations,"progress":format!("{:?}",r.progress),
                "loop_count":r.loop_count,"loop_started":r.loop_started,"sent_bytes":r.sent_bytes,
                "receive_completion":r.receive_completion.as_ref().map(|v|format!("{v:?}"))})).collect::<Vec<_>>());
            result["pending"] = json!(execution.pending.as_ref().map(|p|json!({"send_step":p.send_step,
                "receive_step":p.receive_step,"original_bytes":p.original_bytes,"bytes":p.bytes.len()})));
            result["roles"] = json!(execution.roles.iter().map(|role| {
                let backend = &execution.backends.iter().find(|(name,_)|name==&role.role).expect("role custody").1;
                let outputs = role.outputs.iter().enumerate().filter(|_|include_outputs).map(|(i,value)| {
                    if !zkc_backends::has_native_wire(&value.physical_type()) {
                        return json!(["private",value.physical_type().spelling()]);
                    }
                    match backend.encode_native_value(value) {
                        Ok(bytes)=>json!(["wire",value.physical_type().spelling(),hex(&bytes)]),
                        Err(error)=>{
                            diagnostics.push(json!({"role":role.role,"output":i,"kind":"output","code":error.to_string()}));
                            json!(["unavailable",error.to_string()])
                        }
                    }
                }).collect::<Vec<_>>();
                json!({"role":role.role,"before":state(&role.before),"after":state(&role.after),"cancelled":role.cancelled,
                    "usage":role.usage.map(|u|json!({"instructions":u.instructions,"iterations":u.iterations,
                        "live_values":u.live_values,"live_value_bytes":u.live_value_bytes,"total_value_bytes":u.total_value_bytes})),
                    "external_work":backend.external_work_spent(),"active_frames":backend.active_frames(),
                    "live_resource_units":backend.live_resource_units(),"retained_output_units":unit_count(&role.outputs),"outputs":if include_outputs {Some(outputs)} else {None},
                    "return_at":role.return_at.as_ref().map(|(o,s)|json!({"origin":o.json(),"site":s}))})
            }).collect::<Vec<_>>());
        } else {
            result["outcome"] = json!(["setup-failed", self.failure]);
            result["roles"] = json!(self.unstarted.iter().map(|(role,backend)|json!({"role":role,"started":false,
                "external_work":backend.external_work_spent(),"active_frames":backend.active_frames(),
                "live_resource_units":backend.live_resource_units()})).collect::<Vec<_>>());
        }
        if !diagnostics.is_empty() {
            result["status"] = json!("diagnostic-failed");
        }
        result["diagnostics"] = json!(diagnostics);
        result
    }
}
fn bounded(text: &Text) -> Json {
    json!({"text":text.text,"omitted_bytes":text.omitted_bytes})
}
fn state(state: &State) -> Json {
    match state {
        State::NotStarted => json!(["not-started"]),
        State::Returned => json!(["returned"]),
        State::ReturnIf { site } => json!(["return-if", site]),
        State::Unpolled { kind, site } => json!(["unpolled", kind.map(|k| format!("{k:?}")), site]),
        State::Pending { kind, site } => json!(["pending", format!("{kind:?}"), site]),
        State::Stopped(stop) => json!(["stopped",{"origin":stop.origin.json(),"site":stop.site,
            "cause":match &stop.cause {
                StopCause::Decode(r)=>json!(["decode",r.as_str()]),
                StopCause::Explicit(t)=>json!(["explicit",bounded(t)]),StopCause::Backend(t)=>json!(["backend",bounded(t)]),
                StopCause::Limit=>json!(["limit"]),StopCause::Cancelled=>json!(["cancelled"]),
            },"local":stop.local.as_ref().map(|l|json!({"site":l.site,"function":l.function,"instruction":l.instruction})),
            "cleanup_errors":stop.cleanup_errors.iter().map(bounded).collect::<Vec<_>>(),"omitted_errors":stop.omitted_errors}]),
    }
}

fn unit_count(values: &[Value]) -> usize {
    values
        .iter()
        .map(|value| match value {
            Value::ResourceUnit(_) => 1,
            Value::Variant(v) => unit_count(v.payload()),
            Value::Sequence(v) => unit_count(v.elements()),
            _ => 0,
        })
        .sum()
}

// Identity and current generation matter as well as the residual count. The
// caller retains these units, so observation must not consume or retire them.
pub(super) fn check_units(
    backend: &NativeBackend,
    values: &[Value],
    seen: &mut std::collections::BTreeSet<u64>,
) -> Result<()> {
    for value in values {
        match value {
            Value::ResourceUnit(unit) => {
                zkc_runtime::interactive::Backend::validate_value(backend, value)
                    .map_err(|e| e.to_string())?;
                let state = backend
                    .observe(unit.capability())
                    .map_err(|e| e.to_string())?;
                if !seen.insert(state.issued_id) {
                    return Err("bundle-returned-unit-alias".into());
                }
            }
            Value::Variant(v) => check_units(backend, v.payload(), seen)?,
            Value::Sequence(v) => check_units(backend, v.elements(), seen)?,
            _ => {}
        }
    }
    Ok(())
}
