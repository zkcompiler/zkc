use super::*;
/// Complete ordinary outcome, including backend custody after cleanup. Failures
/// in observations, retirement or output encoding never replace execution state.
pub struct HostReport {
    pub execution: Option<Report<CpuBackend>>,
    pub unstarted: Vec<(String, CpuBackend)>,
    pub phase: &'static str,
    pub failure: Option<String>,
    pub resources: Vec<Json>,
    /// Known service draws observed during retirement, before JSON rendering.
    pub(crate) service_draws: u64,
    pub cleanup_errors: Vec<Json>,
    identity: String,
    session: String,
    limits: Json,
    layout: Json,
    invocation: zkc_runtime::vm::ExecutionLedger,
    /// The returned values' live allowance after the Host took custody.
    outputs_live: Option<zkc_runtime::vm::LiveReservation>,
}
impl HostReport {
    pub(super) fn new(
        host: &RunHost,
        session: &str,
        invocation: zkc_runtime::vm::ExecutionLedger,
    ) -> Self {
        Self {
            execution: None,
            unstarted: Vec::new(),
            phase: "issuance",
            failure: None,
            resources: Vec::new(),
            service_draws: 0,
            cleanup_errors: Vec::new(),
            identity: host.identity.clone(),
            session: session.into(),
            limits: host.limits.record(),
            layout: host.layout(),
            invocation,
            outputs_live: None,
        }
    }
    /// Take custody of the runners' returned values in the invocation root.
    /// Standalone runners kept them under their own budgets, which end with
    /// the runners; custody passes without a new allocation, so the root
    /// reserves their live bytes without a fresh charge. Runners that shared
    /// the root keep their own reservations with the values. When the root
    /// cannot hold them, the report releases the values and records
    /// `bundle-output-limit`. Cleanup observations precede this step.
    pub(super) fn retain_outputs(&mut self) {
        let Some(execution) = &mut self.execution else {
            return;
        };
        match self
            .invocation
            .reserve_live(execution.unreserved_output_bytes())
        {
            Ok(live) => self.outputs_live = Some(live),
            Err(_) => {
                execution.release_outputs();
                self.failure
                    .get_or_insert_with(|| "bundle-output-limit".into());
            }
        }
    }
    /// The ledger that charged this invocation's Host-side inspection; result
    /// encoding charges it too.
    pub fn invocation_ledger(&self) -> &zkc_runtime::vm::ExecutionLedger {
        &self.invocation
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
                    Ok(state) => {
                        self.service_draws += state.state.as_ref().map_or(0, |s| s.draw_count);
                        self.resources.push(json!({"role":role,"kind":"service","index":i,
                            "leased":state.leased,"poisoned":state.poisoned,"state":state.state.map(|s|json!({
                            "generation":s.generation,"transitions":s.draw_count,"budget":s.budget,"stage":s.stage}))}));
                    }
                    Err(error) => self
                        .cleanup_errors
                        .push(json!({"role":role,"kind":"service","index":i,"code":error.code})),
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
    /// Bounded, payload-free child receipt without materializing the whole trace.
    pub fn diagnostics_summary(&self) -> Json {
        use crate::host::diagnostics::{text, values};
        let execution = self.execution.as_ref();
        // The actual stop is independent of the bounded observational prefix.
        let failure_role = execution.and_then(|e| {
            let Outcome::ParticipantStopped { role } = &e.outcome else {
                return None;
            };
            e.roles
                .get(*role)
                .map(|r| json!({"role":text(&r.role),"after":state_summary(&r.after)}))
        });
        json!({"phase":self.phase,"session":self.session,"failure":self.failure.as_deref().map(text),
            "cleanup_errors":values(self.cleanup_errors.iter()),
            "cleanup_omitted":self.cleanup_errors.len().saturating_sub(16),
            "resources":values(self.resources.iter()),
            "resource_count":self.resources.len(),
            "reached_count":execution.map_or(0,|e|e.reached.len()),
            "reached":execution.map(|e|e.reached.iter().take(16).map(|r|json!({"role":r.step.role,"instruction":r.step.instruction,"progress":format!("{:?}",r.progress)})).collect::<Vec<_>>()),
            "wire":execution.map(|e|json!({"sends":e.wire.sends,"receives":e.wire.receives,"sent_bytes":e.wire.sent_bytes,"replacement_bytes":e.wire.replacement_bytes})),
            "outcome":execution.map(|e|outcome_summary(&e.outcome)),
            "failure_role":failure_role,
            "role_count":execution.map_or(0,|e|e.roles.len()),
            "roles":execution.map(|e|e.roles.iter().take(16).map(|r| {
                let backend=&e.backends.iter().find(|(name,_)|name==&r.role).expect("role custody").1;
                json!({"role":text(&r.role),"before":state_summary(&r.before),"after":state_summary(&r.after),"cancelled":r.cancelled,
                    "usage":r.usage.map(|u|json!({"instructions":u.instructions,"iterations":u.iterations,
                        "live_values":u.live_values,"live_value_bytes":u.live_value_bytes,"total_value_bytes":u.total_value_bytes,"logical_bytes":u.logical_bytes})),
                    "external_work":backend.external_work_spent(),"ring_work":backend.ring_work_spent(),
                    "sequence_work":backend.sequence_work_spent(),"active_frames":backend.active_frames(),
                    "live_resource_units":backend.live_resource_units(),"retained_output_units":unit_count(&r.outputs)})
            }).collect::<Vec<_>>())})
    }
    /// Materialize readable native outputs without consuming returned
    /// resources. Each encoding is a new allocation: its conservative bound is
    /// charged to the invocation root before encoding, and the returned
    /// encoding holds its live allowance. An encoding the root cannot afford
    /// is `Unavailable` with `bundle-output-limit`.
    pub fn encode_outputs(&self) -> Vec<RoleOutputEncoding> {
        self.execution
            .as_ref()
            .into_iter()
            .flat_map(|e| &e.roles)
            .map(|role| {
                let backend = &self
                    .execution
                    .as_ref()
                    .unwrap()
                    .backends
                    .iter()
                    .find(|(name, _)| name == &role.role)
                    .expect("role custody")
                    .1;
                let mut retained = Vec::new();
                let values = role
                    .outputs
                    .iter()
                    .map(|value| {
                        let ty = value.physical_type();
                        if !backend.installation().supports_wire(&ty) {
                            return EncodedOutput::Private {
                                physical_type: ty.spelling(),
                            };
                        }
                        match zkc_runtime::host::wire::reserve_allocation(
                            Some(&self.invocation),
                            zkc_cpu::native_encoding_bound(value),
                        ) {
                            Ok(live) => retained.extend(live),
                            Err(_) => {
                                return EncodedOutput::Unavailable {
                                    code: "bundle-output-limit".into(),
                                };
                            }
                        }
                        match backend.encode_native_value(value) {
                            Ok(bytes) => EncodedOutput::Wire {
                                physical_type: ty.spelling(),
                                bytes,
                            },
                            Err(error) => EncodedOutput::Unavailable {
                                code: error.to_string(),
                            },
                        }
                    })
                    .collect();
                RoleOutputEncoding {
                    role: role.role.clone(),
                    values,
                    _retained: retained,
                }
            })
            .collect()
    }
    /// A bound of the rendered diagnostics: a fixed allowance for each reached
    /// row, role, resource and cleanup record, plus the strings and iteration
    /// numbers that each row's rendered control path repeats, and the retained
    /// layout and limit records.
    fn diagnostics_bound(&self) -> usize {
        const RECORD: usize = 2048;
        const ELEMENT: usize = 256;
        const ITERATION: usize = 64;
        let json = |value: &Json| value.to_string().len().saturating_mul(4);
        let rows = self.execution.as_ref().map_or(0, |execution| {
            execution
                .reached
                .iter()
                .map(|row| {
                    let path = row
                        .path
                        .iter()
                        .map(|element| {
                            use zkc_runtime::vm::PathElement;
                            ELEMENT
                                + match element {
                                    PathElement::Branch { site, alternative }
                                    | PathElement::Match { site, alternative } => {
                                        site.len() + alternative.len()
                                    }
                                    PathElement::Conditional { site, .. }
                                    | PathElement::For { site, .. }
                                    | PathElement::Loop { site, .. } => site.len(),
                                }
                        })
                        .fold(0usize, usize::saturating_add);
                    RECORD
                        .saturating_add(path)
                        .saturating_add(row.iterations.len().saturating_mul(ITERATION))
                })
                .fold(0usize, usize::saturating_add)
                .saturating_add(execution.roles.len().saturating_mul(RECORD))
        });
        let records = self
            .resources
            .len()
            .saturating_add(self.cleanup_errors.len())
            .saturating_add(self.unstarted.len())
            .saturating_mul(RECORD);
        rows.saturating_add(records)
            .saturating_add(json(&self.layout))
            .saturating_add(json(&self.limits))
            .saturating_add(RECORD)
    }
    /// Resource and control observations, without a command envelope or values.
    /// Rendering repeats each row's control path, so its bound is charged to
    /// the invocation root first. When the root cannot afford it, the result is
    /// the bounded summary with `"diagnostics": "omitted"`.
    pub fn diagnostics(&self) -> Json {
        let bound = self.diagnostics_bound();
        if self
            .invocation
            .charge(
                zkc_runtime::vm::WorkBudget {
                    instructions: 0,
                    iterations: 0,
                    logical_bytes: bound as u64,
                },
                bound,
            )
            .is_err()
        {
            let mut summary = self.diagnostics_summary();
            summary["diagnostics"] = json!("omitted");
            return summary;
        }
        let diagnostics = self.cleanup_errors.clone();
        let mut result = json!({"phase":self.phase,
            "bundle_sha256":self.identity,"session":self.session,"limits":self.limits,"layout":self.layout,
            "failure":self.failure,"resources":self.resources,"roles":[],"outcome":null});
        if let Some(execution) = &self.execution {
            result["outcome"] = outcome(&execution.outcome);
            result["wire"] = json!({"sends":execution.wire.sends,"receives":execution.wire.receives,
                "sent_bytes":execution.wire.sent_bytes,"replacement_bytes":execution.wire.replacement_bytes});
            result["reached"] = json!(execution.reached.iter().map(|r|json!({"role":r.step.role,"instruction":r.step.instruction,
                "anchor":r.step.anchor,"iterations":&*r.iterations,"progress":format!("{:?}",r.progress),
                "loop_count":r.loop_count,"loop_started":r.loop_started,
                "branch_alternative":r.branch_alternative,"branch_started":r.branch_started,
                "control_path":r.path.iter().map(path_element).collect::<Vec<_>>(),"sent_bytes":r.sent_bytes,
                "receive_completion":r.receive_completion.as_ref().map(|v|format!("{v:?}"))})).collect::<Vec<_>>());
            result["pending"] = json!(execution.pending.as_ref().map(|p|json!({"send_step":p.send_step,
                "receive_step":p.receive_step,"original_bytes":p.original_bytes,"bytes":p.bytes.len()})));
            result["roles"] = json!(execution.roles.iter().map(|role| {
                let backend = &execution.backends.iter().find(|(name,_)|name==&role.role).expect("role custody").1;
                json!({"role":role.role,"before":state(&role.before),"after":state(&role.after),"cancelled":role.cancelled,
                    "usage":role.usage.map(|u|json!({"instructions":u.instructions,"iterations":u.iterations,
                        "live_values":u.live_values,"live_value_bytes":u.live_value_bytes,"total_value_bytes":u.total_value_bytes,
                        "logical_bytes":u.logical_bytes})),
                    "external_work":backend.external_work_spent(),"ring_work":backend.ring_work_spent(),"active_frames":backend.active_frames(),
                    "live_resource_units":backend.live_resource_units(),"retained_output_units":unit_count(&role.outputs),"outputs":null,
                    "return_at":role.return_at.as_ref().map(|(o,s)|json!({"origin":o.json(),"site":s}))})
            }).collect::<Vec<_>>());
        } else {
            result["outcome"] = json!(["setup-failed", self.failure]);
            result["roles"] = json!(self.unstarted.iter().map(|(role,backend)|json!({"role":role,"started":false,
                "external_work":backend.external_work_spent(),"ring_work":backend.ring_work_spent(),"active_frames":backend.active_frames(),
                "live_resource_units":backend.live_resource_units()})).collect::<Vec<_>>());
        }
        result["diagnostics"] = json!(diagnostics);
        result
    }
}
/// Per-role semantic output encoding, independent of command presentation.
/// It holds the encodings' live allowance in the invocation root.
pub struct RoleOutputEncoding {
    pub role: String,
    pub values: Vec<EncodedOutput>,
    _retained: Vec<zkc_runtime::vm::LiveReservation>,
}
pub enum EncodedOutput {
    Wire {
        physical_type: String,
        bytes: Vec<u8>,
    },
    Private {
        physical_type: String,
    },
    Unavailable {
        code: String,
    },
}

fn state_summary(value: &State) -> Json {
    use crate::host::diagnostics::{message, origin, text};
    match value {
        State::Stopped(stop) => {
            json!(["stopped",{"origin":origin(&stop.origin),"origin_path_omitted":stop.origin.path.len().saturating_sub(4),
            "site":stop.site.as_deref().map(text),"cause":match &stop.cause {
                StopCause::Decode(reason)=>json!(["decode",reason.as_str()]),
                StopCause::Explicit(reason)=>json!(["explicit",message(&reason.text)]),
                StopCause::Backend(reason)=>json!(["backend",message(&reason.text)]),
                StopCause::Limit=>json!(["limit"]),StopCause::Cancelled=>json!(["cancelled"]),
            },"local":stop.local.as_ref().map(|l|json!({"site":text(&l.site),"function":text(&l.function),"instruction":l.instruction.as_deref().map(text)})),
            "cleanup_errors":stop.cleanup_errors.iter().take(4).map(|e|message(&e.text)).collect::<Vec<_>>(),
            "omitted_errors":stop.omitted_errors+stop.cleanup_errors.len().saturating_sub(4)}])
        }
        State::ReturnIf { site } => json!(["return-if", text(site)]),
        State::Pending { kind, site } => json!(["pending", format!("{kind:?}"), text(site)]),
        State::Unpolled { kind, site } => json!([
            "unpolled",
            kind.map(|k| format!("{k:?}")),
            site.as_deref().map(text)
        ]),
        _ => state(value),
    }
}
fn outcome_summary(value: &Outcome) -> Json {
    use crate::host::diagnostics::message;
    match value {
        Outcome::ParticipantStopped { role } => json!(["participant-stopped", role]),
        Outcome::ReturnedEarly { role, blocked } => json!(["returned-early", role, blocked]),
        Outcome::DriverFailed(failure) => json!([
            "driver-failed",
            format!("{:?}", failure.kind),
            message(&failure.detail.text)
        ]),
        Outcome::HostCancelled(reason) => json!(["host-cancelled", message(&reason.text)]),
        _ => outcome(value),
    }
}
fn outcome(outcome: &Outcome) -> Json {
    match outcome {
        Outcome::Completed => json!(["completed"]),
        Outcome::ParticipantStopped { role } => json!(["participant-stopped", role]),
        Outcome::ReturnedEarly { role, blocked } => json!(["returned-early", role, blocked]),
        Outcome::DriverFailed(failure) => json!([
            "driver-failed",
            format!("{:?}", failure.kind),
            bounded(&failure.detail)
        ]),
        Outcome::HostCancelled(reason) => json!(["host-cancelled", bounded(reason)]),
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
            Value::Sequence(v) => v
                .iter()
                .map(|child| unit_count(std::slice::from_ref(child)))
                .sum(),
            _ => 0,
        })
        .sum()
}

// Identity and current generation matter as well as the residual count. The
// caller retains these units, so observation must not consume or retire them.
pub(super) fn check_units(
    backend: &CpuBackend,
    values: &[Value],
    seen: &mut std::collections::BTreeSet<u64>,
) -> Result<()> {
    for value in values {
        match value {
            Value::ResourceUnit(unit) => {
                zkc_runtime::vm::Backend::validate_value(backend, value)
                    .map_err(|e| e.to_string())?;
                let state = backend
                    .observe(unit.capability())
                    .map_err(|e| e.to_string())?;
                if !seen.insert(state.issued_id) {
                    return Err("bundle-returned-unit-alias".into());
                }
            }
            Value::Variant(v) => check_units(backend, v.payload(), seen)?,
            Value::Sequence(v) => {
                for child in v.iter() {
                    check_units(backend, std::slice::from_ref(child), seen)?;
                }
            }
            _ => {}
        }
    }
    Ok(())
}

fn path_element(element: &zkc_runtime::vm::PathElement) -> serde_json::Value {
    use zkc_runtime::vm::PathElement;
    match element {
        PathElement::Branch { site, alternative } => json!(["branch", site, alternative]),
        PathElement::Match { site, alternative } => json!(["match", site, alternative]),
        PathElement::Conditional { site, taken } => {
            json!(["if", site, if *taken { "then" } else { "else" }])
        }
        PathElement::For { site, index } => json!(["for", site, index.to_string()]),
        PathElement::Loop { site, iteration } => json!(["loop", site, iteration.to_string()]),
    }
}
