use super::{Bundle, Step, bundle::Segment, report::*};
use zkc_backends::{NativeBackend, NativeWireError, native_wire_size};
use zkc_runtime::interactive::{
    Action, Backend, Cut, Limits, PathElement, PhysicalType, ProgramAction, ProgramState, Runner,
    Value, ValueBudget, WorkBudget,
};

/// The closed native wire profile selected by `zkc.run/0` bundle admission.
/// Implementations preserve its exact physical identities and canonical framing;
/// this trait is not a codec extension point. Invalid is a receive outcome;
/// Limit and Backend are failures before accepting the receive completion.
pub trait WireBackend: Backend {
    fn encode_native(&self, value: &Self::Value) -> Result<Vec<u8>, NativeWireError>;
    fn decode_native(
        &self,
        ty: &PhysicalType,
        bytes: &[u8],
    ) -> Result<Self::Value, NativeWireError>;
}
impl WireBackend for NativeBackend {
    fn encode_native(&self, value: &Self::Value) -> Result<Vec<u8>, NativeWireError> {
        self.encode_native_value(value)
    }
    fn decode_native(
        &self,
        ty: &PhysicalType,
        bytes: &[u8],
    ) -> Result<Self::Value, NativeWireError> {
        self.decode_native_value(ty, bytes)
    }
}
/// Hooks are trusted host policy. They cannot access runners or select a peer.
/// Observers must be read-only, bounded, and release resource locks before return.
/// Returned diagnostic/observation strings are copied with a 4096-byte bound.
/// Callback panic/process abort is outside the ordinary-outcome guarantee.
pub trait Hooks<B: Backend> {
    fn cancel_before(
        &mut self,
        _index: usize,
        _step: &Step,
        _path: &[PathElement],
    ) -> Option<String> {
        None
    }
    /// None preserves the current bytes. An error or oversized replacement
    /// preserves the committed original payload and fails before receiver poll.
    fn transfer(
        &mut self,
        _exchange: Exchange<'_>,
        _bytes: &[u8],
        _limit: usize,
    ) -> Result<Option<Vec<u8>>, String> {
        Ok(None)
    }
    fn observe(
        &mut self,
        _role: &str,
        _backend: &B,
        _phase: Phase,
    ) -> Result<Option<String>, String> {
        Ok(None)
    }
}
pub struct NoHooks;
impl<B: Backend> Hooks<B> for NoHooks {}
#[derive(Clone, Copy, Debug)]
pub struct Exchange<'a> {
    /// Dynamic report occurrence, not a static Bundle::steps index.
    pub send_step: usize,
    pub path: &'a [PathElement],
    pub receive_step: usize,
    pub sender: &'a str,
    pub receiver: &'a str,
    pub site: &'a str,
    pub schema: &'a str,
    pub ty: &'a PhysicalType,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RunLimits {
    pub steps: usize,
    pub wire_bytes: usize,
    pub total_wire_bytes: usize,
    pub values: ValueBudget,
    pub work: WorkBudget,
}
impl Default for RunLimits {
    fn default() -> Self {
        Self {
            steps: 32768,
            wire_bytes: 4096,
            total_wire_bytes: 16 * 1024 * 1024,
            values: ValueBudget::default(),
            work: WorkBudget::default(),
        }
    }
}
impl RunLimits {
    /// Installed joint execution ceilings. Steps count dispatched occurrences,
    /// wire_bytes bounds one message, and total_wire_bytes counts all messages.
    /// Work and retained payload limits apply separately to each runner.
    pub const HARD_MAX: Self = Self {
        steps: 32768,
        wire_bytes: 4096,
        total_wire_bytes: 16 * 1024 * 1024,
        values: ValueBudget {
            live_bytes: Limits::VALUE_BYTES,
            total_bytes: Limits::TOTAL_VALUE_BYTES,
        },
        work: WorkBudget {
            instructions: Limits::INSTRUCTIONS,
            iterations: Limits::ITERATIONS,
        },
    };
    pub fn validate(&self) -> Result<(), Failure> {
        let hard = Self::HARD_MAX;
        if self.steps > hard.steps
            || self.wire_bytes > hard.wire_bytes
            || self.total_wire_bytes > hard.total_wire_bytes
            || self.values.live_bytes > hard.values.live_bytes
            || self.values.total_bytes > hard.values.total_bytes
            || self.work.instructions > hard.work.instructions
            || self.work.iterations > hard.work.iterations
        {
            return Err(Failure::new(FailureKind::Limit, "joint-limits"));
        }
        Ok(())
    }
}
pub struct RoleInput<B: Backend> {
    pub role: String,
    pub backend: B,
    pub values: Vec<B::Value>,
}
/// Rejected before any runner is constructed; all original inputs/custody return.
pub struct StartError<B: Backend> {
    pub failure: Failure,
    pub inputs: Vec<RoleInput<B>>,
}
impl<B: Backend> std::fmt::Debug for StartError<B> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("StartError")
            .field("failure", &self.failure)
            .finish_non_exhaustive()
    }
}
struct Slot<B: Backend> {
    role: String,
    backend: Option<B>,
    inputs: Vec<B::Value>,
    runner: Option<Runner<B>>,
}
impl<B: Backend> Slot<B> {
    fn backend(&self) -> &B {
        match &self.runner {
            Some(runner) => runner.backend(),
            None => self.backend.as_ref().expect("unstarted backend custody"),
        }
    }
}
struct Execution<B: WireBackend> {
    slots: Vec<Slot<B>>,
    report: Report<B>,
    limits: RunLimits,
}
enum StepResult {
    Completed,
    Stopped,
}
type Attempt = Result<StepResult, Failure>;
fn contract(detail: &str) -> Failure {
    Failure::new(FailureKind::Contract, detail)
}
fn limit() -> Failure {
    Failure::new(FailureKind::Limit, "joint-limit")
}
fn codec(error: NativeWireError) -> Failure {
    match error {
        NativeWireError::Limit => limit(),
        NativeWireError::Backend(e) => Failure::new(FailureKind::Codec, &e.code),
        NativeWireError::Invalid(_) => contract("encoder-returned-invalid"),
    }
}
/// Run one admitted bundle. Only its next selected owner is polled. Every
/// ordinary exit after initialization goes through observation and cancellation
/// before any runner drops. The supplied session ID must be fresh by host policy.
pub fn run<B: WireBackend, H: Hooks<B>>(
    bundle: &Bundle,
    session: &str,
    mut inputs: Vec<RoleInput<B>>,
    limits: RunLimits,
    hooks: &mut H,
) -> Result<Report<B>, StartError<B>> {
    if let Err(failure) = limits.validate() {
        return Err(StartError { failure, inputs });
    }
    let refuse = |kind, detail, inputs| {
        Err(StartError {
            failure: Failure::new(kind, detail),
            inputs,
        })
    };
    if session.is_empty()
        || session.len() > 128
        || !session
            .bytes()
            .all(|b| b.is_ascii_alphanumeric() || matches!(b, b'_' | b'.' | b'-'))
    {
        return refuse(FailureKind::Setup, "session", inputs);
    }
    if inputs.len() != bundle.roles.len()
        || bundle
            .roles
            .iter()
            .any(|r| inputs.iter().filter(|i| i.role == r.entry.role).count() != 1)
    {
        return refuse(FailureKind::Setup, "role-input-membership", inputs);
    }
    for role in &bundle.roles {
        let input = inputs
            .iter()
            .find(|i| i.role == role.entry.role)
            .expect("checked membership");
        if input.values.len() != role.entry.inputs.len()
            || input
                .values
                .iter()
                .zip(&role.entry.inputs)
                .any(|(value, (_, ty))| value.physical_type() != *ty)
        {
            return refuse(FailureKind::Setup, "role-input-types", inputs);
        }
    }
    let mut slots = Vec::new();
    let mut rows = Vec::new();
    let mut reached = Vec::new();
    let mut backends = Vec::new();
    if slots.try_reserve_exact(inputs.len()).is_err()
        || rows.try_reserve_exact(inputs.len()).is_err()
        || backends.try_reserve_exact(inputs.len()).is_err()
        || reached.try_reserve_exact(limits.steps).is_err()
    {
        return refuse(FailureKind::Limit, "report-allocation", inputs);
    }
    // Reserve result-port storage before any entry can acquire resources.
    for role in &bundle.roles {
        let mut outputs = Vec::new();
        if outputs.try_reserve_exact(role.entry.outputs.len()).is_err() {
            return refuse(FailureKind::Limit, "output-allocation", inputs);
        }
        rows.push(RoleReport {
            role: role.entry.role.clone(),
            before: State::NotStarted,
            usage: None,
            observation: Observation::default(),
            cancelled: false,
            after: State::NotStarted,
            after_observation: Observation::default(),
            outputs,
            return_at: None,
        });
    }
    for role in &bundle.roles {
        let index = inputs
            .iter()
            .position(|i| i.role == role.entry.role)
            .expect("checked membership");
        let input = inputs.swap_remove(index);
        slots.push(Slot {
            role: input.role,
            backend: Some(input.backend),
            inputs: input.values,
            runner: None,
        });
    }
    let mut execution = Execution {
        slots,
        limits,
        report: Report {
            session: session.into(),
            limits,
            outcome: Outcome::Completed,
            reached,
            wire: WireUsage::default(),
            pending: None,
            roles: rows,
            backends,
        },
    };
    let outcome = execution
        .initialize(bundle, session)
        .unwrap_or_else(|| execution.execute(bundle, hooks));
    Ok(execution.finalize(outcome, hooks))
}
impl<B: WireBackend> Execution<B> {
    fn initialize(&mut self, bundle: &Bundle, session: &str) -> Option<Outcome> {
        for (index, slot) in self.slots.iter_mut().enumerate() {
            let backend = slot.backend.take().expect("unstarted backend");
            match Runner::new_with_budgets(
                &bundle.admitted,
                &bundle.entry,
                &slot.role,
                session,
                backend,
                std::mem::take(&mut slot.inputs),
                self.limits.values,
                self.limits.work,
            ) {
                Ok(runner) => {
                    let stopped = runner.stop().is_some();
                    slot.runner = Some(runner);
                    if stopped {
                        return Some(Outcome::ParticipantStopped { role: index });
                    }
                }
                Err(failure) => {
                    self.report.roles[index].usage = Some(failure.usage);
                    slot.backend = Some(failure.backend);
                    return Some(Outcome::DriverFailed(runtime_failure(
                        FailureKind::Setup,
                        &failure.error,
                    )));
                }
            }
        }
        None
    }
    fn execute<H: Hooks<B>>(&mut self, bundle: &Bundle, hooks: &mut H) -> Outcome {
        if let Some(outcome) = self.segments(bundle, &bundle.segments, &[], hooks) {
            return outcome;
        }
        if self.report.pending.is_some() {
            return Outcome::DriverFailed(contract("pending-at-completion"));
        }
        if self.slots.iter().any(|slot| {
            slot.runner
                .as_ref()
                .is_none_or(|runner| runner.returned_values().is_none())
        }) {
            return Outcome::DriverFailed(contract("unfinished-role"));
        }
        Outcome::Completed
    }
    fn segments<H: Hooks<B>>(
        &mut self,
        bundle: &Bundle,
        segments: &[Segment],
        path: &[PathElement],
        hooks: &mut H,
    ) -> Option<Outcome> {
        for segment in segments {
            match segment {
                Segment::Action(index) => {
                    if let Some(outcome) = self.step(bundle, *index, path, hooks) {
                        return Some(outcome);
                    }
                }
                Segment::Loop {
                    entries,
                    body,
                    exits,
                } => {
                    let mut headers = Vec::new();
                    for index in entries {
                        let step = &bundle.steps[*index];
                        let reached = self.report.reached.len();
                        if let Some(outcome) = self.step(bundle, *index, path, hooks) {
                            return Some(outcome);
                        }
                        if !self.returned(step.role)
                            && matches!(bundle.action(step), Some(ProgramAction::Loop { .. }))
                        {
                            headers.push((*index, reached));
                        }
                    }
                    // Every reached participant bound has completed before this
                    // driver observation. A verifier stop therefore takes precedence.
                    if headers.is_empty() {
                        continue;
                    }
                    let first = &bundle.steps[headers[0].0];
                    let count = self.report.reached[headers[0].1]
                        .loop_count
                        .expect("checked loop count");
                    if headers
                        .iter()
                        .any(|(_, reached)| self.report.reached[*reached].loop_count != Some(count))
                    {
                        return Some(Outcome::DriverFailed(contract("loop-count-disagreement")));
                    }
                    let ProgramAction::Loop { site, .. } =
                        bundle.action(first).expect("loop header")
                    else {
                        unreachable!()
                    };
                    for (index, reached) in &headers {
                        let step = &bundle.steps[*index];
                        let runner = self.slots[step.role]
                            .runner
                            .as_mut()
                            .expect("initialized role");
                        let mut origin = runner.root_origin().clone();
                        origin.path.extend_from_slice(path);
                        let result = runner.enter_loop(&origin, site, count);
                        if runner.stop().is_some() {
                            self.report.reached[*reached].progress = Progress::Stopped;
                            return Some(Outcome::ParticipantStopped { role: step.role });
                        }
                        if let Err(error) = result {
                            self.report.reached[*reached].progress = Progress::Failed;
                            return Some(Outcome::DriverFailed(runtime_failure(
                                FailureKind::Contract,
                                &error,
                            )));
                        }
                        self.report.reached[*reached].loop_started = true;
                    }
                    for iteration in 0..count {
                        if headers
                            .iter()
                            .all(|(i, _)| self.returned(bundle.steps[*i].role))
                        {
                            break;
                        }
                        let mut child = path.to_vec();
                        child.push(PathElement::Loop {
                            site: site.clone(),
                            iteration,
                        });
                        if let Some(outcome) = self.segments(bundle, body, &child, hooks) {
                            return Some(outcome);
                        }
                        for index in exits {
                            if let Some(outcome) = self.step(bundle, *index, &child, hooks) {
                                return Some(outcome);
                            }
                        }
                    }
                }
            }
        }
        None
    }
    fn returned(&self, role: usize) -> bool {
        self.slots[role]
            .runner
            .as_ref()
            .is_some_and(|r| r.returned_values().is_some())
    }
    fn step<H: Hooks<B>>(
        &mut self,
        bundle: &Bundle,
        coordinate: usize,
        path: &[PathElement],
        hooks: &mut H,
    ) -> Option<Outcome> {
        let step = &bundle.steps[coordinate];
        if self.returned(step.role) {
            // A returned role has no reached suffix actions. Admitted groups
            // pair each send immediately with its receive; the live peer check
            // below refuses communication before a packet can become pending.
            return None;
        }
        if let Some(ProgramAction::Send { peer, .. } | ProgramAction::Receive { peer, .. }) =
            bundle.action(step)
            && let Some(role) = bundle.roles.iter().position(|r| &r.entry.role == peer)
            && self.returned(role)
        {
            return Some(Outcome::ReturnedEarly {
                role,
                blocked: step.role,
            });
        }
        let index = self.report.reached.len();
        if let Some(reason) = hooks.cancel_before(index, step, path) {
            return Some(Outcome::HostCancelled(Text::copy(&reason)));
        }
        let action = bundle.action(step).expect("admitted step");
        let cost = if matches!(action, ProgramAction::Send { .. }) {
            2
        } else {
            1
        };
        if index
            .checked_add(cost)
            .is_none_or(|end| end > self.limits.steps)
        {
            return Some(Outcome::DriverFailed(limit()));
        }
        let mut iterations = Vec::new();
        if iterations.try_reserve_exact(path.len()).is_err() {
            return Some(Outcome::DriverFailed(limit()));
        }
        for element in path {
            if let PathElement::Loop { iteration, .. } = element {
                iterations.push(*iteration);
            }
        }
        self.report.reached.push(Reached {
            step: *step,
            iterations,
            loop_count: None,
            loop_started: false,
            progress: Progress::Exposed,
            sent_bytes: None,
            replacement_bytes: None,
            receive_completion: None,
        });
        let result = self.dispatch(bundle, index, step, action, path, hooks);
        let reached = self
            .report
            .reached
            .last_mut()
            .expect("reserved current step");
        match result {
            Ok(StepResult::Completed) => {
                reached.progress = Progress::Completed;
                None
            }
            Ok(StepResult::Stopped) => {
                reached.progress = Progress::Stopped;
                Some(Outcome::ParticipantStopped { role: step.role })
            }
            Err(failure) => {
                reached.progress = Progress::Failed;
                Some(Outcome::DriverFailed(failure))
            }
        }
    }
    fn dispatch<H: Hooks<B>>(
        &mut self,
        bundle: &Bundle,
        index: usize,
        step: &Step,
        action: &ProgramAction,
        path: &[PathElement],
        hooks: &mut H,
    ) -> Attempt {
        // A hostile hook runs before receiver exposure. Keep original bytes on
        // hook failure/oversize; only a successful bounded replacement commits.
        if matches!(action, ProgramAction::Receive { .. }) {
            let pending = self
                .report
                .pending
                .as_mut()
                .ok_or_else(|| contract("empty-handoff"))?;
            if pending.receive_step != index {
                return Err(contract("handoff-coordinate"));
            }
            let send_step = &self.report.reached[pending.send_step].step;
            let ProgramAction::Send {
                site, schema, ty, ..
            } = bundle.action(send_step).expect("admitted send")
            else {
                return Err(contract("handoff-send"));
            };
            let exchange = Exchange {
                send_step: pending.send_step,
                path,
                receive_step: index,
                sender: &bundle.roles[send_step.role].entry.role,
                receiver: &bundle.roles[step.role].entry.role,
                site,
                schema,
                ty,
            };
            let replacement = hooks
                .transfer(exchange, &pending.bytes, self.limits.wire_bytes)
                .map_err(|e| Failure::new(FailureKind::Hook, &e))?;
            if let Some(bytes) = replacement {
                if bytes.len() > self.limits.wire_bytes {
                    return Err(limit());
                }
                let total = self
                    .report
                    .wire
                    .replacement_bytes
                    .checked_add(bytes.len())
                    .ok_or_else(limit)?;
                if self
                    .report
                    .wire
                    .sent_bytes
                    .checked_add(total)
                    .is_none_or(|n| n > self.limits.total_wire_bytes)
                {
                    return Err(limit());
                }
                self.report.wire.replacement_bytes = total;
                self.report.reached.last_mut().unwrap().replacement_bytes = Some(bytes.len());
                pending.bytes = bytes;
            }
            self.report.reached.last_mut().unwrap().sent_bytes = Some(pending.original_bytes);
        }
        let runner = self.slots[step.role]
            .runner
            .as_mut()
            .expect("initialized roster");
        let mut origin = runner.root_origin().clone();
        origin.path.extend_from_slice(path);
        if let ProgramAction::Loop { site, .. } = action {
            match runner
                .loop_count(&origin, site)
                .map_err(|e| runtime_failure(FailureKind::Contract, &e))?
            {
                Some(count) => {
                    self.report.reached.last_mut().unwrap().loop_count = Some(count);
                    return Ok(StepResult::Completed);
                }
                None => return Ok(StepResult::Stopped),
            }
        }
        if let ProgramAction::ReturnIf { site } = action {
            runner
                .return_if(&origin, site)
                .map_err(|e| runtime_failure(FailureKind::Contract, &e))?;
            return Ok(if runner.stop().is_some() {
                StepResult::Stopped
            } else {
                StepResult::Completed
            });
        }
        if matches!(action, ProgramAction::Yield { .. }) {
            runner
                .yield_loop(&origin)
                .map_err(|e| runtime_failure(FailureKind::Contract, &e))?;
            return Ok(if runner.stop().is_some() {
                StepResult::Stopped
            } else {
                StepResult::Completed
            });
        }
        let expected = action.kind().map(|kind| Cut {
            origin,
            role: runner.role().into(),
            site: action.site().unwrap().into(),
            kind,
        });
        // A schedule error must not poll an unrelated control cut and turn a
        // driver fault into a participant stop. Inspection does not advance.
        let state = runner
            .inspect_program()
            .map_err(|e| runtime_failure(FailureKind::Contract, &e))?;
        let agrees = match state {
            ProgramState::Stopped(_) => return Ok(StepResult::Stopped),
            ProgramState::Yield | ProgramState::ReturnIf { .. } => false,
            ProgramState::Pending(cut) => {
                Some(cut.kind) == action.kind() && Some(cut.site) == action.site()
            }
            ProgramState::Unpolled {
                kind: Some(kind),
                site,
            } => Some(kind) == action.kind() && site == action.site(),
            ProgramState::Unpolled {
                kind: None,
                site: None,
            }
            | ProgramState::Returned => matches!(action, ProgramAction::Finish),
            ProgramState::Unpolled {
                kind: None,
                site: Some(_),
            } => false,
        };
        if !agrees {
            return Err(contract("exposed-action"));
        }
        match (action, runner.poll_ref()) {
            (_, Action::Stopped(_)) => return Ok(StepResult::Stopped),
            (ProgramAction::Local { function, .. }, Action::Local(local))
                if Some(&local.cut) == expected.as_ref() && &local.function == function => {}
            (ProgramAction::Query { port, method, .. }, Action::Query(query))
                if Some(&query.cut) == expected.as_ref()
                    && &query.port.name == port
                    && &query.method == method => {}
            (
                ProgramAction::Send {
                    site,
                    schema,
                    peer,
                    ty,
                },
                Action::Send(packet),
            ) if packet.envelope.origin == expected.as_ref().unwrap().origin
                && packet.envelope.sender == expected.as_ref().unwrap().role
                && &packet.envelope.site == site
                && &packet.envelope.schema == schema
                && &packet.envelope.receiver == peer
                && &packet.ty == ty
                && &packet.payload.physical_type() == ty => {}
            (
                ProgramAction::Receive {
                    site,
                    schema,
                    peer,
                    ty,
                },
                Action::Receive(receive),
            ) if receive.envelope.origin == expected.as_ref().unwrap().origin
                && receive.envelope.receiver == expected.as_ref().unwrap().role
                && &receive.envelope.site == site
                && &receive.envelope.schema == schema
                && &receive.envelope.sender == peer
                && &receive.ty == ty => {}
            (ProgramAction::Finish, Action::Returned(_)) => return Ok(StepResult::Completed),
            _ => return Err(contract("exposed-action")),
        }
        let cut = expected.as_ref().expect("non-Finish action");
        let result = match action {
            ProgramAction::Local { .. } => runner.execute_local(cut),
            ProgramAction::Query { .. } => runner.execute_query(cut),
            ProgramAction::Send { .. } => {
                if self.report.pending.is_some() {
                    return Err(contract("occupied-handoff"));
                }
                let Action::Send(packet) = runner.poll_ref() else {
                    unreachable!("checked send")
                };
                let value = packet.payload.clone();
                let bytes = runner.backend().encode_native(&value).map_err(codec)?;
                let ProgramAction::Send { ty, .. } = action else {
                    unreachable!("send")
                };
                // All messages use admitted codecs; fixed-width frames also
                // require the encoder's result to match the exact static size.
                if native_wire_size(ty).is_some_and(|width| width != bytes.len()) {
                    return Err(Failure::new(FailureKind::Codec, "native-wire-width"));
                }
                if bytes.len() > self.limits.wire_bytes {
                    return Err(limit());
                }
                let total = self
                    .report
                    .wire
                    .sent_bytes
                    .checked_add(bytes.len())
                    .ok_or_else(limit)?;
                if total
                    .checked_add(self.report.wire.replacement_bytes)
                    .is_none_or(|n| n > self.limits.total_wire_bytes)
                {
                    return Err(limit());
                }
                let sends = self.report.wire.sends.checked_add(1).ok_or_else(limit)?;
                // The only operations after successful commitment are moves and
                // writes into already reserved report/slot storage.
                match runner.take_send(cut) {
                    Ok(_) => {
                        self.report.wire.sent_bytes = total;
                        self.report.wire.sends = sends;
                        self.report.reached.last_mut().unwrap().sent_bytes = Some(bytes.len());
                        self.report.pending = Some(PendingMessage {
                            send_step: index,
                            receive_step: index + 1,
                            original_bytes: bytes.len(),
                            bytes,
                        });
                        Ok(())
                    }
                    Err(error) => Err(error),
                }
            }
            ProgramAction::Receive { ty, .. } => {
                let pending = self
                    .report
                    .pending
                    .as_ref()
                    .ok_or_else(|| contract("empty-handoff"))?;
                let decoded = match runner.backend().decode_native(ty, &pending.bytes) {
                    Ok(value) => Ok(value),
                    Err(NativeWireError::Invalid(reason)) => Err(reason),
                    Err(error) => return Err(codec(error)),
                };
                let receives = self.report.wire.receives.checked_add(1).ok_or_else(limit)?;
                match runner.complete_receive(cut, decoded) {
                    Ok(completion) => {
                        self.report.reached.last_mut().unwrap().receive_completion =
                            Some(completion);
                        self.report.pending = None;
                        self.report.wire.receives = receives;
                        Ok(())
                    }
                    Err(error) => Err(error),
                }
            }
            ProgramAction::Finish
            | ProgramAction::Loop { .. }
            | ProgramAction::Yield { .. }
            | ProgramAction::ReturnIf { .. } => {
                unreachable!("control handled before cut dispatch")
            }
        };
        if runner.stop().is_some() {
            return Ok(StepResult::Stopped);
        }
        result.map_err(|e| runtime_failure(FailureKind::Contract, &e))?;
        Ok(StepResult::Completed)
    }
    fn finalize<H: Hooks<B>>(mut self, outcome: Outcome, hooks: &mut H) -> Report<B> {
        self.report.outcome = outcome;
        // Freeze every role before cancelling any peer. Terminal roles have
        // already performed their own return/stop cleanup in Runtime.
        for (slot, row) in self.slots.iter().zip(&mut self.report.roles) {
            if let Some(runner) = &slot.runner {
                row.before = State::inspect(runner);
                row.usage = Some(runner.usage());
                row.return_at = runner.early_return().map(|(o, s)| (o.clone(), s.into()));
                if let Some(values) = runner.returned_values() {
                    row.outputs.extend_from_slice(values);
                }
            }
            row.observation = observe(hooks, slot, Phase::BeforeCancellation);
        }
        for (slot, row) in self.slots.iter_mut().zip(&mut self.report.roles) {
            if let Some(runner) = &mut slot.runner {
                if !runner.is_terminal() {
                    runner.cancel();
                    row.cancelled = true;
                }
                row.after = State::inspect(runner);
            }
        }
        for (slot, row) in self.slots.iter().zip(&mut self.report.roles) {
            row.after_observation = observe(hooks, slot, Phase::AfterCancellation);
        }
        for slot in self.slots {
            let backend = match slot.runner {
                Some(runner) => runner.into_backend(),
                None => slot.backend.expect("unstarted backend custody"),
            };
            self.report.backends.push((slot.role, backend));
        }
        self.report
    }
}
fn observe<B: Backend, H: Hooks<B>>(hooks: &mut H, slot: &Slot<B>, phase: Phase) -> Observation {
    match hooks.observe(&slot.role, slot.backend(), phase) {
        Ok(value) => Observation {
            value: value.as_deref().map(Text::copy),
            error: None,
        },
        Err(error) => Observation {
            value: None,
            error: Some(Text::copy(&error)),
        },
    }
}

#[cfg(test)]
mod contract_tests {
    use super::*;
    use serde_json::json;
    use zkc_backends::{Domain, EntryPolicy, Policy};

    fn backend() -> NativeBackend {
        NativeBackend::new(
            Policy::default(),
            EntryPolicy::new(Domain::new("Alice", "test", "main", None), None),
            Default::default(),
        )
        .unwrap()
    }
    fn loop_bundle() -> Bundle {
        let candidate = json!([
            "zkc.program/0",
            [],
            [],
            [[
                "participant",
                "a",
                "root",
                "Alice",
                [["n", "index@native.index/0"]],
                [],
                [
                    [
                        "loop",
                        "rounds",
                        ["value", "n", "8", "i"],
                        [],
                        [],
                        [["yield", []]],
                        []
                    ],
                    ["return", []]
                ],
                []
            ]],
            [["entry", "main", [["Alice", "a"]]]]
        ]);
        let raw = json!({"format":"zkc.run/0", "candidate":candidate.to_string(),
            "entry":"main", "roles":["Alice"], "steps":[
                {"loop":[{"role":0,"instruction":0,"anchor":0}], "body":[],
                 "yield":[{"role":0,"instruction":1,"anchor":null}]},
                {"role":0,"instruction":2,"anchor":null}]});
        Bundle::admit(
            &serde_json::to_vec(&raw).unwrap(),
            &backend(),
            super::super::BundleLimits::default(),
        )
        .unwrap()
    }
    fn execute(bundle: &Bundle) -> Report<NativeBackend> {
        run(
            bundle,
            "test",
            vec![RoleInput {
                role: "Alice".into(),
                backend: backend(),
                values: vec![zkc_backends::Value::Index(1)],
            }],
            RunLimits::default(),
            &mut NoHooks,
        )
        .unwrap()
    }
    #[test]
    fn internal_schedule_drift_cannot_complete_an_unfinished_role() {
        let mut bundle = loop_bundle();
        // Public admission cannot produce this. Check the driver's own terminal
        // obligation independently of decoder and static-coverage construction.
        bundle.segments.clear();
        let report = execute(&bundle);
        assert!(matches!(&report.outcome, Outcome::DriverFailed(f)
            if f.kind == FailureKind::Contract && f.detail.text == "unfinished-role"));
        assert!(
            matches!(&report.roles[0].before, State::Unpolled {kind:None, site:Some(site)} if site == "rounds")
        );
    }
    #[test]
    fn internal_finish_drift_preserves_an_unpolled_yield() {
        let mut bundle = loop_bundle();
        let Segment::Loop { body, .. } = &mut bundle.segments[0] else {
            panic!("loop segment")
        };
        // Enter the loop normally, then incorrectly dispatch the root Finish
        // while the participant is waiting at the loop yield.
        *body = vec![Segment::Action(2)];
        let report = execute(&bundle);
        assert!(matches!(&report.outcome, Outcome::DriverFailed(f)
            if f.kind == FailureKind::Contract && f.detail.text == "exposed-action"));
        assert!(matches!(
            &report.roles[0].before,
            State::Unpolled {
                kind: None,
                site: None
            }
        ));
        assert_eq!(report.roles[0].usage.as_ref().unwrap().instructions, 1);
    }
    #[test]
    fn internal_action_drift_preserves_an_unpolled_control_cut() {
        let mut bundle = loop_bundle();
        bundle.segments = vec![Segment::Action(0)];
        bundle.roles[0].actions[0] = ProgramAction::Local {
            site: "wrong".into(),
            function: "wrong".into(),
        };
        let report = execute(&bundle);
        assert!(matches!(&report.outcome, Outcome::DriverFailed(f)
            if f.kind == FailureKind::Contract && f.detail.text == "exposed-action"));
        assert!(
            matches!(&report.roles[0].before, State::Unpolled {kind:None, site:Some(site)} if site == "rounds")
        );
        assert_eq!(report.roles[0].usage.as_ref().unwrap().instructions, 0);
    }
}
