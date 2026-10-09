use super::{Admitted, PhysicalType, admit, backend::*, model::*, transport::*};
use super::{ProgramCut, ProgramState};
use std::collections::BTreeMap;

// Taking custody out of a runner leaves this empty only while the runner is
// being destroyed. Ordinary methods always operate on the installed backend.
struct BackendOwner<B>(Option<B>);
impl<B> std::ops::Deref for BackendOwner<B> {
    type Target = B;
    fn deref(&self) -> &B {
        self.0.as_ref().expect("runner owns backend")
    }
}
impl<B> std::ops::DerefMut for BackendOwner<B> {
    fn deref_mut(&mut self) -> &mut B {
        self.0.as_mut().expect("runner owns backend")
    }
}

type Result<T> = std::result::Result<T, RuntimeError>;

struct Execution<V> {
    frame: Frame,
    body: Body,
    pc: usize,
    env: BTreeMap<String, V>,
    destination: Destination,
}
enum Destination {
    Root,
    Loop {
        outputs: Vec<String>,
        carried: Ports,
        captures: Vec<String>,
        remaining: u64,
        iteration: u64,
        induction: String,
        site: String,
        base: Box<Origin>,
    },
}

/// One role, one owned backend, no all-role state or peer completion channel.
/// `poll` exposes a stable action; local/send/receive advance only through their
/// corresponding explicit methods. Local computation and loops are bounded.
pub struct Runner<B: Backend> {
    admitted: Admitted,
    backend: BackendOwner<B>,
    role: String,
    root: Origin,
    stack: Vec<Execution<B::Value>>,
    pending: Option<Action<B::Value>>,
    usage: Usage,
    value_budget: ValueBudget,
    work_budget: WorkBudget,
    next_frame: u64,
    local_failure: Option<(String, Origin)>,
    local_cleanup_errors: Vec<BackendError>,
    early_return: Option<(Origin, String)>,
}
impl<B: Backend> Runner<B> {
    /// Positional values must exactly match `admitted.entry(entry)` for `role`.
    /// Backend entry admission validates shapes, keys and capabilities.
    /// Loading performs no program instructions.
    pub fn new(
        admitted: &Admitted,
        entry: &str,
        role: &str,
        session: &str,
        backend: B,
        inputs: Vec<B::Value>,
    ) -> std::result::Result<Self, LoadError<B>> {
        Self::new_with_value_budget(
            admitted,
            entry,
            role,
            session,
            backend,
            inputs,
            ValueBudget::default(),
        )
    }

    /// Select a host value budget before admitting entry values. Zero budgets
    /// are valid: they permit only zero-byte payloads. Arithmetic overflow
    /// refuses retention even when the selected budget is `usize::MAX`.
    pub fn new_with_value_budget(
        admitted: &Admitted,
        entry: &str,
        role: &str,
        session: &str,
        backend: B,
        inputs: Vec<B::Value>,
        value_budget: ValueBudget,
    ) -> std::result::Result<Self, LoadError<B>> {
        Self::new_with_budgets(
            admitted,
            entry,
            role,
            session,
            backend,
            inputs,
            value_budget,
            WorkBudget::default(),
        )
    }

    /// Enforce host work and value budgets inside local and administrative steps,
    /// before execution starts.
    #[allow(clippy::too_many_arguments)]
    pub fn new_with_budgets(
        admitted: &Admitted,
        entry: &str,
        role: &str,
        session: &str,
        backend: B,
        inputs: Vec<B::Value>,
        value_budget: ValueBudget,
        work_budget: WorkBudget,
    ) -> std::result::Result<Self, LoadError<B>> {
        let work_budget = WorkBudget {
            instructions: work_budget.instructions.min(Limits::INSTRUCTIONS),
            iterations: work_budget.iterations.min(Limits::ITERATIONS),
        };
        let root = Origin {
            session: session.to_owned(),
            entry: entry.to_owned(),
            instance: String::new(),
            path: Vec::new(),
        };
        let mut runner = Self {
            admitted: admitted.clone(),
            backend: BackendOwner(Some(backend)),
            role: role.to_owned(),
            root,
            stack: Vec::new(),
            pending: None,
            usage: Usage::default(),
            value_budget,
            work_budget,
            next_frame: 0,
            local_failure: None,
            local_cleanup_errors: Vec::new(),
            early_return: None,
        };
        if let Err(error) = runner.initialize(entry, role, session, inputs) {
            if !runner.stack.is_empty() {
                runner.halt(StopKind::Cancelled, None, None);
            }
            return Err(LoadError {
                error,
                usage: runner.usage,
                backend: runner
                    .backend
                    .0
                    .take()
                    .expect("load retains backend custody"),
            });
        }
        Ok(runner)
    }
    fn initialize(
        &mut self,
        entry: &str,
        role: &str,
        session: &str,
        inputs: Vec<B::Value>,
    ) -> Result<()> {
        if session.is_empty()
            || session.len() > 128
            || !session
                .bytes()
                .all(|b| b.is_ascii_alphanumeric() || matches!(b, b'_' | b'.' | b'-'))
        {
            return Err(RuntimeError::Session);
        }
        admit::installed(&self.admitted.program, self.backend())
            .map_err(RuntimeError::Admission)?;
        let roles = self
            .admitted
            .program
            .entries
            .get(entry)
            .ok_or(RuntimeError::Entry)?;
        let symbol = roles.get(role).ok_or(RuntimeError::Role)?;
        let p = self.admitted.program.participants[symbol].clone();
        self.root.instance = p.instance.clone();
        let mut frame = self.frame(self.root.clone(), FrameKind::Entry, p.inputs.clone());
        frame.services = p.services.clone();
        self.push(frame, p.body.clone(), inputs, Destination::Root)?;
        Ok(())
    }
    pub fn role(&self) -> &str {
        &self.role
    }
    pub fn root_origin(&self) -> &Origin {
        &self.root
    }
    pub fn usage(&self) -> Usage {
        self.usage
    }
    /// Host inspection only; there is no mutable backend/environment getter for child code.
    pub fn backend(&self) -> &B {
        &self.backend
    }
    pub fn is_terminal(&self) -> bool {
        matches!(self.pending, Some(Action::Returned(_) | Action::Stopped(_)))
    }
    /// Borrow terminal data without preparing another action.
    pub fn stop(&self) -> Option<&Stop> {
        match &self.pending {
            Some(Action::Stopped(stop)) => Some(stop),
            _ => None,
        }
    }
    /// Exact reached coordinate of a successful conditional entry return.
    pub fn early_return(&self) -> Option<(&Origin, &str)> {
        self.early_return
            .as_ref()
            .map(|(origin, site)| (origin, site.as_str()))
    }
    pub fn returned_values(&self) -> Option<&[B::Value]> {
        match &self.pending {
            Some(Action::Returned(values)) => Some(values),
            _ => None,
        }
    }
    /// Read-only program status, including an unexposed return. Never accesses
    /// the value environment, invokes backend hooks, or clones payloads.
    pub fn inspect_program(&self) -> Result<ProgramState<'_>> {
        // Local calls and queries run synchronously; their interiors cannot be
        // observed through this immutable borrow between dispatches.
        Ok(match &self.pending {
            Some(Action::Returned(_)) => ProgramState::Returned,
            Some(Action::Stopped(stop)) => ProgramState::Stopped(stop),
            Some(Action::Local(action)) => ProgramState::Pending(ProgramCut {
                origin: &action.cut.origin,
                role: &action.cut.role,
                site: &action.cut.site,
                kind: CutKind::Local,
            }),
            Some(Action::Query(action)) => ProgramState::Pending(ProgramCut {
                origin: &action.cut.origin,
                role: &action.cut.role,
                site: &action.cut.site,
                kind: CutKind::Query,
            }),
            Some(Action::Send(packet)) => ProgramState::Pending(ProgramCut {
                origin: &packet.envelope.origin,
                role: &packet.envelope.sender,
                site: &packet.envelope.site,
                kind: CutKind::Send,
            }),
            Some(Action::Receive(receive)) => ProgramState::Pending(ProgramCut {
                origin: &receive.envelope.origin,
                role: &receive.envelope.receiver,
                site: &receive.envelope.site,
                kind: CutKind::Receive,
            }),
            None => {
                let frame = self.stack.last().ok_or(RuntimeError::WrongAction)?;
                let (kind, site) = match &frame.body[frame.pc] {
                    Instruction::Local { site, .. } => (Some(CutKind::Local), Some(site.as_str())),
                    Instruction::Query { site, .. } => (Some(CutKind::Query), Some(site.as_str())),
                    Instruction::Send { site, .. } => (Some(CutKind::Send), Some(site.as_str())),
                    Instruction::Receive { site, .. } => {
                        (Some(CutKind::Receive), Some(site.as_str()))
                    }
                    Instruction::Loop { site, .. } => (None, Some(site.as_str())),
                    Instruction::ReturnIf { site, .. } => {
                        return Ok(ProgramState::ReturnIf { site });
                    }
                    Instruction::Yield(_) => return Ok(ProgramState::Yield),
                    Instruction::Return(_) => (None, None),
                };
                ProgramState::Unpolled { kind, site }
            }
        })
    }
    /// No participant instruction has executed since successful initialization.
    /// Non-advancing inspection is allowed.
    /// Proof hosts use this to reject reused or partially consumed executions.
    pub fn is_at_entry(&self) -> bool {
        !self.is_terminal()
            && matches!(
                self.stack.as_slice(),
                [Execution {
                    pc: 0,
                    destination: Destination::Root,
                    ..
                }]
            )
    }
    /// Cancel an unfinished role, unwind all backend frames, and recover its state.
    /// No resource transition is rolled back and no peer is signalled.
    pub fn into_backend(mut self) -> B {
        if !self.is_terminal() {
            self.halt(StopKind::Cancelled, None, None);
        }
        self.backend.0.take().expect("runner owns backend custody")
    }
    pub fn cancel(&mut self) {
        if !self.is_terminal() {
            self.halt(StopKind::Cancelled, None, None);
        }
    }
    fn frame(&mut self, origin: Origin, kind: FrameKind, inputs: Ports) -> Frame {
        self.next_frame += 1; // bounded by instruction/iteration/call ceilings
        let services = if matches!(kind, FrameKind::Loop { .. }) {
            self.stack
                .last()
                .map(|frame| frame.frame.services.clone())
                .unwrap_or_default()
        } else {
            vec![]
        };
        Frame {
            id: FrameId(self.next_frame),
            parent: self.stack.last().map(|s| s.frame.id),
            role: self.role.clone(),
            origin,
            kind,
            inputs,
            services,
        }
    }
    fn validate(&self, value: &B::Value, ty: PhysicalType, wire: bool) -> Result<()> {
        if value.physical_type() != ty {
            return Err(RuntimeError::Payload);
        }
        if value.retained_bytes() > Limits::VALUE_BYTES {
            return Err(RuntimeError::Limit);
        }
        self.backend.validate_value(value)?;
        if wire {
            if !ty.is_message_type() {
                return Err(RuntimeError::Payload);
            }
            // Keep the value-level check for types with an existing codec.
            // Complete native-only frames were admitted by is_message_type.
            if ty.is_serializable() {
                value.validate_serializable()?;
            }
        }
        Ok(())
    }
    fn can_retain(&self, values: &[B::Value]) -> Result<usize> {
        let bytes = values.iter().try_fold(0usize, |sum, v| {
            sum.checked_add(v.retained_bytes())
                .ok_or(RuntimeError::Limit)
        })?;
        self.can_retain_size(values.len(), bytes)?;
        Ok(bytes)
    }
    fn can_retain_size(&self, count: usize, bytes: usize) -> Result<()> {
        if self
            .usage
            .live_values
            .checked_add(count)
            .is_none_or(|n| n > Limits::LIVE_VALUES)
            || self
                .usage
                .live_value_bytes
                .checked_add(bytes)
                .is_none_or(|n| n > self.value_budget.live_bytes)
            || self
                .usage
                .total_value_bytes
                .checked_add(bytes)
                .is_none_or(|n| n > self.value_budget.total_bytes)
        {
            return Err(RuntimeError::Limit);
        }
        Ok(())
    }
    fn retain(&mut self, values: &[B::Value]) -> Result<()> {
        self.retain_bytes(values).map(|_| ())
    }
    fn retain_bytes(&mut self, values: &[B::Value]) -> Result<usize> {
        let bytes = self.can_retain(values)?;
        self.usage.live_values += values.len();
        self.usage.live_value_bytes += bytes;
        self.usage.total_value_bytes += bytes;
        Ok(bytes)
    }
    fn release<'a>(&mut self, values: impl Iterator<Item = &'a B::Value>)
    where
        B::Value: 'a,
    {
        for v in values {
            self.usage.live_values -= 1;
            self.usage.live_value_bytes -= v.retained_bytes();
        }
    }
    fn push(
        &mut self,
        frame: Frame,
        body: Body,
        values: Vec<B::Value>,
        destination: Destination,
    ) -> Result<()> {
        if self.stack.len() >= Limits::STACK_DEPTH {
            return Err(RuntimeError::Limit);
        }
        if frame.inputs.len() != values.len() {
            return Err(RuntimeError::Inputs);
        }
        for (v, (_, ty)) in values.iter().zip(&frame.inputs) {
            self.validate(v, ty.clone(), false)?;
        }
        // Captures remain in the suspended parent. The destination stores only
        // names; each iteration owns one checked body view, never a second
        // hidden payload store. The parent cannot advance while this frame lives.
        self.retain(&values)?;
        if let Err(e) = self.backend.enter_frame(&frame, &values) {
            self.release(values.iter());
            return Err(e.into());
        }
        let env = frame
            .inputs
            .iter()
            .map(|(n, _)| n.clone())
            .zip(values)
            .collect();
        self.stack.push(Execution {
            frame,
            body,
            pc: 0,
            env,
            destination,
        });
        Ok(())
    }
    fn push_child(
        &mut self,
        frame: Frame,
        body: Body,
        values: Vec<B::Value>,
        destination: Destination,
        site: &str,
    ) {
        let origin = frame.origin.clone();
        if let Err(error) = self.push(frame, body, values, destination) {
            // A refused child has no installed execution to supply its origin.
            // Unwind only accepted frames, retaining the attempted child's cut.
            self.failed(error, Some(site.to_owned()), Some(origin));
        }
    }
    fn tick(&mut self) -> Result<()> {
        if self.usage.instructions >= self.work_budget.instructions {
            return Err(RuntimeError::Limit);
        }
        self.usage.instructions += 1;
        Ok(())
    }
    fn iteration(&mut self) -> Result<()> {
        if self.usage.iterations >= self.work_budget.iterations {
            return Err(RuntimeError::Limit);
        }
        self.usage.iterations += 1;
        Ok(())
    }
    fn values(&self, names: &[String]) -> Vec<B::Value> {
        let env = &self.stack.last().expect("active frame").env;
        names.iter().map(|n| env[n].clone()).collect()
    }
    fn bind(&mut self, names: &[String], values: Vec<B::Value>) -> Result<()> {
        self.retain(&values)?;
        let env = &mut self.stack.last_mut().expect("parent frame").env;
        for (name, value) in names.iter().zip(values) {
            env.insert(name.clone(), value);
        }
        Ok(())
    }
    fn active_origin(&self) -> Origin {
        self.stack
            .last()
            .map_or_else(|| self.root.clone(), |f| f.frame.origin.clone())
    }
    fn halt(&mut self, kind: StopKind, site: Option<String>, origin: Option<Origin>) {
        let origin = origin.unwrap_or_else(|| self.active_origin());
        let exit = if matches!(kind, StopKind::Cancelled) {
            FrameExit::Cancelled
        } else {
            FrameExit::Stopped
        };
        let mut cleanup_errors = Vec::new();
        while let Some(frame) = self.stack.pop() {
            if let Err(e) = self.backend.leave_frame(&frame.frame, exit, &[]) {
                cleanup_errors.push(e);
            }
            self.release(frame.env.values());
        }
        self.pending = Some(Action::Stopped(Stop {
            origin,
            role: self.role.clone(),
            site,
            kind,
            cleanup_errors,
            local: None,
        }));
    }
    fn failed(&mut self, error: RuntimeError, site: Option<String>, origin: Option<Origin>) {
        let kind = match error {
            RuntimeError::Limit => StopKind::Limit,
            RuntimeError::ExplicitStop(reason) => StopKind::Explicit(reason),
            RuntimeError::Backend(e) => StopKind::Backend(e),
            other => StopKind::Backend(BackendError::new(format!("runtime-contract:{other}"))),
        };
        self.halt(kind, site, origin);
    }
    /// Inspect the next observable action. Once pending, polling is idempotent:
    /// no instructions, frames, backend calls or randomness are advanced.
    pub fn poll(&mut self) -> Action<B::Value> {
        self.poll_ref().clone()
    }
    /// Expose the same action while borrowing its payload and diagnostics.
    /// This avoids cloning an arbitrarily large backend cleanup error list.
    /// Like poll, this may prepare an action; use inspect_program to observe
    /// without execution.
    pub fn poll_ref(&mut self) -> &Action<B::Value> {
        if self.pending.is_none()
            && let Err(e) = self.prepare()
        {
            self.failed(e, None, None);
        }
        self.pending
            .as_ref()
            .expect("prepare always produces action")
    }
    fn prepare(&mut self) -> Result<()> {
        while self.pending.is_none() {
            if self.usage.instructions >= self.work_budget.instructions {
                return Err(RuntimeError::Limit);
            }
            let execution = self.stack.last().expect("nonterminal runner has frame");
            let body = execution.body.clone();
            let instruction = &body[execution.pc];
            let origin = execution.frame.origin.clone();
            match instruction {
                Instruction::Query {
                    site,
                    port,
                    method,
                    inputs,
                    outputs,
                } => {
                    let port = execution
                        .frame
                        .services
                        .iter()
                        .find(|p| &p.name == port)
                        .expect("admitted service port")
                        .clone();
                    let signature = port.contract.signature(method).expect("admitted method");
                    self.pending = Some(Action::Query(QueryAction {
                        cut: Cut {
                            origin,
                            role: self.role.clone(),
                            site: site.clone(),
                            kind: CutKind::Query,
                        },
                        port,
                        method: method.clone(),
                        arguments: self.values(inputs),
                        results: outputs.iter().cloned().zip(signature.outputs).collect(),
                    }));
                }
                Instruction::Local { site, function, .. } => {
                    self.pending = Some(Action::Local(LocalAction {
                        cut: Cut {
                            origin,
                            role: self.role.clone(),
                            site: site.clone(),
                            kind: CutKind::Local,
                        },
                        function: function.clone(),
                    }));
                }
                Instruction::Send {
                    site,
                    schema,
                    peer,
                    input,
                } => {
                    let payload = execution.env[input].clone();
                    let ty = payload.physical_type();
                    self.validate(&payload, ty.clone(), true)?;
                    self.pending = Some(Action::Send(Packet {
                        envelope: Envelope {
                            origin,
                            site: site.clone(),
                            schema: schema.clone(),
                            sender: self.role.clone(),
                            receiver: peer.clone(),
                        },
                        ty,
                        payload,
                    }));
                }
                Instruction::Receive {
                    site,
                    schema,
                    peer,
                    ty,
                    ..
                } => {
                    self.pending = Some(Action::Receive(Receive {
                        envelope: Envelope {
                            origin,
                            site: site.clone(),
                            schema: schema.clone(),
                            sender: peer.clone(),
                            receiver: self.role.clone(),
                        },
                        ty: ty.clone(),
                    }));
                }
                // Structured control is crossed only by the explicit program
                // control API, under the Host's chosen coordination policy.
                Instruction::Loop { .. } | Instruction::Yield(_) | Instruction::ReturnIf { .. } => {
                    return Err(BackendError::new("program-control-cut").into());
                }
                Instruction::Return(names) => {
                    self.tick()?;
                    let values = self.values(names);
                    self.finish(values)?;
                }
            }
        }
        Ok(())
    }
    fn start_loop(&mut self, instruction: &Instruction) -> Result<()> {
        let Instruction::Loop {
            site,
            count,
            carried,
            captures,
            body,
            outputs,
        } = instruction
        else {
            return Err(RuntimeError::WrongAction);
        };
        let origin = self.active_origin();
        self.tick()?;
        let values = self.values(&carried.iter().map(|(_, n)| n.clone()).collect::<Vec<_>>());
        self.stack.last_mut().expect("loop parent").pc += 1;
        let induction = count.induction.clone();
        let maximum = count.maximum;
        let count = self.stack.last().expect("loop parent").env[&count.value].control_index()?;
        if count > maximum {
            return Err(RuntimeError::Backend(BackendError::new("loop-count-bound")));
        }
        if count == 0 {
            self.bind(outputs, values)?;
            return Ok(());
        }
        let mut child_origin = origin.clone();
        child_origin.path.push(PathElement::Loop {
            site: site.clone(),
            iteration: 0,
        });
        if let Err(error) = self.iteration() {
            self.failed(error, Some(site.clone()), Some(child_origin));
            return Ok(());
        }
        let capture_values = self.values(captures);
        let ports: Ports = carried
            .iter()
            .zip(&values)
            .map(|((n, _), v)| Ok((n.clone(), v.physical_type())))
            .collect::<Result<_>>()?;
        let destination = Destination::Loop {
            outputs: outputs.clone(),
            carried: ports.clone(),
            captures: captures.clone(),
            remaining: count,
            iteration: 0,
            induction: induction.clone(),
            site: site.clone(),
            base: Box::new(origin.clone()),
        };
        let mut all_ports = ports;
        for (n, v) in captures.iter().zip(&capture_values) {
            all_ports.push((n.clone(), v.physical_type()));
        }
        let mut all_values = values;
        all_values.extend(capture_values);
        let value = self.index_value(0)?;
        all_ports.insert(0, (induction, value.physical_type()));
        all_values.insert(0, value);
        let frame = self.frame(
            child_origin,
            FrameKind::Loop {
                site: site.clone(),
                iteration: 0,
            },
            all_ports,
        );
        self.push_child(frame, body.clone(), all_values, destination, site);
        Ok(())
    }
    /// Advance one reached loop boundary using this role's own count. This is
    /// for independent participant execution; it establishes no peer agreement.
    /// Returns false without work at an observable action or terminal state.
    pub fn advance_local_control(&mut self) -> Result<bool> {
        let origin = self.active_origin();
        match self.inspect_program()? {
            ProgramState::Unpolled {
                kind: None,
                site: Some(site),
            } => {
                let site = site.to_owned();
                if self.loop_count(&origin, &site)?.is_some() {
                    let (body, pc) = self.program_control(&origin)?;
                    if let Err(error) = self.start_loop(&body[pc]) {
                        self.failed(error, Some(site), Some(origin));
                    }
                }
                Ok(true)
            }
            ProgramState::ReturnIf { site } => {
                let site = site.to_owned();
                self.return_if(&origin, &site)?;
                Ok(true)
            }
            ProgramState::Yield => {
                self.yield_loop(&origin)?;
                Ok(true)
            }
            _ => Ok(false),
        }
    }
    fn program_control(&self, origin: &Origin) -> Result<(Body, usize)> {
        if self.pending.is_some() {
            return Err(RuntimeError::WrongAction);
        }
        let frame = self.stack.last().ok_or(RuntimeError::WrongAction)?;
        if &frame.frame.origin != origin {
            return Err(RuntimeError::WrongCut);
        }
        Ok((frame.body.clone(), frame.pc))
    }
    /// Validate the reached local count before joint agreement. This performs
    /// no body work. A failed bound remains a stopped participant outcome.
    pub fn loop_count(&mut self, origin: &Origin, site: &str) -> Result<Option<u64>> {
        let (body, pc) = self.program_control(origin)?;
        let Instruction::Loop {
            site: actual,
            count,
            ..
        } = &body[pc]
        else {
            return Err(RuntimeError::WrongAction);
        };
        if actual != site {
            return Err(RuntimeError::WrongCut);
        }
        let checked = self.stack.last().expect("active loop").env[&count.value]
            .control_index()
            .and_then(|n| {
                if n <= count.maximum {
                    Ok(n)
                } else {
                    Err(BackendError::new("loop-count-bound"))
                }
            });
        match checked {
            Ok(n) => Ok(Some(n)),
            Err(e) => {
                self.failed(
                    RuntimeError::Backend(e),
                    Some(site.into()),
                    Some(origin.clone()),
                );
                Ok(None)
            }
        }
    }
    /// Enter an agreed segment without exposing or executing its first action.
    /// A local count failure is a stopped outcome, as in `loop_count`.
    pub fn enter_loop(&mut self, origin: &Origin, site: &str, count: u64) -> Result<()> {
        match self.loop_count(origin, site)? {
            None => return Ok(()),
            Some(local) if local != count => return Err(RuntimeError::WrongCut),
            Some(_) => {}
        }
        let (body, pc) = self.program_control(origin)?;
        if let Err(error) = self.start_loop(&body[pc]) {
            self.failed(error, Some(site.into()), Some(origin.clone()));
        }
        Ok(())
    }
    /// Complete exactly one reached iteration. A subsequent iteration has a
    /// fresh occurrence path; its first body action remains unpolled.
    pub fn yield_loop(&mut self, origin: &Origin) -> Result<()> {
        let (body, pc) = self.program_control(origin)?;
        let Instruction::Yield(names) = &body[pc] else {
            return Err(RuntimeError::WrongAction);
        };
        let result = self.tick().and_then(|()| self.finish(self.values(names)));
        if let Err(error) = result {
            self.failed(error, None, Some(origin.clone()));
        }
        Ok(())
    }
    /// Evaluate one conditional entry return. False binds its affine successors;
    /// true transfers the entry tuple through all enclosing loop frames. A
    /// backend or budget failure is a stopped outcome, never a retry result.
    pub fn return_if(&mut self, origin: &Origin, site: &str) -> Result<()> {
        let (body, pc) = self.program_control(origin)?;
        let Instruction::ReturnIf {
            site: actual,
            condition,
            values,
            continuations,
        } = &body[pc]
        else {
            return Err(RuntimeError::WrongAction);
        };
        if actual != site {
            return Err(RuntimeError::WrongCut);
        }
        let result = (|| {
            self.tick()?;
            let taken = self.stack.last().expect("return frame").env[condition].control_bool()?;
            let values = self.values(values);
            if !taken {
                let successors = values
                    .into_iter()
                    .filter(|v| v.physical_type().is_affine())
                    .collect();
                self.bind(continuations, successors)?;
                self.stack.last_mut().expect("return frame").pc += 1;
                return Ok(());
            }
            // Ordinary finish would restart a loop. Transfer the actual entry
            // tuple directly instead, using the backend's normal returned-frame
            // custody checks at each boundary.
            while self.stack.len() > 1 {
                if !matches!(
                    self.stack.last().expect("enclosing frame").frame.kind(),
                    FrameKind::Loop { .. }
                ) {
                    return Err(BackendError::new("program-return-frame").into());
                }
                let execution = self.stack.pop().expect("enclosing loop");
                self.release(execution.env.values());
                self.backend
                    .leave_frame(&execution.frame, FrameExit::Returned, &values)?;
            }
            self.finish(values)?;
            if self.returned_values().is_some() {
                self.early_return = Some((origin.clone(), site.into()));
            } else if let Some(Action::Stopped(stop)) = &mut self.pending {
                stop.origin = origin.clone();
                stop.site = Some(site.into());
            }
            Ok(())
        })();
        if let Err(error) = result {
            self.failed(error, Some(site.into()), Some(origin.clone()));
        }
        Ok(())
    }
    fn finish(&mut self, values: Vec<B::Value>) -> Result<()> {
        let execution = self.stack.pop().expect("return frame");
        let origin = execution.frame.origin.clone();
        self.release(execution.env.values());
        let root = matches!(execution.destination, Destination::Root);
        if root && self.retain(&values).is_err() {
            // The root has no parent to receive a failed result transfer. Reserve
            // its returned values before reporting successful frame completion.
            let cleanup = self
                .backend
                .leave_frame(&execution.frame, FrameExit::Stopped, &[]);
            self.halt(StopKind::Limit, None, Some(origin));
            if let (Err(error), Some(Action::Stopped(stop))) = (cleanup, &mut self.pending) {
                stop.cleanup_errors.push(error);
            }
            return Ok(());
        }
        let leave = self
            .backend
            .leave_frame(&execution.frame, FrameExit::Returned, &values);
        if let Err(e) = leave {
            if root {
                self.release(values.iter());
            }
            self.halt(StopKind::Backend(e), None, Some(origin));
            return Ok(());
        }
        match execution.destination {
            Destination::Root => {
                self.pending = Some(Action::Returned(values));
            }
            Destination::Loop {
                outputs,
                carried,
                captures,
                remaining,
                iteration,
                induction,
                site,
                base,
            } => {
                if remaining == 1 {
                    self.bind(&outputs, values)?;
                } else {
                    let mut origin = (*base).clone();
                    origin.path.push(PathElement::Loop {
                        site: site.clone(),
                        iteration: iteration + 1,
                    });
                    if let Err(error) = self.iteration() {
                        self.failed(error, Some(site.clone()), Some(origin));
                        return Ok(());
                    }
                    let mut ports = carried.clone();
                    let mut all_values = values;
                    for (name, value) in captures.iter().zip(self.values(&captures)) {
                        ports.push((name.clone(), value.physical_type()));
                        all_values.push(value);
                    }
                    let value = self.index_value(iteration + 1)?;
                    ports.insert(0, (induction.clone(), value.physical_type()));
                    all_values.insert(0, value);
                    let frame = self.frame(
                        origin,
                        FrameKind::Loop {
                            site: site.clone(),
                            iteration: iteration + 1,
                        },
                        ports,
                    );
                    self.push_child(
                        frame,
                        execution.body,
                        all_values,
                        Destination::Loop {
                            outputs,
                            carried,
                            captures,
                            remaining: remaining - 1,
                            iteration: iteration + 1,
                            induction,
                            site: site.clone(),
                            base,
                        },
                        &site,
                    );
                }
            }
        }
        Ok(())
    }
    fn require_cut(&mut self, expected: &Cut, kind: CutKind) -> Result<()> {
        if matches!(
            self.inspect_program()?,
            ProgramState::Unpolled { kind: None, .. }
                | ProgramState::Yield
                | ProgramState::ReturnIf { .. }
        ) {
            return Err(RuntimeError::WrongAction);
        }
        let current = self.poll_ref().cut().ok_or(RuntimeError::WrongAction)?;
        if current.kind != kind {
            return Err(RuntimeError::WrongAction);
        }
        if &current != expected {
            return Err(RuntimeError::WrongCut);
        }
        Ok(())
    }
    /// Execute exactly one entire local function at the previously exposed cut.
    /// A kernel failure becomes a local stopped action; no suffix executes.
    pub fn execute_local(&mut self, expected: &Cut) -> Result<()> {
        self.require_cut(expected, CutKind::Local)?;
        if let Err(e) = self.local() {
            self.failed(e, Some(expected.site.clone()), None);
        }
        Ok(())
    }
    /// Execute one exposed query. The backend installs its successor or poison
    /// before returning. Host cancellation can run only at completed cuts.
    pub fn execute_query(&mut self, expected: &Cut) -> Result<()> {
        self.require_cut(expected, CutKind::Query)?;
        if let Err(error) = self.query() {
            self.failed(error, Some(expected.site.clone()), None);
        }
        Ok(())
    }
    fn query(&mut self) -> Result<()> {
        self.tick()?;
        let Some(Action::Query(query)) = self.pending.clone() else {
            unreachable!("checked query cut")
        };
        let (signature, bound) = self
            .backend
            .service_signature(query.port.contract, &query.method)
            .ok_or_else(|| BackendError::new("service-unsupported"))?;
        let expected = query
            .port
            .contract
            .signature(&query.method)
            .ok_or_else(|| BackendError::new("service-unsupported"))?;
        if signature != expected
            || signature.outputs
                != query
                    .results
                    .iter()
                    .map(|(_, ty)| ty.clone())
                    .collect::<Vec<_>>()
        {
            return Err(BackendError::new("service-signature").into());
        }
        self.can_retain_size(signature.outputs.len(), bound)?;
        let frame = self.stack.last().expect("query entry").frame.clone();
        let invocation = ServiceInvocation {
            frame: &frame,
            site: &query.cut.site,
            port: &query.port,
            method: &query.method,
            max_output_bytes: bound,
        };
        let values = self.backend.query(&invocation, &query.arguments)?;
        let result = (|| {
            if values.len() != signature.outputs.len() {
                return Err(RuntimeError::Payload);
            }
            for (value, (_, ty)) in values.iter().zip(&query.results) {
                self.validate(value, ty.clone(), false)?;
            }
            let actual = self.can_retain(&values)?;
            if actual > bound {
                return Err(RuntimeError::Limit);
            }
            self.bind(
                &query
                    .results
                    .iter()
                    .map(|(name, _)| name.clone())
                    .collect::<Vec<_>>(),
                values,
            )
        })();
        if result.is_err() {
            self.backend.reject_service_reply(&invocation);
        }
        result?;
        self.stack.last_mut().expect("query entry").pc += 1;
        self.pending = None;
        Ok(())
    }
    fn local(&mut self) -> Result<()> {
        self.tick()?;
        let execution = self.stack.last().expect("local parent");
        let body = execution.body.clone();
        let Instruction::Local {
            site,
            function,
            inputs,
            outputs,
        } = &body[execution.pc]
        else {
            unreachable!("checked local cut")
        };
        let f = self.admitted.program.functions[function].clone();
        let args = self.values(inputs);
        let frame = self.frame(
            execution.frame.origin.clone(),
            FrameKind::Local {
                site: site.clone(),
                function: function.clone(),
            },
            f.inputs.clone(),
        );
        let result = self.run_local_frame(&frame, &f.origin, &f.body, args, 1);
        if let Err(e) = result {
            let context = LocalContext {
                site: site.clone(),
                function: function.clone(),
                instruction: self.local_failure.as_ref().map(|(site, _)| site.clone()),
            };
            let (site, origin) = self
                .local_failure
                .take()
                .map_or((site.clone(), None), |(s, o)| (s, Some(o)));
            self.failed(e, Some(site), origin);
            if let Some(Action::Stopped(stop)) = &mut self.pending {
                stop.local = Some(Box::new(context));
                // Inner frames already left before failed() unwound the parents.
                stop.cleanup_errors
                    .splice(0..0, self.local_cleanup_errors.drain(..));
            }
            return Ok(());
        }
        let values = result.expect("successful local result");
        self.bind(outputs, values)?;
        self.stack.last_mut().expect("local parent").pc += 1;
        self.pending = None;
        Ok(())
    }
    /// Execute one accepted local frame, preserving the original failure and
    /// recording cleanup failures in actual inner-to-outer leave order.
    fn run_local_frame(
        &mut self,
        frame: &Frame,
        logical_origin: &LogicalOrigin,
        body: &[LocalInstruction],
        args: Vec<B::Value>,
        depth: usize,
    ) -> Result<Vec<B::Value>> {
        if self.stack.len() + depth > Limits::STACK_DEPTH {
            return Err(RuntimeError::Limit);
        }
        self.can_retain(&args)?;
        self.backend.enter_frame(frame, &args)?;
        let result = self.run_local_body(frame, logical_origin, body, args, depth);
        let (exit, returned) = match &result {
            Ok(values) => (FrameExit::Returned, values.as_slice()),
            Err(_) => (FrameExit::Stopped, &[][..]),
        };
        let leave = self.backend.leave_frame(frame, exit, returned);
        match result {
            Ok(values) => {
                leave?;
                Ok(values)
            }
            Err(error) => {
                if let Err(cleanup) = leave {
                    self.local_cleanup_errors.push(cleanup);
                }
                Err(error)
            }
        }
    }
    fn index_value(&self, index: u64) -> Result<B::Value> {
        let value = B::Value::from_control_index(index)?;
        self.validate(
            &value,
            PhysicalType::parse("index@native.index/1").expect("installed index representation"),
            false,
        )?;
        Ok(value)
    }
    fn run_local_body(
        &mut self,
        frame: &Frame,
        logical_origin: &LogicalOrigin,
        body: &[LocalInstruction],
        args: Vec<B::Value>,
        depth: usize,
    ) -> Result<Vec<B::Value>> {
        let mut local_bytes = self.retain_bytes(&args)?;
        let mut local_count = args.len();
        let mut env: BTreeMap<String, B::Value> = frame
            .inputs
            .iter()
            .map(|(n, _)| n.clone())
            .zip(args)
            .collect();
        let mut current_site = None;
        let mut current_has_own_site = false;
        let result = (|| {
            for instruction in body.iter() {
                current_has_own_site = matches!(
                    instruction,
                    LocalInstruction::BoolConstant { .. }
                        | LocalInstruction::Conditional { .. }
                        | LocalInstruction::For { .. }
                        | LocalInstruction::Match { .. }
                        | LocalInstruction::Stop { .. }
                );
                current_site = match instruction {
                    LocalInstruction::BoolConstant { site, .. }
                    | LocalInstruction::Variant { site, .. }
                    | LocalInstruction::Match { site, .. }
                    | LocalInstruction::Stop { site, .. }
                    | LocalInstruction::Op { site, .. }
                    | LocalInstruction::Conditional { site, .. }
                    | LocalInstruction::For { site, .. } => Some(site.clone()),
                    _ => None,
                };
                if let LocalInstruction::Release(names) = instruction {
                    for name in names {
                        // Admission independently excludes resources and future reads.
                        // Removing ordinary immutable storage has no backend effect.
                        env.remove(name).expect("admitted storage release");
                    }
                    continue;
                }
                self.tick()?;
                match instruction {
                    LocalInstruction::BoolConstant { output, value, .. } => {
                        let value = B::Value::from_control_bool(*value)?;
                        self.validate(
                            &value,
                            PhysicalType::parse("bool@native.bool/1")
                                .expect("installed Boolean representation"),
                            false,
                        )?;
                        local_bytes += self.retain_bytes(std::slice::from_ref(&value))?;
                        local_count += 1;
                        env.insert(output.clone(), value);
                    }
                    LocalInstruction::Stop { reason, .. } => {
                        return Err(RuntimeError::ExplicitStop(reason.clone()));
                    }
                    LocalInstruction::Variant {
                        ty,
                        alternative,
                        payload,
                        output,
                        ..
                    } => {
                        let descriptor = ty
                            .logical()
                            .variant_descriptor()
                            .expect("admitted variant")
                            .clone();
                        let index = descriptor
                            .alternatives()
                            .iter()
                            .position(|a| a.label() == alternative)
                            .expect("admitted alternative");
                        let payload = payload.iter().map(|n| env[n].clone()).collect();
                        let value = B::Value::pack_variant(descriptor, index, payload)?;
                        self.validate(&value, ty.clone(), false)?;
                        local_bytes += self.retain_bytes(std::slice::from_ref(&value))?;
                        local_count += 1;
                        env.insert(output.clone(), value);
                    }
                    LocalInstruction::Match {
                        site,
                        input,
                        captures,
                        arms,
                        outputs,
                    } => {
                        let value = &env[input];
                        self.backend.validate_value(value)?;
                        let (descriptor, alternative, mut args) = value.unpack_variant()?;
                        if value.physical_type().logical().variant_descriptor() != Some(&descriptor)
                        {
                            return Err(BackendError::new("variant-descriptor").into());
                        }
                        let arm = arms
                            .get(alternative)
                            .ok_or_else(|| BackendError::new("variant-alternative"))?;
                        let declared = descriptor
                            .alternatives()
                            .get(alternative)
                            .ok_or_else(|| BackendError::new("variant-alternative"))?;
                        if arm.alternative != declared.label()
                            || args.len() != declared.payload().len()
                        {
                            return Err(BackendError::new("variant-payload").into());
                        }
                        for (v, ty) in args.iter().zip(declared.payload()) {
                            self.validate(
                                v,
                                PhysicalType::default_for(ty.clone()).map_err(|_| {
                                    BackendError::new("variant-payload-representation")
                                })?,
                                false,
                            )?;
                        }
                        args.extend(captures.iter().map(|n| env[n].clone()));
                        let ports = arm
                            .payload
                            .iter()
                            .chain(captures)
                            .zip(&args)
                            .map(|(n, v)| (n.clone(), v.physical_type()))
                            .collect();
                        let values = self.run_local_region(
                            frame,
                            logical_origin,
                            &arm.body,
                            ports,
                            args,
                            PathElement::Match {
                                site: site.clone(),
                                alternative: arm.alternative.clone(),
                            },
                            depth,
                        )?;
                        local_bytes += self.retain_bytes(&values)?;
                        local_count += values.len();
                        env.extend(outputs.iter().cloned().zip(values));
                    }
                    LocalInstruction::Op {
                        site,
                        binding,
                        attributes,
                        inputs,
                        outputs,
                    } => {
                        let arguments: Vec<_> = inputs.iter().map(|n| env[n].clone()).collect();
                        let signature = binding.signature();
                        for (v, ty) in arguments.iter().zip(&signature.inputs) {
                            self.validate(v, ty.clone(), false)?;
                        }
                        let invocation = Invocation {
                            frame,
                            site,
                            kernel: binding.implementation(),
                            binding,
                            logical_origin,
                            attributes,
                            max_output_bytes: (self.value_budget.live_bytes
                                - self.usage.live_value_bytes)
                                .min(self.value_budget.total_bytes - self.usage.total_value_bytes)
                                .min(Limits::VALUE_BYTES),
                        };
                        let values = self.backend.apply(&invocation, &arguments)?;
                        if values.len() != signature.outputs.len() {
                            return Err(RuntimeError::Backend(BackendError::new(
                                "kernel-output-arity",
                            )));
                        }
                        for (v, ty) in values.iter().zip(&signature.outputs) {
                            self.validate(v, ty.clone(), false)?;
                        }
                        local_bytes += self.retain_bytes(&values)?;
                        local_count += values.len();
                        for (n, v) in outputs.iter().zip(values) {
                            env.insert(n.clone(), v);
                        }
                    }
                    LocalInstruction::Conditional {
                        site,
                        condition,
                        captures,
                        then_body,
                        else_body,
                        outputs,
                    } => {
                        let taken = env[condition].control_bool()?;
                        let args = captures.iter().map(|n| env[n].clone()).collect::<Vec<_>>();
                        let ports = captures
                            .iter()
                            .zip(&args)
                            .map(|(n, v)| (n.clone(), v.physical_type()))
                            .collect();
                        let values = self.run_local_region(
                            frame,
                            logical_origin,
                            if taken { then_body } else { else_body },
                            ports,
                            args,
                            PathElement::Conditional {
                                site: site.clone(),
                                taken,
                            },
                            depth,
                        )?;
                        local_bytes += self.retain_bytes(&values)?;
                        local_count += values.len();
                        env.extend(outputs.iter().cloned().zip(values));
                    }
                    LocalInstruction::For {
                        conditional,
                        site,
                        induction,
                        lower,
                        upper,
                        carried,
                        captures,
                        body,
                        outputs,
                    } => {
                        let lower = env[lower].control_index()?;
                        let upper = env[upper].control_index()?;
                        if lower > Limits::PARAMETER
                            || upper > Limits::PARAMETER
                            || upper.saturating_sub(lower) > Limits::LOOP_COUNT
                        {
                            return Err(BackendError::new("exhausted:local-bound-limit").into());
                        }
                        let mut values = carried
                            .iter()
                            .map(|(_, n)| env[n].clone())
                            .collect::<Vec<_>>();
                        for index in lower..upper {
                            if let Err(error) = self.iteration() {
                                let mut origin = frame.origin.clone();
                                origin.path.push(PathElement::For {
                                    site: site.clone(),
                                    index,
                                });
                                self.local_failure = Some((site.clone(), origin));
                                return Err(error);
                            }
                            let mut args = vec![self.index_value(index)?];
                            args.extend(values);
                            args.extend(captures.iter().map(|n| env[n].clone()));
                            let names = std::iter::once(induction.clone())
                                .chain(carried.iter().map(|(n, _)| n.clone()))
                                .chain(captures.iter().cloned());
                            let ports = names
                                .zip(&args)
                                .map(|(n, v)| (n, v.physical_type()))
                                .collect();
                            values = self.run_local_region(
                                frame,
                                logical_origin,
                                body,
                                ports,
                                args,
                                PathElement::For {
                                    site: site.clone(),
                                    index,
                                },
                                depth,
                            )?;
                            if *conditional && !values.remove(0).control_bool()? {
                                break;
                            }
                        }
                        local_bytes += self.retain_bytes(&values)?;
                        local_count += values.len();
                        env.extend(outputs.iter().cloned().zip(values));
                    }
                    LocalInstruction::Release(_) => unreachable!("handled without a tick"),
                    LocalInstruction::Return(names) | LocalInstruction::Yield(names) => {
                        return Ok(names.iter().map(|n| env[n].clone()).collect());
                    }
                }
            }
            unreachable!("admitted local terminator")
        })();
        if result.is_err() && self.local_failure.is_none() && (depth > 1 || current_has_own_site) {
            let site = current_site.unwrap_or_else(|| match frame.origin.path.last() {
                Some(
                    PathElement::Conditional { site, .. }
                    | PathElement::For { site, .. }
                    | PathElement::Match { site, .. },
                ) => site.clone(),
                _ => String::new(),
            });
            self.local_failure = Some((site, frame.origin.clone()));
        }
        // Ghost charges survive physical release, including on every early error.
        // Shared Arc backing remains charged once per original retained binding.
        self.usage.live_values -= local_count;
        self.usage.live_value_bytes -= local_bytes;
        result
    }
    #[allow(clippy::too_many_arguments)]
    fn run_local_region(
        &mut self,
        parent: &Frame,
        logical_origin: &LogicalOrigin,
        body: &[LocalInstruction],
        ports: Ports,
        args: Vec<B::Value>,
        path: PathElement,
        depth: usize,
    ) -> Result<Vec<B::Value>> {
        let mut origin = parent.origin.clone();
        origin.path.push(path);
        let mut frame = self.frame(origin, parent.kind.clone(), ports);
        frame.parent = Some(parent.id);
        let result = (|| {
            if self.stack.len() + depth >= Limits::STACK_DEPTH {
                return Err(RuntimeError::Limit);
            }
            for (v, (_, ty)) in args.iter().zip(&frame.inputs) {
                self.validate(v, ty.clone(), false)?;
            }
            self.run_local_frame(&frame, logical_origin, body, args, depth + 1)
        })();
        if result.is_err() && self.local_failure.is_none() {
            let site = match frame.origin.path.last() {
                Some(
                    PathElement::Conditional { site, .. }
                    | PathElement::For { site, .. }
                    | PathElement::Match { site, .. },
                ) => site.clone(),
                _ => String::new(),
            };
            self.local_failure = Some((site, frame.origin));
        }
        result
    }
    /// Consume one pending send. The caller owns delivery; no peer state is accessed.
    pub fn take_send(&mut self, expected: &Cut) -> Result<Packet<B::Value>> {
        self.require_cut(expected, CutKind::Send)?;
        if let Err(e) = self.tick() {
            self.failed(e.clone(), Some(expected.site.clone()), None);
            return Err(e);
        }
        let Some(Action::Send(packet)) = self.pending.take() else {
            unreachable!("checked send")
        };
        self.stack.last_mut().expect("sender").pc += 1;
        Ok(packet)
    }
    /// Validate without consuming the receive or crossing native control cuts.
    /// The driver uses this before committing a send.
    pub fn check_delivery(&mut self, packet: &Packet<B::Value>) -> Result<()> {
        if matches!(
            self.inspect_program()?,
            ProgramState::Unpolled { kind: None, .. }
                | ProgramState::Yield
                | ProgramState::ReturnIf { .. }
        ) {
            return Err(RuntimeError::WrongAction);
        }
        let Action::Receive(request) = self.poll_ref() else {
            return Err(RuntimeError::WrongAction);
        };
        if packet.envelope != request.envelope {
            return Err(RuntimeError::Envelope);
        }
        if packet.ty != request.ty {
            return Err(RuntimeError::Payload);
        }
        let ty = request.ty.clone();
        self.validate(&packet.payload, ty, true)?;
        self.can_retain(std::slice::from_ref(&packet.payload))?;
        if self.usage.instructions >= self.work_budget.instructions {
            return Err(RuntimeError::Limit);
        }
        Ok(())
    }
    /// Complete one already exposed native receive. API errors do not poll or
    /// advance. Once accepted, even a decode/limit/backend stop consumes the
    /// attempt; the host must remove its payload exactly once.
    pub fn complete_receive(
        &mut self,
        expected: &Cut,
        decoded: std::result::Result<B::Value, DecodeReason>,
    ) -> Result<ReceiveCompletion> {
        let Some(Action::Receive(request)) = &self.pending else {
            return Err(RuntimeError::WrongAction);
        };
        if request.cut() != *expected {
            return Err(RuntimeError::WrongCut);
        }
        let ty = request.ty.clone();
        if let Ok(value) = &decoded
            && (value.physical_type() != ty
                || !ty.is_message_type()
                || (ty.is_serializable() && value.validate_serializable().is_err()))
        {
            return Err(RuntimeError::Payload);
        }
        if let Err(error) = self.tick() {
            self.failed(error, Some(expected.site.clone()), None);
            return Ok(ReceiveCompletion::Stopped);
        }
        let value = match decoded {
            Ok(value) => value,
            Err(reason) => {
                self.halt(StopKind::Decode(reason), Some(expected.site.clone()), None);
                return Ok(ReceiveCompletion::Stopped);
            }
        };
        let result = (|| {
            // Serializability was checked before acceptance. Backend validation
            // retains the existing runtime's typed error contract (no text parsing).
            self.validate(&value, ty, false)?;
            let frame = self.stack.last().expect("pending receiver frame");
            let Instruction::Receive { output, .. } = &frame.body[frame.pc] else {
                unreachable!("pending native receive")
            };
            let output = output.clone();
            self.bind(std::slice::from_ref(&output), vec![value])?;
            self.stack.last_mut().expect("receiver").pc += 1;
            self.pending = None;
            Ok(())
        })();
        match result {
            Ok(()) => Ok(ReceiveCompletion::Delivered),
            Err(error) => {
                self.failed(error, Some(expected.site.clone()), None);
                Ok(ReceiveCompletion::Stopped)
            }
        }
    }
    /// Reject a malformed/misrouted packet without advancing or changing the request.
    /// Wire decoding and its byte limits belong to the installed Value adapter.
    pub fn deliver(&mut self, packet: Packet<B::Value>) -> Result<()> {
        self.check_delivery(&packet)?;
        self.tick()?;
        let execution = self.stack.last().expect("receiver");
        let body = execution.body.clone();
        let Instruction::Receive { output, .. } = &body[execution.pc] else {
            unreachable!("checked receive")
        };
        self.bind(std::slice::from_ref(output), vec![packet.payload])?;
        self.stack.last_mut().expect("receiver").pc += 1;
        self.pending = None;
        Ok(())
    }
}

impl<B: Backend> Drop for Runner<B> {
    fn drop(&mut self) {
        if self.backend.0.is_some() && !self.is_terminal() {
            // The explicit cancellation API preserves diagnostics for the host.
            // Drop still closes every admitted view and never rolls back state.
            self.halt(StopKind::Cancelled, None, None);
        }
    }
}

#[cfg(test)]
#[path = "native_tests.rs"]
mod native_tests;
