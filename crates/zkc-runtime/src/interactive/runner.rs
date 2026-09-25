use super::{Admitted, ArtifactFormat, PhysicalType, admit, backend::*, model::*, transport::*};
use std::{collections::BTreeMap, sync::Arc};

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
    destination: Destination<V>,
}
enum Destination<V> {
    Root,
    Call {
        outputs: Vec<String>,
    },
    Loop {
        outputs: Vec<String>,
        carried: Ports,
        captures: Vec<(String, V)>,
        remaining: u64,
        iteration: u64,
        site: String,
        base: Origin,
    },
}

/// One role, one owned backend, no all-role state or peer completion channel.
/// `poll` exposes a stable action; local/send/receive advance only through their
/// corresponding explicit methods. Administrative calls/loops are bounded.
pub struct Runner<B: Backend> {
    admitted: Admitted,
    backend: BackendOwner<B>,
    role: String,
    root: Origin,
    stack: Vec<Execution<B::Value>>,
    pending: Option<Action<B::Value>>,
    usage: Usage,
    value_budget: ValueBudget,
    next_frame: u64,
    selected_parameters: BTreeMap<String, u64>,
    ingress_actions: Vec<LocalAction>,
    local_failure: Option<(String, Origin)>,
    local_cleanup_errors: Vec<BackendError>,
}
impl<B: Backend> Runner<B> {
    /// Positional values must exactly match `admitted.entry(entry)` for `role`.
    /// Backend entry admission validates shapes, keys, parameters and capabilities.
    /// Once entry admission succeeds, ingress failures return a stopped runner
    /// with its reached observations and backend state, not a loading error.
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
        let root = Origin {
            format: admitted.format(),
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
            next_frame: 0,
            selected_parameters: BTreeMap::new(),
            ingress_actions: Vec::new(),
            local_failure: None,
            local_cleanup_errors: Vec::new(),
        };
        if let Err(error) = runner.initialize(entry, role, session, inputs) {
            if !runner.stack.is_empty() {
                runner.halt(StopKind::Cancelled, None, None);
            }
            return Err(LoadError {
                error,
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
        let frame = self.frame(
            self.root.clone(),
            Arc::new(p.parameters.clone()),
            FrameKind::Entry,
            p.inputs.clone(),
        );
        self.push(frame, p.body.clone(), inputs.clone(), Destination::Root)?;
        self.selected_parameters = p.parameters.clone();
        for (name, ingress) in &p.families {
            let selector = &ingress.selectors[role];
            let function = &selector.function;
            let site = format!("ingress.{name}");
            self.ingress_actions.push(LocalAction {
                cut: Cut {
                    origin: self.root.clone(),
                    role: self.role.clone(),
                    site: site.clone(),
                    kind: CutKind::Local,
                },
                function: function.clone(),
            });
            let arguments = self.values(&selector.arguments);
            let f = self.admitted.program.functions[function].clone();
            let frame = self.frame(
                self.root.clone(),
                Arc::new(self.selected_parameters.clone()),
                FrameKind::Local {
                    site: site.clone(),
                    function: function.clone(),
                },
                f.inputs.clone(),
            );
            let result = (|| {
                self.can_retain(&arguments)?;
                self.backend.enter_frame(&frame, &arguments)?;
                let result = self.run_local_body(&frame, &f.origin, &f.body, arguments, 1);
                let (exit, returned) = match &result {
                    Ok(values) => (FrameExit::Returned, values.as_slice()),
                    Err(_) => (FrameExit::Stopped, &[][..]),
                };
                let leave = self.backend.leave_frame(&frame, exit, returned);
                let values = match result {
                    Ok(values) => {
                        leave?;
                        values
                    }
                    Err(error) => {
                        if let Err(cleanup) = leave {
                            self.local_cleanup_errors.push(cleanup);
                        }
                        return Err(error);
                    }
                };
                let [value] = values.as_slice() else {
                    return Err(RuntimeError::Inputs);
                };
                let count = value.control_index()?;
                if count > ingress.bound {
                    return Err(BackendError::new("interactive-family-bound").into());
                }
                Ok(count)
            })();
            match result {
                Ok(count) => {
                    self.selected_parameters.insert(name.clone(), count);
                }
                Err(error) => {
                    let origin = self.local_failure.take().map(|(_, origin)| origin);
                    let cleanup = std::mem::take(&mut self.local_cleanup_errors);
                    self.failed(error, Some(site), origin);
                    if let Some(Action::Stopped(stop)) = &mut self.pending {
                        stop.cleanup_errors.splice(0..0, cleanup);
                    }
                    return Ok(());
                }
            }
        }
        Ok(())
    }
    /// Reached ingress attempts in execution order, including a failed attempt.
    /// Successful counts are in `selected_parameters`; failure is the stopped action.
    pub fn ingress_actions(&self) -> &[LocalAction] {
        &self.ingress_actions
    }
    /// Static and successfully selected counts from this role's own inputs.
    /// A stopped ingress retains earlier selections, never a default failed count.
    pub fn selected_parameters(&self) -> &BTreeMap<String, u64> {
        &self.selected_parameters
    }
    pub fn format(&self) -> ArtifactFormat {
        self.admitted.format()
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
    fn frame(
        &mut self,
        origin: Origin,
        parameters: Arc<BTreeMap<String, u64>>,
        kind: FrameKind,
        inputs: Ports,
    ) -> Frame {
        // Entry admission precedes ingress and its frame identity is immutable.
        // Subsequent frames bind the actual selected counts in their domains.
        let parameters =
            if !matches!(kind, FrameKind::Entry) && origin.instance == self.root.instance {
                let mut bound = (*parameters).clone();
                bound.extend(self.selected_parameters.clone());
                Arc::new(bound)
            } else {
                parameters
            };
        self.next_frame += 1; // bounded by instruction/iteration/call ceilings
        Frame {
            id: FrameId(self.next_frame),
            parent: self.stack.last().map(|s| s.frame.id),
            role: self.role.clone(),
            origin,
            parameters,
            kind,
            inputs,
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
            if !ty.is_serializable() {
                return Err(RuntimeError::Payload);
            }
            value.validate_serializable()?;
        }
        Ok(())
    }
    fn can_retain(&self, values: &[B::Value]) -> Result<usize> {
        let bytes = values.iter().try_fold(0usize, |sum, v| {
            sum.checked_add(v.retained_bytes())
                .ok_or(RuntimeError::Limit)
        })?;
        if self
            .usage
            .live_values
            .checked_add(values.len())
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
        Ok(bytes)
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
        destination: Destination<B::Value>,
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
        // Loop metadata retains captures independently of the active iteration env.
        let mut retained = values.clone();
        if let Destination::Loop { captures, .. } = &destination {
            retained.extend(captures.iter().map(|(_, v)| v.clone()));
        }
        // Admit both stores together, before opening a backend frame. Failed
        // allocation admission cannot strand a successfully opened child view.
        self.retain(&retained)?;
        if let Err(e) = self.backend.enter_frame(&frame, &values) {
            self.release(retained.iter());
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
        destination: Destination<B::Value>,
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
        if self.usage.instructions >= Limits::INSTRUCTIONS {
            return Err(RuntimeError::Limit);
        }
        self.usage.instructions += 1;
        Ok(())
    }
    fn iteration(&mut self) -> Result<()> {
        if self.usage.iterations >= Limits::ITERATIONS {
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
            if let Destination::Loop { captures, .. } = frame.destination {
                self.release(captures.iter().map(|(_, v)| v));
            }
        }
        self.pending = Some(Action::Stopped(Stop {
            origin,
            role: self.role.clone(),
            site,
            kind,
            cleanup_errors,
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
        if self.pending.is_none()
            && let Err(e) = self.prepare()
        {
            self.failed(e, None, None);
        }
        self.pending
            .as_ref()
            .expect("prepare always produces action")
            .clone()
    }
    fn prepare(&mut self) -> Result<()> {
        while self.pending.is_none() {
            if self.usage.instructions >= Limits::INSTRUCTIONS {
                return Err(RuntimeError::Limit);
            }
            let execution = self.stack.last().expect("nonterminal runner has frame");
            let body = execution.body.clone();
            let instruction = &body[execution.pc];
            let origin = execution.frame.origin.clone();
            match instruction {
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
                Instruction::Call {
                    site,
                    participant,
                    inputs,
                    outputs,
                } => {
                    self.tick()?;
                    if self.usage.calls >= Limits::CALLS {
                        return Err(RuntimeError::Limit);
                    }
                    self.usage.calls += 1;
                    let p = self.admitted.program.participants[participant].clone();
                    let values = self.values(inputs);
                    let mut child_origin = origin;
                    child_origin.instance = p.instance.clone();
                    child_origin.path.push(PathElement::Call {
                        site: site.clone(),
                        instance: p.instance.clone(),
                    });
                    let frame = self.frame(
                        child_origin,
                        Arc::new(p.parameters.clone()),
                        FrameKind::Call { site: site.clone() },
                        p.inputs.clone(),
                    );
                    self.stack.last_mut().expect("caller").pc += 1;
                    self.push_child(
                        frame,
                        p.body.clone(),
                        values,
                        Destination::Call {
                            outputs: outputs.clone(),
                        },
                        site,
                    );
                }
                Instruction::Loop {
                    site,
                    count,
                    carried,
                    captures,
                    body,
                    outputs,
                } => {
                    self.tick()?;
                    let values =
                        self.values(&carried.iter().map(|(_, n)| n.clone()).collect::<Vec<_>>());
                    self.stack.last_mut().expect("loop parent").pc += 1;
                    let count = match count {
                        Count::Constant(n) => *n,
                        Count::Parameter(key) => *self
                            .stack
                            .last()
                            .expect("loop parent")
                            .frame
                            .parameters
                            .get(key)
                            .or_else(|| self.selected_parameters.get(key))
                            .ok_or(RuntimeError::Inputs)?,
                    };
                    if count == 0 {
                        self.bind(outputs, values)?;
                        continue;
                    }
                    self.iteration()?;
                    let capture_values = self.values(captures);
                    let ports: Ports = carried
                        .iter()
                        .zip(&values)
                        .map(|((n, _), v)| Ok((n.clone(), v.physical_type())))
                        .collect::<Result<_>>()?;
                    let destination = Destination::Loop {
                        outputs: outputs.clone(),
                        carried: ports.clone(),
                        captures: captures
                            .iter()
                            .cloned()
                            .zip(capture_values.clone())
                            .collect(),
                        remaining: count,
                        iteration: 0,
                        site: site.clone(),
                        base: origin.clone(),
                    };
                    let mut all_ports = ports;
                    for (n, v) in captures.iter().zip(&capture_values) {
                        all_ports.push((n.clone(), v.physical_type()));
                    }
                    let mut all_values = values;
                    all_values.extend(capture_values);
                    let mut child_origin = origin;
                    child_origin.path.push(PathElement::Loop {
                        site: site.clone(),
                        iteration: 0,
                    });
                    let params = self
                        .stack
                        .last()
                        .expect("loop parent")
                        .frame
                        .parameters
                        .clone();
                    let frame = self.frame(
                        child_origin,
                        params,
                        FrameKind::Loop {
                            site: site.clone(),
                            iteration: 0,
                        },
                        all_ports,
                    );
                    self.push_child(frame, body.clone(), all_values, destination, site);
                }
                Instruction::Yield(names) | Instruction::Return(names) => {
                    self.tick()?;
                    let values = self.values(names);
                    self.finish(values)?;
                }
                Instruction::Stop { site, reason } => {
                    self.tick()?;
                    self.halt(StopKind::Explicit(reason.clone()), Some(site.clone()), None);
                }
                Instruction::Incomplete { .. } => {
                    self.tick()?;
                    self.halt(StopKind::Incomplete, None, None);
                }
            }
        }
        Ok(())
    }
    fn finish(&mut self, values: Vec<B::Value>) -> Result<()> {
        let execution = self.stack.pop().expect("return frame");
        let origin = execution.frame.origin.clone();
        self.release(execution.env.values());
        if let Destination::Loop { captures, .. } = &execution.destination {
            self.release(captures.iter().map(|(_, v)| v));
        }
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
            Destination::Call { outputs } => self.bind(&outputs, values)?,
            Destination::Loop {
                outputs,
                carried,
                captures,
                remaining,
                iteration,
                site,
                base,
            } => {
                if remaining == 1 {
                    self.bind(&outputs, values)?;
                } else {
                    self.iteration()?;
                    let mut ports = carried.clone();
                    let mut all_values = values;
                    for (n, v) in &captures {
                        ports.push((n.clone(), v.physical_type()));
                        all_values.push(v.clone());
                    }
                    let mut origin = base.clone();
                    origin.path.push(PathElement::Loop {
                        site: site.clone(),
                        iteration: iteration + 1,
                    });
                    let frame = self.frame(
                        origin,
                        execution.frame.parameters,
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
        let current = self.poll().cut().ok_or(RuntimeError::WrongAction)?;
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
            execution.frame.parameters.clone(),
            FrameKind::Local {
                site: site.clone(),
                function: function.clone(),
            },
            f.inputs.clone(),
        );
        if self.stack.len() >= Limits::STACK_DEPTH {
            return Err(RuntimeError::Limit);
        }
        self.can_retain(&args)?;
        self.backend.enter_frame(&frame, &args)?;
        // Enter succeeded: cleanup is mandatory on every subsequent path.
        let result = self.run_local_body(&frame, &f.origin, &f.body, args, 1);
        let (exit, returned) = match &result {
            Ok(values) => (FrameExit::Returned, values.as_slice()),
            Err(_) => (FrameExit::Stopped, &[][..]),
        };
        let leave = self.backend.leave_frame(&frame, exit, returned);
        if let Err(e) = result {
            let (site, origin) = self
                .local_failure
                .take()
                .map_or((site.clone(), None), |(s, o)| (s, Some(o)));
            self.failed(e, Some(site), origin);
            if let Some(Action::Stopped(stop)) = &mut self.pending {
                stop.cleanup_errors.append(&mut self.local_cleanup_errors);
            }
            if let (Err(cleanup), Some(Action::Stopped(stop))) = (leave, &mut self.pending) {
                stop.cleanup_errors.push(cleanup);
            }
            return Ok(());
        }
        let values = result.expect("successful local result");
        leave?;
        self.bind(outputs, values)?;
        self.stack.last_mut().expect("local parent").pc += 1;
        self.pending = None;
        Ok(())
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
        let mut current_control = false;
        let result = (|| {
            for instruction in body.iter() {
                current_control = matches!(
                    instruction,
                    LocalInstruction::Conditional { .. }
                        | LocalInstruction::For { .. }
                        | LocalInstruction::Match { .. }
                        | LocalInstruction::Stop { .. }
                );
                current_site = match instruction {
                    LocalInstruction::Variant { site, .. }
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
                            self.validate(v, PhysicalType::default_for(ty.clone()), false)?;
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
                            let mut args = vec![B::Value::from_control_index(index)?];
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
        if result.is_err() && self.local_failure.is_none() && (depth > 1 || current_control) {
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
        let mut frame = self.frame(
            origin,
            parent.parameters.clone(),
            parent.kind.clone(),
            ports,
        );
        frame.parent = Some(parent.id);
        let result = (|| {
            if self.stack.len() + depth >= Limits::STACK_DEPTH {
                return Err(RuntimeError::Limit);
            }
            for (v, (_, ty)) in args.iter().zip(&frame.inputs) {
                self.validate(v, ty.clone(), false)?;
            }
            self.can_retain(&args)?;
            self.backend.enter_frame(&frame, &args)?;
            let result = self.run_local_body(&frame, logical_origin, body, args, depth + 1);
            let (exit, values) = match &result {
                Ok(v) => (FrameExit::Returned, v.as_slice()),
                Err(_) => (FrameExit::Stopped, &[][..]),
            };
            let leave = self.backend.leave_frame(&frame, exit, values);
            // Preserve the original failure; cleanup never reverts completed effects.
            match result {
                Ok(v) => {
                    leave?;
                    Ok(v)
                }
                Err(e) => {
                    if let Err(cleanup) = leave {
                        self.local_cleanup_errors.push(cleanup);
                    }
                    Err(e)
                }
            }
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
    /// Validate without advancing. The driver uses this before committing a send.
    pub fn check_delivery(&mut self, packet: &Packet<B::Value>) -> Result<()> {
        let Action::Receive(request) = self.poll() else {
            return Err(RuntimeError::WrongAction);
        };
        if packet.envelope != request.envelope {
            return Err(RuntimeError::Envelope);
        }
        if packet.ty != request.ty {
            return Err(RuntimeError::Payload);
        }
        self.validate(&packet.payload, request.ty, true)?;
        self.can_retain(std::slice::from_ref(&packet.payload))?;
        if self.usage.instructions >= Limits::INSTRUCTIONS {
            return Err(RuntimeError::Limit);
        }
        Ok(())
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
