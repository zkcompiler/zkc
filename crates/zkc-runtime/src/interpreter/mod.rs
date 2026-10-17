use crate::vm::code::{LocalCode, Operation};
use crate::vm::instance::{Instance, Scope, Transfer};
mod local;
mod preparation;
mod values;
use crate::vm::retention::Retention;
use crate::vm::{ProgramCut, ProgramState};
use crate::vm::{
    code::{Body, Instruction},
    *,
};
use std::{collections::BTreeMap, sync::Arc};
use values::Values;

type Result<T> = std::result::Result<T, RuntimeError>;

struct Execution<V> {
    frame: Frame,
    scope: Scope,
    body: Body,
    pc: usize,
    env: BTreeMap<String, V>,
    destination: Destination,
}
enum Destination {
    Root,
    Loop {
        outputs: Vec<String>,
        captures: Vec<String>,
        remaining: u64,
        iteration: u64,
        site: String,
        base: Box<Origin>,
    },
}

/// One role, one owned backend, no all-role state or peer completion channel.
/// `poll` exposes a stable action; local/send/receive advance only through their
/// corresponding explicit methods. Local computation and loops are bounded.
pub struct Runner<B: Backend> {
    instance: Instance<B>,
    preparation: Option<preparation::Preparation<B>>,
    root: Origin,
    stack: Vec<Execution<B::Value>>,
    pending: Option<Action<B::Value>>,
    local_failure: Option<(String, Origin)>,
    local_cleanup_errors: Vec<BackendError>,
    early_return: Option<(Origin, String)>,
}
impl<B: Backend> Runner<B> {
    /// Positional values must exactly match `admitted.entry(entry)` for `role`.
    /// Backend entry admission validates shapes, keys and capabilities.
    /// Loading performs no program instructions.
    pub fn new(
        admitted: &Program,
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
        admitted: &Program,
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
    /// before execution starts. Work budgets above the hard execution limits
    /// refuse before initialization, retaining backend custody and zero usage.
    #[allow(clippy::too_many_arguments)]
    pub fn new_with_budgets(
        admitted: &Program,
        entry: &str,
        role: &str,
        session: &str,
        backend: B,
        inputs: Vec<B::Value>,
        value_budget: ValueBudget,
        work_budget: WorkBudget,
    ) -> std::result::Result<Self, LoadError<B>> {
        let loaded = Instance::load(
            admitted,
            entry,
            role,
            session,
            backend,
            inputs,
            value_budget,
            work_budget,
        )?;
        let root = loaded.frame.origin().clone();
        let env = loaded
            .frame
            .inputs()
            .iter()
            .map(|(n, _)| n.clone())
            .zip(loaded.inputs)
            .collect();
        Ok(Self {
            instance: loaded.instance,
            preparation: None,
            root,
            stack: vec![Execution {
                frame: loaded.frame,
                scope: loaded.scope,
                body: loaded.body,
                pc: 0,
                env,
                destination: Destination::Root,
            }],
            pending: None,
            local_failure: None,
            local_cleanup_errors: Vec::new(),
            early_return: None,
        })
    }
    pub fn role(&self) -> &str {
        self.instance.role()
    }
    pub fn root_origin(&self) -> &Origin {
        &self.root
    }
    /// Snapshot optional instrumentation without exposing participant values.
    pub fn execution_counts(&self) -> crate::vm::ExecutionCounts {
        self.instance.execution_counts()
    }
    pub fn usage(&self) -> Usage {
        self.instance.usage()
    }
    /// Host inspection only; there is no mutable backend/environment getter for child code.
    pub fn backend(&self) -> &B {
        self.instance.backend()
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
        self.instance.take_backend()
    }
    pub fn cancel(&mut self) {
        if !self.is_terminal() {
            self.halt(StopKind::Cancelled, None, None);
        }
    }
    fn local_frame(
        &mut self,
        origin: Origin,
        kind: impl Into<Arc<FrameKind>>,
        inputs: FrameInputs,
    ) -> Frame {
        self.instance.local_frame(origin, kind.into(), inputs)
    }
    /// Cleanup releases exactly the bound environment, so every retained
    /// region result must receive a name. Admission already checks the arity.
    fn matches_outputs<T>(outputs: &[T], values: &[B::Value]) -> Result<()> {
        if outputs.len() != values.len() {
            return Err(RuntimeError::Payload);
        }
        Ok(())
    }
    fn push(
        &mut self,
        frame: Frame,
        body: Body,
        values: Vec<B::Value>,
        destination: Destination,
        retention: Retention,
    ) -> Result<()> {
        let scope = self
            .instance
            .enter_participant(&frame, &values, retention)?;
        let env = frame
            .inputs()
            .iter()
            .map(|(n, _)| n.clone())
            .zip(values)
            .collect();
        self.stack.push(Execution {
            frame,
            scope,
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
        let origin = frame.origin().clone();
        if let Err(error) = self.push(frame, body, values, destination, Retention::Transfer) {
            // A refused child has no installed execution to supply its origin.
            // Unwind only accepted frames, retaining the attempted child's cut.
            self.failed(error, Some(site.to_owned()), Some(origin));
        }
    }
    fn values(&self, names: &[String]) -> Vec<B::Value> {
        let env = &self.stack.last().expect("active frame").env;
        names.iter().map(|n| env[n].clone()).collect()
    }
    fn bind(
        &mut self,
        names: &[String],
        values: Vec<B::Value>,
        retention: Retention,
    ) -> Result<()> {
        let execution = self.stack.last_mut().expect("parent frame");
        self.instance
            .retain_in(&mut execution.scope, &values, retention)?;
        let env = &mut execution.env;
        for (name, value) in names.iter().zip(values) {
            let previous = env.insert(name.clone(), value);
            debug_assert!(
                previous.is_none(),
                "admission guarantees fresh SSA bindings"
            );
        }
        Ok(())
    }
    fn active_origin(&self) -> Origin {
        self.stack
            .last()
            .map_or_else(|| self.root.clone(), |f| f.frame.origin().clone())
    }
    fn halt(&mut self, kind: StopKind, site: Option<String>, origin: Option<Origin>) {
        let origin = origin.unwrap_or_else(|| self.active_origin());
        let exit = if matches!(kind, StopKind::Cancelled) {
            FrameExit::Cancelled
        } else {
            FrameExit::Stopped
        };
        let stack = &mut self.stack;
        let cleanup_errors = self.instance.unwind(exit, |instance, frame| {
            if let Some(execution) = stack.pop_if(|execution| execution.frame.identical(frame)) {
                instance.close_scope(execution.scope, execution.env.values());
            }
        });
        self.pending = Some(Action::Stopped(Stop {
            origin,
            role: self.role().to_owned(),
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
            if !self.instance.has_instruction_capacity() {
                return Err(RuntimeError::Limit);
            }
            let execution = self.stack.last().expect("nonterminal runner has frame");
            let body = execution.body.clone();
            let instruction = &body[execution.pc];
            let origin = execution.frame.origin().clone();
            if !matches!(instruction, Instruction::Local { .. })
                && let Some(p) = &mut self.preparation
            {
                p.close();
            }
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
                        .services()
                        .iter()
                        .find(|p| &p.name == port)
                        .expect("admitted service port")
                        .clone();
                    let signature = port.contract.signature(method).expect("admitted method");
                    self.pending = Some(Action::Query(QueryAction {
                        cut: Cut {
                            origin,
                            role: self.role().to_owned(),
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
                            role: self.role().to_owned(),
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
                    self.instance.validate(&payload, &ty, true)?;
                    self.pending = Some(Action::Send(Packet {
                        envelope: Envelope {
                            origin,
                            site: site.clone(),
                            schema: schema.clone(),
                            sender: self.role().to_owned(),
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
                            receiver: self.role().to_owned(),
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
                    self.instance.tick()?;
                    let values = self.values(names);
                    self.finish(values)?;
                }
            }
        }
        Ok(())
    }
    fn start_loop(&mut self, instruction: &Instruction, count: u64) -> Result<()> {
        self.close_preparation();
        let Instruction::Loop {
            site,
            carried,
            captures,
            body,
            outputs,
            ..
        } = instruction
        else {
            return Err(RuntimeError::WrongAction);
        };
        let origin = self.active_origin();
        self.instance.tick()?;
        let values = self.values(&carried.iter().map(|(_, n)| n.clone()).collect::<Vec<_>>());
        self.stack.last_mut().expect("loop parent").pc += 1;
        if count == 0 {
            self.bind(outputs, values, Retention::Transfer)?;
            return Ok(());
        }
        let mut child_origin = origin.clone();
        child_origin.path.push(PathElement::Loop {
            site: site.clone(),
            iteration: 0,
        });
        if let Err(error) = self.instance.iteration() {
            self.failed(error, Some(site.clone()), Some(child_origin));
            return Ok(());
        }
        let capture_values = self.values(captures);
        let destination = Destination::Loop {
            outputs: outputs.clone(),
            captures: captures.clone(),
            remaining: count,
            iteration: 0,
            site: site.clone(),
            base: Box::new(origin.clone()),
        };
        let mut all_values = values;
        all_values.extend(capture_values);
        let value = self.instance.index_value(0)?;
        all_values.insert(0, value);
        let frame = self.instance.loop_frame(child_origin, site, 0);
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
                if let Some(count) = self.loop_count(&origin, &site)? {
                    let (body, pc) = self.program_control(&origin)?;
                    if let Err(error) = self.start_loop(&body[pc], count) {
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
        if frame.frame.origin() != origin {
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
        let checked = Instance::<B>::loop_count(
            &self.stack.last().expect("active loop").env[&count.value],
            count.maximum,
        );
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
        if let Err(error) = self.start_loop(&body[pc], count) {
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
        let result = self
            .instance
            .tick()
            .and_then(|()| self.finish(self.values(names)));
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
        self.close_preparation();
        let result = (|| {
            self.instance.tick()?;
            let taken = self.stack.last().expect("return frame").env[condition].control_bool()?;
            let values = self.values(values);
            if !taken {
                let successors = values
                    .into_iter()
                    .filter(|v| v.physical_type().is_affine())
                    .collect();
                self.bind(continuations, successors, Retention::Transfer)?;
                self.stack.last_mut().expect("return frame").pc += 1;
                return Ok(());
            }
            // Ordinary finish would restart a loop. Transfer the actual entry
            // tuple directly instead, using the backend's normal returned-frame
            // custody checks at each boundary.
            let values = self.instance.hold_return(values);
            self.accept_return(values, |runner, values| {
                while runner.stack.len() > 1 {
                    if !matches!(
                        runner.stack.last().expect("enclosing frame").frame.kind(),
                        FrameKind::Loop { .. }
                    ) {
                        return Err(BackendError::new("program-return-frame").into());
                    }
                    let execution = runner.stack.pop().expect("enclosing loop");
                    runner
                        .instance
                        .close_scope(execution.scope, execution.env.values());
                    runner.instance.leave_frame_retained(
                        &execution.frame,
                        FrameExit::Returned,
                        values,
                    )?;
                }
                runner.finish_retained(values)?;
                Ok(())
            })?;
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
        // The returning environment is still live and validates every value.
        // Preserve shared backing through cleanup, custody checks and the next
        // participant frame just as for a Local region handoff.
        let values = self.instance.hold_return(values);
        self.accept_return(values, Self::finish_retained)
    }
    fn finish_retained(&mut self, values: &Transfer<B::Value>) -> Result<()> {
        let execution = self.stack.pop().expect("return frame");
        let origin = execution.frame.origin().clone();
        self.instance
            .close_scope(execution.scope, execution.env.values());
        let root = matches!(execution.destination, Destination::Root);
        if root {
            match self.instance.return_root(&execution.frame, values) {
                Ok(()) => self.pending = Some(Action::Returned(values.to_vec())),
                Err(failure) => {
                    self.failed(failure.error, None, Some(origin));
                    if let Some(Action::Stopped(stop)) = &mut self.pending {
                        stop.cleanup_errors.extend(failure.cleanup_errors);
                    }
                }
            }
            return Ok(());
        }
        if let Err(error) =
            self.instance
                .leave_frame_retained(&execution.frame, FrameExit::Returned, values)
        {
            self.halt(StopKind::Backend(error), None, Some(origin));
            return Ok(());
        }
        match execution.destination {
            Destination::Root => unreachable!("root completion handled above"),
            Destination::Loop {
                outputs,
                captures,
                remaining,
                iteration,
                site,
                base,
            } => {
                if remaining == 1 {
                    self.bind(&outputs, values.to_vec(), Retention::Transfer)?;
                } else {
                    let mut origin = (*base).clone();
                    origin.path.push(PathElement::Loop {
                        site: site.clone(),
                        iteration: iteration + 1,
                    });
                    if let Err(error) = self.instance.iteration() {
                        self.failed(error, Some(site.clone()), Some(origin));
                        return Ok(());
                    }
                    let mut all_values = values.to_vec();
                    all_values.extend(self.values(&captures));
                    let value = self.instance.index_value(iteration + 1)?;
                    all_values.insert(0, value);
                    let frame = self.instance.loop_frame(origin, &site, iteration + 1);
                    self.push_child(
                        frame,
                        execution.body,
                        all_values,
                        Destination::Loop {
                            outputs,
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
        match self.inspect_program()? {
            ProgramState::Unpolled {
                kind: Some(actual),
                site: Some(site),
            } => {
                if actual != kind {
                    return Err(RuntimeError::WrongAction);
                }
                let origin = self.stack.last().expect("unpolled cut").frame.origin();
                if expected.kind != actual
                    || expected.site != site
                    || expected.role != self.role()
                    || &expected.origin != origin
                {
                    return Err(RuntimeError::WrongCut);
                }
            }
            ProgramState::Unpolled { .. } | ProgramState::Yield | ProgramState::ReturnIf { .. } => {
                return Err(RuntimeError::WrongAction);
            }
            _ => {}
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
    /// An operation failure becomes a local stopped action; no suffix executes.
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
        self.instance.tick()?;
        let Some(Action::Query(query)) = self.pending.take() else {
            unreachable!("checked query cut")
        };
        let execution = self.stack.last_mut().expect("query entry");
        let values = self.instance.query(&mut execution.scope, &query)?;
        let env = &mut execution.env;
        for ((name, _), value) in query.results.iter().zip(values) {
            let previous = env.insert(name.clone(), value);
            debug_assert!(previous.is_none(), "admitted query result");
        }
        self.stack.last_mut().expect("query entry").pc += 1;
        self.pending = None;
        Ok(())
    }
    fn local(&mut self) -> Result<()> {
        self.instance.tick()?;
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
        let args = self.values(inputs);
        let prepared = self.instance.admitted().function(function);
        let code = &prepared.body;
        let frame: Frame = self.local_frame(
            execution.frame.origin().clone(),
            FrameKind::Local {
                site: site.clone(),
                function: function.clone(),
            },
            code.inputs.clone(),
        );
        let public = self.public_computation(code, inputs);
        let key = if public {
            crate::vm::preparation::Key::new(function, &args)
        } else {
            None
        };
        let result = self.run_local_frame(&frame, &prepared.origin, code, args, 1, key);
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
        let execution = self.stack.last_mut().expect("local parent");
        let values = self
            .instance
            .bind_return(&mut execution.scope, outputs.len(), values)?;
        for (name, value) in outputs.iter().zip(values) {
            let previous = execution.env.insert(name.clone(), value);
            debug_assert!(previous.is_none(), "admitted local output");
        }
        if public {
            self.public_results(outputs);
        }
        self.stack.last_mut().expect("local parent").pc += 1;
        self.pending = None;
        Ok(())
    }
    fn accept_return<T>(
        &mut self,
        values: Transfer<B::Value>,
        accept: impl FnOnce(&mut Self, &Transfer<B::Value>) -> Result<T>,
    ) -> Result<T> {
        let result = accept(self, &values);
        self.instance.release_return(values);
        result
    }

    /// Consume one pending send. The caller owns delivery; no peer state is accessed.
    pub fn take_send(&mut self, expected: &Cut) -> Result<Packet<B::Value>> {
        self.require_cut(expected, CutKind::Send)?;
        if let Err(e) = self.instance.tick() {
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
        let unpolled = match self.inspect_program()? {
            ProgramState::Unpolled {
                kind: Some(CutKind::Receive),
                ..
            } => true,
            ProgramState::Pending(ProgramCut {
                kind: CutKind::Receive,
                ..
            }) => false,
            _ => return Err(RuntimeError::WrongAction),
        };
        if unpolled {
            let execution = self.stack.last().expect("unpolled receive");
            let Instruction::Receive {
                site,
                schema,
                peer,
                ty,
                ..
            } = &execution.body[execution.pc]
            else {
                unreachable!("checked receive kind")
            };
            let envelope = &packet.envelope;
            if &envelope.origin != execution.frame.origin()
                || envelope.receiver != self.role()
                || &envelope.site != site
                || &envelope.schema != schema
                || &envelope.sender != peer
            {
                return Err(RuntimeError::Envelope);
            }
            if &packet.ty != ty {
                return Err(RuntimeError::Payload);
            }
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
        self.instance.validate(&packet.payload, &ty, true)?;
        self.instance
            .can_retain(std::slice::from_ref(&packet.payload), Retention::Input)?;
        if !self.instance.has_instruction_capacity() {
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
            && (!value.has_type(&ty)
                || !ty.is_message_type()
                || (ty.is_serializable() && value.validate_serializable().is_err()))
        {
            return Err(RuntimeError::Payload);
        }
        if let Err(error) = self.instance.tick() {
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
            let value = self.instance.accept(value, &ty)?;
            let frame = self.stack.last().expect("pending receiver frame");
            let Instruction::Receive { output, .. } = &frame.body[frame.pc] else {
                unreachable!("pending native receive")
            };
            let output = output.clone();
            self.bind(std::slice::from_ref(&output), vec![value], Retention::Input)?;
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
        self.instance.tick()?;
        let execution = self.stack.last().expect("receiver");
        let body = execution.body.clone();
        let Instruction::Receive { output, .. } = &body[execution.pc] else {
            unreachable!("checked receive")
        };
        self.bind(
            std::slice::from_ref(output),
            vec![packet.payload],
            Retention::Input,
        )?;
        self.stack.last_mut().expect("receiver").pc += 1;
        self.pending = None;
        Ok(())
    }
}

impl<B: Backend> Drop for Runner<B> {
    fn drop(&mut self) {
        if self.instance.has_backend() && !self.is_terminal() {
            // The explicit cancellation API preserves diagnostics for the host.
            // Drop still closes every admitted view and never rolls back state.
            self.halt(StopKind::Cancelled, None, None);
        }
    }
}

#[cfg(test)]
#[path = "native_tests.rs"]
mod native_tests;
