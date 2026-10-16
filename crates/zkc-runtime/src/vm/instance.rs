//! Engine-independent state for one admitted VM execution.
//!
//! Code is shared; installed handles, reached-call preparation, authority,
//! retained values and work are owned by this instance. Control flow and SSA
//! environments belong to the evaluator.
use super::code::Call;
use super::{
    backend::*,
    counts::{Counts, Event},
    retention::{Charge, Ledger, Retention},
    *,
};
use std::sync::Arc;

mod preparation;

type Result<T> = std::result::Result<T, RuntimeError>;

// Taking custody out of an instance leaves this empty only while the evaluator is
// being destroyed. Ordinary methods always operate on the installed backend.
struct BackendOwner<B>(Option<B>);
impl<B> std::ops::Deref for BackendOwner<B> {
    type Target = B;
    fn deref(&self) -> &B {
        self.0.as_ref().expect("instance owns backend")
    }
}
impl<B> std::ops::DerefMut for BackendOwner<B> {
    fn deref_mut(&mut self) -> &mut B {
        self.0.as_mut().expect("instance owns backend")
    }
}

/// Opaque accounting for one evaluator value environment. Its lifetime is
/// independent of backend frames: arguments may be retained before entry, and
/// returned backing can survive exit. Only the instance updates these charges.
#[must_use = "close the value scope when its environment leaves"]
pub(crate) struct Scope {
    bindings: usize,
    released_storage: usize,
    #[cfg(debug_assertions)]
    released_values: usize,
}
impl Scope {
    fn new() -> Self {
        Self {
            bindings: 0,
            released_storage: 0,
            #[cfg(debug_assertions)]
            released_values: 0,
        }
    }
}

pub(crate) struct Instance<B: Backend> {
    admitted: Program,
    counts: Counts,
    backend: BackendOwner<B>,
    kernels: Vec<B::Kernel>,
    calls: Vec<Option<B::Call>>,
    arguments: Vec<B::Value>,
    usage: Usage,
    ledger: Ledger,
    value_budget: ValueBudget,
    work_budget: WorkBudget,
    next_frame: u64,
    frames: Vec<Frame>,
    role: String,
    returned: Scope,
}
impl<B: Backend> Drop for Instance<B> {
    fn drop(&mut self) {
        // Normal evaluation reports cleanup failures at its control boundary.
        // An abandoned instance must still relinquish every entered view.
        if self.has_backend() {
            self.unwind(FrameExit::Cancelled, |_, _| {});
        }
    }
}
impl<B: Backend> Instance<B> {
    pub(crate) fn new(
        admitted: &Program,
        backend: B,
        role: &str,
        session: &str,
        value_budget: ValueBudget,
        work_budget: WorkBudget,
    ) -> std::result::Result<Self, LoadError<B>> {
        if work_budget.instructions > Limits::INSTRUCTIONS
            || work_budget.iterations > Limits::ITERATIONS
            || work_budget.logical_bytes > Limits::LOGICAL_BYTES
        {
            return Err(LoadError {
                error: RuntimeError::Limit,
                usage: Usage::default(),
                backend,
            });
        }
        if session.is_empty()
            || session.len() > 128
            || !session
                .bytes()
                .all(|b| b.is_ascii_alphanumeric() || matches!(b, b'_' | b'.' | b'-'))
        {
            return Err(LoadError {
                error: RuntimeError::Session,
                usage: Usage::default(),
                backend,
            });
        }
        let kernels = match super::link::install(admitted, &backend) {
            Ok(kernels) => kernels,
            Err(error) => {
                return Err(LoadError {
                    error: RuntimeError::Admission(error),
                    usage: Usage::default(),
                    backend,
                });
            }
        };
        let calls = (0..admitted.executable.calls).map(|_| None).collect();
        Ok(Self {
            admitted: admitted.clone(),
            counts: Counts::new(admitted.executable.bindings.len()),
            backend: BackendOwner(Some(backend)),
            kernels,
            calls,
            arguments: Vec::new(),
            usage: Usage::default(),
            ledger: Ledger::default(),
            value_budget,
            work_budget,
            next_frame: 0,
            frames: Vec::new(),
            role: role.to_owned(),
            returned: Scope::new(),
        })
    }
    pub(crate) fn validate(&self, value: &B::Value, ty: &PhysicalType, wire: bool) -> Result<()> {
        self.counts.event(Event::Validate);
        if !value.has_type(ty) {
            return Err(RuntimeError::Payload);
        }
        if value.retained_bytes() > Limits::VALUE_BYTES {
            return Err(RuntimeError::Limit);
        }
        // An alias of a bound, capability-free immutable value of this type has
        // already passed backend validation; its contents cannot have changed.
        if !self.ledger.validated(value, ty) {
            self.counts.event(Event::BackendValidate);
            self.backend
                .validate_value_retained(value, self.ledger.view())?;
        }
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

    pub(crate) fn accept(&self, value: B::Value, ty: &PhysicalType) -> Result<B::Value> {
        self.validate(&value, ty, false)?;
        Ok(value)
    }

    pub(crate) fn accept_values<'a>(
        &self,
        values: Vec<B::Value>,
        types: impl Iterator<Item = &'a PhysicalType>,
    ) -> Result<Vec<B::Value>> {
        // Arity belongs to the producer's existing diagnostic boundary.
        let mut types = types;
        for value in &values {
            self.validate(value, types.next().ok_or(RuntimeError::Payload)?, false)?;
        }
        if types.next().is_some() {
            return Err(RuntimeError::Payload);
        }
        Ok(values)
    }

    pub(crate) fn can_retain(&self, values: &[B::Value], retention: Retention) -> Result<Charge> {
        self.counts.event(Event::Plan);
        self.counts.add(Event::PlanValue, values.len() as u64);
        let charge = self
            .ledger
            .plan(values, retention)
            .ok_or(RuntimeError::Limit)?;
        let work = if retention == Retention::Result {
            charge.fresh as u64
        } else {
            0
        };
        self.can_retain_size(values.len(), charge.live, charge.fresh, work)?;
        Ok(charge)
    }

    fn can_retain_size(&self, count: usize, live: usize, fresh: usize, work: u64) -> Result<()> {
        if self
            .usage
            .live_values
            .checked_add(count)
            .is_none_or(|n| n > Limits::LIVE_VALUES)
            || self
                .usage
                .live_value_bytes
                .checked_add(live)
                .is_none_or(|n| n > self.value_budget.live_bytes)
            || self
                .usage
                .total_value_bytes
                .checked_add(fresh)
                .is_none_or(|n| n > self.value_budget.total_bytes)
            || self
                .usage
                .logical_bytes
                .checked_add(work)
                .is_none_or(|n| n > self.work_budget.logical_bytes)
        {
            return Err(RuntimeError::Limit);
        }
        Ok(())
    }

    fn retain(&mut self, values: &[B::Value], retention: Retention) -> Result<()> {
        let charge = self.can_retain(values, retention)?;
        self.counts.add(Event::Retain, values.len() as u64);
        self.ledger.retain(values);
        self.usage.live_values += values.len();
        self.usage.live_value_bytes += charge.live;
        self.usage.total_value_bytes += charge.fresh;
        if retention == Retention::Result {
            self.usage.logical_bytes += charge.fresh as u64;
        }
        Ok(())
    }

    pub(crate) fn open_scope(
        &mut self,
        values: &[B::Value],
        retention: Retention,
    ) -> Result<Scope> {
        let mut scope = Scope::new();
        self.retain_in(&mut scope, values, retention)?;
        Ok(scope)
    }
    pub(crate) fn retain_in(
        &mut self,
        scope: &mut Scope,
        values: &[B::Value],
        retention: Retention,
    ) -> Result<()> {
        self.retain(values, retention)?;
        scope.bindings += values.len();
        Ok(())
    }
    pub(crate) fn retain_returned(&mut self, values: &[B::Value]) -> Result<()> {
        self.returned = self.open_scope(values, Retention::Transfer)?;
        Ok(())
    }
    pub(crate) fn release_returned(&mut self, values: &[B::Value]) {
        let scope = std::mem::replace(&mut self.returned, Scope::new());
        self.close_scope(scope, values.iter());
    }

    fn charge_logical(&mut self, bytes: u64) -> Result<()> {
        self.usage.logical_bytes = self
            .usage
            .logical_bytes
            .checked_add(bytes)
            .filter(|n| *n <= self.work_budget.logical_bytes)
            .ok_or(RuntimeError::Limit)?;
        Ok(())
    }

    fn output_allowance(&self) -> usize {
        let logical = self
            .work_budget
            .logical_bytes
            .saturating_sub(self.usage.logical_bytes);
        (self
            .value_budget
            .live_bytes
            .saturating_sub(self.usage.live_value_bytes))
        .min(
            self.value_budget
                .total_bytes
                .saturating_sub(self.usage.total_value_bytes),
        )
        .min(usize::try_from(logical).unwrap_or(usize::MAX))
        .min(Limits::VALUE_BYTES)
    }

    fn operand_bytes(values: &[B::Value]) -> u64 {
        values
            .iter()
            .fold(0u64, |sum, v| sum.saturating_add(v.retained_bytes() as u64))
    }

    pub(crate) fn tick(&mut self) -> Result<()> {
        if self.usage.instructions >= self.work_budget.instructions {
            return Err(RuntimeError::Limit);
        }
        self.usage.instructions += 1;
        self.counts.event(Event::Tick);
        Ok(())
    }

    pub(crate) fn iteration(&mut self) -> Result<()> {
        if self.usage.iterations >= self.work_budget.iterations {
            return Err(RuntimeError::Limit);
        }
        self.usage.iterations += 1;
        Ok(())
    }

    pub(crate) fn unpin_return(&mut self, values: &[B::Value]) {
        self.counts.add(Event::Unpin, values.len() as u64);
        self.usage.live_value_bytes -= self.ledger.unpin(values);
    }

    pub(crate) fn index_value(&self, index: u64) -> Result<B::Value> {
        let value = B::Value::from_control_index(index)?;
        self.validate(&value, &crate::vm::code::INDEX_TYPE, false)?;
        Ok(value)
    }
    /// Execute one reached operation and retain its validated results. The
    /// evaluator supplies only explicit operands, never its value environment.
    pub(crate) fn invoke(
        &mut self,
        scope: &mut Scope,
        logical_origin: &LogicalOrigin,
        call: &Call,
        arguments: impl ExactSizeIterator<Item = B::Value>,
    ) -> Result<Vec<B::Value>> {
        let Call {
            site,
            binding,
            attributes,
            ..
        } = call;
        // The backend borrows arguments only for this call. Keep
        // empty slot capacity, never values or capability handles,
        // between calls. This also restores scratch on failures.
        self.counts.add(Event::Operand, arguments.len() as u64);
        let mut values = std::mem::take(&mut self.arguments);
        values.reserve_exact(arguments.len());
        values.extend(arguments);
        let mut arguments = values;
        let result = (|| {
            let signature = binding.signature();
            for (v, ty) in arguments.iter().zip(&signature.inputs) {
                self.validate(v, ty, false)?;
            }
            let frame = self
                .frames
                .last()
                .expect("operation inside entered frame")
                .clone();
            let context = CallContext {
                frame: &frame,
                site,
                binding,
                logical_origin,
                attributes,
            };
            // Shared operands are read at every use; aliasing never
            // makes repeated computation free.
            // A declared extent can only lower the full-operand charge.
            let full = Self::operand_bytes(&arguments);
            let read = self
                .backend
                .operand_work(&self.kernels[binding.index], &context, &arguments)
                .map_or(full, |declared| declared.min(full));
            self.charge_logical(read)?;
            let invocation = Invocation {
                context,
                max_output_bytes: self.output_allowance(),
                retained: self.ledger.view(),
            };
            self.counts.operation(binding.index);
            let values = self.backend.apply_prepared(
                &self.kernels[binding.index],
                &mut self.calls[call.index],
                &invocation,
                &arguments,
            )?;
            if values.len() != signature.outputs.len() {
                return Err(RuntimeError::Backend(BackendError::new(
                    "kernel-output-arity",
                )));
            }
            let values = self.accept_values(values, signature.outputs.iter())?;
            self.retain_in(scope, &values, Retention::Result)?;
            Ok(values)
        })();
        arguments.clear();
        self.arguments = arguments;
        result
    }

    pub(crate) fn admitted(&self) -> &Program {
        &self.admitted
    }
    pub(crate) fn role(&self) -> &str {
        &self.role
    }
    pub(crate) fn backend(&self) -> &B {
        &self.backend
    }
    pub(crate) fn has_backend(&self) -> bool {
        self.backend.0.is_some()
    }
    pub(crate) fn take_backend(&mut self) -> B {
        self.unwind(FrameExit::Cancelled, |_, _| {});
        self.backend
            .0
            .take()
            .expect("instance owns backend custody")
    }
    pub(crate) fn usage(&self) -> Usage {
        self.usage
    }
    pub(crate) fn execution_counts(&self) -> ExecutionCounts {
        self.counts.snapshot(&self.admitted.executable.bindings)
    }
    pub(crate) fn counts(&self) -> &Counts {
        &self.counts
    }
    pub(crate) fn has_instruction_capacity(&self) -> bool {
        self.usage.instructions < self.work_budget.instructions
    }
    pub(crate) fn deterministic(&self, call: &Call) -> bool {
        self.kernels[call.binding.index].deterministic()
    }
    pub(crate) fn entry_frame(
        &mut self,
        origin: Origin,
        participant: &super::code::Participant,
    ) -> Frame {
        let mut data = self.frame_data(
            origin,
            Arc::new(FrameKind::Entry),
            participant.inputs.clone().into(),
        );
        data.services = participant.services.clone();
        data.into()
    }
    pub(crate) fn frame(
        &mut self,
        origin: Origin,
        kind: Arc<FrameKind>,
        inputs: FrameInputs,
    ) -> Frame {
        self.frame_data(origin, kind, inputs).into()
    }
    fn frame_data(
        &mut self,
        origin: Origin,
        kind: Arc<FrameKind>,
        inputs: FrameInputs,
    ) -> FrameData {
        let parent = self.frames.last();
        self.counts.event(Event::Frame);
        self.next_frame += 1; // bounded by instruction/iteration/call ceilings
        let services = if matches!(kind.as_ref(), FrameKind::Loop { .. }) {
            parent
                .map(|frame| frame.services().to_vec())
                .unwrap_or_default()
        } else {
            vec![]
        };
        FrameData {
            id: FrameId(self.next_frame),
            parent: parent.map(Frame::id),
            role: self.role.clone(),
            origin,
            kind,
            inputs,
            services,
        }
    }
    pub(crate) fn check_frame_depth(&self) -> Result<()> {
        if self.frames.len() >= Limits::STACK_DEPTH {
            Err(RuntimeError::Limit)
        } else {
            Ok(())
        }
    }
    pub(crate) fn enter_frame(&mut self, frame: &Frame, values: &[B::Value]) -> Result<()> {
        self.check_frame_depth()?;
        if frame.parent() != self.frames.last().map(Frame::id) {
            return Err(BackendError::new("vm-frame-parent").into());
        }
        self.counts.event(Event::Enter);
        self.backend
            .enter_frame_retained(frame, values, self.ledger.view())?;
        self.frames.push(frame.clone());
        Ok(())
    }
    fn check_exit(&self, frame: &Frame) -> std::result::Result<(), BackendError> {
        if self
            .frames
            .last()
            .is_none_or(|top| !top.same_boundary(frame))
        {
            return Err(BackendError::new("vm-frame-order"));
        }
        Ok(())
    }
    pub(crate) fn leave_frame(
        &mut self,
        frame: &Frame,
        exit: FrameExit,
        values: &[B::Value],
    ) -> std::result::Result<(), BackendError> {
        self.check_exit(frame)?;
        self.counts.event(Event::Leave);
        let result = self.backend.leave_frame(frame, exit, values);
        self.frames.pop();
        result
    }
    pub(crate) fn leave_frame_retained(
        &mut self,
        frame: &Frame,
        exit: FrameExit,
        values: &[B::Value],
    ) -> std::result::Result<(), BackendError> {
        self.check_exit(frame)?;
        self.counts.event(Event::Leave);
        let result = self
            .backend
            .leave_frame_retained(frame, exit, values, self.ledger.view());
        self.frames.pop();
        result
    }
    /// Close actual entered views in order, then let the evaluator release each
    /// corresponding environment. Recovery and destruction use this same walk.
    pub(crate) fn unwind(
        &mut self,
        exit: FrameExit,
        mut release: impl FnMut(&mut Self, &Frame),
    ) -> Vec<BackendError> {
        let mut errors = Vec::new();
        while let Some(frame) = self.frames.last().cloned() {
            if let Err(error) = self.leave_frame(&frame, exit, &[]) {
                errors.push(error);
            }
            release(self, &frame);
        }
        errors
    }
    pub(crate) fn validate_backend(&self, value: &B::Value) -> Result<()> {
        self.counts.event(Event::BackendValidate);
        self.backend
            .validate_value_retained(value, self.ledger.view())
            .map_err(Into::into)
    }
    /// Pin only shared backing across an admitted frame handoff.
    pub(crate) fn pin_return(&mut self, values: &[B::Value]) {
        debug_assert!(
            values
                .iter()
                .all(|value| value.validation_backing().is_none()
                    || self.ledger.validated(value, &value.physical_type()))
        );
        self.counts.add(Event::Retain, values.len() as u64);
        self.ledger.retain(values);
    }
    /// Physical release preserves logical charges until the region exits.
    pub(crate) fn release_storage(&mut self, scope: &mut Scope, value: &B::Value) {
        self.counts.event(Event::Release);
        scope.released_storage += self.ledger.release(std::iter::once(value));
        #[cfg(debug_assertions)]
        {
            scope.released_values += 1;
        }
    }
    pub(crate) fn close_scope<'a>(
        &mut self,
        scope: Scope,
        values: impl Iterator<Item = &'a B::Value>,
    ) where
        B::Value: 'a,
    {
        #[cfg(debug_assertions)]
        let mut closed_values = scope.released_values;
        let released = self.ledger.release(values.inspect(|_| {
            self.counts.event(Event::Release);
            #[cfg(debug_assertions)]
            {
                closed_values += 1;
            }
        }));
        #[cfg(debug_assertions)]
        debug_assert_eq!(closed_values, scope.bindings);
        self.usage.live_values -= scope.bindings;
        self.usage.live_value_bytes -= released + scope.released_storage;
    }
    pub(crate) fn query(
        &mut self,
        scope: &mut Scope,
        query: &QueryAction<B::Value>,
    ) -> Result<Vec<B::Value>> {
        let support = self
            .backend
            .service_support(query.port.contract, &query.method)
            .ok_or_else(|| BackendError::new("service-unsupported"))?;
        let signature = support.signature;
        let bound = support.max_retained_bytes;
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
        // Service operands are read in full at every use, as kernel operands are.
        let read = Self::operand_bytes(&query.arguments);
        self.can_retain_size(
            signature.outputs.len(),
            bound,
            bound,
            read.saturating_add(bound as u64),
        )?;
        self.charge_logical(read)?;
        let frame = self
            .frames
            .last()
            .expect("query inside entered frame")
            .clone();
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
            let values = self.accept_values(values, query.results.iter().map(|(_, ty)| ty))?;
            // The installed reply bound counts shared backing in full.
            let actual = values
                .iter()
                .try_fold(0usize, |sum, v| sum.checked_add(v.retained_bytes()))
                .ok_or(RuntimeError::Limit)?;
            if actual > bound {
                return Err(RuntimeError::Limit);
            }
            self.retain_in(scope, &values, Retention::Result)?;
            Ok(values)
        })();
        if result.is_err() {
            self.backend.reject_service_reply(&invocation);
        }
        result
    }
}
