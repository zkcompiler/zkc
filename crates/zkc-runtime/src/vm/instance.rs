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

mod frames;
mod loading;
mod preparation;
pub(crate) use preparation::Recording;
mod values;
pub(crate) use values::{Scope, Transfer};

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

pub(crate) struct Instance<B: Backend> {
    admitted: Program,
    participant: Arc<code::Participant>,
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
    pending_frame: Option<Frame>,
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
// Keep metering borrows separate from immutable frame context and mutable
// backend state, so a call can borrow its active frame without cloning it.
fn charge_logical(used: &mut u64, limit: u64, bytes: u64) -> Result<()> {
    *used = used
        .checked_add(bytes)
        .filter(|n| *n <= limit)
        .ok_or(RuntimeError::Limit)?;
    Ok(())
}

impl<B: Backend> Instance<B> {
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
            let frame = self.frames.last().expect("operation inside entered frame");
            let context = CallContext {
                frame,
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
            charge_logical(
                &mut self.usage.logical_bytes,
                self.work_budget.logical_bytes,
                read,
            )?;
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
            self.validate_values(&values, signature.outputs.iter())?;
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
    pub(crate) fn query(
        &mut self,
        scope: &mut Scope,
        query: &QueryAction<B::Value>,
    ) -> Result<Vec<B::Value>> {
        // Reply rejection may follow retention failure; keep its authority
        // context alive across mutable accounting as well as the provider call.
        let frame = self
            .frames
            .last()
            .expect("query inside entered frame")
            .clone();
        let port = frame
            .services()
            .iter()
            .find(|port| port.name == query.port.name)
            .filter(|port| **port == query.port)
            .ok_or_else(|| BackendError::new("vm-service-port"))?;
        let support = self
            .backend
            .service_support(port.contract, &query.method)
            .ok_or_else(|| BackendError::new("service-unsupported"))?;
        let signature = support.signature;
        let bound = support.max_retained_bytes;
        let expected = port
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
        charge_logical(
            &mut self.usage.logical_bytes,
            self.work_budget.logical_bytes,
            read,
        )?;
        let invocation = ServiceInvocation {
            frame: &frame,
            site: &query.cut.site,
            port,
            method: &query.method,
            max_output_bytes: bound,
        };
        let values = self.backend.query(&invocation, &query.arguments)?;
        let result = (|| {
            if values.len() != signature.outputs.len() {
                return Err(RuntimeError::Payload);
            }
            self.validate_values(&values, query.results.iter().map(|(_, ty)| ty))?;
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
