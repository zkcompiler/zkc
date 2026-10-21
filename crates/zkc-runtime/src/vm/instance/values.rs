//! Value validation, retention and lifetime accounting.
use super::*;
use crate::vm::code::{Arm, BOOL_TYPE, INDEX_TYPE};

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
    pub(super) fn new() -> Self {
        Self {
            bindings: 0,
            released_storage: 0,
            #[cfg(debug_assertions)]
            released_values: 0,
        }
    }
}

/// An owned return tuple and its shared-backing references. Only the VM can
/// construct or alter it. It is not a binding and carries no inline-value charge.
/// The evaluator must release it through the originating instance on every path.
#[must_use = "release the return transfer through its VM instance"]
pub(crate) struct Transfer<V> {
    values: Vec<V>,
}
impl<V> Transfer<V> {
    pub(super) fn new(values: Vec<V>) -> Self {
        Self { values }
    }
    pub(crate) fn as_slice(&self) -> &[V] {
        &self.values
    }
}
impl<V> std::ops::Deref for Transfer<V> {
    type Target = [V];
    fn deref(&self) -> &[V] {
        self.as_slice()
    }
}
impl<V> Drop for Transfer<V> {
    fn drop(&mut self) {
        debug_assert!(
            self.values.is_empty() || std::thread::panicking(),
            "unreleased return transfer"
        );
    }
}

impl<B: Backend> Instance<B> {
    fn reserve_constructor(
        &self,
        bound: usize,
    ) -> Result<Option<crate::vm::execution_ledger::AllocationReservation>> {
        let Some(shared) = &self.shared else {
            return Ok(None);
        };
        // Value adapters advertise a stable upper bound before construction.
        // Refuse insufficient capacity before invoking a constructor, even if
        // this particular scalar or variant would have been smaller.
        if bound > Limits::VALUE_BYTES {
            return Err(RuntimeError::Limit);
        }
        self.can_retain_size(1, bound, bound, 0)?;
        let reservation = shared.reserve_output(bound, false);
        if reservation.bytes() < bound {
            reservation.settle(0, 0)?;
            return Err(RuntimeError::Limit);
        }
        Ok(Some(reservation))
    }
    pub(crate) fn boolean(&mut self, scope: &mut Scope, value: bool) -> Result<B::Value> {
        let reservation = self.reserve_constructor(B::Value::control_allocation_bound())?;
        let value = self.accept(B::Value::from_control_bool(value)?, &BOOL_TYPE)?;
        self.retain_reserved(
            scope,
            std::slice::from_ref(&value),
            Retention::Input,
            reservation,
        )?;
        Ok(value)
    }

    pub(crate) fn variant<'a>(
        &mut self,
        scope: &mut Scope,
        ty: &PhysicalType,
        alternative: usize,
        payload: impl ExactSizeIterator<Item = &'a B::Value> + Clone,
    ) -> Result<B::Value>
    where
        B::Value: 'a,
    {
        let descriptor = ty
            .logical()
            .variant_descriptor()
            .expect("admitted variant")
            .clone();
        let reservation = self.reserve_constructor(B::Value::variant_allocation_bound(
            &descriptor,
            payload.clone(),
        ))?;
        // The bound includes the owned payload slots, not just the adapter's
        // final value. Keep their collection and operand clones after admission.
        let payload = payload.cloned().collect();
        let value = self.accept(
            B::Value::pack_variant(descriptor, alternative, payload)?,
            ty,
        )?;
        self.retain_reserved(
            scope,
            std::slice::from_ref(&value),
            Retention::Input,
            reservation,
        )?;
        Ok(value)
    }

    /// Check the actual decomposition before selecting its admitted arm. The
    /// evaluator supplies captures only after this payload has been validated.
    pub(crate) fn match_variant<'a>(
        &self,
        value: &B::Value,
        arms: &'a [Arm],
    ) -> Result<(&'a Arm, Vec<B::Value>)> {
        self.validate_backend(value)?;
        let (descriptor, alternative, args) = value.unpack_variant()?;
        if value.physical_type().logical().variant_descriptor() != Some(&descriptor) {
            return Err(BackendError::new("variant-descriptor").into());
        }
        let arm = arms
            .get(alternative)
            .ok_or_else(|| BackendError::new("variant-alternative"))?;
        let declared = descriptor
            .alternatives()
            .get(alternative)
            .ok_or_else(|| BackendError::new("variant-alternative"))?;
        if arm.alternative != declared.label() || args.len() != declared.payload().len() {
            return Err(BackendError::new("variant-payload").into());
        }
        for (value, (_, ty)) in args.iter().zip(arm.body.inputs.iter()) {
            self.validate(value, ty, false)?;
        }
        Ok((arm, args))
    }

    pub(crate) fn local_range(lower: &B::Value, upper: &B::Value) -> Result<std::ops::Range<u64>> {
        let lower = lower.control_index()?;
        let upper = upper.control_index()?;
        if lower > Limits::PARAMETER
            || upper > Limits::PARAMETER
            || upper.saturating_sub(lower) > Limits::LOOP_COUNT
        {
            return Err(BackendError::new("exhausted:local-bound-limit").into());
        }
        Ok(lower..upper)
    }
    pub(crate) fn loop_count(
        value: &B::Value,
        maximum: u64,
    ) -> std::result::Result<u64, BackendError> {
        let count = value.control_index()?;
        if count > maximum {
            return Err(BackendError::new("loop-count-bound"));
        }
        Ok(count)
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
    pub(crate) fn validate_values<'a>(
        &self,
        values: &[B::Value],
        types: impl Iterator<Item = &'a PhysicalType>,
    ) -> Result<()> {
        // Arity belongs to the producer's existing diagnostic boundary.
        let mut types = types;
        for value in values {
            self.validate(value, types.next().ok_or(RuntimeError::Payload)?, false)?;
        }
        if types.next().is_some() {
            return Err(RuntimeError::Payload);
        }
        Ok(())
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
    pub(super) fn can_retain_size(
        &self,
        count: usize,
        live: usize,
        fresh: usize,
        work: u64,
    ) -> Result<()> {
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
    fn retain(
        &mut self,
        values: &[B::Value],
        retention: Retention,
        reservation: Option<crate::vm::execution_ledger::AllocationReservation>,
    ) -> Result<()> {
        let charge = self.can_retain(values, retention)?;
        let work = if retention == Retention::Result {
            charge.fresh as u64
        } else {
            0
        };
        if let Some(reservation) = reservation {
            reservation.settle(charge.fresh, work)?;
        } else if let Some(shared) = &self.shared {
            shared.charge(
                WorkBudget {
                    instructions: 0,
                    iterations: 0,
                    logical_bytes: work,
                },
                charge.fresh,
            )?;
        }
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
    pub(crate) fn open_reserved_scope(
        &mut self,
        values: &[B::Value],
        retention: Retention,
        reservation: Option<crate::vm::execution_ledger::AllocationReservation>,
    ) -> Result<Scope> {
        let mut scope = Scope::new();
        self.retain_reserved(&mut scope, values, retention, reservation)?;
        Ok(scope)
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
        self.retain(values, retention, None)?;
        scope.bindings += values.len();
        Ok(())
    }
    pub(super) fn retain_reserved(
        &mut self,
        scope: &mut Scope,
        values: &[B::Value],
        retention: Retention,
        reservation: Option<crate::vm::execution_ledger::AllocationReservation>,
    ) -> Result<()> {
        self.retain(values, retention, reservation)?;
        scope.bindings += values.len();
        Ok(())
    }
    pub(crate) fn retain_returned(&mut self, values: &[B::Value]) -> Result<()> {
        debug_assert_eq!(self.returned.bindings, 0, "one terminal reservation");
        self.returned = self.open_scope(values, Retention::Transfer)?;
        Ok(())
    }
    pub(crate) fn release_returned(&mut self, values: &[B::Value]) {
        let scope = std::mem::replace(&mut self.returned, Scope::new());
        self.close_scope(scope, values.iter());
    }
    fn unpin_return(&mut self, values: &[B::Value]) {
        self.counts.add(Event::Unpin, values.len() as u64);
        self.usage.live_value_bytes -= self.ledger.unpin(values);
        self.release_closed_reservation();
    }

    pub(crate) fn release_return(&mut self, mut values: Transfer<B::Value>) -> Vec<B::Value> {
        self.unpin_return(&values);
        std::mem::take(&mut values.values)
    }

    /// Install returned bindings before releasing their temporary backing hold.
    /// Refusal consumes the hold too; success moves the original values without
    /// cloning the tuple into a second environment buffer.
    pub(crate) fn bind_return(
        &mut self,
        scope: &mut Scope,
        outputs: usize,
        values: Transfer<B::Value>,
    ) -> Result<Vec<B::Value>> {
        let result = if values.len() == outputs {
            self.retain_in(scope, &values, Retention::Transfer)
        } else {
            Err(RuntimeError::Payload)
        };
        let values = self.release_return(values);
        result.map(|()| values)
    }

    /// Consume a conditional loop's returned Boolean independently of its carry.
    /// Even a refused Boolean inspection releases that part of the handoff.
    pub(crate) fn take_condition(&mut self, values: &mut Transfer<B::Value>) -> Result<bool> {
        let condition = values.values.remove(0);
        let result = condition.control_bool();
        self.unpin_return(std::slice::from_ref(&condition));
        Ok(result?)
    }

    pub(crate) fn index_value(&self, index: u64) -> Result<B::Value> {
        let reservation = self.reserve_constructor(B::Value::control_allocation_bound())?;
        let value = B::Value::from_control_index(index)?;
        self.validate(&value, &INDEX_TYPE, false)?;
        if let Some(reservation) = reservation {
            reservation.settle(value.retained_bytes(), 0)?;
        }
        Ok(value)
    }
    pub(crate) fn validate_backend(&self, value: &B::Value) -> Result<()> {
        self.counts.event(Event::BackendValidate);
        self.backend
            .validate_value_retained(value, self.ledger.view())
            .map_err(Into::into)
    }
    /// Pin only shared backing across an admitted frame handoff.
    pub(crate) fn hold_return(&mut self, values: Vec<B::Value>) -> Transfer<B::Value> {
        debug_assert!(
            self.ledger
                .plan(&values, Retention::Transfer)
                .is_some_and(|charge| charge.live == charge.fresh),
            "return backing is already charged"
        );
        debug_assert!(
            values
                .iter()
                .all(|value| value.validation_backing().is_none()
                    || self.ledger.validated(value, &value.physical_type()))
        );
        self.counts.add(Event::Retain, values.len() as u64);
        self.ledger.retain(&values);
        Transfer::new(values)
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
        self.release_closed_reservation();
    }
}
