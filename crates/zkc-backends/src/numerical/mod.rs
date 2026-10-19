//! Checked construction inside a synchronous numerical handler.
//! Inputs are immutable typed slices; adapters own shape and field semantics.
//! Counts cover requested managed storage, not allocator RSS or provider scratch.

#![forbid(unsafe_code)]

pub(crate) mod expression;
mod memory;
mod views;

pub(crate) use views::RowMajor;

use crate::{Policy, Result, Value, exhausted};
use memory::{Buffer, Reservation, payload_bytes};
use std::cell::Cell;

/// Fixed call limits without backend resource authority or borrowed policy state.
pub(crate) struct Call {
    policy: Policy,
    available: usize,
    work: Cell<u64>,
    memory: Cell<usize>,
    outputs: Cell<usize>,
}

impl Call {
    pub(crate) fn new(policy: &Policy, available: usize) -> Self {
        Self {
            policy: *policy,
            // Native output validation bounds the complete returned tuple by
            // max_value_bytes, as well as fresh storage by the invocation.
            available: available.min(policy.max_value_bytes),
            work: Cell::new(0),
            memory: Cell::new(0),
            outputs: Cell::new(0),
        }
    }

    /// Admit a conservative bound before performing work. Accepted units stay spent.
    pub(crate) fn work(&self, units: u64) -> Result<()> {
        let next = self
            .work
            .get()
            .checked_add(units)
            .filter(|next| *next <= self.policy.max_numerical_work)
            .ok_or_else(|| exhausted("numerical-work"))?;
        self.work.set(next);
        Ok(())
    }

    /// Checked setup plus a conservative per-element bound, including empty calls.
    pub(crate) fn work_items(&self, len: usize, per_item: u64, setup: u64) -> Result<()> {
        let units = u64::try_from(len)
            .ok()
            .and_then(|len| len.checked_mul(per_item))
            .and_then(|units| units.checked_add(setup))
            .ok_or_else(|| exhausted("numerical-work"))?;
        self.work(units)
    }

    /// Reserve an inline scalar result without allocating a one-element buffer.
    pub(crate) fn scalar(&self, retained_bytes: usize) -> Result<ScalarOutput<'_>> {
        self.policy.output(retained_bytes, self.available)?;
        let allowance = Reservation::new(
            &self.outputs,
            retained_bytes,
            self.available,
            "output-bytes",
        )?;
        let retained = self.reserve_memory(retained_bytes)?;
        Ok(ScalarOutput {
            retained,
            allowance,
        })
    }

    /// Reserve aggregate results and the staging/final overlap before allocation.
    /// Existing consumer preflights still determine shape and per-value semantics.
    pub(crate) fn output<T: Clone>(
        &self,
        len: usize,
        initial: T,
        retained_bytes: usize,
    ) -> Result<Output<'_, T>> {
        let result = self.scalar(retained_bytes)?;
        let staging_bytes = payload_bytes::<T>(len)?;
        let staging = self.reserve_memory(staging_bytes)?;
        Ok(Output {
            buffer: Buffer::new(len, initial, staging)?,
            result,
        })
    }

    pub(crate) fn scratch<T: Clone>(&self, len: usize, initial: T) -> Result<Scratch<'_, T>> {
        let reservation = self.reserve_memory(payload_bytes::<T>(len)?)?;
        Ok(Scratch {
            buffer: Buffer::new(len, initial, reservation)?,
        })
    }

    fn reserve_memory(&self, bytes: usize) -> Result<Reservation<'_>> {
        Reservation::new(
            &self.memory,
            bytes,
            self.policy.max_numerical_bytes,
            "numerical-bytes",
        )
    }
}

/// Private inline result; successful construction keeps both charges until call end.
pub(crate) struct ScalarOutput<'a> {
    retained: Reservation<'a>,
    allowance: Reservation<'a>,
}

impl ScalarOutput<'_> {
    /// Construct only after reservation, releasing charges on error or unwind.
    pub(crate) fn finish(self, construct: impl FnOnce() -> Result<Value>) -> Result<Value> {
        let value = construct()?;
        self.retained.keep();
        self.allowance.keep();
        Ok(value)
    }
}

/// Initialized, fixed-length private result. Only finish can transfer its Vec.
pub(crate) struct Output<'a, T> {
    buffer: Buffer<'a, T>,
    result: ScalarOutput<'a>,
}

impl<T> Output<'_, T> {
    pub(crate) fn as_mut_slice(&mut self) -> &mut [T] {
        &mut self.buffer.data
    }

    /// The trusted adapter consumes the Vec without growth, within its final bound.
    /// Extra allocations inside freeze are outside this managed-storage facade.
    pub(crate) fn finish(self, freeze: impl FnOnce(Vec<T>) -> Result<Value>) -> Result<Value> {
        let Self { buffer, result } = self;
        let Buffer { data, reservation } = buffer;
        // Both reservations remain live while Vec and final storage can overlap.
        let value = result.finish(|| freeze(data))?;
        drop(reservation);
        Ok(value)
    }
}

/// Workspace has borrowed slice access only and cannot be frozen into a Value.
pub(crate) struct Scratch<'a, T> {
    buffer: Buffer<'a, T>,
}

impl<T> AsRef<[T]> for Scratch<'_, T> {
    fn as_ref(&self) -> &[T] {
        &self.buffer.data
    }
}

impl<T> AsMut<[T]> for Scratch<'_, T> {
    fn as_mut(&mut self) -> &mut [T] {
        &mut self.buffer.data
    }
}

#[cfg(test)]
mod tests;
