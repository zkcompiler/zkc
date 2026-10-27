//! Native policy admission and error translation for independent numerical scopes.
pub(crate) mod coset;
pub(crate) mod expression;
pub(crate) mod opening;
use crate::Value;
use crate::{Policy, Result, exhausted};
use zkc_kernels::numerical::{self, Scratch};

/// The native adapter selects the numerical limits; no backend authority enters
/// the scope. Constructors retain the storage required by their freeze contract.
pub(crate) struct Call {
    scope: numerical::Call,
}
impl Call {
    pub(crate) fn new(policy: &Policy, available: usize) -> Self {
        Self {
            scope: numerical::Call::new(numerical::Limits {
                work: policy.max_numerical_work,
                memory: policy.max_numerical_bytes,
                outputs: available.min(policy.max_value_bytes),
            }),
        }
    }
    pub(crate) fn work(&self, units: u64) -> Result<()> {
        self.scope.work(units).map_err(failure)
    }
    pub(crate) fn work_items(&self, len: usize, per_item: u64, setup: u64) -> Result<()> {
        self.scope.work_items(len, per_item, setup).map_err(failure)
    }
    pub(crate) fn scalar(&self, retained_bytes: usize) -> Result<ScalarOutput<'_>> {
        self.scope
            .scalar(retained_bytes)
            .map(ScalarOutput)
            .map_err(failure)
    }
    pub(crate) fn output<T: Clone>(
        &self,
        len: usize,
        initial: T,
        retained_bytes: usize,
    ) -> Result<Output<'_, T>> {
        self.scope
            .output(len, initial, retained_bytes)
            .map(Output)
            .map_err(failure)
    }
    pub(crate) fn scratch<T: Clone>(&self, len: usize, initial: T) -> Result<Scratch<'_, T>> {
        self.scope.scratch(len, initial).map_err(failure)
    }
    /// The final constructor adopts this Vec without allocating another buffer.
    pub(crate) fn output_owned<T: Clone>(
        &self,
        len: usize,
        initial: T,
        retained_bytes: usize,
    ) -> Result<Output<'_, T>> {
        self.scope
            .output_owned(len, initial, retained_bytes)
            .map(Output)
            .map_err(failure)
    }
    pub(crate) fn memory_bytes(&self) -> usize {
        self.scope.usage().memory
    }
    /// Couple provider-owned storage to its charge before allocation. Dense
    /// nonresident callers retain their existing, uncharged construction path.
    pub(crate) fn destination<T>(
        &self,
        resident: bool,
        bytes: usize,
        construct: impl FnOnce() -> Result<T>,
    ) -> Result<Destination<'_, T>> {
        let reservation = if resident {
            Some(self.reserve_workspace::<u8>(bytes)?)
        } else {
            None
        };
        Ok(Destination {
            storage: construct()?,
            reservation,
        })
    }
    pub(crate) fn reserve_workspace<T>(
        &self,
        elements: usize,
    ) -> Result<numerical::StorageReservation<'_>> {
        self.scope.reserve_workspace::<T>(elements).map_err(failure)
    }
}
fn failure(error: numerical::Error) -> zkc_runtime::vm::BackendError {
    exhausted(error.code())
}
#[cfg(test)]
mod tests;

/// Final native values are constructed under the independent scope's reservations.
pub(crate) struct ScalarOutput<'a>(numerical::ScalarOutput<'a>);
impl ScalarOutput<'_> {
    pub(crate) fn finish(self, construct: impl FnOnce() -> Result<Value>) -> Result<Value> {
        self.0.finish(construct)
    }
}
pub(crate) struct Output<'a, T>(numerical::Output<'a, T>);
impl<T> Output<'_, T> {
    pub(crate) fn as_mut_slice(&mut self) -> &mut [T] {
        self.0.as_mut_slice()
    }
    pub(crate) fn finish(self, freeze: impl FnOnce(Vec<T>) -> Result<Value>) -> Result<Value> {
        self.0.finish(freeze)
    }
}

/// A private final buffer and its reservation have one lifetime. Field order
/// destroys abandoned storage before releasing its charge, including on unwind.
pub(crate) struct Destination<'a, T> {
    storage: T,
    reservation: Option<numerical::StorageReservation<'a>>,
}
impl<T> std::ops::Deref for Destination<'_, T> {
    type Target = T;
    fn deref(&self) -> &T {
        &self.storage
    }
}
impl<T> std::ops::DerefMut for Destination<'_, T> {
    fn deref_mut(&mut self) -> &mut T {
        &mut self.storage
    }
}
impl<T> Destination<'_, T> {
    /// The constructor adopts this buffer without a second element allocation.
    /// Keep charges live through construction and after successful publication.
    pub(crate) fn finish(self, freeze: impl FnOnce(T) -> Result<Value>) -> Result<Value> {
        let Self {
            storage,
            reservation,
        } = self;
        let value = freeze(storage)?;
        if let Some(reservation) = reservation {
            reservation.retain();
        }
        Ok(value)
    }
}
