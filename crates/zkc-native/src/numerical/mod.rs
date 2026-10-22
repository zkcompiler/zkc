//! Native policy admission and error translation for independent numerical scopes.
pub(crate) mod coset;
pub(crate) mod expression;
pub(crate) mod opening;
use crate::Value;
use crate::{Policy, Result, exhausted};
use zkc_kernels::numerical;
use zkc_kernels::numerical::Scratch;

/// The native adapter selects the numerical limits; no backend authority enters
/// the scope. Value constructors run while staging and result charges overlap.
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
    pub(crate) fn reserve_workspace<T>(&self, elements: usize) -> Result<impl Drop + '_> {
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
