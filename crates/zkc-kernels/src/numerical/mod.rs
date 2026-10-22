//! Scoped numerical work and typed storage, independent of VM and native values.
//! Limits describe requested managed payloads, not allocator overhead or RSS.
mod memory;
mod views;
pub use memory::payload_bytes;
use memory::{Buffer, Reservation};
use std::cell::Cell;
pub use views::RowMajor;

/// Fixed work, managed payload and aggregate result ceilings for one call.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Limits {
    pub work: u64,
    pub memory: usize,
    pub outputs: usize,
}
/// Accepted work and currently reserved payloads; successful results stay reserved.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Usage {
    pub work: u64,
    pub memory: usize,
    pub outputs: usize,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    Work,
    Memory,
    OutputBytes,
    Allocation,
}
impl Error {
    pub const fn code(self) -> &'static str {
        match self {
            Self::Work => "numerical-work",
            Self::Memory => "numerical-bytes",
            Self::OutputBytes => "output-bytes",
            Self::Allocation => "allocation",
        }
    }
}
impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.code())
    }
}
impl std::error::Error for Error {}
pub type Result<T> = std::result::Result<T, Error>;

/// Fixed call limits without backend resource authority or borrowed policy state.
pub struct Call {
    limits: Limits,
    work: Cell<u64>,
    memory: Cell<usize>,
    outputs: Cell<usize>,
}

impl Call {
    /// Start an empty call scope with caller-selected finite limits.
    pub fn new(limits: Limits) -> Self {
        Self {
            limits,
            work: Cell::new(0),
            memory: Cell::new(0),
            outputs: Cell::new(0),
        }
    }

    /// Current conservative managed charges, excluding upstream hidden storage.
    pub fn usage(&self) -> Usage {
        Usage {
            work: self.work.get(),
            memory: self.memory.get(),
            outputs: self.outputs.get(),
        }
    }

    /// Admit a conservative bound before performing work. Accepted units stay spent.
    pub fn work(&self, units: u64) -> Result<()> {
        let next = self
            .work
            .get()
            .checked_add(units)
            .filter(|next| *next <= self.limits.work)
            .ok_or(Error::Work)?;
        self.work.set(next);
        Ok(())
    }

    /// Checked setup plus a conservative per-element bound, including empty calls.
    pub fn work_items(&self, len: usize, per_item: u64, setup: u64) -> Result<()> {
        let units = u64::try_from(len)
            .ok()
            .and_then(|len| len.checked_mul(per_item))
            .and_then(|units| units.checked_add(setup))
            .ok_or(Error::Work)?;
        self.work(units)
    }

    /// Reserve an inline scalar result without allocating a one-element buffer.
    pub fn scalar(&self, retained_bytes: usize) -> Result<ScalarOutput<'_>> {
        if retained_bytes > self.limits.outputs || retained_bytes > isize::MAX as usize {
            return Err(Error::OutputBytes);
        }
        let allowance = Reservation::new(
            &self.outputs,
            retained_bytes,
            self.limits.outputs,
            Error::OutputBytes,
        )?;
        let retained = self.reserve_memory(retained_bytes)?;
        Ok(ScalarOutput {
            retained,
            allowance,
        })
    }

    /// Reserve aggregate results and the staging/final overlap before allocation.
    /// The caller determines shape and per-value semantics.
    pub fn output<T: Clone>(
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

    /// Reserve and initialize private scratch, releasing its charge on drop.
    pub fn scratch<T: Clone>(&self, len: usize, initial: T) -> Result<Scratch<'_, T>> {
        let reservation = self.reserve_memory(payload_bytes::<T>(len)?)?;
        Ok(Scratch {
            buffer: Buffer::new(len, initial, reservation)?,
        })
    }

    /// Reserve adapter-owned typed workspace without allocating a second buffer.
    /// Keep the guard alive through the corresponding vectors' destruction.
    /// Provider caches, allocator overhead and hidden scratch are outside this scope.
    pub fn reserve_workspace<T>(&self, elements: usize) -> Result<impl Drop + '_> {
        self.reserve_memory(payload_bytes::<T>(elements)?)
    }

    fn reserve_memory(&self, bytes: usize) -> Result<Reservation<'_>> {
        Reservation::new(&self.memory, bytes, self.limits.memory, Error::Memory)
    }
}

/// Private inline result; successful construction keeps both charges until call end.
pub struct ScalarOutput<'a> {
    retained: Reservation<'a>,
    allowance: Reservation<'a>,
}

impl ScalarOutput<'_> {
    /// Construct only after reservation, releasing charges on error or unwind.
    pub fn finish<V, E>(
        self,
        construct: impl FnOnce() -> std::result::Result<V, E>,
    ) -> std::result::Result<V, E> {
        let value = construct()?;
        self.retained.keep();
        self.allowance.keep();
        Ok(value)
    }
}

/// Initialized, fixed-length private result. Only finish can transfer its Vec.
pub struct Output<'a, T> {
    buffer: Buffer<'a, T>,
    result: ScalarOutput<'a>,
}

impl<T> Output<'_, T> {
    pub fn as_mut_slice(&mut self) -> &mut [T] {
        &mut self.buffer.data
    }

    /// The trusted adapter consumes the Vec without growth, within its final bound.
    /// Extra allocations inside freeze are outside this managed-storage facade.
    pub fn finish<V, E>(
        self,
        freeze: impl FnOnce(Vec<T>) -> std::result::Result<V, E>,
    ) -> std::result::Result<V, E> {
        let Self { buffer, result } = self;
        let Buffer { data, reservation } = buffer;
        // Both reservations remain live while Vec and final storage can overlap.
        let value = result.finish(|| freeze(data))?;
        drop(reservation);
        Ok(value)
    }
}

/// Workspace has borrowed slice access only and cannot be published through the result API.
pub struct Scratch<'a, T> {
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
mod tests {
    use super::*;
    #[test]
    fn counter_overflow_does_not_reserve() {
        let counter = Cell::new(usize::MAX);
        for error in [Error::OutputBytes, Error::Memory] {
            assert!(
                matches!(Reservation::new(&counter, 1, usize::MAX, error), Err(e) if e == error)
            );
            assert_eq!(counter.get(), usize::MAX);
        }
    }
    #[test]
    fn allocation_failure_releases_reservation() {
        let call = Call::new(Limits {
            work: 0,
            memory: 32,
            outputs: 0,
        });
        let reservation = call.reserve_memory(32).unwrap();
        assert!(matches!(
            Buffer::new(usize::MAX, 0u64, reservation),
            Err(Error::Allocation)
        ));
        assert_eq!(call.usage().memory, 0);
        call.scratch(4, 0u64).unwrap();
    }
}
