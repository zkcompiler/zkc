//! Owned immutable buffers for synchronous native kernels.
//!
//! A successful reservation permits publication without allocating backing
//! payload or descriptor storage. Every old reference retains its contents on
//! success and error. These are implementation contracts, not Rust proofs of
//! payload immutability or an external adapter's behavior.
//! Adapters must return errors rather than panic during binding/reservation;
//! custody recovery from a panic there is outside the current runtime contract.
mod packed;
mod segmented;
use crate::Error;
pub use packed::PackedBuffers;
pub use segmented::SegmentedBuffers;

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct BufferUsage {
    pub elements: usize,
    pub buffers: usize,
    /// Retained backing capacity, excluding allocator bookkeeping.
    pub reserved_bytes: usize,
}

pub trait BufferStore<T: Copy> {
    type Reference: Clone;
    /// Minimum retained backing capacity needed to reserve additional elements
    /// and references, measured from current live usage. Includes old spare
    /// capacity, not just live payloads. Reservation may allocate more; consumers
    /// with a capacity policy must also inspect actual usage before execution.
    /// It excludes allocator bookkeeping and implementation-external resources.
    fn required_bytes(&self, elements: usize, buffers: usize) -> Result<usize, Error>;
    /// Preserve published contents on all paths. May grow private capacity on
    /// failure; no provider or protocol effects may occur here.
    /// Success supports any publications totalling at most the requested
    /// additional elements and references, without payload/descriptor allocation.
    /// Repeated reservations without publication are not additive: reserving
    /// four twice guarantees four more elements, not eight.
    fn reserve(&mut self, elements: usize, buffers: usize) -> Result<(), Error>;
    /// Copy into exclusively owned storage. Published contents cannot change.
    /// Insufficient reserved capacity is a host error, never a logical stop.
    fn publish(&mut self, values: &[T]) -> Result<Self::Reference, Error>;
    /// The reference must belong to this store and denote a complete buffer.
    /// The returned borrow cannot outlive the owning store.
    fn read(&self, reference: &Self::Reference) -> Result<&[T], Error>;
    fn usage(&self) -> BufferUsage;
}

pub(crate) fn add(a: usize, b: usize) -> Result<usize, Error> {
    a.checked_add(b).ok_or(Error("capacity-overflow"))
}
pub(crate) fn bytes<T>(count: usize) -> Result<usize, Error> {
    count
        .checked_mul(std::mem::size_of::<T>())
        .ok_or(Error("capacity-overflow"))
}
