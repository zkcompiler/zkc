//! Reservations for adapters passing owned vectors through provider transforms.
use super::{Call, memory::payload_bytes};
use crate::{Result, exhausted, refused};

/// The fixed logical column-major shape. Domain validation stays with providers.
#[derive(Clone, Copy)]
pub(crate) struct CosetBatch {
    pub(crate) width: usize,
    pub(crate) height: usize,
    pub(crate) size: usize,
    pub(crate) input_len: usize,
    pub(crate) output_len: usize,
}

impl CosetBatch {
    pub(crate) fn new(len: usize, width: usize, height: usize, size: usize) -> Result<Self> {
        let input_len = width
            .checked_mul(height)
            .ok_or_else(|| exhausted("size-overflow"))?;
        if input_len != len {
            return Err(refused("coset-batch-shape"));
        }
        let output_len = width
            .checked_mul(size)
            .ok_or_else(|| exhausted("size-overflow"))?;
        Ok(Self {
            width,
            height,
            size,
            input_len,
            output_len,
        })
    }

    /// DFT butterfly work scales with the number of base coordinates; shift
    /// multiplication uses the complete extension algebra. Include loop/copy,
    /// initialization, normalization, and a bounded inversion setup allowance.
    /// This is a conservative admission score, not CPU or constant-time cost.
    pub(crate) fn work(self, degree: usize) -> Result<u64> {
        if self.width == 0 {
            return Ok(1);
        }
        let checked = || {
            let butterflies = self
                .input_len
                .checked_mul(self.height.ilog2() as usize)?
                .checked_add(self.output_len.checked_mul(self.size.ilog2() as usize)?)?;
            let transforms = butterflies.checked_mul(16)?.checked_mul(degree)?;
            let per_element = degree
                .checked_mul(degree)?
                .checked_mul(8)?
                .checked_add(16)?;
            let linear = self
                .input_len
                .checked_add(self.output_len)?
                .checked_mul(per_element)?;
            let setup = self
                .width
                .checked_add(1)?
                .checked_mul(4096)?
                .checked_mul(degree)?;
            transforms.checked_add(linear)?.checked_add(setup)
        };
        checked()
            .and_then(|n| u64::try_from(n).ok())
            .ok_or_else(|| exhausted("size-overflow"))
    }

    /// Adapter-owned coefficient and scaled matrices overlap during scaling.
    /// The pinned P3 DFT and natural-order conversion reuse owned dense storage;
    /// extension flattening and reconstitution also preserve that allocation.
    pub(crate) fn p3_workspace(self) -> Result<usize> {
        self.input_len
            .checked_add(self.output_len)
            .ok_or_else(|| exhausted("size-overflow"))
    }
}

impl Call {
    /// Reserve the maximum simultaneously live typed payload before allocating
    /// any transform vectors. Keep the guard alive through their destruction.
    /// This does not allocate a second buffer and does not account provider
    /// twiddle caches, allocator overhead, or hidden provider workspace.
    pub(crate) fn transform_workspace<T>(&self, elements: usize) -> Result<impl Drop + '_> {
        self.reserve_memory(payload_bytes::<T>(elements)?)
    }
}
