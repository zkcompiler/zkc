//! Shared geometry and admission for column-major coset operations.
use crate::{Policy, Result, exhausted, refused, value::size};

/// The fixed logical column-major shape. Domain validation stays with providers.
#[derive(Clone, Copy)]
pub(crate) struct CosetBatchShape {
    pub(crate) width: usize,
    pub(crate) height: usize,
    pub(crate) output_height: usize,
    pub(crate) input_len: usize,
    pub(crate) output_len: usize,
}

impl CosetBatchShape {
    pub(crate) fn new(
        len: usize,
        width: usize,
        height: usize,
        output_height: usize,
    ) -> Result<Self> {
        let input_len = width
            .checked_mul(height)
            .ok_or_else(|| exhausted("size-overflow"))?;
        if input_len != len {
            return Err(refused("coset-batch-shape"));
        }
        let output_len = width
            .checked_mul(output_height)
            .ok_or_else(|| exhausted("size-overflow"))?;
        Ok(Self {
            width,
            height,
            output_height,
            input_len,
            output_len,
        })
    }

    /// Common whole-vector admission, after the provider validates its domains.
    /// A single-point evaluation uses the same geometry with output height one.
    pub(crate) fn admit(
        self,
        policy: &Policy,
        element_bytes: usize,
        available: usize,
    ) -> Result<usize> {
        policy.vector_width(self.input_len, element_bytes)?;
        policy.vector_width(self.output_len, element_bytes)?;
        let retained = size(self.output_len, element_bytes)?;
        policy.output(retained, available)?;
        Ok(retained)
    }

    /// Shared weights cost O(height), followed by O(width * height) dot products.
    /// Count initialization, copies, domain powers and complete extension
    /// multiplication conservatively in base-coordinate units. Providers supply
    /// their inversion count; setup also covers domain construction/powers.
    pub(crate) fn evaluation_work(self, degree: usize, inversions: usize) -> Result<u64> {
        if self.width == 0 {
            return Ok(1);
        }
        let checked = || {
            let arithmetic = degree.checked_mul(degree)?;
            let per_element = arithmetic.checked_mul(16)?.checked_add(16)?;
            // One product/sum per input element. Eight product-equivalent
            // passes per row cover domain traversal, prefix construction,
            // inverse propagation, weight scaling and scratch initialization.
            // Each equivalent already allows 16*d^2+16 base-coordinate units.
            let elements = self
                .input_len
                .checked_add(self.height.checked_mul(8)?)?
                .checked_add(self.width.checked_mul(2)?)?;
            // Four setup allowances cover bounded <=64-bit domain powers and
            // domain construction, in addition to the provider's inversions.
            let setup = inversions
                .checked_add(4)?
                .checked_mul(4096)?
                .checked_mul(arithmetic)?;
            elements.checked_mul(per_element)?.checked_add(setup)
        };
        checked()
            .and_then(|n| u64::try_from(n).ok())
            .ok_or_else(|| exhausted("size-overflow"))
    }

    /// DFT butterfly work scales with the number of base coordinates; shift
    /// multiplication uses the complete extension algebra. Include loop/copy,
    /// initialization, normalization, and a bounded inversion setup allowance.
    /// This is a conservative admission score, not CPU or constant-time cost.
    pub(crate) fn extension_work(self, degree: usize) -> Result<u64> {
        if self.width == 0 {
            return Ok(1);
        }
        let checked = || {
            let butterflies = self
                .input_len
                .checked_mul(self.height.ilog2() as usize)?
                .checked_add(
                    self.output_len
                        .checked_mul(self.output_height.ilog2() as usize)?,
                )?;
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
}
