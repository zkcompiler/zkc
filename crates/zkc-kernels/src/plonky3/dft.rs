//! Natural-order transform plans over installed prime bases.
//!
//! Direction selects an algorithm within the upstream DFT contract.
//! Extension basis and coset semantics stay with the
//! numerical adapter. Retained twiddles belong to the reusable kernel owner.
use p3_dft::{Radix2DFTSmallBatch, TwoAdicSubgroupDft};
use p3_field::TwoAdicField;
use p3_matrix::{Matrix, dense::RowMajorMatrix};
use p3_monty_31::dft::RecursiveDft;

/// Monty31 forward evaluation and interpolation use separate prepared plans.
#[derive(Clone, Default)]
pub struct Monty31<F: TwoAdicField> {
    forward: RecursiveDft<F>,
    inverse: Radix2DFTSmallBatch<F>,
}
impl<F: TwoAdicField> TwoAdicSubgroupDft<F> for Monty31<F>
where
    RecursiveDft<F>: TwoAdicSubgroupDft<F>,
{
    type Evaluations = RowMajorMatrix<F>;
    fn dft_batch(&self, matrix: RowMajorMatrix<F>) -> Self::Evaluations {
        self.forward.dft_batch(matrix).to_row_major_matrix()
    }
    fn idft_batch(&self, matrix: RowMajorMatrix<F>) -> RowMajorMatrix<F> {
        self.inverse.idft_batch(matrix)
    }
}
