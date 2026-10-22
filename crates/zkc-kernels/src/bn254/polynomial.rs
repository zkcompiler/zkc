//! BN254 polynomial transforms and interpolation with caller-owned storage.
use super::Scalar as F;
use crate::fields::{Error, Result};
use ark_ff::{FftField, Field, One, Zero};
use ark_poly::{EvaluationDomain, Radix2EvaluationDomain};

/// A checked exact radix-two coset. The upstream domain has public fields;
/// this wrapper admits construction and exposes only immutable provider access.
#[derive(Clone, Copy, Debug)]
pub struct Domain(Radix2EvaluationDomain<F>);
impl Domain {
    /// Refuse non-powers of two, unsupported sizes and the zero coset shift.
    pub fn new(size: usize, shift: F) -> Option<Self> {
        if !size.is_power_of_two() || size.trailing_zeros() > F::TWO_ADICITY || shift.is_zero() {
            return None;
        }
        Radix2EvaluationDomain::new(size)?
            .get_coset(shift)
            .map(Self)
    }
}
impl std::ops::Deref for Domain {
    type Target = Radix2EvaluationDomain<F>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

/// Invalid batch or workspace extents, or nonzero discarded coefficients.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BatchError {
    BatchShape,
    CoefficientCount,
    SizeOverflow,
}
impl std::fmt::Display for BatchError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Self::BatchShape => "invalid polynomial batch shape or workspace",
            Self::CoefficientCount => "nonzero discarded polynomial coefficient",
            Self::SizeOverflow => "polynomial batch size overflow",
        })
    }
}
impl std::error::Error for BatchError {}

/// Checked column-major coefficient blocks for an exact output size.
/// Construction checks extents and discarded coefficients without constructing
/// a domain or performing transform arithmetic. The immutable borrow keeps those
/// checks valid while the caller admits resources and realizes the domain.
pub struct CoefficientBatch<'a> {
    coefficients: &'a [F],
    width: usize,
    height: usize,
    output_size: usize,
    output_len: usize,
}
impl<'a> CoefficientBatch<'a> {
    pub fn new(
        coefficients: &'a [F],
        width: usize,
        height: usize,
        output_size: usize,
    ) -> std::result::Result<Self, BatchError> {
        let input_len = width.checked_mul(height).ok_or(BatchError::SizeOverflow)?;
        if coefficients.len() != input_len {
            return Err(BatchError::BatchShape);
        }
        let output_len = width
            .checked_mul(output_size)
            .ok_or(BatchError::SizeOverflow)?;
        if width != 0
            && (!output_size.is_power_of_two() || output_size.trailing_zeros() > F::TWO_ADICITY)
        {
            return Err(BatchError::BatchShape);
        }
        if height > output_size
            && coefficients
                .chunks_exact(height)
                .any(|column| column[output_size..].iter().any(|c| !c.is_zero()))
        {
            return Err(BatchError::CoefficientCount);
        }
        Ok(Self {
            coefficients,
            width,
            height,
            output_size,
            output_len,
        })
    }

    /// Evaluate on a domain matching the checked output size, into an exact
    /// destination using a reusable Vec with capacity at least that size.
    /// Its initial length and contents are arbitrary;
    /// neither the caller's Vec capacity nor the borrowed coefficients change.
    /// Extent checks precede writes, and coefficient tails are not scanned again.
    /// Zero-width batches require an empty destination and do not use scratch.
    /// Arkworks' internal transform allocations remain provider-owned.
    pub fn write_into(
        &self,
        domain: Domain,
        scratch: &mut Vec<F>,
        destination: &mut [F],
    ) -> std::result::Result<(), BatchError> {
        if destination.len() != self.output_len {
            return Err(BatchError::BatchShape);
        }
        if self.width == 0 {
            return Ok(());
        }
        if domain.size() != self.output_size || scratch.capacity() < self.output_size {
            return Err(BatchError::BatchShape);
        }
        scratch.resize(self.output_size, F::zero());
        let count = self.height.min(self.output_size);
        for (column, result) in destination.chunks_exact_mut(self.output_size).enumerate() {
            scratch.fill(F::zero());
            let begin = column * self.height;
            scratch[..count].copy_from_slice(&self.coefficients[begin..begin + count]);
            domain.fft_in_place(scratch);
            result.copy_from_slice(scratch);
        }
        Ok(())
    }
}

/// Interpolate independent column-major evaluation vectors and evaluate them
/// on another exact coset. The destination must have exactly width * output
/// size elements; scratch capacity must cover the larger domain for nonzero
/// width. Scratch length and contents are arbitrary and its capacity is retained.
/// Shape checks precede writes. A nonzero discarded coefficient can be found in
/// a later column, leaving a partially written private destination that the
/// caller must discard on error. Inputs are immutable. Arkworks' internal
/// transform allocations remain provider-owned.
pub fn coset_extend_into(
    values: &[F],
    width: usize,
    input: Domain,
    output: Domain,
    scratch: &mut Vec<F>,
    destination: &mut [F],
) -> std::result::Result<(), BatchError> {
    let input_len = width
        .checked_mul(input.size())
        .ok_or(BatchError::SizeOverflow)?;
    let output_len = width
        .checked_mul(output.size())
        .ok_or(BatchError::SizeOverflow)?;
    if values.len() != input_len || destination.len() != output_len {
        return Err(BatchError::BatchShape);
    }
    if width == 0 {
        return Ok(());
    }
    if scratch.capacity() < input.size().max(output.size()) {
        return Err(BatchError::BatchShape);
    }
    for (column, result) in values
        .chunks_exact(input.size())
        .zip(destination.chunks_exact_mut(output.size()))
    {
        scratch.clear();
        scratch.extend_from_slice(column);
        input.ifft_in_place(scratch);
        if scratch
            .get(output.size()..)
            .is_some_and(|tail| tail.iter().any(|c| !c.is_zero()))
        {
            return Err(BatchError::CoefficientCount);
        }
        scratch.resize(output.size(), F::zero());
        output.fft_in_place(scratch);
        result.copy_from_slice(scratch);
    }
    Ok(())
}

/// Serial Montgomery inversion with explicitly supplied prefix storage. Unlike
/// Arkworks' allocating convenience routine, both arrays belong to the caller. No provider-private Vec or Rayon scratch is involved.
pub fn serial_batch_inverse_into(
    denominators: &[F],
    prefixes: &mut [F],
    mut finish: impl FnMut(usize, F),
) -> Result<()> {
    if denominators.len() != prefixes.len() {
        return Err(Error::LengthMismatch);
    }
    let mut product = F::one();
    for (prefix, denominator) in prefixes.iter_mut().zip(denominators) {
        *prefix = product;
        product *= denominator;
    }
    let mut inverse = product.inverse().ok_or(Error::ZeroInverse)?;
    for (row, (prefix, denominator)) in prefixes.iter_mut().zip(denominators).enumerate().rev() {
        let denominator_inverse = *prefix * inverse;
        inverse *= denominator;
        finish(row, denominator_inverse);
        *prefix = denominator_inverse;
    }
    Ok(())
}

/// Evaluate exact column-major coset values into caller-owned storage.
/// Shape checks precede writes. No transform is used.
pub fn coset_evaluate_at_into(
    values: &[F],
    domain: Domain,
    point: F,
    weights: &mut [F],
    destination: &mut [F],
) -> Result<()> {
    if weights.len() != domain.size()
        || destination.len().checked_mul(domain.size()) != Some(values.len())
    {
        return Err(Error::LengthMismatch);
    }
    for (row, (x, denominator)) in domain.elements().zip(weights.iter_mut()).enumerate() {
        if point == x {
            for (column, result) in values.chunks_exact(domain.size()).zip(destination) {
                *result = column[row];
            }
            return Ok(());
        }
        *denominator = point - x;
    }
    ark_ff::serial_batch_inversion_and_mul(weights, &F::one());
    let scale = domain.evaluate_vanishing_polynomial(point)
        * domain.size_inv
        * domain.offset_inv.pow([domain.size() as u64]);
    for (inverse, x) in weights.iter_mut().zip(domain.elements()) {
        *inverse *= scale * x;
    }
    for (column, result) in values.chunks_exact(domain.size()).zip(destination) {
        *result = column
            .iter()
            .zip(weights.iter())
            .fold(F::zero(), |sum, (value, weight)| sum + *value * *weight);
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn horner(coefficients: &[F], point: F) -> F {
        coefficients
            .iter()
            .rev()
            .fold(F::zero(), |value, coefficient| value * point + coefficient)
    }

    fn evaluations(coefficients: &[F], domain: Domain) -> Vec<F> {
        domain.elements().map(|x| horner(coefficients, x)).collect()
    }

    #[test]
    fn coefficient_batches_match_horner_without_reallocating_scratch() {
        for width in [1, 3, 16] {
            for (height, size) in [(0, 1), (0, 8), (1, 1), (1, 8), (3, 8), (8, 8), (5, 2)] {
                let domain = Domain::new(size, F::from(7)).unwrap();
                let mut coefficients = Vec::new();
                let mut expected = Vec::new();
                for column in 0..width {
                    let block: Vec<_> = (0..height)
                        .map(|row| {
                            if row >= size || (column == 0 && width > 1) {
                                F::zero()
                            } else {
                                F::from((19 * column + 7 * row * row + 1) as u64)
                            }
                        })
                        .collect();
                    expected.extend(evaluations(&block, domain));
                    coefficients.extend(block);
                }
                let original = coefficients.clone();
                let batch =
                    CoefficientBatch::new(&coefficients, width, height, domain.size()).unwrap();
                for (capacity, initial_len) in [(size, 0), (size, size), (size + 3, size + 3)] {
                    let mut scratch = Vec::with_capacity(capacity);
                    scratch.resize(initial_len, F::from(97));
                    let pointer = scratch.as_ptr();
                    let capacity = scratch.capacity();
                    let mut destination = vec![F::from(101); width * size];
                    for _ in 0..2 {
                        batch
                            .write_into(domain, &mut scratch, &mut destination)
                            .unwrap();
                        assert_eq!(destination, expected);
                        assert_eq!(scratch.len(), size);
                        assert_eq!(scratch.capacity(), capacity);
                        assert_eq!(scratch.as_ptr(), pointer);
                        assert_eq!(coefficients, original);
                        destination.fill(F::from(101));
                    }
                }
            }
        }
    }

    #[test]
    fn extension_interpolates_horner_values_without_reallocating_scratch() {
        for width in [1, 3, 16] {
            for (height, size) in [
                (1, 1),
                (1, 8),
                (4, 1),
                (4, 2),
                (4, 8),
                (8, 4),
                (8, 8),
                (8, 16),
            ] {
                let input = Domain::new(height, F::from(7)).unwrap();
                let output = Domain::new(size, F::from(11)).unwrap();
                let mut values = Vec::new();
                let mut expected = Vec::new();
                for column in 0..width {
                    let count = if column == 0 && width > 1 {
                        0
                    } else {
                        (column + height.min(size)) % (height.min(size) + 1)
                    };
                    let coefficients: Vec<_> = (0..count)
                        .map(|row| F::from((17 * column + 5 * row + 1) as u64))
                        .collect();
                    values.extend(evaluations(&coefficients, input));
                    expected.extend(evaluations(&coefficients, output));
                }
                let original = values.clone();
                let workspace = height.max(size);
                for (capacity, initial_len) in [
                    (workspace, 0),
                    (workspace, workspace),
                    (workspace + 3, workspace + 3),
                ] {
                    let mut scratch = Vec::with_capacity(capacity);
                    scratch.resize(initial_len, F::from(97));
                    let pointer = scratch.as_ptr();
                    let capacity = scratch.capacity();
                    let mut destination = vec![F::from(101); width * size];
                    for _ in 0..2 {
                        coset_extend_into(
                            &values,
                            width,
                            input,
                            output,
                            &mut scratch,
                            &mut destination,
                        )
                        .unwrap();
                        assert_eq!(destination, expected);
                        assert_eq!(scratch.len(), size);
                        assert_eq!(scratch.capacity(), capacity);
                        assert_eq!(scratch.as_ptr(), pointer);
                        assert_eq!(values, original);
                        destination.fill(F::from(101));
                    }
                }
            }
        }
    }

    #[test]
    fn coefficient_batches_check_all_discarded_tails_before_writing() {
        let domain = Domain::new(2, F::from(7)).unwrap();
        for column in 0..3 {
            for row in [2, 4] {
                let mut coefficients = vec![F::zero(); 15];
                coefficients[column * 5 + row] = F::one();
                assert_eq!(
                    CoefficientBatch::new(&coefficients, 3, 5, domain.size()).err(),
                    Some(BatchError::CoefficientCount)
                );
            }
        }
        // All discarded coefficients are representation zeros, including in
        // later blocks. Construction checks once; repeated writes use the borrow.
        let coefficients = [F::one(), F::zero(), F::zero(), F::zero(), F::zero()];
        let batch = CoefficientBatch::new(&coefficients, 1, 5, domain.size()).unwrap();
        let mut scratch = Vec::with_capacity(2);
        let mut destination = [F::zero(); 2];
        batch
            .write_into(domain, &mut scratch, &mut destination)
            .unwrap();
        assert_eq!(destination, [F::one(); 2]);
    }

    #[test]
    fn coefficient_batches_refuse_bad_extents_before_writing() {
        let domain = Domain::new(8, F::from(7)).unwrap();
        for (len, width, height, expected) in [
            (1, 0, usize::MAX, BatchError::BatchShape),
            (5, 2, 3, BatchError::BatchShape),
            (7, 2, 3, BatchError::BatchShape),
            (0, usize::MAX, 2, BatchError::SizeOverflow),
            (0, usize::MAX, 0, BatchError::SizeOverflow),
        ] {
            assert_eq!(
                CoefficientBatch::new(&vec![F::zero(); len], width, height, domain.size()).err(),
                Some(expected)
            );
        }
        for size in [0, 3, 6] {
            assert_eq!(
                CoefficientBatch::new(&[F::one()], 1, 1, size).err(),
                Some(BatchError::BatchShape)
            );
        }
        let coefficients = [F::one(); 6];
        let batch = CoefficientBatch::new(&coefficients, 2, 3, domain.size()).unwrap();
        for (capacity, output_len) in [(8, 0), (8, 15), (8, 17), (0, 16), (7, 16)] {
            let mut scratch = vec![F::from(97); capacity];
            let original = scratch.clone();
            let pointer = scratch.as_ptr();
            let capacity = scratch.capacity();
            let mut destination = vec![F::from(101); output_len];
            assert_eq!(
                batch.write_into(domain, &mut scratch, &mut destination),
                Err(BatchError::BatchShape)
            );
            assert_eq!(destination, vec![F::from(101); output_len]);
            assert_eq!(scratch, original);
            assert_eq!(scratch.capacity(), capacity);
            assert_eq!(scratch.as_ptr(), pointer);
        }
    }

    #[test]
    fn coefficient_batches_refuse_a_different_domain_size_before_writing() {
        let coefficients = [F::one(); 6];
        let batch = CoefficientBatch::new(&coefficients, 2, 3, 8).unwrap();
        let mut scratch = vec![F::from(97); 16];
        let original = scratch.clone();
        let pointer = scratch.as_ptr();
        let capacity = scratch.capacity();
        let mut destination = [F::from(101); 16];
        for size in [1, 4, 16] {
            let domain = Domain::new(size, F::from(7)).unwrap();
            assert_eq!(
                batch.write_into(domain, &mut scratch, &mut destination),
                Err(BatchError::BatchShape)
            );
            assert_eq!(destination, [F::from(101); 16]);
            assert_eq!(scratch, original);
            assert_eq!(scratch.capacity(), capacity);
            assert_eq!(scratch.as_ptr(), pointer);
        }
    }

    #[test]
    fn extension_refuses_bad_extents_before_writing() {
        for (height, size) in [(4, 8), (8, 2)] {
            let input = Domain::new(height, F::from(7)).unwrap();
            let output = Domain::new(size, F::from(11)).unwrap();
            let workspace = height.max(size);
            for (input_len, output_len, capacity) in [
                (2 * height - 1, 2 * size, workspace),
                (2 * height + 1, 2 * size, workspace),
                (2 * height, 2 * size - 1, workspace),
                (2 * height, 2 * size + 1, workspace),
                (2 * height, 2 * size, 0),
                (2 * height, 2 * size, workspace - 1),
            ] {
                let values = vec![F::one(); input_len];
                let mut destination = vec![F::from(101); output_len];
                let mut scratch = vec![F::from(97); capacity];
                let original = scratch.clone();
                let pointer = scratch.as_ptr();
                let capacity = scratch.capacity();
                assert_eq!(
                    coset_extend_into(&values, 2, input, output, &mut scratch, &mut destination),
                    Err(BatchError::BatchShape)
                );
                assert_eq!(destination, vec![F::from(101); output_len]);
                assert_eq!(scratch, original);
                assert_eq!(scratch.capacity(), capacity);
                assert_eq!(scratch.as_ptr(), pointer);
            }
        }
        let one = Domain::new(1, F::one()).unwrap();
        let two = Domain::new(2, F::one()).unwrap();
        let mut scratch = Vec::new();
        for (input, output) in [(two, one), (one, two)] {
            assert_eq!(
                coset_extend_into(&[], usize::MAX, input, output, &mut scratch, &mut []),
                Err(BatchError::SizeOverflow)
            );
        }
        assert!(scratch.is_empty());
        assert_eq!(scratch.capacity(), 0);
    }

    #[test]
    fn shrinking_extension_refuses_high_coefficients_in_later_columns() {
        let input = Domain::new(8, F::from(7)).unwrap();
        let output = Domain::new(2, F::from(11)).unwrap();
        for high_column in 0..3 {
            for row in [2, 7] {
                let mut values = Vec::new();
                let mut expected_prefix = Vec::new();
                for column in 0..3 {
                    let mut coefficients = vec![F::from((column + 1) as u64)];
                    if column == high_column {
                        coefficients.resize(row + 1, F::zero());
                        coefficients[row] = F::one();
                    } else if column < high_column {
                        expected_prefix.extend(evaluations(&coefficients, output));
                    }
                    values.extend(evaluations(&coefficients, input));
                }
                let original = values.clone();
                let mut destination = [F::from(101); 6];
                let mut scratch = Vec::with_capacity(8);
                let pointer = scratch.as_ptr();
                let capacity = scratch.capacity();
                assert_eq!(
                    coset_extend_into(&values, 3, input, output, &mut scratch, &mut destination),
                    Err(BatchError::CoefficientCount)
                );
                assert_eq!(&destination[..high_column * 2], expected_prefix.as_slice());
                assert!(
                    destination[high_column * 2..]
                        .iter()
                        .all(|value| *value == F::from(101))
                );
                assert_eq!(values, original);
                assert_eq!(scratch.capacity(), capacity);
                assert_eq!(scratch.as_ptr(), pointer);
            }
        }
    }

    #[test]
    fn zero_width_batches_leave_reusable_scratch_untouched() {
        let domain = Domain::new(8, F::from(7)).unwrap();
        let batch = CoefficientBatch::new(&[], 0, usize::MAX, domain.size()).unwrap();
        for mut scratch in [Vec::new(), vec![F::from(97); 3]] {
            let original = scratch.clone();
            let pointer = scratch.as_ptr();
            let capacity = scratch.capacity();
            batch.write_into(domain, &mut scratch, &mut []).unwrap();
            coset_extend_into(&[], 0, domain, domain, &mut scratch, &mut []).unwrap();
            assert_eq!(scratch, original);
            assert_eq!(scratch.capacity(), capacity);
            assert_eq!(scratch.as_ptr(), pointer);
            let mut destination = [F::from(101)];
            assert_eq!(
                batch.write_into(domain, &mut scratch, &mut destination),
                Err(BatchError::BatchShape)
            );
            assert_eq!(
                coset_extend_into(&[], 0, domain, domain, &mut scratch, &mut destination),
                Err(BatchError::BatchShape)
            );
            assert_eq!(destination, [F::from(101)]);
            assert_eq!(scratch, original);
        }
    }
}
