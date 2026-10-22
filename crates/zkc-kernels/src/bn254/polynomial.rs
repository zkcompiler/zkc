//! BN254 interpolation primitives with caller-owned destinations.
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
