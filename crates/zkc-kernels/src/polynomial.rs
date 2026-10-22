//! Dense coefficient polynomial arithmetic, independent of physical values.
use crate::field::Coefficient;
/// Evaluate coefficients in ascending degree order with Horner's rule.
pub fn evaluate<S: Coefficient>(coefficients: &[S], x: S) -> S {
    coefficients.iter().rev().fold(S::zero(), |a, c| a * x + *c)
}
/// Sum evaluations at zero and one, including the empty polynomial.
pub fn boundary<S: Coefficient>(coefficients: &[S]) -> S {
    coefficients.first().copied().unwrap_or_else(S::zero)
        + coefficients.iter().fold(S::zero(), |a, c| a + *c)
}
/// Whether zero is represented by an empty vector and all other degrees are exact.
pub fn normalized<S: Coefficient>(coefficients: &[S]) -> bool {
    coefficients.last().is_none_or(|c| *c != S::zero())
}
/// Reverse a position's bits within a nonempty power-of-two domain.
pub fn reverse_bits(position: usize, count: usize) -> Option<usize> {
    if !count.is_power_of_two() || position >= count {
        return None;
    }
    let bits = count.trailing_zeros();
    Some(if bits == 0 {
        0
    } else {
        position.reverse_bits() >> (usize::BITS - bits)
    })
}
