//! Univariate numerical kernels over Plonky3's KoalaBear DFT.
//!
//! Logical order is `shift * generator^i`, never a bit-reversed storage order.
//! An evaluation vector is arbitrary data: these functions assert neither a
//! degree bound nor successful authentication. Extension coordinates are all
//! retained; the DFT acts over the base field on each coordinate.

use p3_dft::{Radix2DitParallel, TwoAdicSubgroupDft};
use p3_field::{ExtensionField, Field, TwoAdicField};
use p3_koala_bear::KoalaBear;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    DomainSize,
    ElementLimit,
    ZeroShift,
    CoefficientCount,
    EvaluationCount,
    Coordinate,
    FoldSize,
    PointOnDomain,
    OpeningValue,
}

/// A checked multiplicative coset. The generator is the installed base-field
/// generator embedded in `E`, including when `E` is an extension field.
#[derive(Clone, Copy, Debug)]
pub struct Domain<E> {
    size: usize,
    shift: E,
    generator: E,
}
impl<E: ExtensionField<KoalaBear>> Domain<E> {
    pub fn new(size: usize, shift: E, max_elements: usize) -> Result<Self, Error> {
        if !size.is_power_of_two() || size.trailing_zeros() as usize > KoalaBear::TWO_ADICITY {
            return Err(Error::DomainSize);
        }
        if size > max_elements {
            return Err(Error::ElementLimit);
        }
        if shift == E::ZERO {
            return Err(Error::ZeroShift);
        }
        Ok(Self {
            size,
            shift,
            generator: E::from(KoalaBear::two_adic_generator(size.trailing_zeros() as usize)),
        })
    }
    pub fn size(&self) -> usize {
        self.size
    }
    pub fn shift(&self) -> E {
        self.shift
    }
    pub fn generator(&self) -> E {
        self.generator
    }
    pub fn point(&self, index: usize) -> Result<E, Error> {
        if index >= self.size {
            return Err(Error::Coordinate);
        }
        Ok(self.shift * self.generator.exp_u64(index as u64))
    }
    pub fn contains(&self, point: E) -> bool {
        point.exp_u64(self.size as u64) == self.shift.exp_u64(self.size as u64)
    }
    pub fn folded(&self) -> Result<Self, Error> {
        if self.size < 2 {
            return Err(Error::FoldSize);
        }
        Ok(Self {
            size: self.size / 2,
            shift: self.shift.square(),
            generator: self.generator.square(),
        })
    }
}

/// Reusable DFT preparation is local numerical state, not protocol state.
#[derive(Clone, Default)]
pub struct Kernels {
    dft: Radix2DitParallel<KoalaBear>,
}
impl Kernels {
    pub fn evaluate<E: ExtensionField<KoalaBear>>(
        &self,
        coefficients: &[E],
        domain: Domain<E>,
    ) -> Result<Vec<E>, Error> {
        if coefficients.len() > domain.size {
            return Err(Error::CoefficientCount);
        }
        let mut scaled = Vec::with_capacity(domain.size);
        let mut power = E::ONE;
        for c in coefficients {
            scaled.push(*c * power);
            power *= domain.shift;
        }
        scaled.resize(domain.size, E::ZERO);
        Ok(self.dft.dft_algebra(scaled))
    }

    /// Every vector of the admitted length has a unique interpolant. This is
    /// not a low-degree test; the result may have degree `domain.size - 1`.
    pub fn interpolate<E: ExtensionField<KoalaBear>>(
        &self,
        values: &[E],
        domain: Domain<E>,
    ) -> Result<Vec<E>, Error> {
        if values.len() != domain.size {
            return Err(Error::EvaluationCount);
        }
        let mut coefficients = self.dft.idft_algebra(values.to_vec());
        let inverse = domain.shift.inverse();
        let mut power = E::ONE;
        for c in &mut coefficients {
            *c *= power;
            power *= inverse;
        }
        normalize(&mut coefficients);
        Ok(coefficients)
    }
}

pub fn evaluate_at<E: Field>(coefficients: &[E], point: E) -> E {
    coefficients
        .iter()
        .rev()
        .fold(E::ZERO, |value, c| value * point + *c)
}

pub fn normalize<E: Field>(coefficients: &mut Vec<E>) {
    while coefficients.last() == Some(&E::ZERO) {
        coefficients.pop();
    }
}

/// Even/odd polynomial folding in natural coset order. Pair i with i+n/2,
/// then place the folded value at `(shift * generator^i)^2`.
pub fn fold<E: ExtensionField<KoalaBear>>(
    values: &[E],
    domain: Domain<E>,
    challenge: E,
) -> Result<Vec<E>, Error> {
    let next = domain.folded()?;
    if values.len() != domain.size {
        return Err(Error::EvaluationCount);
    }
    let half = next.size;
    let inverse_two = E::TWO.inverse();
    let mut inverse_twice_x = inverse_two / domain.shift;
    let inverse_generator = domain.generator.inverse();
    let mut result = Vec::with_capacity(half);
    for (a, b) in values[..half].iter().zip(&values[half..]) {
        result.push((*a + *b) * inverse_two + challenge * (*a - *b) * inverse_twice_x);
        inverse_twice_x *= inverse_generator;
    }
    Ok(result)
}

/// `(p(X)-value)/(X-point)`. Refuses a wrong claimed value, even when p is
/// constant or zero. The returned coefficient vector is normalized.
pub fn divide_opening<E: Field>(coefficients: &[E], point: E, value: E) -> Result<Vec<E>, Error> {
    if coefficients.is_empty() {
        return if value == E::ZERO {
            Ok(Vec::new())
        } else {
            Err(Error::OpeningValue)
        };
    }
    let mut quotient = vec![E::ZERO; coefficients.len() - 1];
    let mut remainder = *coefficients.last().unwrap();
    for i in (1..coefficients.len()).rev() {
        quotient[i - 1] = remainder;
        remainder = coefficients[i - 1] + point * remainder;
    }
    if remainder != value {
        return Err(Error::OpeningValue);
    }
    normalize(&mut quotient);
    Ok(quotient)
}

/// Pointwise opening quotient on a coset, using one batch inversion. A point
/// on the evaluation domain is refused before allocating inversion workspace.
pub fn opening_quotient<E: ExtensionField<KoalaBear>>(
    values: &[E],
    domain: Domain<E>,
    point: E,
    value: E,
) -> Result<Vec<E>, Error> {
    let quotient = OpeningQuotient::new(values, domain, point, value)?;
    let mut denominators = vec![E::ZERO; domain.size];
    let mut result = vec![E::ZERO; domain.size];
    quotient.write_into(&mut denominators, &mut result)?;
    Ok(result)
}

/// Borrow checked mathematical inputs before admitting or allocating workspace.
/// The same validation serves the public helper and the scoped native adapter.
pub(crate) struct OpeningQuotient<'a, E> {
    values: &'a [E],
    domain: Domain<E>,
    point: E,
    value: E,
}

impl<'a, E: ExtensionField<KoalaBear>> OpeningQuotient<'a, E> {
    pub(crate) fn new(
        values: &'a [E],
        domain: Domain<E>,
        point: E,
        value: E,
    ) -> Result<Self, Error> {
        if values.len() != domain.size {
            return Err(Error::EvaluationCount);
        }
        if domain.contains(point) {
            return Err(Error::PointOnDomain);
        }
        Ok(Self {
            values,
            domain,
            point,
            value,
        })
    }

    /// Use the initialized destination as batch-inversion prefix workspace.
    /// Denominators are the only array scratch; no upstream allocator is called.
    /// Validate both storage lengths before writing either slice.
    pub(crate) fn write_into(
        &self,
        denominators: &mut [E],
        destination: &mut [E],
    ) -> Result<(), Error> {
        if denominators.len() != self.domain.size || destination.len() != self.domain.size {
            return Err(Error::EvaluationCount);
        }
        let mut x = self.domain.shift;
        for denominator in denominators.iter_mut() {
            *denominator = x - self.point;
            x *= self.domain.generator;
        }
        let mut product = E::ONE;
        for (prefix, denominator) in destination.iter_mut().zip(denominators.iter()) {
            *prefix = product;
            product *= *denominator;
        }
        let mut inverse = product.try_inverse().ok_or(Error::PointOnDomain)?;
        for ((out, denominator), evaluation) in destination
            .iter_mut()
            .zip(denominators.iter())
            .zip(self.values)
            .rev()
        {
            let denominator_inverse = *out * inverse;
            inverse *= *denominator;
            *out = (*evaluation - self.value) * denominator_inverse;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use p3_field::{BasedVectorSpace, PrimeCharacteristicRing, extension::BinomialExtensionField};
    type E = BinomialExtensionField<KoalaBear, 8>;
    fn sample(i: usize) -> E {
        E::from_basis_coefficients_fn(|j| KoalaBear::from_usize(3 * i * i + 7 * i + j + 1))
    }
    #[test]
    fn cosets_interpolation_fold_and_opening() {
        let kernels = Kernels::default();
        for log_n in 1..=9 {
            let n = 1 << log_n;
            let coefficients: Vec<_> = (0..n).map(sample).collect();
            // Non-base shifts check that no coordinate silently disappears.
            let domain = Domain::new(4 * n, sample(3), 4096).unwrap();
            let evaluations = kernels.evaluate(&coefficients, domain).unwrap();
            assert_eq!(
                kernels.interpolate(&evaluations, domain).unwrap(),
                coefficients
            );
            let challenge = sample(7);
            let folded = fold(&evaluations, domain, challenge).unwrap();
            let expected: Vec<_> = coefficients
                .as_chunks::<2>()
                .0
                .iter()
                .map(|p| p[0] + challenge * p[1])
                .collect();
            assert_eq!(
                folded,
                kernels
                    .evaluate(&expected, domain.folded().unwrap())
                    .unwrap()
            );
            let point = sample(9);
            let value = evaluate_at(&coefficients, point);
            let quotient = divide_opening(&coefficients, point, value).unwrap();
            assert_eq!(
                opening_quotient(&evaluations, domain, point, value).unwrap(),
                kernels.evaluate(&quotient, domain).unwrap()
            );
            for (i, actual) in evaluations.iter().enumerate() {
                assert_eq!(
                    *actual,
                    evaluate_at(&coefficients, domain.point(i).unwrap())
                );
            }
            assert_eq!(
                divide_opening(&coefficients, point, value + E::ONE),
                Err(Error::OpeningValue)
            );
        }
    }
    #[test]
    fn malformed_domains_and_boundaries() {
        assert!(matches!(Domain::new(0, E::ONE, 8), Err(Error::DomainSize)));
        assert!(matches!(Domain::new(3, E::ONE, 8), Err(Error::DomainSize)));
        assert!(matches!(
            Domain::new(16, E::ONE, 8),
            Err(Error::ElementLimit)
        ));
        assert!(matches!(Domain::new(8, E::ZERO, 8), Err(Error::ZeroShift)));
        let one = Domain::new(1, E::ONE, 8).unwrap();
        assert!(matches!(one.folded(), Err(Error::FoldSize)));
        assert_eq!(one.point(1), Err(Error::Coordinate));
        let k = Kernels::default();
        assert_eq!(
            k.evaluate(&[E::ONE, E::ONE], one),
            Err(Error::CoefficientCount)
        );
        assert_eq!(k.interpolate(&[], one), Err(Error::EvaluationCount));
        assert_eq!(
            opening_quotient(&[E::ONE], one, E::ONE, E::ONE),
            Err(Error::PointOnDomain)
        );
        assert_eq!(fold(&[], one, E::ONE), Err(Error::FoldSize));
        let two = Domain::new(2, E::ONE, 8).unwrap();
        assert_eq!(fold(&[E::ONE], two, E::ONE), Err(Error::EvaluationCount));
        assert_eq!(
            opening_quotient(&[], two, E::ZERO, E::ZERO),
            Err(Error::EvaluationCount)
        );
        assert_eq!(
            divide_opening::<E>(&[], E::ONE, E::ONE),
            Err(Error::OpeningValue)
        );
        assert_eq!(divide_opening::<E>(&[], E::ONE, E::ZERO), Ok(vec![]));
        assert_eq!(divide_opening(&[E::ONE], E::ONE, E::ONE), Ok(vec![]));
        assert_eq!(k.evaluate::<E>(&[], one), Ok(vec![E::ZERO]));
    }

    #[test]
    fn quotient_destinations_validate_before_writes() {
        let domain = Domain::new(4, sample(3), 4).unwrap();
        let values = [sample(5); 4];
        let mut denominators = [sample(7); 4];
        let mut destination = [sample(11); 4];
        for point in [domain.shift(), domain.point(3).unwrap()] {
            assert!(matches!(
                OpeningQuotient::new(&values, domain, point, E::ZERO),
                Err(Error::PointOnDomain)
            ));
        }
        assert!(matches!(
            OpeningQuotient::new(&values[..3], domain, E::ZERO, E::ZERO),
            Err(Error::EvaluationCount)
        ));
        let quotient = OpeningQuotient::new(&values, domain, E::ZERO, E::ZERO).unwrap();
        for (scratch_len, output_len) in [(3, 4), (4, 3)] {
            assert_eq!(
                quotient.write_into(
                    &mut denominators[..scratch_len],
                    &mut destination[..output_len],
                ),
                Err(Error::EvaluationCount)
            );
            assert_eq!(denominators, [sample(7); 4]);
            assert_eq!(destination, [sample(11); 4]);
        }
    }
}
