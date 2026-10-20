//! Univariate numerical kernels over Plonky3's KoalaBear DFT.
//!
//! Logical order is `shift * generator^i`, never a bit-reversed storage order.
//! An evaluation vector is arbitrary data: these functions assert neither a
//! degree bound nor successful authentication. Extension coordinates are all
//! retained; the DFT acts over the base field on each coordinate.

use p3_dft::{Radix2DitParallel, TwoAdicSubgroupDft};
use p3_field::{ExtensionField, Field, PrimeCharacteristicRing, TwoAdicField};
use p3_koala_bear::KoalaBear;
use p3_matrix::dense::RowMajorMatrix;

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
    BatchShape,
    SizeOverflow,
    Allocation,
}

/// A checked multiplicative coset. The generator is the installed base-field
/// generator embedded in `E`, including when `E` is an extension field.
#[derive(Clone, Copy, Debug)]
pub struct Domain<E> {
    size: usize,
    shift: E,
    generator: KoalaBear,
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
            generator: KoalaBear::two_adic_generator(size.trailing_zeros() as usize),
        })
    }
    pub fn size(&self) -> usize {
        self.size
    }
    pub fn shift(&self) -> E {
        self.shift
    }
    pub fn generator(&self) -> E {
        E::from(self.generator)
    }
    /// The subgroup always lies in the base field, even for a non-base shift.
    /// Retain that fact when advancing extension-valued coset points.
    pub(super) fn base_generator(&self) -> KoalaBear {
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
    /// Extend independent column-major evaluation vectors into a fixed private
    /// destination. The caller admits output and transform workspace first.
    /// Neither the borrowed input nor published values are modified. The
    /// destination remains private until the complete batch succeeds.
    pub fn coset_extend_into<E: ExtensionField<KoalaBear>>(
        &self,
        values: &[E],
        width: usize,
        input: Domain<E>,
        output: Domain<E>,
        destination: &mut [E],
    ) -> Result<(), Error> {
        let input_len = width.checked_mul(input.size).ok_or(Error::SizeOverflow)?;
        let output_len = width.checked_mul(output.size).ok_or(Error::SizeOverflow)?;
        if values.len() != input_len || destination.len() != output_len {
            return Err(Error::BatchShape);
        }
        if width == 0 {
            return Ok(());
        }
        // P3 matrices are row-major internally. Every matrix element is E,
        // retaining all extension coordinates through algebra DFTs. Reserve
        // adapter allocations fallibly; provider internals own their caches.
        let mut rows = Vec::new();
        rows.try_reserve_exact(input_len)
            .map_err(|_| Error::Allocation)?;
        rows.resize(input_len, E::ZERO);
        for row in 0..input.size {
            for col in 0..width {
                rows[row * width + col] = values[col * input.size + row];
            }
        }
        let coefficients = self
            .dft
            .idft_algebra_batch(RowMajorMatrix::new(rows, width));
        if output.size < input.size
            && coefficients.values[output_len..]
                .iter()
                .any(|c| *c != E::ZERO)
        {
            return Err(Error::CoefficientCount);
        }
        let mut scaled = Vec::new();
        scaled
            .try_reserve_exact(output_len)
            .map_err(|_| Error::Allocation)?;
        scaled.resize(output_len, E::ZERO);
        let ratio = output.shift / input.shift;
        let mut power = E::ONE;
        for row in 0..input.size.min(output.size) {
            for col in 0..width {
                scaled[row * width + col] = coefficients.values[row * width + col] * power;
            }
            power *= ratio;
        }
        drop(coefficients);
        let evaluations = self
            .dft
            .dft_algebra_batch(RowMajorMatrix::new(scaled, width));
        for col in 0..width {
            for row in 0..output.size {
                destination[col * output.size + row] = evaluations.values[row * width + col];
            }
        }
        Ok(())
    }

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
    let inverse_two = KoalaBear::TWO.inverse();
    let mut inverse_twice_x = E::from(inverse_two) / domain.shift;
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
    fn base_action_matches_embedding<F: ExtensionField<KoalaBear>>() {
        for log_n in 1..=6 {
            let n = 1 << log_n;
            let sample =
                |i| F::from_basis_coefficients_fn(|j| KoalaBear::from_usize(3 * i + 7 * j + 1));
            let domain = Domain::new(n, sample(3), n).unwrap();
            let embedded = F::from(KoalaBear::two_adic_generator(log_n));
            let mut recurrence = domain.shift();
            for index in 0..n {
                let expected = domain.shift() * embedded.exp_u64(index as u64);
                assert_eq!(domain.point(index).unwrap(), expected);
                assert_eq!(recurrence, expected);
                recurrence *= domain.base_generator();
            }
            let values: Vec<_> = (0..n).map(sample).collect();
            let challenge = sample(11);
            let inverse_two = F::TWO.inverse();
            let mut inverse_twice_x = inverse_two / domain.shift();
            let inverse_generator = embedded.inverse();
            let expected: Vec<_> = (0..n / 2)
                .map(|i| {
                    let (a, b) = (values[i], values[i + n / 2]);
                    let result = (a + b) * inverse_two + challenge * (a - b) * inverse_twice_x;
                    inverse_twice_x *= inverse_generator;
                    result
                })
                .collect();
            assert_eq!(fold(&values, domain, challenge).unwrap(), expected);
            assert_eq!(domain.folded().unwrap().generator(), embedded.square());
        }
    }

    #[test]
    fn base_subgroup_action_preserves_non_base_cosets() {
        base_action_matches_embedding::<KoalaBear>();
        base_action_matches_embedding::<crate::KoalaBearExt4>();
        base_action_matches_embedding::<crate::KoalaBearExt8>();
    }

    fn batch_extension_matches_independent_columns<F: ExtensionField<KoalaBear>>() {
        let kernels = Kernels::default();
        let element =
            |i| F::from_basis_coefficients_fn(|j| KoalaBear::from_usize(11 * i + 7 * j + 1));
        for width in [1, 4, 16] {
            for (height, size) in [(1, 1), (1, 4), (4, 1), (4, 2), (4, 8), (8, 4), (8, 16)] {
                let input = Domain::new(height, element(3), 32).unwrap();
                let output = Domain::new(size, element(5), 32).unwrap();
                let mut values = Vec::new();
                let mut expected = Vec::new();
                for col in 0..width {
                    // Distinct columns include zero and constant polynomials.
                    let coefficients: Vec<_> = (0..(col % (height.min(size) + 1)))
                        .map(|i| element(13 * col + i))
                        .collect();
                    let column = kernels.evaluate(&coefficients, input).unwrap();
                    let recovered = kernels.interpolate(&column, input).unwrap();
                    let evaluated = kernels.evaluate(&recovered, output).unwrap();
                    for (row, value) in evaluated.iter().enumerate() {
                        assert_eq!(
                            *value,
                            evaluate_at(&coefficients, output.point(row).unwrap())
                        );
                    }
                    values.extend(column);
                    expected.extend(evaluated);
                }
                let original = values.clone();
                let mut result = vec![element(71); width * size];
                kernels
                    .coset_extend_into(&values, width, input, output, &mut result)
                    .unwrap();
                assert_eq!(result, expected, "{width} columns: {height} -> {size}");
                assert_eq!(values, original);
            }
            // Arbitrary full-height evaluations exercise nonzero high coefficients.
            let input = Domain::new(4, element(7), 32).unwrap();
            let output = Domain::new(16, element(9), 32).unwrap();
            let values: Vec<_> = (0..width * 4).map(element).collect();
            let expected: Vec<_> = values
                .as_chunks::<4>()
                .0
                .iter()
                .flat_map(|column| {
                    kernels
                        .evaluate(&kernels.interpolate(column, input).unwrap(), output)
                        .unwrap()
                })
                .collect();
            let mut result = vec![F::ZERO; width * 16];
            kernels
                .coset_extend_into(&values, width, input, output, &mut result)
                .unwrap();
            assert_eq!(result, expected);
        }
    }

    #[test]
    fn batch_extension_retains_every_extension_coordinate() {
        batch_extension_matches_independent_columns::<KoalaBear>();
        batch_extension_matches_independent_columns::<crate::KoalaBearExt4>();
        batch_extension_matches_independent_columns::<crate::KoalaBearExt8>();
    }

    #[test]
    fn batch_extension_refuses_actual_high_coefficients_and_bad_shapes() {
        let kernels = Kernels::default();
        let input = Domain::new(4, sample(3), 16).unwrap();
        let output = Domain::new(2, sample(5), 16).unwrap();
        let low = kernels.evaluate(&[sample(1), sample(2)], input).unwrap();
        for coefficient in [
            sample(8),
            E::from_basis_coefficients_fn(|j| {
                if j == 7 {
                    KoalaBear::ONE
                } else {
                    KoalaBear::ZERO
                }
            }),
        ] {
            let high = kernels
                .evaluate(&[E::ZERO, E::ZERO, coefficient], input)
                .unwrap();
            for values in [high.clone(), [low.clone(), high.clone()].concat()] {
                let mut destination = vec![E::ZERO; values.len() / 2];
                assert_eq!(
                    kernels.coset_extend_into(
                        &values,
                        values.len() / 4,
                        input,
                        output,
                        &mut destination,
                    ),
                    Err(Error::CoefficientCount)
                );
            }
        }
        let mut destination = [sample(11); 2];
        assert_eq!(
            kernels.coset_extend_into(&low[..3], 1, input, output, &mut destination,),
            Err(Error::BatchShape)
        );
        assert_eq!(destination, [sample(11); 2]);
        assert_eq!(
            kernels.coset_extend_into(&low, 1, input, output, &mut destination[..1],),
            Err(Error::BatchShape)
        );
        assert_eq!(destination, [sample(11); 2]);
        assert_eq!(
            kernels.coset_extend_into(&[], usize::MAX, input, output, &mut [],),
            Err(Error::SizeOverflow)
        );
        kernels
            .coset_extend_into(&[], 0, input, output, &mut [])
            .unwrap();
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
