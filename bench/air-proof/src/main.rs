//! Probe actual Plonky3 domain layout, extension-field LDE and fold equations.
//! This is a numerical contract experiment, not a compiled STARK or benchmark.

use p3_dft::{Radix2DitParallel, TwoAdicSubgroupDft};
use p3_field::extension::BinomialExtensionField;
use p3_field::{BasedVectorSpace, Field, PrimeCharacteristicRing, TwoAdicField};
use p3_koala_bear::KoalaBear;

type F = KoalaBear;
type E = BinomialExtensionField<F, 4>;

fn horner(coefficients: &[E], point: E) -> E {
    coefficients
        .iter()
        .rev()
        .fold(E::ZERO, |x, c| x * point + *c)
}

fn main() {
    let dft = Radix2DitParallel::<F>::default();
    let shift = F::from_u32(7);
    let beta =
        E::from_basis_coefficients_slice(&[F::from_u32(13), F::from_u32(2), F::ONE, F::ZERO])
            .unwrap();
    let mut comparisons = 0;
    let mut wrong_layout_detected = false;
    let mut wrong_shift_detected = false;
    let mut extension_loss_detected = false;
    for log_n in 1..=9 {
        let n = 1 << log_n;
        let coefficients: Vec<F> = (0..n)
            .map(|i| F::from_usize(3 * i * i + 5 * i + 1))
            .collect();
        let coefficients_e: Vec<E> = coefficients.iter().copied().map(E::from).collect();
        let trace = dft.dft(coefficients.clone());
        assert_eq!(dft.idft(trace.clone()), coefficients);
        let lde = dft.coset_lde(trace, 2, shift);
        let g = F::two_adic_generator(log_n + 2);
        let half = lde.len() / 2;
        let inv_two = E::TWO.inverse();
        let folded_coefficients: Vec<E> = coefficients_e
            .as_chunks::<2>()
            .0
            .iter()
            .map(|pair| pair[0] + beta * pair[1])
            .collect();
        for i in 0..half {
            let x = E::from(shift * g.exp_u64(i as u64));
            let left = E::from(lde[i]);
            let right = E::from(lde[i + half]);
            assert_eq!(left, horner(&coefficients_e, x));
            assert_eq!(right, horner(&coefficients_e, -x));
            let folded = (left + right) * inv_two + beta * (left - right) * inv_two / x;
            assert_eq!(folded, horner(&folded_coefficients, x.square()));
            comparisons += 3;
            let reversed = i.reverse_bits() >> (usize::BITS - (log_n + 2) as u32);
            wrong_layout_detected |=
                left != horner(&coefficients_e, E::from(shift * g.exp_u64(reversed as u64)));
            wrong_shift_detected |= left != horner(&coefficients_e, E::from(g.exp_u64(i as u64)));
            let coordinates: &[F] = folded.as_basis_coefficients_slice();
            extension_loss_detected |= folded != E::from(coordinates[0]);
        }
        // The batch implementation transforms each base coordinate, retaining all
        // extension coefficients; it need not run a separate extension FFT.
        let extension_coefficients: Vec<E> = coefficients
            .iter()
            .enumerate()
            .map(|(i, c)| {
                E::from_basis_coefficients_slice(&[*c, F::from_usize(i + 1), F::ONE, F::ZERO])
                    .unwrap()
            })
            .collect();
        let extension_trace = dft.dft_algebra(extension_coefficients.clone());
        let extension_lde = dft.coset_lde_algebra(extension_trace, 2, shift);
        for (i, value) in extension_lde.iter().enumerate() {
            assert_eq!(
                *value,
                horner(
                    &extension_coefficients,
                    E::from(shift * g.exp_u64(i as u64))
                )
            );
            comparisons += 1;
        }
    }
    assert!(wrong_layout_detected && wrong_shift_detected && extension_loss_detected);
    println!("Plonky3 0.5.1: {comparisons} exact field comparisons; 3 representation controls");
}
