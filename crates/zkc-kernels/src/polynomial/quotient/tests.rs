use super::*;

fn operands<'a>(q: u64, a: &'a [u64], b: &'a [u64]) -> Operands<'a> {
    let ring = Ring::new(q, a.len()).unwrap();
    Operands::new(ring.polynomial(a).unwrap(), ring.polynomial(b).unwrap()).unwrap()
}

// Independent integer convolution followed by one quotient reduction. Keep test
// coefficients small enough that the complete signed sum fits in i128.
fn reference(a: &[u64], b: &[u64], q: u64) -> Vec<u64> {
    let n = a.len();
    let mut full = vec![0i128; 2 * n - 1];
    for (i, &x) in a.iter().enumerate() {
        for (j, &y) in b.iter().enumerate() {
            full[i + j] += i128::from(x) * i128::from(y);
        }
    }
    (0..n)
        .map(|i| {
            let value = full[i] - full.get(i + n).copied().unwrap_or(0);
            value.rem_euclid(i128::from(q)) as u64
        })
        .collect()
}

#[test]
fn exact_ring_and_canonical_representative_admission() {
    assert_eq!(Ring::new(0, 1), Err(Error::Modulus));
    assert_eq!(Ring::new(1, 1), Err(Error::Modulus));
    assert_eq!(Ring::new(17, 0), Err(Error::Degree));
    let ring = Ring::new(17, 3).unwrap();
    assert_eq!(ring.polynomial(&[0, 0]).unwrap_err(), Error::Shape);
    assert_eq!(ring.polynomial(&[0, 0, 17]).unwrap_err(), Error::Residue);
    assert_eq!(
        ring.polynomial(&[u64::MAX, 0, 0]).unwrap_err(),
        Error::Residue
    );
    let a = [1, 2, 3];
    let admitted = ring.polynomial(&a).unwrap();
    assert_eq!(admitted.coefficients().as_ptr(), a.as_ptr());
    assert_eq!(admitted.ring(), ring);
    for other in [Ring::new(19, 3).unwrap(), Ring::new(17, 2).unwrap()] {
        let b = vec![0; other.degree()];
        assert_eq!(
            Operands::new(admitted, other.polynomial(&b).unwrap()).unwrap_err(),
            Error::RingMismatch
        );
    }
    let pair = operands(17, &a, &a);
    for length in [0, 2, 4] {
        let mut output = vec![99; length];
        assert_eq!(pair.add_into(&mut output), Err(Error::Destination));
        assert_eq!(pair.subtract_into(&mut output), Err(Error::Destination));
        assert_eq!(pair.multiply_into(&mut output), Err(Error::Destination));
        assert_eq!(output, vec![99; length]);
    }
}

#[test]
fn exhaustive_small_rings_include_zero_divisors_and_nonprime_moduli() {
    for q in 2..=5 {
        for a0 in 0..q {
            for a1 in 0..q {
                for b0 in 0..q {
                    for b1 in 0..q {
                        let a = [a0, a1];
                        let b = [b0, b1];
                        let pair = operands(q, &a, &b);
                        let mut output = [0; 2];
                        pair.multiply_into(&mut output).unwrap();
                        assert_eq!(output.as_slice(), reference(&a, &b, q));
                        pair.add_into(&mut output).unwrap();
                        assert_eq!(output, [(a0 + b0) % q, (a1 + b1) % q]);
                        pair.subtract_into(&mut output).unwrap();
                        assert_eq!(output, [(q + a0 - b0) % q, (q + a1 - b1) % q]);
                    }
                }
            }
        }
    }
    // (X-4)(X+4) = X^2-16 = 0 in F17[X]/(X^2+1).
    let mut zero = [99; 2];
    operands(17, &[13, 1], &[4, 1])
        .multiply_into(&mut zero)
        .unwrap();
    assert_eq!(zero, [0, 0]);
}

#[test]
fn basis_wraps_with_a_minus_sign_at_every_position() {
    for n in 1..=12 {
        for i in 0..n {
            for j in 0..n {
                let mut a = vec![0; n];
                let mut b = vec![0; n];
                a[i] = 1;
                b[j] = 1;
                let mut output = vec![0; n];
                operands(17, &a, &b).multiply_into(&mut output).unwrap();
                let mut expected = vec![0; n];
                expected[(i + j) % n] = if i + j >= n { 16 } else { 1 };
                assert_eq!(output, expected);
            }
        }
    }
}

#[test]
fn lattice_dimensions_match_integer_convolution() {
    // Falcon, ML-DSA and ML-KEM coefficient rings share this meaning, despite
    // their different transform representations. Include a non-two-adic ring.
    for (q, n) in [
        (12289, 512),
        (12289, 1024),
        (8380417, 256),
        (3329, 256),
        (16, 15),
    ] {
        let a: Vec<_> = (0..n)
            .map(|i| (i as u64 * i as u64 + 3 * i as u64 + 1) % q)
            .collect();
        let b: Vec<_> = (0..n).map(|i| (5 * i as u64 + 7) % q).collect();
        let mut output = vec![0; n];
        operands(q, &a, &b).multiply_into(&mut output).unwrap();
        assert_eq!(output, reference(&a, &b, q));
    }
}

#[test]
fn full_word_moduli_never_use_wrapping_integer_arithmetic() {
    let q = u64::MAX;
    let a = [q - 1; 4];
    let pair = operands(q, &a, &a);
    let mut output = [0; 4];
    pair.multiply_into(&mut output).unwrap();
    assert_eq!(output, [q - 2, 0, 2, 4]);
    pair.add_into(&mut output).unwrap();
    assert_eq!(output, [q - 2; 4]);
    pair.subtract_into(&mut output).unwrap();
    assert_eq!(output, [0; 4]);
    let mut scalar = [0];
    operands(q, &[q - 1], &[q - 1])
        .multiply_into(&mut scalar)
        .unwrap();
    assert_eq!(scalar, [1]);
    operands(65537, &[65536], &[65536])
        .multiply_into(&mut scalar)
        .unwrap();
    assert_eq!(scalar, [1]);
}

#[test]
fn centered_norm_is_an_exact_integer_predicate() {
    for (q, coefficients, expected) in [
        (17, vec![0, 8, 9, 16], vec![0, 8, -8, -1]),
        (16, vec![0, 7, 8, 15], vec![0, 7, -8, -1]),
        (2, vec![0, 1], vec![0, -1]),
    ] {
        let p = Ring::new(q, coefficients.len())
            .unwrap()
            .polynomial(&coefficients)
            .unwrap();
        assert_eq!(p.centered().collect::<Vec<_>>(), expected);
        let exact = 2 * expected.iter().map(|x| (x * x) as u64).sum::<u64>();
        let pair = Operands::new(p, p).unwrap();
        assert!(pair.norm_within(exact));
        assert!(!pair.norm_within(exact - 1));
    }
    assert!(operands(17, &[0], &[0]).norm_within(0));
    assert!(operands(u64::MAX, &[u64::MAX - 1], &[1]).norm_within(2));
    let large = [u64::MAX / 2; 8];
    // Even the total norm can overflow u128; the comparison must still be false.
    assert!(!operands(u64::MAX, &large, &large).norm_within(u64::MAX));
}

#[test]
fn work_admission_uses_checked_shape_arithmetic() {
    assert_eq!(linear_work(2), Some(17));
    assert_eq!(product_work(2), Some(37));
    assert_eq!(product_work(512), Some(2_098_177));
    assert_eq!(product_work(usize::MAX), None);
}
