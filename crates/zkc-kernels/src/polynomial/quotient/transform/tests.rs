use super::*;
use crate::polynomial::quotient::Operands;

// Direct evaluation at the n odd powers, independent of butterfly scheduling.
fn evaluate(input: &[u64], q: u64, root: u64) -> Vec<u64> {
    (0..input.len())
        .map(|k| {
            let mut point = 1u128;
            for _ in 0..2 * k + 1 {
                point = point * u128::from(root) % u128::from(q);
            }
            let mut accumulator = 0;
            for &coefficient in input.iter().rev() {
                accumulator = (accumulator * point + u128::from(coefficient)) % u128::from(q);
            }
            accumulator as u64
        })
        .collect()
}

#[test]
fn every_basis_coordinate_matches_direct_evaluation_and_inversion() {
    for (n, root) in [(2, 4), (4, 2), (8, 3)] {
        let ring = Ring::new(17, n).unwrap();
        let forward = Transform::new(ring, root).unwrap();
        let inverse_root = (1..17).find(|r| r * root % 17 == 1).unwrap();
        let inverse = Transform::new(ring, inverse_root).unwrap();
        for position in 0..n {
            for coefficient in 0..17 {
                let mut input = vec![0; n];
                input[position] = coefficient;
                let mut transformed = vec![0; n];
                forward
                    .forward_into(ring.polynomial(&input).unwrap(), &mut transformed)
                    .unwrap();
                assert_eq!(transformed, evaluate(&input, 17, root));
                let mut restored = vec![0; n];
                inverse
                    .inverse_into(ring.polynomial(&transformed).unwrap(), &mut restored)
                    .unwrap();
                assert_eq!(restored, input);
            }
        }
    }
}

#[test]
fn lattice_sized_transform_products_match_integer_convolution() {
    for (q, n) in [(12289, 512), (12289, 1024), (8380417, 256), (2013265921, 8)] {
        let ring = Ring::new(q, n).unwrap();
        let root = (2..q)
            .map(|g| power(g, (q - 1) / (2 * n as u64), q))
            .find(|r| power(*r, n as u64, q) == q - 1)
            .unwrap();
        let forward = Transform::new(ring, root).unwrap();
        let inverse = Transform::new(ring, power(root, q - 2, q)).unwrap();
        for pattern in 0..2 {
            let a: Vec<_> = (0..n)
                .map(|i| {
                    if pattern == 0 {
                        q - 1
                    } else {
                        (i * i + 3 * i + 1) as u64 % q
                    }
                })
                .collect();
            let b: Vec<_> = (0..n)
                .map(|i| {
                    if pattern == 0 {
                        q - 1
                    } else {
                        (5 * i + 7) as u64 % q
                    }
                })
                .collect();
            let mut expected = vec![0; n];
            Operands::new(ring.polynomial(&a).unwrap(), ring.polynomial(&b).unwrap())
                .unwrap()
                .multiply_into(&mut expected)
                .unwrap();
            let mut fa = vec![0; n];
            let mut fb = vec![0; n];
            forward
                .forward_into(ring.polynomial(&a).unwrap(), &mut fa)
                .unwrap();
            forward
                .forward_into(ring.polynomial(&b).unwrap(), &mut fb)
                .unwrap();
            let mut product = vec![0; n];
            Operands::new(ring.polynomial(&fa).unwrap(), ring.polynomial(&fb).unwrap())
                .unwrap()
                .pointwise_into(&mut product)
                .unwrap();
            let mut actual = vec![0; n];
            inverse
                .inverse_into(ring.polynomial(&product).unwrap(), &mut actual)
                .unwrap();
            assert_eq!(actual, expected);
        }
    }
}

#[test]
fn maximum_degree_and_large_modulus_preserve_natural_coordinates() {
    let q = 2013265921;
    let n = 65536;
    let ring = Ring::new(q, n).unwrap();
    let root = power(31, (q - 1) / (2 * n as u64), q);
    let forward = Transform::new(ring, root).unwrap();
    let inverse = Transform::new(ring, power(root, q - 2, q)).unwrap();
    let mut input = vec![0; n];
    input[0] = q - 1;
    input[1] = q - 1;
    let mut evaluations = vec![0; n];
    forward
        .forward_into(ring.polynomial(&input).unwrap(), &mut evaluations)
        .unwrap();
    for (k, &actual) in evaluations.iter().enumerate() {
        let point = u128::from(power(root, (2 * k + 1) as u64, q));
        assert_eq!(
            actual,
            ((u128::from(q - 1) * (point + 1)) % u128::from(q)) as u64
        );
    }
    let mut restored = vec![0; n];
    inverse
        .inverse_into(ring.polynomial(&evaluations).unwrap(), &mut restored)
        .unwrap();
    assert_eq!(restored, input);
}

#[test]
fn profiles_roots_and_destinations_refuse_without_mutation() {
    for (q, n) in [
        (65, 4),
        (3329, 256),
        (17, 1),
        (17, 3),
        (2147483647, 4),
        (2, 2),
        (17, 131072),
    ] {
        assert_eq!(
            Transform::new(Ring::new(q, n).unwrap(), 2).unwrap_err(),
            Error::TransformProfile
        );
    }
    let ring = Ring::new(17, 4).unwrap();
    for root in [0, 1, 4, 17, u64::MAX] {
        assert_eq!(
            Transform::new(ring, root).unwrap_err(),
            Error::TransformRoot
        );
    }
    let plan = Transform::new(ring, 2).unwrap();
    let mut short = [99; 3];
    assert_eq!(
        plan.forward_into(ring.polynomial(&[1, 2, 3, 4]).unwrap(), &mut short),
        Err(Error::Destination)
    );
    assert_eq!(short, [99; 3]);
    let other = Ring::new(19, 4).unwrap();
    let mut output = [99; 4];
    assert_eq!(
        plan.inverse_into(other.polynomial(&[1, 2, 3, 4]).unwrap(), &mut output),
        Err(Error::RingMismatch)
    );
    assert_eq!(output, [99; 4]);
    assert!(work(0).is_none());
    assert!(work(3).is_none());
    assert!(work(usize::MAX).is_none());
}

#[test]
fn projection_reduces_residues_and_all_negacyclic_blocks() {
    for q in [2, 16, 17, u64::MAX] {
        for n in [1, 3, 4] {
            let ring = Ring::new(q, n).unwrap();
            for input in [vec![], vec![u64::MAX; 4 * n + 1], vec![0, 1, 2, 3, 4, 5, 6]] {
                let mut result = vec![77; n];
                ring.project_into(&input, &mut result).unwrap();
                let mut exact = vec![0i128; n];
                for (i, &value) in input.iter().enumerate() {
                    exact[i % n] += if (i / n) % 2 == 0 {
                        i128::from(value)
                    } else {
                        -i128::from(value)
                    };
                }
                assert_eq!(
                    result,
                    exact
                        .iter()
                        .map(|x| x.rem_euclid(i128::from(q)) as u64)
                        .collect::<Vec<_>>()
                );
            }
            let mut short = vec![77; n - 1];
            assert_eq!(ring.project_into(&[1], &mut short), Err(Error::Destination));
            assert_eq!(short, vec![77; n - 1]);
        }
    }
}
