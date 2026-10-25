use super::*;
use crate::arkworks::bls12_381 as reference;
use ark_ff::{BigInteger, PrimeField};
use sha2::{Digest, Sha256};

fn scalars(n: usize) -> Vec<reference::Scalar> {
    (0..n)
        .map(|i| reference::Scalar::from_le_bytes_mod_order(&Sha256::digest(i.to_le_bytes())))
        .collect()
}

#[test]
fn scalar_conversion_is_exact_and_rejects_reduction_and_wrong_lengths() {
    for scalar in scalars(64)
        .into_iter()
        .chain([reference::Scalar::from(0), -reference::Scalar::from(1)])
    {
        assert_eq!(
            arkworks::import_scalar(scalar).unwrap().to_bytes_le(),
            reference::encode_scalar(&scalar).unwrap()
        );
    }
    for invalid in [
        vec![],
        vec![0; 31],
        vec![0; 33],
        vec![255; 32],
        reference::Scalar::MODULUS.to_bytes_le(),
    ] {
        assert_eq!(decode_scalar(&invalid), Err(Error::InvalidEncoding));
    }
}

macro_rules! differential {
    ($test:ident, $point:ident, $import:ident, $export:ident) => {
        #[test]
        fn $test() {
            let scalars = scalars(67);
            let native: Vec<_> = scalars
                .iter()
                .copied()
                .map(|s| arkworks::import_scalar(s).unwrap())
                .collect();
            let mut points: Vec<_> = scalars
                .iter()
                .map(|&s| reference::$point::generator().scale(s))
                .collect();
            points[2] = reference::$point::identity();
            let imported: Vec<_> = points
                .iter()
                .map(|&p| arkworks::$import(p).unwrap())
                .collect();
            assert_eq!(
                $point::generator().to_bytes(),
                reference::$point::generator().to_bytes().unwrap()
            );
            for (&p, &q) in points.iter().zip(&imported) {
                assert_eq!(arkworks::$export(q).unwrap(), p);
                assert_eq!($point::from_bytes(&q.to_bytes()).unwrap(), q);
                assert_eq!(
                    arkworks::$export(q.scale(native[3])).unwrap(),
                    p.scale(scalars[3])
                );
                assert_eq!(arkworks::$export(q.neg()).unwrap(), p.neg());
                assert_eq!(
                    arkworks::$export(q.add(&imported[1])).unwrap(),
                    p.add(&points[1])
                );
            }
            for n in [0, 1, 2, 3, 31, 32, 33, 67] {
                assert_eq!(
                    arkworks::$export($point::msm(&native[..n], &imported[..n]).unwrap()).unwrap(),
                    reference::$point::msm(&scalars[..n], &points[..n]).unwrap()
                );
            }
            let zero = Scalar::from(0);
            assert_eq!(
                $point::msm(&[zero; 3], &imported[..3]).unwrap(),
                $point::identity()
            );
            assert_eq!(
                $point::msm(&native[..2], &imported[..1]),
                Err(Error::LengthMismatch)
            );
            assert_eq!($point::msm(&[], &imported[..1]), Err(Error::LengthMismatch));
            assert_eq!(
                $point::msm(&native[..1], &imported[..2]),
                Err(Error::LengthMismatch)
            );
            for invalid in [vec![], vec![0; $point::BYTES], vec![255; $point::BYTES]] {
                assert_eq!($point::from_bytes(&invalid), Err(Error::InvalidEncoding));
            }
            let mut infinity = $point::identity().to_bytes();
            infinity[$point::BYTES - 1] = 1;
            assert_eq!($point::from_bytes(&infinity), Err(Error::InvalidEncoding));
            let mut infinity = $point::identity().to_bytes();
            infinity[0] |= 0x20;
            assert_eq!($point::from_bytes(&infinity), Err(Error::InvalidEncoding));
        }
    };
}
differential!(g1_agrees_with_arkworks, G1, import_g1, export_g1);
differential!(g2_agrees_with_arkworks, G2, import_g2, export_g2);

#[test]
fn on_curve_non_subgroup_point_is_rejected() {
    // (0, 2) lies on y^2=x^3+4 but has order three, not the prime order r.
    let mut bytes = [0; G1::BYTES];
    bytes[0] = 0x80;
    assert!(G1::from_bytes(&bytes).is_err());
    assert!(reference::G1::from_bytes(&bytes).is_err());
}

#[test]
fn pairing_product_preserves_false_empty_and_identity_cases() {
    let scalars = scalars(8);
    for i in 0..4 {
        let p = reference::G1::generator().scale(scalars[i]);
        let q = reference::G2::generator().scale(scalars[i + 4]);
        for (left, right) in [
            (vec![], vec![]),
            (vec![p], vec![q]),
            (vec![p, p.neg()], vec![q, q]),
            (vec![reference::G1::identity()], vec![q]),
            (vec![p], vec![reference::G2::identity()]),
        ] {
            let a: Vec<_> = left
                .iter()
                .map(|&p| arkworks::import_g1(p).unwrap())
                .collect();
            let b: Vec<_> = right
                .iter()
                .map(|&q| arkworks::import_g2(q).unwrap())
                .collect();
            assert_eq!(
                pairing_check(&a, &b).unwrap(),
                reference::pairing_check(&left, &right).unwrap()
            );
        }
    }
    assert_eq!(
        pairing_check(&[G1::generator()], &[]),
        Err(Error::LengthMismatch)
    );
}

#[test]
fn allocation_refusal_and_workspace_overflow_are_explicit() {
    let _failure = crate::allocation::failure::after(0);
    assert_eq!(
        G1::msm(&[Scalar::from(1)], &[G1::generator()]),
        Err(Error::Allocation)
    );
    assert_eq!(msm_workspace_bytes(0), Ok(0));
    assert_eq!(
        msm_workspace_bytes(usize::MAX),
        Err(Error::CapacityOverflow)
    );
}

#[test]
fn pairing_batches_remove_all_unit_factors_and_preserve_equations() {
    for n in [1, 7, 8, 9, 16, 17] {
        let p = G1::generator();
        let q = G2::generator();
        let mut left = vec![p; n * 2];
        let mut right = vec![q; n * 2];
        for point in left.iter_mut().skip(n) {
            *point = point.neg();
        }
        assert!(pairing_check(&left, &right).unwrap());
        left.push(G1::identity());
        right.push(q);
        left.push(p);
        right.push(G2::identity());
        assert!(pairing_check(&left, &right).unwrap());
        left.push(p);
        right.push(q);
        assert!(!pairing_check(&left, &right).unwrap());
        assert!(pairing_check(&vec![G1::identity(); n], &vec![q; n]).unwrap());
        assert!(pairing_check(&vec![p; n], &vec![G2::identity(); n]).unwrap());
        assert!(pairing_check(&vec![G1::identity(); n], &vec![G2::identity(); n]).unwrap());
    }
}

#[test]
fn resident_calls_do_not_rebuild_managed_input_vectors() {
    let scalars = ScalarVector::from_slice(&[Scalar::ONE, Scalar::from(2)]).unwrap();
    let g1 = G1Vector::filled(2, G1::generator()).unwrap();
    let g2 = G2Vector::filled(2, G2::generator()).unwrap();
    let mut scalar_output = ScalarVector::filled(2, Scalar::ZERO).unwrap();
    let mut g1_output = G1Vector::filled(2, G1::identity()).unwrap();
    let mut g2_output = G2Vector::filled(2, G2::identity()).unwrap();
    let _failure = crate::allocation::failure::after(0);
    // This detects any new adapter-owned reservation on a resident path. It
    // deliberately does not claim to intercept upstream hidden allocations.
    for _ in 0..2 {
        assert_eq!(
            g1.msm(&scalars).unwrap(),
            G1::generator().scale(Scalar::from(3))
        );
        assert_eq!(
            g2.msm(&scalars).unwrap(),
            G2::generator().scale(Scalar::from(3))
        );
        scalars.add_into(&scalars, &mut scalar_output).unwrap();
        scalars.inverse_into(&mut scalar_output).unwrap();
        g1.scale_each_into(&scalars, &mut g1_output).unwrap();
        g2.scale_into(Scalar::from(3), &mut g2_output).unwrap();
        assert!(!pairing_check_bulk(&g1, &g2).unwrap());
    }
    // The injection is still pending: none of those paths reserved a buffer.
    assert_eq!(ScalarVector::filled(1, Scalar::ONE), Err(Error::Allocation));
}

#[test]
fn resident_construction_failures_and_empty_cases_are_explicit() {
    for fail_after in [0, 1] {
        let _failure = crate::allocation::failure::after(fail_after);
        assert_eq!(
            G1::msm(&[Scalar::ONE], &[G1::generator()]),
            Err(Error::Allocation)
        );
    }
    macro_rules! refusal {
        ($bulk:ident, $element:expr) => {{
            let _failure = crate::allocation::failure::after(0);
            let empty = $bulk::filled(0, $element).unwrap();
            assert!(empty.is_empty());
            assert_eq!(empty.storage_bytes(), 0);
            assert_eq!($bulk::filled(1, $element), Err(Error::Allocation));
            assert_eq!(
                $bulk::filled(usize::MAX, $element),
                Err(Error::CapacityOverflow)
            );
            assert_eq!(
                $bulk::try_from_fn(2, |_| Err(Error::InvalidEncoding)),
                Err(Error::InvalidEncoding)
            );
        }};
    }
    refusal!(ScalarVector, Scalar::ZERO);
    refusal!(G1Vector, G1::identity());
    refusal!(G2Vector, G2::identity());
}

#[test]
fn failed_resident_freeze_releases_numerical_reservations() {
    let call = crate::numerical::Call::new(crate::numerical::Limits {
        work: 0,
        memory: 128,
        outputs: 64,
    });
    let output = call.output(2, Scalar::ZERO, 64).unwrap();
    let _failure = crate::allocation::failure::after(0);
    assert_eq!(
        output.finish(|values| ScalarVector::from_slice(&values)),
        Err(Error::Allocation)
    );
    assert_eq!(call.usage().memory, 0);
    assert_eq!(call.usage().outputs, 0);
}
