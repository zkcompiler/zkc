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
