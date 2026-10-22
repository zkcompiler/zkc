//! Kernel APIs are independently usable without native values or VM policy.
use zkc_kernels::{
    Binary64, Binary64Ext3, Bn254Scalar, KoalaBear, KoalaBearExt4, KoalaBearExt8, RistrettoScalar,
    Scalar,
    fields::{Coefficient, Error},
    matrix, vector,
};

fn arithmetic<S: Coefficient>(element: impl Fn(usize) -> S) {
    // Cover empty, packed blocks and suffixes without assuming a machine width.
    for n in 0..70 {
        let a: Vec<_> = (0..n).map(&element).collect();
        let b: Vec<_> = (n..2 * n).map(&element).collect();
        let mut out = vec![S::zero(); n];
        for (apply, expected) in [
            (
                vector::add::<S> as fn(&[S], &[S], &mut [S]) -> _,
                a.iter().zip(&b).map(|(a, b)| *a + *b).collect::<Vec<_>>(),
            ),
            (
                vector::sub::<S>,
                a.iter().zip(&b).map(|(a, b)| *a - *b).collect(),
            ),
            (
                vector::mul::<S>,
                a.iter().zip(&b).map(|(a, b)| *a * *b).collect(),
            ),
        ] {
            apply(&a, &b, &mut out).unwrap();
            assert!(out == expected);
        }
        vector::neg(&a, &mut out).unwrap();
        assert!(out.iter().zip(&a).all(|(x, a)| *x == -*a));
        vector::scale(&a, element(11), &mut out).unwrap();
        assert!(out.iter().zip(&a).all(|(x, a)| *x == *a * element(11)));
        let expected = a
            .iter()
            .zip(&b)
            .fold(S::zero(), |sum, (a, b)| sum + *a * *b);
        assert!(S::dot_product(&a, &b).unwrap() == expected);
        let before = out.clone();
        assert_eq!(
            vector::mul(&a, &vec![S::one(); n + 1], &mut out),
            Err(Error::LengthMismatch)
        );
        assert!(out == before);
    }
    let values = [S::one(), S::one() + S::one(), -S::one()];
    let nonzero: Vec<_> = values.into_iter().filter(|x| *x != S::zero()).collect();
    let mut inverse = vec![S::zero(); nonzero.len()];
    let plan = vector::Inversion::new(&nonzero).unwrap();
    assert_eq!(plan.write_into(&mut []), Err(Error::LengthMismatch));
    plan.write_into(&mut inverse).unwrap();
    assert!(
        nonzero
            .iter()
            .zip(&inverse)
            .all(|(x, y)| *x * *y == S::one())
    );
    assert!(matches!(
        vector::Inversion::new(&[S::zero()]),
        Err(Error::ZeroInverse)
    ));
}

#[test]
fn all_installed_families_support_checked_typed_arithmetic() {
    arithmetic::<Scalar>(|i| Scalar::from((i * 13 + 3) as u64));
    arithmetic::<Bn254Scalar>(|i| Bn254Scalar::from((i * 17 + 5) as u64));
    arithmetic::<RistrettoScalar>(|i| RistrettoScalar::from((i * 19 + 7) as u64));
    arithmetic::<KoalaBear>(|i| KoalaBear::new((i * 23 + 11) as u32));
    arithmetic::<KoalaBearExt4>(|i| {
        KoalaBearExt4::from(std::array::from_fn(|j| {
            KoalaBear::new((i * 29 + j * 7 + 13) as u32)
        }))
    });
    arithmetic::<KoalaBearExt8>(|i| {
        KoalaBearExt8::from(std::array::from_fn(|j| {
            KoalaBear::new((i * 31 + j * 11 + 17) as u32)
        }))
    });
    use zkc_kernels::plonky3::binary;
    arithmetic::<Binary64>(|i| binary::from_bits(0x89abcdef01234567u64.rotate_left(i as u32)));
    arithmetic::<Binary64Ext3>(|i| {
        binary::ext3_from_bits(std::array::from_fn(|j| {
            (0xdeadbeef12345678u64 + j as u64).rotate_left(i as u32)
        }))
    });
}

#[test]
fn sparse_contractions_share_canonical_storage_and_reject_shapes_before_writes() {
    let f = Scalar::from;
    let entries = [(0, 1, f(3u64)), (2, 0, f(5u64)), (2, 1, f(7u64))];
    let m = matrix::from_entries(3, 2, &entries).unwrap();
    let alias = m.clone();
    assert!(std::sync::Arc::ptr_eq(m.storage(), alias.storage()));
    let mut out = [f(99u64); 3];
    assert_eq!(
        matrix::mul_into(&m, &[f(2u64)], false, &mut out),
        Err(matrix::Error::Shape)
    );
    assert_eq!(out, [f(99u64); 3]);
    matrix::mul_into(&m, &[f(2u64), f(11u64)], false, &mut out).unwrap();
    assert_eq!(out, [f(33u64), f(0u64), f(87u64)]);
    let mut transpose = [f(0u64); 2];
    matrix::mul_into(&m, &[f(13u64), f(17u64), f(19u64)], true, &mut transpose).unwrap();
    assert_eq!(transpose, [f(95u64), f(172u64)]);
    assert_eq!(
        matrix::bilinear(&m, &[f(13u64), f(17u64), f(19u64)], &[f(2u64), f(11u64)]).unwrap(),
        f(2082u64)
    );
    for (entries, error) in [
        (vec![(3, 0, f(1u64))], matrix::Error::Index),
        (vec![(0, 1, f(1u64)), (0, 1, f(2u64))], matrix::Error::Order),
        (vec![(0, 1, f(0u64))], matrix::Error::Zero),
    ] {
        assert!(matches!(matrix::from_entries(3,2,&entries),Err(e) if e==error));
    }
    if usize::BITS > 32 {
        let large = matrix::from_entries((u32::MAX as usize) + 2, 1, &[(0, 0, f(9u64))]).unwrap();
        assert_eq!(
            matrix::get(&large, (u32::MAX as usize) + 1, 0).unwrap(),
            f(0u64)
        );
    }
}

#[test]
fn bit_reversal_refuses_invalid_domains() {
    use zkc_kernels::polynomial::reverse_bits;
    assert_eq!(
        (0..8)
            .map(|i| reverse_bits(i, 8).unwrap())
            .collect::<Vec<_>>(),
        [0, 4, 2, 6, 1, 5, 3, 7]
    );
    for (i, n) in [(0, 0), (0, 3), (8, 8)] {
        assert_eq!(reverse_bits(i, n), None);
    }
    assert_eq!(reverse_bits(0, 1), Some(0));
}
