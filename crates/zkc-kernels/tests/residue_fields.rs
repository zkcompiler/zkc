use p3_field::{BasedVectorSpace, PrimeCharacteristicRing, PrimeField64, TwoAdicField};
use zkc_kernels::plonky3::{BabyBear, BabyBearExt4, Goldilocks, GoldilocksExt2, KoalaBearExt4};
use zkc_kernels::plonky3::{
    polynomial::{self, Domain, Error, Kernels},
    residue::{self, PrimeWord, Residue},
};

#[test]
fn goldilocks_words_and_natural_embedding_are_exact() {
    const P: u64 = 18_446_744_069_414_584_321;
    for n in [0, 1, 1 << 32, (1 << 53) + 1, 1 << 63, P - 1] {
        let value = residue::parse_decimal::<Goldilocks>(&n.to_string()).unwrap();
        assert_eq!(value.as_canonical_u64(), n);
        let mut bytes = Vec::new();
        residue::encode_into(&value, &mut bytes);
        assert_eq!(bytes, n.to_le_bytes());
        assert_eq!(residue::decode::<Goldilocks>(&bytes).unwrap(), value);
        let extension = residue::parse_decimal::<GoldilocksExt2>(&n.to_string()).unwrap();
        assert_eq!(
            <GoldilocksExt2 as BasedVectorSpace<Goldilocks>>::as_basis_coefficients_slice(
                &extension
            ),
            &[value, Goldilocks::ZERO]
        );
    }
    for n in [P, u64::MAX] {
        assert!(residue::decode::<Goldilocks>(&n.to_le_bytes()).is_err());
        assert!(residue::parse_decimal::<Goldilocks>(&n.to_string()).is_err());
    }
    for text in ["", "00", "+1", "-1", "1.0", " 1", "18446744073709551616"] {
        assert!(residue::parse_decimal::<Goldilocks>(text).is_err());
    }
    for length in [0, 4, 7, 9, 16] {
        assert!(residue::decode::<Goldilocks>(&vec![0; length]).is_err());
    }
}

fn independent_product<E: Residue>(nonresidue: u64) {
    let p = u128::from(E::Base::ORDER_U64);
    let mut seed = 1234567u64;
    for _ in 0..40 {
        let mut next = || {
            seed = seed
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            seed % E::Base::ORDER_U64
        };
        let a: Vec<u64> = (0..E::DIMENSION).map(|_| next()).collect();
        let b: Vec<u64> = (0..E::DIMENSION).map(|_| next()).collect();
        let x = E::from_basis_coefficients_fn(|i| E::Base::from_u64(a[i]));
        let y = E::from_basis_coefficients_fn(|i| E::Base::from_u64(b[i]));
        let mut expected = vec![0u128; E::DIMENSION];
        for (i, a) in a.iter().enumerate() {
            for (j, b) in b.iter().enumerate() {
                let k = (i + j) % E::DIMENSION;
                let term = (u128::from(*a) * u128::from(*b)) % p;
                expected[k] = (expected[k]
                    + term
                        * if i + j >= E::DIMENSION {
                            u128::from(nonresidue)
                        } else {
                            1
                        })
                    % p;
            }
        }
        let actual = x * y;
        assert_eq!(
            actual
                .as_basis_coefficients_slice()
                .iter()
                .map(|c| c.as_canonical_u64())
                .collect::<Vec<_>>(),
            expected.iter().map(|n| *n as u64).collect::<Vec<_>>()
        );
        assert_eq!(x * x.inverse(), E::ONE);
        let mut bytes = Vec::new();
        residue::encode_into(&actual, &mut bytes);
        assert_eq!(residue::decode::<E>(&bytes).unwrap(), actual);
        let last = bytes.len() - E::Base::WORD_BYTES;
        bytes[last..].copy_from_slice(&E::Base::ORDER_U64.to_le_bytes()[..E::Base::WORD_BYTES]);
        assert!(residue::decode::<E>(&bytes).is_err());
    }
}
#[test]
fn binomial_products_match_integer_convolution() {
    independent_product::<BabyBearExt4>(11);
    independent_product::<GoldilocksExt2>(7);
}

fn cosets<E: Residue>(base_log: usize) {
    let shift = E::from_basis_coefficients_fn(|i| E::Base::from_usize(i + 2));
    let max = 1usize << base_log;
    assert!(Domain::<E>::validate(max, shift, max).is_ok());
    assert_eq!(
        Domain::<E>::validate(max * 2, shift, max * 2),
        Err(Error::DomainSize)
    );
    assert_eq!(
        Domain::<E>::validate(max, shift, max - 1),
        Err(Error::ElementLimit)
    );
    assert_eq!(Domain::<E>::validate(3, shift, max), Err(Error::DomainSize));
    assert_eq!(
        Domain::<E>::validate(8, E::ZERO, max),
        Err(Error::ZeroShift)
    );
    let d = Domain::new(8, shift, 8).unwrap();
    assert_eq!(d.base_generator(), E::Base::two_adic_generator(3));
    let coefficients: Vec<_> = (0..6)
        .map(|i| E::from_basis_coefficients_fn(|j| E::Base::from_usize(i * 7 + j + 1)))
        .collect();
    let kernels = Kernels::default();
    let values = kernels.evaluate(&coefficients, d).unwrap();
    for (i, value) in values.iter().enumerate() {
        assert_eq!(
            *value,
            polynomial::evaluate_at(&coefficients, d.point(i).unwrap())
        );
    }
    assert_eq!(kernels.interpolate(&values, d).unwrap(), coefficients);
    let challenge = shift + E::ONE;
    let folded = polynomial::fold(&values, d, challenge).unwrap();
    let folded_coefficients: Vec<_> = coefficients
        .chunks(2)
        .map(|pair| pair[0] + challenge * pair[1])
        .collect();
    for (i, value) in folded.iter().enumerate() {
        assert_eq!(
            *value,
            polynomial::evaluate_at(&folded_coefficients, d.folded().unwrap().point(i).unwrap())
        );
    }
}
#[test]
fn structural_limits_and_nonbase_cosets_use_the_base_root() {
    cosets::<BabyBear>(27);
    cosets::<BabyBearExt4>(27);
    cosets::<Goldilocks>(32);
    cosets::<GoldilocksExt2>(32);
}
#[test]
fn equal_width_extensions_have_distinct_modulus_checks() {
    let mut bytes = vec![0; 16];
    bytes[..4].copy_from_slice(&2_050_000_000u32.to_le_bytes());
    assert!(residue::decode::<BabyBearExt4>(&bytes).is_err());
    assert!(residue::decode::<KoalaBearExt4>(&bytes).is_ok());
    assert!(residue::decode::<GoldilocksExt2>(&bytes).is_ok());
}

#[test]
fn baby_bear_montgomery_words_match_integer_representatives() {
    use zkc_kernels::plonky3::words::{self, Form};
    const P: u64 = 2_013_265_921;
    let values = [0, 1, 1 << 24, P - 1];
    let x = BabyBearExt4::from(values.map(BabyBear::from_u64));
    for form in [Form::Canonical, Form::Montgomery] {
        let mut bytes = Vec::new();
        words::encode_into(&x, form, &mut bytes);
        for (word, n) in bytes.as_chunks::<4>().0.iter().zip(values) {
            let expected = match form {
                Form::Canonical => n,
                Form::Montgomery => ((u128::from(n) << 32) % u128::from(P)) as u64,
            };
            assert_eq!(word, &(expected as u32).to_le_bytes());
        }
        assert_eq!(words::decode::<BabyBearExt4>(&bytes, form).unwrap(), x);
        bytes[4..8].copy_from_slice(&(P as u32).to_le_bytes());
        assert!(words::decode::<BabyBearExt4>(&bytes, form).is_none());
    }
    assert!(words::decode::<Goldilocks>(&[0; 8], Form::Montgomery).is_none());
}
