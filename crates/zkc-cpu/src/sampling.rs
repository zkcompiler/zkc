//! Exact coordinate samplers for explicitly installed residue-field suites. The bounded
//! rejection loop has an explicit exhaustion outcome; it never reduces a
//! rejected coordinate modulo the characteristic.
#[cfg(test)]
use crate::{KoalaBear, KoalaBearExt8};
use crate::{Result, exhausted, refused};
use p3_field::PrimeCharacteristicRing;

pub(crate) fn residue<E: zkc_kernels::plonky3::residue::Residue>(
    mut block: impl FnMut() -> [u8; 64],
) -> Result<E> {
    use p3_field::PrimeField64;
    use zkc_kernels::plonky3::residue::PrimeWord;
    let mut coordinates = [E::Base::ZERO; 8];
    let mut count = 0;
    for _ in 0..16 {
        let bytes = block();
        for word in bytes.chunks_exact(E::Base::WORD_BYTES) {
            let mut input = [0; 8];
            input[..word.len()].copy_from_slice(word);
            let candidate = u64::from_le_bytes(input) & E::Base::CANDIDATE_MASK;
            if candidate < E::Base::ORDER_U64 {
                coordinates[count] = E::Base::from_u64(candidate);
                count += 1;
                if count == E::DIMENSION {
                    return E::from_basis_coefficients_slice(&coordinates[..count])
                        .ok_or_else(|| refused("challenge-coordinates"));
                }
            }
        }
    }
    Err(exhausted("challenge-rejection-limit"))
}
pub(crate) fn installed(field: zkc_runtime::vm::Identity) -> bool {
    matches!(
        field,
        zkc_runtime::vm::Identity::KoalaBearExt8
            | zkc_runtime::vm::Identity::BabyBearExt4
            | zkc_runtime::vm::Identity::GoldilocksExt2
    )
}
pub(crate) fn value(
    field: zkc_runtime::vm::Identity,
    block: impl FnMut() -> [u8; 64],
) -> Result<crate::Value> {
    use crate::operations::field::Family;
    if !installed(field) {
        return Err(refused("challenge-field"));
    }
    crate::fields::with_residue!(field, |E| Ok(E::field_value(residue::<E>(block)?)))
}

pub(crate) fn index_bound(bound: u64) -> Result<()> {
    if !bound.is_power_of_two() {
        return Err(refused("query-bound"));
    }
    Ok(())
}

/// Power-of-two bounds make this an exact uniform map from uniform 64-bit words.
pub(crate) fn index(bytes: &[u8; 64], bound: u64) -> Result<u64> {
    index_bound(bound)?;
    Ok(u64::from_le_bytes(bytes[..8].try_into().expect("eight bytes")) & (bound - 1))
}

#[cfg(test)]
mod tests {
    use super::*;
    use p3_field::BasedVectorSpace;

    #[test]
    fn new_profiles_reject_exact_moduli_and_preserve_coordinate_order() {
        use crate::{BabyBear, BabyBearExt4, Goldilocks, GoldilocksExt2};
        let mut bytes = [255; 64];
        for (slot, n) in bytes.as_chunks_mut::<4>().0.iter_mut().zip([
            2_013_265_921u32,
            0x8000_0001,
            0x0403_0201,
            2_013_265_920,
            5,
        ]) {
            slot.copy_from_slice(&n.to_le_bytes());
        }
        let baby = residue::<BabyBearExt4>(|| bytes).unwrap();
        assert_eq!(
            <BabyBearExt4 as BasedVectorSpace<BabyBear>>::as_basis_coefficients_slice(&baby),
            &[1, 67_305_985, 2_013_265_920, 5].map(BabyBear::from_u32)
        );
        const P: u64 = 18_446_744_069_414_584_321;
        for (slot, n) in bytes.as_chunks_mut::<8>().0.iter_mut().zip([
            P,
            u64::MAX,
            9_007_199_254_740_993,
            P - 1,
            0,
            0,
            0,
            0,
        ]) {
            slot.copy_from_slice(&n.to_le_bytes());
        }
        let gold = residue::<GoldilocksExt2>(|| bytes).unwrap();
        assert_eq!(
            <GoldilocksExt2 as BasedVectorSpace<Goldilocks>>::as_basis_coefficients_slice(&gold),
            &[9_007_199_254_740_993, P - 1].map(Goldilocks::from_u64)
        );
        for field in [
            zkc_runtime::vm::Identity::BabyBearExt4,
            zkc_runtime::vm::Identity::GoldilocksExt2,
        ] {
            let mut calls = 0;
            let error = value(field, || {
                calls += 1;
                [255; 64]
            })
            .unwrap_err();
            assert_eq!(calls, 16);
            assert_eq!(error.code, "exhausted:challenge-rejection-limit");
        }
    }

    #[test]
    fn canonical_coordinates_rejection_and_exhaustion() {
        let mut calls = 0;
        let x = residue::<KoalaBearExt8>(|| {
            calls += 1;
            if calls == 1 { [255; 64] } else { [0; 64] }
        })
        .unwrap();
        assert_eq!(calls, 2);
        assert!(
            <KoalaBearExt8 as BasedVectorSpace<KoalaBear>>::as_basis_coefficients_slice(&x)
                .iter()
                .all(|x| *x == KoalaBear::ZERO)
        );
        let mut calls = 0;
        assert!(
            residue::<KoalaBearExt8>(|| {
                calls += 1;
                [255; 64]
            })
            .is_err()
        );
        assert_eq!(calls, 16);
    }

    #[test]
    fn extension_checks_word_order_mask_and_rejected_coordinates() {
        // The characteristic is rejected; the high bit is removed from the
        // next word. Distinct bytes distinguish little- from big-endian input.
        let words: [u32; 9] = [
            2_130_706_433,
            0x8000_0001,
            0x0403_0201,
            2_130_706_432,
            3,
            4,
            5,
            6,
            7,
        ];
        let mut bytes = [255; 64];
        for (slot, word) in bytes.as_chunks_mut::<4>().0.iter_mut().zip(words) {
            slot.copy_from_slice(&word.to_le_bytes());
        }
        let mut calls = 0;
        let value = residue::<KoalaBearExt8>(|| {
            calls += 1;
            bytes
        })
        .unwrap();
        let expected = [1, 67_305_985, 2_130_706_432, 3, 4, 5, 6, 7].map(KoalaBear::from_u32);
        assert_eq!(calls, 1);
        assert_eq!(
            <KoalaBearExt8 as BasedVectorSpace<KoalaBear>>::as_basis_coefficients_slice(&value),
            &expected,
        );
    }

    #[test]
    fn index_uses_the_first_little_endian_word() {
        let mut bytes = [255; 64];
        bytes[..8].copy_from_slice(&[1, 2, 3, 4, 5, 6, 7, 8]);
        assert_eq!(index(&bytes, 256).unwrap(), 1);
        assert_eq!(index(&bytes, 65_536).unwrap(), 513);
        assert_eq!(index(&bytes, 1u64 << 63).unwrap(), 0x0807_0605_0403_0201);
    }

    #[test]
    fn index_bounds_and_endpoints() {
        for power in 0..64 {
            let bound = 1u64 << power;
            assert_eq!(index(&[0; 64], bound).unwrap(), 0);
            assert_eq!(index(&[255; 64], bound).unwrap(), bound - 1);
        }
        for bound in [0, 3, 5, u64::MAX] {
            assert!(index(&[0; 64], bound).is_err());
        }
    }
}
