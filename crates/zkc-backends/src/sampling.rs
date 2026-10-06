//! Exact samplers for the installed octic-field transcript suite. The bounded
//! rejection loop has an explicit exhaustion outcome; it never reduces a
//! rejected coordinate modulo the characteristic.
use crate::{KoalaBear, KoalaBearExt8, Result, exhausted, refused};
use p3_field::PrimeCharacteristicRing;

pub(crate) fn extension(mut block: impl FnMut() -> [u8; 64]) -> Result<KoalaBearExt8> {
    let mut coordinates = [KoalaBear::ZERO; 8];
    let mut count = 0;
    for _ in 0..16 {
        for word in block().as_chunks::<4>().0 {
            let candidate = u32::from_le_bytes(*word) & 0x7fff_ffff;
            if candidate < 2_130_706_433 {
                coordinates[count] = KoalaBear::from_u32(candidate);
                count += 1;
                if count == 8 {
                    return Ok(KoalaBearExt8::from(coordinates));
                }
            }
        }
    }
    Err(exhausted("challenge-rejection-limit"))
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
    fn canonical_coordinates_rejection_and_exhaustion() {
        let mut calls = 0;
        let x = extension(|| {
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
            extension(|| {
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
        let value = extension(|| {
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
