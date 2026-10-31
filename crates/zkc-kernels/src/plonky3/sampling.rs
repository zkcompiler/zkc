//! Bounded rejection sampling of ascending residue coordinates.
//!
//! The caller supplies advancing random or transcript blocks. This function
//! owns neither entropy nor transcript authority, and never reduces a rejected
//! coordinate modulo the characteristic.
use super::residue::{PrimeWord, Residue};
use p3_field::{PrimeCharacteristicRing, PrimeField64};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    Coordinates,
    Exhausted,
}

/// Consume at most sixteen 64-byte blocks, stopping at the last accepted
/// coordinate of one element. Unused bytes in that block are discarded.
pub fn residue<E: Residue>(mut block: impl FnMut() -> [u8; 64]) -> Result<E, Error> {
    let mut coordinates = [E::Base::ZERO; 8];
    if E::DIMENSION == 0 || E::DIMENSION > coordinates.len() {
        return Err(Error::Coordinates);
    }
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
                        .ok_or(Error::Coordinates);
                }
            }
        }
    }
    Err(Error::Exhausted)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::plonky3::{KoalaBear, KoalaBearExt4, MODULUS, encode_quartic};

    #[test]
    fn quartic_rejects_modulus_masks_candidates_and_preserves_basis_order() {
        let mut block = [255; 64];
        for (slot, word) in block.as_chunks_mut::<4>().0.iter_mut().zip([
            MODULUS,
            0x8000_0001,
            0x0403_0201,
            MODULUS - 1,
            5,
        ]) {
            *slot = word.to_le_bytes();
        }
        let mut calls = 0;
        let sampled = residue::<KoalaBearExt4>(|| {
            calls += 1;
            block
        })
        .unwrap();
        assert_eq!(calls, 1);
        assert_eq!(
            sampled,
            KoalaBearExt4::from([1, 67_305_985, MODULUS - 1, 5].map(KoalaBear::new))
        );
        let expected: Vec<_> = [1u32, 67_305_985, MODULUS - 1, 5]
            .iter()
            .flat_map(|w| w.to_le_bytes())
            .collect();
        assert_eq!(encode_quartic(sampled).as_slice(), expected);
    }

    #[test]
    fn quartic_retains_partial_coordinates_across_blocks_and_bounds_rejection() {
        let mut calls = 0;
        let sampled = residue::<KoalaBearExt4>(|| {
            calls += 1;
            let mut block = [255; 64];
            block[..4].copy_from_slice(&(calls as u32).to_le_bytes());
            block
        })
        .unwrap();
        assert_eq!(calls, 4);
        assert_eq!(
            sampled,
            KoalaBearExt4::from([1, 2, 3, 4].map(KoalaBear::new))
        );
        let mut rejected = 0;
        assert_eq!(
            residue::<KoalaBearExt4>(|| {
                rejected += 1;
                [255; 64]
            }),
            Err(Error::Exhausted)
        );
        assert_eq!(rejected, 16);
    }
}
