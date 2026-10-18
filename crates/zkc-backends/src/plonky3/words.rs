//! Four-byte little-endian words of KoalaBear coordinates.
//!
//! A word is either the canonical residue `x` or the Montgomery residue
//! `x * 2^32 mod p` that Plonky3's binary serializers write. Extension elements
//! are their ascending power-basis coordinates, one word each. Decoding accepts
//! only words below the modulus; it never reduces. See
//! docs/spec/domains/values.md for the exchanged encodings.
use super::{KoalaBear, MODULUS};
use p3_field::{BasedVectorSpace, PrimeField32};

/// The residue that a word carries.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Form {
    Canonical,
    Montgomery,
}

/// `2^32 mod p`: the Montgomery factor of a four-byte word.
pub const MONTGOMERY_FACTOR: KoalaBear = KoalaBear::new(33_554_430);
/// The inverse of [`MONTGOMERY_FACTOR`] modulo `p`.
pub const MONTGOMERY_INVERSE: KoalaBear = KoalaBear::new(1_057_030_144);

pub fn encode_word(value: KoalaBear, form: Form) -> [u8; 4] {
    match form {
        Form::Canonical => value,
        Form::Montgomery => value * MONTGOMERY_FACTOR,
    }
    .as_canonical_u32()
    .to_le_bytes()
}

/// `None` when the word is not below the modulus.
pub fn decode_word(bytes: [u8; 4], form: Form) -> Option<KoalaBear> {
    let word = u32::from_le_bytes(bytes);
    if word >= MODULUS {
        return None;
    }
    let value = KoalaBear::new(word);
    Some(match form {
        Form::Canonical => value,
        Form::Montgomery => value * MONTGOMERY_INVERSE,
    })
}

/// Bytes of one element: four per coordinate.
pub fn width<E: BasedVectorSpace<KoalaBear>>() -> usize {
    4 * E::DIMENSION
}

pub fn encode_into<E: BasedVectorSpace<KoalaBear>>(value: &E, form: Form, out: &mut Vec<u8>) {
    for coordinate in value.as_basis_coefficients_slice() {
        out.extend_from_slice(&encode_word(*coordinate, form));
    }
}

/// Decode exactly one element; `None` for any other width or a word at or
/// above the modulus.
pub fn decode<E: BasedVectorSpace<KoalaBear>>(bytes: &[u8], form: Form) -> Option<E> {
    if bytes.len() != width::<E>() {
        return None;
    }
    let (words, _) = bytes.as_chunks::<4>();
    let mut coordinates = [KoalaBear::new(0); 8];
    let coordinates = coordinates.get_mut(..E::DIMENSION)?;
    for (coordinate, word) in coordinates.iter_mut().zip(words) {
        *coordinate = decode_word(*word, form)?;
    }
    E::from_basis_coefficients_slice(coordinates)
}

/// Whether every word of a whole number of elements is below the modulus.
/// Validation precedes any allocation of decoded elements.
pub fn valid_elements<E: BasedVectorSpace<KoalaBear>>(bytes: &[u8]) -> bool {
    bytes.len().is_multiple_of(width::<E>())
        && bytes
            .as_chunks::<4>()
            .0
            .iter()
            .all(|word| u32::from_le_bytes(*word) < MODULUS)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::KoalaBearExt8;
    use p3_field::{Field, PrimeCharacteristicRing};

    #[test]
    fn montgomery_constants_match_the_upstream_representation() {
        // Upstream asserts MONTY_BITS == 32 in its constructor; its residue of
        // one is therefore 2^32 mod p.
        assert_eq!(MONTGOMERY_FACTOR, KoalaBear::from_u64(1 << 32));
        assert_eq!(MONTGOMERY_FACTOR * MONTGOMERY_INVERSE, KoalaBear::ONE);
        assert_eq!(MONTGOMERY_FACTOR.inverse(), MONTGOMERY_INVERSE);
        // Human-readable serde writes the stored Montgomery residue as a number;
        // binary serde writes the same residue as four little-endian bytes.
        for value in [0, 1, 2, 3, 1 << 24, MODULUS - 1, 123_456_789] {
            let x = KoalaBear::new(value);
            let upstream: u32 = serde_json::from_value(serde_json::to_value(x).unwrap()).unwrap();
            assert_eq!(encode_word(x, Form::Montgomery), upstream.to_le_bytes());
            let expected = (u64::from(value) << 32) % u64::from(MODULUS);
            assert_eq!(u64::from(upstream), expected);
            assert_eq!(encode_word(x, Form::Canonical), value.to_le_bytes());
            for form in [Form::Canonical, Form::Montgomery] {
                assert_eq!(decode_word(encode_word(x, form), form), Some(x));
            }
        }
    }

    #[test]
    fn decoding_rejects_words_at_or_above_the_modulus() {
        for word in [MODULUS, MODULUS + 1, u32::MAX] {
            for form in [Form::Canonical, Form::Montgomery] {
                assert_eq!(decode_word(word.to_le_bytes(), form), None);
            }
        }
        assert_eq!(
            decode_word((MODULUS - 1).to_le_bytes(), Form::Canonical),
            Some(-KoalaBear::ONE)
        );
    }

    #[test]
    fn extension_elements_are_coordinate_words_in_ascending_order() {
        let x = KoalaBearExt8::from_basis_coefficients_fn(|i| KoalaBear::new(10 + i as u32));
        // The derived serializer writes the coordinate array, then a unit
        // marker that binary formats encode as nothing.
        let upstream: Vec<u32> =
            serde_json::from_value(serde_json::to_value(x).unwrap()["value"].clone()).unwrap();
        let mut bytes = Vec::new();
        encode_into(&x, Form::Montgomery, &mut bytes);
        assert_eq!(bytes.len(), width::<KoalaBearExt8>());
        let words: Vec<u32> = bytes
            .as_chunks::<4>()
            .0
            .iter()
            .map(|w| u32::from_le_bytes(*w))
            .collect();
        assert_eq!(words, upstream);
        assert_eq!(decode::<KoalaBearExt8>(&bytes, Form::Montgomery), Some(x));
        assert_eq!(
            decode::<KoalaBearExt8>(&bytes[..28], Form::Montgomery),
            None
        );
        let mut high = bytes.clone();
        high[28..].copy_from_slice(&MODULUS.to_le_bytes());
        assert_eq!(decode::<KoalaBearExt8>(&high, Form::Montgomery), None);
        assert!(!valid_elements::<KoalaBearExt8>(&high));
        assert!(!valid_elements::<KoalaBearExt8>(&bytes[..4]));
        assert!(valid_elements::<KoalaBearExt8>(&bytes));
        assert!(valid_elements::<KoalaBear>(&[]));
    }
}
