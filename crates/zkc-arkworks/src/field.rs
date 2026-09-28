use crate::{Error, Scalar};
use ark_ff::{BigInt, PrimeField};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};

/// Compressed canonical Fr encoding size (little-endian integer, below p).
pub const SCALAR_BYTES: usize = 32;

/// An admitted nonzero Fr value. The private payload prevents unchecked
/// construction; conversion to an ordinary scalar is total and explicit.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct NonzeroScalar(Scalar);

impl NonzeroScalar {
    /// Check the nonzero predicate on an already admitted field value.
    pub fn new(value: Scalar) -> Option<Self> {
        (value != Scalar::from(0u64)).then_some(Self(value))
    }

    /// Forget the nonzero refinement without changing the field value.
    pub fn scalar(self) -> Scalar {
        self.0
    }

    /// The payload has the ordinary canonical Fr encoding.
    pub fn to_bytes(self) -> Result<[u8; SCALAR_BYTES], Error> {
        encode_scalar(&self.0)
    }

    /// Admit exactly one canonical, nonzero scalar. Zero is a wire refusal.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, Error> {
        Self::new(decode_scalar(bytes)?).ok_or(Error::InvalidEncoding)
    }
}

/// Encode one Fr scalar using the upstream canonical codec.
pub fn encode_scalar(value: &Scalar) -> Result<[u8; SCALAR_BYTES], Error> {
    let mut bytes = [0; SCALAR_BYTES];
    value
        .serialize_compressed(&mut bytes[..])
        .map_err(|_| Error::InvalidEncoding)?;
    Ok(bytes)
}

/// Decode exactly one canonical scalar. No reduction of noncanonical integers.
pub fn decode_scalar(bytes: &[u8]) -> Result<Scalar, Error> {
    if bytes.len() != SCALAR_BYTES {
        return Err(Error::InvalidEncoding);
    }
    let mut input = bytes;
    let value = Scalar::deserialize_compressed(&mut input).map_err(|_| Error::InvalidEncoding)?;
    if !input.is_empty() {
        return Err(Error::InvalidEncoding);
    }
    if encode_scalar(&value)?.as_slice() != bytes {
        return Err(Error::NonCanonicalEncoding);
    }
    Ok(value)
}

/// Parse a canonical unsigned base-ten integer in `[0, p)` without reduction.
/// Reject signs, whitespace and leading zeros (except `"0"`). The maximum
/// digit count follows the field modulus, not an application arity policy.
pub fn parse_decimal(text: &str) -> Result<Scalar, Error> {
    let digits = text.as_bytes();
    if digits.is_empty()
        || digits.len() > 77
        || (digits.len() > 1 && digits[0] == b'0')
        || !digits.iter().all(u8::is_ascii_digit)
    {
        return Err(Error::InvalidEncoding);
    }
    // Upstream big-integer parsing is exact; Fr::from_str would reduce modulo p.
    let integer: BigInt<4> = text.parse().map_err(|_| Error::InvalidEncoding)?;
    Scalar::from_bigint(integer).ok_or(Error::InvalidEncoding)
}

#[cfg(test)]
mod nonzero_tests {
    use super::*;

    #[test]
    fn nonzero_codec_and_inclusion_agree() {
        for value in [1u64, 2, 17, u64::MAX] {
            let field = Scalar::from(value);
            let refined = NonzeroScalar::new(field).unwrap();
            let bytes = refined.to_bytes().unwrap();
            assert_eq!(bytes, encode_scalar(&field).unwrap());
            assert_eq!(NonzeroScalar::from_bytes(&bytes).unwrap().scalar(), field);
        }
    }

    #[test]
    fn zero_and_noncanonical_replies_are_refused() {
        assert!(NonzeroScalar::new(Scalar::from(0u64)).is_none());
        for bytes in [
            &[0u8; SCALAR_BYTES][..],
            &[255u8; SCALAR_BYTES][..],
            &[1u8; 31][..],
        ] {
            assert_eq!(
                NonzeroScalar::from_bytes(bytes),
                Err(Error::InvalidEncoding)
            );
        }
        let mut trailing = encode_scalar(&Scalar::from(1u64)).unwrap().to_vec();
        trailing.push(0);
        assert_eq!(
            NonzeroScalar::from_bytes(&trailing),
            Err(Error::InvalidEncoding)
        );
    }
}
