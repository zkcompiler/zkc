use crate::{Error, Scalar};
use ark_ff::{BigInt, PrimeField};
use ark_serialize::CanonicalSerialize;

/// Compressed canonical Fr encoding size (little-endian integer, below p).
pub const SCALAR_BYTES: usize = 32;

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
    crate::codec::read_field(bytes)
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
