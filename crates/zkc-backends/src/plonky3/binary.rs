//! The installed binary fields: `gf2-64.pentanomial-4-3-1`, which is
//! `GF(2)[x]/(x^64 + x^4 + x^3 + x + 1)`, and its cubic extension
//! `gf2-64.pentanomial-4-3-1.ext3-trinomial1`, which is `K[y]/(y^3 + y + 1)`.
//! Arithmetic is pinned to Plonky3 0.8.0's `Poly64` and `Poly192`.
//!
//! An element's bit pattern lists its coordinates over GF(2): bit `i` of the
//! base field is the coefficient of `x^i`, and bit `64 j + i` of the extension
//! is the coefficient of `x^i y^j` (docs/spec/domains/values.md). Every bit
//! pattern of the right width is a distinct element, so decoding never
//! reduces. Plonky3's integer constructors such as `from_u64` cast through
//! GF(2) and keep only the parity; values here are built from bit patterns.
use crate::{Result, refused};
use p3_field::{BasedVectorSpace, PrimeCharacteristicRing};

/// `GF(2)[x]/(x^64 + x^4 + x^3 + x + 1)` in the polynomial basis.
pub type Binary64 = p3_binary_field::Poly64;
/// `Binary64[y]/(y^3 + y + 1)` in the basis `1, y, y^2`.
pub type Binary64Ext3 = p3_binary_field::Poly192;

/// Bytes of one base-field element: its 64-bit pattern, little-endian.
pub const WIDTH: usize = 8;
/// Bytes of one extension element: three base coordinates in basis order.
pub const EXT3_WIDTH: usize = 24;

pub fn from_bits(bits: u64) -> Binary64 {
    Binary64::new(bits)
}
pub fn bits(value: Binary64) -> u64 {
    value.to_bits()
}
pub fn ext3_from_bits(words: [u64; 3]) -> Binary64Ext3 {
    Binary64Ext3::new(words.map(Binary64::new))
}
pub fn ext3_bits(value: Binary64Ext3) -> [u64; 3] {
    value.coefficients().map(Binary64::to_bits)
}

pub fn encode(value: Binary64) -> [u8; WIDTH] {
    value.to_bits().to_le_bytes()
}
/// Exact width; every eight-byte string is an element.
pub fn decode(bytes: &[u8]) -> Result<Binary64> {
    let bytes: [u8; WIDTH] = bytes.try_into().map_err(|_| refused("wire-length"))?;
    Ok(Binary64::from_le_bytes(bytes))
}
pub fn encode_ext3(value: Binary64Ext3) -> [u8; EXT3_WIDTH] {
    let mut bytes = [0; EXT3_WIDTH];
    for (coordinate, out) in value
        .as_basis_coefficients_slice()
        .iter()
        .zip(bytes.as_chunks_mut::<WIDTH>().0)
    {
        *out = encode(*coordinate);
    }
    bytes
}
/// Exact width; every 24-byte string is an element.
pub fn decode_ext3(bytes: &[u8]) -> Result<Binary64Ext3> {
    let bytes: &[u8; EXT3_WIDTH] = bytes.try_into().map_err(|_| refused("wire-length"))?;
    let mut coordinates = [Binary64::ZERO; 3];
    for (coordinate, input) in coordinates.iter_mut().zip(bytes.as_chunks::<WIDTH>().0) {
        *coordinate = decode(input)?;
    }
    Ok(Binary64Ext3::new(coordinates))
}

/// A constant attribute: `0`, `1` or a canonical bit-pattern literal.
fn literal(s: &str, width: u32) -> Result<[u64; 3]> {
    match s {
        "0" => Ok([0; 3]),
        "1" => Ok([1, 0, 0]),
        _ => zkc_runtime::interactive::bit_pattern_literal(s, width)
            .ok_or_else(|| refused("noncanonical-scalar")),
    }
}
pub fn parse_literal(s: &str) -> Result<Binary64> {
    Ok(Binary64::new(literal(s, 64)?[0]))
}
pub fn parse_ext3_literal(s: &str) -> Result<Binary64Ext3> {
    Ok(ext3_from_bits(literal(s, 192)?))
}

/// The readable form of a base-field element: `0x` and its bit pattern in
/// lowercase hexadecimal without leading zeros. No element prints as a
/// decimal residue.
pub fn readable(value: Binary64) -> String {
    format!("{:#x}", value.to_bits())
}
/// Accepts exactly the strings `readable` produces.
pub fn parse_readable(s: &str) -> Option<Binary64> {
    let digits = s.strip_prefix("0x")?;
    if digits.is_empty()
        || digits.len() > 16
        || (digits.len() > 1 && digits.starts_with('0'))
        || !digits
            .bytes()
            .all(|b| matches!(b, b'0'..=b'9' | b'a'..=b'f'))
    {
        return None;
    }
    u64::from_str_radix(digits, 16).ok().map(Binary64::new)
}
