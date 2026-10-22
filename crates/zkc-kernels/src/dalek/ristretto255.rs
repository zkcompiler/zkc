//! Ristretto255 scalar field and prime-order group.
pub use curve25519_dalek::{ristretto::RistrettoPoint as Point, scalar::Scalar};
/// Exact order of the scalar field.
pub const SCALAR_MODULUS_DECIMAL: &str =
    "7237005577332262213973186563042994240857116359379907606001950938285454250989";

use crate::field::{Error, Result};
pub fn parse_decimal(s: &str) -> Result<Scalar> {
    const MODULUS: &str = SCALAR_MODULUS_DECIMAL;
    if s.is_empty()
        || !s.bytes().all(|b| b.is_ascii_digit())
        || (s.len() > 1 && s.starts_with('0'))
        || s.len() > MODULUS.len()
        || (s.len() == MODULUS.len() && s >= MODULUS)
    {
        return Err(Error::NoncanonicalScalar);
    }
    Ok(s.bytes().fold(Scalar::ZERO, |a, b| {
        a * Scalar::from(10u64) + Scalar::from(u64::from(b - b'0'))
    }))
}
