//! The KoalaBear instantiation of the generic upstream sources and its
//! canonical encoding.
//!
//! OpenVM deploys BabyBear. Every upstream component this adapter runs is
//! generic over `PrimeField32` or `Field`; the native zkc evaluators install
//! KoalaBear, so the subsystem is instantiated at KoalaBear. Constants are
//! exported as canonical representatives (`as_canonical_u32`), never as the
//! library's internal Montgomery residues.

use crate::refusal::{Result, ensure, refuse};
use p3_field::{PrimeCharacteristicRing, PrimeField32};

pub type F = p3_koala_bear::KoalaBear;
pub const FIELD_IDENTITY: &str = "koala-bear";
pub const MODULUS: u32 = 2_130_706_433;

const _: () = assert!(MODULUS == p3_koala_bear::KoalaBear::ORDER_U32);

/// Canonical decimal representative.
pub fn decimal(x: F) -> String {
    x.as_canonical_u32().to_string()
}

/// Parse a canonical decimal representative strictly below the modulus.
pub fn parse_decimal(text: &str) -> Result<F> {
    ensure(
        !text.is_empty() && text.bytes().all(|b| b.is_ascii_digit()),
        "openvm-scalar",
        || format!("{text:?} is not a decimal natural"),
    )?;
    ensure(
        text == "0" || !text.starts_with('0'),
        "openvm-scalar",
        || format!("{text:?} has a leading zero"),
    )?;
    let Ok(value) = text.parse::<u64>() else {
        return refuse("openvm-scalar", format!("{text:?} is too large"));
    };
    ensure(value < MODULUS as u64, "openvm-scalar", || {
        format!("{text:?} is not below the modulus")
    })?;
    Ok(F::from_u32(value as u32))
}

/// Signed decimal of a small integer with the field's sign convention: values
/// above `(p-1)/2` are printed as negative numbers.
pub fn signed(x: F) -> i64 {
    let v = x.as_canonical_u32() as i64;
    if v > (MODULUS as i64 - 1) / 2 {
        v - MODULUS as i64
    } else {
        v
    }
}
