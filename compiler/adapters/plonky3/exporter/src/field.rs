//! KoalaBear values, canonical decimal spelling and the two-adic trace domain.

use crate::refusal::{Result, ensure, refuse};
use p3_field::{
    PrimeCharacteristicRing, PrimeField32, TwoAdicField, extension::BinomialExtensionField,
};

pub use p3_koala_bear::KoalaBear as F;

/// Ascending power basis of F_p[X]/(X^8 - 3), the native provider's Ext8.
pub type Ext8 = BinomialExtensionField<F, 8>;

/// The `zkc.ring/0` field identity of KoalaBear.
pub const FIELD_IDENTITY: &str = "koala-bear";
pub const MODULUS: u32 = 2_130_706_433;
/// Two-adicity of the KoalaBear multiplicative group.
pub const MAX_LOG_HEIGHT: usize = 24;

/// Canonical representative, never the internal Montgomery residue.
pub fn decimal(value: F) -> String {
    value.as_canonical_u32().to_string()
}

/// Exact canonical decimal below the modulus; host input is never reduced.
pub fn parse_decimal(text: &str) -> Result<F> {
    let canonical = !text.is_empty()
        && text.len() <= 10
        && text.bytes().all(|b| b.is_ascii_digit())
        && (text.len() == 1 || !text.starts_with('0'));
    ensure(canonical, "plonky3-noncanonical-scalar", || {
        format!("{text:?} is not a canonical decimal")
    })?;
    match text.parse::<u64>() {
        Ok(value) if value < MODULUS as u64 => Ok(F::from_u32(value as u32)),
        _ => refuse(
            "plonky3-noncanonical-scalar",
            format!("{text} is not below the KoalaBear modulus"),
        ),
    }
}

/// Base-two logarithm of an admitted trace height: a power of two from 1 to 2^24.
pub fn log_height(height: usize) -> Result<usize> {
    ensure(
        height.is_power_of_two() && height.trailing_zeros() as usize <= MAX_LOG_HEIGHT,
        "plonky3-height",
        || format!("height {height} is not a power of two from 1 to 2^{MAX_LOG_HEIGHT}"),
    )?;
    Ok(height.trailing_zeros() as usize)
}

/// Generator `g` of the order-`2^log` subgroup used by Plonky3's trace domain.
pub fn generator(log: usize) -> F {
    F::two_adic_generator(log)
}

/// `n` as a field element; `n < p` for every admitted height.
pub fn height_scalar(height: usize) -> F {
    F::from_u32(height as u32)
}

pub fn ext(value: F) -> Ext8 {
    Ext8::from(value)
}

/// Coordinates are ascending powers of the extension generator.
pub fn ext_from_coordinates(coordinates: [u32; 8]) -> Ext8 {
    Ext8::from(coordinates.map(F::from_u32))
}
