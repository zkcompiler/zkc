//! Pinned Plonky3 numerical primitives used by the native execution adapter.
//! No RNG, transcript, group, table or PCS implementation is installed here.
//! Slice kernels expose the same arithmetic used by Runtime for matched benchmarks.
pub(crate) mod numerical;
pub mod oracle;
pub mod polynomial;

use crate::{Result, refused};
use p3_field::{Field, PackedValue, PrimeCharacteristicRing, PrimeField32};

use p3_field::BasedVectorSpace;
pub use p3_koala_bear::KoalaBear;

/// Ascending power basis of F_p[X]/(X^8 - 3), pinned by Plonky3 0.5.1.
pub type KoalaBearExt8 = p3_field::extension::BinomialExtensionField<KoalaBear, 8>;

/// Natural constants embed into the base coordinate, never encode eight coordinates.
pub fn parse_extension_decimal(s: &str) -> Result<KoalaBearExt8> {
    Ok(parse_decimal(s)?.into())
}

pub fn encode_extension(value: KoalaBearExt8) -> [u8; 32] {
    let mut bytes = [0; 32];
    for (coordinate, out) in value
        .as_basis_coefficients_slice()
        .iter()
        .zip(bytes.as_chunks_mut::<4>().0)
    {
        *out = encode_scalar(*coordinate);
    }
    bytes
}

pub fn decode_extension(bytes: &[u8]) -> Result<KoalaBearExt8> {
    let bytes: &[u8; 32] = bytes.try_into().map_err(|_| refused("wire-length"))?;
    let mut coordinates = [KoalaBear::ZERO; 8];
    for (coordinate, input) in coordinates.iter_mut().zip(bytes.as_chunks::<4>().0) {
        *coordinate = decode_scalar(input)?;
    }
    Ok(KoalaBearExt8::from(coordinates))
}
pub const MODULUS: u32 = 2_130_706_433;
pub const MODULUS_DECIMAL: &str = "2130706433";
type Packed = <KoalaBear as Field>::Packing;

/// Upstream compile-time packing width; portable builds may use width one.
pub const PACKING_WIDTH: usize = Packed::WIDTH;

/// Parse an exact canonical decimal representative; never reduce host input.
pub fn parse_decimal(s: &str) -> Result<KoalaBear> {
    if s.is_empty()
        || !s.bytes().all(|b| b.is_ascii_digit())
        || (s.len() > 1 && s.starts_with('0'))
        || s.len() > MODULUS_DECIMAL.len()
        || (s.len() == MODULUS_DECIMAL.len() && s >= MODULUS_DECIMAL)
    {
        return Err(refused("noncanonical-scalar"));
    }
    Ok(KoalaBear::new(
        s.parse().map_err(|_| refused("noncanonical-scalar"))?,
    ))
}

/// Canonical four-byte little-endian representative, independent of Montgomery storage.
pub fn encode_scalar(value: KoalaBear) -> [u8; 4] {
    value.as_canonical_u32().to_le_bytes()
}

pub fn decode_scalar(bytes: &[u8]) -> Result<KoalaBear> {
    let value = u32::from_le_bytes(bytes.try_into().map_err(|_| refused("wire-length"))?);
    if value >= MODULUS {
        return Err(refused("noncanonical-scalar"));
    }
    Ok(KoalaBear::new(value))
}

/// Equal-length dot product, including zero for empty inputs. No allocations.
pub fn dot(a: &[KoalaBear], b: &[KoalaBear]) -> Result<KoalaBear> {
    crate::kernels::arithmetic::equal_len(a.len(), b.len())?;
    let (a, a_tail) = Packed::pack_slice_with_suffix(a);
    let (b, b_tail) = Packed::pack_slice_with_suffix(b);
    let packed = a.iter().zip(b).fold(Packed::ZERO, |s, (a, b)| s + *a * *b);
    let sum = packed.as_slice().iter().copied().sum::<KoalaBear>();
    Ok(a_tail.iter().zip(b_tail).fold(sum, |s, (a, b)| s + *a * *b))
}

/// Equal-length component product into caller-owned storage. Validate every
/// shape before writing; handles the scalar suffix when length is not packed.
pub fn mul_into(a: &[KoalaBear], b: &[KoalaBear], out: &mut [KoalaBear]) -> Result<()> {
    crate::kernels::arithmetic::equal_len(a.len(), b.len())?;
    crate::kernels::arithmetic::equal_len(a.len(), out.len())?;
    let (a, a_tail) = Packed::pack_slice_with_suffix(a);
    let (b, b_tail) = Packed::pack_slice_with_suffix(b);
    let (out, out_tail) = Packed::pack_slice_with_suffix_mut(out);
    for ((a, b), out) in a.iter().zip(b).zip(out) {
        *out = *a * *b;
    }
    for ((a, b), out) in a_tail.iter().zip(b_tail).zip(out_tail) {
        *out = *a * *b;
    }
    Ok(())
}
