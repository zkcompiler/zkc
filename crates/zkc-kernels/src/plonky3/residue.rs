//! Canonical residue coordinates and base-subgroup preparation.
//! APIs are pinned to p3-field/DFT 0.8.0; no VM identity enters this layer.
use super::{
    BabyBear, BabyBearExt4, Goldilocks, GoldilocksExt2, KoalaBear, KoalaBearExt4, KoalaBearExt8,
};
use crate::field::{Error, Result};
use p3_dft::{Radix2DFTSmallBatch, TwoAdicSubgroupDft};
use p3_field::{ExtensionField, PrimeField64, TwoAdicField};

/// Exact external coordinate words; Montgomery support is explicitly selected.
pub trait PrimeWord: PrimeField64 + TwoAdicField {
    const WORD_BYTES: usize;
    const CANDIDATE_MASK: u64;
    /// The inverse of `2^32` for supported Montgomery32 words; `None` otherwise.
    const MONTGOMERY_INVERSE: Option<Self>;
    type Dft: TwoAdicSubgroupDft<Self>;
    fn dft(kernels: &super::polynomial::Kernels) -> &Self::Dft;
}
macro_rules! base {
    ($base:ty, $bytes:expr, $mask:expr, $montgomery:expr, $cache:ident, $dft:ty) => {
        impl PrimeWord for $base {
            const WORD_BYTES: usize = $bytes;
            const CANDIDATE_MASK: u64 = $mask;
            const MONTGOMERY_INVERSE: Option<Self> = $montgomery;
            type Dft = $dft;
            fn dft(kernels: &super::polynomial::Kernels) -> &Self::Dft {
                &kernels.$cache
            }
        }
    };
}
base!(
    KoalaBear,
    4,
    0x7fff_ffff,
    Some(KoalaBear::new(1_057_030_144)),
    koala,
    super::dft::Monty31<Self>
);
base!(
    BabyBear,
    4,
    0x7fff_ffff,
    Some(BabyBear::new(943_718_400)),
    baby,
    super::dft::Monty31<Self>
);
base!(
    Goldilocks,
    8,
    u64::MAX,
    None,
    goldilocks,
    Radix2DFTSmallBatch<Self>
);

/// The installed prime base controls both encoding and subgroup convention.
pub trait Residue: ExtensionField<Self::Base> {
    type Base: PrimeWord;
}
macro_rules! residue {
    ($base:ty; $($field:ty),+ $(,)?) => { $(impl Residue for $field { type Base = $base; })+ };
}
residue!(KoalaBear; KoalaBear, KoalaBearExt4, KoalaBearExt8);
residue!(BabyBear; BabyBear, BabyBearExt4);
residue!(Goldilocks; Goldilocks, GoldilocksExt2);

// Canonical base words can also be used by an independently selected digest
// construction. This supplies serialization only, without selecting a hash,
// compression function, tree shape, or installed commitment profile.
macro_rules! digest_word {
    ($($base:ty),+ $(,)?) => { $(
        impl super::merkle::DigestWord for $base {
            const BYTES: usize = <Self as PrimeWord>::WORD_BYTES;
            fn write(self, out: &mut Vec<u8>) { encode_into(&self, out); }
            fn read(bytes: &[u8]) -> Option<Self> { decode_word(bytes).ok() }
        }
    )+ };
}
digest_word!(BabyBear, Goldilocks);

pub fn parse_base<B: PrimeWord>(text: &str) -> Result<B> {
    if text.is_empty()
        || !text.bytes().all(|b| b.is_ascii_digit())
        || (text.len() > 1 && text.starts_with('0'))
    {
        return Err(Error::NoncanonicalScalar);
    }
    let word: u64 = text.parse().map_err(|_| Error::NoncanonicalScalar)?;
    if word >= B::ORDER_U64 {
        return Err(Error::NoncanonicalScalar);
    }
    Ok(B::from_u64(word))
}
/// Naturals embed into the prime subfield, never an encoded extension integer.
pub fn parse_decimal<E: Residue>(text: &str) -> Result<E> {
    Ok(E::from(parse_base::<E::Base>(text)?))
}
pub fn width<E: Residue>() -> usize {
    E::DIMENSION * E::Base::WORD_BYTES
}
pub fn encode_into<E: Residue>(value: &E, out: &mut Vec<u8>) {
    for c in value.as_basis_coefficients_slice() {
        out.extend_from_slice(&c.as_canonical_u64().to_le_bytes()[..E::Base::WORD_BYTES]);
    }
}
pub fn valid_elements<E: Residue>(bytes: &[u8]) -> bool {
    bytes.len().is_multiple_of(width::<E>())
        && bytes
            .chunks_exact(E::Base::WORD_BYTES)
            .all(|word| decode_word::<E::Base>(word).is_ok())
}
pub fn decode_word<B: PrimeWord>(bytes: &[u8]) -> Result<B> {
    if bytes.len() != B::WORD_BYTES {
        return Err(Error::WireLength);
    }
    let mut word = [0; 8];
    word[..B::WORD_BYTES].copy_from_slice(bytes);
    let word = u64::from_le_bytes(word);
    if word >= B::ORDER_U64 {
        return Err(Error::NoncanonicalScalar);
    }
    Ok(B::from_u64(word))
}
pub fn decode<E: Residue>(bytes: &[u8]) -> Result<E> {
    if bytes.len() != width::<E>() {
        return Err(Error::WireLength);
    }
    // Validate completely before constructing any field element.
    if !valid_elements::<E>(bytes) {
        return Err(Error::NoncanonicalScalar);
    }
    Ok(E::from_basis_coefficients_fn(|i| {
        decode_word::<E::Base>(&bytes[i * E::Base::WORD_BYTES..(i + 1) * E::Base::WORD_BYTES])
            .expect("validated coordinate")
    }))
}
