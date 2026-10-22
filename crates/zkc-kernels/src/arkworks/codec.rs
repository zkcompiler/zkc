use super::Error;
use ark_ff::{Fp, FpConfig, PrimeField};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};

pub(crate) fn write<T: CanonicalSerialize>(value: &T, bytes: &mut Vec<u8>) -> Result<(), Error> {
    value
        .serialize_compressed(bytes)
        .map_err(|_| Error::InvalidEncoding)
}

/// Arkworks Fp uses an unflagged little-endian integer strictly below the
/// modulus. Its checked decoder rejects noncanonical integers directly;
/// unlike group decoding, it cannot normalize an exceptional encoding.
pub(crate) fn read_field<P: FpConfig<N>, const N: usize>(bytes: &[u8]) -> Result<Fp<P, N>, Error> {
    if bytes.len() != Fp::<P, N>::MODULUS_BIT_SIZE.div_ceil(8) as usize {
        return Err(Error::InvalidEncoding);
    }
    let mut input = bytes;
    let value =
        Fp::<P, N>::deserialize_compressed(&mut input).map_err(|_| Error::InvalidEncoding)?;
    finish(input)?;
    Ok(value)
}

// Largest installed fixed object: the BLS12-381 pairing target (twelve Fq coefficients).
const MAX_FIXED_BYTES: usize = 576;
/// Group objects require checked decoding and byte-for-byte canonicality.
/// Only fixed-size objects reach either upstream decoder; no attacker-controlled
/// Vec length is ever handed to canonical deserialization.
pub(crate) fn read<T: CanonicalDeserialize + CanonicalSerialize>(
    input: &mut &[u8],
    width: usize,
) -> Result<T, Error> {
    if input.len() < width || width > MAX_FIXED_BYTES {
        return Err(Error::InvalidEncoding);
    }
    let (bytes, rest) = input.split_at(width);
    let mut exact = bytes;
    // Compressed deserialization uses Validate::Yes, including subgroup checks.
    let value = T::deserialize_compressed(&mut exact).map_err(|_| Error::InvalidEncoding)?;
    if !exact.is_empty() {
        return Err(Error::InvalidEncoding);
    }
    // Some upstream point decoders normalize exceptional encodings. Require
    // byte-for-byte canonicality too, including the representation of infinity.
    let mut canonical = [0u8; MAX_FIXED_BYTES];
    value
        .serialize_compressed(&mut canonical[..width])
        .map_err(|_| Error::InvalidEncoding)?;
    if &canonical[..width] != bytes {
        return Err(Error::NonCanonicalEncoding);
    }
    *input = rest;
    Ok(value)
}

pub(crate) fn finish(input: &[u8]) -> Result<(), Error> {
    if input.is_empty() {
        Ok(())
    } else {
        Err(Error::InvalidEncoding)
    }
}
