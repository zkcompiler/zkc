use crate::{Bounds, Error, Metadata, PROFILE, bounds::vector};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use sha2::{Digest, Sha256};

pub(crate) const HEADER: usize = 81;
pub(crate) const G1_BYTES: usize = 48;
pub(crate) const G2_BYTES: usize = 96;
const MAGIC: &[u8; 8] = b"ZKCAR006";

#[derive(Clone, Copy)]
pub(crate) enum Kind {
    Verifier = 1,
    Commitment = 2,
    Proof = 3,
    Prover = 4,
}

pub(crate) fn size(kind: Kind, n: usize) -> Result<usize, Error> {
    let payload = match kind {
        Kind::Verifier => n
            .checked_mul(G1_BYTES)
            .and_then(|v| v.checked_add(G1_BYTES + G2_BYTES)),
        Kind::Commitment => Some(G1_BYTES),
        Kind::Proof => n.checked_mul(G2_BYTES),
        Kind::Prover => prover_basis_count(n)?
            .checked_add(1)
            .and_then(|v| v.checked_mul(G1_BYTES + G2_BYTES)),
    }
    .ok_or(Error::CapacityOverflow)?;
    HEADER.checked_add(payload).ok_or(Error::CapacityOverflow)
}

/// Sum of the n basis row lengths 2^n, ..., 2, in each group.
pub(crate) fn prover_basis_count(n: usize) -> Result<usize, Error> {
    if n == 0 {
        return Err(Error::PositiveArityRequired);
    }
    let shift = u32::try_from(n).map_err(|_| Error::CapacityOverflow)?;
    1usize
        .checked_shl(shift)
        .and_then(|v| v.checked_sub(1))
        .and_then(|v| v.checked_mul(2))
        .ok_or(Error::CapacityOverflow)
}

pub(crate) fn header(bytes: &[u8], kind: Kind, bounds: &Bounds) -> Result<Metadata, Error> {
    bounds.bytes(bytes.len())?;
    if bytes.len() < HEADER {
        return Err(Error::InvalidEncoding);
    }
    if &bytes[..8] != MAGIC || bytes[8] != kind as u8 {
        return Err(Error::InvalidHeader);
    }
    let n = u64::from_le_bytes(
        bytes[9..17]
            .try_into()
            .map_err(|_| Error::InvalidEncoding)?,
    );
    let n = usize::try_from(n).map_err(|_| Error::CapacityOverflow)?;
    bounds.pcs_arity(n)?;
    if bytes.len() != size(kind, n)? {
        return Err(Error::InvalidEncoding);
    }
    Ok(Metadata {
        arity: n,
        setup_id: bytes[17..49]
            .try_into()
            .map_err(|_| Error::InvalidEncoding)?,
        key_id: bytes[49..81]
            .try_into()
            .map_err(|_| Error::InvalidEncoding)?,
    })
}

pub(crate) fn start(meta: Metadata, kind: Kind, bounds: &Bounds) -> Result<Vec<u8>, Error> {
    bounds.pcs_arity(meta.arity)?;
    let len = size(kind, meta.arity)?;
    bounds.bytes(len)?;
    let mut bytes = vector(len)?;
    bytes.extend_from_slice(MAGIC);
    bytes.push(kind as u8);
    let n = u64::try_from(meta.arity).map_err(|_| Error::CapacityOverflow)?;
    bytes.extend_from_slice(&n.to_le_bytes());
    bytes.extend_from_slice(&meta.setup_id);
    bytes.extend_from_slice(&meta.key_id);
    Ok(bytes)
}

pub(crate) fn write<T: CanonicalSerialize>(value: &T, bytes: &mut Vec<u8>) -> Result<(), Error> {
    value
        .serialize_compressed(bytes)
        .map_err(|_| Error::InvalidEncoding)
}

/// Only fixed-size field/group objects reach the upstream deserializer. No
/// attacker-controlled Vec length is ever handed to canonical deserialization.
pub(crate) fn read<T: CanonicalDeserialize + CanonicalSerialize>(
    input: &mut &[u8],
    width: usize,
) -> Result<T, Error> {
    if input.len() < width || width > G2_BYTES {
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
    let mut canonical = [0u8; G2_BYTES];
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

struct HashWriter(Sha256);
impl std::io::Write for HashWriter {
    fn write(&mut self, bytes: &[u8]) -> std::io::Result<usize> {
        self.0.update(bytes);
        Ok(bytes.len())
    }
    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}

/// Domain-separated standard SHA-256 over length-framed profile, context and
/// the upstream canonical compressed object. Stream large setup material.
pub(crate) fn fingerprint<T: CanonicalSerialize>(
    domain: &[u8],
    context: &[u8],
    value: &T,
) -> Result<[u8; 32], Error> {
    let mut writer = HashWriter(Sha256::new());
    for part in [domain, PROFILE.as_bytes(), context] {
        let len = u64::try_from(part.len()).map_err(|_| Error::CapacityOverflow)?;
        writer.0.update(len.to_le_bytes());
        writer.0.update(part);
    }
    value
        .serialize_compressed(&mut writer)
        .map_err(|_| Error::InvalidEncoding)?;
    Ok(writer.0.finalize().into())
}
