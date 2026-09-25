use crate::{Bounds, Error, RandomSource, Scalar, Table};
use crate::{
    bounds::vector,
    codec::{self, G1_BYTES, G2_BYTES, HEADER, Kind},
    error::same_arity,
};
use ark_bls12_381::Bls12_381;
use ark_ec::AffineRepr;
use ark_poly_commit::multilinear_pc::{MultilinearPC, data_structures as upstream};
use ark_std::rand::{CryptoRng, RngCore};
use std::{fmt, sync::Arc};

type Pcs = MultilinearPC<Bls12_381>;

mod key_codec;

/// Public arity and fingerprints for the selected profile. These identify
/// material; they are not authority tokens, signatures, or ceremony receipts.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Metadata {
    pub(crate) arity: usize,
    pub(crate) setup_id: [u8; 32],
    pub(crate) key_id: [u8; 32],
}

impl Metadata {
    /// Exact key/commitment/proof arity.
    pub const fn arity(self) -> usize {
        self.arity
    }
    /// SHA-256 fingerprint of all canonical compressed universal parameters,
    /// including generators, every G1/G2 basis table, masks, arity and profile.
    pub const fn setup_id(self) -> [u8; 32] {
        self.setup_id
    }
    /// SHA-256 fingerprint of the profile, setup ID and complete canonical
    /// verifier key. Authenticate this pin separately before verifier import.
    pub const fn key_id(self) -> [u8; 32] {
        self.key_id
    }

    fn matches(self, other: Self) -> Result<(), Error> {
        same_arity(self.arity, other.arity)?;
        if self.setup_id != other.setup_id || self.key_id != other.key_id {
            return Err(Error::KeyMismatch);
        }
        Ok(())
    }
}

/// Shareable keys for exactly one positive arity. Setup is paid once; cloning
/// the bundle or either key shares immutable allocations through Arc.
#[derive(Clone, Debug)]
pub struct Keys {
    prover: ProverKey,
    verifier: VerifierKey,
}

impl Keys {
    /// Locally generate structured setup using OS-seeded randomness.
    /// This is test/development setup, not an audited ceremony. The generation
    /// process sees trapdoor randomness; upstream does not guarantee erasure.
    pub fn setup_for_development(n: usize, bounds: &Bounds) -> Result<Self, Error> {
        bounds.setup(n)?;
        bounds.bytes(codec::size(Kind::Verifier, n)?)?;
        let mut source = RandomSource::from_os()?;
        Self::setup_with_rng(n, &mut source.rng, bounds)
    }

    /// Generate local setup with an explicitly supplied cryptographic RNG.
    /// A seeded RNG is suitable for reproducible tests only. The trait bound
    /// does not establish unpredictable seeding or honest setup generation.
    /// No fresh setup occurs in commit/open/check.
    pub fn setup_with_rng<R: RngCore + CryptoRng>(
        n: usize,
        rng: &mut R,
        bounds: &Bounds,
    ) -> Result<Self, Error> {
        bounds.setup(n)?;
        // Reject an inadmissible public transport before the expensive setup.
        bounds.bytes(codec::size(Kind::Verifier, n)?)?;
        let params = Pcs::setup(n, rng);
        let setup_id = codec::fingerprint(b"zkc-arkworks/setup/v1", &[], &params)?;
        // Move the exactly-sized setup arrays. trim(n) would clone every basis
        // table, temporarily retaining an unnecessary second full setup.
        let vk = upstream::VerifierKey {
            nv: n,
            g: params.g,
            h: params.h,
            g_mask_random: params.g_mask,
        };
        validate_verifier(&vk)?;
        let ck = upstream::CommitterKey {
            nv: n,
            g: params.g,
            h: params.h,
            powers_of_g: params.powers_of_g,
            powers_of_h: params.powers_of_h,
        };
        validate_prover(&ck)?;
        let key_id = key_fingerprint(setup_id, &vk)?;
        let metadata = Metadata {
            arity: n,
            setup_id,
            key_id,
        };
        let material_fingerprint = key_codec::material_fingerprint(metadata, &ck)?;
        Ok(Self {
            prover: ProverKey {
                inner: Arc::new(ProverMaterial {
                    key: ck,
                    metadata,
                    material_fingerprint,
                }),
            },
            verifier: VerifierKey {
                inner: Arc::new(VerifierMaterial { key: vk, metadata }),
            },
        })
    }

    /// Borrow the immutable prover key; cloning it is inexpensive.
    pub fn prover_key(&self) -> &ProverKey {
        &self.prover
    }
    /// Borrow the public verifier key, transportable without private tables.
    pub fn verifier_key(&self) -> &VerifierKey {
        &self.verifier
    }
}

struct ProverMaterial {
    key: upstream::CommitterKey<Bls12_381>,
    metadata: Metadata,
    material_fingerprint: [u8; 32],
}
struct VerifierMaterial {
    key: upstream::VerifierKey<Bls12_381>,
    metadata: Metadata,
}

/// Immutable, shared public proving/SRS material, distinct from private tables
/// and opening state. Import requires an independent full-material pin and an
/// admitted verifier key; no arbitrary raw key constructor is exposed.
#[derive(Clone)]
pub struct ProverKey {
    inner: Arc<ProverMaterial>,
}

impl fmt::Debug for ProverKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ProverKey")
            .field("metadata", &self.metadata())
            .finish_non_exhaustive()
    }
}

impl ProverKey {
    /// Public setup/key identity and exact arity.
    pub fn metadata(&self) -> Metadata {
        self.inner.metadata
    }

    /// Commit through upstream and retain the exact original plus key.
    /// The returned opening state shares the table's immutable allocation.
    pub fn commit(&self, table: &Table) -> Result<CommittedTable, Error> {
        same_arity(self.metadata().arity, table.arity())?;
        let raw = Pcs::commit(&self.inner.key, table.polynomial.as_ref());
        same_arity(self.metadata().arity, raw.nv)?;
        let commitment = Commitment {
            raw,
            metadata: self.metadata(),
        };
        Ok(CommittedTable {
            key: self.clone(),
            original: table.clone(),
            commitment,
        })
    }
}

/// A commitment's immutable original and key custody. Clones share both.
/// Opening takes no replacement table, commitment or key argument, so scratch
/// cannot redirect a delayed opening. Repeated opens are immutable borrows.
#[derive(Clone, Debug)]
pub struct CommittedTable {
    key: ProverKey,
    original: Table,
    commitment: Commitment,
}

impl CommittedTable {
    /// Public commitment; cloning it does not retain the private table.
    pub fn commitment(&self) -> &Commitment {
        &self.commitment
    }
    /// Immutable original for local kernel work. Restriction makes scratch.
    pub fn original(&self) -> &Table {
        &self.original
    }
    /// Open this original at the unchanged logical point. Return the actual
    /// MLE value and upstream proof, with no protocol or transcript callback.
    pub fn open(&self, point: &[Scalar]) -> Result<(Scalar, OpeningProof), Error> {
        same_arity(self.key.metadata().arity, point.len())?;
        let value = self.original.evaluate(point)?;
        let raw = Pcs::open(
            &self.key.inner.key,
            self.original.polynomial.as_ref(),
            point,
        );
        same_arity(self.key.metadata().arity, raw.proofs.len())?;
        Ok((
            value,
            OpeningProof {
                raw: Arc::new(raw),
                metadata: self.key.metadata(),
            },
        ))
    }
}

/// Canonical subgroup-checked public verifier material, shared on clone.
#[derive(Clone)]
pub struct VerifierKey {
    inner: Arc<VerifierMaterial>,
}

impl fmt::Debug for VerifierKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("VerifierKey")
            .field("metadata", &self.metadata())
            .finish_non_exhaustive()
    }
}

impl VerifierKey {
    /// Public setup/key identity and exact arity.
    pub fn metadata(&self) -> Metadata {
        self.inner.metadata
    }

    /// Check only public data. Shape/identity errors return Err; well-formed
    /// false opening claims return Ok(false). Both are nonacceptance.
    pub fn check(
        &self,
        commitment: &Commitment,
        point: &[Scalar],
        value: Scalar,
        proof: &OpeningProof,
    ) -> Result<bool, Error> {
        let meta = self.metadata();
        meta.matches(commitment.metadata)?;
        meta.matches(proof.metadata)?;
        same_arity(meta.arity, commitment.raw.nv)?; // upstream check ignores nv
        same_arity(meta.arity, point.len())?; // upstream permits excess
        same_arity(meta.arity, proof.raw.proofs.len())?;
        // Verifier shape is established once by private constructors/import.
        Ok(Pcs::check(
            &self.inner.key,
            &commitment.raw,
            point,
            value,
            &proof.raw,
        ))
    }

    /// Encode this public key using the v1 envelope and fixed-size points.
    pub fn to_bytes(&self, bounds: &Bounds) -> Result<Vec<u8>, Error> {
        let mut bytes = codec::start(self.metadata(), Kind::Verifier, bounds)?;
        codec::write(&self.inner.key.g, &mut bytes)?;
        codec::write(&self.inner.key.h, &mut bytes)?;
        for mask in &self.inner.key.g_mask_random {
            codec::write(mask, &mut bytes)?;
        }
        Ok(bytes)
    }

    /// Import a key against an independently authenticated expected fingerprint.
    /// This validates canonical points, subgroups, shape and byte identity, not
    /// the claimed setup's honest generation or consistency of its full bases.
    /// Never take `expected_key_id` from the same untrusted incoming artifact.
    pub fn from_bytes(
        bytes: &[u8],
        expected_key_id: [u8; 32],
        bounds: &Bounds,
    ) -> Result<Self, Error> {
        let metadata = codec::header(bytes, Kind::Verifier, bounds)?;
        if metadata.key_id != expected_key_id {
            return Err(Error::KeyMismatch);
        }
        let mut input = &bytes[HEADER..];
        let g = codec::read(&mut input, G1_BYTES)?;
        let h = codec::read(&mut input, G2_BYTES)?;
        let mut g_mask_random = vector(metadata.arity)?;
        for _ in 0..metadata.arity {
            g_mask_random.push(codec::read(&mut input, G1_BYTES)?);
        }
        codec::finish(input)?;
        let key = upstream::VerifierKey {
            nv: metadata.arity,
            g,
            h,
            g_mask_random,
        };
        validate_verifier(&key)?;
        if key_fingerprint(metadata.setup_id, &key)? != expected_key_id {
            return Err(Error::KeyMismatch);
        }
        Ok(Self {
            inner: Arc::new(VerifierMaterial { key, metadata }),
        })
    }

    /// Decode a commitment only under this selected key and explicit bounds.
    pub fn decode_commitment(&self, bytes: &[u8], bounds: &Bounds) -> Result<Commitment, Error> {
        let metadata = codec::header(bytes, Kind::Commitment, bounds)?;
        self.metadata().matches(metadata)?;
        let mut input = &bytes[HEADER..];
        let g_product = codec::read(&mut input, G1_BYTES)?;
        codec::finish(input)?;
        Ok(Commitment {
            metadata,
            raw: upstream::Commitment {
                nv: metadata.arity,
                g_product,
            },
        })
    }

    /// Decode a proof only under this selected key. Header identity and exact
    /// total byte count are checked before allocating the quotient vector.
    pub fn decode_proof(&self, bytes: &[u8], bounds: &Bounds) -> Result<OpeningProof, Error> {
        let metadata = codec::header(bytes, Kind::Proof, bounds)?;
        self.metadata().matches(metadata)?;
        let mut input = &bytes[HEADER..];
        let mut proofs = vector(metadata.arity)?;
        for _ in 0..metadata.arity {
            proofs.push(codec::read(&mut input, G2_BYTES)?);
        }
        codec::finish(input)?;
        Ok(OpeningProof {
            metadata,
            raw: Arc::new(upstream::Proof { proofs }),
        })
    }
}

/// Nonhiding public commitment. Private fields prevent bypassing admission.
#[derive(Clone, Debug)]
pub struct Commitment {
    raw: upstream::Commitment<Bls12_381>,
    metadata: Metadata,
}

impl Commitment {
    /// Arity and setup/key bindings.
    pub fn metadata(&self) -> Metadata {
        self.metadata
    }
    /// Encode the envelope and canonical compressed G1 point.
    pub fn to_bytes(&self, bounds: &Bounds) -> Result<Vec<u8>, Error> {
        let mut bytes = codec::start(self.metadata, Kind::Commitment, bounds)?;
        codec::write(&self.raw.g_product, &mut bytes)?;
        Ok(bytes)
    }
}

/// Public G2 quotient commitments. Clone shares the immutable proof vector.
#[derive(Clone, Debug)]
pub struct OpeningProof {
    raw: Arc<upstream::Proof<Bls12_381>>,
    metadata: Metadata,
}

impl OpeningProof {
    /// Arity and setup/key bindings.
    pub fn metadata(&self) -> Metadata {
        self.metadata
    }
    /// Encode the envelope and exactly n canonical compressed G2 points.
    pub fn to_bytes(&self, bounds: &Bounds) -> Result<Vec<u8>, Error> {
        let mut bytes = codec::start(self.metadata, Kind::Proof, bounds)?;
        for point in &self.raw.proofs {
            codec::write(point, &mut bytes)?;
        }
        Ok(bytes)
    }
}

fn key_fingerprint(
    setup_id: [u8; 32],
    key: &upstream::VerifierKey<Bls12_381>,
) -> Result<[u8; 32], Error> {
    codec::fingerprint(b"zkc-arkworks/key/v1", &setup_id, key)
}

fn validate_verifier(key: &upstream::VerifierKey<Bls12_381>) -> Result<(), Error> {
    if key.nv == 0 || key.g_mask_random.len() != key.nv || key.g.is_zero() || key.h.is_zero() {
        return Err(Error::InvalidKey);
    }
    Ok(())
}

fn validate_prover(key: &upstream::CommitterKey<Bls12_381>) -> Result<(), Error> {
    if key.nv == 0
        || key.powers_of_g.len() != key.nv
        || key.powers_of_h.len() != key.nv
        || key.g.is_zero()
        || key.h.is_zero()
    {
        return Err(Error::InvalidKey);
    }
    for i in 0..key.nv {
        let shift = u32::try_from(key.nv - i).map_err(|_| Error::CapacityOverflow)?;
        let expected = 1usize.checked_shl(shift).ok_or(Error::CapacityOverflow)?;
        if key.powers_of_g[i].len() != expected || key.powers_of_h[i].len() != expected {
            return Err(Error::InvalidKey);
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests;
