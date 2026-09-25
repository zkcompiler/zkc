//! Fixed-shape transport for public proving material. Upstream 0.6.0 setup
//! creates n rows of lengths 2^n, ..., 2 in each group (multilinear_pc/mod.rs).
//! Never deserialize an upstream CommitterKey or any vector from incoming bytes.
use super::*;
use crate::bounds::allocation_size;
use ark_bls12_381::{G1Affine, G2Affine};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};

impl ProverKey {
    /// Full public prover-material SHA-256 pin, including profile, arity,
    /// setup/key IDs, both generators and every G1/G2 basis point.
    /// Obtain the expected pin from local setup/export or authenticated
    /// configuration, never from the same untrusted incoming artifact.
    /// This cached identity is not evidence of an honest or consistent SRS.
    pub fn material_fingerprint(&self) -> [u8; 32] {
        self.inner.material_fingerprint
    }

    /// Encode public proving material with the v1 envelope, kind 4, and
    /// fixed-width compressed points. No witness or opening state is included.
    /// Row lengths are implicit in the positive arity; there are no Vec lengths.
    pub fn to_bytes(&self, bounds: &Bounds) -> Result<Vec<u8>, Error> {
        let mut bytes = codec::start(self.metadata(), Kind::Prover, bounds)?;
        let key = &self.inner.key;
        codec::write(&key.g, &mut bytes)?;
        codec::write(&key.h, &mut bytes)?;
        for row in &key.powers_of_g {
            for point in row {
                codec::write(point, &mut bytes)?;
            }
        }
        for row in &key.powers_of_h {
            for point in row {
                codec::write(point, &mut bytes)?;
            }
        }
        Ok(bytes)
    }

    /// Import canonical public proving material under an independently expected
    /// full-material pin and an actual admitted verifier key of exactly this
    /// arity. Check metadata, shared generators, full setup hash, fixed shape,
    /// curve/subgroup membership, canonical bytes and exact EOF.
    ///
    /// The expected pin must come from local setup/export or authenticated
    /// configuration. A candidate cannot authorize itself. These checks bind
    /// bytes; they do not prove that the bases/masks have consistent algebraic
    /// relations or that trapdoors were honestly sampled, kept secret or erased.
    /// Malicious or inconsistent but correctly pinned SRS remains possible.
    ///
    /// Arity, total bytes and all array capacities are checked before allocating
    /// basis vectors. Import uses the arity/element/byte policy, not the setup
    /// work limit: it runs no setup. Bounds are per object, not a session budget.
    pub fn from_bytes(
        bytes: &[u8],
        expected_material_fingerprint: [u8; 32],
        verifier: &VerifierKey,
        bounds: &Bounds,
    ) -> Result<Self, Error> {
        let metadata = codec::header(bytes, Kind::Prover, bounds)?;
        verifier.metadata().matches(metadata)?;
        // Preflight every possible row capacity via the total basis count,
        // as well as both outer vectors, before any parsing or allocation.
        let bases = codec::prover_basis_count(metadata.arity)?;
        allocation_size::<G1Affine>(bases)?;
        allocation_size::<G2Affine>(bases)?;
        allocation_size::<Vec<G1Affine>>(metadata.arity)?;
        allocation_size::<Vec<G2Affine>>(metadata.arity)?;
        let mut input = &bytes[HEADER..];
        let g = codec::read(&mut input, G1_BYTES)?;
        let h = codec::read(&mut input, G2_BYTES)?;
        if g != verifier.inner.key.g || h != verifier.inner.key.h {
            return Err(Error::KeyMismatch);
        }
        let powers_of_g = read_bases(&mut input, metadata.arity, G1_BYTES)?;
        let powers_of_h = read_bases(&mut input, metadata.arity, G2_BYTES)?;
        codec::finish(input)?;
        let key = upstream::CommitterKey {
            nv: metadata.arity,
            powers_of_g,
            powers_of_h,
            g,
            h,
        };
        validate_prover(&key)?;
        let material_fingerprint = material_fingerprint(metadata, &key)?;
        if material_fingerprint != expected_material_fingerprint
            || setup_fingerprint(&key, &verifier.inner.key)? != metadata.setup_id
        {
            return Err(Error::KeyMismatch);
        }
        Ok(Self {
            inner: Arc::new(ProverMaterial {
                key,
                metadata,
                material_fingerprint,
            }),
        })
    }
}

fn read_bases<T: CanonicalDeserialize + CanonicalSerialize>(
    input: &mut &[u8],
    n: usize,
    width: usize,
) -> Result<Vec<Vec<T>>, Error> {
    let mut rows = vector(n)?;
    for i in 0..n {
        // All dimensions were admitted before entering this function.
        let shift = u32::try_from(n - i).map_err(|_| Error::CapacityOverflow)?;
        let len = 1usize.checked_shl(shift).ok_or(Error::CapacityOverflow)?;
        let mut row = vector(len)?;
        for _ in 0..len {
            row.push(codec::read(input, width)?);
        }
        rows.push(row);
    }
    Ok(rows)
}

pub(super) fn material_fingerprint(
    metadata: Metadata,
    key: &upstream::CommitterKey<Bls12_381>,
) -> Result<[u8; 32], Error> {
    let mut context = [0u8; 64];
    context[..32].copy_from_slice(&metadata.setup_id);
    context[32..].copy_from_slice(&metadata.key_id);
    codec::fingerprint(b"zkc-arkworks/prover/v1", &context, key)
}

/// Serialization-only borrowed view matching upstream UniversalParams field
/// order. Reconstruct its hash from the exact-arity CK plus admitted VK masks,
/// without cloning O(2^n) basis storage or exposing a raw constructor.
#[derive(CanonicalSerialize)]
struct SetupView<'a> {
    num_vars: usize,
    powers_of_g: &'a Vec<Vec<G1Affine>>,
    powers_of_h: &'a Vec<Vec<G2Affine>>,
    g: &'a G1Affine,
    h: &'a G2Affine,
    g_mask: &'a Vec<G1Affine>,
}

fn setup_fingerprint(
    key: &upstream::CommitterKey<Bls12_381>,
    verifier: &upstream::VerifierKey<Bls12_381>,
) -> Result<[u8; 32], Error> {
    codec::fingerprint(
        b"zkc-arkworks/setup/v1",
        &[],
        &SetupView {
            num_vars: key.nv,
            powers_of_g: &key.powers_of_g,
            powers_of_h: &key.powers_of_h,
            g: &key.g,
            h: &key.h,
            g_mask: &verifier.g_mask_random,
        },
    )
}
