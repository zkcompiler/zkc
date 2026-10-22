//! BLS12-381 scalar tables and arkworks 0.6.0 `MultilinearPC` kernels.
//!
//! Logical tables use MSB-first coordinates. Storage is bit-reversed once on
//! ingress; points keep their logical order. Clones share immutable originals,
//! and restriction creates independent scratch. The PCS is **nonhiding**.
//!
//! Local setup is a development facility, not a ceremony. Public key import
//! requires a previously authenticated key fingerprint. Fingerprints identify
//! bytes and the selected profile; they do not validate an adversarial setup.
//! `ProverKey` transports only public SRS material, with a separate full-material
//! pin and an admitted `VerifierKey`; private opening state stays local.
//! See the crate README for wire formats, trust, and allocation limits.
//!
//! ```
//! use zkc_kernels::arkworks::bls12_381::{Bounds, Keys, ProverKey, Scalar, Table, VerifierKey};
//! # fn main() -> Result<(), zkc_kernels::arkworks::Error> {
//! let bounds = Bounds::new(8, 256, 1 << 20, 8 * 256);
//! let keys = Keys::setup_for_development(2, &bounds)?;
//! let table = Table::from_logical(
//!     &[2u64, 3, 5, 7].map(Scalar::from), &bounds)?;
//! let original = keys.prover_key().commit(&table)?;
//! let point = [11u64, 13].map(Scalar::from);
//! let (value, proof) = original.open(&point)?;
//! // Deliver this pin through an authenticated configuration channel.
//! let pin = keys.verifier_key().metadata().key_id();
//! let verifier = VerifierKey::from_bytes(
//!     &keys.verifier_key().to_bytes(&bounds)?, pin, &bounds)?;
//! let commitment = verifier.decode_commitment(
//!     &original.commitment().to_bytes(&bounds)?, &bounds)?;
//! let proof = verifier.decode_proof(&proof.to_bytes(&bounds)?, &bounds)?;
//! assert!(verifier.check(&commitment, &point, value, &proof)?);
//! // Persist public proving material for another producer process. Its expected
//! // full-material pin also comes from local setup/authenticated configuration.
//! let prover_pin = keys.prover_key().material_fingerprint();
//! let prover = ProverKey::from_bytes(
//!     &keys.prover_key().to_bytes(&bounds)?, prover_pin, &verifier, &bounds)?;
//! let reloaded = prover.commit(&table)?;
//! let (value, proof) = reloaded.open(&point)?;
//! assert!(verifier.check(reloaded.commitment(), &point, value, &proof)?);
//! # Ok(())
//! # }
//! ```
//!
//! Published storage cannot be mutated through an alias:
//! ```compile_fail
//! # use zkc_kernels::arkworks::bls12_381::Table;
//! fn overwrite(table: &mut Table) {
//!     table.polynomial.evaluations.clear();
//! }
//! ```
//! Raw upstream commitment objects cannot bypass metadata admission:
//! ```compile_fail
//! use zkc_kernels::arkworks::bls12_381::Commitment;
//! fn bypass(raw: ark_poly_commit::multilinear_pc::data_structures::Commitment<ark_bls12_381::Bls12_381>) -> Commitment {
//!     Commitment { raw }
//! }
//! ```

mod bounds;
mod codec;
mod group;
mod pcs;
mod random;
mod scalar;
mod table;
mod table_msb;
use super::Error;
pub use ark_bls12_381::Fr as Scalar;
pub use bounds::Bounds;
pub use group::{G1, GROUP_BYTES, scalar_from_wide_be};
pub use pcs::{Commitment, CommittedTable, Keys, Metadata, OpeningProof, ProverKey, VerifierKey};
pub use random::RandomSource;
pub use scalar::{SCALAR_BYTES, decode_scalar, encode_scalar, parse_decimal};
pub use table::Table;
pub use table_msb::MsbTable;
/// Scheme, field, layout, embedding and codec identity; bytes are construction inputs.
pub const PROFILE: &str = "zkc-arkworks/v0;arkworks=0.6.0;field=BLS12-381::Fr;pcs=MultilinearPC;hiding=false;logical=msb-first;storage=bit-reversal;point=unchanged;embedding=identity;codec=compressed-exact-v0";
/// Exact order of the scalar field.
pub const SCALAR_MODULUS_DECIMAL: &str =
    "52435875175126190479447740508185965837690552500527637822603658699938581184513";

use ark_bls12_381::{Bls12_381, G2Affine, G2Projective};
use ark_ec::{AffineRepr, CurveGroup, VariableBaseMSM, pairing::Pairing};
use ark_ff::{PrimeField, Zero};
use ark_serialize::CanonicalSerialize;

/// Checked prime-order G2 subgroup point with private upstream coordinates.
/// The compressed encoding is the 96-byte big-endian format with the
/// compression, infinity and sign flags in the three most significant bits.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct G2(G2Affine);
crate::arkworks::scaling::impl_scaling!(G2, ark_bls12_381::g2::Config);
impl G2 {
    /// Canonical compressed byte width.
    pub const BYTES: usize = 96;
    /// Standard generator.
    pub fn generator() -> Self {
        Self(G2Affine::generator())
    }
    /// Additive identity.
    pub fn identity() -> Self {
        Self(G2Affine::identity())
    }
    /// Group addition.
    pub fn add(&self, b: &Self) -> Self {
        Self((self.0 + b.0).into_affine())
    }
    /// Additive inverse.
    pub fn neg(&self) -> Self {
        Self(-self.0)
    }
    /// Scalar multiplication; zero is allowed.
    pub fn scale(&self, s: Scalar) -> Self {
        Self(self.0.mul_bigint(s.into_bigint()).into_affine())
    }
    /// Checked equal-length MSM. The caller bounds workload and scratch memory.
    pub fn msm(s: &[Scalar], p: &[Self]) -> Result<Self, Error> {
        if s.len() != p.len() {
            return Err(Error::InvalidEncoding);
        }
        let mut bases = crate::arkworks::allocation::vector(p.len())?;
        bases.extend(p.iter().map(|p| p.0));
        Ok(Self(
            G2Projective::msm(&bases, s)
                .map_err(|_| Error::InvalidEncoding)?
                .into_affine(),
        ))
    }
    /// Exact canonical compressed encoding.
    pub fn to_bytes(&self) -> Result<[u8; Self::BYTES], Error> {
        let mut b = [0; Self::BYTES];
        self.0
            .serialize_compressed(&mut b[..])
            .map_err(|_| Error::InvalidEncoding)?;
        Ok(b)
    }
    /// Canonical decoding, including curve, subgroup and unique infinity checks.
    pub fn from_bytes(b: &[u8]) -> Result<Self, Error> {
        if b.len() != Self::BYTES {
            return Err(Error::InvalidEncoding);
        }
        let mut input = b;
        Ok(Self(crate::arkworks::codec::read(&mut input, Self::BYTES)?))
    }
}

/// Product of pairings equals one. Empty product is one; lengths must match.
/// The caller bounds workload and preparation memory before entering arkworks.
pub fn pairing_check(a: &[G1], b: &[G2]) -> Result<bool, Error> {
    if a.len() != b.len() {
        return Err(Error::InvalidEncoding);
    }
    Ok(Bls12_381::multi_pairing(a.iter().map(|p| p.0), b.iter().map(|p| p.0)).is_zero())
}

/// Prime-order BLS12-381 pairing target. Abstract additive notation denotes
/// target field multiplication; scalar multiplication denotes exponentiation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Gt(ark_ec::pairing::PairingOutput<Bls12_381>);
impl Gt {
    /// Canonical target-field byte width (twelve base-field coefficients).
    pub const BYTES: usize = 576;
    /// Pairing of the installed source generators.
    pub fn generator() -> Self {
        pairing(&G1::generator(), &G2::generator())
    }
    /// Multiplicative one, the abstract group identity.
    pub fn identity() -> Self {
        Self(ark_ec::pairing::PairingOutput::zero())
    }
    /// Target group product.
    pub fn add(&self, other: &Self) -> Self {
        Self(self.0 + other.0)
    }
    /// Target group inverse.
    pub fn neg(&self) -> Self {
        Self(-self.0)
    }
    /// Target group exponentiation by a canonical scalar.
    pub fn scale(&self, scalar: Scalar) -> Self {
        Self(self.0 * scalar)
    }
    /// Canonical representation of the twelve base-field coefficients.
    pub fn to_bytes(&self) -> Result<[u8; Self::BYTES], Error> {
        let mut bytes = [0; Self::BYTES];
        self.0
            .serialize_compressed(&mut bytes[..])
            .map_err(|_| Error::InvalidEncoding)?;
        Ok(bytes)
    }
    /// Exact canonical decoding with arkworks' prime-order subgroup check.
    /// In particular, extension-field zero and non-subgroup values are refused.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, Error> {
        if bytes.len() != Self::BYTES {
            return Err(Error::InvalidEncoding);
        }
        let mut input = bytes;
        Ok(Self(crate::arkworks::codec::read(&mut input, Self::BYTES)?))
    }
}
/// Total bilinear map into the prime-order target, including final exponentiation.
pub fn pairing(a: &G1, b: &G2) -> Gt {
    Gt(Bls12_381::pairing(a.0, b.0))
}
