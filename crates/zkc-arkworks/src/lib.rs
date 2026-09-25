#![warn(missing_docs)]
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
//! use zkc_arkworks::{Bounds, Keys, ProverKey, Scalar, Table, VerifierKey};
//! # fn main() -> Result<(), zkc_arkworks::Error> {
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
//! # use zkc_arkworks::Table;
//! fn overwrite(table: &mut Table) {
//!     table.polynomial.evaluations.clear();
//! }
//! ```
//! Raw upstream commitment objects cannot bypass metadata admission:
//! ```compile_fail
//! use zkc_arkworks::Commitment;
//! fn bypass(raw: ark_poly_commit::multilinear_pc::data_structures::Commitment<ark_bls12_381::Bls12_381>) -> Commitment {
//!     Commitment { raw }
//! }
//! ```

mod bounds;
mod codec;
mod error;
mod field;
mod pcs;
mod random;
mod table;
mod table_msb;

pub use ark_bls12_381::Fr as Scalar;
pub use bounds::Bounds;
pub use error::Error;
pub use field::{SCALAR_BYTES, decode_scalar, encode_scalar, parse_decimal};
pub use pcs::{Commitment, CommittedTable, Keys, Metadata, OpeningProof, ProverKey, VerifierKey};
pub use random::RandomSource;
pub use table::Table;
pub use table_msb::MsbTable;

/// The exact scheme, scalar, layout, embedding and codec profile bound by IDs.
/// Base and challenge fields are identical; the embedding is the identity.
pub const PROFILE: &str = "zkc-arkworks/v1;arkworks=0.6.0;field=BLS12-381::Fr;pcs=MultilinearPC;hiding=false;logical=msb-first;storage=bit-reversal;point=unchanged;embedding=identity;codec=compressed-exact-v1";

mod group;
pub use group::{GROUP_BYTES, GroupPoint, scalar_from_wide_be};

/// Validated BN254 field and pairing groups.
pub mod bn254;
