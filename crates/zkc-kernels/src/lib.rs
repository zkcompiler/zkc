//! VM-independent typed mathematical kernels.
//!
//! Shared field, vector, matrix and polynomial algorithms use explicit provider
//! types. Providers own their concrete arithmetic and encodings;
//! interop owns exact pinned external constructions. The calling backend owns
//! VM values, authority, resource admission and output publication.
pub mod allocation;
pub mod arkworks;
pub mod blst;
/// Shared CPU workers for typed numerical phases; independent of the VM.
pub mod cpu;
pub mod dalek;
pub mod field;
pub mod halo2curves;
pub mod interop;
pub mod matrix;
pub mod numerical;
pub mod plonky3;
pub mod polynomial;
pub mod vector;
