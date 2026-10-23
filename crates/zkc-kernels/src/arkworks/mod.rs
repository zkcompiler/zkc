//! Arkworks-backed curves, fields and multilinear commitments.
//!
//! The workspace keeps ark-ec and PCS parallel features disabled: ark-ec 0.6
//! full-width MSM otherwise creates private Rayon pools inside an installed
//! owner. Field and polynomial parallel features remain enabled; their numerical
//! leaves still require `cpu::install` to reuse the caller's CPU workers.
mod allocation;
mod codec;
mod error;
pub use error::Error;
pub mod bls12_381;
pub mod bn254;
pub mod scaling;
