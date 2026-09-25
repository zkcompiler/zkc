//! The ONLY module calling opaque upstream proof algorithms. Independent
//! interoperability/performance baseline, never called by our prover/validator.
use crate::{Statement, application_transcript};
use bulletproofs::{BulletproofGens, PedersenGens, RangeProof};
use curve25519_dalek::{ristretto::CompressedRistretto, scalar::Scalar};
use rand_core::{CryptoRng, RngCore};

pub struct Upstream {
    pub bp: BulletproofGens,
    pub pc: PedersenGens,
}
impl Upstream {
    pub fn new(n: usize, m: usize) -> Self {
        Self {
            bp: BulletproofGens::new(n, m),
            pc: PedersenGens::default(),
        }
    }
    pub fn prove<R: RngCore + CryptoRng>(
        &self,
        statement: &Statement,
        values: &[u64],
        blindings: &[Scalar],
        rng: &mut R,
    ) -> (Vec<u8>, Vec<[u8; 32]>, [u8; 32]) {
        let mut t = application_transcript(&statement.context);
        let (proof, commitments) = RangeProof::prove_multiple_with_rng(
            &self.bp,
            &self.pc,
            &mut t,
            values,
            blindings,
            statement.bits,
            rng,
        )
        .expect("independent upstream proving baseline");
        let mut end = [0; 32];
        t.challenge_bytes(b"research-end-state", &mut end);
        (
            proof.to_bytes(),
            commitments.iter().map(|p| p.to_bytes()).collect(),
            end,
        )
    }
    pub fn verify<R: RngCore + CryptoRng>(
        &self,
        statement: &Statement,
        bytes: &[u8],
        rng: &mut R,
    ) -> std::result::Result<[u8; 32], bulletproofs::ProofError> {
        let proof = RangeProof::from_bytes(bytes)?;
        let mut t = application_transcript(&statement.context);
        let commitments: Vec<_> = statement
            .commitments
            .iter()
            .map(|b| CompressedRistretto(*b))
            .collect();
        proof.verify_multiple_with_rng(
            &self.bp,
            &self.pc,
            &mut t,
            &commitments,
            statement.bits,
            rng,
        )?;
        let mut end = [0; 32];
        t.challenge_bytes(b"research-end-state", &mut end);
        Ok(end)
    }
}
