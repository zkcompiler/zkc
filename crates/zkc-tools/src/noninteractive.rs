//! Prepared execution of protocols whose proof flow is already one-way.
//!
//! Unlike Fiat–Shamir construction, this path projects the authored protocol
//! directly. It requires an installed source-correspondence checker and then
//! admits the actual endpoint graph as a public noninteractive protocol.
//! Public statement/key selection remains an explicit application obligation.

use crate::{artifact, protocol::WireBackend};
use sha2::{Digest, Sha256};
use zkc_runtime::interactive::{
    AdmissionError, Backend, Correspondence, LoadError, NoninteractiveEntry, NoninteractiveError,
    Runner, admit_physical,
};

#[derive(Debug)]
pub enum PrepareError {
    Correspondence(AdmissionError),
    Profile(NoninteractiveError),
}
impl std::fmt::Display for PrepareError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Correspondence(e) => e.fmt(f),
            Self::Profile(e) => e.fmt(f),
        }
    }
}
impl std::error::Error for PrepareError {}

/// Immutable checked code and endpoint selection. No witness or randomness is
/// retained here; one prepared artifact may serve many statements/invocations.
#[derive(Clone, Debug)]
pub struct NoninteractiveArtifact {
    entry: NoninteractiveEntry,
    identity: [u8; 32],
}

fn item(hash: &mut Sha256, bytes: &[u8]) {
    hash.update((bytes.len() as u64).to_le_bytes());
    hash.update(bytes);
}

impl NoninteractiveArtifact {
    pub fn prepare<B: Backend, C: Correspondence>(
        source: &[u8],
        candidate: &[u8],
        backend: &B,
        checker: &C,
        selection: (&str, &str, &str, usize),
    ) -> Result<Self, PrepareError> {
        let admitted = admit_physical(source, candidate, backend, checker)
            .map_err(PrepareError::Correspondence)?;
        let (name, producer, verifier, acceptance) = selection;
        let entry = NoninteractiveEntry::new(admitted, name, producer, verifier, acceptance)
            .map_err(PrepareError::Profile)?;
        let mut hash = Sha256::new();
        item(&mut hash, b"zkc.noninteractive-code/1");
        item(&mut hash, source);
        item(&mut hash, candidate);
        item(&mut hash, name.as_bytes());
        item(&mut hash, producer.as_bytes());
        item(&mut hash, verifier.as_bytes());
        item(&mut hash, &(acceptance as u64).to_le_bytes());
        Ok(Self {
            entry,
            identity: hash.finalize().into(),
        })
    }

    pub fn entry(&self) -> &NoninteractiveEntry {
        &self.entry
    }

    /// Bind an application-owned canonical statement and prepared public-key
    /// context. The candidate proof must never choose these bytes. Hashing is
    /// transport context separation, not a proof that an arbitrary key encodes
    /// a named relation, nor a substitute for the protocol's verifier equation.
    pub fn bind(&self, public_context: &[u8]) -> ProofInvocation<'_> {
        let mut hash = Sha256::new();
        item(&mut hash, b"zkc.noninteractive-invocation/1");
        item(&mut hash, &self.identity);
        item(&mut hash, public_context);
        ProofInvocation {
            artifact: self,
            binding: hash.finalize().into(),
        }
    }
}

/// Statement-specific context shared by independently created endpoints.
pub struct ProofInvocation<'a> {
    artifact: &'a NoninteractiveArtifact,
    binding: [u8; 32],
}
impl ProofInvocation<'_> {
    pub fn binding(&self) -> &[u8; 32] {
        &self.binding
    }
    /// Stable origin for this invocation. Proof replay for the same statement
    /// and key is intentional; this is not an interactive freshness guarantee.
    pub fn session(&self) -> String {
        self.binding
            .iter()
            .map(|byte| format!("{byte:02x}"))
            .collect()
    }
    pub fn producer<B: WireBackend>(
        &self,
        backend: B,
        inputs: Vec<B::Value>,
    ) -> Result<ProofProducer<B>, LoadError<B>> {
        let entry = &self.artifact.entry;
        let runner = Runner::new(
            entry.admitted(),
            entry.entry(),
            &entry.producer().role,
            &self.session(),
            backend,
            inputs,
        )?;
        Ok(ProofProducer {
            runner,
            binding: self.binding,
        })
    }
    pub fn verifier<B: WireBackend>(
        &self,
        backend: B,
        inputs: Vec<B::Value>,
    ) -> Result<ProofVerifier<B>, LoadError<B>> {
        let entry = &self.artifact.entry;
        let runner = Runner::new(
            entry.admitted(),
            entry.entry(),
            &entry.verifier().role,
            &self.session(),
            backend,
            inputs,
        )?;
        Ok(ProofVerifier {
            runner,
            binding: self.binding,
            acceptance: entry.acceptance(),
        })
    }
}

pub struct ProofProducer<B: WireBackend> {
    runner: Runner<B>,
    binding: [u8; 32],
}
impl<B: WireBackend> ProofProducer<B> {
    pub fn produce(&mut self) -> artifact::ArtifactReport<artifact::Produced<B::Value>> {
        artifact::produce(&mut self.runner, &self.binding)
    }
    pub fn backend(&self) -> &B {
        self.runner.backend()
    }
    pub fn into_backend(self) -> B {
        self.runner.into_backend()
    }
}

pub struct ProofVerifier<B: WireBackend> {
    runner: Runner<B>,
    binding: [u8; 32],
    acceptance: usize,
}
impl<B: WireBackend> ProofVerifier<B> {
    pub fn verify(
        &mut self,
        proof: &[u8],
        boolean: impl Fn(&B::Value) -> Option<bool>,
    ) -> artifact::ArtifactReport<Vec<B::Value>> {
        artifact::validate(
            &mut self.runner,
            proof,
            &self.binding,
            self.acceptance,
            boolean,
        )
    }
    pub fn backend(&self) -> &B {
        self.runner.backend()
    }
    pub fn into_backend(self) -> B {
        self.runner.into_backend()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn context_hashing_frames_each_item() {
        let hash = |items: &[&[u8]]| {
            let mut hash = Sha256::new();
            for bytes in items {
                item(&mut hash, bytes);
            }
            hash.finalize()
        };
        assert_ne!(hash(&[b"ab", b"c"]), hash(&[b"a", b"bc"]));
        assert_ne!(hash(&[b"a", b""]), hash(&[b"a"]));
    }
}
