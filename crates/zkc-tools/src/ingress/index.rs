//! Encoding v1: flatten each canonical A/B/C matrix in row-major order,
//! including implicit zero cells. Interpret the canonical BN254 integer in
//! BLS12-381 Fr (injective because the BN254 modulus is smaller), then pad with
//! zeros to exactly 2^arity. Entry mask m is the coefficient of the squarefree
//! monomial whose logical MSB-first variable mask is m. No trailing-zero trim,
//! sparse-entry concatenation, modular reduction or field homomorphism is used.
//! Subset sums convert these coefficients to Boolean evaluations for the
//! existing multilinear PCS. This is encoding/capacity, not SNARK adequacy.
use super::*;
use ark_ff::{BigInteger, PrimeField};
use zkc_arkworks::{Bounds, CommittedTable, Keys, ProverKey, Scalar, Table, VerifierKey};

pub const PCS_PREMISES: [Premise; 3] = [
    Premise::PcsBasisConsistency,
    Premise::Ceremony,
    Premise::NativeCryptoContracts,
];

pub const INDEX_ENCODING: &str = "zkc.r1cs-integer-multilinear-coefficients/1";
/// Bounds coefficient cells across all three padded tables. Validation uses
/// temporary coefficient and evaluation copies; only evaluation tables remain
/// in the checked value. This is not a global host-allocation reservation.
#[derive(Clone, Copy, Debug)]
pub struct IndexLimits {
    pub max_coefficients: usize,
}
impl Default for IndexLimits {
    fn default() -> Self {
        Self {
            max_coefficients: 3 * (1 << 20),
        }
    }
}

/// Authenticated local/configuration keys. Exact bytes supplement existing hash
/// pins. No relation is part of this subject and no ceremony claim is made.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExpectedSetup {
    verifier_bytes: Arc<[u8]>,
    prover_bytes: Arc<[u8]>,
    verifier_pin: [u8; 32],
    prover_pin: [u8; 32],
}
impl ExpectedSetup {
    pub fn from_keys(expected: &Keys, bounds: &Bounds) -> Result<Self> {
        Self::from_configured_keys(expected.prover_key(), expected.verifier_key(), bounds)
    }
    /// Already authenticated imported keys can supply configuration too.
    pub fn from_configured_keys(
        prover: &ProverKey,
        verifier: &VerifierKey,
        bounds: &Bounds,
    ) -> Result<Self> {
        if prover.metadata() != verifier.metadata() {
            return Err(fail(FailureKind::Mismatch, "ingress-setup-pair"));
        }
        Ok(Self {
            verifier_bytes: verifier.to_bytes(bounds).map_err(pcs_error)?.into(),
            prover_bytes: prover.to_bytes(bounds).map_err(pcs_error)?.into(),
            verifier_pin: verifier.metadata().key_id(),
            prover_pin: prover.material_fingerprint(),
        })
    }
    pub fn verifier_bytes(&self) -> &[u8] {
        &self.verifier_bytes
    }
    pub fn prover_bytes(&self) -> &[u8] {
        &self.prover_bytes
    }
    pub fn check(
        &self,
        verifier_bytes: &[u8],
        prover_bytes: &[u8],
        bounds: &Bounds,
    ) -> Result<CheckedSetup> {
        let verifier = VerifierKey::from_bytes(verifier_bytes, self.verifier_pin, bounds)
            .map_err(pcs_error)?;
        let prover = ProverKey::from_bytes(prover_bytes, self.prover_pin, &verifier, bounds)
            .map_err(pcs_error)?;
        // Canonical key bytes that decode under both pins are the pinned bytes
        // unless SHA-256 collides.
        assert!(
            verifier_bytes == self.verifier_bytes.as_ref()
                && prover_bytes == self.prover_bytes.as_ref(),
            "setup keys accepted under their pins differ from the pinned bytes"
        );
        Ok(CheckedSetup {
            expected: self.clone(),
            prover,
            verifier,
            bounds: *bounds,
        })
    }
}
#[derive(Clone, Debug)]
pub struct CheckedSetup {
    expected: ExpectedSetup,
    prover: ProverKey,
    verifier: VerifierKey,
    bounds: Bounds,
}
impl CheckedSetup {
    pub fn arity(&self) -> usize {
        self.prover.metadata().arity()
    }
    pub fn capacity(&self) -> usize {
        1usize << self.arity()
    }
    pub fn verifier(&self) -> &VerifierKey {
        &self.verifier
    }
    pub fn evidence(&self) -> [EvidenceStatus; 4] {
        [
            EvidenceStatus::Checked(Predicate::PcsMaterialAndCapacity),
            EvidenceStatus::MissingProof(Premise::PcsBasisConsistency),
            EvidenceStatus::MissingProof(Premise::Ceremony),
            EvidenceStatus::MissingProof(Premise::NativeCryptoContracts),
        ]
    }
    pub fn check_index(
        &self,
        expected_relation: &RelationSubject,
        candidate: &CoefficientIndex,
        limits: IndexLimits,
    ) -> Result<CheckedIndex> {
        // Recompute under this relation and setup. A candidate does not provide
        // the expected relation, dimensions, encoding or padding convention.
        let recomputed = CoefficientIndex::encode(expected_relation, self.arity(), limits)?;
        if candidate != &recomputed {
            return Err(fail(FailureKind::Mismatch, "ingress-index-mismatch"));
        }
        let mut tables = Vec::new();
        for coefficients in &recomputed.coefficients {
            let mut values = coefficients.clone();
            for bit in 0..self.arity() {
                for mask in 0..values.len() {
                    if mask & (1 << bit) != 0 {
                        let lower = values[mask ^ (1 << bit)];
                        values[mask] += lower;
                    }
                }
            }
            tables.push(Table::from_logical_vec(values, &self.bounds).map_err(pcs_error)?);
        }
        Ok(CheckedIndex {
            setup: self.expected.clone(),
            subject: IndexSubject {
                relation: expected_relation.clone(),
                encoding: recomputed.encoding,
                rows: recomputed.rows,
                columns: recomputed.columns,
                arity: recomputed.arity,
            },
            tables: tables.try_into().expect("three matrices"),
        })
    }
    /// Actual PCS use takes checked material and independently expected relation;
    /// no public setter can retag the index or replace its retained tables.
    pub fn commit_index(
        &self,
        expected_relation: &RelationSubject,
        index: &CheckedIndex,
        accepted: &AcceptedPremises,
    ) -> Result<CommittedIndex> {
        index.check_applicability(self, expected_relation)?;
        authorize(PCS_PREMISES, accepted)?;
        let mut committed = Vec::new();
        for table in &index.tables {
            committed.push(self.prover.commit(table).map_err(pcs_error)?);
        }
        Ok(CommittedIndex {
            setup: self.expected.clone(),
            subject: index.subject.clone(),
            tables: committed.try_into().expect("three matrices"),
        })
    }
}

/// Untrusted candidate. Public fields deliberately allow external indexers;
/// only recomputation can produce CheckedIndex.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CoefficientIndex {
    pub encoding: String,
    pub relation_descriptor: Vec<u8>,
    pub rows: usize,
    pub columns: usize,
    pub arity: usize,
    pub coefficients: [Vec<Scalar>; 3],
}
impl CoefficientIndex {
    pub fn encode(relation: &RelationSubject, arity: usize, limits: IndexLimits) -> Result<Self> {
        let len = u32::try_from(arity)
            .ok()
            .and_then(|s| 1usize.checked_shl(s))
            .ok_or_else(|| fail(FailureKind::Resource, "ingress-index-capacity-overflow"))?;
        if len
            .checked_mul(3)
            .is_none_or(|n| n > limits.max_coefficients.min(3 * (1 << 20)))
        {
            return Err(fail(FailureKind::Resource, "ingress-index-budget"));
        }
        let r = relation.relation();
        if arity == 0 || r.rows().checked_mul(r.columns()).is_none_or(|n| n > len) {
            return Err(fail(FailureKind::Mismatch, "ingress-setup-capacity"));
        }
        let mut coefficients: [Vec<Scalar>; 3] = Default::default();
        for (matrix, output) in r.matrices().iter().zip(&mut coefficients) {
            // Bounded by ingress-index-budget above.
            output.resize(len, Scalar::from(0));
            for &(row, column, value) in matrix.entries() {
                // BN254's least nonnegative integer is below BLS12-381 Fr.
                output[row as usize * r.columns() + column as usize] =
                    Scalar::from_le_bytes_mod_order(&value.into_bigint().to_bytes_le());
            }
        }
        Ok(Self {
            encoding: INDEX_ENCODING.into(),
            relation_descriptor: relation.descriptor().to_vec(),
            rows: r.rows(),
            columns: r.columns(),
            arity,
            coefficients,
        })
    }
}
#[derive(Clone, Debug)]
pub struct CheckedIndex {
    setup: ExpectedSetup,
    subject: IndexSubject,
    tables: [Table; 3],
}
impl CheckedIndex {
    pub fn subject(&self) -> &IndexSubject {
        &self.subject
    }
    pub fn evidence(&self) -> EvidenceStatus {
        EvidenceStatus::Checked(Predicate::MatrixCoefficientEncoding)
    }
    pub fn check_applicability(
        &self,
        setup: &CheckedSetup,
        relation: &RelationSubject,
    ) -> Result<()> {
        if self.setup != setup.expected || &self.subject.relation != relation {
            return Err(fail(FailureKind::Mismatch, "ingress-index-subject"));
        }
        Ok(())
    }
}

/// Exact preparation subject, retained separately from the polynomial values.
/// Equal A/B/C tables with different public layouts are different subjects.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IndexSubject {
    relation: RelationSubject,
    encoding: String,
    rows: usize,
    columns: usize,
    arity: usize,
}
impl IndexSubject {
    pub fn relation(&self) -> &RelationSubject {
        &self.relation
    }
    pub fn encoding(&self) -> &str {
        &self.encoding
    }
    pub fn dimensions(&self) -> (usize, usize) {
        (self.rows, self.columns)
    }
    pub fn arity(&self) -> usize {
        self.arity
    }
    /// Canonical bytes that a protocol's authenticated statement carries next
    /// to the raw commitments. Relations whose flattened cells coincide, such
    /// as a 1x4 and a 2x2 matrix with the same row-major entries, commit to
    /// equal tables, so the commitments alone do not identify the matrices;
    /// these bytes name the relation, encoding, dimensions and arity.
    pub fn binding(&self) -> Vec<u8> {
        use sha2::{Digest, Sha256};
        let descriptor = Sha256::digest(self.relation.descriptor());
        serde_json::to_vec(&serde_json::json!([
            "zkc.index-subject/1",
            crate::artifact::hex(&descriptor),
            self.encoding,
            self.rows.to_string(),
            self.columns.to_string(),
            self.arity.to_string()
        ]))
        .expect("strings serialize")
    }
}

/// Native commitments paired with the exact checked preparation subject.
/// Sending only the raw commitments binds neither the relation's public layout
/// nor its dimensions; a protocol must bind [`IndexSubject::binding`] through
/// its own authenticated statement.
pub struct CommittedIndex {
    setup: ExpectedSetup,
    subject: IndexSubject,
    tables: [CommittedTable; 3],
}
impl std::fmt::Debug for CommittedIndex {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CommittedIndex")
            .field("subject", &self.subject)
            .finish_non_exhaustive()
    }
}
impl CommittedIndex {
    pub fn subject(&self) -> &IndexSubject {
        &self.subject
    }
    pub fn tables(&self) -> &[CommittedTable; 3] {
        &self.tables
    }
    pub fn check_applicability(
        &self,
        setup: &CheckedSetup,
        relation: &RelationSubject,
    ) -> Result<()> {
        if self.setup != setup.expected || &self.subject.relation != relation {
            return Err(fail(FailureKind::Mismatch, "ingress-commitment-subject"));
        }
        Ok(())
    }
}
