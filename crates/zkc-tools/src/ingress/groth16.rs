use super::*;
use crate::{
    groth16::{
        Invocation, PreparedProtocol, ProducedProof, ProverKey, Randomness, Statement, VerifyingKey,
    },
    snarkjs::{self, Limits, Witness},
};
use std::collections::BTreeSet;

pub const GROTH16_PREMISES: [Premise; 6] = [
    Premise::Groth16CDerivation,
    Premise::Groth16IcDerivation,
    Premise::Groth16HDerivation,
    Premise::Groth16QueryConsistency,
    Premise::Ceremony,
    Premise::NativeCryptoContracts,
];

/// Independently selected compiled input contract. Construction establishes
/// only well-formed configuration; it does not authenticate its source.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Groth16Contract {
    relation: RelationSubject,
    verifier: VerifyingKey,
    required: BTreeSet<Premise>,
}
impl Groth16Contract {
    pub fn new(
        relation: RelationSubject,
        expected_vk: VerifyingKey,
        required: impl IntoIterator<Item = Premise>,
    ) -> Result<Self> {
        if relation.relation().n_public() != expected_vk.n_public() {
            return Err(fail(FailureKind::Mismatch, "ingress-public-layout"));
        }
        let required: BTreeSet<_> = required.into_iter().collect();
        if required.iter().any(|p| !GROTH16_PREMISES.contains(p)) {
            return Err(fail(FailureKind::Unavailable, "ingress-groth16-premise"));
        }
        Ok(Self {
            relation,
            verifier: expected_vk,
            required,
        })
    }
    pub fn relation(&self) -> &RelationSubject {
        &self.relation
    }
    pub fn verifier(&self) -> &VerifyingKey {
        &self.verifier
    }
    pub fn required_premises(&self) -> &BTreeSet<Premise> {
        &self.required
    }
    /// Re-evaluated for each use. This report records caller acceptance, never
    /// upgrades a missing predicate to a checked fact.
    pub fn authorize(&self, accepted: &AcceptedPremises) -> Result<Vec<EvidenceStatus>> {
        if self.required.iter().any(|p| !accepted.contains(*p)) {
            return Err(fail(
                FailureKind::UnapprovedPremise,
                "ingress-required-premise",
            ));
        }
        Ok(GROTH16_PREMISES
            .iter()
            .map(|p| {
                if accepted.contains(*p) {
                    EvidenceStatus::AcceptedPremise(*p)
                } else {
                    EvidenceStatus::UnacceptedPremise(*p)
                }
            })
            .collect())
    }

    pub fn check_key(
        &self,
        candidate_relation: &[u8],
        zkey: &[u8],
        limits: &Limits,
    ) -> Result<CheckedGroth16Key> {
        let relation = RelationSubject::from_normalized(candidate_relation)?;
        if relation != self.relation {
            return Err(fail(FailureKind::Mismatch, "ingress-relation-mismatch"));
        }
        let decoded =
            snarkjs::decode_zkey(zkey, limits, &crate::groth16::policy()).map_err(import_error)?;
        let key = ProverKey::new(&decoded, &self.verifier, relation.relation())
            .map_err(|e| fail(FailureKind::Mismatch, e.code))?;
        Ok(CheckedGroth16Key {
            relation,
            verifier: self.verifier.clone(),
            key,
            captured: zkey.into(),
        })
    }

    /// Binds the exact public statement and actual witness, not a witness hash.
    /// Satisfaction is deliberately not claimed here: the generated PIR guard
    /// remains responsible for evaluating A*w * B*w = C*w.
    pub fn check_assignment(
        &self,
        statement: &Statement,
        wtns: &[u8],
        limits: &Limits,
    ) -> Result<CheckedAssignment> {
        let witness =
            snarkjs::decode_wtns(wtns, limits, &crate::groth16::policy()).map_err(import_error)?;
        self.bind_assignment(statement, witness)
    }
    /// Typed callers have already crossed the scalar decoder boundary.
    pub fn bind_assignment(
        &self,
        statement: &Statement,
        witness: Witness,
    ) -> Result<CheckedAssignment> {
        if statement.0.len() != self.verifier.n_public() {
            return Err(fail(FailureKind::Mismatch, "ingress-public-layout"));
        }
        if witness.0.len() != self.relation.relation().columns()
            || witness.0.first() != Some(&ark_bn254::Fr::from(1))
        {
            return Err(fail(FailureKind::Mismatch, "ingress-assignment-layout"));
        }
        if witness.0[1..1 + statement.0.len()] != *statement.0 {
            return Err(fail(FailureKind::Mismatch, "ingress-statement-mismatch"));
        }
        Ok(CheckedAssignment {
            relation: self.relation.clone(),
            statement: statement.clone(),
            witness,
        })
    }

    pub fn bind(
        &self,
        protocol: &PreparedProtocol,
        statement: Statement,
        context: &[u8],
    ) -> Result<CheckedInvocation> {
        // A cached origin digest alone cannot establish exact descriptor equality.
        let relation = protocol.relation().ok_or_else(|| {
            fail(
                FailureKind::Unavailable,
                "ingress-compiled-descriptor-unavailable",
            )
        })?;
        if relation.canonical_descriptor() != self.relation.descriptor() {
            return Err(fail(
                FailureKind::Mismatch,
                "ingress-compiled-relation-mismatch",
            ));
        }
        if context.is_empty() {
            return Err(fail(FailureKind::Malformed, "groth16-relation-context"));
        }
        if context.len() > 4096 {
            return Err(fail(FailureKind::Resource, "groth16-relation-context"));
        }
        let invocation = protocol
            .bind(self.verifier.clone(), statement.clone(), context)
            .map_err(|e| fail(FailureKind::Mismatch, e.code))?;
        Ok(CheckedInvocation {
            contract: self.clone(),
            statement,
            invocation,
        })
    }
}

/// Private successful constructor, retaining the actual ProverKey consumed by
/// execution and exact imported bytes. Query changes cannot mutate this value.
#[derive(Clone, Debug)]
pub struct CheckedGroth16Key {
    relation: RelationSubject,
    verifier: VerifyingKey,
    key: ProverKey,
    captured: Arc<[u8]>,
}
impl CheckedGroth16Key {
    pub fn relation(&self) -> &RelationSubject {
        &self.relation
    }
    /// Immutable original encoding for audit/replay of imported section data.
    /// This intentionally retains input bytes in addition to decoded query data.
    pub fn captured_zkey(&self) -> &[u8] {
        &self.captured
    }
    pub fn evidence(&self) -> Vec<EvidenceStatus> {
        let mut facts = vec![
            EvidenceStatus::Checked(Predicate::Groth16RelationLayoutAndAB),
            EvidenceStatus::Checked(Predicate::ExpectedVerificationKey),
            EvidenceStatus::Checked(Predicate::KeyShapeAndDomain),
        ];
        facts.extend(GROTH16_PREMISES.map(EvidenceStatus::MissingProof));
        facts
    }
    pub fn check_applicability(&self, contract: &Groth16Contract) -> Result<()> {
        if self.relation != contract.relation || self.verifier != contract.verifier {
            return Err(fail(FailureKind::Mismatch, "ingress-key-subject"));
        }
        Ok(())
    }
}
#[derive(Clone, Debug)]
pub struct CheckedAssignment {
    relation: RelationSubject,
    statement: Statement,
    witness: Witness,
}
impl CheckedAssignment {
    pub fn statement(&self) -> &Statement {
        &self.statement
    }
    pub fn witness(&self) -> &Witness {
        &self.witness
    }
    pub fn evidence(&self) -> EvidenceStatus {
        EvidenceStatus::Checked(Predicate::AssignmentLayoutAndPublicPrefix)
    }
    pub fn check_applicability(
        &self,
        relation: &RelationSubject,
        statement: &Statement,
    ) -> Result<()> {
        if &self.relation != relation || &self.statement != statement {
            return Err(fail(FailureKind::Mismatch, "ingress-assignment-subject"));
        }
        Ok(())
    }
}
#[derive(Clone, Debug)]
pub struct CheckedInvocation {
    contract: Groth16Contract,
    statement: Statement,
    invocation: Invocation,
}
impl CheckedInvocation {
    pub fn evidence(&self, accepted: &AcceptedPremises) -> Result<Vec<EvidenceStatus>> {
        self.contract.authorize(accepted)
    }
    pub fn prove(
        &self,
        key: &CheckedGroth16Key,
        assignment: &CheckedAssignment,
        accepted: &AcceptedPremises,
        randomness: Randomness,
    ) -> Result<ProducedProof> {
        key.check_applicability(&self.contract)?;
        assignment.check_applicability(&self.contract.relation, &self.statement)?;
        self.evidence(accepted)?;
        self.invocation
            .prove(&key.key, &assignment.witness, randomness)
            .map_err(execution_error)
    }
    pub fn verify_artifact(&self, bytes: &[u8], accepted: &AcceptedPremises) -> Result<()> {
        self.evidence(accepted)?;
        self.invocation
            .verify_artifact(bytes)
            .map_err(execution_error)
    }
}
