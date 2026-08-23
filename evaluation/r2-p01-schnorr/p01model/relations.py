"""Finite Schnorr relation, grounding, and theorem-boundary probes for P01.

This module is executable falsification evidence for one frozen finite profile.
It deliberately separates five judgments that are easy to conflate:

* relation, instance, and witness-assignment admission;
* relation satisfaction by one admitted witness assignment;
* the closed shape and value law of a proposed execution-grounding bridge;
* finite special-soundness and special-HVZK algebra; and
* applicability of a general security theorem.

Only the first four are executable here.  In particular, exhaustive checks for
``p=23, q=11, g=2`` are not proofs for an unbounded protocol family and are not
ROM, QROM, knowledge-soundness, identification, or signature results.

``QualifiedExecutionStatement`` is the intentionally narrow coupling point for
the execution evaluator.  It can carry exact replay-qualified identifiers and
the statement event, but this freely constructible data class is not itself a
qualification capability.  Once ``execution.py`` exists, a public grounding
judgment must replay a real ``QualifiedExecution``, derive this adapter, and
then invoke the shape checker here.  Raw adapters and raw trace values are not
positive execution-grounding evidence.
"""

from __future__ import annotations

from collections import Counter
from dataclasses import dataclass, replace
from enum import Enum
import re
from typing import Any, Mapping

from .semantic import (
    HONEST_WITNESS_SOURCE,
    STATEMENT,
    AlgebraProfile,
    ConversationCore,
    HonestProverContract,
    admit_algebra,
    admit_core,
    admit_honest_prover_contract,
    group_domain_id,
    group_parameters_id,
    honest_witness_precondition_contract_id,
    scalar_domain_id,
)
from .terms import (
    Outcome,
    Result,
    TermEncodingError,
    affirmative,
    result,
    semantic_id,
)


_CONTENT_ID = re.compile(r"sha256:[0-9a-f]{64}\Z")
FINITE_PROFILE = AlgebraProfile(p=23, q=11, generator=2, challenge_size=8)


def _closed_id(value: Any) -> bool:
    return isinstance(value, str) and _CONTENT_ID.fullmatch(value) is not None


def _bounded_label(value: Any, limit: int = 256) -> bool:
    if not isinstance(value, str) or not value:
        return False
    try:
        return len(value.encode("utf-8")) <= limit
    except UnicodeEncodeError:
        return False


def _safe_identity(value: Any) -> str:
    """Return a diagnostic subject without trusting an unchecked term."""

    try:
        identity = value.identity
    except (AttributeError, TermEncodingError, TypeError, ValueError):
        return ""
    return identity if _closed_id(identity) else ""


def _safe_public_reference(value: Any) -> str:
    """Return a non-secret reference only after its closed shape permits it."""

    try:
        reference = value.public_reference
    except (AttributeError, TermEncodingError, TypeError, ValueError):
        return ""
    return reference if _closed_id(reference) else ""


@dataclass(frozen=True)
class SchnorrRelation:
    """The typed prime-order discrete-log relation used by P01."""

    group_parameters_id: str
    statement_domain_id: str
    witness_domain_id: str
    equation: str = "statement=generator^witness mod p"
    relation_version: str = "SchnorrDiscreteLogRelation.v1"

    def term(self) -> dict[str, str]:
        return {
            "relation_version": self.relation_version,
            "group_parameters_id": self.group_parameters_id,
            "statement_domain_id": self.statement_domain_id,
            "witness_domain_id": self.witness_domain_id,
            "equation": self.equation,
        }

    @property
    def identity(self) -> str:
        return semantic_id("p01.schnorr-relation.v1", self.term())


def canonical_schnorr_relation(profile: AlgebraProfile) -> SchnorrRelation:
    return SchnorrRelation(
        group_parameters_id=group_parameters_id(profile),
        statement_domain_id=group_domain_id(profile),
        witness_domain_id=scalar_domain_id(profile),
    )


def admit_relation(
    relation: SchnorrRelation,
    profile: AlgebraProfile,
) -> Result:
    algebra_result = admit_algebra(profile)
    if algebra_result.outcome is not Outcome.AFFIRMATIVE:
        return algebra_result
    if not isinstance(relation, SchnorrRelation):
        return result(
            Outcome.MALFORMED,
            "relations:relation-admission",
            "P01-REL-001",
            "relation has the wrong type",
        )
    if (
        not _closed_id(relation.group_parameters_id)
        or not _closed_id(relation.statement_domain_id)
        or not _closed_id(relation.witness_domain_id)
        or not _bounded_label(relation.equation)
        or not _bounded_label(relation.relation_version, 128)
    ):
        return result(
            Outcome.MALFORMED,
            "relations:relation-admission:shape",
            "P01-REL-003",
            "relation fields are outside the closed typed grammar",
            subject=_safe_identity(relation),
        )
    expected = canonical_schnorr_relation(profile)
    if relation != expected:
        outcome = (
            Outcome.MISMATCH
            if relation.group_parameters_id != group_parameters_id(profile)
            else Outcome.SEMANTIC_NEGATIVE
        )
        return result(
            outcome,
            "relations:relation-admission",
            "P01-REL-002",
            "relation is not the exact typed Schnorr relation for this profile",
            subject=_safe_identity(relation),
            expected_relation_id=expected.identity,
        )
    return affirmative(
        "relations:relation-admission",
        "P01-REL-OK",
        "prime-order Schnorr relation is admitted",
        subject=relation.identity,
        group_parameters_id=group_parameters_id(profile),
    )


@dataclass(frozen=True)
class SchnorrRelationInstance:
    """One public Schnorr statement, without a witness-possession claim."""

    relation_id: str
    public_statement: int

    def term(self) -> dict[str, Any]:
        return {
            "relation_id": self.relation_id,
            "public_statement": self.public_statement,
        }

    @property
    def identity(self) -> str:
        return semantic_id("p01.schnorr-relation-instance.v1", self.term())


def admit_instance(
    instance: SchnorrRelationInstance,
    relation: SchnorrRelation,
    profile: AlgebraProfile,
) -> Result:
    relation_result = admit_relation(relation, profile)
    if relation_result.outcome is not Outcome.AFFIRMATIVE:
        return relation_result
    if not isinstance(instance, SchnorrRelationInstance):
        return result(
            Outcome.MALFORMED,
            "relations:instance-admission",
            "P01-INS-001",
            "relation instance has the wrong type",
        )
    if (
        not _closed_id(instance.relation_id)
        or not isinstance(instance.public_statement, int)
        or isinstance(instance.public_statement, bool)
    ):
        return result(
            Outcome.MALFORMED,
            "relations:instance-admission:shape",
            "P01-INS-004",
            "relation instance fields are outside the closed typed grammar",
            subject=_safe_identity(instance),
        )
    if instance.relation_id != relation.identity:
        return result(
            Outcome.MISMATCH,
            "relations:instance-admission:relation",
            "P01-INS-002",
            "relation instance names a different relation",
            subject=_safe_identity(instance),
        )
    if not profile.valid_group_element(instance.public_statement):
        return result(
            Outcome.SEMANTIC_NEGATIVE,
            "relations:instance-admission:statement-domain",
            "P01-INS-003",
            "public statement is not in the declared prime-order subgroup",
            subject=_safe_identity(instance),
        )
    return affirmative(
        "relations:instance-admission",
        "P01-INS-OK",
        "Schnorr relation instance is admitted without asserting witness possession or satisfaction",
        subject=instance.identity,
        relation_id=relation.identity,
    )


@dataclass(frozen=True)
class SchnorrWitnessAssignment:
    """Occurrence-local secret input; deliberately has no content identity."""

    instance_id: str
    occurrence: str
    secret_scalar: int

    @property
    def public_reference(self) -> str:
        """A non-secret occurrence handle, not an identity of the secret value."""

        return semantic_id(
            "p01.schnorr-witness-occurrence.v1",
            {"instance_id": self.instance_id, "occurrence": self.occurrence},
        )


def admit_witness_assignment(
    witness: SchnorrWitnessAssignment,
    instance: SchnorrRelationInstance,
    relation: SchnorrRelation,
    profile: AlgebraProfile,
) -> Result:
    instance_result = admit_instance(instance, relation, profile)
    if instance_result.outcome is not Outcome.AFFIRMATIVE:
        return instance_result
    if not isinstance(witness, SchnorrWitnessAssignment):
        return result(
            Outcome.MALFORMED,
            "relations:witness-admission",
            "P01-WIT-001",
            "witness assignment has the wrong type",
        )
    if (
        not _closed_id(witness.instance_id)
        or not isinstance(witness.secret_scalar, int)
        or isinstance(witness.secret_scalar, bool)
    ):
        return result(
            Outcome.MALFORMED,
            "relations:witness-admission:shape",
            "P01-WIT-005",
            "witness assignment fields are outside the closed typed grammar",
            subject=_safe_public_reference(witness),
        )
    if witness.instance_id != instance.identity:
        return result(
            Outcome.MISMATCH,
            "relations:witness-admission:instance",
            "P01-WIT-002",
            "witness assignment names a different relation instance",
            subject=_safe_identity(instance),
        )
    if not _bounded_label(witness.occurrence):
        return result(
            Outcome.MALFORMED,
            "relations:witness-admission:occurrence",
            "P01-WIT-003",
            "witness occurrence is empty or outside the bounded vocabulary",
            subject=_safe_identity(instance),
        )
    if not profile.valid_scalar(witness.secret_scalar):
        return result(
            Outcome.SEMANTIC_NEGATIVE,
            "relations:witness-admission:scalar-domain",
            "P01-WIT-004",
            "witness is not a scalar modulo q",
            subject=instance.identity,
        )
    return affirmative(
        "relations:witness-admission",
        "P01-WIT-OK",
        "occurrence-local witness assignment is admitted without yet asserting satisfaction",
        subject=witness.public_reference,
        instance_id=instance.identity,
    )


def check_relation_satisfaction(
    witness: SchnorrWitnessAssignment,
    instance: SchnorrRelationInstance,
    relation: SchnorrRelation,
    profile: AlgebraProfile,
) -> Result:
    witness_result = admit_witness_assignment(witness, instance, relation, profile)
    if witness_result.outcome is not Outcome.AFFIRMATIVE:
        return witness_result
    if pow(profile.generator, witness.secret_scalar, profile.p) != instance.public_statement:
        return result(
            Outcome.SEMANTIC_NEGATIVE,
            "relations:satisfaction",
            "P01-SAT-001",
            "admitted witness assignment does not satisfy the Schnorr relation",
            subject=instance.identity,
            witness_occurrence=witness.public_reference,
        )
    return affirmative(
        "relations:satisfaction",
        "P01-SAT-OK",
        "admitted witness assignment satisfies the finite Schnorr equation",
        subject=instance.identity,
        witness_occurrence=witness.public_reference,
    )


@dataclass(frozen=True)
class RelationHonestProverCorrespondence:
    """Typed Relation -> Core Statement -> honest witness-law bridge."""

    relation_id: str
    core_id: str
    honest_prover_contract_id: str
    statement_occurrence: str
    statement_domain_id: str
    witness_source: str
    witness_domain_id: str
    witness_precondition_contract_id: str
    law: str = "ExactSchnorrStatementWitnessCorrespondence.v1"

    def term(self) -> dict[str, str]:
        return {
            "relation_id": self.relation_id,
            "core_id": self.core_id,
            "honest_prover_contract_id": self.honest_prover_contract_id,
            "statement_occurrence": self.statement_occurrence,
            "statement_domain_id": self.statement_domain_id,
            "witness_source": self.witness_source,
            "witness_domain_id": self.witness_domain_id,
            "witness_precondition_contract_id": (
                self.witness_precondition_contract_id
            ),
            "law": self.law,
        }

    @property
    def identity(self) -> str:
        return semantic_id(
            "p01.relation-honest-prover-correspondence.v1", self.term()
        )


def relation_honest_prover_candidate(
    relation: SchnorrRelation,
    core: ConversationCore,
    honest_contract: HonestProverContract,
    profile: AlgebraProfile,
) -> RelationHonestProverCorrespondence:
    """Construct the sole P01 correspondence candidate after admission."""

    statement_contract = core.contract_for(STATEMENT)
    witness_inputs = tuple(
        local
        for local in honest_contract.local_inputs
        if local.purpose == "RelationWitness"
    )
    if len(witness_inputs) != 1:
        raise ValueError("honest contract has no unique relation-witness input")
    witness_input = witness_inputs[0]
    return RelationHonestProverCorrespondence(
        relation_id=relation.identity,
        core_id=core.identity,
        honest_prover_contract_id=honest_contract.identity,
        statement_occurrence=STATEMENT,
        statement_domain_id=statement_contract.value_domain_id,
        witness_source=witness_input.name,
        witness_domain_id=witness_input.value_domain_id,
        witness_precondition_contract_id=(
            honest_contract.witness_precondition_contract_id
        ),
    )


def check_relation_honest_prover_correspondence(
    correspondence: RelationHonestProverCorrespondence,
    relation: SchnorrRelation,
    core: ConversationCore,
    honest_contract: HonestProverContract,
    profile: AlgebraProfile,
) -> Result:
    """Check correspondence without merging admission or satisfaction."""

    relation_result = admit_relation(relation, profile)
    if relation_result.outcome is not Outcome.AFFIRMATIVE:
        return relation_result
    core_result = admit_core(core, profile)
    if core_result.outcome is not Outcome.AFFIRMATIVE:
        return core_result
    honest_result = admit_honest_prover_contract(
        honest_contract, core, profile
    )
    if honest_result.outcome is not Outcome.AFFIRMATIVE:
        return honest_result
    if not isinstance(correspondence, RelationHonestProverCorrespondence):
        return result(
            Outcome.MALFORMED,
            "relations:honest-prover-correspondence",
            "P01-RHC-001",
            "relation/honest-prover correspondence has the wrong type",
        )
    fields = (
        correspondence.relation_id,
        correspondence.core_id,
        correspondence.honest_prover_contract_id,
        correspondence.statement_domain_id,
        correspondence.witness_domain_id,
        correspondence.witness_precondition_contract_id,
    )
    if (
        not all(_closed_id(value) for value in fields)
        or not _bounded_label(correspondence.statement_occurrence)
        or not _bounded_label(correspondence.witness_source)
        or not _bounded_label(correspondence.law, 128)
    ):
        return result(
            Outcome.MALFORMED,
            "relations:honest-prover-correspondence:shape",
            "P01-RHC-002",
            "correspondence fields are outside the closed typed grammar",
            subject=_safe_identity(correspondence),
        )
    try:
        expected = relation_honest_prover_candidate(
            relation, core, honest_contract, profile
        )
    except (AttributeError, KeyError, TypeError, ValueError) as error:
        return result(
            Outcome.CHECKER_FAILURE,
            "relations:honest-prover-correspondence:construction",
            "P01-RHC-003",
            f"admitted operands did not yield a correspondence: {error}",
            subject=_safe_identity(correspondence),
        )
    if (
        correspondence != expected
        or correspondence.statement_occurrence != STATEMENT
        or correspondence.statement_domain_id != relation.statement_domain_id
        or correspondence.witness_source != HONEST_WITNESS_SOURCE
        or correspondence.witness_domain_id != relation.witness_domain_id
        or correspondence.witness_precondition_contract_id
        != honest_witness_precondition_contract_id(profile)
    ):
        return result(
            Outcome.MISMATCH,
            "relations:honest-prover-correspondence:exact-law",
            "P01-RHC-004",
            "Relation, Core Statement, or honest witness law does not correspond exactly",
            subject=_safe_identity(correspondence),
            expected_correspondence_id=expected.identity,
        )
    return affirmative(
        "relations:honest-prover-correspondence",
        "P01-RHC-OK",
        "the admitted relation is the exact precondition of the admitted Schnorr honest prover",
        subject=correspondence.identity,
        relation_id=relation.identity,
        core_id=core.identity,
        honest_prover_contract_id=honest_contract.identity,
        non_claim="not witness satisfaction, completeness, acceptance, or security",
    )


@dataclass(frozen=True)
class QualifiedExecutionStatement:
    """Closed statement-event adapter shape for the execution evaluator.

    This adapter is intentionally independent of the eventual execution record
    class.  The execution evaluator remains responsible for constructing it
    from a replayed qualification, not from caller-supplied trace syntax.  Its
    digest-shaped fields do not independently prove that replay occurred.
    """

    qualification_id: str
    execution_id: str
    protocol_id: str
    core_id: str
    evaluation_profile_id: str
    occurrence: str
    value: int
    source_event_id: str

    def term(self) -> dict[str, Any]:
        return {
            "qualification_id": self.qualification_id,
            "execution_id": self.execution_id,
            "protocol_id": self.protocol_id,
            "core_id": self.core_id,
            "evaluation_profile_id": self.evaluation_profile_id,
            "occurrence": self.occurrence,
            "value": self.value,
            "source_event_id": self.source_event_id,
        }

    @property
    def identity(self) -> str:
        return semantic_id("p01.qualified-execution-statement.v1", self.term())


@dataclass(frozen=True)
class RelationExecutionGrounding:
    """Exact relation-instance -> statement-event -> execution bridge."""

    relation_id: str
    instance_id: str
    statement_occurrence_id: str
    qualification_id: str
    law: str = "ExactSameDomainStatementEquality.v1"

    def term(self) -> dict[str, str]:
        return {
            "relation_id": self.relation_id,
            "instance_id": self.instance_id,
            "statement_occurrence_id": self.statement_occurrence_id,
            "qualification_id": self.qualification_id,
            "law": self.law,
        }

    @property
    def identity(self) -> str:
        return semantic_id("p01.relation-execution-grounding.v1", self.term())


def grounding_candidate(
    instance: SchnorrRelationInstance,
    relation: SchnorrRelation,
    statement: QualifiedExecutionStatement,
) -> RelationExecutionGrounding:
    """Form a candidate only; ``check_grounding_shape`` checks no authority."""

    return RelationExecutionGrounding(
        relation_id=relation.identity,
        instance_id=instance.identity,
        statement_occurrence_id=statement.identity,
        qualification_id=statement.qualification_id,
    )


def _check_statement_adapter_shape(
    statement: QualifiedExecutionStatement,
    profile: AlgebraProfile,
) -> Result:
    if not isinstance(statement, QualifiedExecutionStatement):
        return result(
            Outcome.MALFORMED,
            "relations:execution-grounding-shape:statement",
            "P01-GRD-001",
            "execution statement adapter has the wrong type",
        )
    id_fields = (
        statement.qualification_id,
        statement.execution_id,
        statement.protocol_id,
        statement.core_id,
        statement.evaluation_profile_id,
        statement.source_event_id,
    )
    if (
        not all(_closed_id(value) for value in id_fields)
        or not isinstance(statement.occurrence, str)
        or not isinstance(statement.value, int)
        or isinstance(statement.value, bool)
    ):
        return result(
            Outcome.MALFORMED,
            "relations:execution-grounding-shape:qualification",
            "P01-GRD-002",
            "execution statement adapter contains a malformed identity",
            subject=_safe_identity(statement),
        )
    if statement.evaluation_profile_id != profile.identity:
        return result(
            Outcome.MISMATCH,
            "relations:execution-grounding-shape:algebra",
            "P01-GRD-003",
            "statement adapter belongs to a different finite evaluation profile",
            subject=statement.identity,
        )
    if statement.occurrence != STATEMENT:
        return result(
            Outcome.MISMATCH,
            "relations:execution-grounding-shape:occurrence",
            "P01-GRD-004",
            "adapter event is not the exact Schnorr Statement occurrence",
            subject=statement.identity,
        )
    if not profile.valid_group_element(statement.value):
        return result(
            Outcome.SEMANTIC_NEGATIVE,
            "relations:execution-grounding-shape:statement-domain",
            "P01-GRD-005",
            "adapter Statement value is outside the prime-order subgroup",
            subject=statement.identity,
        )
    return affirmative(
        "relations:execution-grounding-shape:statement",
        "P01-GRD-STATEMENT-OK",
        "statement adapter has one well-typed Schnorr Statement occurrence shape",
        subject=statement.identity,
        non_claim="does not authenticate or replay an execution qualification",
    )


def check_grounding_shape(
    grounding: RelationExecutionGrounding,
    instance: SchnorrRelationInstance,
    relation: SchnorrRelation,
    statement: QualifiedExecutionStatement,
    profile: AlgebraProfile,
) -> Result:
    """Check bridge shape and value only, never execution qualification.

    A future execution-owned wrapper must requalify a real execution, derive
    ``statement`` itself, call this function, and mint the public grounding
    result only when both replay and this shape check affirm.
    """

    instance_result = admit_instance(instance, relation, profile)
    if instance_result.outcome is not Outcome.AFFIRMATIVE:
        return instance_result
    statement_result = _check_statement_adapter_shape(statement, profile)
    if statement_result.outcome is not Outcome.AFFIRMATIVE:
        return statement_result
    if not isinstance(grounding, RelationExecutionGrounding):
        return result(
            Outcome.MALFORMED,
            "relations:execution-grounding-shape",
            "P01-GRD-006",
            "grounding bridge has the wrong type",
        )
    if (
        not _closed_id(grounding.relation_id)
        or not _closed_id(grounding.instance_id)
        or not _closed_id(grounding.statement_occurrence_id)
        or not _closed_id(grounding.qualification_id)
        or not _bounded_label(grounding.law, 128)
    ):
        return result(
            Outcome.MALFORMED,
            "relations:execution-grounding-shape:closed-grammar",
            "P01-GRD-009",
            "grounding bridge fields are outside the closed typed grammar",
            subject=_safe_identity(grounding),
        )
    expected = grounding_candidate(instance, relation, statement)
    if grounding != expected:
        return result(
            Outcome.MISMATCH,
            "relations:execution-grounding-shape:exact-operands",
            "P01-GRD-007",
            "grounding bridge does not retain the exact relation, instance, statement, and qualification",
            subject=grounding.identity,
            expected_grounding_id=expected.identity,
        )
    if statement.value != instance.public_statement:
        return result(
            Outcome.MISMATCH,
            "relations:execution-grounding-shape:value",
            "P01-GRD-008",
            "adapter Statement differs from the relation-instance value",
            subject=grounding.identity,
            relation_instance_id=instance.identity,
            statement_occurrence_id=statement.identity,
        )
    return affirmative(
        "relations:execution-grounding-shape",
        "P01-GRD-SHAPE-OK",
        "candidate bridge has exact operands and same-domain Statement equality",
        subject=grounding.identity,
        relation_id=relation.identity,
        relation_instance_id=instance.identity,
        statement_occurrence_id=statement.identity,
        qualification_id=statement.qualification_id,
        execution_id=statement.execution_id,
        non_claim="does not authenticate or replay the named execution qualification",
    )


@dataclass(frozen=True)
class SchnorrTranscript:
    instance_id: str
    statement: int
    commitment: int
    challenge: int
    response: int

    def term(self) -> dict[str, Any]:
        return {
            "instance_id": self.instance_id,
            "statement": self.statement,
            "commitment": self.commitment,
            "challenge": self.challenge,
            "response": self.response,
        }

    @property
    def identity(self) -> str:
        return semantic_id("p01.schnorr-transcript.v1", self.term())


def honest_transcript(
    instance: SchnorrRelationInstance,
    witness_scalar: int,
    nonce: int,
    challenge: int,
    profile: AlgebraProfile,
) -> SchnorrTranscript:
    if not profile.valid_scalar(witness_scalar):
        raise ValueError("witness scalar is outside the declared domain")
    if not profile.valid_scalar(nonce):
        raise ValueError("nonce is outside the declared scalar domain")
    if not profile.valid_challenge(challenge):
        raise ValueError("challenge is outside the declared challenge domain")
    return SchnorrTranscript(
        instance_id=instance.identity,
        statement=instance.public_statement,
        commitment=pow(profile.generator, nonce, profile.p),
        challenge=challenge,
        response=(nonce + challenge * witness_scalar) % profile.q,
    )


def check_accepting_transcript(
    transcript: SchnorrTranscript,
    instance: SchnorrRelationInstance,
    relation: SchnorrRelation,
    profile: AlgebraProfile,
) -> Result:
    instance_result = admit_instance(instance, relation, profile)
    if instance_result.outcome is not Outcome.AFFIRMATIVE:
        return instance_result
    if not isinstance(transcript, SchnorrTranscript):
        return result(
            Outcome.MALFORMED,
            "analysis:finite-transcript",
            "P01-TRN-001",
            "transcript has the wrong type",
        )
    if (
        not _closed_id(transcript.instance_id)
        or any(
            not isinstance(value, int) or isinstance(value, bool)
            for value in (
                transcript.statement,
                transcript.commitment,
                transcript.challenge,
                transcript.response,
            )
        )
    ):
        return result(
            Outcome.MALFORMED,
            "analysis:finite-transcript:shape",
            "P01-TRN-009",
            "transcript fields are outside the closed typed grammar",
            subject=_safe_identity(transcript),
        )
    if transcript.instance_id != instance.identity:
        return result(
            Outcome.MISMATCH,
            "analysis:finite-transcript:instance",
            "P01-TRN-002",
            "transcript names a different relation instance",
            subject=_safe_identity(transcript),
        )
    if transcript.statement != instance.public_statement:
        return result(
            Outcome.MISMATCH,
            "analysis:finite-transcript:statement",
            "P01-TRN-003",
            "transcript Statement differs from the relation instance",
            subject=transcript.identity,
        )
    if not profile.valid_group_element(transcript.statement):
        return result(
            Outcome.SEMANTIC_NEGATIVE,
            "analysis:finite-transcript:statement-domain",
            "P01-TRN-004",
            "transcript Statement is outside the subgroup",
            subject=transcript.identity,
        )
    if not profile.valid_group_element(transcript.commitment):
        return result(
            Outcome.SEMANTIC_NEGATIVE,
            "analysis:finite-transcript:commitment-domain",
            "P01-TRN-005",
            "transcript commitment is outside the subgroup",
            subject=transcript.identity,
        )
    if not profile.valid_challenge(transcript.challenge):
        return result(
            Outcome.SEMANTIC_NEGATIVE,
            "analysis:finite-transcript:challenge-domain",
            "P01-TRN-006",
            "transcript challenge is outside the challenge set",
            subject=transcript.identity,
        )
    if not profile.valid_scalar(transcript.response):
        return result(
            Outcome.SEMANTIC_NEGATIVE,
            "analysis:finite-transcript:response-domain",
            "P01-TRN-007",
            "transcript response is outside the scalar domain",
            subject=transcript.identity,
        )
    left = pow(profile.generator, transcript.response, profile.p)
    right = (
        transcript.commitment
        * pow(transcript.statement, transcript.challenge, profile.p)
    ) % profile.p
    if left != right:
        return result(
            Outcome.SEMANTIC_NEGATIVE,
            "analysis:finite-transcript:verifier-equation",
            "P01-TRN-008",
            "transcript does not satisfy the Schnorr verifier equation",
            subject=transcript.identity,
        )
    return affirmative(
        "analysis:finite-transcript",
        "P01-TRN-OK",
        "finite transcript satisfies the Schnorr verifier equation",
        subject=transcript.identity,
    )


@dataclass(frozen=True)
class TranscriptFork:
    left: SchnorrTranscript
    right: SchnorrTranscript

    @property
    def identity(self) -> str:
        return semantic_id(
            "p01.schnorr-transcript-fork.v1",
            {"left": self.left.identity, "right": self.right.identity},
        )


@dataclass(frozen=True)
class FiniteForkExtraction:
    """Finite evaluator output; the scalar must not be persisted as an ID."""

    fork_id: str
    instance_id: str
    extracted_scalar: int


def extract_special_soundness_fork(
    fork: TranscriptFork,
    instance: SchnorrRelationInstance,
    relation: SchnorrRelation,
    profile: AlgebraProfile,
) -> FiniteForkExtraction | Result:
    """Apply the two-transcript Schnorr extractor after exact fork checks."""

    if not isinstance(fork, TranscriptFork):
        return result(
            Outcome.MALFORMED,
            "analysis:finite-special-soundness:fork",
            "P01-SS-001",
            "fork has the wrong type",
        )
    if not isinstance(fork.left, SchnorrTranscript) or not isinstance(
        fork.right, SchnorrTranscript
    ):
        return result(
            Outcome.MALFORMED,
            "analysis:finite-special-soundness:fork-shape",
            "P01-SS-009",
            "fork operands must be typed Schnorr transcripts",
            subject=_safe_identity(fork),
        )
    left_result = check_accepting_transcript(fork.left, instance, relation, profile)
    if left_result.outcome is not Outcome.AFFIRMATIVE:
        return result(
            left_result.outcome,
            "analysis:finite-special-soundness:left",
            "P01-SS-002",
            "left fork operand is not an accepting transcript",
            subject=_safe_identity(fork),
            operand_result=left_result.term(),
        )
    right_result = check_accepting_transcript(fork.right, instance, relation, profile)
    if right_result.outcome is not Outcome.AFFIRMATIVE:
        return result(
            right_result.outcome,
            "analysis:finite-special-soundness:right",
            "P01-SS-003",
            "right fork operand is not an accepting transcript",
            subject=_safe_identity(fork),
            operand_result=right_result.term(),
        )
    if fork.left.statement != fork.right.statement:
        return result(
            Outcome.MISMATCH,
            "analysis:finite-special-soundness:common-statement",
            "P01-SS-004",
            "fork transcripts do not share the exact Statement",
            subject=_safe_identity(fork),
        )
    if fork.left.commitment != fork.right.commitment:
        return result(
            Outcome.MISMATCH,
            "analysis:finite-special-soundness:common-first-message",
            "P01-SS-005",
            "fork transcripts do not share the exact first message",
            subject=_safe_identity(fork),
        )
    if fork.left.challenge == fork.right.challenge:
        return result(
            Outcome.SEMANTIC_NEGATIVE,
            "analysis:finite-special-soundness:distinct-challenges",
            "P01-SS-006",
            "special-soundness fork requires distinct challenges",
            subject=_safe_identity(fork),
        )
    denominator = (fork.left.challenge - fork.right.challenge) % profile.q
    if denominator == 0:
        return result(
            Outcome.SEMANTIC_NEGATIVE,
            "analysis:finite-special-soundness:invertibility",
            "P01-SS-007",
            "challenge difference is not invertible modulo q",
            subject=_safe_identity(fork),
        )
    extracted = (
        (fork.left.response - fork.right.response)
        * pow(denominator, -1, profile.q)
    ) % profile.q
    if pow(profile.generator, extracted, profile.p) != instance.public_statement:
        return result(
            Outcome.CHECKER_FAILURE,
            "analysis:finite-special-soundness:extraction",
            "P01-SS-008",
            "algebraic fork extraction did not satisfy the relation",
            subject=_safe_identity(fork),
        )
    return FiniteForkExtraction(fork.identity, instance.identity, extracted)


def check_special_soundness_fork(
    fork: TranscriptFork,
    instance: SchnorrRelationInstance,
    relation: SchnorrRelation,
    profile: AlgebraProfile,
) -> Result:
    extraction = extract_special_soundness_fork(fork, instance, relation, profile)
    if isinstance(extraction, Result):
        return extraction
    return affirmative(
        "analysis:finite-special-soundness",
        "P01-SS-OK",
        "two accepting finite transcripts with one first message and distinct challenges yield a satisfying scalar",
        subject=extraction.fork_id,
        instance_id=extraction.instance_id,
        extracted_scalar=extraction.extracted_scalar,
        scope="one finite transcript pair; no strategy or theorem quantification",
    )


def _require_finite_profile(profile: AlgebraProfile, boundary: str) -> Result | None:
    algebra_result = admit_algebra(profile)
    if algebra_result.outcome is not Outcome.AFFIRMATIVE:
        return algebra_result
    if profile != FINITE_PROFILE:
        return result(
            Outcome.UNSUPPORTED,
            boundary,
            "P01-FIN-001",
            "exhaustive evaluator is pinned to p=23, q=11, g=2, C={0,...,7}",
            subject=profile.identity,
            supported_profile_id=FINITE_PROFILE.identity,
        )
    return None


def exhaustive_special_soundness(
    profile: AlgebraProfile = FINITE_PROFILE,
) -> Result:
    """Enumerate every accepted fork in the frozen scalar parameterization.

    Every subgroup Statement and commitment has a unique scalar exponent in
    this prime-order cyclic group.  Therefore enumerating all ``x`` and nonce
    values, then every unordered distinct challenge pair, covers all accepting
    transcript forks for this profile without treating finite coverage as a
    general theorem.
    """

    profile_failure = _require_finite_profile(
        profile, "analysis:finite-special-soundness:exhaustive"
    )
    if profile_failure is not None:
        return profile_failure
    relation = canonical_schnorr_relation(profile)
    fork_count = 0
    accepting_transcript_count = 0
    for secret in range(profile.q):
        instance = SchnorrRelationInstance(
            relation.identity,
            pow(profile.generator, secret, profile.p),
        )
        for nonce in range(profile.q):
            transcripts = tuple(
                honest_transcript(instance, secret, nonce, challenge, profile)
                for challenge in range(profile.challenge_size)
            )
            accepting_transcript_count += len(transcripts)
            for left_index, left in enumerate(transcripts):
                for right in transcripts[left_index + 1 :]:
                    extraction = extract_special_soundness_fork(
                        TranscriptFork(left, right), instance, relation, profile
                    )
                    if isinstance(extraction, Result):
                        return result(
                            Outcome.CHECKER_FAILURE,
                            "analysis:finite-special-soundness:exhaustive",
                            "P01-SS-ENUM-001",
                            "an exhaustively generated accepting fork failed extraction",
                            subject=profile.identity,
                            secret=secret,
                            nonce=nonce,
                            left_challenge=left.challenge,
                            right_challenge=right.challenge,
                            failure=extraction.term(),
                        )
                    if extraction.extracted_scalar != secret:
                        return result(
                            Outcome.CHECKER_FAILURE,
                            "analysis:finite-special-soundness:exhaustive",
                            "P01-SS-ENUM-002",
                            "finite extractor returned a different scalar",
                            subject=profile.identity,
                            expected_scalar=secret,
                            actual_scalar=extraction.extracted_scalar,
                        )
                    fork_count += 1
    expected_forks = (
        profile.q
        * profile.q
        * profile.challenge_size
        * (profile.challenge_size - 1)
        // 2
    )
    if fork_count != expected_forks:
        return result(
            Outcome.CHECKER_FAILURE,
            "analysis:finite-special-soundness:exhaustive",
            "P01-SS-ENUM-003",
            "enumeration cardinality differs from the closed coverage formula",
            subject=profile.identity,
            expected=expected_forks,
            actual=fork_count,
        )
    return affirmative(
        "analysis:finite-special-soundness:exhaustive",
        "P01-SS-ENUM-OK",
        "all finite accepting forks extract the unique enumerated witness scalar",
        subject=profile.identity,
        statement_scalars=profile.q,
        nonce_scalars=profile.q,
        challenge_values=profile.challenge_size,
        accepting_transcripts=accepting_transcript_count,
        unordered_distinct_challenge_forks=fork_count,
        coverage="all x, all nonces, and all unordered distinct challenge pairs in the frozen profile",
        non_claim="not a general special-soundness theorem or knowledge extractor",
    )


def exhaustive_shvzk_distribution_equality(
    profile: AlgebraProfile = FINITE_PROFILE,
) -> Result:
    """Compare exact real and challenge-conditioned simulator distributions."""

    profile_failure = _require_finite_profile(
        profile, "analysis:finite-shvzk:exhaustive"
    )
    if profile_failure is not None:
        return profile_failure
    compared_distributions = 0
    samples_per_side = 0
    for secret in range(profile.q):
        statement = pow(profile.generator, secret, profile.p)
        for challenge in range(profile.challenge_size):
            real: Counter[tuple[int, int, int]] = Counter()
            simulated: Counter[tuple[int, int, int]] = Counter()
            for nonce in range(profile.q):
                commitment = pow(profile.generator, nonce, profile.p)
                response = (nonce + challenge * secret) % profile.q
                real[(commitment, challenge, response)] += 1
            for response in range(profile.q):
                statement_power = pow(statement, challenge, profile.p)
                commitment = (
                    pow(profile.generator, response, profile.p)
                    * pow(statement_power, -1, profile.p)
                ) % profile.p
                simulated[(commitment, challenge, response)] += 1
                left = pow(profile.generator, response, profile.p)
                right = commitment * statement_power % profile.p
                if left != right:
                    return result(
                        Outcome.CHECKER_FAILURE,
                        "analysis:finite-shvzk:simulator-acceptance",
                        "P01-SHVZK-001",
                        "challenge-conditioned simulator emitted a rejecting transcript",
                        subject=profile.identity,
                        secret=secret,
                        challenge=challenge,
                        response=response,
                    )
            if real != simulated:
                return result(
                    Outcome.SEMANTIC_NEGATIVE,
                    "analysis:finite-shvzk:distribution-equality",
                    "P01-SHVZK-002",
                    "real and challenge-conditioned simulator distributions differ",
                    subject=profile.identity,
                    secret=secret,
                    challenge=challenge,
                    real_support=len(real),
                    simulated_support=len(simulated),
                )
            compared_distributions += 1
            samples_per_side += profile.q
    return affirmative(
        "analysis:finite-shvzk:exhaustive",
        "P01-SHVZK-OK",
        "real and simulator transcript distributions are exactly equal for every finite Statement and fixed challenge",
        subject=profile.identity,
        statements=profile.q,
        challenges_per_statement=profile.challenge_size,
        compared_conditional_distributions=compared_distributions,
        samples_per_side=samples_per_side,
        simulator_inputs=("statement", "fixed challenge", "simulator randomness"),
        simulator_omits="witness",
        non_claim="not malicious-verifier ZK, a general SHVZK theorem, or ROM/QROM simulation",
    )


class ApplicabilityClaim(str, Enum):
    FINITE_SPECIAL_SOUNDNESS_ALGEBRA = "FiniteSpecialSoundnessAlgebra"
    FINITE_SHVZK_DISTRIBUTION = "FiniteSHVZKDistribution"
    GENERAL_SPECIAL_SOUNDNESS = "GeneralSpecialSoundnessTheorem"
    GENERAL_SHVZK = "GeneralSpecialHVZKTheorem"
    GENERAL_HVZK = "GeneralHVZKTheorem"
    KNOWLEDGE_SOUNDNESS = "KnowledgeSoundness"
    FIAT_SHAMIR_ROM = "FiatShamirROM"
    FIAT_SHAMIR_QROM = "FiatShamirQROM"


def probe_analysis_applicability(
    claim: ApplicabilityClaim,
    profile: AlgebraProfile = FINITE_PROFILE,
) -> Result:
    """Answer finite questions and refuse unsupported theorem promotions."""

    if not isinstance(claim, ApplicabilityClaim):
        return result(
            Outcome.MALFORMED,
            "analysis:applicability",
            "P01-APP-001",
            "analysis applicability claim is outside the closed vocabulary",
        )
    profile_result = admit_algebra(profile)
    if profile_result.outcome is not Outcome.AFFIRMATIVE:
        return profile_result
    if claim is ApplicabilityClaim.FINITE_SPECIAL_SOUNDNESS_ALGEBRA:
        return exhaustive_special_soundness(profile)
    if claim is ApplicabilityClaim.FINITE_SHVZK_DISTRIBUTION:
        return exhaustive_shvzk_distribution_equality(profile)

    requirements: Mapping[ApplicabilityClaim, tuple[str, str, str]] = {
        ApplicabilityClaim.GENERAL_SPECIAL_SOUNDNESS: (
            "P01-APP-101",
            "finite enumeration cannot mint a general special-soundness theorem",
            "authenticated theorem capability with exact protocol/relation correspondence",
        ),
        ApplicabilityClaim.GENERAL_SHVZK: (
            "P01-APP-102",
            "finite challenge-conditioned equality cannot mint a general special-HVZK theorem",
            "challenge-conditioned simulator theorem over the declared protocol family",
        ),
        ApplicabilityClaim.GENERAL_HVZK: (
            "P01-APP-103",
            "SHVZK evidence is not silently retyped as an independently scoped HVZK result",
            "honest-verifier view definition and exact joint-distribution theorem",
        ),
        ApplicabilityClaim.KNOWLEDGE_SOUNDNESS: (
            "P01-APP-104",
            "a direct two-transcript extractor is not a strategy-level proof-of-knowledge extractor",
            "adversarial strategy, rewinding/access rights, success threshold, extractor, and quantitative bound",
        ),
        ApplicabilityClaim.FIAT_SHAMIR_ROM: (
            "P01-APP-105",
            "finite transcript algebra does not establish a Fiat-Shamir ROM theorem",
            "exact ROM theorem instance, oracle interface, adversary map, correspondence, and loss transformer",
        ),
        ApplicabilityClaim.FIAT_SHAMIR_QROM: (
            "P01-APP-106",
            "classical finite transcript algebra does not establish a Fiat-Shamir QROM theorem",
            "exact QROM theorem instance, quantum query access, measure/reprogram rights, adversary map, and loss transformer",
        ),
    }
    code, detail, missing = requirements[claim]
    return result(
        Outcome.REFUSED,
        f"analysis:applicability:{claim.value}",
        code,
        detail,
        subject=profile.identity,
        available_evidence=(
            ApplicabilityClaim.FINITE_SPECIAL_SOUNDNESS_ALGEBRA.value,
            ApplicabilityClaim.FINITE_SHVZK_DISTRIBUTION.value,
        ),
        missing_capability=missing,
        non_promotion_law="finite evidence cannot author theorem applicability",
    )


def applicability_refusal_matrix(
    profile: AlgebraProfile = FINITE_PROFILE,
) -> dict[str, Result]:
    return {
        claim.value: probe_analysis_applicability(claim, profile)
        for claim in ApplicabilityClaim
    }


def _synthetic_statement(
    profile: AlgebraProfile,
    value: int,
    *,
    salt: str,
) -> QualifiedExecutionStatement:
    """Self-check fixture only; production evidence must come from execution.py."""

    return QualifiedExecutionStatement(
        qualification_id=semantic_id("p01.self-check.qualification", salt),
        execution_id=semantic_id("p01.self-check.execution", salt),
        protocol_id=semantic_id("p01.self-check.protocol", salt),
        core_id=semantic_id("p01.self-check.core", salt),
        evaluation_profile_id=profile.identity,
        occurrence=STATEMENT,
        value=value,
        source_event_id=semantic_id("p01.self-check.statement-event", salt),
    )


def run_self_check() -> dict[str, Result]:
    """Exercise positive, negative, exhaustive, and refusal boundaries."""

    profile = FINITE_PROFILE
    relation = canonical_schnorr_relation(profile)
    instance = SchnorrRelationInstance(relation.identity, 13)
    witness = SchnorrWitnessAssignment(instance.identity, "witness:x", 7)
    statement = _synthetic_statement(profile, 13, salt="matching")
    grounding = grounding_candidate(instance, relation, statement)
    wrong_statement = _synthetic_statement(profile, 3, salt="wrong-value")
    wrong_grounding = grounding_candidate(instance, relation, wrong_statement)

    left = honest_transcript(instance, 7, 4, 3, profile)
    right = honest_transcript(instance, 7, 4, 4, profile)
    fork = TranscriptFork(left, right)
    equal_challenge = TranscriptFork(left, left)
    different_commitment = TranscriptFork(
        left, honest_transcript(instance, 7, 5, 4, profile)
    )
    rejected = TranscriptFork(left, replace(right, response=(right.response + 1) % profile.q))

    checks = {
        "relation": admit_relation(relation, profile),
        "instance": admit_instance(instance, relation, profile),
        "witness_admission": admit_witness_assignment(
            witness, instance, relation, profile
        ),
        "satisfaction": check_relation_satisfaction(
            witness, instance, relation, profile
        ),
        "grounding_shape": check_grounding_shape(
            grounding, instance, relation, statement, profile
        ),
        "wrong_grounding_shape": check_grounding_shape(
            wrong_grounding, instance, relation, wrong_statement, profile
        ),
        "fork": check_special_soundness_fork(fork, instance, relation, profile),
        "equal_challenge_fork": check_special_soundness_fork(
            equal_challenge, instance, relation, profile
        ),
        "different_commitment_fork": check_special_soundness_fork(
            different_commitment, instance, relation, profile
        ),
        "rejected_fork": check_special_soundness_fork(
            rejected, instance, relation, profile
        ),
        "exhaustive_special_soundness": exhaustive_special_soundness(profile),
        "exhaustive_shvzk": exhaustive_shvzk_distribution_equality(profile),
    }
    expected = {
        "relation": Outcome.AFFIRMATIVE,
        "instance": Outcome.AFFIRMATIVE,
        "witness_admission": Outcome.AFFIRMATIVE,
        "satisfaction": Outcome.AFFIRMATIVE,
        "grounding_shape": Outcome.AFFIRMATIVE,
        "wrong_grounding_shape": Outcome.MISMATCH,
        "fork": Outcome.AFFIRMATIVE,
        "equal_challenge_fork": Outcome.SEMANTIC_NEGATIVE,
        "different_commitment_fork": Outcome.MISMATCH,
        "rejected_fork": Outcome.SEMANTIC_NEGATIVE,
        "exhaustive_special_soundness": Outcome.AFFIRMATIVE,
        "exhaustive_shvzk": Outcome.AFFIRMATIVE,
    }
    for name, expected_outcome in expected.items():
        actual = checks[name]
        if actual.outcome is not expected_outcome:
            raise AssertionError(
                f"{name}: expected {expected_outcome.value}, got "
                f"{actual.outcome.value} ({actual.code})"
            )

    matrix = applicability_refusal_matrix(profile)
    for claim in (
        ApplicabilityClaim.FINITE_SPECIAL_SOUNDNESS_ALGEBRA,
        ApplicabilityClaim.FINITE_SHVZK_DISTRIBUTION,
    ):
        if matrix[claim.value].outcome is not Outcome.AFFIRMATIVE:
            raise AssertionError(f"finite analysis probe {claim.value} did not affirm")
    for claim in (
        ApplicabilityClaim.GENERAL_SPECIAL_SOUNDNESS,
        ApplicabilityClaim.GENERAL_SHVZK,
        ApplicabilityClaim.GENERAL_HVZK,
        ApplicabilityClaim.KNOWLEDGE_SOUNDNESS,
        ApplicabilityClaim.FIAT_SHAMIR_ROM,
        ApplicabilityClaim.FIAT_SHAMIR_QROM,
    ):
        if matrix[claim.value].outcome is not Outcome.REFUSED:
            raise AssertionError(f"theorem probe {claim.value} was not refused")
    checks.update({f"applicability:{name}": value for name, value in matrix.items()})
    return checks


if __name__ == "__main__":
    completed = run_self_check()
    affirmative_count = sum(
        value.outcome is Outcome.AFFIRMATIVE for value in completed.values()
    )
    refusal_count = sum(value.outcome is Outcome.REFUSED for value in completed.values())
    print(
        "P01 relations self-check passed: "
        f"{len(completed)} judgments, {affirmative_count} affirmative, "
        f"{refusal_count} theorem refusals"
    )
