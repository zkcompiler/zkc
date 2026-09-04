"""Relations-owned Schnorr operands, satisfaction, and grounding for P01.

This module deliberately owns only relation meaning:

* relation and public-instance admission;
* owner-local private-witness allocation and admission;
* occurrence-local relation satisfaction;
* Relation/Core/honest-prover correspondence; and
* public Statement grounding from a checker-issued execution view.

Private witness occurrences and completed satisfaction results are owner-local
capabilities.  They have no content identity, portable term, deterministic
public reference, or cold-replay equality.  Missing or foreign owner authority
is a refusal, never a negative relation-satisfaction result.

Transcript algebra, exhaustive finite evaluation, and theorem applicability
belong to :mod:`p01model.analysis`.  Keeping them out of this module prevents an
Analysis procedure from silently becoming a second owner of relation truth.
"""

from __future__ import annotations

from dataclasses import dataclass
import re
from typing import Any

from .provenance import ArtifactContentId, EvidenceRecordId, evidence_record_id
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


_LOCAL_WITNESS_ALLOCATION_SEAL = object()
_LOCAL_SATISFACTION_SEAL = object()


class PrivateWitnessOccurrenceRef:
    """Fresh opaque reference to one owner-local witness occurrence.

    Equality and hashing retain Python object identity.  The reference exposes
    no bytes, label, term, digest, or stable comparison rule and explicitly
    refuses serialization.  It is an in-process authority handle, not a
    semantic value.
    """

    __slots__ = ("_owner_token", "_occurrence_token", "_frozen")

    def __init__(self, owner_token: object, occurrence_token: object, *, _seal: object):
        if _seal is not _LOCAL_WITNESS_ALLOCATION_SEAL:
            raise TypeError("private witness occurrence references are owner-issued")
        object.__setattr__(self, "_owner_token", owner_token)
        object.__setattr__(self, "_occurrence_token", occurrence_token)
        object.__setattr__(self, "_frozen", True)

    def __setattr__(self, name: str, value: object) -> None:
        raise AttributeError("private witness occurrence references are immutable")

    def __repr__(self) -> str:
        return "<PrivateWitnessOccurrenceRef owner-local>"

    def __reduce_ex__(self, protocol: int) -> Any:
        raise TypeError("private witness occurrence references are not serializable")


class SchnorrWitnessAssignment:
    """Owner-issued private assignment with no portable representation.

    ``instance_id`` identifies the public relation instance.  The occurrence
    itself is a fresh opaque local reference.  In particular, this class has
    no ``identity``, ``term``, occurrence label, or deterministic public
    reference derived from the witness or its public context.
    """

    __slots__ = (
        "instance_id",
        "local_occurrence",
        "secret_scalar",
        "_owner_token",
        "_frozen",
    )

    def __init__(
        self,
        instance_id: str,
        local_occurrence: PrivateWitnessOccurrenceRef,
        secret_scalar: int,
        owner_token: object,
        *,
        _seal: object,
    ) -> None:
        if _seal is not _LOCAL_WITNESS_ALLOCATION_SEAL:
            raise TypeError("private witness assignments are owner-issued")
        object.__setattr__(self, "instance_id", instance_id)
        object.__setattr__(self, "local_occurrence", local_occurrence)
        object.__setattr__(self, "secret_scalar", secret_scalar)
        object.__setattr__(self, "_owner_token", owner_token)
        object.__setattr__(self, "_frozen", True)

    def __setattr__(self, name: str, value: object) -> None:
        raise AttributeError("private witness assignments are immutable")

    def __repr__(self) -> str:
        return (
            "<SchnorrWitnessAssignment owner-local "
            f"instance_id={self.instance_id!r} secret_scalar=<redacted>>"
        )

    def __reduce_ex__(self, protocol: int) -> Any:
        raise TypeError("private witness assignments are not serializable")


class RelationSatisfactionOwner:
    """Local authority that allocates witnesses and owns satisfaction checks."""

    __slots__ = ("_owner_token", "_assignments")

    def __init__(self) -> None:
        self._owner_token = object()
        self._assignments: set[SchnorrWitnessAssignment] = set()

    def allocate_witness(
        self,
        instance: SchnorrRelationInstance,
        secret_scalar: int,
    ) -> SchnorrWitnessAssignment:
        """Allocate one fresh occurrence without judging scalar membership."""

        if not isinstance(instance, SchnorrRelationInstance):
            raise TypeError("witness allocation requires a Schnorr relation instance")
        if not isinstance(secret_scalar, int) or isinstance(secret_scalar, bool):
            raise TypeError("witness allocation requires an integer scalar candidate")
        try:
            instance_id = instance.identity
        except (TermEncodingError, TypeError, ValueError) as error:
            raise ValueError("witness allocation requires a closed instance") from error
        occurrence = PrivateWitnessOccurrenceRef(
            self._owner_token,
            object(),
            _seal=_LOCAL_WITNESS_ALLOCATION_SEAL,
        )
        assignment = SchnorrWitnessAssignment(
            instance_id,
            occurrence,
            secret_scalar,
            self._owner_token,
            _seal=_LOCAL_WITNESS_ALLOCATION_SEAL,
        )
        self._assignments.add(assignment)
        return assignment

    def _owns(self, witness: object) -> bool:
        return (
            isinstance(witness, SchnorrWitnessAssignment)
            and witness in self._assignments
            and witness._owner_token is self._owner_token
            and isinstance(witness.local_occurrence, PrivateWitnessOccurrenceRef)
            and witness.local_occurrence._owner_token is self._owner_token
        )

    def __repr__(self) -> str:
        return "<RelationSatisfactionOwner local-authority>"

    def __reduce_ex__(self, protocol: int) -> Any:
        raise TypeError("relation satisfaction owners are not serializable")


class CheckedRelationSatisfaction:
    """Completed owner-local satisfaction judgment and narrow capability.

    The result can be affirmative or semantic-negative, but it is never a
    portable :class:`Result`.  A holder may use the affirmative value only to
    authorize the exact local witness/precondition tuple checked here.
    """

    __slots__ = (
        "outcome",
        "boundary",
        "code",
        "detail",
        "_owner_token",
        "_relation_id",
        "_instance_id",
        "_precondition_contract_id",
        "_public_statement",
        "_witness_assignment",
        "_local_occurrence",
        "_frozen",
    )

    def __init__(
        self,
        *,
        outcome: Outcome,
        boundary: str,
        code: str,
        detail: str,
        owner_token: object,
        relation_id: str,
        instance_id: str,
        precondition_contract_id: str,
        public_statement: int,
        witness_assignment: SchnorrWitnessAssignment,
        _seal: object,
    ) -> None:
        if _seal is not _LOCAL_SATISFACTION_SEAL:
            raise TypeError("relation satisfaction results are Relations-issued")
        if outcome not in (Outcome.AFFIRMATIVE, Outcome.SEMANTIC_NEGATIVE):
            raise ValueError("a completed satisfaction result must be affirmative or negative")
        object.__setattr__(self, "outcome", outcome)
        object.__setattr__(self, "boundary", boundary)
        object.__setattr__(self, "code", code)
        object.__setattr__(self, "detail", detail)
        object.__setattr__(self, "_owner_token", owner_token)
        object.__setattr__(self, "_relation_id", relation_id)
        object.__setattr__(self, "_instance_id", instance_id)
        object.__setattr__(self, "_precondition_contract_id", precondition_contract_id)
        object.__setattr__(self, "_public_statement", public_statement)
        object.__setattr__(self, "_witness_assignment", witness_assignment)
        object.__setattr__(self, "_local_occurrence", witness_assignment.local_occurrence)
        object.__setattr__(self, "_frozen", True)

    def __setattr__(self, name: str, value: object) -> None:
        raise AttributeError("relation satisfaction results are immutable")

    def authorizes_assignment(
        self,
        *,
        witness_assignment: SchnorrWitnessAssignment,
        owner: RelationSatisfactionOwner,
        precondition_contract_id: str,
        public_statement: int,
    ) -> bool:
        """Authorize only the exact owner-issued occurrence checked here."""

        return (
            self.outcome is Outcome.AFFIRMATIVE
            and isinstance(owner, RelationSatisfactionOwner)
            and owner._owner_token is self._owner_token
            and isinstance(witness_assignment, SchnorrWitnessAssignment)
            and witness_assignment is self._witness_assignment
            and owner._owns(witness_assignment)
            and witness_assignment.local_occurrence is self._local_occurrence
            and precondition_contract_id == self._precondition_contract_id
            and public_statement == self._public_statement
        )

    def __repr__(self) -> str:
        return (
            "<CheckedRelationSatisfaction owner-local "
            f"outcome={self.outcome.value} code={self.code!r}>"
        )

    def __reduce_ex__(self, protocol: int) -> Any:
        raise TypeError("relation satisfaction results are not serializable")


def admit_witness_assignment(
    witness: SchnorrWitnessAssignment,
    instance: SchnorrRelationInstance,
    relation: SchnorrRelation,
    profile: AlgebraProfile,
    *,
    owner: RelationSatisfactionOwner | None = None,
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
    if not isinstance(owner, RelationSatisfactionOwner) or not owner._owns(witness):
        return result(
            Outcome.REFUSED,
            "relations:witness-admission:owner-authority",
            "P01-WIT-006",
            "witness admission requires the allocating owner authority",
            subject=instance.identity,
            missing_capability="owner-local witness allocation authority",
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
            subject=instance.identity,
        )
    if witness.instance_id != instance.identity:
        return result(
            Outcome.MISMATCH,
            "relations:witness-admission:instance",
            "P01-WIT-002",
            "witness assignment names a different relation instance",
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
        subject=instance.identity,
        instance_id=instance.identity,
        owner_local=True,
    )


def check_relation_satisfaction(
    witness: SchnorrWitnessAssignment,
    instance: SchnorrRelationInstance,
    relation: SchnorrRelation,
    profile: AlgebraProfile,
    *,
    owner: RelationSatisfactionOwner | None = None,
) -> CheckedRelationSatisfaction | Result:
    witness_result = admit_witness_assignment(
        witness,
        instance,
        relation,
        profile,
        owner=owner,
    )
    if witness_result.outcome is not Outcome.AFFIRMATIVE:
        return witness_result
    if owner is None:  # Kept explicit for type narrowing after admission.
        raise AssertionError("affirmative witness admission without an owner")
    satisfied = (
        pow(profile.generator, witness.secret_scalar, profile.p)
        == instance.public_statement
    )
    return CheckedRelationSatisfaction(
        outcome=(Outcome.AFFIRMATIVE if satisfied else Outcome.SEMANTIC_NEGATIVE),
        boundary="relations:satisfaction",
        code=("P01-SAT-OK" if satisfied else "P01-SAT-001"),
        detail=(
            "admitted owner-local witness assignment satisfies the finite Schnorr equation"
            if satisfied
            else "admitted owner-local witness assignment does not satisfy the Schnorr relation"
        ),
        owner_token=owner._owner_token,
        relation_id=relation.identity,
        instance_id=instance.identity,
        precondition_contract_id=honest_witness_precondition_contract_id(profile),
        public_statement=instance.public_statement,
        witness_assignment=witness,
        _seal=_LOCAL_SATISFACTION_SEAL,
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


_PUBLIC_EXECUTION_STATEMENT_SEAL = object()


class CheckedPublicExecutionStatement:
    """Public Statement projected by the execution qualification checker.

    The constructor is sealed.  Relations can inspect this typed public
    projection, but only the execution checker-owned private factory below can
    mint a normally formed instance.  This prevents grounding from accepting a
    caller-assembled bag of digest-shaped fields as evidence of replay.

    The view itself has no term or identity.  Its coordinates retain their
    existing typed lanes: evidence qualification, artifact record/event, and
    semantic protocol/core/profile identities.
    """

    __slots__ = (
        "public_execution_qualification_id",
        "public_execution_record_id",
        "protocol_id",
        "core_id",
        "evaluation_profile_id",
        "occurrence",
        "value",
        "source_event_id",
        "_issuance_seal",
        "_frozen",
    )

    def __init__(
        self,
        *,
        public_execution_qualification_id: EvidenceRecordId,
        public_execution_record_id: ArtifactContentId,
        protocol_id: str,
        core_id: str,
        evaluation_profile_id: str,
        occurrence: str,
        value: int,
        source_event_id: ArtifactContentId,
        _seal: object,
    ) -> None:
        if _seal is not _PUBLIC_EXECUTION_STATEMENT_SEAL:
            raise TypeError(
                "checked public execution statements are execution-checker-issued"
            )
        object.__setattr__(
            self,
            "public_execution_qualification_id",
            public_execution_qualification_id,
        )
        object.__setattr__(self, "public_execution_record_id", public_execution_record_id)
        object.__setattr__(self, "protocol_id", protocol_id)
        object.__setattr__(self, "core_id", core_id)
        object.__setattr__(self, "evaluation_profile_id", evaluation_profile_id)
        object.__setattr__(self, "occurrence", occurrence)
        object.__setattr__(self, "value", value)
        object.__setattr__(self, "source_event_id", source_event_id)
        object.__setattr__(self, "_issuance_seal", _PUBLIC_EXECUTION_STATEMENT_SEAL)
        object.__setattr__(self, "_frozen", True)

    def __setattr__(self, name: str, value: object) -> None:
        raise AttributeError("checked public execution statements are immutable")

    @property
    def qualification_id(self) -> EvidenceRecordId:
        """Compatibility spelling for the checked qualification identity."""

        return self.public_execution_qualification_id

    @property
    def execution_id(self) -> ArtifactContentId:
        """Compatibility spelling for the checked execution-record identity."""

        return self.public_execution_record_id

    def __reduce_ex__(self, protocol: int) -> Any:
        raise TypeError(
            "checked public execution statement views are not serializable"
        )


def _issue_checked_public_execution_statement(
    *,
    public_execution_qualification_id: EvidenceRecordId,
    public_execution_record_id: ArtifactContentId,
    protocol_id: str,
    core_id: str,
    evaluation_profile_id: str,
    occurrence: str,
    value: int,
    source_event_id: ArtifactContentId,
) -> CheckedPublicExecutionStatement:
    """Execution-checker factory; intentionally private to the package."""

    return CheckedPublicExecutionStatement(
        public_execution_qualification_id=public_execution_qualification_id,
        public_execution_record_id=public_execution_record_id,
        protocol_id=protocol_id,
        core_id=core_id,
        evaluation_profile_id=evaluation_profile_id,
        occurrence=occurrence,
        value=value,
        source_event_id=source_event_id,
        _seal=_PUBLIC_EXECUTION_STATEMENT_SEAL,
    )


# Import compatibility only.  Direct construction still fails without the
# private issuance seal, so this name cannot recreate the former adapter bypass.
QualifiedExecutionStatement = CheckedPublicExecutionStatement


@dataclass(frozen=True)
class RelationExecutionGrounding:
    """Exact relation-instance -> statement-event -> execution bridge."""

    relation_id: str
    instance_id: str
    statement_occurrence_id: ArtifactContentId
    public_execution_qualification_id: EvidenceRecordId
    law: str = "ExactSameDomainStatementEquality.v1"

    def term(self) -> dict[str, str]:
        return {
            "relation_id": self.relation_id,
            "instance_id": self.instance_id,
            "statement_occurrence_id": str(self.statement_occurrence_id),
            "public_execution_qualification_id": (
                str(self.public_execution_qualification_id)
            ),
            "law": self.law,
        }

    @property
    def identity(self) -> EvidenceRecordId:
        """Identify this checked-occurrence bridge as Evidence, not semantics.

        A grounding retains an execution qualification and a concrete Statement
        event.  Those occurrence coordinates are deliberately outside the
        stable semantic identity graph, so the bridge must rotate as an
        Evidence record when either occurrence changes.
        """

        return evidence_record_id("relation-execution-grounding", self.term())

    @property
    def qualification_id(self) -> EvidenceRecordId:
        """Compatibility spelling for the checked qualification identity."""

        return self.public_execution_qualification_id


def relation_execution_grounding_candidate(
    instance: SchnorrRelationInstance,
    relation: SchnorrRelation,
    statement: CheckedPublicExecutionStatement,
) -> RelationExecutionGrounding:
    """Form the unique candidate around a checker-issued public view."""

    return RelationExecutionGrounding(
        relation_id=relation.identity,
        instance_id=instance.identity,
        statement_occurrence_id=statement.source_event_id,
        public_execution_qualification_id=(
            statement.public_execution_qualification_id
        ),
    )


def _check_checked_public_statement(
    statement: CheckedPublicExecutionStatement,
    profile: AlgebraProfile,
) -> Result:
    if not isinstance(statement, CheckedPublicExecutionStatement):
        return result(
            Outcome.MALFORMED,
            "relations:execution-grounding-shape:statement",
            "P01-GRD-001",
            "checked public execution statement has the wrong type",
        )
    if getattr(statement, "_issuance_seal", None) is not _PUBLIC_EXECUTION_STATEMENT_SEAL:
        return result(
            Outcome.REFUSED,
            "relations:execution-grounding-shape:statement-authority",
            "P01-GRD-010",
            "grounding requires a Statement view issued by the execution checker",
            missing_capability="checked public execution statement view",
        )
    semantic_id_fields = (
        statement.protocol_id,
        statement.core_id,
        statement.evaluation_profile_id,
    )
    if (
        not isinstance(
            statement.public_execution_qualification_id,
            EvidenceRecordId,
        )
        or not isinstance(statement.public_execution_record_id, ArtifactContentId)
        or not isinstance(statement.source_event_id, ArtifactContentId)
        or not all(_closed_id(value) for value in semantic_id_fields)
        or not isinstance(statement.occurrence, str)
        or not isinstance(statement.value, int)
        or isinstance(statement.value, bool)
    ):
        return result(
            Outcome.MALFORMED,
            "relations:execution-grounding-shape:qualification",
            "P01-GRD-002",
            "checked public execution statement contains a malformed identity",
            subject="",
        )
    if statement.evaluation_profile_id != profile.identity:
        return result(
            Outcome.MISMATCH,
            "relations:execution-grounding-shape:algebra",
            "P01-GRD-003",
            "checked Statement view belongs to a different finite evaluation profile",
            subject=str(statement.public_execution_qualification_id),
        )
    if statement.occurrence != STATEMENT:
        return result(
            Outcome.MISMATCH,
            "relations:execution-grounding-shape:occurrence",
            "P01-GRD-004",
            "checked event is not the exact Schnorr Statement occurrence",
            subject=str(statement.public_execution_qualification_id),
        )
    if not profile.valid_group_element(statement.value):
        return result(
            Outcome.SEMANTIC_NEGATIVE,
            "relations:execution-grounding-shape:statement-domain",
            "P01-GRD-005",
            "checked Statement value is outside the prime-order subgroup",
            subject=str(statement.public_execution_qualification_id),
        )
    return affirmative(
        "relations:execution-grounding-shape:statement",
        "P01-GRD-STATEMENT-OK",
        "execution-checker-issued view has one well-typed Schnorr Statement occurrence",
        subject=str(statement.public_execution_qualification_id),
    )


def check_relation_execution_grounding(
    grounding: RelationExecutionGrounding,
    instance: SchnorrRelationInstance,
    relation: SchnorrRelation,
    statement: CheckedPublicExecutionStatement,
    profile: AlgebraProfile,
) -> Result:
    """Check exact grounding against an execution-checker-issued public view."""

    instance_result = admit_instance(instance, relation, profile)
    if instance_result.outcome is not Outcome.AFFIRMATIVE:
        return instance_result
    statement_result = _check_checked_public_statement(statement, profile)
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
        or not isinstance(grounding.statement_occurrence_id, ArtifactContentId)
        or not isinstance(
            grounding.public_execution_qualification_id,
            EvidenceRecordId,
        )
        or not _bounded_label(grounding.law, 128)
    ):
        return result(
            Outcome.MALFORMED,
            "relations:execution-grounding-shape:closed-grammar",
            "P01-GRD-009",
            "grounding bridge fields are outside the closed typed grammar",
            subject=_safe_identity(grounding),
        )
    expected = relation_execution_grounding_candidate(
        instance,
        relation,
        statement,
    )
    if grounding != expected:
        return result(
            Outcome.MISMATCH,
            "relations:execution-grounding-shape:exact-operands",
            "P01-GRD-007",
            "grounding bridge does not retain the exact relation, instance, checked Statement, and qualification",
            subject=str(grounding.identity),
            expected_grounding_id=str(expected.identity),
        )
    if statement.value != instance.public_statement:
        return result(
            Outcome.MISMATCH,
            "relations:execution-grounding-shape:value",
            "P01-GRD-008",
            "checked execution Statement differs from the relation-instance value",
            subject=str(grounding.identity),
            relation_instance_id=instance.identity,
            statement_occurrence_id=str(statement.source_event_id),
        )
    return affirmative(
        "relations:execution-grounding-shape",
        "P01-GRD-SHAPE-OK",
        "grounding has exact operands and same-domain checked Statement equality",
        subject=str(grounding.identity),
        relation_id=relation.identity,
        relation_instance_id=instance.identity,
        statement_occurrence_id=str(statement.source_event_id),
        public_execution_qualification_id=(
            str(statement.public_execution_qualification_id)
        ),
        public_execution_record_id=str(statement.public_execution_record_id),
    )


# Compatibility constructor spelling.  The sealed Statement operand remains
# mandatory, so this alias cannot revive the former digest-shaped adapter path.
grounding_candidate = relation_execution_grounding_candidate

# Compatibility checker spelling.  Authority is unchanged because the target
# checker still rejects every non-issued Statement view.
check_grounding_shape = check_relation_execution_grounding


def run_self_check() -> dict[str, Any]:
    """Exercise Relations-owned admission, satisfaction, and authority cuts."""

    profile = AlgebraProfile(p=23, q=11, generator=2, challenge_size=8)
    relation = canonical_schnorr_relation(profile)
    instance = SchnorrRelationInstance(relation.identity, 13)
    owner = RelationSatisfactionOwner()
    foreign_owner = RelationSatisfactionOwner()
    witness = owner.allocate_witness(instance, 7)
    same_value_other_occurrence = owner.allocate_witness(instance, 7)
    foreign_same_value = foreign_owner.allocate_witness(instance, 7)
    wrong_witness = owner.allocate_witness(instance, 8)

    checks: dict[str, Any] = {
        "relation": admit_relation(relation, profile),
        "instance": admit_instance(instance, relation, profile),
        "witness_admission": admit_witness_assignment(
            witness,
            instance,
            relation,
            profile,
            owner=owner,
        ),
        "satisfaction": check_relation_satisfaction(
            witness,
            instance,
            relation,
            profile,
            owner=owner,
        ),
        "negative_satisfaction": check_relation_satisfaction(
            wrong_witness,
            instance,
            relation,
            profile,
            owner=owner,
        ),
        "missing_owner_authority": admit_witness_assignment(
            witness,
            instance,
            relation,
            profile,
        ),
        "foreign_owner_authority": admit_witness_assignment(
            witness,
            instance,
            relation,
            profile,
            owner=foreign_owner,
        ),
    }
    for name in ("relation", "instance", "witness_admission"):
        if checks[name].outcome is not Outcome.AFFIRMATIVE:
            raise AssertionError(f"{name} did not affirm: {checks[name].code}")
    satisfaction = checks["satisfaction"]
    if (
        not isinstance(satisfaction, CheckedRelationSatisfaction)
        or satisfaction.outcome is not Outcome.AFFIRMATIVE
        or not satisfaction.authorizes_assignment(
            witness_assignment=witness,
            owner=owner,
            precondition_contract_id=honest_witness_precondition_contract_id(profile),
            public_statement=instance.public_statement,
        )
    ):
        raise AssertionError("affirmative owner-local satisfaction was not usable")
    if satisfaction.authorizes_assignment(
        witness_assignment=same_value_other_occurrence,
        owner=owner,
        precondition_contract_id=honest_witness_precondition_contract_id(profile),
        public_statement=instance.public_statement,
    ):
        raise AssertionError("same-value occurrence substitution was authorized")
    if satisfaction.authorizes_assignment(
        witness_assignment=foreign_same_value,
        owner=foreign_owner,
        precondition_contract_id=honest_witness_precondition_contract_id(profile),
        public_statement=instance.public_statement,
    ):
        raise AssertionError("foreign-owner assignment substitution was authorized")
    negative = checks["negative_satisfaction"]
    if (
        not isinstance(negative, CheckedRelationSatisfaction)
        or negative.outcome is not Outcome.SEMANTIC_NEGATIVE
        or negative.authorizes_assignment(
            witness_assignment=wrong_witness,
            owner=owner,
            precondition_contract_id=honest_witness_precondition_contract_id(profile),
            public_statement=instance.public_statement,
        )
    ):
        raise AssertionError("negative satisfaction was not kept non-authorizing")
    for name in ("missing_owner_authority", "foreign_owner_authority"):
        if checks[name].outcome is not Outcome.REFUSED:
            raise AssertionError(f"{name} was not refused")
    return checks


if __name__ == "__main__":
    completed = run_self_check()
    print(
        "P01 Relations self-check passed: "
        f"{len(completed)} admission, satisfaction, and authority judgments"
    )
