"""Finite model for the recursive-composition ownership boundary.

This module deliberately models only the distinctions selected by the research
package.  It is not an IVC, PCD, folding, accumulation, or CycleFold
implementation and does not establish any cryptographic theorem.
"""

from __future__ import annotations

from dataclasses import asdict, dataclass
from enum import Enum
import hashlib
import json
from types import MappingProxyType
from typing import Mapping


class Outcome(str, Enum):
    AFFIRMATIVE = "Affirmative"
    NEGATIVE = "Negative"
    MALFORMED = "Malformed"
    REFUSED = "Refused"
    UNSUPPORTED = "Unsupported"
    CANNOT_ANSWER = "CannotAnswer"


@dataclass(frozen=True)
class Answer:
    outcome: Outcome
    value: object | None = None
    reason: str = ""


def affirmative(value: object) -> Answer:
    return Answer(Outcome.AFFIRMATIVE, value)


def _canonical(value: object) -> object:
    if isinstance(value, Enum):
        return value.value
    if hasattr(value, "__dataclass_fields__"):
        return {
            key: _canonical(item)
            for key, item in asdict(value).items()
            if not key.startswith("_")
        }
    if isinstance(value, Mapping):
        return {
            str(key): _canonical(value[key])
            for key in sorted(value, key=lambda item: str(item))
        }
    if isinstance(value, (tuple, list)):
        return [_canonical(item) for item in value]
    if isinstance(value, bytes):
        return {"bytes_hex": value.hex()}
    return value


def semantic_id(domain: str, value: object) -> str:
    encoded = json.dumps(
        {"domain": domain, "value": _canonical(value)},
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


# ---------------------------------------------------------------------------
# Relations-owned recursion-facing instance coverage


@dataclass(frozen=True)
class DigestBindingEdge:
    child_role: str
    parent_role: str
    digest_rule_id: str


@dataclass(frozen=True)
class BindingCoverageSchema:
    roles: tuple[str, ...]
    strictly_checked_roles: tuple[str, ...]
    digest_edges: tuple[DigestBindingEdge, ...]

    @property
    def identity(self) -> str:
        return semantic_id("relations.recursion-binding-coverage-schema", self)


@dataclass(eq=False, frozen=True)
class InstanceOccurrence:
    role: str
    interface_id: str
    public_value: object
    occurrence_label: str


@dataclass(frozen=True)
class StrictInstanceCheck:
    role: str
    occurrence: InstanceOccurrence
    affirmative: bool


@dataclass(frozen=True)
class DigestEquationCheck:
    edge: DigestBindingEdge
    child: InstanceOccurrence
    parent: InstanceOccurrence
    affirmative: bool


@dataclass(frozen=True)
class BindingCoverageInvocation:
    instances: Mapping[str, InstanceOccurrence]
    strict_checks: tuple[StrictInstanceCheck, ...]
    digest_checks: tuple[DigestEquationCheck, ...]


@dataclass(eq=False, frozen=True)
class CheckedBindingCoverage:
    schema_id: str
    paths_to_strict_check: Mapping[str, tuple[str, ...]]
    digest_rule_ids: tuple[str, ...]


_QUALIFIED_BINDING_COVERAGE_RESULTS: dict[int, CheckedBindingCoverage] = {}


def check_binding_coverage(
    schema: BindingCoverageSchema,
    invocation: BindingCoverageInvocation,
) -> Answer:
    roles = schema.roles
    strict_roles = schema.strictly_checked_roles
    if not roles or any(not role for role in roles):
        return Answer(Outcome.MALFORMED, reason="coverage roles are empty")
    if len(set(roles)) != len(roles) or len(set(strict_roles)) != len(strict_roles):
        return Answer(Outcome.MALFORMED, reason="coverage roles are duplicated")
    if not set(strict_roles).issubset(roles) or not strict_roles:
        return Answer(Outcome.MALFORMED, reason="strict roots are absent or unknown")
    if set(invocation.instances) != set(roles):
        return Answer(Outcome.MALFORMED, reason="instance invocation is not exact")
    if any(
        occurrence.role != role
        for role, occurrence in invocation.instances.items()
    ):
        return Answer(Outcome.REFUSED, reason="instance occurrence has the wrong role")

    edge_by_child: dict[str, DigestBindingEdge] = {}
    for edge in schema.digest_edges:
        if (
            edge.child_role not in roles
            or edge.parent_role not in roles
            or edge.child_role == edge.parent_role
            or not edge.digest_rule_id
        ):
            return Answer(Outcome.MALFORMED, reason="digest edge is ill formed")
        if edge.child_role in edge_by_child:
            return Answer(Outcome.MALFORMED, reason="digest child has multiple parents")
        if edge.child_role in strict_roles:
            return Answer(Outcome.MALFORMED, reason="strict root has a surplus parent edge")
        edge_by_child[edge.child_role] = edge

    uncovered = set(roles) - set(strict_roles) - set(edge_by_child)
    if uncovered:
        return Answer(
            Outcome.REFUSED,
            reason=f"unbound recursion-facing roles: {sorted(uncovered)}",
        )

    paths: dict[str, tuple[str, ...]] = {}
    for role in roles:
        path = [role]
        seen = {role}
        cursor = role
        while cursor not in strict_roles:
            edge = edge_by_child.get(cursor)
            if edge is None:
                return Answer(Outcome.REFUSED, reason="binding path has no strict root")
            cursor = edge.parent_role
            if cursor in seen:
                return Answer(Outcome.REFUSED, reason="binding coverage contains a cycle")
            seen.add(cursor)
            path.append(cursor)
        paths[role] = tuple(path)

    strict_by_role = {item.role: item for item in invocation.strict_checks}
    if len(strict_by_role) != len(invocation.strict_checks) or set(strict_by_role) != set(strict_roles):
        return Answer(Outcome.MALFORMED, reason="strict checks are not exact")
    for role, checked in strict_by_role.items():
        if checked.occurrence is not invocation.instances[role]:
            return Answer(Outcome.REFUSED, reason="strict check binds a different occurrence")
        if not checked.affirmative:
            return Answer(Outcome.NEGATIVE, reason="strict instance check is false")

    digest_by_edge = {item.edge: item for item in invocation.digest_checks}
    if len(digest_by_edge) != len(invocation.digest_checks) or set(digest_by_edge) != set(schema.digest_edges):
        return Answer(Outcome.MALFORMED, reason="digest equation checks are not exact")
    for edge in schema.digest_edges:
        checked = digest_by_edge[edge]
        if (
            checked.child is not invocation.instances[edge.child_role]
            or checked.parent is not invocation.instances[edge.parent_role]
        ):
            return Answer(Outcome.REFUSED, reason="digest check binds a different occurrence")
        if not checked.affirmative:
            return Answer(Outcome.NEGATIVE, reason="digest binding equation is false")

    checked = CheckedBindingCoverage(
        schema.identity,
        MappingProxyType(paths),
        tuple(sorted({edge.digest_rule_id for edge in schema.digest_edges})),
    )
    _QUALIFIED_BINDING_COVERAGE_RESULTS[id(checked)] = checked
    return affirmative(checked)


# ---------------------------------------------------------------------------
# Analysis-owned closed incremental-composition family


@dataclass(frozen=True)
class FamilyDescriptionAdviceContract:
    protocol_advice_coordinate: str
    relation_advice_coordinate: str
    grounding_equation_id: str
    digest_algorithm_id: str
    digest_evaluation_id: str


@dataclass(frozen=True)
class IncrementalCompositionMember:
    member_key: str
    protocol_id: str
    plan_id: str
    protocol_relation_binding_id: str
    recurrence_grounding_equation_id: str
    binding_coverage_schema_id: str
    predecessor_ingress_keys: tuple[str, ...]
    carried_public_coordinates: tuple[str, ...]
    family_description_advice: FamilyDescriptionAdviceContract | None = None
    authenticated: bool = True
    runtime_structure_dependencies: tuple[str, ...] = ()
    embeds_family_identity: bool = False
    embeds_derived_family_digest: bool = False


@dataclass(frozen=True)
class SelectorEntry:
    selector_value: int
    member_key: str


@dataclass(frozen=True)
class CompositionDecisionContract:
    input_schema_id: str
    output_schema_id: str
    operation_semantics_id: str
    failure_partition_id: str

    @property
    def identity(self) -> str:
        return semantic_id("analysis.composition-decision-contract", self)


@dataclass(frozen=True)
class CarriedObligationSlot:
    role: str
    public_coordinate_type: str
    discharge_operation_id: str


@dataclass(frozen=True)
class IncrementalCompositionFamily:
    members: tuple[IncrementalCompositionMember, ...]
    selector_table: tuple[SelectorEntry, ...]
    update_verifier: CompositionDecisionContract
    final_decider: CompositionDecisionContract
    carried_obligation_slots: tuple[CarriedObligationSlot, ...]

    @property
    def identity(self) -> str:
        return semantic_id("analysis.incremental-composition-family", self)


@dataclass(frozen=True)
class CheckedIncrementalCompositionFamily:
    family_id: str
    member_keys: tuple[str, ...]
    selector_values: tuple[int, ...]
    family_description_digests: Mapping[str, str]


_QUALIFIED_FAMILY_CHECKS: dict[int, CheckedIncrementalCompositionFamily] = {}


def derive_family_description_digest(
    family: IncrementalCompositionFamily,
    contract: FamilyDescriptionAdviceContract,
) -> Answer:
    if contract.digest_algorithm_id != "sha256-v1":
        return Answer(Outcome.UNSUPPORTED, reason="digest algorithm is unsupported")
    if contract.digest_evaluation_id != "canonical-json-v1":
        return Answer(Outcome.UNSUPPORTED, reason="digest evaluation is unsupported")
    return affirmative(
        semantic_id("analysis.incremental-composition-family-description", family)
    )


def check_incremental_composition_family(
    family: IncrementalCompositionFamily,
) -> Answer:
    if not family.members or not family.selector_table:
        return Answer(Outcome.MALFORMED, reason="family or selector table is empty")
    member_keys = tuple(member.member_key for member in family.members)
    if any(not key for key in member_keys) or len(set(member_keys)) != len(member_keys):
        return Answer(Outcome.MALFORMED, reason="family member keys are not unique")
    selector_values = tuple(entry.selector_value for entry in family.selector_table)
    if len(set(selector_values)) != len(selector_values):
        return Answer(Outcome.MALFORMED, reason="selector values are duplicated")
    selected_keys = tuple(entry.member_key for entry in family.selector_table)
    if set(selected_keys) != set(member_keys):
        return Answer(Outcome.MALFORMED, reason="selector table does not cover the exact family")

    for contract in (family.update_verifier, family.final_decider):
        if not all(
            (
                contract.input_schema_id,
                contract.output_schema_id,
                contract.operation_semantics_id,
                contract.failure_partition_id,
            )
        ):
            return Answer(Outcome.MALFORMED, reason="decision contract is incomplete")

    slot_roles = tuple(slot.role for slot in family.carried_obligation_slots)
    if len(set(slot_roles)) != len(slot_roles):
        return Answer(Outcome.MALFORMED, reason="carried-obligation roles are duplicated")
    if any(
        not all((slot.role, slot.public_coordinate_type, slot.discharge_operation_id))
        for slot in family.carried_obligation_slots
    ):
        return Answer(Outcome.MALFORMED, reason="carried-obligation slot is incomplete")

    derived_digests: dict[str, str] = {}
    for member in family.members:
        if not member.authenticated or not all(
            (
                member.protocol_id,
                member.plan_id,
                member.protocol_relation_binding_id,
                member.recurrence_grounding_equation_id,
                member.binding_coverage_schema_id,
            )
        ):
            return Answer(Outcome.REFUSED, reason="family member structure is not authenticated")
        if len(set(member.predecessor_ingress_keys)) != len(member.predecessor_ingress_keys):
            return Answer(Outcome.MALFORMED, reason="predecessor ingress keys are duplicated")
        if not member.carried_public_coordinates or len(
            set(member.carried_public_coordinates)
        ) != len(member.carried_public_coordinates):
            return Answer(Outcome.MALFORMED, reason="carried public coordinates are not exact")
        if member.runtime_structure_dependencies:
            return Answer(Outcome.REFUSED, reason="member structure depends on runtime values")
        if member.embeds_family_identity or member.embeds_derived_family_digest:
            return Answer(Outcome.REFUSED, reason="member embeds a derived family result")
        advice = member.family_description_advice
        if advice is not None:
            if not all(
                (
                    advice.protocol_advice_coordinate,
                    advice.relation_advice_coordinate,
                    advice.grounding_equation_id,
                    advice.digest_algorithm_id,
                    advice.digest_evaluation_id,
                )
            ):
                return Answer(Outcome.MALFORMED, reason="family-description advice is incomplete")
            digest = derive_family_description_digest(family, advice)
            if digest.outcome is not Outcome.AFFIRMATIVE:
                return digest
            derived_digests[member.member_key] = digest.value
    checked = CheckedIncrementalCompositionFamily(
        family.identity,
        member_keys,
        selector_values,
        MappingProxyType(derived_digests),
    )
    _QUALIFIED_FAMILY_CHECKS[id(checked)] = checked
    return affirmative(checked)


def select_incremental_composition_member(
    family: IncrementalCompositionFamily,
    checked: CheckedIncrementalCompositionFamily,
    selector_value: int,
    runtime_generated_structure: object | None = None,
) -> Answer:
    if (
        _QUALIFIED_FAMILY_CHECKS.get(id(checked)) is not checked
        or checked.family_id != family.identity
    ):
        return Answer(Outcome.REFUSED, reason="family check names another family")
    if runtime_generated_structure is not None:
        return Answer(Outcome.REFUSED, reason="runtime structure generation is forbidden")
    table = {entry.selector_value: entry.member_key for entry in family.selector_table}
    if selector_value not in table:
        return Answer(Outcome.REFUSED, reason="selector is outside the closed family")
    member = next(item for item in family.members if item.member_key == table[selector_value])
    return affirmative(member)


# ---------------------------------------------------------------------------
# Exact two-run/two-instance EquationGrounding control


class GroundingSourceKind(str, Enum):
    INSTANCE_PUBLIC = "InstancePublic"
    PROTOCOL_VALUE = "ProtocolValue"


@dataclass(frozen=True)
class GroundingSource:
    kind: GroundingSourceKind
    slot: int
    key: str
    value_type: str = "Nat"


@dataclass(frozen=True)
class GroundingEquality:
    left_source: int
    right_source: int
    value_type: str = "Nat"


@dataclass(frozen=True)
class GroundingEquation:
    instance_interfaces: tuple[str, ...]
    run_protocols: tuple[str, ...]
    sources: tuple[GroundingSource, ...]
    equalities: tuple[GroundingEquality, ...]

    @property
    def identity(self) -> str:
        return semantic_id("relations.grounding-equation", self)


@dataclass(eq=False, frozen=True)
class RelationInstanceOccurrence:
    interface_id: str
    public_values: Mapping[str, object]
    occurrence_label: str


@dataclass(eq=False, frozen=True)
class QualifiedRunOccurrence:
    protocol_id: str
    values: Mapping[str, object]
    occurrence_label: str


@dataclass(eq=False, frozen=True)
class GroundingSourceAuthority:
    source: RelationInstanceOccurrence | QualifiedRunOccurrence


@dataclass(frozen=True)
class GroundingInvocation:
    instances: Mapping[int, RelationInstanceOccurrence]
    runs: Mapping[int, QualifiedRunOccurrence]
    authorities: Mapping[tuple[str, int], GroundingSourceAuthority]


@dataclass(frozen=True)
class CheckedGroundingEvaluation:
    equation_id: str
    source_values: tuple[object, ...]
    agreements: tuple[bool, ...]


def canonical_two_run_recurrence_equation() -> GroundingEquation:
    return GroundingEquation(
        instance_interfaces=("relations.source-instance.v1", "relations.target-instance.v1"),
        run_protocols=("pir.source-step.v1", "pir.target-step.v1"),
        sources=(
            GroundingSource(GroundingSourceKind.PROTOCOL_VALUE, 0, "produced_accumulator"),
            GroundingSource(GroundingSourceKind.INSTANCE_PUBLIC, 0, "accumulator"),
            GroundingSource(GroundingSourceKind.INSTANCE_PUBLIC, 1, "accumulator"),
            GroundingSource(GroundingSourceKind.PROTOCOL_VALUE, 1, "statement"),
        ),
        equalities=(
            GroundingEquality(0, 1),
            GroundingEquality(1, 2),
            GroundingEquality(2, 3),
        ),
    )


def evaluate_two_run_recurrence_grounding(
    equation: GroundingEquation,
    invocation: GroundingInvocation,
) -> Answer:
    expected = canonical_two_run_recurrence_equation()
    if equation != expected or equation.identity != expected.identity:
        return Answer(Outcome.REFUSED, reason="equation is not the exact recurrence grounding law")
    if set(invocation.instances) != {0, 1} or set(invocation.runs) != {0, 1}:
        return Answer(Outcome.MALFORMED, reason="grounding operands are not exact")
    expected_authorities = {("instance", 0), ("instance", 1), ("run", 0), ("run", 1)}
    if set(invocation.authorities) != expected_authorities:
        return Answer(Outcome.MALFORMED, reason="source authorities are not exact")
    for ordinal, interface_id in enumerate(equation.instance_interfaces):
        occurrence = invocation.instances[ordinal]
        authority = invocation.authorities[("instance", ordinal)]
        if occurrence.interface_id != interface_id:
            return Answer(Outcome.REFUSED, reason="instance owner differs")
        if authority.source is not occurrence:
            return Answer(Outcome.REFUSED, reason="instance authority binds another occurrence")
    for ordinal, protocol_id in enumerate(equation.run_protocols):
        occurrence = invocation.runs[ordinal]
        authority = invocation.authorities[("run", ordinal)]
        if occurrence.protocol_id != protocol_id:
            return Answer(Outcome.REFUSED, reason="run owner differs")
        if authority.source is not occurrence:
            return Answer(Outcome.REFUSED, reason="run authority binds another occurrence")

    values: list[object] = []
    try:
        for source in equation.sources:
            if source.kind is GroundingSourceKind.INSTANCE_PUBLIC:
                values.append(invocation.instances[source.slot].public_values[source.key])
            else:
                values.append(invocation.runs[source.slot].values[source.key])
    except (KeyError, IndexError):
        return Answer(Outcome.CANNOT_ANSWER, reason="grounding source value is absent")
    agreements = tuple(
        values[equality.left_source] == values[equality.right_source]
        for equality in equation.equalities
    )
    result = CheckedGroundingEvaluation(equation.identity, tuple(values), agreements)
    return Answer(
        Outcome.AFFIRMATIVE if all(agreements) else Outcome.NEGATIVE,
        result,
    )


# ---------------------------------------------------------------------------
# Portable re-admission and process-local causal authority


@dataclass(frozen=True)
class PortableAccumulatorPair:
    public_instance: int
    private_witness: bytes


@dataclass(eq=False, frozen=True)
class SourceContinuationOccurrence:
    value: PortableAccumulatorPair
    occurrence_label: str


@dataclass(eq=False, frozen=True)
class CausalHandoffCapability:
    source: SourceContinuationOccurrence


@dataclass(eq=False, frozen=True)
class CausalTargetInputOccurrence:
    value: PortableAccumulatorPair
    source: SourceContinuationOccurrence
    capability: CausalHandoffCapability


@dataclass(eq=False, frozen=True)
class DeciderResult:
    value: PortableAccumulatorPair
    affirmative: bool
    decider_id: str


@dataclass(eq=False, frozen=True)
class ReadmittedPortableInputOccurrence:
    value: PortableAccumulatorPair
    validation: DeciderResult


_ISSUED_CAUSAL_CAPABILITIES: dict[int, CausalHandoffCapability] = {}
_SPENT_CAUSAL_CAPABILITIES: set[int] = set()
_ISSUED_CAUSAL_TARGETS: dict[int, CausalTargetInputOccurrence] = {}


def issue_causal_handoff_capability(
    source: SourceContinuationOccurrence,
) -> CausalHandoffCapability:
    capability = CausalHandoffCapability(source)
    _ISSUED_CAUSAL_CAPABILITIES[id(capability)] = capability
    return capability


def issue_causal_handoff(
    source: SourceContinuationOccurrence,
    capability: CausalHandoffCapability,
) -> Answer:
    capability_key = id(capability)
    if (
        _ISSUED_CAUSAL_CAPABILITIES.get(capability_key) is not capability
        or capability.source is not source
        or capability_key in _SPENT_CAUSAL_CAPABILITIES
    ):
        return Answer(Outcome.REFUSED, reason="causal capability is stale or wrong")
    target = CausalTargetInputOccurrence(source.value, source, capability)
    _SPENT_CAUSAL_CAPABILITIES.add(capability_key)
    _ISSUED_CAUSAL_TARGETS[id(target)] = target
    return affirmative(target)


def join_causal_handoff(
    source: SourceContinuationOccurrence,
    target: object,
) -> Answer:
    if type(target) is not CausalTargetInputOccurrence:
        return Answer(Outcome.REFUSED, reason="target is not a causal input occurrence")
    if (
        _ISSUED_CAUSAL_TARGETS.get(id(target)) is not target
        or target.source is not source
        or target.capability.source is not source
    ):
        return Answer(Outcome.REFUSED, reason="causal occurrences differ")
    return affirmative((source, target))


def serialize_portable_pair(value: PortableAccumulatorPair) -> bytes:
    return json.dumps(
        {
            "private_witness_hex": value.private_witness.hex(),
            "public_instance": value.public_instance,
        },
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")


def decode_portable_pair(encoded: bytes) -> Answer:
    try:
        body = json.loads(encoded.decode("utf-8"))
        if set(body) != {"private_witness_hex", "public_instance"}:
            raise ValueError("portable body has unexpected fields")
        value = PortableAccumulatorPair(
            int(body["public_instance"]),
            bytes.fromhex(body["private_witness_hex"]),
        )
    except (UnicodeDecodeError, json.JSONDecodeError, KeyError, TypeError, ValueError) as error:
        return Answer(Outcome.MALFORMED, reason=str(error))
    return affirmative(value)


def readmit_portable_pair(
    value: PortableAccumulatorPair,
    validation: DeciderResult,
) -> Answer:
    if validation.value is not value:
        return Answer(Outcome.REFUSED, reason="decider result binds another decoded occurrence")
    if not validation.affirmative:
        return Answer(Outcome.NEGATIVE, reason="decider rejected the received accumulator")
    if not validation.decider_id:
        return Answer(Outcome.MALFORMED, reason="decider identity is absent")
    return affirmative(ReadmittedPortableInputOccurrence(value, validation))


# ---------------------------------------------------------------------------
# Analysis-owned derived obligations and report qualification


class ReportMode(str, Enum):
    CONDITIONAL = "Conditional"
    CARRIED_OBLIGATIONS_DISCHARGED = "CarriedObligationsDischarged"
    HYPOTHESIS_FREE = "HypothesisFree"


@dataclass(eq=False, frozen=True)
class OutstandingCompositionObligation:
    hypothesis_goal_id: str
    member_key: str
    slot_ordinal: int
    public_coordinate: str
    discharge_operation_id: str


@dataclass(eq=False, frozen=True)
class ObligationDischargeCapability:
    obligation: OutstandingCompositionObligation
    operation_id: str
    affirmative: bool
    result_id: str


@dataclass(frozen=True)
class ObligationDischarge:
    obligation: OutstandingCompositionObligation
    operation_id: str
    affirmative: bool
    result_id: str
    capability: ObligationDischargeCapability


@dataclass(frozen=True)
class QualifiedVerificationReport:
    judgment_id: str
    mode: ReportMode
    remaining_hypotheses: tuple[str, ...]
    outstanding_carried_obligations: tuple[OutstandingCompositionObligation, ...]
    discharge_result_ids: tuple[str, ...]


_QUALIFIED_COMPOSITION_JUDGMENTS: dict[int, IncrementalCompositionJudgment] = {}
_QUALIFIED_COMPOSITION_OBLIGATIONS: dict[int, OutstandingCompositionObligation] = {}
_ISSUED_OBLIGATION_DISCHARGE_CAPABILITIES: dict[
    int, ObligationDischargeCapability
] = {}
_SPENT_OBLIGATION_DISCHARGE_CAPABILITIES: set[int] = set()


def issue_obligation_discharge(
    obligation: OutstandingCompositionObligation,
    operation_id: str,
    is_affirmative: bool,
    result_id: str,
) -> Answer:
    if _QUALIFIED_COMPOSITION_OBLIGATIONS.get(id(obligation)) is not obligation:
        return Answer(Outcome.REFUSED, reason="obligation is not judgment-derived")
    if operation_id != obligation.discharge_operation_id:
        return Answer(Outcome.REFUSED, reason="discharge operation is not authorized")
    if not result_id:
        return Answer(Outcome.MALFORMED, reason="discharge result identity is absent")
    capability = ObligationDischargeCapability(
        obligation,
        operation_id,
        is_affirmative,
        result_id,
    )
    _ISSUED_OBLIGATION_DISCHARGE_CAPABILITIES[id(capability)] = capability
    return affirmative(
        ObligationDischarge(
            obligation,
            operation_id,
            is_affirmative,
            result_id,
            capability,
        )
    )


def qualify_verification_report(
    judgment: IncrementalCompositionJudgment,
    discharges: tuple[ObligationDischarge, ...],
    mode: ReportMode,
) -> Answer:
    if _QUALIFIED_COMPOSITION_JUDGMENTS.get(id(judgment)) is not judgment:
        return Answer(Outcome.REFUSED, reason="judgment is not a qualified Analysis result")
    outstanding = judgment.outstanding_carried_obligations
    if len({id(item.obligation) for item in discharges}) != len(discharges):
        return Answer(Outcome.MALFORMED, reason="obligation discharge is duplicated")
    by_identity = {id(item.obligation): item for item in discharges}
    expected_ids = {id(item) for item in outstanding}
    if not set(by_identity).issubset(expected_ids):
        return Answer(Outcome.REFUSED, reason="discharge names an extra or substituted obligation")
    for discharge in discharges:
        capability_key = id(discharge.capability)
        if (
            _ISSUED_OBLIGATION_DISCHARGE_CAPABILITIES.get(capability_key)
            is not discharge.capability
            or capability_key in _SPENT_OBLIGATION_DISCHARGE_CAPABILITIES
            or discharge.capability.obligation is not discharge.obligation
            or discharge.capability.operation_id != discharge.operation_id
            or discharge.capability.affirmative is not discharge.affirmative
            or discharge.capability.result_id != discharge.result_id
        ):
            return Answer(Outcome.REFUSED, reason="discharge capability is stale or mismatched")
        if discharge.operation_id != discharge.obligation.discharge_operation_id:
            return Answer(Outcome.REFUSED, reason="discharge operation is not authorized")
        if not discharge.result_id:
            return Answer(Outcome.MALFORMED, reason="discharge result identity is absent")

    remaining_obligations = tuple(
        obligation
        for obligation in outstanding
        if id(obligation) not in by_identity or not by_identity[id(obligation)].affirmative
    )
    discharged_goal_ids = {
        item.obligation.hypothesis_goal_id for item in discharges if item.affirmative
    }
    remaining_hypotheses = tuple(
        item for item in judgment.retained_hypotheses if item not in discharged_goal_ids
    )
    if (
        mode in {
            ReportMode.CARRIED_OBLIGATIONS_DISCHARGED,
            ReportMode.HYPOTHESIS_FREE,
        }
        and remaining_obligations
    ):
        return Answer(Outcome.REFUSED, reason="report has outstanding carried obligations")
    if mode is ReportMode.HYPOTHESIS_FREE and remaining_hypotheses:
        return Answer(Outcome.REFUSED, reason="hypothesis-free report retains hypotheses")

    _SPENT_OBLIGATION_DISCHARGE_CAPABILITIES.update(
        id(discharge.capability) for discharge in discharges
    )
    return affirmative(
        QualifiedVerificationReport(
            judgment.judgment_id,
            mode,
            remaining_hypotheses,
            remaining_obligations,
            tuple(sorted(item.result_id for item in discharges if item.affirmative)),
        )
    )


# ---------------------------------------------------------------------------
# CycleFold same-step guardrail


@dataclass(eq=False, frozen=True)
class StepOccurrence:
    step_id: str


@dataclass(eq=False, frozen=True)
class PrimaryFoldValues:
    step: StepOccurrence
    rho: int
    c1: int
    c2: int
    c_prime: int


@dataclass(eq=False, frozen=True)
class CompanionCurveInstance:
    created_in_step: StepOccurrence
    public_io: tuple[int, int, int, int]
    strict: bool
    folded_in_step: StepOccurrence | None
    folded_before_completion: bool
    terminal_handoff_only: bool = False


@dataclass(eq=False, frozen=True)
class CheckedCycleFoldSameStepBinding:
    step_id: str
    public_io: tuple[int, int, int, int]


_QUALIFIED_CYCLEFOLD_RESULTS: dict[int, CheckedCycleFoldSameStepBinding] = {}


def check_cyclefold_same_step_binding(
    primary: PrimaryFoldValues,
    companion: CompanionCurveInstance,
) -> Answer:
    expected_io = (primary.rho, primary.c1, primary.c2, primary.c_prime)
    if companion.terminal_handoff_only:
        return Answer(Outcome.REFUSED, reason="terminal handoff does not establish intra-step binding")
    if companion.created_in_step is not primary.step:
        return Answer(Outcome.REFUSED, reason="companion instance was not created in the primary step")
    if not companion.strict:
        return Answer(Outcome.NEGATIVE, reason="companion instance is not strict")
    if companion.public_io != expected_io:
        return Answer(Outcome.NEGATIVE, reason="companion public I/O differs from the primary fold")
    if companion.folded_in_step is not primary.step or not companion.folded_before_completion:
        return Answer(Outcome.REFUSED, reason="companion instance was not folded before step completion")
    checked = CheckedCycleFoldSameStepBinding(primary.step.step_id, expected_io)
    _QUALIFIED_CYCLEFOLD_RESULTS[id(checked)] = checked
    return affirmative(checked)


# ---------------------------------------------------------------------------
# Exact owner-local Relations-result ingress into Analysis


@dataclass(frozen=True)
class CausalStepRecurrenceQuestionCoordinate:
    equation_id: str
    source_binding_id: str
    source_edge: str
    target_binding_id: str
    target_edge: str

    @property
    def identity(self) -> str:
        return semantic_id("relations.causal-plan-step-recurrence-question", self)


@dataclass(eq=False, frozen=True)
class CheckedCausalStepRecurrence:
    question: CausalStepRecurrenceQuestionCoordinate
    grounding: CheckedGroundingEvaluation
    source_run: QualifiedRunOccurrence
    target_run: QualifiedRunOccurrence
    source: SourceContinuationOccurrence
    target: CausalTargetInputOccurrence


_QUALIFIED_CAUSAL_STEP_RESULTS: dict[int, CheckedCausalStepRecurrence] = {}


def check_causal_step_recurrence(
    question: CausalStepRecurrenceQuestionCoordinate,
    equation: GroundingEquation,
    invocation: GroundingInvocation,
    source: SourceContinuationOccurrence,
    target: object,
) -> Answer:
    if question.equation_id != equation.identity or not all(
        (
            question.source_binding_id,
            question.source_edge,
            question.target_binding_id,
            question.target_edge,
        )
    ):
        return Answer(Outcome.REFUSED, reason="recurrence question coordinate differs")
    grounding = evaluate_two_run_recurrence_grounding(equation, invocation)
    if grounding.outcome is not Outcome.AFFIRMATIVE:
        return grounding
    handoff = join_causal_handoff(source, target)
    if handoff.outcome is not Outcome.AFFIRMATIVE:
        return handoff
    if type(target) is not CausalTargetInputOccurrence:
        return Answer(Outcome.REFUSED, reason="target is not the issued causal occurrence")
    try:
        source_public = invocation.runs[0].values["produced_accumulator"]
        target_public = invocation.runs[1].values["statement"]
    except KeyError:
        return Answer(Outcome.CANNOT_ANSWER, reason="recurrence public value is absent")
    if (
        source.value.public_instance != source_public
        or target.value.public_instance != target_public
    ):
        return Answer(Outcome.REFUSED, reason="private handoff and public recurrence differ")
    checked = CheckedCausalStepRecurrence(
        question,
        grounding.value,
        invocation.runs[0],
        invocation.runs[1],
        source,
        target,
    )
    _QUALIFIED_CAUSAL_STEP_RESULTS[id(checked)] = checked
    return affirmative(checked)


class RelationsCheckedResultFamily(str, Enum):
    CAUSAL_STEP_RECURRENCE = "causal-plan-step-recurrence-result"
    BINDING_COVERAGE = "recursion-binding-coverage-result"
    CYCLEFOLD_SAME_STEP = "cyclefold-same-step-grounding-result"


@dataclass(eq=False, frozen=True)
class OwnerLocalRelationsResultBinding:
    family: RelationsCheckedResultFamily
    question_coordinate_id: str
    result: object
    consumer_id: str
    purpose_id: str
    payload_id: str
    requirement_id: str
    policy_closure_id: str


@dataclass(eq=False, frozen=True)
class RelationsResultSourceCapability:
    binding: OwnerLocalRelationsResultBinding


@dataclass(frozen=True)
class IssuedRelationsResultSource:
    binding: OwnerLocalRelationsResultBinding
    capability: RelationsResultSourceCapability


_ISSUED_RELATIONS_RESULT_BINDINGS: dict[int, OwnerLocalRelationsResultBinding] = {}
_ISSUED_RELATIONS_RESULT_CAPABILITIES: dict[int, RelationsResultSourceCapability] = {}


def _issue_relations_result_source(
    family: RelationsCheckedResultFamily,
    question_coordinate_id: str,
    result: object,
    consumer_id: str,
    purpose_id: str,
) -> Answer:
    if not all((question_coordinate_id, consumer_id, purpose_id)):
        return Answer(Outcome.MALFORMED, reason="result source coordinate is incomplete")
    payload = {
        "owner_domain": "relations",
        "family": family.value,
        "question_coordinate_id": question_coordinate_id,
        "manifest": "CompleteResult",
        "consumer_id": consumer_id,
        "purpose_id": purpose_id,
    }
    payload_id = semantic_id("relations.source-binding-payload", payload)
    requirement_id = semantic_id(
        "relations.source-capability-requirement",
        {
            "family": family.value,
            "payload_id": payload_id,
            "consumer_id": consumer_id,
            "purpose_id": purpose_id,
        },
    )
    closure_id = semantic_id(
        "relations.source-policy-closure",
        {"family": family.value, "payload_id": payload_id, "requirement_id": requirement_id},
    )
    binding = OwnerLocalRelationsResultBinding(
        family,
        question_coordinate_id,
        result,
        consumer_id,
        purpose_id,
        payload_id,
        requirement_id,
        closure_id,
    )
    capability = RelationsResultSourceCapability(binding)
    _ISSUED_RELATIONS_RESULT_BINDINGS[id(binding)] = binding
    _ISSUED_RELATIONS_RESULT_CAPABILITIES[id(capability)] = capability
    return affirmative(IssuedRelationsResultSource(binding, capability))


def issue_causal_step_recurrence_result_source(
    result: CheckedCausalStepRecurrence,
    consumer_id: str,
    purpose_id: str,
) -> Answer:
    if _QUALIFIED_CAUSAL_STEP_RESULTS.get(id(result)) is not result:
        return Answer(Outcome.REFUSED, reason="causal recurrence result is not owner-qualified")
    return _issue_relations_result_source(
        RelationsCheckedResultFamily.CAUSAL_STEP_RECURRENCE,
        result.question.identity,
        result,
        consumer_id,
        purpose_id,
    )


def issue_binding_coverage_result_source(
    result: CheckedBindingCoverage,
    consumer_id: str,
    purpose_id: str,
) -> Answer:
    if _QUALIFIED_BINDING_COVERAGE_RESULTS.get(id(result)) is not result:
        return Answer(Outcome.REFUSED, reason="coverage result is not owner-qualified")
    return _issue_relations_result_source(
        RelationsCheckedResultFamily.BINDING_COVERAGE,
        result.schema_id,
        result,
        consumer_id,
        purpose_id,
    )


def issue_cyclefold_same_step_result_source(
    result: CheckedCycleFoldSameStepBinding,
    question_coordinate_id: str,
    consumer_id: str,
    purpose_id: str,
) -> Answer:
    if _QUALIFIED_CYCLEFOLD_RESULTS.get(id(result)) is not result:
        return Answer(Outcome.REFUSED, reason="CycleFold result is not owner-qualified")
    expected_coordinate = semantic_id(
        "relations.cyclefold-same-step-grounding-question",
        {"step_id": result.step_id},
    )
    if question_coordinate_id != expected_coordinate:
        return Answer(Outcome.REFUSED, reason="CycleFold question coordinate differs")
    return _issue_relations_result_source(
        RelationsCheckedResultFamily.CYCLEFOLD_SAME_STEP,
        question_coordinate_id,
        result,
        consumer_id,
        purpose_id,
    )


@dataclass(frozen=True)
class CompositionStepResultManifest:
    recurrence_question_coordinate_id: str
    coverage_question_coordinate_id: str
    source_profile_id: str = "analysis.incremental-composition-step-relations-results.v0"
    purpose_id: str = "analysis.incremental-composition.occurrence-evidence"

    @property
    def identity(self) -> str:
        return semantic_id("analysis.semantic-read-manifest", self)


@dataclass(eq=False, frozen=True)
class LocalCompositionStepSourceSupport:
    manifest: CompositionStepResultManifest
    recurrence_source: IssuedRelationsResultSource
    coverage_source: IssuedRelationsResultSource


_QUALIFIED_LOCAL_COMPOSITION_SUPPORTS: dict[int, LocalCompositionStepSourceSupport] = {}


def bind_composition_step_result_support(
    manifest: CompositionStepResultManifest,
    recurrence_source: IssuedRelationsResultSource,
    coverage_source: IssuedRelationsResultSource,
) -> Answer:
    expected = (
        (
            recurrence_source,
            RelationsCheckedResultFamily.CAUSAL_STEP_RECURRENCE,
            manifest.recurrence_question_coordinate_id,
        ),
        (
            coverage_source,
            RelationsCheckedResultFamily.BINDING_COVERAGE,
            manifest.coverage_question_coordinate_id,
        ),
    )
    for issued, family, coordinate in expected:
        binding = issued.binding
        capability = issued.capability
        if (
            _ISSUED_RELATIONS_RESULT_BINDINGS.get(id(binding)) is not binding
            or _ISSUED_RELATIONS_RESULT_CAPABILITIES.get(id(capability)) is not capability
            or capability.binding is not binding
            or binding.family is not family
            or binding.question_coordinate_id != coordinate
            or binding.consumer_id != manifest.identity
            or binding.purpose_id != manifest.purpose_id
        ):
            return Answer(Outcome.REFUSED, reason="Relations result source does not match manifest")
    support = LocalCompositionStepSourceSupport(
        manifest,
        recurrence_source,
        coverage_source,
    )
    _QUALIFIED_LOCAL_COMPOSITION_SUPPORTS[id(support)] = support
    return affirmative(support)


@dataclass(frozen=True)
class CycleFoldResultManifest:
    question_coordinate_id: str
    source_profile_id: str = "analysis.incremental-composition-cyclefold-result.v0"
    purpose_id: str = "analysis.incremental-composition.occurrence-evidence"

    @property
    def identity(self) -> str:
        return semantic_id("analysis.semantic-read-manifest", self)


@dataclass(eq=False, frozen=True)
class LocalCycleFoldSourceSupport:
    manifest: CycleFoldResultManifest
    result_source: IssuedRelationsResultSource


def bind_cyclefold_result_support(
    manifest: CycleFoldResultManifest,
    result_source: IssuedRelationsResultSource,
) -> Answer:
    binding = result_source.binding
    capability = result_source.capability
    if (
        _ISSUED_RELATIONS_RESULT_BINDINGS.get(id(binding)) is not binding
        or _ISSUED_RELATIONS_RESULT_CAPABILITIES.get(id(capability)) is not capability
        or capability.binding is not binding
        or binding.family is not RelationsCheckedResultFamily.CYCLEFOLD_SAME_STEP
        or binding.question_coordinate_id != manifest.question_coordinate_id
        or binding.consumer_id != manifest.identity
        or binding.purpose_id != manifest.purpose_id
    ):
        return Answer(Outcome.REFUSED, reason="CycleFold source does not match manifest")
    return affirmative(LocalCycleFoldSourceSupport(manifest, result_source))


# ---------------------------------------------------------------------------
# Analysis theorem application and finite live-chain non-aliasing


class ExperimentModel(str, Enum):
    STANDARD = "StandardModel"
    RANDOM_ORACLE = "RandomOracleModel"


class CompositionTopology(str, Enum):
    PATH = "Path"
    FINITE_IN_DEGREE_DAG = "FiniteInDegreeDag"


class ExecutionDepthDomain(str, Enum):
    EXACT_FINITE_PREFIX = "ExactFinitePrefix"
    POLYNOMIAL_IN_SECURITY_PARAMETER = "PolynomialInSecurityParameter"
    ALL_NATURAL_DEPTHS = "AllNaturalDepths"


class CompliancePredicateDepthDomain(str, Enum):
    CONSTANT_DEPTH = "ConstantDepth"
    EXPLICIT_BOUND = "ExplicitBound"
    POLYNOMIAL_DEPTH = "PolynomialDepth"


class ContinuationQuantifier(str, Enum):
    SAME_PROCESS_ACCEPTED_HANDOFF = "SameProcessAcceptedHandoff"
    ANY_ELIGIBLE_PROVER = "AnyEligibleProver"
    OUTSOURCED_FINAL_DECIDER = "OutsourcedFinalDecider"


class ConclusionKind(str, Enum):
    COMPLETENESS = "Completeness"
    KNOWLEDGE_SOUNDNESS = "KnowledgeSoundness"
    EFFICIENCY = "Efficiency"


class TheoremTruthTreatment(str, Enum):
    ESTABLISHED = "Established"
    RETAINED_ASSUMPTION = "RetainedAssumption"


@dataclass(frozen=True)
class CarriedObligationBinding:
    hypothesis_goal_id: str
    member_key: str
    slot_ordinal: int
    public_coordinate: str
    discharge_operation_id: str


@dataclass(frozen=True)
class IncrementalCompositionTheoremSchema:
    family_id: str
    topology: CompositionTopology
    maximum_predecessors: int
    execution_depth_domain: ExecutionDepthDomain
    execution_depth_bound_id: str | None
    compliance_predicate_depth_domain: CompliancePredicateDepthDomain
    compliance_depth_bound_id: str | None
    model: ExperimentModel
    continuation_quantifier: ContinuationQuantifier
    update_verifier_contract_id: str
    final_decider_contract_id: str
    recurrence_and_coverage_premise_ids: tuple[str, ...]
    digest_binding_rule_ids: tuple[str, ...]
    required_assumption_ids: tuple[str, ...]
    carried_obligation_bindings: tuple[CarriedObligationBinding, ...]
    conclusion_kinds: tuple[ConclusionKind, ...]

    @property
    def identity(self) -> str:
        return semantic_id("analysis.theorem-schema", self)


@dataclass(frozen=True)
class TheoremSourceValidation:
    theorem_schema_id: str
    source_validation_id: str
    truth_treatment: TheoremTruthTreatment


@dataclass(frozen=True)
class IncrementalCompositionJudgment:
    judgment_id: str
    conclusion_kind: ConclusionKind
    retained_hypotheses: tuple[str, ...]
    outstanding_carried_obligations: tuple[OutstandingCompositionObligation, ...]


@dataclass(frozen=True)
class AppliedIncrementalCompositionTheorem:
    semantic_basis_id: str
    support_instantiation_id: str
    validation_basis_id: str
    judgments: tuple[IncrementalCompositionJudgment, ...]


def apply_incremental_composition_theorem(
    family: IncrementalCompositionFamily,
    family_check: CheckedIncrementalCompositionFamily,
    schema: IncrementalCompositionTheoremSchema,
    source_validation: TheoremSourceValidation,
) -> Answer:
    if (
        _QUALIFIED_FAMILY_CHECKS.get(id(family_check)) is not family_check
        or family_check.family_id != family.identity
        or schema.family_id != family.identity
    ):
        return Answer(Outcome.REFUSED, reason="family qualification or theorem coordinate differs")
    if source_validation.theorem_schema_id != schema.identity:
        return Answer(Outcome.REFUSED, reason="theorem source validation names another theorem")
    if not source_validation.source_validation_id:
        return Answer(Outcome.MALFORMED, reason="theorem source validation is incomplete")
    if schema.update_verifier_contract_id != family.update_verifier.identity:
        return Answer(Outcome.REFUSED, reason="update-verifier contract differs")
    if schema.final_decider_contract_id != family.final_decider.identity:
        return Answer(Outcome.REFUSED, reason="final-decider contract differs")
    if schema.maximum_predecessors < 1:
        return Answer(Outcome.MALFORMED, reason="maximum predecessor count is not positive")
    if schema.topology is CompositionTopology.PATH and schema.maximum_predecessors != 1:
        return Answer(Outcome.REFUSED, reason="path topology has non-path predecessor arity")
    if (
        schema.execution_depth_domain is ExecutionDepthDomain.EXACT_FINITE_PREFIX
    ) != bool(schema.execution_depth_bound_id):
        return Answer(Outcome.MALFORMED, reason="execution-depth bound shape differs")
    if (
        schema.compliance_predicate_depth_domain
        is CompliancePredicateDepthDomain.EXPLICIT_BOUND
    ) != bool(schema.compliance_depth_bound_id):
        return Answer(Outcome.MALFORMED, reason="compliance-depth bound shape differs")
    if not schema.recurrence_and_coverage_premise_ids:
        return Answer(Outcome.MALFORMED, reason="recurrence and coverage premises are absent")
    if len(set(schema.recurrence_and_coverage_premise_ids)) != len(
        schema.recurrence_and_coverage_premise_ids
    ):
        return Answer(Outcome.MALFORMED, reason="recurrence premises are duplicated")
    if tuple(sorted(schema.required_assumption_ids)) != schema.required_assumption_ids:
        return Answer(Outcome.MALFORMED, reason="theorem assumptions are not canonical")
    if len(set(schema.required_assumption_ids)) != len(schema.required_assumption_ids):
        return Answer(Outcome.MALFORMED, reason="theorem assumptions are duplicated")
    required_family_premises = {
        f"goal:step-recurrence-correspondence:{member.member_key}"
        for member in family.members
    }
    required_family_premises.update(
        f"goal:binding-coverage-correspondence:{member.member_key}"
        for member in family.members
    )
    required_family_premises.update(
        f"goal:family-description-advice-correspondence:{member.member_key}"
        for member in family.members
        if member.family_description_advice is not None
    )
    if not required_family_premises.issubset(
        schema.recurrence_and_coverage_premise_ids
    ):
        return Answer(Outcome.REFUSED, reason="family correspondence premise is absent")
    required_digest_rules = set(schema.digest_binding_rule_ids)
    required_digest_rules.update(
        member.family_description_advice.digest_algorithm_id
        for member in family.members
        if member.family_description_advice is not None
    )
    required_digest_assumptions = {
        f"analysis.hash-binding-assumption:{rule_id}"
        for rule_id in required_digest_rules
    }
    if not required_digest_assumptions.issubset(schema.required_assumption_ids):
        return Answer(Outcome.REFUSED, reason="digest binding assumption is absent")
    if not schema.conclusion_kinds or len(set(schema.conclusion_kinds)) != len(
        schema.conclusion_kinds
    ):
        return Answer(Outcome.MALFORMED, reason="theorem conclusions are duplicated")

    members = {member.member_key: member for member in family.members}
    seen_goals: set[str] = set()
    seen_slots: set[tuple[str, int]] = set()
    obligations: list[OutstandingCompositionObligation] = []
    for binding in schema.carried_obligation_bindings:
        if binding.hypothesis_goal_id in seen_goals:
            return Answer(Outcome.MALFORMED, reason="carried-obligation goal is duplicated")
        slot_key = (binding.member_key, binding.slot_ordinal)
        if slot_key in seen_slots:
            return Answer(Outcome.MALFORMED, reason="carried-obligation slot is duplicated")
        member = members.get(binding.member_key)
        if member is None or not (0 <= binding.slot_ordinal < len(family.carried_obligation_slots)):
            return Answer(Outcome.REFUSED, reason="carried-obligation coordinate is outside the family")
        slot = family.carried_obligation_slots[binding.slot_ordinal]
        if (
            binding.public_coordinate not in member.carried_public_coordinates
            or binding.discharge_operation_id != slot.discharge_operation_id
        ):
            return Answer(Outcome.REFUSED, reason="carried-obligation coordinate or operation differs")
        seen_goals.add(binding.hypothesis_goal_id)
        seen_slots.add(slot_key)
        obligations.append(
            OutstandingCompositionObligation(
                binding.hypothesis_goal_id,
                binding.member_key,
                binding.slot_ordinal,
                binding.public_coordinate,
                binding.discharge_operation_id,
            )
        )

    expected_slots = {
        (member.member_key, slot_ordinal)
        for member in family.members
        if member.predecessor_ingress_keys
        for slot_ordinal in range(len(family.carried_obligation_slots))
    }
    if seen_slots != expected_slots:
        return Answer(Outcome.REFUSED, reason="derived carried-obligation set is not exact")

    retained = list(schema.required_assumption_ids)
    retained.extend(binding.hypothesis_goal_id for binding in schema.carried_obligation_bindings)
    if source_validation.truth_treatment is TheoremTruthTreatment.RETAINED_ASSUMPTION:
        retained.append(f"analysis.theorem-truth:{schema.identity}")
    if len(set(retained)) != len(retained):
        return Answer(Outcome.MALFORMED, reason="theorem hypothesis treatment overlaps")
    retained_hypotheses = tuple(sorted(retained))

    semantic_basis_id = semantic_id(
        "analysis.semantic-basis",
        {"family_id": family.identity, "theorem_schema_id": schema.identity},
    )
    support_instantiation_id = semantic_id(
        "analysis.support-instantiation",
        {
            "semantic_basis_id": semantic_basis_id,
            "retained_hypotheses": retained_hypotheses,
            "premises": schema.recurrence_and_coverage_premise_ids,
        },
    )
    validation_basis_id = semantic_id(
        "analysis.validation-basis",
        {
            "support_instantiation_id": support_instantiation_id,
            "source_validation_id": source_validation.source_validation_id,
        },
    )
    exact_obligations = tuple(obligations)
    judgments = tuple(
        IncrementalCompositionJudgment(
            semantic_id(
                "analysis.judgment-record",
                {
                    "validation_basis_id": validation_basis_id,
                    "conclusion_kind": conclusion.value,
                    "retained_hypotheses": retained_hypotheses,
                },
            ),
            conclusion,
            retained_hypotheses,
            exact_obligations,
        )
        for conclusion in schema.conclusion_kinds
    )
    for obligation in exact_obligations:
        _QUALIFIED_COMPOSITION_OBLIGATIONS[id(obligation)] = obligation
    for judgment in judgments:
        _QUALIFIED_COMPOSITION_JUDGMENTS[id(judgment)] = judgment
    return affirmative(
        AppliedIncrementalCompositionTheorem(
            semantic_basis_id,
            support_instantiation_id,
            validation_basis_id,
            judgments,
        )
    )


@dataclass(eq=False, frozen=True)
class LiveRun:
    label: str


@dataclass(eq=False, frozen=True)
class CheckedLiveRecurrenceEdge:
    source: LiveRun
    target: LiveRun
    checked_label: str


@dataclass(eq=False, frozen=True)
class CheckedFiniteLiveChain:
    edges: tuple[CheckedLiveRecurrenceEdge, ...]


def check_finite_live_chain(edges: tuple[CheckedLiveRecurrenceEdge, ...]) -> Answer:
    if not edges:
        return Answer(Outcome.MALFORMED, reason="live recurrence chain is empty")
    if len({id(edge) for edge in edges}) != len(edges):
        return Answer(Outcome.REFUSED, reason="live recurrence edge is reused")
    for left, right in zip(edges, edges[1:], strict=False):
        if left.target is not right.source:
            return Answer(Outcome.REFUSED, reason="live recurrence chain is not occurrence-adjacent")
    return affirmative(CheckedFiniteLiveChain(edges))


def form_theorem_from_live_chain(_chain: CheckedFiniteLiveChain) -> Answer:
    return Answer(
        Outcome.UNSUPPORTED,
        reason="finite occurrence records cannot form an incremental theorem judgment",
    )
