"""Request-bound Fresh and Fiat--Shamir execution for the finite R2 model."""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
import hashlib
from pathlib import Path
import re
from typing import Any, Iterable

from .frigrind import (
    ActionKind,
    Actor,
    BASE_HASH,
    DEFAULT_RESOURCE_PLAN,
    CoinVector,
    CoreDerivationKind,
    CoreAction,
    ApplicationContext,
    EvaluatorBasis,
    EvaluatorSource,
    ExecutionRequest,
    FailureEffect,
    FreshCoinTape,
    FreshTapeOrigin,
    FixedNoncePlan,
    EXTERNAL_FRESH_HASH,
    Interpretation,
    InputBundle,
    MAX_QUALIFICATION_CAPS,
    NonceSearchPlan,
    ProtocolCore,
    QualificationCaps,
    PredicateKind,
    Provenance,
    ResidualKind,
    ResourcePlan,
    RouteFormula,
    StrategyKind,
    ScenarioVariant,
    TerminalKind,
    TranscriptConstruction,
    admit_scenario,
    base_core,
    fresh_fri_scenario,
    load_fixture,
    load_external_fresh,
    load_invocation,
)
from .terms import (
    CheckResult,
    OutcomeClass,
    TermEncodingError,
    affirmative,
    encode_term,
    semantic_id,
)


_REPO_ROOT = Path(__file__).resolve().parents[3]
_CONTENT_ID = re.compile(r"sha256:[0-9a-f]{64}\Z")
_EVALUATOR_PATHS = (
    "evaluation/r2-protocol-model/r2model/frigrind.py",
    "evaluation/r2-protocol-model/r2model/execution.py",
    "evaluation/r2-protocol-model/r2model/terms.py",
)


class TraceKind(str, Enum):
    STATEMENT = "Statement"
    CHALLENGE = "Challenge"
    MESSAGE = "Message"
    CHECK = "Check"
    ROUTE = "Route"
    RESIDUAL = "Residual"
    TERMINAL = "Terminal"


_TRACE_KIND = {
    ActionKind.STATEMENT: TraceKind.STATEMENT,
    ActionKind.CHALLENGE: TraceKind.CHALLENGE,
    ActionKind.MESSAGE: TraceKind.MESSAGE,
    ActionKind.CHECK: TraceKind.CHECK,
    ActionKind.ROUTE: TraceKind.ROUTE,
    ActionKind.RESIDUAL: TraceKind.RESIDUAL,
}


@dataclass(frozen=True)
class TraceEvent:
    occurrence: str
    kind: TraceKind
    actor: Actor
    value: Any
    origin: Provenance

    def term(self) -> dict[str, Any]:
        value = self.value.value if isinstance(self.value, Enum) else self.value
        return {
            "occurrence": self.occurrence,
            "kind": self.kind.value,
            "actor": self.actor.value,
            "value": value,
            "origin": self.origin.value,
        }


@dataclass(frozen=True)
class StrategyReceipt:
    output_occurrence: str
    strategy_kind: StrategyKind
    visible_reads: tuple[str, ...]
    previews: tuple[str, ...]
    output: int
    resource_count: int

    def term(self) -> dict[str, Any]:
        return {
            "output": self.output_occurrence,
            "strategy": self.strategy_kind.value,
            "visible_reads": list(self.visible_reads),
            "previews": list(self.previews),
            "value": self.output,
            "resource_count": self.resource_count,
        }


@dataclass(frozen=True)
class ResourceUsage:
    nonce_candidates: int
    transcript_events: int
    trace_events: int
    challenge_values: int
    sampler_attempts: int
    hash_queries: int

    def term(self) -> dict[str, int]:
        return {
            "nonce_candidates": self.nonce_candidates,
            "transcript_events": self.transcript_events,
            "trace_events": self.trace_events,
            "challenge_values": self.challenge_values,
            "sampler_attempts": self.sampler_attempts,
            "hash_queries": self.hash_queries,
        }


@dataclass(frozen=True)
class QualificationUsage:
    dependency_executions: int
    nonce_candidates: int
    transcript_events: int
    trace_events: int
    challenge_values: int
    sampler_attempts: int
    hash_queries: int

    def term(self) -> dict[str, int]:
        return {
            "dependency_executions": self.dependency_executions,
            "nonce_candidates": self.nonce_candidates,
            "transcript_events": self.transcript_events,
            "trace_events": self.trace_events,
            "challenge_values": self.challenge_values,
            "sampler_attempts": self.sampler_attempts,
            "hash_queries": self.hash_queries,
        }


@dataclass(frozen=True)
class ExecutionRecord:
    interpretation: Interpretation
    core_id: str
    scenario_id: str
    request_id: str
    evaluator_basis_id: str
    events: tuple[TraceEvent, ...]
    receipts: tuple[StrategyReceipt, ...]
    disposition: TerminalKind
    usage: ResourceUsage

    @property
    def identity(self) -> str:
        return semantic_id(
            "r2.execution-record.v3",
            {
                "interpretation": self.interpretation.value,
                "core": self.core_id,
                "scenario": self.scenario_id,
                "request": self.request_id,
                "evaluator_basis": self.evaluator_basis_id,
                "events": [event.term() for event in self.events],
                "receipts": [receipt.term() for receipt in self.receipts],
                "disposition": self.disposition.value,
                "usage": self.usage.term(),
            },
        )

    def term(self, include_trace: bool = True) -> dict[str, Any]:
        result: dict[str, Any] = {
            "id": self.identity,
            "interpretation": self.interpretation.value,
            "core_id": self.core_id,
            "scenario_id": self.scenario_id,
            "request_id": self.request_id,
            "evaluator_basis_id": self.evaluator_basis_id,
            "disposition": self.disposition.value,
            "usage": self.usage.term(),
            "receipts": [receipt.term() for receipt in self.receipts],
        }
        if include_trace:
            result["events"] = [event.term() for event in self.events]
        return result

    def challenge_values(self) -> dict[str, tuple[int, ...]]:
        return {
            event.occurrence: tuple(int(value) for value in event.value)
            for event in self.events
            if event.kind is TraceKind.CHALLENGE
        }

    def prover_value(self, label_or_occurrence: str) -> int:
        occurrence = (
            label_or_occurrence
            if label_or_occurrence.startswith("message:")
            else f"message:{label_or_occurrence}"
        )
        for event in self.events:
            if event.kind is TraceKind.MESSAGE and event.occurrence == occurrence:
                return int(event.value)
        raise KeyError(label_or_occurrence)


@dataclass(frozen=True)
class QualifiedExecution:
    request: ExecutionRequest
    evaluator_basis: EvaluatorBasis
    record: ExecutionRecord
    dependencies: tuple["QualifiedExecution", ...] = ()
    usage: QualificationUsage | None = None

    @property
    def identity(self) -> str:
        return semantic_id(
            "r2.qualified-execution.v3",
            {
                "request": self.request.identity,
                "evaluator_basis": self.evaluator_basis.identity,
                "record": self.record.identity,
                "law": self.evaluator_basis.qualification_law,
                "dependencies": [dependency.identity for dependency in self.dependencies],
                "qualification_usage": self.usage.term() if self.usage else None,
            },
        )


class _ExecutionFailure(Exception):
    def __init__(self, result: CheckResult) -> None:
        super().__init__(result.detail)
        self.result = result


def _result(outcome: OutcomeClass, boundary: str, code: str, detail: str) -> CheckResult:
    return CheckResult(outcome, boundary, code, detail)


def _positive_int(value: Any) -> bool:
    return not isinstance(value, bool) and isinstance(value, int) and value > 0


def _valid_id(value: Any) -> bool:
    return isinstance(value, str) and _CONTENT_ID.fullmatch(value) is not None


def _bounded_text(value: Any, limit: int = 256) -> bool:
    if not isinstance(value, str) or not value:
        return False
    try:
        return len(value.encode("utf-8")) <= limit
    except UnicodeEncodeError:
        return False


def _resource_values(plan: ResourcePlan) -> tuple[int, ...]:
    return (
        plan.max_nonce_candidates,
        plan.max_transcript_events,
        plan.max_trace_events,
        plan.max_challenge_values,
        plan.max_sampler_retries_per_value,
        plan.max_hash_queries,
    )


def _qualification_cap_values(caps: QualificationCaps) -> tuple[int, ...]:
    return (
        caps.max_dependency_executions,
        caps.max_total_nonce_candidates,
        caps.max_total_transcript_events,
        caps.max_total_trace_events,
        caps.max_total_challenge_values,
        caps.max_total_sampler_attempts,
        caps.max_total_hash_queries,
    )


def _admit_basis(basis: EvaluatorBasis) -> CheckResult | None:
    if (
        not isinstance(basis, EvaluatorBasis)
        or not isinstance(basis.hard_caps, ResourcePlan)
        or not isinstance(basis.qualification_caps, QualificationCaps)
    ):
        return _result(OutcomeClass.MALFORMED, "evaluator-basis", "R2-EVAL-001", "evaluator basis has the wrong type")
    if basis.qualification_law != "r2.exact-request-reexecution.v1":
        return _result(OutcomeClass.UNSUPPORTED, "evaluator-basis", "R2-EVAL-002", "qualification law is unsupported")
    if (
        not isinstance(basis.supported_construction_ids, tuple)
        or not basis.supported_construction_ids
        or len(basis.supported_construction_ids) > 8
        or any(not _valid_id(value) for value in basis.supported_construction_ids)
        or tuple(sorted(set(basis.supported_construction_ids))) != basis.supported_construction_ids
    ):
        return _result(OutcomeClass.MALFORMED, "evaluator-basis", "R2-EVAL-003", "construction support set is malformed")
    if any(not _positive_int(value) for value in _resource_values(basis.hard_caps)):
        return _result(OutcomeClass.MALFORMED, "evaluator-basis", "R2-EVAL-004", "hard caps are malformed")
    if any(
        left > right
        for left, right in zip(
            _resource_values(basis.hard_caps),
            _resource_values(DEFAULT_RESOURCE_PLAN),
            strict=True,
        )
    ):
        return _result(OutcomeClass.RESOURCE_EXCEEDED, "evaluator-basis", "R2-EVAL-008", "hard caps exceed the implementation ceiling")
    if (
        any(not _positive_int(value) for value in _qualification_cap_values(basis.qualification_caps))
        or any(
            left > right
            for left, right in zip(
                _qualification_cap_values(basis.qualification_caps),
                _qualification_cap_values(MAX_QUALIFICATION_CAPS),
                strict=True,
            )
        )
    ):
        return _result(OutcomeClass.RESOURCE_EXCEEDED, "evaluator-basis", "R2-EVAL-009", "qualification caps exceed the implementation ceiling")
    if (
        not isinstance(basis.source_digests, tuple)
        or len(basis.source_digests) != len(_EVALUATOR_PATHS)
        or any(not isinstance(source, EvaluatorSource) for source in basis.source_digests)
    ):
        return _result(OutcomeClass.MALFORMED, "evaluator-basis", "R2-EVAL-005", "evaluator source set is malformed")
    if tuple(source.relative_path for source in basis.source_digests) != _EVALUATOR_PATHS:
        return _result(OutcomeClass.MISMATCH, "evaluator-basis", "R2-EVAL-005", "evaluator source set differs")
    for source in basis.source_digests:
        if not isinstance(source.sha256, str) or re.fullmatch(r"[0-9a-f]{64}", source.sha256) is None:
            return _result(OutcomeClass.MALFORMED, "evaluator-basis", "R2-EVAL-006", "evaluator digest is malformed")
        path = _REPO_ROOT / source.relative_path
        if (
            not path.is_file()
            or path.stat().st_size > 1 << 20
            or hashlib.sha256(path.read_bytes()).hexdigest() != source.sha256
        ):
            return _result(OutcomeClass.MISMATCH, "evaluator-basis", "R2-EVAL-007", "evaluator source digest differs")
    return None


def _retry_bound(cardinality: int, plan: ResourcePlan) -> int:
    return 1 if (1 << 256) % cardinality == 0 else plan.max_sampler_retries_per_value


def worst_case_usage(request: ExecutionRequest) -> ResourceUsage | CheckResult:
    if not isinstance(request, ExecutionRequest) or not isinstance(request.resources, ResourcePlan):
        return _result(OutcomeClass.MALFORMED, "execution-resource", "R2-REQ-001", "request resources have the wrong type")
    if (
        not isinstance(request.scenario, ScenarioVariant)
        or not isinstance(request.scenario.core, ProtocolCore)
        or not isinstance(request.scenario.interpretation, Interpretation)
    ):
        return _result(OutcomeClass.MALFORMED, "execution-resource", "R2-REQ-002", "request scenario has the wrong type")
    if any(not _positive_int(value) for value in _resource_values(request.resources)):
        return _result(OutcomeClass.MALFORMED, "execution-resource", "R2-REQ-004", "request caps are malformed")
    scenario_result = admit_scenario(request.scenario)
    if scenario_result.outcome is not OutcomeClass.AFFIRMATIVE:
        return _result(OutcomeClass.MISSING_DEPENDENCY, "execution-resource", "R2-REQ-027", "worst-case accounting requires an admitted scenario")
    core = request.scenario.core
    challenge_values = sum(action.count for action in core.challenge_actions)
    trace_events = len(core.actions)
    nonce_candidates = 0
    transcript_events = 0
    sampler_attempts = 0
    hash_queries = 0
    if request.scenario.interpretation is Interpretation.FS:
        construction = request.scenario.construction
        if not isinstance(construction, TranscriptConstruction):
            return _result(OutcomeClass.MALFORMED, "execution-resource", "R2-REQ-002", "FS construction is absent")
        transcript_events = len(construction.absorb_order)
        sampler_attempts = sum(
            action.count * _retry_bound(action.cardinality or 1, request.resources)
            for action in core.challenge_actions
        )
        hash_queries = 1 + transcript_events + sampler_attempts
        if core.includes_grinding:
            plan = request.nonce_search
            if (
                not isinstance(plan, NonceSearchPlan)
                or isinstance(plan.start, bool)
                or not isinstance(plan.start, int)
                or isinstance(plan.limit, bool)
                or not isinstance(plan.limit, int)
                or plan.start < 0
                or plan.limit <= plan.start
                or plan.limit > 1 << 64
            ):
                return _result(OutcomeClass.MALFORMED, "execution-resource", "R2-REQ-003", "nonce search plan is malformed")
            nonce_candidates = plan.limit - plan.start
            pow_action = core.action("challenge:pow")
            preview_attempts = pow_action.count * _retry_bound(pow_action.cardinality or 1, request.resources)
            sampler_attempts += nonce_candidates * preview_attempts
            hash_queries += nonce_candidates * (1 + preview_attempts)
    return ResourceUsage(
        nonce_candidates,
        transcript_events,
        trace_events,
        challenge_values,
        sampler_attempts,
        hash_queries,
    )


def _check_resource_bounds(
    request: ExecutionRequest,
    basis: EvaluatorBasis,
) -> CheckResult | None:
    plan = request.resources
    if any(not _positive_int(value) for value in _resource_values(plan)):
        return _result(OutcomeClass.MALFORMED, "execution-resource", "R2-REQ-004", "request caps are malformed")
    if any(left > right for left, right in zip(_resource_values(plan), _resource_values(basis.hard_caps), strict=True)):
        return _result(OutcomeClass.RESOURCE_EXCEEDED, "execution-resource", "R2-REQ-005", "request cap exceeds evaluator hard cap")
    usage = worst_case_usage(request)
    if isinstance(usage, CheckResult):
        return usage
    limits = (
        plan.max_nonce_candidates,
        plan.max_transcript_events,
        plan.max_trace_events,
        plan.max_challenge_values,
        plan.max_sampler_retries_per_value * max(1, plan.max_challenge_values + plan.max_nonce_candidates),
        plan.max_hash_queries,
    )
    actual = (
        usage.nonce_candidates,
        usage.transcript_events,
        usage.trace_events,
        usage.challenge_values,
        usage.sampler_attempts,
        usage.hash_queries,
    )
    if any(value > limit for value, limit in zip(actual, limits, strict=True)):
        return _result(OutcomeClass.RESOURCE_EXCEEDED, "execution-resource", "R2-REQ-006", "aggregate worst-case work exceeds request cap")
    return None


def _admit_tape(request: ExecutionRequest) -> CheckResult | None:
    tape = request.coin_tape
    if not isinstance(tape, FreshCoinTape) or not isinstance(tape.origin, FreshTapeOrigin):
        return _result(OutcomeClass.MALFORMED, "fresh-coin-tape", "R2-REQ-007", "Fresh coin tape has the wrong type")
    if not _valid_id(tape.source_id):
        return _result(OutcomeClass.MALFORMED, "fresh-coin-tape", "R2-REQ-008", "Fresh tape source identity is malformed")
    if tape.origin is FreshTapeOrigin.EXTERNAL_FIXTURE:
        if tape.dependency_execution_id is not None or tape.source_id != f"sha256:{EXTERNAL_FRESH_HASH}":
            return _result(OutcomeClass.MISMATCH, "fresh-coin-tape", "R2-REQ-009", "external support-point tape has an execution dependency")
        try:
            expected_tape, expected_nonce = load_external_fresh(_REPO_ROOT, request.scenario.core)
        except (OSError, TypeError, ValueError) as error:
            return _result(OutcomeClass.MISSING_DEPENDENCY, "fresh-coin-tape", "R2-REQ-028", f"external support-point tape source cannot be reconstructed: {error}")
        if tape != expected_tape or request.fixed_nonce != expected_nonce:
            return _result(OutcomeClass.MISMATCH, "fresh-coin-tape", "R2-REQ-029", "external support-point tape or fixed nonce differs from the frozen source")
    elif not _valid_id(tape.dependency_execution_id) or tape.source_id != tape.dependency_execution_id:
        return _result(OutcomeClass.MISMATCH, "fresh-coin-tape", "R2-REQ-010", "coupled tape dependency is not exact")
    expected = request.scenario.core.challenge_actions
    if (
        not isinstance(tape.vectors, tuple)
        or len(tape.vectors) != len(expected)
        or any(not isinstance(vector, CoinVector) for vector in tape.vectors)
        or tuple(vector.challenge_occurrence for vector in tape.vectors)
        != tuple(action.occurrence for action in expected)
    ):
        return _result(OutcomeClass.MISMATCH, "fresh-coin-tape", "R2-REQ-011", "Fresh tape slot set or order differs")
    for action, vector in zip(expected, tape.vectors, strict=True):
        if (
            not isinstance(vector.values, tuple)
            or len(vector.values) != action.count
            or action.cardinality is None
            or any(
                isinstance(value, bool) or not isinstance(value, int)
                or value < 0 or value >= action.cardinality
                for value in vector.values
            )
        ):
            return _result(OutcomeClass.MALFORMED, "fresh-coin-tape", "R2-REQ-012", "Fresh tape value is outside its slot")
    return None


def _admit_coin_dependencies(
    request: ExecutionRequest,
    dependencies: tuple[QualifiedExecution, ...],
) -> CheckResult | None:
    if (
        not isinstance(dependencies, tuple)
        or len(dependencies) > 1
        or any(
        not isinstance(dependency, QualifiedExecution) for dependency in dependencies
        )
    ):
        return _result(OutcomeClass.MALFORMED, "fresh-coin-coupling", "R2-COUPLE-002", "execution dependency set is malformed")
    tape = request.coin_tape
    if request.scenario.interpretation is Interpretation.FS or (
        isinstance(tape, FreshCoinTape)
        and tape.origin is FreshTapeOrigin.EXTERNAL_FIXTURE
    ):
        if dependencies:
            return _result(OutcomeClass.MISMATCH, "fresh-coin-coupling", "R2-COUPLE-003", "execution dependency is inactive")
        return None
    if not isinstance(tape, FreshCoinTape) or tape.origin is not FreshTapeOrigin.DERIVED_EXECUTION:
        return _result(OutcomeClass.MISSING_DEPENDENCY, "fresh-coin-coupling", "R2-COUPLE-004", "derived Fresh tape is absent")
    if len(dependencies) != 1:
        return _result(OutcomeClass.MISSING_DEPENDENCY, "fresh-coin-coupling", "R2-COUPLE-005", "exactly one replay-qualified FS source is required")
    source = dependencies[0]
    if (
        not isinstance(source.dependencies, tuple)
        or source.dependencies
        or not isinstance(source.request, ExecutionRequest)
        or not isinstance(source.record, ExecutionRecord)
        or not isinstance(source.request.scenario, ScenarioVariant)
        or not isinstance(source.request.scenario.core, ProtocolCore)
        or source.record.interpretation is not Interpretation.FS
        or source.record.disposition is not TerminalKind.SOURCE_RESIDUAL
    ):
        return _result(OutcomeClass.MISMATCH, "fresh-coin-coupling", "R2-COUPLE-007", "Fresh tape source binding differs")
    try:
        source_record_id = source.record.identity
        expected_core_id = (
            source.request.scenario.core.identity
            if request.scenario.core.includes_grinding
            else fresh_fri_scenario(source.request.scenario.core).core.identity
        )
    except (AttributeError, TermEncodingError, TypeError, ValueError):
        return _result(OutcomeClass.MALFORMED, "fresh-coin-coupling", "R2-COUPLE-014", "source execution identity is malformed")
    if (
        tape.source_id != source_record_id
        or tape.dependency_execution_id != source_record_id
        or request.scenario.core.identity != expected_core_id
    ):
        return _result(OutcomeClass.MISMATCH, "fresh-coin-coupling", "R2-COUPLE-008", "target Core is not the declared FS projection")
    try:
        available = source.record.challenge_values()
    except (TypeError, ValueError):
        return _result(OutcomeClass.MALFORMED, "fresh-coin-coupling", "R2-COUPLE-006", "source challenge record is malformed")
    try:
        expected_vectors = tuple(
            CoinVector(action.occurrence, available[action.occurrence])
            for action in request.scenario.core.challenge_actions
        )
    except KeyError as error:
        return _result(OutcomeClass.MISSING_DEPENDENCY, "fresh-coin-coupling", "R2-COUPLE-009", f"source challenge is absent: {error}")
    if tape.vectors != expected_vectors:
        return _result(OutcomeClass.MISMATCH, "fresh-coin-coupling", "R2-COUPLE-010", "Fresh tape is not the exact source challenge projection")
    return None


def admit_request(
    request: ExecutionRequest,
    basis: EvaluatorBasis,
    dependencies: tuple[QualifiedExecution, ...] = (),
) -> CheckResult:
    if not isinstance(request, ExecutionRequest):
        return _result(OutcomeClass.MALFORMED, "execution-request", "R2-REQ-000", "request has the wrong type")
    basis_failure = _admit_basis(basis)
    if basis_failure:
        return basis_failure
    if (
        not isinstance(request.scenario, ScenarioVariant)
        or not isinstance(request.inputs, InputBundle)
        or not isinstance(request.application_context, ApplicationContext)
        or not isinstance(request.resources, ResourcePlan)
        or not isinstance(request.core_derivation, CoreDerivationKind)
    ):
        return _result(OutcomeClass.MALFORMED, "execution-request", "R2-REQ-013", "request components are malformed")
    scenario_result = admit_scenario(request.scenario)
    if scenario_result.outcome is not OutcomeClass.AFFIRMATIVE:
        return _result(OutcomeClass.MISSING_DEPENDENCY, "execution-request", "R2-REQ-014", "request scenario is not admitted")
    if request.evaluator_basis_id != basis.identity:
        return _result(OutcomeClass.MISMATCH, "execution-request", "R2-REQ-015", "request evaluator basis differs")
    if request.scenario.construction.identity not in basis.supported_construction_ids:
        return _result(OutcomeClass.UNSUPPORTED, "execution-request", "R2-REQ-016", "scenario construction is unsupported by evaluator")
    if (
        not isinstance(request.application_context.domain, str)
        or not request.application_context.domain
        or not isinstance(request.application_context.session, str)
        or not request.application_context.session
    ):
        return _result(OutcomeClass.MALFORMED, "execution-request", "R2-REQ-017", "application context is malformed")
    if not _bounded_text(request.application_context.domain) or not _bounded_text(request.application_context.session):
        return _result(OutcomeClass.RESOURCE_EXCEEDED, "execution-request", "R2-REQ-026", "application context exceeds the identity-text bound")
    statement = request.inputs.statement_value
    if (
        isinstance(statement, bool) or not isinstance(statement, int)
        or statement < 0 or statement >= request.scenario.field
        or request.inputs.base_prover_input is not StrategyKind.COPY_STATEMENT
    ):
        return _result(OutcomeClass.MALFORMED, "execution-request:inputs", "R2-REQ-018", "input bundle is outside the Core domain")
    try:
        source_fixture = load_fixture(_REPO_ROOT)
        source_package = load_invocation(_REPO_ROOT)
        canonical_grinding = base_core(source_fixture)
        canonical_core_id = (
            canonical_grinding.identity
            if request.scenario.core.includes_grinding
            else fresh_fri_scenario(canonical_grinding).core.identity
        )
    except (OSError, TypeError, ValueError) as error:
        return _result(OutcomeClass.MISSING_DEPENDENCY, "execution-request:source", "R2-REQ-030", f"source package cannot be reconstructed: {error}")
    if (
        request.source_fixture_id != f"sha256:{BASE_HASH}"
        or request.source_package_id != source_package.identity
        or request.inputs != source_package.input_bundle
        or request.scenario.core.identity != canonical_core_id
        or request.core_derivation
        is not (
            CoreDerivationKind.FIXTURE_GRINDING_CORE
            if request.scenario.core.includes_grinding
            else CoreDerivationKind.DROP_GRINDING_PROJECTION
        )
    ):
        return _result(OutcomeClass.MISMATCH, "execution-request:source", "R2-REQ-019", "source binding differs")
    if request.scenario.interpretation is Interpretation.FS:
        if request.coin_tape is not None or request.fixed_nonce is not None:
            return _result(OutcomeClass.MALFORMED, "execution-request", "R2-REQ-020", "FS request contains Fresh-only controls")
        if request.scenario.includes_grinding:
            plan = request.nonce_search
            if (
                not isinstance(plan, NonceSearchPlan)
                or isinstance(plan.start, bool) or not isinstance(plan.start, int)
                or isinstance(plan.limit, bool) or not isinstance(plan.limit, int)
                or plan.start < 0 or plan.limit <= plan.start or plan.limit > 1 << 64
            ):
                return _result(OutcomeClass.MALFORMED, "execution-request:nonce-search", "R2-REQ-021", "nonce search interval is malformed")
        elif request.nonce_search is not None:
            return _result(OutcomeClass.MALFORMED, "execution-request", "R2-REQ-022", "inactive FS nonce state is present")
    else:
        if request.nonce_search is not None:
            return _result(OutcomeClass.MALFORMED, "execution-request", "R2-REQ-023", "Fresh request contains FS search state")
        tape_failure = _admit_tape(request)
        if tape_failure:
            return tape_failure
        if request.scenario.includes_grinding:
            nonce = request.fixed_nonce.nonce if isinstance(request.fixed_nonce, FixedNoncePlan) else None
            if isinstance(nonce, bool) or not isinstance(nonce, int) or nonce < 0 or nonce >= 1 << 64:
                return _result(OutcomeClass.MALFORMED, "execution-request:fixed-nonce", "R2-REQ-024", "Fresh fixed nonce is malformed")
        elif request.fixed_nonce is not None:
            return _result(OutcomeClass.MALFORMED, "execution-request", "R2-REQ-025", "inactive Fresh nonce state is present")
    resource_failure = _check_resource_bounds(request, basis)
    if resource_failure:
        return resource_failure
    dependency_failure = _admit_coin_dependencies(request, dependencies)
    if dependency_failure:
        return dependency_failure
    return affirmative(
        "execution-request", "R2-REQ-100", "closed execution request admitted",
        request_id=request.identity, evaluator_basis_id=basis.identity,
    )


def _vector(codec: Any, values: Iterable[int]) -> bytes:
    encoded = [codec.encode(int(value)) for value in values]
    return len(encoded).to_bytes(8, "big") + b"".join(
        len(value).to_bytes(8, "big") + value for value in encoded
    )


class _Transcript:
    def __init__(self, request: ExecutionRequest) -> None:
        construction = request.scenario.construction
        assert isinstance(construction, TranscriptConstruction)
        self.request = request
        self.construction = construction
        self.state = hashlib.sha256(
            b"zkc-r2-fs-v3\0"
            + encode_term(
                {
                    "core": request.scenario.core.identity,
                    "construction": construction.identity,
                    "application_context": request.application_context.identity,
                }
            )
        ).digest()
        self.transcript_events = 0
        self.sampler_attempts = 0
        self.hash_queries = 1

    def _state_after(self, action: CoreAction, value: Any, encoded: bytes) -> bytes:
        return hashlib.sha256(
            b"O" + self.state + encode_term(
                {
                    "occurrence": action.occurrence,
                    "sort": action.value_sort.value,
                    "value": value,
                    "encoded": encoded,
                }
            )
        ).digest()

    def observe(self, action: CoreAction, value: Any) -> None:
        codec = self.construction.codec_for(action.occurrence)
        encoded = _vector(codec, value) if action.kind is ActionKind.CHALLENGE else codec.encode(int(value))
        self.state = self._state_after(action, value, encoded)
        self.transcript_events += 1
        self.hash_queries += 1

    def _sample(self, state: bytes, action: CoreAction) -> tuple[tuple[int, ...], int]:
        assert action.cardinality is not None and action.namespace is not None
        limit = ((1 << 256) // action.cardinality) * action.cardinality
        values: list[int] = []
        attempts = 0
        for index in range(action.count):
            for retry in range(self.request.resources.max_sampler_retries_per_value):
                digest = hashlib.sha256(
                    b"S" + state + action.namespace.encode("utf-8")
                    + index.to_bytes(8, "big") + retry.to_bytes(8, "big")
                ).digest()
                attempts += 1
                candidate = int.from_bytes(digest, "big")
                if candidate < limit:
                    values.append(candidate % action.cardinality)
                    break
            else:
                raise _ExecutionFailure(
                    _result(OutcomeClass.RESOURCE_EXCEEDED, "execution-resource:sampler", "R2-EXEC-012", "sampler retry bound exhausted")
                )
        return tuple(values), attempts

    def derive(self, action: CoreAction) -> tuple[int, ...]:
        values, attempts = self._sample(self.state, action)
        self.sampler_attempts += attempts
        self.hash_queries += attempts
        self.observe(action, values)
        return values

    def preview(self, message: CoreAction, value: int, challenge: CoreAction) -> tuple[tuple[int, ...], int]:
        codec = self.construction.codec_for(message.occurrence)
        state = self._state_after(message, value, codec.encode(value))
        values, attempts = self._sample(state, challenge)
        return values, attempts


def _event(action: CoreAction, value: Any, origin: Provenance) -> TraceEvent:
    return TraceEvent(action.occurrence, _TRACE_KIND[action.kind], action.actor, value, origin)


def _usage(
    events: list[TraceEvent],
    nonce_candidates: int,
    transcript: _Transcript | None,
    challenge_values: int,
) -> ResourceUsage:
    return ResourceUsage(
        nonce_candidates,
        transcript.transcript_events if transcript else 0,
        len(events),
        challenge_values,
        transcript.sampler_attempts if transcript else 0,
        transcript.hash_queries if transcript else 0,
    )


def _record(
    request: ExecutionRequest,
    basis: EvaluatorBasis,
    events: list[TraceEvent],
    receipts: list[StrategyReceipt],
    disposition: TerminalKind,
    nonce_candidates: int,
    transcript: _Transcript | None,
    challenge_values: int,
) -> ExecutionRecord:
    return ExecutionRecord(
        request.scenario.interpretation,
        request.scenario.core.identity,
        request.scenario.identity,
        request.identity,
        basis.identity,
        tuple(events),
        tuple(receipts),
        disposition,
        _usage(events, nonce_candidates, transcript, challenge_values),
    )


def execute(
    request: ExecutionRequest,
    basis: EvaluatorBasis,
    dependencies: tuple[QualifiedExecution, ...] = (),
) -> ExecutionRecord | CheckResult:
    admitted = admit_request(request, basis, dependencies)
    if admitted.outcome is not OutcomeClass.AFFIRMATIVE:
        return admitted
    scenario = request.scenario
    core = scenario.core
    statement = request.inputs.statement_value
    transcript = _Transcript(request) if scenario.interpretation is Interpretation.FS else None
    events: list[TraceEvent] = []
    receipts: list[StrategyReceipt] = []
    values: dict[str, Any] = {}
    checks: dict[PredicateKind, bool] = {}
    nonce_candidates = 0
    challenge_values = 0
    try:
        for action in core.actions:
            if action.kind is ActionKind.STATEMENT:
                value = statement
                origin = Provenance.INPUT_BUNDLE
                if transcript:
                    transcript.observe(action, value)
            elif action.kind is ActionKind.CHALLENGE:
                if transcript:
                    value = transcript.derive(action)
                    origin = Provenance.TRANSCRIPT_CONSTRUCTION
                else:
                    assert request.coin_tape is not None
                    value = request.coin_tape.values_for(action.occurrence)
                    origin = Provenance.PUBLIC_COIN_TAPE
                challenge_values += len(value)
            elif action.kind is ActionKind.MESSAGE:
                strategy = next(
                    item for item in scenario.strategies
                    if item.output_occurrence == action.occurrence
                )
                if action.occurrence in {"message:g1", "message:post_grind"}:
                    value = statement
                    resource_count = 1
                elif action.occurrence == "message:nonce" and transcript:
                    assert request.nonce_search is not None
                    pow_action = core.action("challenge:pow")
                    value = None
                    preview_attempts = 0
                    for candidate in range(request.nonce_search.start, request.nonce_search.limit):
                        nonce_candidates += 1
                        preview, attempts = transcript.preview(action, candidate, pow_action)
                        preview_attempts += attempts
                        if preview == (0,):
                            value = candidate
                            break
                    transcript.sampler_attempts += preview_attempts
                    transcript.hash_queries += preview_attempts + nonce_candidates
                    if value is None:
                        events.append(
                            TraceEvent(
                                "terminal:nonce_search",
                                TraceKind.TERMINAL,
                                Actor.PROVER,
                                TerminalKind.ABORT,
                                Provenance.PROVER_STRATEGY,
                            )
                        )
                        return _record(
                            request,
                            basis,
                            events,
                            receipts,
                            TerminalKind.ABORT,
                            nonce_candidates,
                            transcript,
                            challenge_values,
                        )
                    resource_count = nonce_candidates
                elif action.occurrence == "message:nonce":
                    assert request.fixed_nonce is not None
                    value = request.fixed_nonce.nonce
                    resource_count = 1
                else:
                    raise _ExecutionFailure(
                        _result(OutcomeClass.UNSUPPORTED, "strategy-generation", "R2-EXEC-019", "message strategy is unsupported")
                    )
                receipts.append(
                    StrategyReceipt(
                        action.occurrence,
                        strategy.kind,
                        strategy.reads,
                        strategy.previews,
                        int(value),
                        resource_count,
                    )
                )
                origin = Provenance.PROVER_STRATEGY
                if transcript:
                    transcript.observe(action, value)
            elif action.kind is ActionKind.CHECK:
                if action.predicate is PredicateKind.POW_ZERO:
                    value = values["challenge:pow"] == (0,)
                elif action.predicate is PredicateKind.ROOT_EQUALS_G1:
                    value = values["statement:f_root"] == values["message:g1"]
                else:
                    raise _ExecutionFailure(
                        _result(OutcomeClass.UNSUPPORTED, "execution-predicate", "R2-EXEC-020", "predicate is unsupported")
                    )
                checks[action.predicate] = value
                origin = Provenance.DETERMINISTIC_VERIFIER
                values[action.occurrence] = value
                events.append(_event(action, value, origin))
                if value is False and action.failure_effect is FailureEffect.REJECT_IMMEDIATELY:
                    events.append(
                        TraceEvent(
                            f"terminal:{action.label}", TraceKind.TERMINAL,
                            Actor.VERIFIER, TerminalKind.REJECT,
                            Provenance.DETERMINISTIC_VERIFIER,
                        )
                    )
                    return _record(
                        request, basis, events, receipts, TerminalKind.REJECT,
                        nonce_candidates, transcript, challenge_values,
                    )
                continue
            elif action.kind is ActionKind.ROUTE:
                root = checks.get(PredicateKind.ROOT_EQUALS_G1, False)
                pow_ok = checks.get(PredicateKind.POW_ZERO, True)
                if action.route_formula is RouteFormula.ROOT_CHECK:
                    value = root
                elif action.route_formula is RouteFormula.ROOT_AND_POW:
                    value = root and pow_ok
                else:
                    raise _ExecutionFailure(
                        _result(OutcomeClass.UNSUPPORTED, "execution-route", "R2-EXEC-022", "route formula is unsupported")
                    )
                origin = Provenance.DETERMINISTIC_VERIFIER
            elif action.kind is ActionKind.RESIDUAL:
                if action.residual is not ResidualKind.FRI_TERMINAL_NOT_MODELED:
                    raise _ExecutionFailure(
                        _result(OutcomeClass.UNSUPPORTED, "source-boundary", "R2-EXEC-023", "residual is unsupported")
                    )
                value = action.residual
                origin = Provenance.WITNESS_LOCAL_MODEL
            else:
                raise _ExecutionFailure(
                    _result(OutcomeClass.UNSUPPORTED, "execution-action", "R2-EXEC-024", "Core action is unsupported")
                )
            values[action.occurrence] = value
            events.append(_event(action, value, origin))
        return _record(
            request, basis, events, receipts, TerminalKind.SOURCE_RESIDUAL,
            nonce_candidates, transcript, challenge_values,
        )
    except _ExecutionFailure as failure:
        return failure.result
    except (AssertionError, KeyError, TypeError, ValueError, OverflowError) as error:
        return _result(OutcomeClass.CHECKER_FAILURE, "execution-evaluator", "R2-EXEC-999", str(error))


def _event_matches_action(
    event: TraceEvent,
    action: CoreAction,
    interpretation: Interpretation,
) -> bool:
    if (
        not isinstance(event, TraceEvent)
        or event.occurrence != action.occurrence
        or event.kind is not _TRACE_KIND[action.kind]
        or event.actor is not action.actor
        or not isinstance(event.origin, Provenance)
    ):
        return False
    expected_origin = {
        ActionKind.STATEMENT: Provenance.INPUT_BUNDLE,
        ActionKind.MESSAGE: Provenance.PROVER_STRATEGY,
        ActionKind.CHECK: Provenance.DETERMINISTIC_VERIFIER,
        ActionKind.ROUTE: Provenance.DETERMINISTIC_VERIFIER,
        ActionKind.RESIDUAL: Provenance.WITNESS_LOCAL_MODEL,
    }.get(action.kind)
    if action.kind is ActionKind.CHALLENGE:
        expected_origin = (
            Provenance.TRANSCRIPT_CONSTRUCTION
            if interpretation is Interpretation.FS
            else Provenance.PUBLIC_COIN_TAPE
        )
    if event.origin is not expected_origin:
        return False
    if action.kind is ActionKind.CHALLENGE:
        return (
            isinstance(event.value, tuple)
            and len(event.value) == action.count
            and action.cardinality is not None
            and all(
                not isinstance(value, bool)
                and isinstance(value, int)
                and 0 <= value < action.cardinality
                for value in event.value
            )
        )
    if action.kind in {ActionKind.STATEMENT, ActionKind.MESSAGE}:
        return (
            not isinstance(event.value, bool)
            and isinstance(event.value, int)
            and action.cardinality is not None
            and 0 <= event.value < action.cardinality
        )
    if action.kind in {ActionKind.CHECK, ActionKind.ROUTE}:
        return isinstance(event.value, bool)
    return event.value is action.residual


def validate_terminal_law(request: ExecutionRequest, record: ExecutionRecord) -> CheckResult:
    if not isinstance(request, ExecutionRequest) or not isinstance(record, ExecutionRecord):
        return _result(OutcomeClass.MALFORMED, "execution-transition", "R2-TERM-001", "terminal-law input has the wrong type")
    if (
        not isinstance(request.scenario, ScenarioVariant)
        or not isinstance(request.scenario.core, ProtocolCore)
        or not isinstance(request.inputs, InputBundle)
        or not isinstance(request.application_context, ApplicationContext)
        or not isinstance(request.resources, ResourcePlan)
        or not isinstance(request.core_derivation, CoreDerivationKind)
        or not _bounded_text(request.application_context.domain)
        or not _bounded_text(request.application_context.session)
        or not _valid_id(request.evaluator_basis_id)
        or not _valid_id(request.source_fixture_id)
        or not _valid_id(request.source_package_id)
        or request.nonce_search is not None
        and not isinstance(request.nonce_search, NonceSearchPlan)
        or request.fixed_nonce is not None
        and not isinstance(request.fixed_nonce, FixedNoncePlan)
        or request.coin_tape is not None
        and not isinstance(request.coin_tape, FreshCoinTape)
    ):
        return _result(OutcomeClass.MALFORMED, "execution-transition", "R2-TERM-013", "terminal-law request vocabulary is malformed")
    scenario_result = admit_scenario(request.scenario)
    if scenario_result.outcome is not OutcomeClass.AFFIRMATIVE:
        return _result(OutcomeClass.MISSING_DEPENDENCY, "execution-transition", "R2-TERM-014", "terminal law requires an admitted scenario")
    try:
        request_id = request.identity
        core_id = request.scenario.core.identity
        scenario_id = request.scenario.identity
    except (AttributeError, TermEncodingError, TypeError, ValueError):
        return _result(OutcomeClass.MALFORMED, "execution-transition", "R2-TERM-015", "terminal-law request identity is malformed")
    if (
        record.request_id != request_id
        or record.core_id != core_id
        or record.scenario_id != scenario_id
        or record.evaluator_basis_id != request.evaluator_basis_id
        or record.interpretation is not request.scenario.interpretation
    ):
        return _result(OutcomeClass.MISMATCH, "execution-transition", "R2-TERM-002", "record binding differs")
    if (
        not isinstance(record.interpretation, Interpretation)
        or not isinstance(record.disposition, TerminalKind)
        or not isinstance(record.events, tuple)
        or any(not isinstance(event, TraceEvent) for event in record.events)
    ):
        return _result(OutcomeClass.MALFORMED, "execution-transition", "R2-TERM-009", "record transition vocabulary is malformed")
    occurrences = tuple(event.occurrence for event in record.events)
    if record.disposition is TerminalKind.SOURCE_RESIDUAL:
        if occurrences != request.scenario.core.schedule:
            return _result(OutcomeClass.MISMATCH, "execution-transition:residual", "R2-TERM-003", "source-residual trace is not the exact Core schedule")
        if any(
            not _event_matches_action(event, action, record.interpretation)
            for event, action in zip(record.events, request.scenario.core.actions, strict=True)
        ):
            return _result(OutcomeClass.MISMATCH, "execution-transition:residual", "R2-TERM-010", "source-residual event semantics differ from the Core")
        if any(
            action.kind is ActionKind.CHECK
            and action.failure_effect is FailureEffect.REJECT_IMMEDIATELY
            and event.value is False
            for event, action in zip(record.events, request.scenario.core.actions, strict=True)
        ):
            return _result(OutcomeClass.MISMATCH, "execution-transition:residual", "R2-TERM-011", "trace continues after a rejecting check")
        last = record.events[-1]
        if last.kind is not TraceKind.RESIDUAL or last.value is not ResidualKind.FRI_TERMINAL_NOT_MODELED:
            return _result(OutcomeClass.MISMATCH, "execution-transition:residual", "R2-TERM-004", "source residual suffix differs")
        return affirmative("execution-transition:residual", "R2-TERM-100", "source residual transition is exact")
    if record.disposition is TerminalKind.ABORT:
        if not record.events:
            return _result(OutcomeClass.MISMATCH, "execution-transition:abort", "R2-TERM-016", "abort terminal is absent")
        terminal = record.events[-1]
        try:
            nonce_index = request.scenario.core.schedule.index("message:nonce")
        except ValueError:
            return _result(OutcomeClass.MISMATCH, "execution-transition:abort", "R2-TERM-017", "abort is outside an FS grinding strategy")
        prefix = record.events[:-1]
        if (
            request.scenario.interpretation is not Interpretation.FS
            or tuple(event.occurrence for event in prefix)
            != request.scenario.core.schedule[:nonce_index]
            or any(
                not _event_matches_action(event, action, record.interpretation)
                for event, action in zip(
                    prefix,
                    request.scenario.core.actions[:nonce_index],
                    strict=True,
                )
            )
            or terminal.occurrence != "terminal:nonce_search"
            or terminal.kind is not TraceKind.TERMINAL
            or terminal.actor is not Actor.PROVER
            or terminal.value is not TerminalKind.ABORT
            or terminal.origin is not Provenance.PROVER_STRATEGY
        ):
            return _result(OutcomeClass.MISMATCH, "execution-transition:abort", "R2-TERM-018", "bounded-strategy abort transition differs")
        return affirmative("execution-transition:abort", "R2-TERM-102", "bounded-strategy abort transition is exact")
    if record.disposition is not TerminalKind.REJECT or not record.events:
        return _result(OutcomeClass.MISMATCH, "execution-transition", "R2-TERM-005", "unsupported disposition")
    terminal = record.events[-1]
    if (
        terminal.kind is not TraceKind.TERMINAL
        or terminal.actor is not Actor.VERIFIER
        or terminal.value is not TerminalKind.REJECT
        or terminal.origin is not Provenance.DETERMINISTIC_VERIFIER
    ):
        return _result(OutcomeClass.MISMATCH, "execution-transition:reject", "R2-TERM-006", "reject terminal is absent or wrong")
    prefix = occurrences[:-1]
    if not prefix or prefix[-1] not in request.scenario.core.schedule:
        return _result(OutcomeClass.MISMATCH, "execution-transition:reject", "R2-TERM-007", "rejecting check is absent")
    index = request.scenario.core.schedule.index(prefix[-1])
    action = request.scenario.core.actions[index]
    if (
        prefix != request.scenario.core.schedule[:index + 1]
        or any(
            not _event_matches_action(event, expected_action, record.interpretation)
            for event, expected_action in zip(
                record.events[:-1],
                request.scenario.core.actions[:index + 1],
                strict=True,
            )
        )
        or action.kind is not ActionKind.CHECK
        or action.failure_effect is not FailureEffect.REJECT_IMMEDIATELY
        or record.events[-2].value is not False
        or terminal.occurrence != f"terminal:{action.label}"
    ):
        return _result(OutcomeClass.MISMATCH, "execution-transition:reject", "R2-TERM-008", "reject suffix is not the exact failed-check effect")
    if any(
        expected_action.kind is ActionKind.CHECK
        and expected_action.failure_effect is FailureEffect.REJECT_IMMEDIATELY
        and event.value is False
        for event, expected_action in zip(
            record.events[:-2],
            request.scenario.core.actions[:index],
            strict=True,
        )
    ):
        return _result(OutcomeClass.MISMATCH, "execution-transition:reject", "R2-TERM-012", "trace passed an earlier rejecting check")
    return affirmative("execution-transition:reject", "R2-TERM-101", "reject transition is exact")


def _qualification_usage(
    target: ResourceUsage,
    dependencies: tuple[QualifiedExecution, ...],
) -> QualificationUsage | CheckResult:
    dependency_usages: list[QualificationUsage] = []
    for dependency in dependencies:
        if not isinstance(dependency.usage, QualificationUsage):
            return _result(OutcomeClass.MISSING_DEPENDENCY, "execution-qualification:resource", "R2-QUAL-006", "dependency qualification usage is absent")
        dependency_usages.append(dependency.usage)
    return QualificationUsage(
        len(dependencies) + sum(usage.dependency_executions for usage in dependency_usages),
        target.nonce_candidates + sum(usage.nonce_candidates for usage in dependency_usages),
        target.transcript_events + sum(usage.transcript_events for usage in dependency_usages),
        target.trace_events + sum(usage.trace_events for usage in dependency_usages),
        target.challenge_values + sum(usage.challenge_values for usage in dependency_usages),
        target.sampler_attempts + sum(usage.sampler_attempts for usage in dependency_usages),
        target.hash_queries + sum(usage.hash_queries for usage in dependency_usages),
    )


def qualification_worst_case(
    request: ExecutionRequest,
    basis: EvaluatorBasis,
    dependencies: tuple[QualifiedExecution, ...] = (),
) -> QualificationUsage | CheckResult:
    basis_failure = _admit_basis(basis)
    if basis_failure:
        return basis_failure
    if not isinstance(dependencies, tuple) or len(dependencies) > 1 or any(
        not isinstance(dependency, QualifiedExecution) for dependency in dependencies
    ):
        return _result(OutcomeClass.MALFORMED, "execution-qualification:resource", "R2-QUAL-007", "qualification dependency set is malformed")
    target = worst_case_usage(request)
    if isinstance(target, CheckResult):
        return target
    dependency_worst: list[ResourceUsage] = []
    for dependency in dependencies:
        if dependency.dependencies:
            return _result(OutcomeClass.UNSUPPORTED, "execution-qualification:resource", "R2-QUAL-008", "nested execution dependencies exceed the witness profile")
        usage = worst_case_usage(dependency.request)
        if isinstance(usage, CheckResult):
            return usage
        dependency_worst.append(usage)
    result = QualificationUsage(
        len(dependencies),
        target.nonce_candidates + sum(usage.nonce_candidates for usage in dependency_worst),
        target.transcript_events + sum(usage.transcript_events for usage in dependency_worst),
        target.trace_events + sum(usage.trace_events for usage in dependency_worst),
        target.challenge_values + sum(usage.challenge_values for usage in dependency_worst),
        target.sampler_attempts + sum(usage.sampler_attempts for usage in dependency_worst),
        target.hash_queries + sum(usage.hash_queries for usage in dependency_worst),
    )
    if any(
        value > limit
        for value, limit in zip(
            (
                result.dependency_executions,
                result.nonce_candidates,
                result.transcript_events,
                result.trace_events,
                result.challenge_values,
                result.sampler_attempts,
                result.hash_queries,
            ),
            _qualification_cap_values(basis.qualification_caps),
            strict=True,
        )
    ):
        return _result(OutcomeClass.RESOURCE_EXCEEDED, "execution-qualification:resource", "R2-QUAL-009", "aggregate qualification replay exceeds evaluator caps")
    return result


def qualify_execution(
    request: ExecutionRequest,
    basis: EvaluatorBasis,
    record: ExecutionRecord,
    dependencies: tuple[QualifiedExecution, ...] = (),
) -> QualifiedExecution | CheckResult:
    if not isinstance(record, ExecutionRecord):
        return _result(OutcomeClass.MALFORMED, "execution-qualification", "R2-QUAL-001", "record has the wrong type")
    admitted = admit_request(request, basis, dependencies)
    if admitted.outcome is not OutcomeClass.AFFIRMATIVE:
        return admitted
    worst = qualification_worst_case(request, basis, dependencies)
    if isinstance(worst, CheckResult):
        return worst
    checked_dependencies: list[QualifiedExecution] = []
    for dependency in dependencies:
        checked = requalify(dependency)
        if isinstance(checked, CheckResult):
            return _result(OutcomeClass.MISSING_DEPENDENCY, "execution-qualification", "R2-QUAL-010", f"dependency requalification failed: {checked.code}")
        checked_dependencies.append(checked)
    checked_tuple = tuple(checked_dependencies)
    expected = execute(request, basis, checked_tuple)
    if isinstance(expected, CheckResult):
        return expected
    if record != expected or record.identity != expected.identity:
        return _result(OutcomeClass.MISMATCH, "execution-qualification", "R2-QUAL-003", "record differs from exact reexecution")
    terminal = validate_terminal_law(request, record)
    if terminal.outcome is not OutcomeClass.AFFIRMATIVE:
        return terminal
    actual_usage = _qualification_usage(record.usage, checked_tuple)
    if isinstance(actual_usage, CheckResult):
        return actual_usage
    return QualifiedExecution(request, basis, record, checked_tuple, actual_usage)


def requalify(qualified: QualifiedExecution) -> QualifiedExecution | CheckResult:
    if not isinstance(qualified, QualifiedExecution):
        return _result(OutcomeClass.MALFORMED, "execution-qualification", "R2-QUAL-004", "qualification has the wrong type")
    replayed = qualify_execution(
        qualified.request,
        qualified.evaluator_basis,
        qualified.record,
        qualified.dependencies,
    )
    if isinstance(replayed, CheckResult):
        return replayed
    if replayed.identity != qualified.identity:
        return _result(OutcomeClass.MISMATCH, "execution-qualification", "R2-QUAL-005", "qualification identity differs")
    return replayed


def coupled_fresh_tape(
    source: QualifiedExecution,
    target_core: Any,
) -> FreshCoinTape | CheckResult:
    checked = requalify(source)
    if isinstance(checked, CheckResult):
        return checked
    source = checked
    if source.record.interpretation is not Interpretation.FS or source.record.disposition is not TerminalKind.SOURCE_RESIDUAL:
        return _result(OutcomeClass.MISMATCH, "fresh-coin-coupling", "R2-COUPLE-011", "coupling source is not a complete FS execution")
    if not isinstance(target_core, ProtocolCore):
        return _result(OutcomeClass.MALFORMED, "fresh-coin-coupling", "R2-COUPLE-012", "target Core has the wrong type")
    expected_target = (
        source.request.scenario.core.identity
        if target_core.includes_grinding
        else fresh_fri_scenario(source.request.scenario.core).core.identity
    )
    if target_core.identity != expected_target:
        return _result(OutcomeClass.MISMATCH, "fresh-coin-coupling", "R2-COUPLE-013", "target Core is not the declared FS projection")
    try:
        available = source.record.challenge_values()
        vectors = tuple(
            CoinVector(action.occurrence, available[action.occurrence])
            for action in target_core.challenge_actions
        )
    except (AttributeError, KeyError, TypeError) as error:
        return _result(OutcomeClass.MISSING_DEPENDENCY, "fresh-coin-coupling", "R2-COUPLE-001", str(error))
    return FreshCoinTape(
        FreshTapeOrigin.DERIVED_EXECUTION,
        vectors,
        source.record.identity,
        source.record.identity,
    )
