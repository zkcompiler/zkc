"""Bounded strategy execution and exact replay for the finite P01 witness.

The public request deliberately contains no witness or nonce.  Those values
live in a request-bound local object whose identity, but not whose contents,
is retained by public records.  Prover algorithms are evaluator-owned closed
programs: they receive accessor capabilities, not a trace or a caller-authored
read set.  Consequently the receipts below report reads observed by the
evaluator, and a clairvoyant read is refused at the causal boundary.

This is a finite expressibility witness, not a cryptographic implementation or
a sandbox for caller-supplied Python code.
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from enum import Enum
import hashlib
from pathlib import Path
import re
from typing import Any, Iterable, Mapping

from .semantic import (
    CHALLENGE,
    COMMITMENT,
    RESPONSE,
    STATEMENT,
    AlgebraProfile,
    ConversationCore,
    FreshRealization,
    ParticipantRole,
    ProtocolVariant,
    RealizationKind,
    TranscriptConstruction,
    admit_application_context,
    admit_honest_prover_contract,
    admit_protocol,
    canonical_honest_prover_contract,
    derive_fs_challenge,
)
from .terms import Outcome, Result, TermEncodingError, affirmative, result, semantic_id


_REPO_ROOT = Path(__file__).resolve().parents[3]
_CONTENT_ID = re.compile(r"sha256:[0-9a-f]{64}\Z")
_EVALUATOR_PATHS = (
    "evaluation/r2-p01-schnorr/p01model/terms.py",
    "evaluation/r2-p01-schnorr/p01model/semantic.py",
    "evaluation/r2-p01-schnorr/p01model/execution.py",
    "evaluation/r2-p01-schnorr/p01model/relations.py",
)
_QUALIFICATION_LAW = "p01.exact-request-reexecution.v1"
_STRATEGY_LAW = "p01.evaluator-owned-two-stage-strategy.v1"
_PRIVATE_NONCE = "local:nonce:r"
_PRIVATE_WITNESS = "local:witness:x"
_ABORT_OCCURRENCE = "failure:explicit-prover-abort@message:response"


class Disposition(str, Enum):
    """A protocol terminal value, distinct from evaluator Result outcomes."""

    ACCEPT = "Accept"
    REJECT = "Reject"
    ABORT = "Abort"


class StrategyKind(str, Enum):
    HONEST = "Honest"
    CLAIRVOYANT_COMMITMENT = "ClairvoyantCommitment"
    INVALID_RESPONSE = "InvalidResponse"
    ABORT_RESPONSE = "AbortResponse"


class StrategyDecision(str, Enum):
    PRODUCED = "Produced"
    ABORTED = "Aborted"


class TraceKind(str, Enum):
    MESSAGE = "Message"
    CHALLENGE = "Challenge"
    CHECK = "Check"
    FAILURE = "Failure"
    TERMINAL = "Terminal"


class Actor(str, Enum):
    PROVER = "Prover"
    VERIFIER = "Verifier"
    PUBLIC_ENVIRONMENT = "PublicEnvironment"
    TRANSCRIPT = "TranscriptConstruction"


@dataclass(frozen=True)
class ProverStrategy:
    """Closed evaluator program interpreted against one honest-prover contract.

    The contract identifier is a semantic target, not a conformance claim:
    ``Honest`` follows it, while the other finite strategies deliberately probe
    one deviation or execution-level abort relative to it.
    """

    kind: StrategyKind
    honest_prover_contract_id: str
    law: str = _STRATEGY_LAW

    def term(self) -> dict[str, str]:
        return {
            "kind": self.kind.value,
            "honest_prover_contract_id": self.honest_prover_contract_id,
            "law": self.law,
        }

    @property
    def identity(self) -> str:
        return semantic_id("p01.prover-strategy.v1", self.term())


@dataclass(frozen=True)
class FreshChallengeBinding:
    """One exact public-environment support point for a Fresh invocation."""

    core_id: str
    protocol_id: str
    challenge_occurrence: str
    value: int
    source_id: str

    def term(self) -> dict[str, Any]:
        return {
            "core": self.core_id,
            "protocol": self.protocol_id,
            "challenge_occurrence": self.challenge_occurrence,
            "value": self.value,
            "source": self.source_id,
        }

    @property
    def identity(self) -> str:
        return semantic_id("p01.fresh-challenge-binding.v1", self.term())


@dataclass(frozen=True)
class ResourcePlan:
    """Caller budget using the exact six finite fixture dimensions.

    ``max_hash_queries`` meters challenge-oracle queries.  The deterministic
    construction of the session prefix is framing work, not a second oracle
    query.  Trace volume is separately fixed by the admitted five-event Core.
    """

    max_strategy_steps: int
    max_public_reads: int
    max_private_reads: int
    max_transcript_atoms: int
    max_hash_queries: int
    max_replay_executions: int

    def term(self) -> dict[str, int]:
        return {
            "max_strategy_steps": self.max_strategy_steps,
            "max_public_reads": self.max_public_reads,
            "max_private_reads": self.max_private_reads,
            "max_transcript_atoms": self.max_transcript_atoms,
            "max_hash_queries": self.max_hash_queries,
            "max_replay_executions": self.max_replay_executions,
        }


# These are intentionally fixture-scale caps, not configurable production
# defaults.  The hard cap remains wider than the exact admitted strategies so
# a fixture can demonstrate that a caller budget and static need are distinct.
MAX_EVALUATOR_CAPS = ResourcePlan(2, 5, 2, 2, 1, 1)
DEFAULT_RESOURCE_PLAN = MAX_EVALUATOR_CAPS


@dataclass(frozen=True)
class ResourceUsage:
    strategy_steps: int
    public_reads: int
    private_reads: int
    transcript_atoms: int
    hash_queries: int
    replay_executions: int
    trace_events: int

    def term(self) -> dict[str, int]:
        return {
            "strategy_steps": self.strategy_steps,
            "public_reads": self.public_reads,
            "private_reads": self.private_reads,
            "transcript_atoms": self.transcript_atoms,
            "hash_queries": self.hash_queries,
            "replay_executions": self.replay_executions,
            "trace_events": self.trace_events,
        }


@dataclass(frozen=True)
class EvaluatorSource:
    relative_path: str
    sha256: str
    byte_length: int

    def term(self) -> dict[str, Any]:
        return {
            "path": self.relative_path,
            "sha256": self.sha256,
            "byte_length": self.byte_length,
        }


@dataclass(frozen=True)
class EvaluatorBasis:
    """Validation basis; its identity is not a Protocol semantic identity."""

    qualification_law: str
    supported_protocol_ids: tuple[str, ...]
    supported_strategy_ids: tuple[str, ...]
    source_digests: tuple[EvaluatorSource, ...]
    hard_caps: ResourcePlan

    def term(self) -> dict[str, Any]:
        return {
            "qualification_law": self.qualification_law,
            "supported_protocols": list(self.supported_protocol_ids),
            "supported_strategies": list(self.supported_strategy_ids),
            "source_digests": [source.term() for source in self.source_digests],
            "hard_caps": self.hard_caps.term(),
        }

    @property
    def identity(self) -> str:
        return semantic_id("p01.evaluator-basis.v1", self.term())


@dataclass(frozen=True)
class PublicExecutionRequest:
    """Complete public validation request with no local witness material.

    Its identity intentionally binds evaluator sources and resource policy.  It
    is validation identity and must never be used as Protocol equivalence.
    ``application_context`` is present only for a Fiat--Shamir invocation; it
    is not a public input occurrence of the challenge-neutral Core.
    """

    evaluation_profile_id: str
    core_id: str
    honest_prover_contract_id: str
    protocol_id: str
    strategy_id: str
    evaluator_basis_id: str
    statement: int
    application_context: str | None
    resources: ResourcePlan
    source_fixture_id: str
    fresh_challenge: FreshChallengeBinding | None = None

    def term(self) -> dict[str, Any]:
        return {
            "evaluation_profile": self.evaluation_profile_id,
            "core": self.core_id,
            "honest_prover_contract": self.honest_prover_contract_id,
            "protocol": self.protocol_id,
            "strategy": self.strategy_id,
            "evaluator_basis": self.evaluator_basis_id,
            "statement": self.statement,
            "application_context": self.application_context,
            "resources": self.resources.term(),
            "source_fixture": self.source_fixture_id,
            "fresh_challenge": (
                self.fresh_challenge.identity if self.fresh_challenge else None
            ),
        }

    @property
    def identity(self) -> str:
        return semantic_id("p01.public-execution-request.v1", self.term())


@dataclass(frozen=True, repr=False)
class PrivateLocalBinding:
    """Replay material retained locally and never expanded by public terms."""

    request_id: str
    witness: int
    nonce: int

    def _private_term(self) -> dict[str, Any]:
        return {
            "request": self.request_id,
            "witness": self.witness,
            "nonce": self.nonce,
        }

    @property
    def identity(self) -> str:
        return semantic_id("p01.private-local-binding.v1", self._private_term())

    def public_term(self) -> dict[str, str]:
        return {"id": self.identity, "request": self.request_id}


@dataclass(frozen=True)
class AccessReceipt:
    output_occurrence: str
    strategy_id: str
    decision: StrategyDecision
    public_reads: tuple[str, ...]
    private_reads: tuple[str, ...]
    output: int | None

    def term(self) -> dict[str, Any]:
        return {
            "output_occurrence": self.output_occurrence,
            "strategy": self.strategy_id,
            "decision": self.decision.value,
            "public_reads": list(self.public_reads),
            "private_reads": list(self.private_reads),
            "output": self.output,
        }


@dataclass(frozen=True)
class TranscriptReadReceipt:
    source_kind: str
    occurrence: str
    value_domain_id: str
    codec: str
    encoded_hex: str

    def term(self) -> dict[str, str]:
        return {
            "source_kind": self.source_kind,
            "occurrence": self.occurrence,
            "value_domain_id": self.value_domain_id,
            "codec": self.codec,
            "encoded_hex": self.encoded_hex,
        }


@dataclass(frozen=True)
class ChallengeReceipt:
    realization_kind: RealizationKind
    value: int
    source_id: str
    query_hex: str | None
    transcript_reads: tuple[TranscriptReadReceipt, ...]

    def term(self) -> dict[str, Any]:
        return {
            "realization_kind": self.realization_kind.value,
            "value": self.value,
            "source": self.source_id,
            "query_hex": self.query_hex,
            "transcript_reads": [read.term() for read in self.transcript_reads],
        }


@dataclass(frozen=True)
class TraceEvent:
    occurrence: str
    kind: TraceKind
    actor: Actor
    value: Any
    authority_id: str

    def term(self) -> dict[str, Any]:
        value = self.value.value if isinstance(self.value, Enum) else self.value
        return {
            "occurrence": self.occurrence,
            "kind": self.kind.value,
            "actor": self.actor.value,
            "value": value,
            "authority": self.authority_id,
        }


@dataclass(frozen=True)
class RuleReference:
    """The Core-owned deterministic rule referenced by an execution record."""

    output_occurrence: str
    semantic_contract_id: str

    def term(self) -> dict[str, str]:
        return {
            "output_occurrence": self.output_occurrence,
            "semantic_contract_id": self.semantic_contract_id,
        }


@dataclass(frozen=True)
class ExecutionRecord:
    """Validation evidence for one request-bound execution occurrence."""

    evaluation_profile_id: str
    core_id: str
    honest_prover_contract_id: str
    protocol_id: str
    request_id: str
    local_binding_id: str
    strategy_id: str
    evaluator_basis_id: str
    events: tuple[TraceEvent, ...]
    access_receipts: tuple[AccessReceipt, ...]
    challenge_receipt: ChallengeReceipt
    verifier_check_rule: RuleReference
    terminal_route_rule: RuleReference
    disposition: Disposition
    usage: ResourceUsage

    def _identity_term(self) -> dict[str, Any]:
        return {
            "evaluation_profile": self.evaluation_profile_id,
            "core": self.core_id,
            "honest_prover_contract": self.honest_prover_contract_id,
            "protocol": self.protocol_id,
            "request": self.request_id,
            "local_binding": self.local_binding_id,
            "strategy": self.strategy_id,
            "evaluator_basis": self.evaluator_basis_id,
            "events": [event.term() for event in self.events],
            "access_receipts": [receipt.term() for receipt in self.access_receipts],
            "challenge_receipt": self.challenge_receipt.term(),
            "verifier_check_rule": self.verifier_check_rule.term(),
            "terminal_route_rule": self.terminal_route_rule.term(),
            "disposition": self.disposition.value,
            "usage": self.usage.term(),
        }

    @property
    def identity(self) -> str:
        return semantic_id("p01.execution-record.v1", self._identity_term())

    def term(self, include_trace: bool = True) -> dict[str, Any]:
        value: dict[str, Any] = {
            "id": self.identity,
            "evaluation_profile_id": self.evaluation_profile_id,
            "core_id": self.core_id,
            "honest_prover_contract_id": self.honest_prover_contract_id,
            "protocol_id": self.protocol_id,
            "request_id": self.request_id,
            "local_binding_id": self.local_binding_id,
            "strategy_id": self.strategy_id,
            "evaluator_basis_id": self.evaluator_basis_id,
            "access_receipts": [
                receipt.term() for receipt in self.access_receipts
            ],
            "challenge_receipt": self.challenge_receipt.term(),
            "verifier_check_rule": self.verifier_check_rule.term(),
            "terminal_route_rule": self.terminal_route_rule.term(),
            "disposition": self.disposition.value,
            "usage": self.usage.term(),
        }
        if include_trace:
            value["events"] = [event.term() for event in self.events]
        return value

    def value_for(self, occurrence: str) -> Any:
        matches = tuple(
            event.value for event in self.events if event.occurrence == occurrence
        )
        if len(matches) != 1:
            raise KeyError(occurrence)
        return matches[0]


@dataclass(frozen=True, repr=False)
class QualifiedExecution:
    """Local replay capability whose identity belongs to validation evidence.

    Its public term exposes only bound identities.  None of these validation
    identities can replace Core, Protocol, Construction, or Profile identity.
    """

    request: PublicExecutionRequest
    local_binding: PrivateLocalBinding
    strategy: ProverStrategy
    evaluator_basis: EvaluatorBasis
    protocol: ProtocolVariant
    profile: AlgebraProfile
    core: ConversationCore
    record: ExecutionRecord
    replay_usage: ResourceUsage
    fresh: FreshRealization | None = None
    construction: TranscriptConstruction | None = None

    @property
    def identity(self) -> str:
        return semantic_id(
            "p01.qualified-execution.v1",
            {
                "request": self.request.identity,
                "local_binding": self.local_binding.identity,
                "strategy": self.strategy.identity,
                "evaluator_basis": self.evaluator_basis.identity,
                "protocol": self.protocol.identity,
                "evaluation_profile": self.profile.identity,
                "core": self.core.identity,
                "record": self.record.identity,
                "qualification_law": self.evaluator_basis.qualification_law,
                "replay_usage": self.replay_usage.term(),
                "fresh": self.fresh.identity if self.fresh else None,
                "construction": (
                    self.construction.identity if self.construction else None
                ),
            },
        )

    def public_term(self) -> dict[str, Any]:
        return {
            "id": self.identity,
            "request_id": self.request.identity,
            "local_binding_id": self.local_binding.identity,
            "strategy_id": self.strategy.identity,
            "evaluator_basis_id": self.evaluator_basis.identity,
            "record_id": self.record.identity,
            "replay_usage": self.replay_usage.term(),
        }


class _AccessFailure(Exception):
    def __init__(
        self,
        boundary: str,
        code: str,
        detail: str,
        *,
        output_occurrence: str,
        attempted_source: str,
        observed_reads: tuple[str, ...],
    ) -> None:
        super().__init__(detail)
        self.check_result = result(
            Outcome.REFUSED,
            boundary,
            code,
            detail,
            output_occurrence=output_occurrence,
            attempted_source=attempted_source,
            observed_reads=list(observed_reads),
        )


class _PublicAccessor:
    """Evaluator-owned capability over the actual visible prefix."""

    def __init__(
        self,
        output_occurrence: str,
        allowed: tuple[str, ...],
        visible: Mapping[str, Any],
        known_occurrences: frozenset[str],
    ) -> None:
        self._output = output_occurrence
        self._allowed = allowed
        self._visible = dict(visible)
        self._known = known_occurrences
        self._reads: list[str] = []

    @property
    def reads(self) -> tuple[str, ...]:
        return tuple(self._reads)

    def read(self, occurrence: str) -> Any:
        if occurrence in self._known and occurrence not in self._visible:
            raise _AccessFailure(
                f"strategy-causality:{self._output}",
                "P01-EXEC-CAUSALITY",
                "strategy attempted to read a value outside its actual visible past",
                output_occurrence=self._output,
                attempted_source=occurrence,
                observed_reads=self.reads,
            )
        if occurrence not in self._allowed:
            raise _AccessFailure(
                f"strategy-authority:{self._output}",
                "P01-EXEC-AUTHORITY",
                "strategy attempted a public read not granted by Core",
                output_occurrence=self._output,
                attempted_source=occurrence,
                observed_reads=self.reads,
            )
        if occurrence not in self._visible:
            raise _AccessFailure(
                f"strategy-availability:{self._output}",
                "P01-EXEC-AVAILABILITY",
                "strategy attempted to read an unknown public occurrence",
                output_occurrence=self._output,
                attempted_source=occurrence,
                observed_reads=self.reads,
            )
        self._reads.append(occurrence)
        return self._visible[occurrence]


class _PrivateAccessor:
    """Evaluator-owned capability over the request's exact local binding."""

    def __init__(
        self,
        output_occurrence: str,
        allowed: tuple[str, ...],
        binding: PrivateLocalBinding,
    ) -> None:
        self._output = output_occurrence
        self._allowed = allowed
        self._values = {
            _PRIVATE_NONCE: binding.nonce,
            _PRIVATE_WITNESS: binding.witness,
        }
        self._reads: list[str] = []

    @property
    def reads(self) -> tuple[str, ...]:
        return tuple(self._reads)

    def read(self, source: str) -> int:
        if source not in self._allowed or source not in self._values:
            raise _AccessFailure(
                f"strategy-private-authority:{self._output}",
                "P01-EXEC-PRIVATE-AUTHORITY",
                "strategy attempted a private read not granted by evaluator law",
                output_occurrence=self._output,
                attempted_source=source,
                observed_reads=self.reads,
            )
        self._reads.append(source)
        return self._values[source]


class _StrategyMachine:
    """Closed two-stage programs; callers cannot substitute a callback."""

    def __init__(self, strategy: ProverStrategy, profile: AlgebraProfile) -> None:
        self.strategy = strategy
        self.profile = profile
        self._nonce: int | None = None
        self._committed = False

    def commit(
        self, public: _PublicAccessor, private: _PrivateAccessor
    ) -> int:
        if self._committed:
            raise RuntimeError("commitment stage invoked more than once")
        if self.strategy.kind is StrategyKind.CLAIRVOYANT_COMMITMENT:
            # The accessor, rather than a later trace checker, refuses this.
            public.read(CHALLENGE)
        nonce = private.read(_PRIVATE_NONCE)
        self._nonce = nonce
        self._committed = True
        return pow(self.profile.generator, nonce, self.profile.p)

    def respond(
        self, public: _PublicAccessor, private: _PrivateAccessor
    ) -> tuple[StrategyDecision, int | None]:
        if not self._committed or self._nonce is None:
            raise RuntimeError("response stage invoked before commitment")
        challenge = public.read(CHALLENGE)
        if self.strategy.kind is StrategyKind.ABORT_RESPONSE:
            return StrategyDecision.ABORTED, None
        witness = private.read(_PRIVATE_WITNESS)
        response_value = (self._nonce + challenge * witness) % self.profile.q
        if self.strategy.kind is StrategyKind.INVALID_RESPONSE:
            response_value = (response_value + 1) % self.profile.q
        return StrategyDecision.PRODUCED, response_value


def _source_digests(repo_root: Path) -> tuple[EvaluatorSource, ...]:
    sources: list[EvaluatorSource] = []
    for relative in _EVALUATOR_PATHS:
        raw = (repo_root / relative).read_bytes()
        sources.append(
            EvaluatorSource(
                relative,
                f"sha256:{hashlib.sha256(raw).hexdigest()}",
                len(raw),
            )
        )
    return tuple(sources)


def build_evaluator_basis(
    repo_root: Path,
    supported_protocol_ids: Iterable[str],
    supported_strategy_ids: Iterable[str],
    hard_caps: ResourcePlan = DEFAULT_RESOURCE_PLAN,
) -> EvaluatorBasis:
    """Bind qualification to the code actually imported in this process."""

    resolved = Path(repo_root).resolve()
    if resolved != _REPO_ROOT:
        raise ValueError("evaluator basis root differs from the loaded checkout")
    return EvaluatorBasis(
        _QUALIFICATION_LAW,
        tuple(sorted(set(supported_protocol_ids))),
        tuple(sorted(set(supported_strategy_ids))),
        _source_digests(resolved),
        hard_caps,
    )


def _resource_values(plan: ResourcePlan) -> tuple[int, ...]:
    return (
        plan.max_strategy_steps,
        plan.max_public_reads,
        plan.max_private_reads,
        plan.max_transcript_atoms,
        plan.max_hash_queries,
        plan.max_replay_executions,
    )


def _usage_values(usage: ResourceUsage) -> tuple[int, ...]:
    return (
        usage.strategy_steps,
        usage.public_reads,
        usage.private_reads,
        usage.transcript_atoms,
        usage.hash_queries,
        usage.replay_executions,
    )


def _valid_resource_plan(plan: Any) -> bool:
    return isinstance(plan, ResourcePlan) and all(
        isinstance(value, int) and not isinstance(value, bool) and value >= 0
        for value in _resource_values(plan)
    )


def _is_content_id(value: Any) -> bool:
    return isinstance(value, str) and _CONTENT_ID.fullmatch(value) is not None


def admit_evaluator_basis(basis: EvaluatorBasis) -> Result:
    if not isinstance(basis, EvaluatorBasis):
        return result(
            Outcome.MALFORMED,
            "evaluator-basis",
            "P01-BASIS-001",
            "evaluator basis has the wrong type",
        )
    try:
        basis_id = basis.identity
    except (AttributeError, TermEncodingError, TypeError, ValueError) as error:
        return result(
            Outcome.MALFORMED,
            "evaluator-basis",
            "P01-BASIS-002",
            f"evaluator basis identity is malformed: {error}",
        )
    if basis.qualification_law != _QUALIFICATION_LAW:
        return result(
            Outcome.UNSUPPORTED,
            "evaluator-basis:qualification-law",
            "P01-BASIS-003",
            "qualification law is unsupported",
            subject=basis_id,
        )
    if (
        not basis.supported_protocol_ids
        or tuple(sorted(set(basis.supported_protocol_ids)))
        != basis.supported_protocol_ids
        or not all(_is_content_id(value) for value in basis.supported_protocol_ids)
    ):
        return result(
            Outcome.MALFORMED,
            "evaluator-basis:protocol-support",
            "P01-BASIS-004",
            "supported protocol identities must be a nonempty canonical set",
            subject=basis_id,
        )
    if (
        not basis.supported_strategy_ids
        or tuple(sorted(set(basis.supported_strategy_ids)))
        != basis.supported_strategy_ids
        or not all(_is_content_id(value) for value in basis.supported_strategy_ids)
    ):
        return result(
            Outcome.MALFORMED,
            "evaluator-basis:strategy-support",
            "P01-BASIS-005",
            "supported strategy identities must be a nonempty canonical set",
            subject=basis_id,
        )
    if not _valid_resource_plan(basis.hard_caps):
        return result(
            Outcome.MALFORMED,
            "evaluator-basis:resource",
            "P01-BASIS-006",
            "evaluator hard caps are malformed",
            subject=basis_id,
        )
    if any(
        value > maximum
        for value, maximum in zip(
            _resource_values(basis.hard_caps),
            _resource_values(MAX_EVALUATOR_CAPS),
            strict=True,
        )
    ):
        return result(
            Outcome.RESOURCE_EXCEEDED,
            "evaluator-basis:resource",
            "P01-BASIS-007",
            "evaluator hard caps exceed the finite implementation profile",
            subject=basis_id,
        )
    try:
        current_sources = _source_digests(_REPO_ROOT)
    except OSError as error:
        return result(
            Outcome.MISSING_DEPENDENCY,
            "evaluator-basis:sources",
            "P01-BASIS-008",
            f"an evaluator source cannot be read: {error}",
            subject=basis_id,
        )
    if basis.source_digests != current_sources:
        return result(
            Outcome.MISMATCH,
            "evaluator-basis:sources",
            "P01-BASIS-009",
            "evaluator source digests differ from the loaded checkout",
            subject=basis_id,
        )
    return affirmative(
        "evaluator-basis",
        "P01-BASIS-OK",
        "evaluator basis is bound to the loaded finite implementation",
        subject=basis_id,
    )


def admit_strategy(
    strategy: ProverStrategy,
    basis: EvaluatorBasis,
    protocol: ProtocolVariant,
) -> Result:
    if not isinstance(strategy, ProverStrategy) or not isinstance(
        strategy.kind, StrategyKind
    ) or not isinstance(protocol, ProtocolVariant):
        return result(
            Outcome.MALFORMED,
            "strategy-admission",
            "P01-STRATEGY-001",
            "strategy has the wrong type",
        )
    try:
        strategy_id = strategy.identity
    except (AttributeError, TermEncodingError, TypeError, ValueError) as error:
        return result(
            Outcome.MALFORMED,
            "strategy-admission",
            "P01-STRATEGY-004",
            f"strategy identity is malformed: {error}",
        )
    if strategy.law != _STRATEGY_LAW:
        return result(
            Outcome.UNSUPPORTED,
            "strategy-admission:law",
            "P01-STRATEGY-002",
            "strategy law is not evaluator-owned P01 code",
            subject=strategy_id,
        )
    if (
        not _is_content_id(strategy.honest_prover_contract_id)
        or strategy.honest_prover_contract_id
        != protocol.honest_prover_contract_id
    ):
        return result(
            Outcome.MISMATCH,
            "strategy-admission:honest-prover-contract",
            "P01-STRATEGY-005",
            "strategy is not interpreted against the Protocol's honest-prover contract",
            subject=strategy_id,
            protocol_id=protocol.identity,
            expected_honest_prover_contract_id=(
                protocol.honest_prover_contract_id
            ),
        )
    if strategy_id not in basis.supported_strategy_ids:
        return result(
            Outcome.UNSUPPORTED,
            "strategy-admission:support",
            "P01-STRATEGY-003",
            "strategy is outside the evaluator basis",
            subject=strategy_id,
        )
    return affirmative(
        "strategy-admission",
        "P01-STRATEGY-OK",
        "closed two-stage strategy is admitted",
        subject=strategy_id,
    )


def worst_case_usage(
    request: PublicExecutionRequest,
    protocol: ProtocolVariant,
) -> ResourceUsage | Result:
    if not isinstance(request, PublicExecutionRequest) or not isinstance(
        protocol, ProtocolVariant
    ):
        return result(
            Outcome.MALFORMED,
            "execution-resource",
            "P01-RESOURCE-001",
            "resource subject has the wrong type",
        )
    try:
        protocol_id = protocol.identity
    except (AttributeError, TermEncodingError, TypeError, ValueError) as error:
        return result(
            Outcome.MALFORMED,
            "execution-resource:protocol",
            "P01-RESOURCE-007",
            f"resource protocol identity is malformed: {error}",
        )
    if protocol_id != request.protocol_id:
        return result(
            Outcome.MISMATCH,
            "execution-resource:protocol",
            "P01-RESOURCE-002",
            "resource subject names a different protocol",
        )
    if protocol.realization_kind is RealizationKind.FRESH:
        transcript_atoms, hash_queries = 0, 0
    elif protocol.realization_kind is RealizationKind.FIAT_SHAMIR:
        transcript_atoms, hash_queries = 2, 1
    else:
        return result(
            Outcome.UNSUPPORTED,
            "execution-resource:realization",
            "P01-RESOURCE-003",
            "realization kind has no finite resource model",
        )
    return ResourceUsage(
        strategy_steps=2,
        public_reads=1,
        private_reads=2,
        transcript_atoms=transcript_atoms,
        hash_queries=hash_queries,
        replay_executions=0,
        trace_events=5,
    )


def preadmit_resources(
    request: PublicExecutionRequest,
    protocol: ProtocolVariant,
    basis: EvaluatorBasis,
    *,
    for_replay: bool = False,
) -> ResourceUsage | Result:
    if (
        not isinstance(request, PublicExecutionRequest)
        or not isinstance(protocol, ProtocolVariant)
        or not isinstance(basis, EvaluatorBasis)
    ):
        return result(
            Outcome.MALFORMED,
            "execution-resource",
            "P01-RESOURCE-008",
            "resource preadmission dependency has the wrong type",
        )
    try:
        request_id = request.identity
    except (AttributeError, TermEncodingError, TypeError, ValueError) as error:
        return result(
            Outcome.MALFORMED,
            "execution-resource",
            "P01-RESOURCE-009",
            f"resource request identity is malformed: {error}",
        )
    if not _valid_resource_plan(request.resources):
        return result(
            Outcome.MALFORMED,
            "execution-resource",
            "P01-RESOURCE-004",
            "request resource plan is malformed",
            subject=request_id,
        )
    requested = _resource_values(request.resources)
    if any(
        value > cap
        for value, cap in zip(
            requested, _resource_values(basis.hard_caps), strict=True
        )
    ):
        return result(
            Outcome.RESOURCE_EXCEEDED,
            "execution-resource:evaluator-cap",
            "P01-RESOURCE-005",
            "requested budget exceeds evaluator hard caps",
            subject=request_id,
        )
    worst = worst_case_usage(request, protocol)
    if isinstance(worst, Result):
        return worst
    if for_replay:
        worst = replace(worst, replay_executions=1)
    if any(
        need > available
        for need, available in zip(
            _usage_values(worst), requested, strict=True
        )
    ):
        return result(
            Outcome.RESOURCE_EXCEEDED,
            "execution-resource:preadmission",
            "P01-RESOURCE-006",
            "request budget cannot cover the static worst case",
            subject=request_id,
            required=worst.term(),
        )
    return worst


def admit_request(
    request: PublicExecutionRequest,
    basis: EvaluatorBasis,
    protocol: ProtocolVariant,
    profile: AlgebraProfile,
    core: ConversationCore,
    *,
    fresh: FreshRealization | None = None,
    construction: TranscriptConstruction | None = None,
) -> Result:
    if not isinstance(request, PublicExecutionRequest):
        return result(
            Outcome.MALFORMED,
            "execution-request",
            "P01-REQUEST-001",
            "public request has the wrong type",
        )
    try:
        request_id = request.identity
    except (AttributeError, TermEncodingError, TypeError, ValueError) as error:
        return result(
            Outcome.MALFORMED,
            "execution-request",
            "P01-REQUEST-002",
            f"public request identity is malformed: {error}",
        )
    basis_result = admit_evaluator_basis(basis)
    if basis_result.outcome is not Outcome.AFFIRMATIVE:
        return basis_result
    if request.evaluator_basis_id != basis.identity:
        return result(
            Outcome.MISMATCH,
            "execution-request:evaluator-basis",
            "P01-REQUEST-003",
            "request names a different evaluator basis",
            subject=request_id,
        )
    try:
        protocol_id = protocol.identity
        profile_id = profile.identity
        core_id = core.identity
        honest_contract = canonical_honest_prover_contract(core, profile)
    except (AttributeError, TermEncodingError, TypeError, ValueError) as error:
        return result(
            Outcome.MALFORMED,
            "execution-request:semantic-dependency",
            "P01-REQUEST-004",
            f"semantic dependency is malformed: {error}",
            subject=request_id,
        )
    if request.protocol_id != protocol_id:
        return result(
            Outcome.MISMATCH,
            "execution-request:protocol-identity",
            "P01-REQUEST-013",
            "supplied Protocol differs from the public request",
            subject=request_id,
        )
    if protocol_id not in basis.supported_protocol_ids:
        return result(
            Outcome.UNSUPPORTED,
            "execution-request:protocol-support",
            "P01-REQUEST-005",
            "request protocol is mismatched or outside the evaluator basis",
            subject=request_id,
        )
    if (
        request.evaluation_profile_id != profile_id
        or request.core_id != core_id
        or protocol.core_id != core_id
    ):
        return result(
            Outcome.MISMATCH,
            "execution-request:semantic-scope",
            "P01-REQUEST-006",
            "request evaluation profile, Core, and Protocol identities do not agree",
            subject=request_id,
        )
    protocol_result = admit_protocol(
        protocol,
        core,
        profile,
        fresh=fresh,
        construction=construction,
    )
    if protocol_result.outcome is not Outcome.AFFIRMATIVE:
        return protocol_result
    honest_result = admit_honest_prover_contract(
        honest_contract, core, profile
    )
    if honest_result.outcome is not Outcome.AFFIRMATIVE:
        return honest_result
    if (
        request.honest_prover_contract_id != honest_contract.identity
        or protocol.honest_prover_contract_id != honest_contract.identity
    ):
        return result(
            Outcome.MISMATCH,
            "execution-request:honest-prover-contract",
            "P01-REQUEST-014",
            "request and Protocol do not bind the exact admitted honest-prover contract",
            subject=request_id,
            expected_honest_prover_contract_id=honest_contract.identity,
        )
    if not profile.valid_group_element(request.statement):
        return result(
            Outcome.MALFORMED,
            "execution-request:statement",
            "P01-REQUEST-007",
            "public statement is not in the admitted group",
            subject=request_id,
        )
    if not _is_content_id(request.source_fixture_id):
        return result(
            Outcome.MALFORMED,
            "execution-request:source",
            "P01-REQUEST-008",
            "source fixture identity is not a content identifier",
            subject=request_id,
        )
    if request.strategy_id not in basis.supported_strategy_ids:
        return result(
            Outcome.UNSUPPORTED,
            "execution-request:strategy-support",
            "P01-REQUEST-009",
            "request strategy is outside the evaluator basis",
            subject=request_id,
        )
    if protocol.realization_kind is RealizationKind.FRESH:
        if request.application_context is not None:
            return result(
                Outcome.SEMANTIC_NEGATIVE,
                "execution-request:fresh-context-authority",
                "P01-REQUEST-015",
                "Fresh request must not author Fiat-Shamir-only application context",
                subject=request_id,
            )
        binding = request.fresh_challenge
        if not isinstance(binding, FreshChallengeBinding):
            return result(
                Outcome.MISSING_DEPENDENCY,
                "execution-request:fresh-challenge",
                "P01-REQUEST-010",
                "Fresh request lacks an exact public challenge binding",
                subject=request_id,
            )
        if (
            binding.core_id != core_id
            or binding.protocol_id != protocol_id
            or binding.challenge_occurrence != CHALLENGE
            or not profile.valid_challenge(binding.value)
            or not _is_content_id(binding.source_id)
        ):
            return result(
                Outcome.MISMATCH,
                "execution-request:fresh-challenge",
                "P01-REQUEST-011",
                "Fresh challenge binding has the wrong scope, source, or value",
                subject=request_id,
            )
    else:
        if request.application_context is None:
            return result(
                Outcome.MISSING_DEPENDENCY,
                "execution-request:fs-context",
                "P01-REQUEST-016",
                "Fiat-Shamir request lacks its realization-owned application context",
                subject=request_id,
            )
        context_result = admit_application_context(request.application_context)
        if context_result.outcome is not Outcome.AFFIRMATIVE:
            return context_result
        if request.fresh_challenge is not None:
            return result(
                Outcome.SEMANTIC_NEGATIVE,
                "execution-request:fs-challenge-authority",
                "P01-REQUEST-012",
                "Fiat-Shamir request must not author an external challenge value",
                subject=request_id,
            )
    resource_result = preadmit_resources(request, protocol, basis)
    if isinstance(resource_result, Result):
        return resource_result
    return affirmative(
        "execution-request",
        "P01-REQUEST-OK",
        "exact public request is admitted before strategy invocation",
        subject=request_id,
        static_worst_case=resource_result.term(),
        fresh_support_point_non_claim=(
            "not evidence of sampling from or satisfying the Fresh distribution"
            if protocol.realization_kind is RealizationKind.FRESH
            else None
        ),
    )


def admit_local_binding(
    binding: PrivateLocalBinding,
    request: PublicExecutionRequest,
    profile: AlgebraProfile,
) -> Result:
    if (
        not isinstance(binding, PrivateLocalBinding)
        or not isinstance(request, PublicExecutionRequest)
        or not isinstance(profile, AlgebraProfile)
    ):
        return result(
            Outcome.MALFORMED,
            "local-binding",
            "P01-BINDING-001",
            "private local binding dependency has the wrong type",
        )
    if binding.request_id != request.identity:
        return result(
            Outcome.MISMATCH,
            "local-binding:request",
            "P01-BINDING-002",
            "private local binding names a different public request",
            subject=binding.identity,
        )
    if not profile.valid_scalar(binding.witness) or not profile.valid_scalar(
        binding.nonce
    ):
        return result(
            Outcome.MALFORMED,
            "local-binding:scalar-domain",
            "P01-BINDING-003",
            "witness or nonce is outside the admitted scalar domain",
            subject=binding.identity,
        )
    if pow(profile.generator, binding.witness, profile.p) != request.statement:
        return result(
            Outcome.MISMATCH,
            "local-binding:statement-witness",
            "P01-BINDING-004",
            "local witness does not open the exact public statement",
            subject=binding.identity,
        )
    return affirmative(
        "local-binding",
        "P01-BINDING-OK",
        "private material is bound to the exact public request",
        subject=binding.identity,
    )


def _transcript_receipts(
    receipts: tuple[dict[str, Any], ...],
) -> tuple[TranscriptReadReceipt, ...]:
    expected = frozenset(
        {
            "source_kind",
            "occurrence",
            "value_domain_id",
            "codec",
            "encoded_hex",
        }
    )
    values: list[TranscriptReadReceipt] = []
    for receipt in receipts:
        if not isinstance(receipt, dict) or frozenset(receipt) != expected:
            raise ValueError("semantic transcript receipt shape changed")
        values.append(
            TranscriptReadReceipt(
                str(receipt["source_kind"]),
                str(receipt["occurrence"]),
                str(receipt["value_domain_id"]),
                str(receipt["codec"]),
                str(receipt["encoded_hex"]),
            )
        )
    return tuple(values)


def _actual_usage(
    receipts: tuple[AccessReceipt, ...],
    challenge_receipt: ChallengeReceipt,
    events: tuple[TraceEvent, ...],
) -> ResourceUsage:
    return ResourceUsage(
        strategy_steps=len(receipts),
        public_reads=sum(len(receipt.public_reads) for receipt in receipts),
        private_reads=sum(len(receipt.private_reads) for receipt in receipts),
        transcript_atoms=len(challenge_receipt.transcript_reads),
        hash_queries=(
            1
            if challenge_receipt.realization_kind is RealizationKind.FIAT_SHAMIR
            else 0
        ),
        replay_executions=0,
        trace_events=len(events),
    )


def _make_record(
    request: PublicExecutionRequest,
    binding: PrivateLocalBinding,
    strategy: ProverStrategy,
    basis: EvaluatorBasis,
    protocol: ProtocolVariant,
    profile: AlgebraProfile,
    core: ConversationCore,
    events: list[TraceEvent],
    receipts: list[AccessReceipt],
    challenge_receipt: ChallengeReceipt,
    disposition: Disposition,
) -> ExecutionRecord:
    event_tuple = tuple(events)
    receipt_tuple = tuple(receipts)
    usage = _actual_usage(receipt_tuple, challenge_receipt, event_tuple)
    return ExecutionRecord(
        evaluation_profile_id=profile.identity,
        core_id=core.identity,
        honest_prover_contract_id=protocol.honest_prover_contract_id,
        protocol_id=protocol.identity,
        request_id=request.identity,
        local_binding_id=binding.identity,
        strategy_id=strategy.identity,
        evaluator_basis_id=basis.identity,
        events=event_tuple,
        access_receipts=receipt_tuple,
        challenge_receipt=challenge_receipt,
        verifier_check_rule=RuleReference(
            core.verifier_check.output_occurrence,
            core.verifier_check.semantic_contract_id,
        ),
        terminal_route_rule=RuleReference(
            core.terminal_route.output_occurrence,
            core.terminal_route.semantic_contract_id,
        ),
        disposition=disposition,
        usage=usage,
    )


def _evaluate_core_verifier_check(
    core: ConversationCore,
    profile: AlgebraProfile,
    visible: Mapping[str, Any],
) -> bool:
    """Interpret the exact Core-owned verifier rule, not a local read ledger."""

    bindings = dict(core.verifier_check.named_inputs)
    if len(bindings) != len(core.verifier_check.named_inputs):
        raise ValueError("Core verifier rule duplicates a named input")
    operands = {name: visible[occurrence] for name, occurrence in bindings.items()}
    if frozenset(operands) != frozenset(
        {"statement", "commitment", "challenge", "response"}
    ):
        raise ValueError("Core verifier rule is not the admitted Schnorr contract")
    return pow(profile.generator, operands["response"], profile.p) == (
        operands["commitment"]
        * pow(operands["statement"], operands["challenge"], profile.p)
    ) % profile.p


def _route_core_terminal(
    core: ConversationCore,
    check_value: bool,
) -> Disposition:
    bindings = dict(core.terminal_route.named_inputs)
    if (
        len(bindings) != len(core.terminal_route.named_inputs)
        or bindings != {"check": core.verifier_check.output_occurrence}
    ):
        raise ValueError("Core terminal route does not reference its verifier check")
    return Disposition.ACCEPT if check_value else Disposition.REJECT


def execute(
    request: PublicExecutionRequest,
    binding: PrivateLocalBinding,
    strategy: ProverStrategy,
    basis: EvaluatorBasis,
    protocol: ProtocolVariant,
    profile: AlgebraProfile,
    core: ConversationCore,
    *,
    fresh: FreshRealization | None = None,
    construction: TranscriptConstruction | None = None,
) -> ExecutionRecord | Result:
    """Execute one admitted support point under a closed prover strategy."""

    admitted = admit_request(
        request,
        basis,
        protocol,
        profile,
        core,
        fresh=fresh,
        construction=construction,
    )
    if admitted.outcome is not Outcome.AFFIRMATIVE:
        return admitted
    strategy_result = admit_strategy(strategy, basis, protocol)
    if strategy_result.outcome is not Outcome.AFFIRMATIVE:
        return strategy_result
    if strategy.identity != request.strategy_id:
        return result(
            Outcome.MISMATCH,
            "execution:strategy",
            "P01-EXEC-001",
            "supplied strategy differs from the public request",
            subject=request.identity,
        )
    binding_result = admit_local_binding(binding, request, profile)
    if binding_result.outcome is not Outcome.AFFIRMATIVE:
        return binding_result

    known = frozenset(contract.occurrence for contract in core.occurrences)
    visible: dict[str, Any] = {STATEMENT: request.statement}
    machine = _StrategyMachine(strategy, profile)
    events: list[TraceEvent] = []
    receipts: list[AccessReceipt] = []

    try:
        commitment_public = _PublicAccessor(
            COMMITMENT,
            core.visible_public_before(ParticipantRole.PROVER, COMMITMENT),
            visible,
            known,
        )
        commitment_private = _PrivateAccessor(
            COMMITMENT, (_PRIVATE_NONCE,), binding
        )
        commitment = machine.commit(commitment_public, commitment_private)
        if not profile.valid_group_element(commitment):
            return result(
                Outcome.CHECKER_FAILURE,
                "execution:commitment",
                "P01-EXEC-002",
                "closed strategy escaped the admitted commitment domain",
                subject=request.identity,
            )
        receipts.append(
            AccessReceipt(
                COMMITMENT,
                strategy.identity,
                StrategyDecision.PRODUCED,
                commitment_public.reads,
                commitment_private.reads,
                commitment,
            )
        )
        visible[COMMITMENT] = commitment
        events.append(
            TraceEvent(
                COMMITMENT,
                TraceKind.MESSAGE,
                Actor.PROVER,
                commitment,
                strategy.identity,
            )
        )

        if protocol.realization_kind is RealizationKind.FRESH:
            if request.fresh_challenge is None:
                raise RuntimeError("admitted Fresh request lost its challenge binding")
            challenge = request.fresh_challenge.value
            challenge_receipt = ChallengeReceipt(
                RealizationKind.FRESH,
                challenge,
                request.fresh_challenge.identity,
                None,
                (),
            )
            challenge_actor = Actor.PUBLIC_ENVIRONMENT
        else:
            if construction is None:
                raise RuntimeError("admitted FS request lost its construction")
            if not isinstance(request.application_context, str):
                raise RuntimeError("admitted FS request lost its application context")
            challenge, query, semantic_receipts = derive_fs_challenge(
                construction,
                profile,
                request.application_context,
                request.statement,
                commitment,
            )
            challenge_receipt = ChallengeReceipt(
                RealizationKind.FIAT_SHAMIR,
                challenge,
                construction.identity,
                query.hex(),
                _transcript_receipts(semantic_receipts),
            )
            challenge_actor = Actor.TRANSCRIPT
        visible[CHALLENGE] = challenge
        events.append(
            TraceEvent(
                CHALLENGE,
                TraceKind.CHALLENGE,
                challenge_actor,
                challenge,
                challenge_receipt.source_id,
            )
        )

        response_public = _PublicAccessor(
            RESPONSE,
            core.visible_public_before(ParticipantRole.PROVER, RESPONSE),
            visible,
            known,
        )
        response_private = _PrivateAccessor(
            RESPONSE, (_PRIVATE_WITNESS,), binding
        )
        decision, response_value = machine.respond(
            response_public, response_private
        )
        receipts.append(
            AccessReceipt(
                RESPONSE,
                strategy.identity,
                decision,
                response_public.reads,
                response_private.reads,
                response_value,
            )
        )
        if decision is StrategyDecision.ABORTED:
            events.append(
                TraceEvent(
                    _ABORT_OCCURRENCE,
                    TraceKind.FAILURE,
                    Actor.PROVER,
                    {"at": RESPONSE, "class": "ExplicitProverAbort"},
                    strategy.identity,
                )
            )
            record = _make_record(
                request,
                binding,
                strategy,
                basis,
                protocol,
                profile,
                core,
                events,
                receipts,
                challenge_receipt,
                Disposition.ABORT,
            )
        else:
            if response_value is None or not profile.valid_scalar(response_value):
                return result(
                    Outcome.CHECKER_FAILURE,
                    "execution:response",
                    "P01-EXEC-003",
                    "closed strategy escaped the admitted response domain",
                    subject=request.identity,
                )
            visible[RESPONSE] = response_value
            events.append(
                TraceEvent(
                    RESPONSE,
                    TraceKind.MESSAGE,
                    Actor.PROVER,
                    response_value,
                    strategy.identity,
                )
            )
            equation_holds = _evaluate_core_verifier_check(
                core, profile, visible
            )
            visible[core.verifier_check.output_occurrence] = equation_holds
            events.append(
                TraceEvent(
                    core.verifier_check.output_occurrence,
                    TraceKind.CHECK,
                    Actor.VERIFIER,
                    equation_holds,
                    core.verifier_check.semantic_contract_id,
                )
            )
            disposition = _route_core_terminal(core, equation_holds)
            events.append(
                TraceEvent(
                    core.terminal_route.output_occurrence,
                    TraceKind.TERMINAL,
                    Actor.VERIFIER,
                    disposition,
                    core.terminal_route.semantic_contract_id,
                )
            )
            record = _make_record(
                request,
                binding,
                strategy,
                basis,
                protocol,
                profile,
                core,
                events,
                receipts,
                challenge_receipt,
                disposition,
            )
    except _AccessFailure as failure:
        return failure.check_result
    except (AssertionError, KeyError, RuntimeError, TypeError, ValueError) as error:
        return result(
            Outcome.CHECKER_FAILURE,
            "execution:evaluator",
            "P01-EXEC-004",
            f"closed evaluator failed: {error}",
            subject=request.identity,
        )

    if any(
        used > allowed
        for used, allowed in zip(
            _usage_values(record.usage),
            _resource_values(request.resources),
            strict=True,
        )
    ):
        return result(
            Outcome.CHECKER_FAILURE,
            "execution:resource-accounting",
            "P01-EXEC-005",
            "actual usage escaped its pre-admitted request budget",
            subject=request.identity,
            actual=record.usage.term(),
        )
    return record


def validate_terminal_law(
    request: PublicExecutionRequest,
    record: ExecutionRecord,
) -> Result:
    """Validate Core termination or an execution-level prover abort.

    ``Accept`` and ``Reject`` must be routed by the Core.  ``Abort`` closes only
    this evaluator invocation and therefore must not manufacture either the
    Core verifier-check occurrence or the Core terminal occurrence.  None of
    these dispositions is an evaluator ``Result`` outcome.
    """

    if not isinstance(record, ExecutionRecord):
        return result(
            Outcome.MALFORMED,
            "execution-terminal",
            "P01-TERMINAL-001",
            "execution record has the wrong type",
        )
    if record.request_id != request.identity or not record.events:
        return result(
            Outcome.MISMATCH,
            "execution-terminal:request",
            "P01-TERMINAL-002",
            "terminal record is empty or names a different request",
            subject=record.identity,
        )
    if not isinstance(record.disposition, Disposition):
        return result(
            Outcome.MALFORMED,
            "execution-terminal:disposition",
            "P01-TERMINAL-005",
            "execution disposition is outside the closed evaluator vocabulary",
            subject=record.identity,
        )
    checks = tuple(
        event
        for event in record.events
        if event.occurrence == record.verifier_check_rule.output_occurrence
    )
    terminals = tuple(
        event
        for event in record.events
        if event.occurrence == record.terminal_route_rule.output_occurrence
        or event.kind is TraceKind.TERMINAL
    )
    failures = tuple(
        event for event in record.events if event.occurrence == _ABORT_OCCURRENCE
    )
    if record.disposition is Disposition.ABORT:
        final = record.events[-1]
        valid = (
            not checks
            and not terminals
            and len(failures) == 1
            and failures[0] is final
            and final.kind is TraceKind.FAILURE
            and final.actor is Actor.PROVER
            and final.authority_id == record.strategy_id
            and final.value
            == {"at": RESPONSE, "class": "ExplicitProverAbort"}
        )
    else:
        final = record.events[-1]
        terminal_closed = (
            len(terminals) == 1
            and terminals[0] is final
            and final.occurrence
            == record.terminal_route_rule.output_occurrence
            and final.kind is TraceKind.TERMINAL
            and final.actor is Actor.VERIFIER
            and final.value is record.disposition
            and final.authority_id
            == record.terminal_route_rule.semantic_contract_id
        )
        if not terminal_closed:
            return result(
                Outcome.SEMANTIC_NEGATIVE,
                "execution-terminal:closure",
                "P01-TERMINAL-003",
                "Core terminal event and execution disposition disagree",
                subject=record.identity,
            )
        if record.disposition is Disposition.ACCEPT:
            valid = (
                len(checks) == 1
                and checks[0].kind is TraceKind.CHECK
                and checks[0].actor is Actor.VERIFIER
                and checks[0].value is True
                and checks[0].authority_id
                == record.verifier_check_rule.semantic_contract_id
                and not failures
            )
        else:
            valid = (
                len(checks) == 1
                and checks[0].kind is TraceKind.CHECK
                and checks[0].actor is Actor.VERIFIER
                and checks[0].value is False
                and checks[0].authority_id
                == record.verifier_check_rule.semantic_contract_id
                and not failures
            )
    if not valid:
        return result(
            Outcome.SEMANTIC_NEGATIVE,
            "execution-terminal:meaning",
            "P01-TERMINAL-004",
            "disposition does not have its exact Core check or execution-abort witness",
            subject=record.identity,
        )
    return affirmative(
        "execution-terminal",
        "P01-TERMINAL-OK",
        "execution disposition has its exact Core-terminal or evaluator-abort witness",
        subject=record.identity,
        disposition=record.disposition.value,
        core_terminal_emitted=record.disposition is not Disposition.ABORT,
    )


def qualify_execution(
    request: PublicExecutionRequest,
    binding: PrivateLocalBinding,
    strategy: ProverStrategy,
    basis: EvaluatorBasis,
    protocol: ProtocolVariant,
    profile: AlgebraProfile,
    core: ConversationCore,
    record: ExecutionRecord,
    *,
    fresh: FreshRealization | None = None,
    construction: TranscriptConstruction | None = None,
) -> QualifiedExecution | Result:
    """Reexecute exact inputs; the supplied record has no authoring authority."""

    if not isinstance(record, ExecutionRecord):
        return result(
            Outcome.MALFORMED,
            "execution-qualification",
            "P01-QUAL-001",
            "candidate record has the wrong type",
        )
    admitted = admit_request(
        request,
        basis,
        protocol,
        profile,
        core,
        fresh=fresh,
        construction=construction,
    )
    if admitted.outcome is not Outcome.AFFIRMATIVE:
        return admitted
    try:
        record_id = record.identity
    except (AttributeError, TermEncodingError, TypeError, ValueError) as error:
        return result(
            Outcome.MALFORMED,
            "execution-qualification",
            "P01-QUAL-006",
            f"candidate record identity is malformed: {error}",
        )
    replay_bound = preadmit_resources(
        request, protocol, basis, for_replay=True
    )
    if isinstance(replay_bound, Result):
        return replay_bound
    expected = execute(
        request,
        binding,
        strategy,
        basis,
        protocol,
        profile,
        core,
        fresh=fresh,
        construction=construction,
    )
    if isinstance(expected, Result):
        return expected
    if record != expected or record_id != expected.identity:
        return result(
            Outcome.MISMATCH,
            "execution-qualification:exact-replay",
            "P01-QUAL-002",
            "candidate record differs from exact evaluator reexecution",
            subject=record_id,
            expected_record_id=expected.identity,
        )
    terminal_result = validate_terminal_law(request, record)
    if terminal_result.outcome is not Outcome.AFFIRMATIVE:
        return terminal_result
    replay_usage = replace(record.usage, replay_executions=1)
    if any(
        used > allowed
        for used, allowed in zip(
            _usage_values(replay_usage),
            _resource_values(request.resources),
            strict=True,
        )
    ):
        return result(
            Outcome.CHECKER_FAILURE,
            "execution-qualification:resource-accounting",
            "P01-QUAL-003",
            "replay usage escaped the pre-admitted qualification budget",
            subject=record_id,
        )
    return QualifiedExecution(
        request,
        binding,
        strategy,
        basis,
        protocol,
        profile,
        core,
        record,
        replay_usage,
        fresh,
        construction,
    )


def requalify(qualified: QualifiedExecution) -> QualifiedExecution | Result:
    if not isinstance(qualified, QualifiedExecution):
        return result(
            Outcome.MALFORMED,
            "execution-qualification",
            "P01-QUAL-004",
            "qualified execution has the wrong type",
        )
    replayed = qualify_execution(
        qualified.request,
        qualified.local_binding,
        qualified.strategy,
        qualified.evaluator_basis,
        qualified.protocol,
        qualified.profile,
        qualified.core,
        qualified.record,
        fresh=qualified.fresh,
        construction=qualified.construction,
    )
    if isinstance(replayed, Result):
        return replayed
    if replayed.identity != qualified.identity:
        return result(
            Outcome.MISMATCH,
            "execution-qualification:identity",
            "P01-QUAL-005",
            "qualified execution identity differs after exact replay",
            subject=qualified.identity,
        )
    return replayed


def check_qualified_execution(qualified: QualifiedExecution) -> Result:
    """Execution-owner judgment: exact replay precedes every affirmation."""

    replayed = requalify(qualified)
    if isinstance(replayed, Result):
        return replayed
    return affirmative(
        "execution-owner:qualified-execution",
        "P01-OWNER-QUAL-OK",
        "the exact request and local binding reproduce the retained record",
        subject=replayed.identity,
        execution_record_id=replayed.record.identity,
        public_request_id=replayed.request.identity,
        protocol_id=replayed.protocol.identity,
        core_id=replayed.core.identity,
        disposition=replayed.record.disposition.value,
        validation_basis_id=replayed.evaluator_basis.identity,
    )


def _statement_from_replayed(replayed: QualifiedExecution) -> Any | Result:
    try:
        from .relations import QualifiedExecutionStatement

        statement_contract = replayed.core.contract_for(STATEMENT)
        source_event_id = semantic_id(
            "p01.qualified-invocation-input-occurrence.v1",
            {
                "qualification": replayed.identity,
                "execution": replayed.record.identity,
                "public_request": replayed.request.identity,
                "occurrence_contract": statement_contract.term(),
                "occurrence": STATEMENT,
                "value": replayed.request.statement,
            },
        )
        return QualifiedExecutionStatement(
            qualification_id=replayed.identity,
            execution_id=replayed.record.identity,
            protocol_id=replayed.protocol.identity,
            core_id=replayed.core.identity,
            evaluation_profile_id=replayed.profile.identity,
            occurrence=STATEMENT,
            value=replayed.request.statement,
            source_event_id=source_event_id,
        )
    except ImportError as error:
        return result(
            Outcome.MISSING_DEPENDENCY,
            "execution-owner:statement-export",
            "P01-OWNER-EXPORT-001",
            f"Relations statement adapter is unavailable: {error}",
            subject=replayed.identity,
        )
    except (AttributeError, KeyError, TermEncodingError, TypeError, ValueError) as error:
        return result(
            Outcome.CHECKER_FAILURE,
            "execution-owner:statement-export",
            "P01-OWNER-EXPORT-002",
            f"qualified statement export failed: {error}",
            subject=replayed.identity,
        )


def export_qualified_statement(
    qualified: QualifiedExecution,
) -> Any | Result:
    """Export the narrow Relations adapter only after execution-owned replay."""

    replayed = requalify(qualified)
    if isinstance(replayed, Result):
        return replayed
    return _statement_from_replayed(replayed)


def check_qualified_execution_grounding(
    qualified: QualifiedExecution,
    relation: Any,
    instance: Any,
) -> Result:
    """Mint grounding only from replayed execution, never an authored adapter."""

    replayed = requalify(qualified)
    if isinstance(replayed, Result):
        return replayed
    statement = _statement_from_replayed(replayed)
    if isinstance(statement, Result):
        return statement
    try:
        from .relations import check_grounding_shape, grounding_candidate

        grounding = grounding_candidate(instance, relation, statement)
        shape_result = check_grounding_shape(
            grounding,
            instance,
            relation,
            statement,
            replayed.profile,
        )
    except ImportError as error:
        return result(
            Outcome.MISSING_DEPENDENCY,
            "execution-owner:relation-grounding",
            "P01-OWNER-GROUND-001",
            f"Relations grounding checker is unavailable: {error}",
            subject=replayed.identity,
        )
    except (AttributeError, KeyError, TermEncodingError, TypeError, ValueError) as error:
        return result(
            Outcome.CHECKER_FAILURE,
            "execution-owner:relation-grounding",
            "P01-OWNER-GROUND-002",
            f"execution-owned grounding evaluation failed: {error}",
            subject=replayed.identity,
        )
    if not isinstance(shape_result, Result):
        return result(
            Outcome.CHECKER_FAILURE,
            "execution-owner:relation-grounding",
            "P01-OWNER-GROUND-003",
            "Relations grounding checker returned a non-Result value",
            subject=replayed.identity,
        )
    if shape_result.outcome is not Outcome.AFFIRMATIVE:
        return shape_result
    return affirmative(
        "execution-owner:relation-grounding",
        "P01-OWNER-GROUND-OK",
        "exact replay and same-domain statement equality ground the relation instance in this execution",
        subject=grounding.identity,
        qualification_id=replayed.identity,
        execution_record_id=replayed.record.identity,
        relation_id=relation.identity,
        relation_instance_id=instance.identity,
        statement_occurrence_id=statement.identity,
        shape_result_id=shape_result.subject,
        non_claim="does not widen one execution into completeness, soundness, or security",
    )


def check_qualified_private_witness_grounding(
    qualified: QualifiedExecution,
    relation: Any,
    instance: Any,
) -> Result:
    """Ground the replay-owned local witness as a separate private judgment.

    The witness assignment is constructed here from the retained private
    binding after exact replay.  The public result exposes only its occurrence
    handle.  This does not mint public statement grounding, relation
    satisfaction, or protocol acceptance; those remain separate judgments.
    """

    replayed = requalify(qualified)
    if isinstance(replayed, Result):
        return replayed
    try:
        from .relations import SchnorrWitnessAssignment, admit_witness_assignment

        witness = SchnorrWitnessAssignment(
            instance_id=instance.identity,
            occurrence="execution-local:witness:x",
            secret_scalar=replayed.local_binding.witness,
        )
        witness_result = admit_witness_assignment(
            witness,
            instance,
            relation,
            replayed.profile,
        )
    except ImportError as error:
        return result(
            Outcome.MISSING_DEPENDENCY,
            "execution-owner:private-witness-grounding",
            "P01-OWNER-WITNESS-001",
            f"Relations witness checker is unavailable: {error}",
            subject=replayed.identity,
        )
    except (AttributeError, KeyError, TermEncodingError, TypeError, ValueError) as error:
        return result(
            Outcome.CHECKER_FAILURE,
            "execution-owner:private-witness-grounding",
            "P01-OWNER-WITNESS-002",
            f"execution-owned private witness grounding failed: {error}",
            subject=replayed.identity,
        )
    if not isinstance(witness_result, Result):
        return result(
            Outcome.CHECKER_FAILURE,
            "execution-owner:private-witness-grounding",
            "P01-OWNER-WITNESS-003",
            "Relations witness checker returned a non-Result value",
            subject=replayed.identity,
        )
    if witness_result.outcome is not Outcome.AFFIRMATIVE:
        return witness_result
    if instance.public_statement != replayed.request.statement:
        return result(
            Outcome.MISMATCH,
            "execution-owner:private-witness-grounding:instance",
            "P01-OWNER-WITNESS-004",
            "relation instance does not carry the replayed execution's exact statement",
            subject=replayed.identity,
            relation_instance_id=instance.identity,
        )
    grounding_id = semantic_id(
        "p01.execution-private-witness-grounding.v1",
        {
            "qualification": replayed.identity,
            "execution_record": replayed.record.identity,
            "local_binding": replayed.local_binding.identity,
            "relation": relation.identity,
            "relation_instance": instance.identity,
            "witness_occurrence": witness.public_reference,
            "law": "ExactReplayOwnedPrivateBindingOccurrence.v1",
        },
    )
    return affirmative(
        "execution-owner:private-witness-grounding",
        "P01-OWNER-WITNESS-OK",
        "exact replay grounds the retained local witness in this relation-instance occurrence",
        subject=grounding_id,
        qualification_id=replayed.identity,
        execution_record_id=replayed.record.identity,
        local_binding_id=replayed.local_binding.identity,
        relation_id=relation.identity,
        relation_instance_id=instance.identity,
        witness_occurrence=witness.public_reference,
        non_claim="not public statement grounding, relation satisfaction, protocol acceptance, or witness possession beyond this retained replay binding",
    )


def _requalify_coupled_pair(
    fresh_qualified: QualifiedExecution,
    fs_qualified: QualifiedExecution,
) -> tuple[QualifiedExecution, QualifiedExecution] | Result:
    if not isinstance(fresh_qualified, QualifiedExecution) or not isinstance(
        fs_qualified, QualifiedExecution
    ):
        return result(
            Outcome.MALFORMED,
            "execution-coupling",
            "P01-COUPLE-001",
            "coupling operands must be qualified executions",
        )
    fresh_replayed = requalify(fresh_qualified)
    if isinstance(fresh_replayed, Result):
        return fresh_replayed
    fs_replayed = requalify(fs_qualified)
    if isinstance(fs_replayed, Result):
        return fs_replayed
    if (
        fresh_replayed.protocol.realization_kind is not RealizationKind.FRESH
        or fs_replayed.protocol.realization_kind is not RealizationKind.FIAT_SHAMIR
    ):
        return result(
            Outcome.MISMATCH,
            "execution-coupling:realization-roles",
            "P01-COUPLE-002",
            "coupling requires Fresh on the left and Fiat-Shamir on the right",
            fresh_protocol_id=fresh_replayed.protocol.identity,
            fs_protocol_id=fs_replayed.protocol.identity,
        )
    if fresh_replayed.protocol.identity == fs_replayed.protocol.identity:
        return result(
            Outcome.REFUSED,
            "execution-coupling:protocol-equality",
            "P01-COUPLE-003",
            "distinct challenge realizations cannot be retyped as one Protocol",
            subject=fresh_replayed.protocol.identity,
        )
    return fresh_replayed, fs_replayed


def compare_coupled_fresh_fs(
    fresh_qualified: QualifiedExecution,
    fs_qualified: QualifiedExecution,
) -> Result:
    """Compare one Fresh support point with one equal-challenge FS point.

    The result is pointwise only.  In particular, it says nothing about the
    Fresh distribution, random-oracle distributions, or theorem transport.
    """

    replayed = _requalify_coupled_pair(fresh_qualified, fs_qualified)
    if isinstance(replayed, Result):
        return replayed
    fresh, fs = replayed
    if (
        fresh.core.identity != fs.core.identity
        or fresh.profile.identity != fs.profile.identity
        or fresh.protocol.honest_prover_contract_id
        != fs.protocol.honest_prover_contract_id
    ):
        return result(
            Outcome.MISMATCH,
            "execution-coupling:semantic-scope",
            "P01-COUPLE-004",
            "coupled executions do not share one Core, evaluation profile, and honest-prover contract",
            fresh_core_id=fresh.core.identity,
            fs_core_id=fs.core.identity,
        )
    if fresh.request.statement != fs.request.statement:
        return result(
            Outcome.MISMATCH,
            "execution-coupling:runtime-inputs",
            "P01-COUPLE-005",
            "coupled executions differ in their shared runtime statement",
            fresh_request_id=fresh.request.identity,
            fs_request_id=fs.request.identity,
        )
    if (
        fresh.request.application_context is not None
        or not isinstance(fs.request.application_context, str)
    ):
        return result(
            Outcome.MISMATCH,
            "execution-coupling:realization-context-authority",
            "P01-COUPLE-009",
            "Fresh must have no application context while Fiat-Shamir owns one",
            fresh_request_id=fresh.request.identity,
            fs_request_id=fs.request.identity,
        )
    fresh_challenge = fresh.record.value_for(CHALLENGE)
    fs_challenge = fs.record.value_for(CHALLENGE)
    if fresh_challenge != fs_challenge:
        return result(
            Outcome.MISMATCH,
            "execution-coupling:challenge",
            "P01-COUPLE-006",
            "Fresh support point does not equal the derived Fiat-Shamir challenge",
            fresh_challenge=fresh_challenge,
            fs_challenge=fs_challenge,
        )

    def optional_value(record: ExecutionRecord, occurrence: str) -> tuple[bool, Any]:
        try:
            return True, record.value_for(occurrence)
        except KeyError:
            return False, None

    fresh_point = (
        optional_value(fresh.record, COMMITMENT),
        optional_value(fresh.record, RESPONSE),
        fresh.record.disposition,
    )
    fs_point = (
        optional_value(fs.record, COMMITMENT),
        optional_value(fs.record, RESPONSE),
        fs.record.disposition,
    )
    if fresh_point != fs_point:
        return result(
            Outcome.MISMATCH,
            "execution-coupling:pointwise-behavior",
            "P01-COUPLE-007",
            "commitment, response, or disposition differs at the coupled point",
            fresh_execution_id=fresh.record.identity,
            fs_execution_id=fs.record.identity,
        )
    comparison_id = semantic_id(
        "p01.coupled-fresh-fs-point.v1",
        {
            "fresh_qualification": fresh.identity,
            "fs_qualification": fs.identity,
            "core": fresh.core.identity,
            "fs_application_context": fs.request.application_context,
            "statement": fresh.request.statement,
            "challenge": fresh_challenge,
            "commitment": fresh_point[0],
            "response": fresh_point[1],
            "disposition": fresh.record.disposition.value,
        },
    )
    return affirmative(
        "execution-coupling:pointwise-behavior",
        "P01-COUPLE-OK",
        "Fresh and Fiat-Shamir executions agree at one exact equal-challenge point",
        subject=comparison_id,
        fresh_qualification_id=fresh.identity,
        fs_qualification_id=fs.identity,
        fresh_protocol_id=fresh.protocol.identity,
        fs_protocol_id=fs.protocol.identity,
        core_id=fresh.core.identity,
        fs_application_context=fs.request.application_context,
        challenge=fresh_challenge,
        non_claim="not Protocol equality, distribution equality, or security transport",
    )


def claim_coupled_protocol_equality(
    fresh_qualified: QualifiedExecution,
    fs_qualified: QualifiedExecution,
) -> Result:
    """Explicitly refuse promotion of pointwise coupling to Protocol equality."""

    replayed = _requalify_coupled_pair(fresh_qualified, fs_qualified)
    if isinstance(replayed, Result):
        return replayed
    fresh, fs = replayed
    return result(
        Outcome.REFUSED,
        "execution-coupling:protocol-equality",
        "P01-COUPLE-008",
        "shared Core or pointwise equality does not identify distinct Protocol variants",
        subject=semantic_id(
            "p01.refused-protocol-equality-claim.v1",
            {
                "fresh_protocol": fresh.protocol.identity,
                "fs_protocol": fs.protocol.identity,
                "shared_core": fresh.core.identity,
            },
        ),
        fresh_protocol_id=fresh.protocol.identity,
        fs_protocol_id=fs.protocol.identity,
        core_id=fresh.core.identity,
        missing_capability="a semantic equality law over realization identity",
    )
