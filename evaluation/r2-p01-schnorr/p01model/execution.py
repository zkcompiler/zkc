"""Two-lane execution and exact public replay for the finite P01 witness.

The portable lane contains only public invocation data, public protocol events,
and source-bound replay qualification.  The owner-local lane contains witness
material, nonce material, a response plan, and access receipts.  No object from
the owner-local lane has a semantic identity, finite term, or serialization
path.  Exact portable replay and read-only confidential audit reconstruction are
separate checks.

Canonical generation uses a Relations-issued satisfaction capability when
a challenge-neutral invocation occurrence is precommitted.  This module
deliberately does not re-evaluate the relation equation at that boundary.

This is a bounded executable model, not a cryptographic implementation or a
sandbox for caller-supplied Python code.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from pathlib import Path
import re
from typing import Any, Iterable

from .provenance import (
    ArtifactContentId,
    EvidenceRecordId,
    ProvenanceError,
    SourceEntry,
    ValidationBasisId,
    bind_loaded_root,
    canonical_json_content_id,
    evidence_record_id,
    validation_basis_id,
)

from .semantic import (
    CHALLENGE,
    CHECK,
    COMMITMENT,
    RESPONSE,
    STATEMENT,
    TERMINAL,
    AlgebraProfile,
    ConversationCore,
    FreshRealization,
    ProtocolVariant,
    RealizationKind,
    TranscriptConstruction,
    admit_application_context,
    admit_core,
    admit_honest_prover_contract,
    admit_protocol,
    canonical_honest_prover_contract,
    derive_fs_challenge,
    honest_witness_precondition_contract_id,
)
from .terms import Outcome, Result, TermEncodingError, affirmative, result


_REPO_ROOT = Path(__file__).resolve().parents[3]
_CONTENT_ID = re.compile(r"sha256:[0-9a-f]{64}\Z")
_EVALUATOR_SOURCES = (
    ("package-initializer", "evaluation/r2-p01-schnorr/p01model/__init__.py"),
    ("closed-term", "evaluation/r2-p01-schnorr/p01model/terms.py"),
    ("provenance", "evaluation/r2-p01-schnorr/p01model/provenance.py"),
    ("protocol-semantics", "evaluation/r2-p01-schnorr/p01model/semantic.py"),
    ("public-execution", "evaluation/r2-p01-schnorr/p01model/execution.py"),
    ("proof-interface", "evaluation/r2-p01-schnorr/p01model/interface.py"),
)
_PUBLIC_REPLAY_LAW = "p01.exact-portable-public-replay.v2"


def _is_semantic_id(value: Any) -> bool:
    return isinstance(value, str) and _CONTENT_ID.fullmatch(value) is not None


def _safe_identity(value: Any) -> str:
    try:
        identity = value.identity
    except (AttributeError, ProvenanceError, TermEncodingError, TypeError, ValueError):
        return ""
    if isinstance(identity, (ArtifactContentId, EvidenceRecordId, ValidationBasisId)):
        return str(identity)
    return identity if _is_semantic_id(identity) else ""


class Disposition(str, Enum):
    """A public verifier terminal value, distinct from ``Result.outcome``."""

    ACCEPT = "Accept"
    REJECT = "Reject"
    ABORT = "Abort"


class ResponsePlan(str, Enum):
    """Closed response-stage choices used by this finite probe.

    Commitment construction is not caller-selectable: ``precommit`` always
    executes the canonical transition before a challenge is available through
    the modeled capability flow.
    """

    CANONICAL = "CanonicalResponse"
    INVALID = "InvalidResponse"
    ABORT = "AbortResponse"


class TraceKind(str, Enum):
    MESSAGE = "Message"
    CHALLENGE = "Challenge"
    CHECK = "Check"
    TERMINAL = "Terminal"


class Actor(str, Enum):
    PROVER = "Prover"
    VERIFIER = "Verifier"
    PUBLIC_ENVIRONMENT = "PublicEnvironment"
    TRANSCRIPT_CONSTRUCTION = "TranscriptConstruction"


@dataclass(frozen=True)
class FreshChallengeBinding:
    """One public support point; it is not evidence of honest sampling."""

    core_id: str
    protocol_id: str
    challenge_occurrence: str
    value: int
    source_id: ArtifactContentId

    def term(self) -> dict[str, Any]:
        return {
            "core_id": self.core_id,
            "protocol_id": self.protocol_id,
            "challenge_occurrence": self.challenge_occurrence,
            "value": self.value,
            "source_id": str(self.source_id),
        }

    @property
    def identity(self) -> ArtifactContentId:
        return canonical_json_content_id(self.term())


@dataclass(frozen=True)
class PublicResourcePlan:
    max_transcript_atoms: int
    max_hash_queries: int
    max_trace_events: int
    max_replay_executions: int

    def term(self) -> dict[str, int]:
        return {
            "max_transcript_atoms": self.max_transcript_atoms,
            "max_hash_queries": self.max_hash_queries,
            "max_trace_events": self.max_trace_events,
            "max_replay_executions": self.max_replay_executions,
        }


@dataclass(frozen=True)
class PublicResourceUsage:
    transcript_atoms: int
    hash_queries: int
    trace_events: int

    def term(self) -> dict[str, int]:
        return {
            "transcript_atoms": self.transcript_atoms,
            "hash_queries": self.hash_queries,
            "trace_events": self.trace_events,
        }


@dataclass(frozen=True)
class LocalResourcePlan:
    max_strategy_steps: int
    max_public_reads: int
    max_private_reads: int


@dataclass(frozen=True)
class LocalResourceUsage:
    strategy_steps: int
    public_reads: int
    private_reads: int


MAX_PUBLIC_EVALUATOR_CAPS = PublicResourcePlan(2, 2, 5, 1)
DEFAULT_PUBLIC_RESOURCE_PLAN = MAX_PUBLIC_EVALUATOR_CAPS
DEFAULT_LOCAL_RESOURCE_PLAN = LocalResourcePlan(2, 1, 2)


def _valid_nonnegative_int(value: Any) -> bool:
    return isinstance(value, int) and not isinstance(value, bool) and value >= 0


def _valid_public_plan(plan: Any) -> bool:
    return isinstance(plan, PublicResourcePlan) and all(
        _valid_nonnegative_int(value)
        for value in (
            plan.max_transcript_atoms,
            plan.max_hash_queries,
            plan.max_trace_events,
            plan.max_replay_executions,
        )
    )


def _valid_local_plan(plan: Any) -> bool:
    return isinstance(plan, LocalResourcePlan) and all(
        _valid_nonnegative_int(value)
        for value in (
            plan.max_strategy_steps,
            plan.max_public_reads,
            plan.max_private_reads,
        )
    )


def public_usage_fits(usage: PublicResourceUsage, plan: PublicResourcePlan) -> bool:
    """Return whether exact public work fits an admitted resource plan."""

    return (
        usage.transcript_atoms <= plan.max_transcript_atoms
        and usage.hash_queries <= plan.max_hash_queries
        and usage.trace_events <= plan.max_trace_events
    )


def _local_usage_fits(usage: LocalResourceUsage, plan: LocalResourcePlan) -> bool:
    return (
        usage.strategy_steps <= plan.max_strategy_steps
        and usage.public_reads <= plan.max_public_reads
        and usage.private_reads <= plan.max_private_reads
    )


@dataclass(frozen=True)
class EvaluatorBasis:
    """Public validation basis; never a Protocol semantic identity."""

    qualification_law: str
    supported_protocol_ids: tuple[str, ...]
    source_manifest: tuple[SourceEntry, ...]
    hard_caps: PublicResourcePlan

    def term(self) -> dict[str, Any]:
        return {
            "qualification_law": self.qualification_law,
            "supported_protocol_ids": list(self.supported_protocol_ids),
            "source_manifest": [source.term() for source in self.source_manifest],
            "hard_caps": self.hard_caps.term(),
        }

    @property
    def identity(self) -> ValidationBasisId:
        return validation_basis_id("p01-public-evaluator", self.term())


def _source_manifest(repo_root: Path) -> tuple[SourceEntry, ...]:
    return tuple(
        SourceEntry.from_current_file(repo_root, role=role, path=relative_path)
        for role, relative_path in sorted(_EVALUATOR_SOURCES)
    )


def build_evaluator_basis(
    repo_root: Path,
    supported_protocol_ids: Iterable[str],
    hard_caps: PublicResourcePlan = DEFAULT_PUBLIC_RESOURCE_PLAN,
) -> EvaluatorBasis:
    """Bind public qualification to the implementation loaded in this process."""

    resolved = bind_loaded_root(repo_root)
    return EvaluatorBasis(
        _PUBLIC_REPLAY_LAW,
        tuple(sorted(set(supported_protocol_ids))),
        _source_manifest(resolved),
        hard_caps,
    )


def admit_evaluator_basis(basis: EvaluatorBasis) -> Result:
    if not isinstance(basis, EvaluatorBasis):
        return result(
            Outcome.MALFORMED,
            "public-evaluator-basis",
            "P01-BASIS-001",
            "public evaluator basis has the wrong type",
        )
    try:
        basis_id = basis.identity
    except (AttributeError, ProvenanceError, TermEncodingError, TypeError, ValueError):
        return result(
            Outcome.MALFORMED,
            "public-evaluator-basis",
            "P01-BASIS-001",
            "public evaluator basis is outside the closed grammar",
        )
    if (
        basis.qualification_law != _PUBLIC_REPLAY_LAW
        or not basis.supported_protocol_ids
        or tuple(sorted(set(basis.supported_protocol_ids)))
        != basis.supported_protocol_ids
        or any(not _is_semantic_id(value) for value in basis.supported_protocol_ids)
        or not _valid_public_plan(basis.hard_caps)
    ):
        return result(
            Outcome.MALFORMED,
            "public-evaluator-basis",
            "P01-BASIS-001",
            "public evaluator basis has malformed support or resource fields",
            subject=str(basis_id),
        )
    if any(
        actual > maximum
        for actual, maximum in zip(
            (
                basis.hard_caps.max_transcript_atoms,
                basis.hard_caps.max_hash_queries,
                basis.hard_caps.max_trace_events,
                basis.hard_caps.max_replay_executions,
            ),
            (
                MAX_PUBLIC_EVALUATOR_CAPS.max_transcript_atoms,
                MAX_PUBLIC_EVALUATOR_CAPS.max_hash_queries,
                MAX_PUBLIC_EVALUATOR_CAPS.max_trace_events,
                MAX_PUBLIC_EVALUATOR_CAPS.max_replay_executions,
            ),
            strict=True,
        )
    ):
        return result(
            Outcome.RESOURCE_EXCEEDED,
            "public-evaluator-basis:resources",
            "P01-BASIS-003",
            "public evaluator hard caps exceed this finite implementation",
            subject=str(basis_id),
        )
    try:
        current_sources = _source_manifest(_REPO_ROOT)
    except (OSError, ProvenanceError):
        return result(
            Outcome.MISSING_DEPENDENCY,
            "public-evaluator-basis:sources",
            "P01-BASIS-002",
            "a public evaluator source cannot be read",
            subject=str(basis_id),
        )
    if basis.source_manifest != current_sources:
        return result(
            Outcome.MISMATCH,
            "public-evaluator-basis:sources",
            "P01-BASIS-002",
            "public evaluator source digests differ from the loaded checkout",
            subject=str(basis_id),
        )
    return affirmative(
        "public-evaluator-basis",
        "P01-BASIS-OK",
        "public evaluator basis is bound to the loaded implementation",
        subject=str(basis_id),
    )


@dataclass(frozen=True)
class PublicInvocationPrefix:
    """Public invocation data available before any challenge is resolved."""

    algebra_profile_id: str
    core_id: str
    protocol_id: str
    statement: int
    application_context: str | None

    def term(self) -> dict[str, Any]:
        return {
            "algebra_profile_id": self.algebra_profile_id,
            "core_id": self.core_id,
            "protocol_id": self.protocol_id,
            "statement": self.statement,
            "application_context": self.application_context,
        }

    @property
    def identity(self) -> ArtifactContentId:
        return canonical_json_content_id(self.term())


@dataclass(frozen=True)
class PublicInvocation:
    """Complete portable public inputs for one protocol invocation value."""

    algebra_profile_id: str
    core_id: str
    protocol_id: str
    statement: int
    application_context: str | None
    fresh_challenge: FreshChallengeBinding | None = None

    def prefix(self) -> PublicInvocationPrefix:
        return PublicInvocationPrefix(
            self.algebra_profile_id,
            self.core_id,
            self.protocol_id,
            self.statement,
            self.application_context,
        )

    def term(self) -> dict[str, Any]:
        return {
            **self.prefix().term(),
            "fresh_challenge_id": (
                str(self.fresh_challenge.identity) if self.fresh_challenge else None
            ),
        }

    @property
    def identity(self) -> ArtifactContentId:
        return canonical_json_content_id(self.term())


def admit_public_invocation_prefix(
    prefix: PublicInvocationPrefix,
    protocol: ProtocolVariant,
    profile: AlgebraProfile,
    core: ConversationCore,
    *,
    fresh: FreshRealization | None = None,
    construction: TranscriptConstruction | None = None,
) -> Result:
    if not isinstance(prefix, PublicInvocationPrefix):
        return result(
            Outcome.MALFORMED,
            "public-invocation-prefix",
            "P01-INV-001",
            "public invocation prefix has the wrong type",
        )
    try:
        prefix_id = prefix.identity
        protocol_id = protocol.identity
        profile_id = profile.identity
        core_id = core.identity
    except (AttributeError, ProvenanceError, TermEncodingError, TypeError, ValueError):
        return result(
            Outcome.MALFORMED,
            "public-invocation-prefix",
            "P01-INV-001",
            "public invocation prefix or semantic dependency is outside the closed grammar",
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
    if (
        prefix.algebra_profile_id != profile_id
        or prefix.core_id != core_id
        or prefix.protocol_id != protocol_id
    ):
        return result(
            Outcome.MISMATCH,
            "public-invocation-prefix:scope",
            "P01-INV-002",
            "public invocation prefix names different profile, Core, or Protocol",
            subject=str(prefix_id),
        )
    if not profile.valid_group_element(prefix.statement):
        return result(
            Outcome.SEMANTIC_NEGATIVE,
            "public-invocation-prefix:statement",
            "P01-INV-003",
            "public Statement is outside the admitted group domain",
            subject=str(prefix_id),
        )
    if protocol.realization_kind is RealizationKind.FRESH:
        if prefix.application_context is not None:
            return result(
                Outcome.MISMATCH,
                "public-invocation-prefix:fresh-input",
                "P01-INV-004",
                "Fresh invocation prefix must not author Fiat-Shamir context",
                subject=str(prefix_id),
            )
    else:
        context_result = admit_application_context(prefix.application_context)
        if context_result.outcome is not Outcome.AFFIRMATIVE:
            return context_result
    return affirmative(
        "public-invocation-prefix",
        "P01-INV-OK",
        "challenge-neutral public invocation prefix is admitted",
        subject=str(prefix_id),
    )


def admit_public_invocation(
    invocation: PublicInvocation,
    protocol: ProtocolVariant,
    profile: AlgebraProfile,
    core: ConversationCore,
    *,
    fresh: FreshRealization | None = None,
    construction: TranscriptConstruction | None = None,
) -> Result:
    if not isinstance(invocation, PublicInvocation):
        return result(
            Outcome.MALFORMED,
            "public-invocation",
            "P01-INV-001",
            "public invocation has the wrong type",
        )
    prefix_result = admit_public_invocation_prefix(
        invocation.prefix(),
        protocol,
        profile,
        core,
        fresh=fresh,
        construction=construction,
    )
    if prefix_result.outcome is not Outcome.AFFIRMATIVE:
        return prefix_result
    invocation_id = invocation.identity
    if protocol.realization_kind is RealizationKind.FRESH:
        binding = invocation.fresh_challenge
        if (
            not isinstance(binding, FreshChallengeBinding)
            or binding.core_id != core.identity
            or binding.protocol_id != protocol.identity
            or binding.challenge_occurrence != CHALLENGE
            or not profile.valid_challenge(binding.value)
            or not isinstance(binding.source_id, ArtifactContentId)
        ):
            return result(
                Outcome.MISMATCH,
                "public-invocation:fresh-input",
                "P01-INV-004",
                "Fresh invocation lacks its exact public support point",
                subject=str(invocation_id),
            )
    elif invocation.fresh_challenge is not None:
        return result(
            Outcome.SEMANTIC_NEGATIVE,
            "public-invocation:fs-input",
            "P01-INV-004",
            "FS invocation must not author a Fresh challenge",
            subject=str(invocation_id),
        )
    return affirmative(
        "public-invocation",
        "P01-INV-OK",
        "complete public invocation is admitted",
        subject=str(invocation_id),
        fresh_non_claim=(
            "not evidence that the challenge was sampled from the Fresh kernel"
            if protocol.realization_kind is RealizationKind.FRESH
            else None
        ),
    )


@dataclass(frozen=True)
class TranscriptReadReceipt:
    source_kind: str
    occurrence: str
    value_domain_id: str
    codec: str
    framed_hex: str

    def term(self) -> dict[str, str]:
        return {
            "source_kind": self.source_kind,
            "occurrence": self.occurrence,
            "value_domain_id": self.value_domain_id,
            "codec": self.codec,
            "framed_hex": self.framed_hex,
        }


@dataclass(frozen=True)
class ChallengeReceipt:
    realization_kind: RealizationKind
    realization_id: str
    challenge: int
    source_artifact_id: ArtifactContentId | None
    query_hex: str
    reads: tuple[TranscriptReadReceipt, ...]

    def term(self) -> dict[str, Any]:
        return {
            "realization_kind": self.realization_kind.value,
            "realization_id": self.realization_id,
            "challenge": self.challenge,
            "source_artifact_id": (
                str(self.source_artifact_id) if self.source_artifact_id else None
            ),
            "query_hex": self.query_hex,
            "reads": [receipt.term() for receipt in self.reads],
        }


@dataclass(frozen=True)
class PublicTraceEvent:
    occurrence: str
    kind: TraceKind
    actor: Actor
    contract_id: str
    value: Any

    def term(self) -> dict[str, Any]:
        return {
            "occurrence": self.occurrence,
            "kind": self.kind.value,
            "actor": self.actor.value,
            "contract_id": self.contract_id,
            "value": self.value,
        }


@dataclass(frozen=True)
class PublicVerifierDecision:
    core_id: str
    verifier_check_contract_id: str
    terminal_contract_id: str
    check_value: bool
    disposition: Disposition

    def term(self) -> dict[str, Any]:
        return {
            "core_id": self.core_id,
            "verifier_check_contract_id": self.verifier_check_contract_id,
            "terminal_contract_id": self.terminal_contract_id,
            "check_value": self.check_value,
            "disposition": self.disposition.value,
        }

def evaluate_schnorr_verifier(
    core: ConversationCore,
    profile: AlgebraProfile,
    *,
    statement: int,
    commitment: int,
    challenge: int,
    response: int,
) -> PublicVerifierDecision | Result:
    """The sole implementation of the Schnorr equation and terminal routing."""

    core_result = admit_core(core, profile)
    if core_result.outcome is not Outcome.AFFIRMATIVE:
        return core_result
    if (
        not profile.valid_group_element(statement)
        or not profile.valid_group_element(commitment)
        or not profile.valid_challenge(challenge)
        or not profile.valid_scalar(response)
    ):
        return result(
            Outcome.SEMANTIC_NEGATIVE,
            "public-verifier:operand-domain",
            "P01-PUBLIC-VERIFY-001",
            "a public verifier operand is outside its declared domain",
            subject=core.identity,
        )
    check_value = (
        pow(profile.generator, response, profile.p)
        == (commitment * pow(statement, challenge, profile.p)) % profile.p
    )
    return PublicVerifierDecision(
        core.identity,
        core.verifier_check.semantic_contract_id,
        core.terminal_route.semantic_contract_id,
        check_value,
        Disposition.ACCEPT if check_value else Disposition.REJECT,
    )


@dataclass(frozen=True)
class PortableExecutionRecord:
    """Public execution facts; never an honest-prover or witness claim."""

    invocation_id: ArtifactContentId
    algebra_profile_id: str
    core_id: str
    protocol_id: str
    realization_kind: RealizationKind
    trace: tuple[PublicTraceEvent, ...]
    challenge_receipt: ChallengeReceipt
    verifier_decision: PublicVerifierDecision
    usage: PublicResourceUsage

    def term(self) -> dict[str, Any]:
        return {
            "invocation_id": str(self.invocation_id),
            "algebra_profile_id": self.algebra_profile_id,
            "core_id": self.core_id,
            "protocol_id": self.protocol_id,
            "realization_kind": self.realization_kind.value,
            "trace": [event.term() for event in self.trace],
            "challenge_receipt": self.challenge_receipt.term(),
            "verifier_decision": self.verifier_decision.term(),
            "usage": self.usage.term(),
        }

    @property
    def identity(self) -> ArtifactContentId:
        return canonical_json_content_id(self.term())


def _receipt_from_derived(raw: dict[str, Any]) -> TranscriptReadReceipt:
    return TranscriptReadReceipt(
        raw["source_kind"],
        raw["occurrence"],
        raw["value_domain_id"],
        raw["codec"],
        raw["encoded_hex"],
    )


def _challenge_for_invocation(
    invocation: PublicInvocation,
    protocol: ProtocolVariant,
    profile: AlgebraProfile,
    commitment: int,
    *,
    construction: TranscriptConstruction | None,
) -> ChallengeReceipt | Result:
    if protocol.realization_kind is RealizationKind.FRESH:
        binding = invocation.fresh_challenge
        if not isinstance(binding, FreshChallengeBinding):
            return result(
                Outcome.MISSING_DEPENDENCY,
                "public-execution:fresh-challenge",
                "P01-BUILD-002",
                "Fresh invocation has no public challenge binding",
                subject=_safe_identity(invocation),
            )
        return ChallengeReceipt(
            RealizationKind.FRESH,
            protocol.realization_id,
            binding.value,
            binding.source_id,
            "",
            (),
        )
    if not isinstance(construction, TranscriptConstruction):
        return result(
            Outcome.MISSING_DEPENDENCY,
            "public-execution:fs-construction",
            "P01-BUILD-002",
            "FS execution has no transcript construction",
            subject=_safe_identity(invocation),
        )
    try:
        challenge, query, raw_receipts = derive_fs_challenge(
            construction,
            profile,
            invocation.application_context,
            invocation.statement,
            commitment,
        )
        receipts = tuple(_receipt_from_derived(raw) for raw in raw_receipts)
    except (KeyError, TypeError, ValueError):
        return result(
            Outcome.MALFORMED,
            "public-execution:fs-challenge",
            "P01-BUILD-002",
            "FS challenge derivation failed on public inputs",
            subject=_safe_identity(invocation),
        )
    return ChallengeReceipt(
        RealizationKind.FIAT_SHAMIR,
        construction.identity,
        challenge,
        None,
        query.hex(),
        receipts,
    )


def build_portable_execution(
    invocation: PublicInvocation,
    commitment: int,
    response: int,
    protocol: ProtocolVariant,
    profile: AlgebraProfile,
    core: ConversationCore,
    *,
    fresh: FreshRealization | None = None,
    construction: TranscriptConstruction | None = None,
) -> PortableExecutionRecord | Result:
    """Evaluate public messages into one canonical portable record."""

    invocation_result = admit_public_invocation(
        invocation,
        protocol,
        profile,
        core,
        fresh=fresh,
        construction=construction,
    )
    if invocation_result.outcome is not Outcome.AFFIRMATIVE:
        return invocation_result
    if not profile.valid_group_element(commitment) or not profile.valid_scalar(response):
        return result(
            Outcome.SEMANTIC_NEGATIVE,
            "public-execution:message-domain",
            "P01-BUILD-001",
            "commitment or response is outside its public message domain",
            subject=str(invocation.identity),
        )
    challenge_receipt = _challenge_for_invocation(
        invocation,
        protocol,
        profile,
        commitment,
        construction=construction,
    )
    if isinstance(challenge_receipt, Result):
        return challenge_receipt
    decision = evaluate_schnorr_verifier(
        core,
        profile,
        statement=invocation.statement,
        commitment=commitment,
        challenge=challenge_receipt.challenge,
        response=response,
    )
    if isinstance(decision, Result):
        return decision
    challenge_actor = (
        Actor.PUBLIC_ENVIRONMENT
        if protocol.realization_kind is RealizationKind.FRESH
        else Actor.TRANSCRIPT_CONSTRUCTION
    )
    trace = (
        PublicTraceEvent(
            COMMITMENT,
            TraceKind.MESSAGE,
            Actor.PROVER,
            core.contract_for(COMMITMENT).semantic_contract_id,
            commitment,
        ),
        PublicTraceEvent(
            CHALLENGE,
            TraceKind.CHALLENGE,
            challenge_actor,
            core.contract_for(CHALLENGE).semantic_contract_id,
            challenge_receipt.challenge,
        ),
        PublicTraceEvent(
            RESPONSE,
            TraceKind.MESSAGE,
            Actor.PROVER,
            core.contract_for(RESPONSE).semantic_contract_id,
            response,
        ),
        PublicTraceEvent(
            CHECK,
            TraceKind.CHECK,
            Actor.VERIFIER,
            core.verifier_check.semantic_contract_id,
            decision.check_value,
        ),
        PublicTraceEvent(
            TERMINAL,
            TraceKind.TERMINAL,
            Actor.VERIFIER,
            core.terminal_route.semantic_contract_id,
            decision.disposition.value,
        ),
    )
    usage = PublicResourceUsage(
        len(challenge_receipt.reads),
        2 if protocol.realization_kind is RealizationKind.FIAT_SHAMIR else 0,
        len(trace),
    )
    return PortableExecutionRecord(
        invocation.identity,
        profile.identity,
        core.identity,
        protocol.identity,
        protocol.realization_kind,
        trace,
        challenge_receipt,
        decision,
        usage,
    )


def public_trace_value(record: PortableExecutionRecord, occurrence: str) -> Any | Result:
    if not isinstance(record, PortableExecutionRecord):
        return result(
            Outcome.MALFORMED,
            "portable-execution:trace",
            "P01-TRACE-001",
            "portable execution record has the wrong type",
        )
    matches = tuple(event.value for event in record.trace if event.occurrence == occurrence)
    if len(matches) != 1:
        return result(
            Outcome.MALFORMED,
            "portable-execution:trace",
            "P01-TRACE-001",
            "portable trace does not contain exactly one requested occurrence",
            subject=_safe_identity(record),
        )
    return matches[0]


@dataclass(frozen=True)
class PublicReplayRequest:
    """Exact candidate, validation basis, source, and public resource policy."""

    invocation: PublicInvocation
    candidate: PortableExecutionRecord
    evaluator_basis_id: ValidationBasisId
    public_case_bundle_id: ArtifactContentId
    resources: PublicResourcePlan = DEFAULT_PUBLIC_RESOURCE_PLAN

    def term(self) -> dict[str, Any]:
        return {
            "invocation_id": str(self.invocation.identity),
            "candidate_id": str(self.candidate.identity),
            "evaluator_basis_id": str(self.evaluator_basis_id),
            "public_case_bundle_id": str(self.public_case_bundle_id),
            "resources": self.resources.term(),
        }

    @property
    def identity(self) -> ArtifactContentId:
        return canonical_json_content_id(self.term())


@dataclass(frozen=True)
class CheckedPublicExecution:
    """Portable, source-bound validation artifact issued by exact replay."""

    replay_request: PublicReplayRequest
    evaluator_basis: EvaluatorBasis
    protocol: ProtocolVariant
    profile: AlgebraProfile
    core: ConversationCore
    fresh: FreshRealization | None
    construction: TranscriptConstruction | None
    replay_executions: int = 1

    @property
    def record(self) -> PortableExecutionRecord:
        return self.replay_request.candidate

    @property
    def invocation(self) -> PublicInvocation:
        return self.replay_request.invocation

    def term(self) -> dict[str, Any]:
        return {
            "replay_request_id": str(self.replay_request.identity),
            "record_id": str(self.record.identity),
            "evaluator_basis_id": str(self.evaluator_basis.identity),
            "protocol_id": self.protocol.identity,
            "profile_id": self.profile.identity,
            "core_id": self.core.identity,
            "realization_id": self.protocol.realization_id,
            "replay_executions": self.replay_executions,
            "qualification_law": _PUBLIC_REPLAY_LAW,
        }

    @property
    def identity(self) -> EvidenceRecordId:
        return evidence_record_id("checked-public-execution", self.term())


def qualify_public_execution(
    replay_request: PublicReplayRequest,
    evaluator_basis: EvaluatorBasis,
    protocol: ProtocolVariant,
    profile: AlgebraProfile,
    core: ConversationCore,
    *,
    fresh: FreshRealization | None = None,
    construction: TranscriptConstruction | None = None,
) -> CheckedPublicExecution | Result:
    """Cold-replay public data and require canonical record equality."""

    if not isinstance(replay_request, PublicReplayRequest):
        return result(
            Outcome.MALFORMED,
            "public-replay",
            "P01-REPLAY-001",
            "public replay request has the wrong type",
        )
    try:
        replay_request_id = replay_request.identity
    except (AttributeError, TermEncodingError, TypeError, ValueError):
        return result(
            Outcome.MALFORMED,
            "public-replay",
            "P01-REPLAY-001",
            "public replay request is outside the closed grammar",
        )
    basis_result = admit_evaluator_basis(evaluator_basis)
    if basis_result.outcome is not Outcome.AFFIRMATIVE:
        return basis_result
    invocation_result = admit_public_invocation(
        replay_request.invocation,
        protocol,
        profile,
        core,
        fresh=fresh,
        construction=construction,
    )
    if invocation_result.outcome is not Outcome.AFFIRMATIVE:
        return invocation_result
    if (
        replay_request.evaluator_basis_id != evaluator_basis.identity
        or protocol.identity not in evaluator_basis.supported_protocol_ids
        or not isinstance(replay_request.evaluator_basis_id, ValidationBasisId)
        or not isinstance(replay_request.public_case_bundle_id, ArtifactContentId)
        or not _valid_public_plan(replay_request.resources)
    ):
        return result(
            Outcome.MISMATCH,
            "public-replay:scope",
            "P01-REPLAY-002",
            "replay basis, source, protocol support, or resource policy is invalid",
            subject=str(replay_request_id),
        )
    candidate = replay_request.candidate
    if not isinstance(candidate, PortableExecutionRecord):
        return result(
            Outcome.MALFORMED,
            "public-replay:candidate",
            "P01-REPLAY-001",
            "portable candidate has the wrong type",
            subject=str(replay_request_id),
        )
    commitment = public_trace_value(candidate, COMMITMENT)
    response = public_trace_value(candidate, RESPONSE)
    if isinstance(commitment, Result) or isinstance(response, Result):
        return result(
            Outcome.MALFORMED,
            "public-replay:candidate",
            "P01-REPLAY-003",
            "portable candidate lacks its exact proof-message projection",
            subject=str(replay_request_id),
        )
    expected = build_portable_execution(
        replay_request.invocation,
        commitment,
        response,
        protocol,
        profile,
        core,
        fresh=fresh,
        construction=construction,
    )
    if isinstance(expected, Result):
        return expected
    if candidate != expected:
        return result(
            Outcome.MISMATCH,
            "public-replay:exact-record",
            "P01-REPLAY-003",
            "portable candidate differs from canonical public re-evaluation",
            subject=str(replay_request_id),
            expected_record_id=str(expected.identity),
            candidate_record_id=_safe_identity(candidate),
        )
    if (
        not public_usage_fits(candidate.usage, replay_request.resources)
        or replay_request.resources.max_replay_executions < 1
        or not public_usage_fits(candidate.usage, evaluator_basis.hard_caps)
        or evaluator_basis.hard_caps.max_replay_executions < 1
    ):
        return result(
            Outcome.RESOURCE_EXCEEDED,
            "public-replay:resources",
            "P01-REPLAY-004",
            "exact public replay exceeds caller or evaluator resource bounds",
            subject=str(replay_request_id),
        )
    return CheckedPublicExecution(
        replay_request,
        evaluator_basis,
        protocol,
        profile,
        core,
        fresh,
        construction,
    )


def requalify_public_execution(
    checked: CheckedPublicExecution,
) -> CheckedPublicExecution | Result:
    """Rebuild a portable qualification from complete public dependencies."""

    if not isinstance(checked, CheckedPublicExecution):
        return result(
            Outcome.MALFORMED,
            "checked-public-execution",
            "P01-CHECKED-001",
            "checked public execution has the wrong type",
        )
    return qualify_public_execution(
        checked.replay_request,
        checked.evaluator_basis,
        checked.protocol,
        checked.profile,
        checked.core,
        fresh=checked.fresh,
        construction=checked.construction,
    )


def check_checked_public_execution(checked: CheckedPublicExecution) -> Result:
    replayed = requalify_public_execution(checked)
    if isinstance(replayed, Result):
        return replayed
    if replayed.identity != checked.identity:
        return result(
            Outcome.MISMATCH,
            "checked-public-execution:identity",
            "P01-CHECKED-001",
            "checked execution differs from fresh exact public replay",
            subject=_safe_identity(checked),
        )
    return affirmative(
        "checked-public-execution",
        "P01-CHECKED-OK",
        "checked public execution survives exact portable replay",
        subject=str(checked.identity),
    )


def check_fresh_public_execution(checked: CheckedPublicExecution) -> Result:
    replayed = requalify_public_execution(checked)
    if isinstance(replayed, Result):
        return replayed
    if replayed.protocol.realization_kind is not RealizationKind.FRESH:
        return result(
            Outcome.MISMATCH,
            "fresh-public-verification",
            "P01-FRESH-PUBLIC-001",
            "checked execution is not a Fresh realization",
            subject=str(replayed.identity),
        )
    return affirmative(
        "fresh-public-verification",
        "P01-FRESH-PUBLIC-OK",
        "Fresh transcript satisfies exact public replay and verifier evaluation",
        subject=str(replayed.identity),
        non_claim="not evidence that the challenge support point was honestly sampled",
    )


@dataclass(frozen=True)
class PublicStatementExport:
    checked_execution_id: EvidenceRecordId
    record_id: ArtifactContentId
    occurrence: str
    value_domain_id: str
    semantic_contract_id: str
    source_event_id: ArtifactContentId
    value: int

    def term(self) -> dict[str, Any]:
        return {
            "checked_execution_id": str(self.checked_execution_id),
            "record_id": str(self.record_id),
            "occurrence": self.occurrence,
            "value_domain_id": self.value_domain_id,
            "semantic_contract_id": self.semantic_contract_id,
            "source_event_id": str(self.source_event_id),
            "value": self.value,
        }

    @property
    def identity(self) -> EvidenceRecordId:
        return evidence_record_id("checked-public-statement-export", self.term())


@dataclass(frozen=True)
class PublicTranscriptExport:
    checked_execution_id: EvidenceRecordId
    invocation_id: ArtifactContentId
    trace: tuple[PublicTraceEvent, ...]
    challenge_receipt: ChallengeReceipt

    def term(self) -> dict[str, Any]:
        return {
            "checked_execution_id": str(self.checked_execution_id),
            "invocation_id": str(self.invocation_id),
            "trace": [event.term() for event in self.trace],
            "challenge_receipt": self.challenge_receipt.term(),
        }

    @property
    def identity(self) -> EvidenceRecordId:
        return evidence_record_id("checked-public-transcript-export", self.term())


def _statement_event_id(checked: CheckedPublicExecution) -> ArtifactContentId:
    contract = checked.core.contract_for(STATEMENT)
    return canonical_json_content_id(
        {
            "record_id": str(checked.record.identity),
            "invocation_id": str(checked.invocation.identity),
            "occurrence": STATEMENT,
            "contract_id": contract.semantic_contract_id,
            "value": checked.invocation.statement,
        }
    )


def export_checked_public_statement(
    checked: CheckedPublicExecution,
) -> PublicStatementExport | Result:
    """Export Statement only after re-establishing public qualification."""

    replayed = requalify_public_execution(checked)
    if isinstance(replayed, Result):
        return replayed
    contract = replayed.core.contract_for(STATEMENT)
    return PublicStatementExport(
        replayed.identity,
        replayed.record.identity,
        STATEMENT,
        contract.value_domain_id,
        contract.semantic_contract_id,
        _statement_event_id(replayed),
        replayed.invocation.statement,
    )


def issue_relations_checked_statement(checked: CheckedPublicExecution) -> Any | Result:
    """Issue the sealed Relations view only from a replay-checked execution."""

    replayed = requalify_public_execution(checked)
    if isinstance(replayed, Result):
        return replayed
    try:
        from .relations import _issue_checked_public_execution_statement

        return _issue_checked_public_execution_statement(
            public_execution_qualification_id=replayed.identity,
            public_execution_record_id=replayed.record.identity,
            protocol_id=replayed.protocol.identity,
            core_id=replayed.core.identity,
            evaluation_profile_id=replayed.profile.identity,
            occurrence=STATEMENT,
            value=replayed.invocation.statement,
            source_event_id=_statement_event_id(replayed),
        )
    except (ImportError, TypeError, ValueError):
        return result(
            Outcome.CHECKER_FAILURE,
            "checked-public-statement:relations-bridge",
            "P01-CHECKED-002",
            "Relations statement-view issuer rejected a replay-checked execution",
            subject=str(replayed.identity),
        )


def export_checked_public_transcript(
    checked: CheckedPublicExecution,
) -> PublicTranscriptExport | Result:
    """Export transcript only after re-establishing public qualification."""

    replayed = requalify_public_execution(checked)
    if isinstance(replayed, Result):
        return replayed
    return PublicTranscriptExport(
        replayed.identity,
        replayed.invocation.identity,
        replayed.record.trace,
        replayed.record.challenge_receipt,
    )


class OwnerLocalInvocationRef:
    """Opaque occurrence coordinate for one owner-local invocation."""

    __slots__ = ("__owner", "__generation", "__ordinal")

    def __init__(self, owner: object, generation: object, ordinal: int) -> None:
        self.__owner = owner
        self.__generation = generation
        self.__ordinal = ordinal

    def __repr__(self) -> str:
        return "<OwnerLocalInvocationRef opaque>"

    def __reduce_ex__(self, protocol: int) -> Any:
        raise TypeError("owner-local invocation refs are not serializable")


class OwnerLocalPrecommitmentHandle:
    """Opaque authority for one frozen, single-use prover precommitment."""

    __slots__ = ("__owner", "__generation", "__ordinal")

    def __init__(self, owner: object, generation: object, ordinal: int) -> None:
        self.__owner = owner
        self.__generation = generation
        self.__ordinal = ordinal

    def __repr__(self) -> str:
        return "<OwnerLocalPrecommitmentHandle opaque>"

    def __reduce_ex__(self, protocol: int) -> Any:
        raise TypeError("owner-local precommitment handles are not serializable")


class _LocalInvocationState:
    __slots__ = (
        "prefix",
        "protocol",
        "profile",
        "core",
        "fresh",
        "construction",
        "precommitted",
        "precommitment_handle",
    )

    def __init__(
        self,
        prefix: PublicInvocationPrefix,
        protocol: ProtocolVariant,
        profile: AlgebraProfile,
        core: ConversationCore,
        fresh: FreshRealization | None,
        construction: TranscriptConstruction | None,
    ) -> None:
        self.prefix = prefix
        self.protocol = protocol
        self.profile = profile
        self.core = core
        self.fresh = fresh
        self.construction = construction
        self.precommitted = False
        self.precommitment_handle: OwnerLocalPrecommitmentHandle | None = None


class _LocalPrecommitment:
    __slots__ = (
        "invocation_ref",
        "state",
        "witness_assignment",
        "nonce",
        "response_plan",
        "evaluator_basis",
        "public_resources",
        "local_resources",
        "commitment",
        "consumed",
        "final_invocation",
    )

    def __init__(
        self,
        invocation_ref: OwnerLocalInvocationRef,
        state: _LocalInvocationState,
        witness_assignment: Any,
        nonce: int,
        response_plan: ResponsePlan,
        evaluator_basis: EvaluatorBasis,
        public_resources: PublicResourcePlan,
        local_resources: LocalResourcePlan,
        commitment: int,
    ) -> None:
        self.invocation_ref = invocation_ref
        self.state = state
        self.witness_assignment = witness_assignment
        self.nonce = nonce
        self.response_plan = response_plan
        self.evaluator_basis = evaluator_basis
        self.public_resources = public_resources
        self.local_resources = local_resources
        self.commitment = commitment
        self.consumed = False
        self.final_invocation: PublicInvocation | None = None


class OwnerLocalBindingStore:
    """Owner-scoped store for staged private prover execution.

    ``begin_invocation`` creates an occurrence over a challenge-neutral public
    prefix. ``precommit`` then freezes exact Relations authority, nonce,
    canonical commitment, response plan, and policies before a Fresh challenge
    can be resolved through this API. ``generate_local_execution`` consumes that
    precommitment once.

    This orders capabilities in the modeled flow.  It does not prove that an
    external caller lacked out-of-band knowledge of a frozen challenge value.
    """

    __slots__ = (
        "__owner",
        "__generation",
        "__next_invocation",
        "__next_precommitment",
        "__invocations",
        "__precommitments",
    )

    def __init__(self) -> None:
        self.__owner = object()
        self.__generation = object()
        self.__next_invocation = 0
        self.__next_precommitment = 0
        self.__invocations: dict[OwnerLocalInvocationRef, _LocalInvocationState] = {}
        self.__precommitments: dict[
            OwnerLocalPrecommitmentHandle, _LocalPrecommitment
        ] = {}

    def begin_invocation(
        self,
        prefix: PublicInvocationPrefix,
        protocol: ProtocolVariant,
        profile: AlgebraProfile,
        core: ConversationCore,
        *,
        fresh: FreshRealization | None = None,
        construction: TranscriptConstruction | None = None,
    ) -> OwnerLocalInvocationRef | Result:
        prefix_result = admit_public_invocation_prefix(
            prefix,
            protocol,
            profile,
            core,
            fresh=fresh,
            construction=construction,
        )
        if prefix_result.outcome is not Outcome.AFFIRMATIVE:
            return prefix_result
        invocation_ref = OwnerLocalInvocationRef(
            self.__owner,
            self.__generation,
            self.__next_invocation,
        )
        self.__next_invocation += 1
        self.__invocations[invocation_ref] = _LocalInvocationState(
            prefix,
            protocol,
            profile,
            core,
            fresh,
            construction,
        )
        return invocation_ref

    def precommit(
        self,
        invocation_ref: OwnerLocalInvocationRef,
        witness_assignment: Any,
        relation_owner: Any,
        nonce_scalar: int,
        satisfaction_capability: Any,
        response_plan: ResponsePlan,
        evaluator_basis: EvaluatorBasis,
        *,
        public_resources: PublicResourcePlan = DEFAULT_PUBLIC_RESOURCE_PLAN,
        local_resources: LocalResourcePlan = DEFAULT_LOCAL_RESOURCE_PLAN,
    ) -> OwnerLocalPrecommitmentHandle | Result:
        state = (
            self.__invocations.get(invocation_ref)
            if isinstance(invocation_ref, OwnerLocalInvocationRef)
            else None
        )
        if (
            state is None
            or not isinstance(response_plan, ResponsePlan)
            or not state.profile.valid_scalar(nonce_scalar)
            or not _valid_public_plan(public_resources)
            or not _valid_local_plan(local_resources)
        ):
            return result(
                Outcome.MALFORMED,
                "local-precommitment",
                "P01-LOCAL-BIND-001",
                "precommitment dependencies, response plan, or policies are malformed",
            )
        if state.precommitted:
            return result(
                Outcome.REFUSED,
                "local-precommitment:occurrence",
                "P01-LOCAL-BIND-003",
                "owner-local invocation occurrence already has a precommitment",
                subject=str(state.prefix.identity),
            )
        basis_result = admit_evaluator_basis(evaluator_basis)
        if basis_result.outcome is not Outcome.AFFIRMATIVE:
            return basis_result
        if state.protocol.identity not in evaluator_basis.supported_protocol_ids:
            return result(
                Outcome.UNSUPPORTED,
                "local-generation:protocol-support",
                "P01-LOCAL-EXEC-001",
                "local generation Protocol is outside the frozen evaluator basis",
                subject=str(state.prefix.identity),
            )
        honest_contract = canonical_honest_prover_contract(
            state.core, state.profile
        )
        contract_result = admit_honest_prover_contract(
            honest_contract, state.core, state.profile
        )
        if contract_result.outcome is not Outcome.AFFIRMATIVE:
            return contract_result
        usage = LocalResourceUsage(2, 1, 2)
        if not _local_usage_fits(usage, local_resources):
            return result(
                Outcome.RESOURCE_EXCEEDED,
                "local-generation:resources",
                "P01-LOCAL-EXEC-003",
                "confidential generation exceeds its owner-local resource policy",
                subject=str(state.prefix.identity),
            )
        try:
            from .relations import (
                CheckedRelationSatisfaction,
                RelationSatisfactionOwner,
                SchnorrWitnessAssignment,
            )

            authorized = isinstance(
                satisfaction_capability, CheckedRelationSatisfaction
            ) and isinstance(
                witness_assignment, SchnorrWitnessAssignment
            ) and isinstance(
                relation_owner, RelationSatisfactionOwner
            ) and satisfaction_capability.authorizes_assignment(
                witness_assignment=witness_assignment,
                owner=relation_owner,
                precondition_contract_id=honest_witness_precondition_contract_id(
                    state.profile
                ),
                public_statement=state.prefix.statement,
            )
        except (AttributeError, TypeError, ValueError):
            authorized = False
        if not authorized:
            return result(
                Outcome.REFUSED,
                "owner-local-binding:relation-authority",
                "P01-LOCAL-BIND-002",
                "Relations did not issue an affirmative capability for this exact local witness binding",
                subject=str(state.prefix.identity),
            )
        handle = OwnerLocalPrecommitmentHandle(
            self.__owner,
            self.__generation,
            self.__next_precommitment,
        )
        self.__next_precommitment += 1
        state.precommitted = True
        self.__precommitments[handle] = _LocalPrecommitment(
            invocation_ref,
            state,
            witness_assignment,
            nonce_scalar,
            response_plan,
            evaluator_basis,
            public_resources,
            local_resources,
            pow(state.profile.generator, nonce_scalar, state.profile.p),
        )
        state.precommitment_handle = handle
        return handle

    def resolve_challenge(
        self,
        invocation_ref: OwnerLocalInvocationRef,
    ) -> ChallengeReceipt | Result:
        """Resolve a challenge only after this occurrence has finalized.

        Before finalization the same operation is an executable phase-boundary
        refusal.  The transition says nothing about information obtained
        outside this modeled capability flow.
        """

        state = (
            self.__invocations.get(invocation_ref)
            if isinstance(invocation_ref, OwnerLocalInvocationRef)
            else None
        )
        if state is None:
            return result(
                Outcome.REFUSED,
                "local-precommitment:authority",
                "P01-LOCAL-BIND-003",
                "invocation reference is absent or belongs to another owner-local store",
            )
        precommitment = (
            self.__precommitments.get(state.precommitment_handle)
            if isinstance(
                state.precommitment_handle,
                OwnerLocalPrecommitmentHandle,
            )
            else None
        )
        if precommitment is None or precommitment.final_invocation is None:
            return result(
                Outcome.REFUSED,
                "local-precommitment:causality",
                "P01-LOCAL-EXEC-002",
                "challenge resolution is unavailable before finalization",
                subject=str(state.prefix.identity),
            )
        return _challenge_for_invocation(
            precommitment.final_invocation,
            state.protocol,
            state.profile,
            precommitment.commitment,
            construction=state.construction,
        )

    def _claim_finalization(
        self,
        invocation_ref: OwnerLocalInvocationRef,
        handle: OwnerLocalPrecommitmentHandle,
        fresh_challenge: FreshChallengeBinding | None,
    ) -> tuple[_LocalPrecommitment, PublicInvocation] | Result:
        precommitment = (
            self.__precommitments.get(handle)
            if isinstance(handle, OwnerLocalPrecommitmentHandle)
            else None
        )
        if (
            precommitment is None
            or not isinstance(invocation_ref, OwnerLocalInvocationRef)
            or precommitment.invocation_ref is not invocation_ref
            or self.__invocations.get(invocation_ref) is not precommitment.state
        ):
            return result(
                Outcome.REFUSED,
                "local-precommitment:authority",
                "P01-LOCAL-BIND-003",
                "precommitment handle is absent, foreign, or bound to another invocation occurrence",
            )
        if precommitment.consumed:
            return result(
                Outcome.REFUSED,
                "local-precommitment:single-use",
                "P01-LOCAL-BIND-003",
                "precommitment has already been finalized",
                subject=str(precommitment.state.prefix.identity),
            )
        # Claim the state before inspecting a supplied Fresh value: a failed
        # attempt cannot be retried with a different challenge.
        precommitment.consumed = True
        state = precommitment.state
        if state.protocol.realization_kind is RealizationKind.FRESH:
            if not isinstance(fresh_challenge, FreshChallengeBinding):
                return result(
                    Outcome.MALFORMED,
                    "local-finalization:fresh-challenge",
                    "P01-LOCAL-EXEC-001",
                    "Fresh finalization requires one public challenge binding",
                    subject=str(state.prefix.identity),
                )
        elif fresh_challenge is not None:
            return result(
                Outcome.SEMANTIC_NEGATIVE,
                "local-finalization:fs-challenge",
                "P01-LOCAL-EXEC-001",
                "Fiat-Shamir finalization cannot accept a caller-authored challenge",
                subject=str(state.prefix.identity),
            )
        invocation = PublicInvocation(
            state.prefix.algebra_profile_id,
            state.prefix.core_id,
            state.prefix.protocol_id,
            state.prefix.statement,
            state.prefix.application_context,
            fresh_challenge,
        )
        invocation_result = admit_public_invocation(
            invocation,
            state.protocol,
            state.profile,
            state.core,
            fresh=state.fresh,
            construction=state.construction,
        )
        if invocation_result.outcome is not Outcome.AFFIRMATIVE:
            return invocation_result
        precommitment.final_invocation = invocation
        return precommitment, invocation

    def _resolve_audit(
        self, generation: LocalGenerationRecord
    ) -> _LocalPrecommitment | Result:
        precommitment = self.__precommitments.get(generation.precommitment_handle)
        if (
            precommitment is None
            or not precommitment.consumed
            or precommitment.invocation_ref is not generation.invocation_ref
            or precommitment.final_invocation is not generation.invocation
        ):
            return result(
                Outcome.REFUSED,
                "local-generation-qualification:authority",
                "P01-LOCAL-QUAL-001",
                "generation is not the exact finalized owner-local occurrence",
                subject=_safe_identity(generation.invocation),
            )
        return precommitment


class LocalAccessReceipt:
    """Owner-local observed access, with no value, identity, term, or codec."""

    __slots__ = ("source", "stage")

    def __init__(self, source: str, stage: str) -> None:
        object.__setattr__(self, "source", source)
        object.__setattr__(self, "stage", stage)

    def __setattr__(self, name: str, value: object) -> None:
        raise AttributeError("owner-local access receipts are immutable")

    def __repr__(self) -> str:
        return "<LocalAccessReceipt private>"

    def __reduce_ex__(self, protocol: int) -> Any:
        raise TypeError("owner-local access receipts are not serializable")


class LocalGenerationRecord:
    """Non-authoritative local view; deliberately not a portable artifact.

    Exact owner-local authority remains the store-held occurrence and
    precommitment coordinates.  Equal-coordinate audit reconstructions may be
    rechecked, but this record cannot finalize or resurrect a consumed handle.
    """

    __slots__ = (
        "invocation_ref",
        "invocation",
        "precommitment_handle",
        "response_plan",
        "evaluator_basis",
        "protocol",
        "profile",
        "core",
        "fresh",
        "construction",
        "public_resources",
        "local_resources",
        "portable_record",
        "local_usage",
        "access_receipts",
    )

    def __init__(
        self,
        invocation_ref: OwnerLocalInvocationRef,
        invocation: PublicInvocation,
        precommitment_handle: OwnerLocalPrecommitmentHandle,
        response_plan: ResponsePlan,
        evaluator_basis: EvaluatorBasis,
        protocol: ProtocolVariant,
        profile: AlgebraProfile,
        core: ConversationCore,
        fresh: FreshRealization | None,
        construction: TranscriptConstruction | None,
        public_resources: PublicResourcePlan,
        local_resources: LocalResourcePlan,
        portable_record: PortableExecutionRecord,
        local_usage: LocalResourceUsage,
        access_receipts: tuple[LocalAccessReceipt, ...],
    ) -> None:
        object.__setattr__(self, "invocation_ref", invocation_ref)
        object.__setattr__(self, "invocation", invocation)
        object.__setattr__(self, "precommitment_handle", precommitment_handle)
        object.__setattr__(self, "response_plan", response_plan)
        object.__setattr__(self, "evaluator_basis", evaluator_basis)
        object.__setattr__(self, "protocol", protocol)
        object.__setattr__(self, "profile", profile)
        object.__setattr__(self, "core", core)
        object.__setattr__(self, "fresh", fresh)
        object.__setattr__(self, "construction", construction)
        object.__setattr__(self, "public_resources", public_resources)
        object.__setattr__(self, "local_resources", local_resources)
        object.__setattr__(self, "portable_record", portable_record)
        object.__setattr__(self, "local_usage", local_usage)
        object.__setattr__(self, "access_receipts", access_receipts)

    def __setattr__(self, name: str, value: object) -> None:
        raise AttributeError("local generation records are immutable")

    def __repr__(self) -> str:
        return "<LocalGenerationRecord private>"

    def __reduce_ex__(self, protocol: int) -> Any:
        raise TypeError("local generation records are not serializable")


def _evaluate_local_precommitment(
    precommitment: _LocalPrecommitment,
    invocation: PublicInvocation,
    precommitment_handle: OwnerLocalPrecommitmentHandle,
) -> LocalGenerationRecord | Result:
    """Execute or reconstruct one frozen owner-local transition."""

    state = precommitment.state
    evaluator_basis = precommitment.evaluator_basis
    protocol = state.protocol
    profile = state.profile
    core = state.core
    fresh = state.fresh
    construction = state.construction
    public_resources = precommitment.public_resources
    local_resources = precommitment.local_resources
    basis_result = admit_evaluator_basis(evaluator_basis)
    if basis_result.outcome is not Outcome.AFFIRMATIVE:
        return basis_result
    if protocol.identity not in evaluator_basis.supported_protocol_ids:
        return result(
            Outcome.UNSUPPORTED,
            "local-generation:protocol-support",
            "P01-LOCAL-EXEC-001",
            "local generation protocol is outside the evaluator basis",
            subject=str(state.prefix.identity),
        )
    invocation_result = admit_public_invocation(
        invocation,
        protocol,
        profile,
        core,
        fresh=fresh,
        construction=construction,
    )
    if invocation_result.outcome is not Outcome.AFFIRMATIVE:
        return invocation_result
    honest_contract = canonical_honest_prover_contract(core, profile)
    contract_result = admit_honest_prover_contract(honest_contract, core, profile)
    if contract_result.outcome is not Outcome.AFFIRMATIVE:
        return contract_result
    usage = LocalResourceUsage(2, 1, 2)
    if not _local_usage_fits(usage, local_resources):
        return result(
            Outcome.RESOURCE_EXCEEDED,
            "local-generation:resources",
            "P01-LOCAL-EXEC-003",
            "confidential generation exceeds its owner-local resource policy",
            subject=str(invocation.identity),
        )
    expected_commitment = pow(profile.generator, precommitment.nonce, profile.p)
    if precommitment.commitment != expected_commitment:
        return result(
            Outcome.MISMATCH,
            "local-generation:precommitment",
            "P01-LOCAL-EXEC-001",
            "frozen commitment differs from the canonical precommitment transition",
            subject=str(invocation.identity),
        )
    commitment = precommitment.commitment
    challenge_receipt = _challenge_for_invocation(
        invocation,
        protocol,
        profile,
        commitment,
        construction=construction,
    )
    if isinstance(challenge_receipt, Result):
        return challenge_receipt
    if precommitment.response_plan is ResponsePlan.ABORT:
        return result(
            Outcome.REFUSED,
            "local-generation:explicit-abort",
            "P01-LOCAL-EXEC-004",
            "the frozen response plan aborted after challenge resolution",
            subject=str(invocation.identity),
        )
    response = (
        precommitment.nonce
        + challenge_receipt.challenge
        * precommitment.witness_assignment.secret_scalar
    ) % profile.q
    if precommitment.response_plan is ResponsePlan.INVALID:
        response = (response + 1) % profile.q
    portable = build_portable_execution(
        invocation,
        commitment,
        response,
        protocol,
        profile,
        core,
        fresh=fresh,
        construction=construction,
    )
    if isinstance(portable, Result):
        return portable
    if (
        not public_usage_fits(portable.usage, public_resources)
        or not public_usage_fits(portable.usage, evaluator_basis.hard_caps)
    ):
        return result(
            Outcome.RESOURCE_EXCEEDED,
            "local-generation:public-resources",
            "P01-LOCAL-EXEC-003",
            "generated portable record exceeds public resource bounds",
            subject=str(invocation.identity),
        )
    receipts = (
        LocalAccessReceipt("local:nonce:r", COMMITMENT),
        LocalAccessReceipt("public:challenge:c", RESPONSE),
        LocalAccessReceipt("local:witness:x", RESPONSE),
    )
    return LocalGenerationRecord(
        precommitment.invocation_ref,
        invocation,
        precommitment_handle,
        precommitment.response_plan,
        evaluator_basis,
        protocol,
        profile,
        core,
        fresh,
        construction,
        public_resources,
        local_resources,
        portable,
        usage,
        receipts,
    )


def generate_local_execution(
    store: OwnerLocalBindingStore,
    invocation_ref: OwnerLocalInvocationRef,
    precommitment_handle: OwnerLocalPrecommitmentHandle,
    *,
    fresh_challenge: FreshChallengeBinding | None = None,
) -> LocalGenerationRecord | Result:
    """Consume one precommitment and construct its completed invocation.

    No commitment, response plan, semantic dependency, or resource policy can
    be supplied at finalization.  Fresh challenge consumption and Fiat-Shamir
    derivation therefore occur only after the commitment has been frozen.
    """

    if not isinstance(store, OwnerLocalBindingStore):
        return result(
            Outcome.MALFORMED,
            "local-generation",
            "P01-LOCAL-EXEC-001",
            "local generation store has the wrong type",
        )
    claimed = store._claim_finalization(
        invocation_ref,
        precommitment_handle,
        fresh_challenge,
    )
    if isinstance(claimed, Result):
        return claimed
    precommitment, invocation = claimed
    return _evaluate_local_precommitment(
        precommitment,
        invocation,
        precommitment_handle,
    )


class LocalGenerationQualification:
    """Read-only local audit result; no identity, term, or serialization."""

    __slots__ = (
        "generation",
        "audit_reconstruction",
        "checked_public_execution",
    )

    def __init__(
        self,
        generation: LocalGenerationRecord,
        audit_reconstruction: LocalGenerationRecord,
        checked_public_execution: CheckedPublicExecution,
    ) -> None:
        object.__setattr__(self, "generation", generation)
        object.__setattr__(self, "audit_reconstruction", audit_reconstruction)
        object.__setattr__(
            self,
            "checked_public_execution",
            checked_public_execution,
        )

    def __setattr__(self, name: str, value: object) -> None:
        raise AttributeError("local generation qualifications are immutable")

    def __repr__(self) -> str:
        return "<LocalGenerationQualification private>"

    def __reduce_ex__(self, protocol: int) -> Any:
        raise TypeError("local generation qualifications are not serializable")


def _same_local_generation(
    left: LocalGenerationRecord,
    right: LocalGenerationRecord,
) -> bool:
    """Compare every retained coordinate without publishing a local term."""

    if not isinstance(left, LocalGenerationRecord) or not isinstance(
        right, LocalGenerationRecord
    ):
        return False
    try:
        return (
            left.invocation_ref is right.invocation_ref
            and left.invocation is right.invocation
            and left.precommitment_handle is right.precommitment_handle
            and left.response_plan is right.response_plan
            and left.evaluator_basis is right.evaluator_basis
            and left.protocol is right.protocol
            and left.profile is right.profile
            and left.core is right.core
            and left.fresh is right.fresh
            and left.construction is right.construction
            and left.public_resources is right.public_resources
            and left.local_resources is right.local_resources
            and left.portable_record == right.portable_record
            and left.local_usage == right.local_usage
            and tuple((item.source, item.stage) for item in left.access_receipts)
            == tuple((item.source, item.stage) for item in right.access_receipts)
        )
    except (AttributeError, TypeError, ValueError):
        return False


def qualify_local_generation(
    store: OwnerLocalBindingStore,
    generation: LocalGenerationRecord,
    *,
    public_case_bundle_id: ArtifactContentId,
) -> LocalGenerationQualification | Result:
    """Reconstruct frozen local state read-only, then replay public output."""

    if not isinstance(generation, LocalGenerationRecord):
        return result(
            Outcome.MALFORMED,
            "local-generation-qualification",
            "P01-LOCAL-QUAL-001",
            "local generation record has the wrong type",
        )
    if not isinstance(store, OwnerLocalBindingStore):
        return result(
            Outcome.MALFORMED,
            "local-generation-qualification",
            "P01-LOCAL-QUAL-001",
            "owner-local store has the wrong type",
        )
    precommitment = store._resolve_audit(generation)
    if isinstance(precommitment, Result):
        return precommitment
    reconstruction = _evaluate_local_precommitment(
        precommitment,
        generation.invocation,
        generation.precommitment_handle,
    )
    if isinstance(reconstruction, Result):
        return reconstruction
    if not _same_local_generation(reconstruction, generation):
        return result(
            Outcome.MISMATCH,
            "local-generation-qualification:confidential-audit",
            "P01-LOCAL-QUAL-001",
            "read-only confidential reconstruction differs from the frozen generation",
            subject=str(generation.invocation.identity),
        )
    replay_request = PublicReplayRequest(
        generation.invocation,
        generation.portable_record,
        generation.evaluator_basis.identity,
        public_case_bundle_id,
        generation.public_resources,
    )
    checked = qualify_public_execution(
        replay_request,
        generation.evaluator_basis,
        generation.protocol,
        generation.profile,
        generation.core,
        fresh=generation.fresh,
        construction=generation.construction,
    )
    if isinstance(checked, Result):
        return checked
    return LocalGenerationQualification(generation, reconstruction, checked)


def requalify_local_generation(
    store: OwnerLocalBindingStore,
    qualification: LocalGenerationQualification,
    *,
    public_case_bundle_id: ArtifactContentId,
) -> LocalGenerationQualification | Result:
    if not isinstance(qualification, LocalGenerationQualification):
        return result(
            Outcome.MALFORMED,
            "local-generation-qualification",
            "P01-LOCAL-QUAL-001",
            "local generation qualification has the wrong type",
        )
    rebuilt = qualify_local_generation(
        store,
        qualification.generation,
        public_case_bundle_id=public_case_bundle_id,
    )
    if isinstance(rebuilt, Result):
        return rebuilt
    if not _same_local_generation(
        qualification.audit_reconstruction,
        rebuilt.audit_reconstruction,
    ):
        return result(
            Outcome.MISMATCH,
            "local-generation-qualification:retained-audit",
            "P01-LOCAL-QUAL-001",
            "retained confidential audit differs from read-only reconstruction",
            subject=str(rebuilt.checked_public_execution.identity),
        )
    retained_checked = qualification.checked_public_execution
    try:
        checked_matches = (
            isinstance(retained_checked, CheckedPublicExecution)
            and retained_checked == rebuilt.checked_public_execution
            and retained_checked.identity == rebuilt.checked_public_execution.identity
        )
    except (AttributeError, ProvenanceError, TermEncodingError, TypeError, ValueError):
        checked_matches = False
    if not checked_matches:
        return result(
            Outcome.MISMATCH,
            "local-generation-qualification:retained-public-evidence",
            "P01-LOCAL-QUAL-001",
            "retained checked-public evidence differs from read-only reconstruction",
            subject=str(rebuilt.checked_public_execution.identity),
        )
    return rebuilt


def check_local_generation_qualification(
    store: OwnerLocalBindingStore,
    qualification: LocalGenerationQualification,
    *,
    public_case_bundle_id: ArtifactContentId,
) -> Result:
    rerun = requalify_local_generation(
        store,
        qualification,
        public_case_bundle_id=public_case_bundle_id,
    )
    if isinstance(rerun, Result):
        return rerun
    return affirmative(
        "local-generation-qualification",
        "P01-LOCAL-QUAL-OK",
        "owner-local generation survives read-only confidential audit and exact portable replay",
        subject=str(rerun.checked_public_execution.identity),
    )
