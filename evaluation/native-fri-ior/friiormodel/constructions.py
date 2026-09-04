"""Checked evidence for the three concrete FRI construction arrows.

This module deliberately keeps the arrows separate.  The first execution
compiles one accepted native logical-oracle run into one accepted committed
Fresh-coin run.  The second preserves that committed run and inserts one
explicit Fresh work challenge, nonce publication, and deterministic check.
Only the final composition operation joins those two issued receipts with the
already admitted same-Core Fiat--Shamir construction.

All claims are about one concrete execution.  Commitment salts and complete
logical-oracle carriers remain owner-local advice.  The receipts do not claim
commitment security, FRI proximity, work amplification, random-oracle
security, or transport of a protocol theorem.
"""

from __future__ import annotations

from dataclasses import dataclass, field
import hashlib
from pathlib import Path
import stat
from types import MappingProxyType
from typing import Any

from .commitment import EXACT_COMMITMENT_PROFILE, MerkleCap, build_commitment
from .committed import (
    ExplicitCommittedFriExecution,
    verify_committed_fri,
    verify_explicit_committed_fri,
    verify_explicit_committed_prefix,
)
from .field import Fp2
from .generation import (
    CheckedNativeToCommittedExecution,
    PrivateFriGenerationMaterial,
)
from .native import (
    LayerQueryAnswerOccurrence,
    NativeFriTrace,
    RandomQueryDraw,
    derive_honest_native_trace,
    resolve_layer_query_answers,
    verify_native_trace,
)
from .profile import (
    D0,
    D1,
    DEFAULT_VALIDATION_LIMITS,
    EXACT_ALGEBRA_PROFILE,
)
from .proof import OccurrenceSelector, OpeningTableEntry
from .provenance import ValidationBasisId, artifact_content_id, validation_basis_id
from .subjects import (
    CHECKED_FIAT_SHAMIR_CONSTRUCTION,
    COMMITTED_FRI_CORE,
    COMMITMENT_COMPILATION_DECLARATION,
    FIAT_SHAMIR_WORK_AUGMENTED_PROTOCOL,
    FRESH_WORK_AUGMENTED_PROTOCOL,
    GRINDING_AUGMENTATION_DECLARATION,
    NATIVE_FRI_CORE,
    WORK_AUGMENTED_COMMITTED_FRI_CORE,
    CheckedFiatShamirConstruction,
)
from .terms import (
    CheckResult,
    ModelFailure,
    OutcomeClass,
    ResourceCounter,
    ResourceLimits,
    SemanticId,
    affirmative,
    checker_failure,
    encode_term,
    malformed,
    semantic_id,
)
from .transcript import (
    FiatShamirTranscript,
    EXACT_GRINDING_PROFILE,
    MAX_GRINDING_NONCE,
    WORK_CHECK_NAMESPACE,
    WORK_RULE,
    derive_fiat_shamir_transcript,
)


COMMITTED_FRESH_RUN_SCHEMA = "zkc.fri-ior.committed-fresh-run.v1"
WORK_AUGMENTED_FRESH_RUN_SCHEMA = "zkc.fri-ior.work-augmented-fresh-run.v1"
COMMITMENT_RECEIPT_SCHEMA = "zkc.fri-ior.checked-native-to-committed-fresh-execution.v1"
GRINDING_RECEIPT_SCHEMA = "zkc.fri-ior.checked-committed-to-work-fresh-execution.v1"
COMPOSITION_RECEIPT_SCHEMA = "zkc.fri-ior.checked-construction-composition.v1"

COMMITMENT_VALIDATION_LAW = "fri-ior.native-to-committed-fresh-execution.v1"
GRINDING_VALIDATION_LAW = "fri-ior.committed-to-work-fresh-execution.v1"
COMPOSITION_VALIDATION_LAW = "fri-ior.concrete-fresh-fs-composition.v1"

_CONSTRUCTION_VALIDATION_SOURCES = (
    "__init__.py",
    "commitment.py",
    "committed.py",
    "constructions.py",
    "field.py",
    "generation.py",
    "native.py",
    "profile.py",
    "proof.py",
    "provenance.py",
    "subjects.py",
    "terms.py",
    "transcript.py",
)

_WORK_DOMAIN = b"zkc.fri-ior.work-check.v1\x00"
_COMMITTED_SCHEDULE = tuple(COMMITTED_FRI_CORE.to_term()["event_schedule"])
_WORK_SCHEDULE = tuple(WORK_AUGMENTED_COMMITTED_FRI_CORE.to_term()["event_schedule"])
_INSERTED_WORK_OCCURRENCES = (
    "fresh-work-seed",
    "publish-grinding-nonce",
    "check-work-seed-and-nonce",
)

_CONSTRUCTION_NONCLAIMS = (
    "general-construction-correctness",
    "commitment-binding-hiding-or-extractability",
    "fri-proximity-soundness-or-completeness",
    "work-amplification-or-honest-work-bound",
    "random-oracle-security",
    "protocol-property-transport",
    "outer-computation-relation",
)


def _freeze_public_environment_term(value: Any) -> Any:
    """Copy one bounded public-environment term into immutable storage."""

    if value is None or type(value) in (bool, int, str, bytes):
        frozen = value
    elif type(value) in (tuple, list):
        frozen = tuple(_freeze_public_environment_term(item) for item in value)
    elif type(value) in (dict, MappingProxyType):
        if not all(isinstance(key, str) for key in value):
            raise malformed(
                "constructions:public-environment-formation",
                "FRI-IOR-CONSTRUCTION-055",
                "public-environment maps require text keys",
            )
        frozen = MappingProxyType(
            {
                key: _freeze_public_environment_term(value[key])
                for key in sorted(value, key=lambda item: item.encode("utf-8"))
            }
        )
    else:
        raise malformed(
            "constructions:public-environment-formation",
            "FRI-IOR-CONSTRUCTION-056",
            "statement and application context must be closed finite terms",
        )
    encode_term(frozen)
    return frozen


def _public_environment_term_copy(value: Any) -> Any:
    if type(value) in (dict, MappingProxyType):
        return {key: _public_environment_term_copy(item) for key, item in value.items()}
    if isinstance(value, tuple):
        return [_public_environment_term_copy(item) for item in value]
    return value


def _refusal(code: str, detail: str, **evidence: Any) -> CheckResult:
    return CheckResult(
        OutcomeClass.REFUSED,
        "constructions:execution-check",
        code,
        detail,
        evidence=evidence,
    )


def _malformed_result(code: str, detail: str) -> CheckResult:
    return CheckResult(
        OutcomeClass.MALFORMED,
        "constructions:execution-check",
        code,
        detail,
    )


def _draw_term(draw: RandomQueryDraw) -> dict[str, int]:
    return {
        "ordinal": draw.ordinal,
        "initial_domain_index": draw.initial_domain_index,
    }


def _fp2_identity(occurrence: str, value: Fp2) -> SemanticId:
    return semantic_id(
        "fresh-coin-occurrence",
        "fri-ior.fresh-coin-occurrence.v1",
        {"occurrence": occurrence, "value": value.to_term()},
    )


def _draw_identity(occurrence: str, draw: RandomQueryDraw) -> SemanticId:
    return semantic_id(
        "fresh-query-occurrence",
        "fri-ior.fresh-query-occurrence.v1",
        {"occurrence": occurrence, **_draw_term(draw)},
    )


def _oracle_carrier_identity(trace: NativeFriTrace, layer: int) -> SemanticId:
    oracle = trace.initial_oracle if layer == 0 else trace.prover_oracle
    return semantic_id(
        "owner-local-logical-oracle-carrier",
        "fri-ior.owner-local-logical-oracle-carrier.v1",
        {
            "trace_id": trace.identity.to_term(),
            "oracle_name": oracle.name,
            "domain": oracle.domain.to_term(),
            "ordered_values": [entry.value.to_term() for entry in oracle.entries],
        },
    )


def _layer_query_identity(query: LayerQueryAnswerOccurrence) -> SemanticId:
    return semantic_id(
        "native-layer-query-answer-occurrence",
        "fri-ior.native-layer-query-answer-occurrence.v1",
        {
            "ordinal": query.top_level_ordinal,
            "layer": query.layer.value,
            "oracle_name": query.oracle_name,
            "pair_index": query.pair_index,
            "positive_answer_index": query.positive_answer_index,
            "negative_answer_index": query.negative_answer_index,
            "positive_value": query.positive_value.to_term(),
            "negative_value": query.negative_value.to_term(),
        },
    )


def _terminal_identity(coefficients: tuple[Fp2, ...]) -> SemanticId:
    return semantic_id(
        "fri-terminal-polynomial",
        "fri-ior.terminal-polynomial.v1",
        {
            "coefficient_order": "ascending",
            "coefficients": [coefficient.to_term() for coefficient in coefficients],
        },
    )


def _public_environment_value_identity(occurrence: str, value: Any) -> SemanticId:
    return semantic_id(
        "fresh-public-environment-value",
        "fri-ior.fresh-public-environment-value.v1",
        {
            "occurrence": occurrence,
            "value": _public_environment_term_copy(value),
        },
    )


@dataclass(frozen=True, slots=True)
class ExactResourceUsage:
    """Frozen usage from a checker-private exact ResourceCounter."""

    field_operations: int
    hash_calls: int
    hash_bytes: int
    merkle_nodes: int
    transcript_frames: int
    sampler_attempts: int
    grinding_trials: int
    logical_query_occurrences: int
    unique_openings: int
    proof_bytes: int

    @classmethod
    def from_counter(cls, counter: ResourceCounter) -> ExactResourceUsage:
        if type(counter) is not ResourceCounter:
            raise malformed(
                "constructions:resource-snapshot",
                "FRI-IOR-CONSTRUCTION-001",
                "a resource snapshot requires the evaluator-owned exact counter",
            )
        return cls(**counter.snapshot())

    def to_term(self) -> dict[str, int]:
        return {
            name: getattr(self, name)
            for name in (
                "field_operations",
                "hash_calls",
                "hash_bytes",
                "merkle_nodes",
                "transcript_frames",
                "sampler_attempts",
                "grinding_trials",
                "logical_query_occurrences",
                "unique_openings",
                "proof_bytes",
            )
        }


@dataclass(frozen=True, slots=True)
class SeparatedResourceUsage:
    """Exact source and target meters for one checked construction arrow."""

    source: ExactResourceUsage
    target: ExactResourceUsage

    def to_term(self) -> dict[str, Any]:
        return {
            "source_execution": self.source.to_term(),
            "target_execution": self.target.to_term(),
        }


@dataclass(frozen=True, slots=True)
class ConstructionValidationSource:
    """One exact source file in the construction-checker basis."""

    path: str
    artifact_content_id: str
    byte_length: int

    def __post_init__(self) -> None:
        if (
            type(self.path) is not str
            or self.path not in _CONSTRUCTION_VALIDATION_SOURCES
            or type(self.artifact_content_id) is not str
            or not self.artifact_content_id.startswith("sha256:")
            or type(self.byte_length) is not int
            or self.byte_length <= 0
        ):
            raise malformed(
                "constructions:validation-source-formation",
                "FRI-IOR-CONSTRUCTION-053",
                "a validation source requires an exact path, digest, and byte length",
            )

    def to_term(self) -> dict[str, Any]:
        return {
            "path": self.path,
            "artifact_content_id": self.artifact_content_id,
            "byte_length": self.byte_length,
        }


def _construction_source_manifest() -> tuple[ConstructionValidationSource, ...]:
    root = Path(__file__).resolve().parent
    manifest: list[ConstructionValidationSource] = []
    for relative in _CONSTRUCTION_VALIDATION_SOURCES:
        path = root / relative
        metadata = path.lstat()
        if stat.S_ISLNK(metadata.st_mode) or not stat.S_ISREG(metadata.st_mode):
            raise ModelFailure(
                OutcomeClass.MISSING_DEPENDENCY,
                "constructions:validation-source-load",
                "FRI-IOR-CONSTRUCTION-054",
                "a required construction-checker source is not a regular non-symlink file",
            )
        raw = path.read_bytes()
        manifest.append(
            ConstructionValidationSource(
                relative,
                str(artifact_content_id(raw)),
                len(raw),
            )
        )
    return tuple(manifest)


def _validation_basis(
    law: str,
    limits: ResourceLimits,
) -> tuple[ValidationBasisId, tuple[ConstructionValidationSource, ...]]:
    manifest = _construction_source_manifest()
    basis = validation_basis_id(
        "construction-arrows",
        {
            "law": law,
            "selected_resource_limits": limits.to_term(),
            "sources": [source.to_term() for source in manifest],
        },
    )
    return basis, manifest


@dataclass(frozen=True, slots=True)
class CommitmentAdvice:
    """Owner-local salts with no term, serialization, or identity surface."""

    initial_layer_salts: tuple[bytes, ...] = field(repr=False)
    first_fold_layer_salts: tuple[bytes, ...] = field(repr=False)

    def __post_init__(self) -> None:
        expected = (
            (self.initial_layer_salts, D0.order // 2),
            (self.first_fold_layer_salts, D1.order // 2),
        )
        if type(self) is not CommitmentAdvice or any(
            type(salts) is not tuple
            or len(salts) != count
            or not all(type(salt) is bytes and len(salt) == 16 for salt in salts)
            for salts, count in expected
        ):
            raise malformed(
                "constructions:commitment-advice-formation",
                "FRI-IOR-CONSTRUCTION-002",
                "commitment advice requires the exact owner-local salt carriers",
            )


@dataclass(frozen=True, slots=True)
class FreshPublicEnvironment:
    """Exact statement and context supplied independently of prover advice."""

    statement: Any
    application_context: Any

    def __post_init__(self) -> None:
        if type(self) is not FreshPublicEnvironment:
            raise malformed(
                "constructions:public-environment-formation",
                "FRI-IOR-CONSTRUCTION-057",
                "a Fresh public environment requires the exact closed carrier",
            )
        object.__setattr__(
            self,
            "statement",
            _freeze_public_environment_term(self.statement),
        )
        object.__setattr__(
            self,
            "application_context",
            _freeze_public_environment_term(self.application_context),
        )
        encode_term(self.to_term())

    def to_term(self) -> dict[str, Any]:
        return {
            "schema": "zkc.fri-ior.fresh-public-environment.v1",
            "statement": _public_environment_term_copy(self.statement),
            "application_context": _public_environment_term_copy(
                self.application_context
            ),
        }

    @property
    def identity(self) -> SemanticId:
        return semantic_id(
            "fresh-public-environment",
            "fri-ior.fresh-public-environment.v1",
            self.to_term(),
        )


@dataclass(frozen=True, slots=True)
class PublicEnvironmentMapEntry:
    occurrence: str
    source_value_id: SemanticId
    target_value_id: SemanticId

    def to_term(self) -> dict[str, Any]:
        return {
            "occurrence": self.occurrence,
            "source_value_id": self.source_value_id.to_term(),
            "target_value_id": self.target_value_id.to_term(),
            "equal": self.source_value_id == self.target_value_id,
            "outside_logical_oracle_publication_map": True,
        }


@dataclass(frozen=True, slots=True)
class PublicationMapEntry:
    source_occurrence: str
    target_occurrence: str
    source_oracle_id: SemanticId
    target_cap_id: SemanticId

    def to_term(self) -> dict[str, Any]:
        return {
            "source_occurrence": self.source_occurrence,
            "target_occurrence": self.target_occurrence,
            "source_oracle_id": self.source_oracle_id.to_term(),
            "target_cap_id": self.target_cap_id.to_term(),
        }


@dataclass(frozen=True, slots=True)
class CoinMapEntry:
    source_occurrence: str
    target_occurrence: str
    source_coin_id: SemanticId
    target_coin_id: SemanticId

    def to_term(self) -> dict[str, Any]:
        return {
            "source_occurrence": self.source_occurrence,
            "target_occurrence": self.target_occurrence,
            "source_coin_id": self.source_coin_id.to_term(),
            "target_coin_id": self.target_coin_id.to_term(),
        }


@dataclass(frozen=True, slots=True)
class QueryOccurrenceMapEntry:
    ordinal: int
    source_occurrence_id: SemanticId
    target_occurrence_id: SemanticId

    def to_term(self) -> dict[str, Any]:
        return {
            "ordinal": self.ordinal,
            "source_occurrence_id": self.source_occurrence_id.to_term(),
            "target_occurrence_id": self.target_occurrence_id.to_term(),
        }


@dataclass(frozen=True, slots=True)
class ExtractedAnswerMapEntry:
    ordinal: int
    layer: int
    source_answer_id: SemanticId
    target_opening_table_index: int
    target_opening_id: SemanticId

    def to_term(self) -> dict[str, Any]:
        return {
            "ordinal": self.ordinal,
            "layer": self.layer,
            "source_answer_id": self.source_answer_id.to_term(),
            "target_opening_table_index": self.target_opening_table_index,
            "target_opening_id": self.target_opening_id.to_term(),
        }


@dataclass(frozen=True, slots=True)
class TerminalMap:
    source_terminal_id: SemanticId
    target_terminal_id: SemanticId

    def to_term(self) -> dict[str, Any]:
        return {
            "source_terminal_id": self.source_terminal_id.to_term(),
            "target_terminal_id": self.target_terminal_id.to_term(),
            "equal": self.source_terminal_id == self.target_terminal_id,
        }


@dataclass(frozen=True, slots=True)
class DecisionMap:
    source: str
    target: str

    def to_term(self) -> dict[str, Any]:
        return {
            "source": self.source,
            "target": self.target,
            "equal": self.source == self.target,
        }


@dataclass(frozen=True, slots=True)
class PreservedOccurrenceMapEntry:
    occurrence: str
    source_index: int
    target_index: int

    def to_term(self) -> dict[str, Any]:
        return {
            "occurrence": self.occurrence,
            "source_index": self.source_index,
            "target_index": self.target_index,
        }


@dataclass(frozen=True, slots=True)
class InsertedWorkOccurrence:
    occurrence: str
    target_index: int
    value_id: SemanticId

    def to_term(self) -> dict[str, Any]:
        return {
            "occurrence": self.occurrence,
            "target_index": self.target_index,
            "value_id": self.value_id.to_term(),
        }


@dataclass(frozen=True, slots=True)
class CommittedFreshRun:
    """One public committed execution under externally supplied Fresh coins."""

    algebra_profile_id: SemanticId
    commitment_profile_id: SemanticId
    core_id: SemanticId
    statement: Any
    application_context: Any
    cap0: MerkleCap
    beta0: Fp2
    cap1: MerkleCap
    beta1: Fp2
    terminal_coefficients: tuple[Fp2, ...]
    query_draws: tuple[RandomQueryDraw, ...]
    opening_table: tuple[OpeningTableEntry, ...]
    occurrence_selectors: tuple[OccurrenceSelector, ...]

    def __post_init__(self) -> None:
        if type(self) is not CommittedFreshRun:
            raise malformed(
                "constructions:committed-fresh-formation",
                "FRI-IOR-CONSTRUCTION-003",
                "a committed Fresh run requires the exact closed carrier",
            )
        if not all(
            isinstance(value, expected)
            for value, expected in (
                (self.algebra_profile_id, SemanticId),
                (self.commitment_profile_id, SemanticId),
                (self.core_id, SemanticId),
                (self.cap0, MerkleCap),
                (self.beta0, Fp2),
                (self.cap1, MerkleCap),
                (self.beta1, Fp2),
            )
        ):
            raise malformed(
                "constructions:committed-fresh-formation",
                "FRI-IOR-CONSTRUCTION-003",
                "a committed Fresh run contains a wrong-kind semantic value",
            )
        object.__setattr__(
            self,
            "statement",
            _freeze_public_environment_term(self.statement),
        )
        object.__setattr__(
            self,
            "application_context",
            _freeze_public_environment_term(self.application_context),
        )
        if (
            type(self.terminal_coefficients) is not tuple
            or not self.terminal_coefficients
            or not all(isinstance(item, Fp2) for item in self.terminal_coefficients)
            or type(self.query_draws) is not tuple
            or not all(type(item) is RandomQueryDraw for item in self.query_draws)
            or type(self.opening_table) is not tuple
            or not all(type(item) is OpeningTableEntry for item in self.opening_table)
            or type(self.occurrence_selectors) is not tuple
            or not all(
                type(item) is OccurrenceSelector for item in self.occurrence_selectors
            )
        ):
            raise malformed(
                "constructions:committed-fresh-formation",
                "FRI-IOR-CONSTRUCTION-003",
                "a committed Fresh run requires exact immutable sequences",
            )
        encode_term(self.to_term())

    def to_term(self) -> dict[str, Any]:
        return {
            "schema": COMMITTED_FRESH_RUN_SCHEMA,
            "algebra_profile_id": self.algebra_profile_id.to_term(),
            "commitment_profile_id": self.commitment_profile_id.to_term(),
            "core_id": self.core_id.to_term(),
            "public_environment": {
                "statement": _public_environment_term_copy(self.statement),
                "application_context": _public_environment_term_copy(
                    self.application_context
                ),
            },
            "publications": {
                "cap0": self.cap0.to_term(),
                "cap1": self.cap1.to_term(),
                "terminal_coefficients": [
                    coefficient.to_term() for coefficient in self.terminal_coefficients
                ],
                "opening_table": [entry.to_term() for entry in self.opening_table],
                "occurrence_selectors": [
                    selector.to_term() for selector in self.occurrence_selectors
                ],
            },
            "fresh_coins": {
                "beta0": self.beta0.to_term(),
                "beta1": self.beta1.to_term(),
                "ordered_query_occurrences": [
                    _draw_term(draw) for draw in self.query_draws
                ],
            },
            "verdict_scope": "one-execution-sampled-equations-only",
        }

    @property
    def identity(self) -> SemanticId:
        return semantic_id(
            "committed-fresh-fri-run",
            "fri-ior.committed-fresh-run.v1",
            self.to_term(),
        )


def _as_explicit_committed_execution(
    run: CommittedFreshRun,
) -> ExplicitCommittedFriExecution:
    return ExplicitCommittedFriExecution(
        run.algebra_profile_id,
        run.commitment_profile_id,
        run.cap0,
        run.beta0,
        run.cap1,
        run.beta1,
        run.terminal_coefficients,
        run.query_draws,
        run.opening_table,
        run.occurrence_selectors,
    )


def _verify_committed_fresh(
    run: CommittedFreshRun,
    resources: ResourceCounter,
) -> CheckResult:
    if (
        run.algebra_profile_id != EXACT_ALGEBRA_PROFILE.identity
        or run.commitment_profile_id != EXACT_COMMITMENT_PROFILE.identity
        or run.core_id != COMMITTED_FRI_CORE.identity
    ):
        return _refusal(
            "FRI-IOR-CONSTRUCTION-004",
            "the committed Fresh run names unsupported algebra, commitment, or Core subjects",
        )
    explicit = _as_explicit_committed_execution(run)
    result = verify_explicit_committed_fri(explicit, resources)
    if result.outcome is not OutcomeClass.AFFIRMATIVE:
        return result
    return affirmative(
        "constructions:committed-fresh-verification",
        "FRI-IOR-CONSTRUCTION-100",
        "the one committed Fresh execution accepts",
        subject=run.identity,
        verdict="Accept",
        ordered_query_indices=tuple(
            draw.initial_domain_index for draw in run.query_draws
        ),
        establishes_proximity=False,
        establishes_outer_relation=False,
    )


def verify_committed_fresh_run(
    candidate: object,
    limits: object = DEFAULT_VALIDATION_LIMITS,
) -> CheckResult:
    """Verify one committed Fresh run under a privately created meter."""

    if type(candidate) is not CommittedFreshRun:
        return _malformed_result(
            "FRI-IOR-CONSTRUCTION-011",
            "committed Fresh verification requires the exact run carrier",
        )
    if type(limits) is not ResourceLimits:
        return _malformed_result(
            "FRI-IOR-CONSTRUCTION-012",
            "authoritative Fresh verification requires exact immutable limits",
        )
    try:
        return _verify_committed_fresh(candidate, ResourceCounter(limits))
    except ModelFailure as error:
        return error.to_result()
    except Exception as error:  # pragma: no cover - fault-injection boundary
        return checker_failure(
            "constructions:committed-fresh-verification",
            f"unexpected Fresh-verifier failure: {type(error).__name__}",
        )


def _build_public_target(
    source: NativeFriTrace,
    statement: Any,
    application_context: Any,
    tree0: Any,
    tree1: Any,
) -> CommittedFreshRun:
    keys = tuple(
        sorted(
            {
                key
                for draw in source.query_draws
                for key in (
                    (0, draw.initial_domain_index % (D0.order // 2)),
                    (1, draw.initial_domain_index % (D1.order // 2)),
                )
            }
        )
    )
    opening_table = tuple(
        OpeningTableEntry(
            layer,
            (tree0 if layer == 0 else tree1).open_pair(pair_index),
        )
        for layer, pair_index in keys
    )
    table_index = {entry.key: index for index, entry in enumerate(opening_table)}
    selectors = tuple(
        OccurrenceSelector(
            draw.ordinal,
            table_index[(0, draw.initial_domain_index % (D0.order // 2))],
            table_index[(1, draw.initial_domain_index % (D1.order // 2))],
        )
        for draw in source.query_draws
    )
    return CommittedFreshRun(
        EXACT_ALGEBRA_PROFILE.identity,
        EXACT_COMMITMENT_PROFILE.identity,
        COMMITTED_FRI_CORE.identity,
        statement,
        application_context,
        tree0.cap,
        source.beta0,
        tree1.cap,
        source.beta1,
        source.terminal.coefficients,
        source.query_draws,
        opening_table,
        selectors,
    )


def _expected_compilation_maps(
    source: NativeFriTrace,
    target: CommittedFreshRun,
    resources: ResourceCounter,
) -> tuple[
    tuple[PublicationMapEntry, ...],
    tuple[CoinMapEntry, ...],
    tuple[QueryOccurrenceMapEntry, ...],
    tuple[ExtractedAnswerMapEntry, ...],
    TerminalMap,
]:
    publications = (
        PublicationMapEntry(
            "publish-initial-logical-oracle",
            "publish-cap-0",
            _oracle_carrier_identity(source, 0),
            target.cap0.identity,
        ),
        PublicationMapEntry(
            "publish-prover-logical-oracle",
            "publish-cap-1",
            _oracle_carrier_identity(source, 1),
            target.cap1.identity,
        ),
    )
    coins: list[CoinMapEntry] = [
        CoinMapEntry(
            "fresh-beta0",
            "fresh-fold-challenge-0",
            _fp2_identity("native.beta0", source.beta0),
            _fp2_identity("committed.beta0", target.beta0),
        ),
        CoinMapEntry(
            "fresh-beta1",
            "fresh-fold-challenge-1",
            _fp2_identity("native.beta1", source.beta1),
            _fp2_identity("committed.beta1", target.beta1),
        ),
    ]
    queries: list[QueryOccurrenceMapEntry] = []
    for source_draw, target_draw in zip(
        source.query_draws,
        target.query_draws,
        strict=True,
    ):
        source_name = f"native.query-draw[{source_draw.ordinal}]"
        target_name = f"committed.query-occurrence[{target_draw.ordinal}]"
        source_id = _draw_identity(source_name, source_draw)
        target_id = _draw_identity(target_name, target_draw)
        coins.append(CoinMapEntry(source_name, target_name, source_id, target_id))
        queries.append(
            QueryOccurrenceMapEntry(source_draw.ordinal, source_id, target_id)
        )

    resolved = resolve_layer_query_answers(source, resources)
    if isinstance(resolved, CheckResult):
        raise ModelFailure(
            resolved.outcome,
            resolved.boundary,
            resolved.code,
            resolved.detail,
        )
    answers: list[ExtractedAnswerMapEntry] = []
    for source_initial, source_first, selector in zip(
        resolved[::2],
        resolved[1::2],
        target.occurrence_selectors,
        strict=True,
    ):
        for layer, query, table_index in (
            (0, source_initial, selector.layer0_opening_index),
            (1, source_first, selector.layer1_opening_index),
        ):
            opening = target.opening_table[table_index].opening
            answers.append(
                ExtractedAnswerMapEntry(
                    query.top_level_ordinal,
                    layer,
                    _layer_query_identity(query),
                    table_index,
                    opening.identity,
                )
            )
    terminal = TerminalMap(
        _terminal_identity(source.terminal.coefficients),
        _terminal_identity(target.terminal_coefficients),
    )
    return publications, tuple(coins), tuple(queries), tuple(answers), terminal


def _expected_public_environment_map(
    source: FreshPublicEnvironment,
    target: CommittedFreshRun,
) -> tuple[PublicEnvironmentMapEntry, ...]:
    pairs = (
        ("statement", source.statement, target.statement),
        (
            "application-context",
            source.application_context,
            target.application_context,
        ),
    )
    return tuple(
        PublicEnvironmentMapEntry(
            occurrence,
            _public_environment_value_identity(occurrence, source_value),
            _public_environment_value_identity(occurrence, target_value),
        )
        for occurrence, source_value, target_value in pairs
    )


@dataclass(frozen=True, slots=True)
class NativeToCommittedFreshCandidate:
    advice: CommitmentAdvice = field(repr=False)
    source_public_environment: FreshPublicEnvironment
    source_trace: NativeFriTrace = field(repr=False)
    target_run: CommittedFreshRun
    public_environment_map: tuple[PublicEnvironmentMapEntry, ...]
    publication_map: tuple[PublicationMapEntry, ...]
    coin_map: tuple[CoinMapEntry, ...]
    query_occurrence_map: tuple[QueryOccurrenceMapEntry, ...]
    extracted_answer_map: tuple[ExtractedAnswerMapEntry, ...]
    terminal_map: TerminalMap
    decision_map: DecisionMap
    declaration_id: SemanticId

    def semantic_term(self) -> dict[str, Any]:
        return {
            "schema": "zkc.fri-ior.native-to-committed-fresh-candidate.v1",
            "declaration_id": self.declaration_id.to_term(),
            "source_core_id": NATIVE_FRI_CORE.identity.to_term(),
            "target_core_id": COMMITTED_FRI_CORE.identity.to_term(),
            "selected_semantics": {
                "algebra_profile_id": self.target_run.algebra_profile_id.to_term(),
                "commitment_profile_id": (
                    self.target_run.commitment_profile_id.to_term()
                ),
            },
            "source_public_environment_id": (
                self.source_public_environment.identity.to_term()
            ),
            "source_trace_id": self.source_trace.identity.to_term(),
            "target_run_id": self.target_run.identity.to_term(),
            "maps": {
                "complete_public_environment_map": [
                    item.to_term() for item in self.public_environment_map
                ],
                "complete_publication_map": [
                    item.to_term() for item in self.publication_map
                ],
                "complete_fresh_coin_map": [item.to_term() for item in self.coin_map],
                "complete_query_occurrence_map": [
                    item.to_term() for item in self.query_occurrence_map
                ],
                "complete_extracted_answer_map": [
                    item.to_term() for item in self.extracted_answer_map
                ],
                "terminal_map": self.terminal_map.to_term(),
                "decision_map": self.decision_map.to_term(),
            },
            "scope": "one-concrete-native-to-committed-fresh-execution",
            "nonclaims": list(_CONSTRUCTION_NONCLAIMS),
        }


_COMMITMENT_RECEIPT_TOKEN = object()


@dataclass(frozen=True, slots=True, init=False)
class CheckedNativeToCommittedFreshRun:
    candidate: NativeToCommittedFreshCandidate
    semantic_execution_id: SemanticId
    validation_basis_id: ValidationBasisId
    validation_source_manifest: tuple[ConstructionValidationSource, ...]
    validation_limits: ResourceLimits
    resource_usage: ExactResourceUsage

    def __init__(
        self,
        candidate: NativeToCommittedFreshCandidate,
        validation_limits: ResourceLimits,
        resource_usage: ExactResourceUsage,
        *,
        _token: object,
    ) -> None:
        if _token is not _COMMITMENT_RECEIPT_TOKEN:
            raise ModelFailure(
                OutcomeClass.MISSING_DEPENDENCY,
                "constructions:commitment-receipt-formation",
                "FRI-IOR-CONSTRUCTION-013",
                "a commitment-construction receipt requires the authoritative checker",
            )
        object.__setattr__(self, "candidate", candidate)
        object.__setattr__(
            self,
            "semantic_execution_id",
            semantic_id(
                "native-to-committed-fresh-execution",
                "fri-ior.native-to-committed-fresh-execution.v1",
                candidate.semantic_term(),
            ),
        )
        basis, manifest = _validation_basis(
            COMMITMENT_VALIDATION_LAW, validation_limits
        )
        object.__setattr__(self, "validation_basis_id", basis)
        object.__setattr__(self, "validation_source_manifest", manifest)
        object.__setattr__(self, "validation_limits", validation_limits)
        object.__setattr__(self, "resource_usage", resource_usage)

    @property
    def target_run(self) -> CommittedFreshRun:
        return self.candidate.target_run

    def to_term(self) -> dict[str, Any]:
        return {
            "schema": COMMITMENT_RECEIPT_SCHEMA,
            "semantic_execution_id": self.semantic_execution_id.to_term(),
            "semantic_execution": self.candidate.semantic_term(),
            "validation": {
                "law": COMMITMENT_VALIDATION_LAW,
                "basis_id": str(self.validation_basis_id),
                "source_manifest": [
                    source.to_term() for source in self.validation_source_manifest
                ],
                "selected_resource_limits": self.validation_limits.to_term(),
                "exact_resource_usage": self.resource_usage.to_term(),
            },
        }

    @property
    def identity(self) -> SemanticId:
        return semantic_id(
            "checked-native-to-committed-fresh-execution",
            "fri-ior.checked-native-to-committed-fresh-execution.v1",
            self.to_term(),
        )


@dataclass(frozen=True, slots=True)
class CommitmentCompilationAdmission:
    result: CheckResult
    checked_receipt: CheckedNativeToCommittedFreshRun | None


def _compilation_failure(result: CheckResult) -> CommitmentCompilationAdmission:
    return CommitmentCompilationAdmission(result, None)


def check_native_to_committed_fresh(
    candidate: object,
    limits: object = DEFAULT_VALIDATION_LIMITS,
) -> CommitmentCompilationAdmission:
    """Check one complete Native-to-Committed Fresh execution map."""

    if type(candidate) is not NativeToCommittedFreshCandidate:
        return _compilation_failure(
            _malformed_result(
                "FRI-IOR-CONSTRUCTION-014",
                "commitment compilation requires the exact candidate carrier",
            )
        )
    if type(limits) is not ResourceLimits:
        return _compilation_failure(
            _malformed_result(
                "FRI-IOR-CONSTRUCTION-012",
                "the construction checker requires exact immutable limits",
            )
        )
    try:
        resources = ResourceCounter(limits)
        if candidate.declaration_id != COMMITMENT_COMPILATION_DECLARATION.identity:
            return _compilation_failure(
                _refusal(
                    "FRI-IOR-CONSTRUCTION-015",
                    "the execution names a different commitment-compilation declaration",
                )
            )
        if type(candidate.source_public_environment) is not FreshPublicEnvironment:
            return _compilation_failure(
                _malformed_result(
                    "FRI-IOR-CONSTRUCTION-058",
                    "the construction requires an exact source PublicEnvironment carrier",
                )
            )
        if (
            candidate.source_public_environment.statement
            != candidate.target_run.statement
            or candidate.source_public_environment.application_context
            != candidate.target_run.application_context
            or candidate.public_environment_map
            != _expected_public_environment_map(
                candidate.source_public_environment,
                candidate.target_run,
            )
        ):
            return _compilation_failure(
                _refusal(
                    "FRI-IOR-CONSTRUCTION-059",
                    "the statement/context environment map is not exact, complete, and unchanged",
                )
            )
        source_result = verify_native_trace(candidate.source_trace, resources)
        if source_result.outcome is not OutcomeClass.AFFIRMATIVE:
            return _compilation_failure(source_result)
        target_result = _verify_committed_fresh(candidate.target_run, resources)
        if target_result.outcome is not OutcomeClass.AFFIRMATIVE:
            return _compilation_failure(target_result)

        tree0 = build_commitment(
            D0,
            tuple(
                entry.value for entry in candidate.source_trace.initial_oracle.entries
            ),
            candidate.advice.initial_layer_salts,
            resources,
        )
        tree1 = build_commitment(
            D1,
            tuple(
                entry.value for entry in candidate.source_trace.prover_oracle.entries
            ),
            candidate.advice.first_fold_layer_salts,
            resources,
        )
        if (
            tree0.cap != candidate.target_run.cap0
            or tree1.cap != candidate.target_run.cap1
        ):
            return _compilation_failure(
                _refusal(
                    "FRI-IOR-CONSTRUCTION-016",
                    "the complete owner-local oracles and advice do not rebuild the target caps",
                )
            )
        if (
            candidate.source_trace.beta0 != candidate.target_run.beta0
            or candidate.source_trace.beta1 != candidate.target_run.beta1
            or candidate.source_trace.query_draws != candidate.target_run.query_draws
            or candidate.source_trace.terminal.coefficients
            != candidate.target_run.terminal_coefficients
        ):
            return _compilation_failure(
                _refusal(
                    "FRI-IOR-CONSTRUCTION-017",
                    "Fresh coins, occurrences, or terminal material do not commute",
                )
            )
        expected = _expected_compilation_maps(
            candidate.source_trace,
            candidate.target_run,
            resources,
        )
        actual = (
            candidate.publication_map,
            candidate.coin_map,
            candidate.query_occurrence_map,
            candidate.extracted_answer_map,
            candidate.terminal_map,
        )
        if actual[0] != expected[0]:
            code = "FRI-IOR-CONSTRUCTION-018"
            detail = "the cap/publication map is not exact and complete"
        elif actual[1] != expected[1]:
            code = "FRI-IOR-CONSTRUCTION-019"
            detail = "the Fresh coin map is not exact and complete"
        elif actual[2] != expected[2]:
            code = "FRI-IOR-CONSTRUCTION-020"
            detail = "the query-occurrence map does not preserve order and multiplicity"
        elif actual[3] != expected[3]:
            code = "FRI-IOR-CONSTRUCTION-021"
            detail = "the extracted-answer map is not exact and complete"
        elif actual[4] != expected[4]:
            code = "FRI-IOR-CONSTRUCTION-022"
            detail = "the terminal map is not exact"
        else:
            code = ""
            detail = ""
        if code:
            return _compilation_failure(_refusal(code, detail))
        if candidate.decision_map != DecisionMap("Accept", "Accept"):
            return _compilation_failure(
                _refusal(
                    "FRI-IOR-CONSTRUCTION-023",
                    "the execution decision map is stale or unequal",
                )
            )

        receipt = CheckedNativeToCommittedFreshRun(
            candidate,
            limits,
            ExactResourceUsage.from_counter(resources),
            _token=_COMMITMENT_RECEIPT_TOKEN,
        )
        return CommitmentCompilationAdmission(
            affirmative(
                "constructions:native-to-committed-fresh",
                "FRI-IOR-CONSTRUCTION-101",
                "one native execution and its committed Fresh compilation commute",
                subject=receipt.identity,
                public_environment_map_entries=len(candidate.public_environment_map),
                publication_map_entries=len(candidate.publication_map),
                fresh_coin_map_entries=len(candidate.coin_map),
                query_occurrence_map_entries=len(candidate.query_occurrence_map),
                extracted_answer_map_entries=len(candidate.extracted_answer_map),
                scope="one-execution",
            ),
            receipt,
        )
    except ModelFailure as error:
        return _compilation_failure(error.to_result())
    except Exception as error:  # pragma: no cover - fault-injection boundary
        return _compilation_failure(
            checker_failure(
                "constructions:native-to-committed-fresh",
                f"unexpected construction-checker failure: {type(error).__name__}",
            )
        )


def generate_native_to_committed_fresh(
    private_material: object,
    statement: Any,
    application_context: Any,
    beta0: object,
    beta1: object,
    ordered_query_draws: object,
    limits: object = DEFAULT_VALIDATION_LIMITS,
) -> CommitmentCompilationAdmission:
    """Generate and check one run from externally supplied Fresh values."""

    if type(private_material) is not PrivateFriGenerationMaterial:
        return _compilation_failure(
            _malformed_result(
                "FRI-IOR-CONSTRUCTION-024",
                "Fresh generation requires exact owner-local polynomial material",
            )
        )
    if type(limits) is not ResourceLimits:
        return _compilation_failure(
            _malformed_result(
                "FRI-IOR-CONSTRUCTION-012",
                "Fresh generation requires exact immutable limits",
            )
        )
    if not isinstance(beta0, Fp2) or not isinstance(beta1, Fp2):
        return _compilation_failure(
            _malformed_result(
                "FRI-IOR-CONSTRUCTION-025",
                "Fresh generation requires two externally supplied Fp2 coins",
            )
        )
    if type(ordered_query_draws) is not tuple or not all(
        type(index) is int for index in ordered_query_draws
    ):
        return _compilation_failure(
            _malformed_result(
                "FRI-IOR-CONSTRUCTION-026",
                "Fresh generation requires an external ordered integer draw sequence",
            )
        )
    try:
        public_environment = FreshPublicEnvironment(statement, application_context)
        generation_resources = ResourceCounter(limits)
        source = derive_honest_native_trace(
            private_material.coefficients,
            beta0,
            beta1,
            ordered_query_draws,
            generation_resources,
        )
        advice = CommitmentAdvice(
            private_material.initial_layer_salts,
            private_material.first_fold_layer_salts,
        )
        tree0 = build_commitment(
            D0,
            tuple(entry.value for entry in source.initial_oracle.entries),
            advice.initial_layer_salts,
            generation_resources,
        )
        tree1 = build_commitment(
            D1,
            tuple(entry.value for entry in source.prover_oracle.entries),
            advice.first_fold_layer_salts,
            generation_resources,
        )
        target = _build_public_target(
            source,
            public_environment.statement,
            public_environment.application_context,
            tree0,
            tree1,
        )
        maps = _expected_compilation_maps(source, target, generation_resources)
        candidate = NativeToCommittedFreshCandidate(
            advice,
            public_environment,
            source,
            target,
            _expected_public_environment_map(public_environment, target),
            maps[0],
            maps[1],
            maps[2],
            maps[3],
            maps[4],
            DecisionMap("Accept", "Accept"),
            COMMITMENT_COMPILATION_DECLARATION.identity,
        )
        return check_native_to_committed_fresh(candidate, limits)
    except ModelFailure as error:
        return _compilation_failure(error.to_result())
    except Exception as error:  # pragma: no cover - fault-injection boundary
        return _compilation_failure(
            checker_failure(
                "constructions:native-to-committed-fresh-generation",
                f"unexpected Fresh-generation failure: {type(error).__name__}",
            )
        )


def _frame_work(payload: bytes, resources: ResourceCounter) -> bytes:
    namespace = WORK_CHECK_NAMESPACE.encode("ascii")
    codec = WORK_RULE.encode("ascii")
    framed = (
        len(namespace).to_bytes(2, "big")
        + namespace
        + len(codec).to_bytes(2, "big")
        + codec
        + len(payload).to_bytes(4, "big")
        + payload
    )
    resources.consume_transcript_frames(1)
    return framed


def _exact_work_digest(
    work_seed: bytes,
    nonce: int,
    resources: ResourceCounter,
) -> bytes:
    if type(work_seed) is not bytes or len(work_seed) != 32:
        raise malformed(
            "constructions:work-check",
            "FRI-IOR-CONSTRUCTION-027",
            "the Fresh work seed must contain exactly 32 bytes",
        )
    if type(nonce) is not int or not 0 <= nonce <= MAX_GRINDING_NONCE:
        raise malformed(
            "constructions:work-check",
            "FRI-IOR-CONSTRUCTION-028",
            "the work nonce must fit the selected grinding-profile width",
        )
    resources.consume_grinding_trials(1)
    payload = _WORK_DOMAIN + _frame_work(
        work_seed + nonce.to_bytes(EXACT_GRINDING_PROFILE.nonce_bytes, "big"),
        resources,
    )
    resources.consume_hash(len(payload))
    return hashlib.sha256(payload).digest()


def _work_succeeds(digest: bytes) -> bool:
    return digest[0] >> (8 - EXACT_GRINDING_PROFILE.difficulty_bits) == 0


@dataclass(frozen=True, slots=True)
class WorkAugmentedFreshRun:
    source_run: CommittedFreshRun
    core_id: SemanticId
    protocol_id: SemanticId
    work_seed: bytes
    nonce: int
    work_digest: bytes

    def __post_init__(self) -> None:
        if (
            type(self) is not WorkAugmentedFreshRun
            or type(self.source_run) is not CommittedFreshRun
            or not isinstance(self.core_id, SemanticId)
            or not isinstance(self.protocol_id, SemanticId)
            or type(self.work_seed) is not bytes
            or len(self.work_seed) != 32
            or type(self.nonce) is not int
            or not 0 <= self.nonce <= MAX_GRINDING_NONCE
            or type(self.work_digest) is not bytes
            or len(self.work_digest) != 32
        ):
            raise malformed(
                "constructions:work-fresh-formation",
                "FRI-IOR-CONSTRUCTION-029",
                "a work-augmented Fresh run requires the exact closed carrier",
            )

    def to_term(self) -> dict[str, Any]:
        return {
            "schema": WORK_AUGMENTED_FRESH_RUN_SCHEMA,
            "preserved_committed_run_id": self.source_run.identity.to_term(),
            "core_id": self.core_id.to_term(),
            "protocol_id": self.protocol_id.to_term(),
            "inserted_work": {
                "work_seed": self.work_seed.hex(),
                "nonce": self.nonce,
                "work_digest": self.work_digest.hex(),
                "placement": "after-terminal-before-query-randomness",
            },
            "scope": "one-explicit-fresh-work-execution",
        }

    @property
    def identity(self) -> SemanticId:
        return semantic_id(
            "work-augmented-committed-fresh-run",
            "fri-ior.work-augmented-committed-fresh-run.v1",
            self.to_term(),
        )


def _verify_work_augmented_fresh(
    run: WorkAugmentedFreshRun,
    resources: ResourceCounter,
) -> CheckResult:
    if (
        run.core_id != WORK_AUGMENTED_COMMITTED_FRI_CORE.identity
        or run.protocol_id != FRESH_WORK_AUGMENTED_PROTOCOL.identity
    ):
        return _refusal(
            "FRI-IOR-CONSTRUCTION-030",
            "the work-augmented run names unsupported Core or Fresh Protocol subjects",
        )
    prefix_result = verify_explicit_committed_prefix(
        _as_explicit_committed_execution(run.source_run),
        resources,
    )
    if prefix_result.outcome is not OutcomeClass.AFFIRMATIVE:
        return prefix_result
    expected_digest = _exact_work_digest(run.work_seed, run.nonce, resources)
    if expected_digest != run.work_digest:
        return _refusal(
            "FRI-IOR-CONSTRUCTION-031",
            "the published work-check digest does not match the exact predicate",
            target_verdict="Reject",
            rejection_before_query_suffix=True,
            target_resource_usage=resources.snapshot(),
        )
    if not _work_succeeds(expected_digest):
        return _refusal(
            "FRI-IOR-CONSTRUCTION-032",
            "the invalid nonce is refused before the target query/opening suffix",
            target_verdict="Reject",
            rejection_before_query_suffix=True,
            target_resource_usage=resources.snapshot(),
        )
    suffix_result = _verify_committed_fresh(run.source_run, resources)
    if suffix_result.outcome is not OutcomeClass.AFFIRMATIVE:
        return suffix_result
    return affirmative(
        "constructions:work-augmented-fresh-verification",
        "FRI-IOR-CONSTRUCTION-102",
        "the committed run and inserted Fresh work check accept",
        subject=run.identity,
        source_verdict="Accept",
        target_verdict="Accept",
        target_only_invalid_nonce_refusal=True,
        establishes_work_amplification=False,
    )


def verify_work_augmented_fresh_run(
    candidate: object,
    limits: object = DEFAULT_VALIDATION_LIMITS,
) -> CheckResult:
    if type(candidate) is not WorkAugmentedFreshRun:
        return _malformed_result(
            "FRI-IOR-CONSTRUCTION-033",
            "work-augmented verification requires the exact run carrier",
        )
    if type(limits) is not ResourceLimits:
        return _malformed_result(
            "FRI-IOR-CONSTRUCTION-012",
            "authoritative work verification requires exact immutable limits",
        )
    try:
        source_resources = ResourceCounter(limits)
        source_result = _verify_committed_fresh(candidate.source_run, source_resources)
        if source_result.outcome is not OutcomeClass.AFFIRMATIVE:
            return source_result
        target_resources = ResourceCounter(limits)
        target_result = _verify_work_augmented_fresh(candidate, target_resources)
        if target_result.outcome is OutcomeClass.AFFIRMATIVE:
            return target_result
        return CheckResult(
            target_result.outcome,
            target_result.boundary,
            target_result.code,
            target_result.detail,
            target_result.subject,
            {
                **target_result.evidence,
                "source_verdict": "Accept",
                "target_only": True,
                "source_resource_usage": source_resources.snapshot(),
                "target_resource_usage": target_resources.snapshot(),
            },
        )
    except ModelFailure as error:
        return error.to_result()
    except Exception as error:  # pragma: no cover
        return checker_failure(
            "constructions:work-augmented-fresh-verification",
            f"unexpected work-verifier failure: {type(error).__name__}",
        )


def _expected_preserved_map() -> tuple[PreservedOccurrenceMapEntry, ...]:
    return tuple(
        PreservedOccurrenceMapEntry(
            occurrence,
            source_index,
            _WORK_SCHEDULE.index(occurrence),
        )
        for source_index, occurrence in enumerate(_COMMITTED_SCHEDULE)
    )


def _inserted_value_identity(occurrence: str, value: Any) -> SemanticId:
    return semantic_id(
        "inserted-work-occurrence",
        "fri-ior.inserted-work-occurrence.v1",
        {"occurrence": occurrence, "value": value},
    )


def _expected_insertion_map(
    target: WorkAugmentedFreshRun,
) -> tuple[InsertedWorkOccurrence, ...]:
    values: tuple[Any, ...] = (
        target.work_seed.hex(),
        target.nonce,
        {
            "digest": target.work_digest.hex(),
            "succeeds": _work_succeeds(target.work_digest),
        },
    )
    return tuple(
        InsertedWorkOccurrence(
            occurrence,
            _WORK_SCHEDULE.index(occurrence),
            _inserted_value_identity(occurrence, value),
        )
        for occurrence, value in zip(_INSERTED_WORK_OCCURRENCES, values, strict=True)
    )


@dataclass(frozen=True, slots=True)
class CommittedToWorkFreshCandidate:
    source_run: CommittedFreshRun
    target_run: WorkAugmentedFreshRun
    preserved_occurrence_map: tuple[PreservedOccurrenceMapEntry, ...]
    inserted_work_map: tuple[InsertedWorkOccurrence, ...]
    decision_map: DecisionMap
    declaration_id: SemanticId

    def semantic_term(self) -> dict[str, Any]:
        return {
            "schema": "zkc.fri-ior.committed-to-work-fresh-candidate.v1",
            "declaration_id": self.declaration_id.to_term(),
            "source_core_id": COMMITTED_FRI_CORE.identity.to_term(),
            "target_core_id": WORK_AUGMENTED_COMMITTED_FRI_CORE.identity.to_term(),
            "target_fresh_protocol_id": FRESH_WORK_AUGMENTED_PROTOCOL.identity.to_term(),
            "source_run_id": self.source_run.identity.to_term(),
            "target_run_id": self.target_run.identity.to_term(),
            "complete_preserved_occurrence_map": [
                item.to_term() for item in self.preserved_occurrence_map
            ],
            "exact_inserted_work_map": [
                item.to_term() for item in self.inserted_work_map
            ],
            "decision_map": self.decision_map.to_term(),
            "scope": "one-concrete-committed-to-work-fresh-execution",
            "nonclaims": list(_CONSTRUCTION_NONCLAIMS),
        }


_GRINDING_RECEIPT_TOKEN = object()


@dataclass(frozen=True, slots=True, init=False)
class CheckedCommittedToWorkFreshRun:
    candidate: CommittedToWorkFreshCandidate
    semantic_execution_id: SemanticId
    validation_basis_id: ValidationBasisId
    validation_source_manifest: tuple[ConstructionValidationSource, ...]
    validation_limits: ResourceLimits
    resource_usage: SeparatedResourceUsage

    def __init__(
        self,
        candidate: CommittedToWorkFreshCandidate,
        validation_limits: ResourceLimits,
        resource_usage: SeparatedResourceUsage,
        *,
        _token: object,
    ) -> None:
        if _token is not _GRINDING_RECEIPT_TOKEN:
            raise ModelFailure(
                OutcomeClass.MISSING_DEPENDENCY,
                "constructions:grinding-receipt-formation",
                "FRI-IOR-CONSTRUCTION-034",
                "a grinding-augmentation receipt requires the authoritative checker",
            )
        object.__setattr__(self, "candidate", candidate)
        object.__setattr__(
            self,
            "semantic_execution_id",
            semantic_id(
                "committed-to-work-fresh-execution",
                "fri-ior.committed-to-work-fresh-execution.v1",
                candidate.semantic_term(),
            ),
        )
        basis, manifest = _validation_basis(GRINDING_VALIDATION_LAW, validation_limits)
        object.__setattr__(self, "validation_basis_id", basis)
        object.__setattr__(self, "validation_source_manifest", manifest)
        object.__setattr__(self, "validation_limits", validation_limits)
        object.__setattr__(self, "resource_usage", resource_usage)

    @property
    def target_run(self) -> WorkAugmentedFreshRun:
        return self.candidate.target_run

    def to_term(self) -> dict[str, Any]:
        return {
            "schema": GRINDING_RECEIPT_SCHEMA,
            "semantic_execution_id": self.semantic_execution_id.to_term(),
            "semantic_execution": self.candidate.semantic_term(),
            "validation": {
                "law": GRINDING_VALIDATION_LAW,
                "basis_id": str(self.validation_basis_id),
                "source_manifest": [
                    source.to_term() for source in self.validation_source_manifest
                ],
                "selected_resource_limits": self.validation_limits.to_term(),
                "exact_resource_usage": self.resource_usage.to_term(),
            },
        }

    @property
    def identity(self) -> SemanticId:
        return semantic_id(
            "checked-committed-to-work-fresh-execution",
            "fri-ior.checked-committed-to-work-fresh-execution.v1",
            self.to_term(),
        )


@dataclass(frozen=True, slots=True)
class GrindingAugmentationAdmission:
    result: CheckResult
    checked_receipt: CheckedCommittedToWorkFreshRun | None


def _grinding_failure(result: CheckResult) -> GrindingAugmentationAdmission:
    return GrindingAugmentationAdmission(result, None)


def check_committed_to_work_fresh(
    candidate: object,
    limits: object = DEFAULT_VALIDATION_LIMITS,
) -> GrindingAugmentationAdmission:
    """Check one exact committed-to-work Fresh execution map."""

    if type(candidate) is not CommittedToWorkFreshCandidate:
        return _grinding_failure(
            _malformed_result(
                "FRI-IOR-CONSTRUCTION-035",
                "grinding augmentation requires the exact candidate carrier",
            )
        )
    if type(limits) is not ResourceLimits:
        return _grinding_failure(
            _malformed_result(
                "FRI-IOR-CONSTRUCTION-012",
                "the construction checker requires exact immutable limits",
            )
        )
    try:
        if candidate.declaration_id != GRINDING_AUGMENTATION_DECLARATION.identity:
            return _grinding_failure(
                _refusal(
                    "FRI-IOR-CONSTRUCTION-036",
                    "the execution names a different grinding-augmentation declaration",
                )
            )
        if candidate.target_run.source_run.identity != candidate.source_run.identity:
            return _grinding_failure(
                _refusal(
                    "FRI-IOR-CONSTRUCTION-037",
                    "the augmented target does not preserve the selected committed source run",
                )
            )
        source_resources = ResourceCounter(limits)
        source_result = _verify_committed_fresh(candidate.source_run, source_resources)
        if source_result.outcome is not OutcomeClass.AFFIRMATIVE:
            return _grinding_failure(source_result)
        target_resources = ResourceCounter(limits)
        target_result = _verify_work_augmented_fresh(
            candidate.target_run,
            target_resources,
        )
        if target_result.outcome is not OutcomeClass.AFFIRMATIVE:
            return _grinding_failure(
                CheckResult(
                    target_result.outcome,
                    target_result.boundary,
                    target_result.code,
                    target_result.detail,
                    target_result.subject,
                    {
                        **target_result.evidence,
                        "source_verdict": "Accept",
                        "target_only": True,
                        "source_resource_usage": source_resources.snapshot(),
                        "target_resource_usage": target_resources.snapshot(),
                    },
                )
            )
        if candidate.preserved_occurrence_map != _expected_preserved_map():
            return _grinding_failure(
                _refusal(
                    "FRI-IOR-CONSTRUCTION-038",
                    "the preserved occurrence map is not exact and complete",
                )
            )
        terminal_index = _WORK_SCHEDULE.index("publish-terminal-polynomial")
        query_index = _WORK_SCHEDULE.index(
            "sample-fresh-ordered-query-occurrence-vector"
        )
        inserted_indices = tuple(
            item.target_index for item in candidate.inserted_work_map
        )
        if not all(terminal_index < index < query_index for index in inserted_indices):
            return _grinding_failure(
                _refusal(
                    "FRI-IOR-CONSTRUCTION-040",
                    "the work insertion is not after terminal material and before query randomness",
                )
            )
        if candidate.inserted_work_map != _expected_insertion_map(candidate.target_run):
            return _grinding_failure(
                _refusal(
                    "FRI-IOR-CONSTRUCTION-039",
                    "the inserted work seed, nonce, and check map is not exact",
                )
            )
        if candidate.decision_map != DecisionMap("Accept", "Accept"):
            return _grinding_failure(
                _refusal(
                    "FRI-IOR-CONSTRUCTION-041",
                    "the grinding decision map is stale or unequal",
                )
            )
        receipt = CheckedCommittedToWorkFreshRun(
            candidate,
            limits,
            SeparatedResourceUsage(
                ExactResourceUsage.from_counter(source_resources),
                ExactResourceUsage.from_counter(target_resources),
            ),
            _token=_GRINDING_RECEIPT_TOKEN,
        )
        return GrindingAugmentationAdmission(
            affirmative(
                "constructions:committed-to-work-fresh",
                "FRI-IOR-CONSTRUCTION-103",
                "one committed Fresh run and its work-augmented execution commute",
                subject=receipt.identity,
                preserved_occurrences=len(candidate.preserved_occurrence_map),
                inserted_work_occurrences=len(candidate.inserted_work_map),
                scope="one-execution",
            ),
            receipt,
        )
    except ModelFailure as error:
        return _grinding_failure(error.to_result())
    except Exception as error:  # pragma: no cover
        return _grinding_failure(
            checker_failure(
                "constructions:committed-to-work-fresh",
                f"unexpected construction-checker failure: {type(error).__name__}",
            )
        )


def generate_committed_to_work_fresh(
    compilation_receipt: object,
    work_seed: object,
    nonce: object,
    limits: object = DEFAULT_VALIDATION_LIMITS,
) -> GrindingAugmentationAdmission:
    """Generate and check one explicit Fresh work insertion."""

    if type(compilation_receipt) is not CheckedNativeToCommittedFreshRun:
        return _grinding_failure(
            _malformed_result(
                "FRI-IOR-CONSTRUCTION-042",
                "work generation requires an issued commitment-construction receipt",
            )
        )
    if type(limits) is not ResourceLimits:
        return _grinding_failure(
            _malformed_result(
                "FRI-IOR-CONSTRUCTION-012",
                "work generation requires exact immutable limits",
            )
        )
    try:
        resources = ResourceCounter(limits)
        digest = _exact_work_digest(work_seed, nonce, resources)
        target = WorkAugmentedFreshRun(
            compilation_receipt.target_run,
            WORK_AUGMENTED_COMMITTED_FRI_CORE.identity,
            FRESH_WORK_AUGMENTED_PROTOCOL.identity,
            work_seed,
            nonce,
            digest,
        )
        candidate = CommittedToWorkFreshCandidate(
            compilation_receipt.target_run,
            target,
            _expected_preserved_map(),
            _expected_insertion_map(target),
            DecisionMap(
                "Accept",
                "Accept" if _work_succeeds(digest) else "Reject",
            ),
            GRINDING_AUGMENTATION_DECLARATION.identity,
        )
        return check_committed_to_work_fresh(candidate, limits)
    except ModelFailure as error:
        return _grinding_failure(error.to_result())
    except Exception as error:  # pragma: no cover
        return _grinding_failure(
            checker_failure(
                "constructions:committed-to-work-fresh-generation",
                f"unexpected work-generation failure: {type(error).__name__}",
            )
        )


_COMPOSITION_TOKEN = object()


@dataclass(frozen=True, slots=True, init=False)
class CheckedConstructionComposition:
    semantic_composition_id: SemanticId
    commitment_receipt_id: SemanticId
    grinding_receipt_id: SemanticId
    fiat_shamir_construction_id: SemanticId
    concrete_fiat_shamir_execution_id: SemanticId
    fiat_shamir_public_inputs_id: SemanticId
    fiat_shamir_public_proof_id: SemanticId
    native_core_id: SemanticId
    committed_core_id: SemanticId
    work_augmented_core_id: SemanticId
    fresh_protocol_id: SemanticId
    fiat_shamir_protocol_id: SemanticId
    validation_basis_id: ValidationBasisId
    validation_source_manifest: tuple[ConstructionValidationSource, ...]
    validation_limits: ResourceLimits
    resource_usage: ExactResourceUsage

    def __init__(
        self,
        commitment_receipt: CheckedNativeToCommittedFreshRun,
        grinding_receipt: CheckedCommittedToWorkFreshRun,
        fiat_shamir_construction: CheckedFiatShamirConstruction,
        concrete_fiat_shamir_execution: CheckedNativeToCommittedExecution,
        validation_limits: ResourceLimits,
        resource_usage: ExactResourceUsage,
        *,
        _token: object,
    ) -> None:
        if _token is not _COMPOSITION_TOKEN:
            raise ModelFailure(
                OutcomeClass.MISSING_DEPENDENCY,
                "constructions:composition-formation",
                "FRI-IOR-CONSTRUCTION-043",
                "a composition receipt requires all checked structural and concrete inputs",
            )
        public_artifacts = concrete_fiat_shamir_execution.public_artifacts
        values = {
            "semantic_composition_id": semantic_id(
                "concrete-construction-composition",
                "fri-ior.concrete-construction-composition.v1",
                {
                    "native_to_committed_fresh_execution_id": (
                        commitment_receipt.semantic_execution_id.to_term()
                    ),
                    "committed_to_work_fresh_execution_id": (
                        grinding_receipt.semantic_execution_id.to_term()
                    ),
                    "fiat_shamir_construction_id": (
                        fiat_shamir_construction.identity.to_term()
                    ),
                    "concrete_fiat_shamir_execution_id": (
                        concrete_fiat_shamir_execution.semantic_execution_id.to_term()
                    ),
                    "public_inputs_id": public_artifacts.public_inputs.identity.to_term(),
                    "public_proof_id": public_artifacts.proof.identity.to_term(),
                },
            ),
            "commitment_receipt_id": commitment_receipt.identity,
            "grinding_receipt_id": grinding_receipt.identity,
            "fiat_shamir_construction_id": fiat_shamir_construction.identity,
            "concrete_fiat_shamir_execution_id": concrete_fiat_shamir_execution.identity,
            "fiat_shamir_public_inputs_id": public_artifacts.public_inputs.identity,
            "fiat_shamir_public_proof_id": public_artifacts.proof.identity,
            "native_core_id": NATIVE_FRI_CORE.identity,
            "committed_core_id": COMMITTED_FRI_CORE.identity,
            "work_augmented_core_id": WORK_AUGMENTED_COMMITTED_FRI_CORE.identity,
            "fresh_protocol_id": FRESH_WORK_AUGMENTED_PROTOCOL.identity,
            "fiat_shamir_protocol_id": FIAT_SHAMIR_WORK_AUGMENTED_PROTOCOL.identity,
        }
        for name, value in values.items():
            object.__setattr__(self, name, value)
        basis, manifest = _validation_basis(
            COMPOSITION_VALIDATION_LAW, validation_limits
        )
        object.__setattr__(self, "validation_basis_id", basis)
        object.__setattr__(self, "validation_source_manifest", manifest)
        object.__setattr__(self, "validation_limits", validation_limits)
        object.__setattr__(self, "resource_usage", resource_usage)

    def to_term(self) -> dict[str, Any]:
        return {
            "schema": COMPOSITION_RECEIPT_SCHEMA,
            "semantic_composition_id": self.semantic_composition_id.to_term(),
            "checked_arrows": {
                "native_to_committed_fresh": self.commitment_receipt_id.to_term(),
                "committed_to_work_fresh": self.grinding_receipt_id.to_term(),
                "fresh_to_fiat_shamir": self.fiat_shamir_construction_id.to_term(),
            },
            "concrete_fiat_shamir_anchor": {
                "checked_execution_id": (
                    self.concrete_fiat_shamir_execution_id.to_term()
                ),
                "public_inputs_id": self.fiat_shamir_public_inputs_id.to_term(),
                "public_proof_id": self.fiat_shamir_public_proof_id.to_term(),
            },
            "exact_shared_subjects": {
                "native_core_id": self.native_core_id.to_term(),
                "committed_core_id": self.committed_core_id.to_term(),
                "work_augmented_core_id": self.work_augmented_core_id.to_term(),
                "fresh_protocol_id": self.fresh_protocol_id.to_term(),
                "fiat_shamir_protocol_id": self.fiat_shamir_protocol_id.to_term(),
            },
            "validation": {
                "law": COMPOSITION_VALIDATION_LAW,
                "basis_id": str(self.validation_basis_id),
                "source_manifest": [
                    source.to_term() for source in self.validation_source_manifest
                ],
                "selected_resource_limits": self.validation_limits.to_term(),
                "exact_resource_usage": self.resource_usage.to_term(),
            },
            "scope": "one-composed-concrete-execution-with-structural-and-concrete-fs-evidence",
            "nonclaims": list(_CONSTRUCTION_NONCLAIMS),
        }

    @property
    def identity(self) -> SemanticId:
        return semantic_id(
            "checked-construction-composition",
            "fri-ior.checked-construction-composition.v1",
            self.to_term(),
        )


@dataclass(frozen=True, slots=True)
class ConstructionCompositionAdmission:
    result: CheckResult
    checked_receipt: CheckedConstructionComposition | None


def compose_checked_constructions(
    commitment_receipt: object,
    grinding_receipt: object,
    fiat_shamir_construction: object,
    concrete_fiat_shamir_execution: object,
    limits: object = DEFAULT_VALIDATION_LIMITS,
) -> ConstructionCompositionAdmission:
    """Compose issued arrows with exact structural and concrete FS evidence."""

    if (
        type(commitment_receipt) is not CheckedNativeToCommittedFreshRun
        or type(grinding_receipt) is not CheckedCommittedToWorkFreshRun
        or type(fiat_shamir_construction) is not CheckedFiatShamirConstruction
        or type(concrete_fiat_shamir_execution) is not CheckedNativeToCommittedExecution
    ):
        return ConstructionCompositionAdmission(
            _malformed_result(
                "FRI-IOR-CONSTRUCTION-044",
                "composition requires all four exact checked carriers",
            ),
            None,
        )
    if type(limits) is not ResourceLimits:
        return ConstructionCompositionAdmission(
            _malformed_result(
                "FRI-IOR-CONSTRUCTION-052",
                "composition requires exact immutable validation limits",
            ),
            None,
        )
    if fiat_shamir_construction.identity != CHECKED_FIAT_SHAMIR_CONSTRUCTION.identity:
        return ConstructionCompositionAdmission(
            _refusal(
                "FRI-IOR-CONSTRUCTION-045",
                "composition requires the selected checked Fiat--Shamir construction",
            ),
            None,
        )
    if (
        commitment_receipt.candidate.declaration_id
        != COMMITMENT_COMPILATION_DECLARATION.identity
        or grinding_receipt.candidate.declaration_id
        != GRINDING_AUGMENTATION_DECLARATION.identity
        or fiat_shamir_construction.core_id
        != WORK_AUGMENTED_COMMITTED_FRI_CORE.identity
        or fiat_shamir_construction.source_protocol_id
        != FRESH_WORK_AUGMENTED_PROTOCOL.identity
        or fiat_shamir_construction.target_protocol_id
        != FIAT_SHAMIR_WORK_AUGMENTED_PROTOCOL.identity
    ):
        return ConstructionCompositionAdmission(
            _refusal(
                "FRI-IOR-CONSTRUCTION-046",
                "the checked arrows do not name the exact shared construction subjects",
            ),
            None,
        )
    concrete_candidate = concrete_fiat_shamir_execution.candidate
    if (
        concrete_candidate.commitment_compilation_declaration_id
        != COMMITMENT_COMPILATION_DECLARATION.identity
        or concrete_candidate.grinding_augmentation_declaration_id
        != GRINDING_AUGMENTATION_DECLARATION.identity
        or concrete_candidate.fiat_shamir_construction_declaration_id
        != fiat_shamir_construction.declaration_id
        or concrete_candidate.checked_fiat_shamir_construction_id
        != fiat_shamir_construction.identity
    ):
        return ConstructionCompositionAdmission(
            _refusal(
                "FRI-IOR-CONSTRUCTION-048",
                "the concrete Fiat--Shamir receipt names different construction subjects",
            ),
            None,
        )
    if (
        commitment_receipt.target_run.identity
        != grinding_receipt.candidate.source_run.identity
        or grinding_receipt.target_run.source_run.identity
        != commitment_receipt.target_run.identity
    ):
        return ConstructionCompositionAdmission(
            _refusal(
                "FRI-IOR-CONSTRUCTION-047",
                "the two concrete receipts do not share the same intermediate execution",
            ),
            None,
        )
    if (
        concrete_candidate.source_trace.identity
        != commitment_receipt.candidate.source_trace.identity
        or concrete_candidate.claimed_source_trace_id
        != commitment_receipt.candidate.source_trace.identity
    ):
        return ConstructionCompositionAdmission(
            _refusal(
                "FRI-IOR-CONSTRUCTION-049",
                "the concrete Fiat--Shamir receipt does not share the native source execution",
            ),
            None,
        )

    public_artifacts = concrete_fiat_shamir_execution.public_artifacts
    public_inputs = public_artifacts.public_inputs
    proof = public_artifacts.proof
    committed_run = commitment_receipt.target_run
    work_run = grinding_receipt.target_run
    if (
        public_inputs.statement != committed_run.statement
        or public_inputs.application_context != committed_run.application_context
        or proof.cap0 != committed_run.cap0
        or proof.cap1 != committed_run.cap1
        or proof.terminal_coefficients != committed_run.terminal_coefficients
        or proof.opening_table != committed_run.opening_table
        or proof.occurrence_selectors != committed_run.occurrence_selectors
        or proof.grinding_nonce != work_run.nonce
    ):
        return ConstructionCompositionAdmission(
            _refusal(
                "FRI-IOR-CONSTRUCTION-050",
                "the concrete Fiat--Shamir inputs and proof do not preserve the exact Fresh public-message view",
            ),
            None,
        )
    try:
        resources = ResourceCounter(limits)
        transcript = derive_fiat_shamir_transcript(
            public_inputs.transcript_plan,
            public_inputs.statement,
            public_inputs.application_context,
            proof.cap0,
            proof.cap1,
            proof.terminal_coefficients,
            proof.grinding_nonce,
            resources,
        )
        if isinstance(transcript, CheckResult):
            return ConstructionCompositionAdmission(transcript, None)
        if not isinstance(transcript, FiatShamirTranscript):
            raise RuntimeError("the one-shot transcript returned a wrong-kind value")
        resolved_draws = tuple(
            RandomQueryDraw(
                occurrence.ordinal,
                occurrence.initial_domain_index,
            )
            for occurrence in transcript.query_occurrences
        )
        if (
            transcript.beta0 != committed_run.beta0
            or transcript.beta1 != committed_run.beta1
            or resolved_draws != committed_run.query_draws
            or transcript.work_seed != work_run.work_seed
            or transcript.grinding_nonce != work_run.nonce
            or transcript.work_digest != work_run.work_digest
            or commitment_receipt.candidate.decision_map
            != DecisionMap("Accept", "Accept")
            or grinding_receipt.candidate.decision_map
            != DecisionMap("Accept", "Accept")
            or concrete_candidate.claimed_source_decision != "Accept"
            or concrete_candidate.claimed_target_decision != "Accept"
        ):
            return ConstructionCompositionAdmission(
                _refusal(
                    "FRI-IOR-CONSTRUCTION-051",
                    "the concrete Fiat--Shamir interpretation resolves different Core values or decision",
                ),
                None,
            )
        fs_verdict = verify_committed_fri(public_inputs, proof, resources)
        if fs_verdict.outcome is not OutcomeClass.AFFIRMATIVE:
            return ConstructionCompositionAdmission(fs_verdict, None)
    except ModelFailure as error:
        return ConstructionCompositionAdmission(error.to_result(), None)
    except Exception as error:  # pragma: no cover - fault-injection boundary
        return ConstructionCompositionAdmission(
            checker_failure(
                "constructions:composition",
                f"unexpected composition failure: {type(error).__name__}",
            ),
            None,
        )
    receipt = CheckedConstructionComposition(
        commitment_receipt,
        grinding_receipt,
        fiat_shamir_construction,
        concrete_fiat_shamir_execution,
        limits,
        ExactResourceUsage.from_counter(resources),
        _token=_COMPOSITION_TOKEN,
    )
    return ConstructionCompositionAdmission(
        affirmative(
            "constructions:composition",
            "FRI-IOR-CONSTRUCTION-104",
            "the checked concrete arrows and exact structural and concrete Fiat--Shamir evidence compose",
            subject=receipt.identity,
            scope="one-concrete-execution",
        ),
        receipt,
    )


__all__ = [
    "CheckedCommittedToWorkFreshRun",
    "CheckedConstructionComposition",
    "CheckedNativeToCommittedFreshRun",
    "CoinMapEntry",
    "CommitmentAdvice",
    "CommitmentCompilationAdmission",
    "CommittedFreshRun",
    "CommittedToWorkFreshCandidate",
    "ConstructionCompositionAdmission",
    "DecisionMap",
    "ExactResourceUsage",
    "ExtractedAnswerMapEntry",
    "FreshPublicEnvironment",
    "GrindingAugmentationAdmission",
    "InsertedWorkOccurrence",
    "NativeToCommittedFreshCandidate",
    "PreservedOccurrenceMapEntry",
    "PublicationMapEntry",
    "PublicEnvironmentMapEntry",
    "QueryOccurrenceMapEntry",
    "SeparatedResourceUsage",
    "TerminalMap",
    "WorkAugmentedFreshRun",
    "check_committed_to_work_fresh",
    "check_native_to_committed_fresh",
    "compose_checked_constructions",
    "generate_committed_to_work_fresh",
    "generate_native_to_committed_fresh",
    "verify_committed_fresh_run",
    "verify_work_augmented_fresh_run",
]
