"""Owner-local FRI generation and one checked concrete construction execution.

This module connects the finite native and committed models without changing
their authority boundaries.  Polynomial coefficients, commitment salts,
complete logical oracles, and commitment trees remain owner-local generation
material.  :class:`PublicFriArtifacts` is the only public projection, and it
contains exactly the raw public inputs and public proof accepted by the
committed verifier.

The checked receipt is deliberately an execution-level result.  It establishes
that one owner-local native trace, its two exact commitment trees, the inserted
work step, and the raw-input Fiat--Shamir replay commute on the four sampled
occurrences and reach the same decision.  It does not discharge the general
commitment-compilation or grinding declarations, prove a commitment security
property, prove FRI proximity, or transport a protocol theorem.

Generation uses the transcript module's evaluator-owned staged operations only
to respect the causal dependency of ``cap[1]`` on ``beta0`` and of terminal
material on ``beta1``.  No staged transcript crosses this module's boundary.
The completed target trace is always reconstructed through the authoritative
one-shot raw-input transcript API before a proof or checked receipt is issued.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from pathlib import Path
import stat
from typing import Any

from .commitment import CommitmentTree, build_commitment
from .committed import verify_committed_fri
from .field import Fp, Fp2, canonical_polynomial, evaluate_polynomial
from .native import (
    LayerQueryAnswerOccurrence,
    NativeFriTrace,
    derive_honest_native_trace,
    resolve_layer_query_answers,
    verify_native_trace,
)
from .profile import (
    D0,
    D1,
    D2,
    DEFAULT_VALIDATION_LIMITS,
    EXACT_PROFILE,
    admit_exact_profile,
)
from .proof import (
    CommittedFriPublicInputs,
    OccurrenceSelector,
    OpeningTableEntry,
    PublicFriProof,
)
from .provenance import (
    ValidationBasisId,
    artifact_content_id,
    validation_basis_id,
)
from .subjects import (
    CHECKED_FIAT_SHAMIR_CONSTRUCTION,
    COMMITMENT_COMPILATION_DECLARATION,
    FIAT_SHAMIR_CONSTRUCTION_DECLARATION,
    GRINDING_AUGMENTATION_DECLARATION,
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
    malformed,
    semantic_id,
)
from .transcript import (
    CANONICAL_CONSTRUCTION_PLAN,
    FiatShamirTranscript,
    _begin_transcript,
    _continue_transcript,
    construct_fiat_shamir_transcript,
    derive_fiat_shamir_transcript,
)


GENERATION_SCHEMA = "zkc.fri-ior.native-to-committed-generation.v1"
EXECUTION_SCHEMA = "zkc.fri-ior.checked-concrete-construction-execution.v1"
VALIDATION_LAW = "fri-ior.concrete-native-commit-grind-fs-commutation.v1"

_GENERATION_VALIDATION_SOURCES = (
    "commitment.py",
    "committed.py",
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

# This public material is shared with the existing committed-verifier vector.
PRIMARY_STATEMENT = {
    "schema": "zkc.fri-ior.statement.v1",
    "profile": "f97-binary-two-round",
    "initial_oracle_role": "relation-supplied",
}
PRIMARY_APPLICATION_CONTEXT = {
    "application": "native-fri-ior-validation",
    "case": "primary",
    "suffix": 71394,
}
PRIMARY_COEFFICIENTS = (3, 5, 7, 11, 13, 17, 19, 23)

# One coefficient fold performs one extension multiplication and addition per
# target coefficient, matching the native evaluator's abstract cost basis.
COEFFICIENT_FOLD_FIELD_OPERATIONS = 2


def _fp2(value: int) -> Fp2:
    return Fp2(Fp.reduce(value), Fp(0))


@dataclass(frozen=True, slots=True)
class PrivateFriGenerationMaterial:
    """Owner-local inputs with no term, serialization, or identity surface."""

    coefficients: tuple[Fp2, ...] = field(repr=False)
    initial_layer_salts: tuple[bytes, ...] = field(repr=False)
    first_fold_layer_salts: tuple[bytes, ...] = field(repr=False)

    def __post_init__(self) -> None:
        if type(self) is not PrivateFriGenerationMaterial:
            raise malformed(
                "generation:private-material-formation",
                "FRI-IOR-GENERATION-001",
                "private generation material requires the exact owner-local carrier",
            )
        canonical_polynomial(
            self.coefficients,
            EXACT_PROFILE.initial_degree_bound_exclusive,
        )
        expected_salt_counts = (
            (self.initial_layer_salts, D0.order // 2),
            (self.first_fold_layer_salts, D1.order // 2),
        )
        for salts, expected_count in expected_salt_counts:
            if (
                type(salts) is not tuple
                or len(salts) != expected_count
                or not all(type(salt) is bytes and len(salt) == 16 for salt in salts)
            ):
                raise malformed(
                    "generation:private-material-formation",
                    "FRI-IOR-GENERATION-002",
                    "each private commitment layer requires its exact sequence of sixteen-byte salts",
                )


def primary_private_generation_material() -> PrivateFriGenerationMaterial:
    """Return the deterministic, explicitly non-production private vector."""

    return PrivateFriGenerationMaterial(
        coefficients=tuple(_fp2(value) for value in PRIMARY_COEFFICIENTS),
        initial_layer_salts=tuple(
            bytes((0x10 + index,)) * 16 for index in range(D0.order // 2)
        ),
        first_fold_layer_salts=tuple(
            bytes((0x40 + index,)) * 16 for index in range(D1.order // 2)
        ),
    )


def primary_public_inputs() -> CommittedFriPublicInputs:
    """Return the primary raw public statement and application context."""

    return CommittedFriPublicInputs(
        EXACT_PROFILE,
        CANONICAL_CONSTRUCTION_PLAN,
        PRIMARY_STATEMENT,
        PRIMARY_APPLICATION_CONTEXT,
    )


@dataclass(frozen=True, slots=True)
class PublicFriArtifacts:
    """The complete public projection; no owner-local generation field exists."""

    public_inputs: CommittedFriPublicInputs
    proof: PublicFriProof

    def __post_init__(self) -> None:
        if type(self) is not PublicFriArtifacts:
            raise malformed(
                "generation:public-projection-formation",
                "FRI-IOR-GENERATION-003",
                "the public projection requires the exact closed carrier",
            )
        if not isinstance(self.public_inputs, CommittedFriPublicInputs):
            raise malformed(
                "generation:public-projection-formation",
                "FRI-IOR-GENERATION-004",
                "the public projection requires formed committed public inputs",
            )
        if not isinstance(self.proof, PublicFriProof):
            raise malformed(
                "generation:public-projection-formation",
                "FRI-IOR-GENERATION-005",
                "the public projection requires a formed public FRI proof",
            )

    def to_term(self) -> dict[str, Any]:
        return {
            "schema": "zkc.fri-ior.public-artifacts.v1",
            "public_inputs": self.public_inputs.to_term(),
            "proof": self.proof.to_term(),
        }

    @property
    def identity(self) -> SemanticId:
        return semantic_id(
            "committed-fri-public-artifacts",
            "fri-ior.public-artifacts.v1",
            self.to_term(),
        )


def _layer_query_identity(query: LayerQueryAnswerOccurrence) -> SemanticId:
    return semantic_id(
        "native-layer-query-answer-occurrence",
        "fri-ior.native-layer-query-answer-occurrence.v1",
        {
            "top_level_ordinal": query.top_level_ordinal,
            "layer": query.layer.value,
            "oracle_name": query.oracle_name,
            "pair_index": query.pair_index,
            "positive_answer_index": query.positive_answer_index,
            "negative_answer_index": query.negative_answer_index,
            "positive_value": query.positive_value.to_term(),
            "negative_value": query.negative_value.to_term(),
        },
    )


@dataclass(frozen=True, slots=True)
class CompiledOccurrenceMapEntry:
    """One order-preserving source-query to public-opening correspondence."""

    ordinal: int
    initial_domain_index: int
    initial_layer_table_index: int
    first_fold_layer_table_index: int
    source_initial_query_id: SemanticId
    target_initial_opening_id: SemanticId
    source_first_fold_query_id: SemanticId
    target_first_fold_opening_id: SemanticId

    def __post_init__(self) -> None:
        if type(self) is not CompiledOccurrenceMapEntry:
            raise malformed(
                "generation:occurrence-map-formation",
                "FRI-IOR-GENERATION-006",
                "an occurrence map requires the exact closed entry carrier",
            )
        for value in (
            self.ordinal,
            self.initial_domain_index,
            self.initial_layer_table_index,
            self.first_fold_layer_table_index,
        ):
            if type(value) is not int or value < 0:
                raise malformed(
                    "generation:occurrence-map-formation",
                    "FRI-IOR-GENERATION-007",
                    "occurrence-map coordinates must be non-negative integers",
                )
        for value in (
            self.source_initial_query_id,
            self.target_initial_opening_id,
            self.source_first_fold_query_id,
            self.target_first_fold_opening_id,
        ):
            if not isinstance(value, SemanticId):
                raise malformed(
                    "generation:occurrence-map-formation",
                    "FRI-IOR-GENERATION-008",
                    "occurrence-map endpoints require typed semantic identities",
                )

    def to_term(self) -> dict[str, Any]:
        return {
            "ordinal": self.ordinal,
            "initial_domain_index": self.initial_domain_index,
            "initial_layer_table_index": self.initial_layer_table_index,
            "first_fold_layer_table_index": self.first_fold_layer_table_index,
            "source_initial_query_id": self.source_initial_query_id.to_term(),
            "target_initial_opening_id": self.target_initial_opening_id.to_term(),
            "source_first_fold_query_id": self.source_first_fold_query_id.to_term(),
            "target_first_fold_opening_id": (
                self.target_first_fold_opening_id.to_term()
            ),
        }


@dataclass(frozen=True, slots=True)
class FrozenResourceSnapshot:
    """Immutable validation usage, separate from semantic execution identity."""

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
    def from_counter(cls, counter: ResourceCounter) -> FrozenResourceSnapshot:
        return cls(**counter.snapshot())

    def to_term(self) -> dict[str, int]:
        return {
            "field_operations": self.field_operations,
            "hash_calls": self.hash_calls,
            "hash_bytes": self.hash_bytes,
            "merkle_nodes": self.merkle_nodes,
            "transcript_frames": self.transcript_frames,
            "sampler_attempts": self.sampler_attempts,
            "grinding_trials": self.grinding_trials,
            "logical_query_occurrences": self.logical_query_occurrences,
            "unique_openings": self.unique_openings,
            "proof_bytes": self.proof_bytes,
        }


@dataclass(frozen=True, slots=True)
class ValidationSourceArtifact:
    """One exact evaluator source in a validation-basis manifest."""

    path: str
    artifact_content_id: str
    byte_length: int

    def __post_init__(self) -> None:
        if (
            type(self.path) is not str
            or self.path not in _GENERATION_VALIDATION_SOURCES
            or type(self.artifact_content_id) is not str
            or not self.artifact_content_id.startswith("sha256:")
            or type(self.byte_length) is not int
            or self.byte_length <= 0
        ):
            raise malformed(
                "generation:validation-source-formation",
                "FRI-IOR-GENERATION-038",
                "a validation source requires one exact path, digest, and positive byte length",
            )

    def to_term(self) -> dict[str, Any]:
        return {
            "path": self.path,
            "artifact_content_id": self.artifact_content_id,
            "byte_length": self.byte_length,
        }


def _generation_source_manifest() -> tuple[ValidationSourceArtifact, ...]:
    root = Path(__file__).resolve().parent
    manifest: list[ValidationSourceArtifact] = []
    for relative in _GENERATION_VALIDATION_SOURCES:
        path = root / relative
        metadata = path.lstat()
        if stat.S_ISLNK(metadata.st_mode) or not stat.S_ISREG(metadata.st_mode):
            raise ModelFailure(
                OutcomeClass.MISSING_DEPENDENCY,
                "generation:validation-source-load",
                "FRI-IOR-GENERATION-039",
                "a required evaluator source is not a regular non-symlink file",
            )
        raw = path.read_bytes()
        manifest.append(
            ValidationSourceArtifact(
                relative,
                str(artifact_content_id(raw)),
                len(raw),
            )
        )
    return tuple(manifest)


@dataclass(frozen=True, slots=True)
class NativeToCommittedExecutionCandidate:
    """Owner-local carrier submitted to the concrete correspondence checker.

    The two fields marked ``repr=False`` are never part of a public projection.
    Claimed identities are retained separately so replacing a carrier cannot
    silently reuse a prior validation result.
    """

    private_material: PrivateFriGenerationMaterial = field(repr=False)
    source_trace: NativeFriTrace = field(repr=False)
    public_artifacts: PublicFriArtifacts
    occurrence_map: tuple[CompiledOccurrenceMapEntry, ...]
    claimed_source_trace_id: SemanticId
    claimed_public_inputs_id: SemanticId
    claimed_proof_id: SemanticId
    claimed_target_trace_id: SemanticId
    claimed_source_decision: str
    claimed_target_decision: str
    commitment_compilation_declaration_id: SemanticId
    grinding_augmentation_declaration_id: SemanticId
    fiat_shamir_construction_declaration_id: SemanticId
    checked_fiat_shamir_construction_id: SemanticId

    def __post_init__(self) -> None:
        if type(self) is not NativeToCommittedExecutionCandidate:
            raise malformed(
                "generation:candidate-formation",
                "FRI-IOR-GENERATION-009",
                "concrete construction checking requires the exact candidate carrier",
            )
        if not isinstance(self.private_material, PrivateFriGenerationMaterial):
            raise malformed(
                "generation:candidate-formation",
                "FRI-IOR-GENERATION-010",
                "the owner-local candidate requires private generation material",
            )
        if not isinstance(self.source_trace, NativeFriTrace):
            raise malformed(
                "generation:candidate-formation",
                "FRI-IOR-GENERATION-011",
                "the owner-local candidate requires a native source trace",
            )
        if not isinstance(self.public_artifacts, PublicFriArtifacts):
            raise malformed(
                "generation:candidate-formation",
                "FRI-IOR-GENERATION-012",
                "the candidate requires one public-artifact projection",
            )
        if type(self.occurrence_map) is not tuple or not all(
            isinstance(entry, CompiledOccurrenceMapEntry)
            for entry in self.occurrence_map
        ):
            raise malformed(
                "generation:candidate-formation",
                "FRI-IOR-GENERATION-013",
                "the candidate requires a typed occurrence-map sequence",
            )
        for value in (
            self.claimed_source_trace_id,
            self.claimed_public_inputs_id,
            self.claimed_proof_id,
            self.claimed_target_trace_id,
            self.commitment_compilation_declaration_id,
            self.grinding_augmentation_declaration_id,
            self.fiat_shamir_construction_declaration_id,
            self.checked_fiat_shamir_construction_id,
        ):
            if not isinstance(value, SemanticId):
                raise malformed(
                    "generation:candidate-formation",
                    "FRI-IOR-GENERATION-014",
                    "candidate bindings require typed semantic identities",
                )
        if self.claimed_source_decision not in ("Accept", "Reject") or (
            self.claimed_target_decision not in ("Accept", "Reject")
        ):
            raise malformed(
                "generation:candidate-formation",
                "FRI-IOR-GENERATION-015",
                "candidate decisions must be exact terminal values",
            )

    def semantic_term(self) -> dict[str, Any]:
        """Return the private-data-free semantic correspondence claim."""

        return {
            "schema": GENERATION_SCHEMA,
            "source_native_trace_id": self.claimed_source_trace_id.to_term(),
            "target_public_inputs_id": self.claimed_public_inputs_id.to_term(),
            "target_public_proof_id": self.claimed_proof_id.to_term(),
            "target_committed_trace_id": self.claimed_target_trace_id.to_term(),
            "construction_subjects": {
                "commitment_compilation_declaration_id": (
                    self.commitment_compilation_declaration_id.to_term()
                ),
                "grinding_augmentation_declaration_id": (
                    self.grinding_augmentation_declaration_id.to_term()
                ),
                "fiat_shamir_construction_declaration_id": (
                    self.fiat_shamir_construction_declaration_id.to_term()
                ),
                "checked_fiat_shamir_construction_id": (
                    self.checked_fiat_shamir_construction_id.to_term()
                ),
            },
            "occurrence_map": [entry.to_term() for entry in self.occurrence_map],
            "commutation": {
                "complete_oracles_commit_to_target_caps": True,
                "sampled_source_pairs_equal_authenticated_target_pairs": True,
                "fold_challenges_terminal_and_query_occurrences_equal": True,
            },
            "decision_map": {
                "source": self.claimed_source_decision,
                "target": self.claimed_target_decision,
                "equal": self.claimed_source_decision == self.claimed_target_decision,
            },
            "scope": "one-concrete-generated-execution",
            "nonclaims": [
                "general-commitment-compilation-correctness",
                "general-grinding-augmentation-correctness",
                "commitment-binding-hiding-or-extractability",
                "proximity-soundness-or-completeness",
                "random-oracle-security",
                "protocol-property-transport",
                "outer-computation-relation",
            ],
        }

    @property
    def semantic_execution_id(self) -> SemanticId:
        return semantic_id(
            "concrete-native-to-committed-execution",
            "fri-ior.concrete-construction-execution.v1",
            self.semantic_term(),
        )


_CHECKED_EXECUTION_TOKEN = object()


@dataclass(frozen=True, slots=True, init=False)
class CheckedNativeToCommittedExecution:
    """One issued receipt; validation resources are not protocol semantics."""

    candidate: NativeToCommittedExecutionCandidate
    semantic_execution_id: SemanticId
    validation_basis_id: ValidationBasisId
    validation_source_manifest: tuple[ValidationSourceArtifact, ...]
    validation_limits: ResourceLimits
    resource_snapshot: FrozenResourceSnapshot

    def __init__(
        self,
        candidate: NativeToCommittedExecutionCandidate,
        validation_limits: ResourceLimits,
        resource_snapshot: FrozenResourceSnapshot,
        *,
        _token: object,
    ) -> None:
        if _token is not _CHECKED_EXECUTION_TOKEN:
            raise ModelFailure(
                OutcomeClass.MISSING_DEPENDENCY,
                "generation:checked-execution-formation",
                "FRI-IOR-GENERATION-016",
                "a checked execution requires the concrete correspondence checker",
            )
        semantic_execution_id = candidate.semantic_execution_id
        validation_source_manifest = _generation_source_manifest()
        validation_basis = validation_basis_id(
            "construction-checker",
            {
                "law": VALIDATION_LAW,
                "selected_resource_limits": validation_limits.to_term(),
                "sources": [source.to_term() for source in validation_source_manifest],
            },
        )
        object.__setattr__(self, "candidate", candidate)
        object.__setattr__(self, "semantic_execution_id", semantic_execution_id)
        object.__setattr__(self, "validation_basis_id", validation_basis)
        object.__setattr__(
            self,
            "validation_source_manifest",
            validation_source_manifest,
        )
        object.__setattr__(self, "validation_limits", validation_limits)
        object.__setattr__(self, "resource_snapshot", resource_snapshot)

    @property
    def public_artifacts(self) -> PublicFriArtifacts:
        return self.candidate.public_artifacts

    def to_term(self) -> dict[str, Any]:
        """Return a receipt with references only, never owner-local values."""

        return {
            "schema": EXECUTION_SCHEMA,
            "semantic_execution_id": self.semantic_execution_id.to_term(),
            "semantic_execution": self.candidate.semantic_term(),
            "validation": {
                "law": VALIDATION_LAW,
                "basis_id": str(self.validation_basis_id),
                "source_manifest": [
                    source.to_term() for source in self.validation_source_manifest
                ],
                "selected_resource_limits": self.validation_limits.to_term(),
                "resource_snapshot": self.resource_snapshot.to_term(),
            },
        }

    @property
    def identity(self) -> SemanticId:
        return semantic_id(
            "checked-concrete-construction-execution",
            "fri-ior.checked-concrete-construction-execution.v1",
            self.to_term(),
        )


@dataclass(frozen=True, slots=True)
class CompilationExecutionAdmission:
    """Typed result plus a checked receipt only on affirmation."""

    result: CheckResult
    checked_execution: CheckedNativeToCommittedExecution | None

    def __post_init__(self) -> None:
        if not isinstance(self.result, CheckResult):
            raise TypeError("execution admission requires a CheckResult")
        if self.result.outcome is OutcomeClass.AFFIRMATIVE:
            if not isinstance(
                self.checked_execution,
                CheckedNativeToCommittedExecution,
            ):
                raise TypeError("affirmative admission requires a checked execution")
        elif self.checked_execution is not None:
            raise TypeError(
                "non-affirmative admission cannot carry a checked execution"
            )


def _failed(result: CheckResult) -> CompilationExecutionAdmission:
    return CompilationExecutionAdmission(result, None)


def _typed_failure(error: ModelFailure) -> CompilationExecutionAdmission:
    return _failed(error.to_result())


def _fold_coefficients(
    coefficients: tuple[Fp2, ...],
    challenge: Fp2,
    target_count: int,
    resources: ResourceCounter,
) -> tuple[Fp2, ...]:
    padded = list(coefficients) + [Fp2.zero()] * (2 * target_count - len(coefficients))
    resources.consume_field_operations(target_count * COEFFICIENT_FOLD_FIELD_OPERATIONS)
    folded = tuple(
        padded[2 * index] + challenge * padded[2 * index + 1]
        for index in range(target_count)
    )
    end = len(folded)
    while end > 1 and folded[end - 1] == Fp2.zero():
        end -= 1
    return folded[:end]


def _target_trace_identity(transcript: FiatShamirTranscript) -> SemanticId:
    return semantic_id(
        "work-augmented-committed-fri-trace",
        "fri-ior.work-augmented-committed-trace.v1",
        {
            "transcript_plan_id": transcript.plan.identity.to_term(),
            "beta0": transcript.beta0.to_term(),
            "beta1": transcript.beta1.to_term(),
            "terminal_coefficients": [
                coefficient.to_term()
                for coefficient in transcript.terminal_coefficients
            ],
            "work_seed": transcript.work_seed.hex(),
            "grinding_nonce": transcript.grinding_nonce,
            "work_digest": transcript.work_digest.hex(),
            "query_seed": transcript.query_seed.hex(),
            "ordered_query_occurrences": [
                occurrence.to_term() for occurrence in transcript.query_occurrences
            ],
        },
    )


def _proof_from_trees(
    tree0: CommitmentTree,
    tree1: CommitmentTree,
    transcript: FiatShamirTranscript,
) -> PublicFriProof:
    keys = tuple(
        sorted(
            {
                key
                for occurrence in transcript.query_occurrences
                for key in (
                    (0, occurrence.initial_domain_index % (D0.order // 2)),
                    (1, occurrence.initial_domain_index % (D1.order // 2)),
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
            occurrence.ordinal,
            table_index[(0, occurrence.initial_domain_index % (D0.order // 2))],
            table_index[(1, occurrence.initial_domain_index % (D1.order // 2))],
        )
        for occurrence in transcript.query_occurrences
    )
    return PublicFriProof(
        tree0.cap,
        tree1.cap,
        transcript.terminal_coefficients,
        transcript.grinding_nonce,
        opening_table,
        selectors,
    )


def _occurrence_map(
    source_queries: tuple[LayerQueryAnswerOccurrence, ...],
    proof: PublicFriProof,
    transcript: FiatShamirTranscript,
) -> tuple[CompiledOccurrenceMapEntry, ...] | CheckResult:
    boundary = "generation:occurrence-commutation"
    if len(source_queries) != 2 * len(transcript.query_occurrences):
        return CheckResult(
            OutcomeClass.REFUSED,
            boundary,
            "FRI-IOR-GENERATION-030",
            "source layer-query expansion has the wrong occurrence count",
        )
    entries: list[CompiledOccurrenceMapEntry] = []
    for occurrence, source_initial, source_first, selector in zip(
        transcript.query_occurrences,
        source_queries[::2],
        source_queries[1::2],
        proof.occurrence_selectors,
        strict=True,
    ):
        if (
            selector.ordinal != occurrence.ordinal
            or selector.layer0_opening_index >= len(proof.opening_table)
            or selector.layer1_opening_index >= len(proof.opening_table)
        ):
            return CheckResult(
                OutcomeClass.REFUSED,
                boundary,
                "FRI-IOR-GENERATION-031",
                "the target selector cannot realize its source occurrence",
            )
        target_initial = proof.opening_table[selector.layer0_opening_index].opening
        target_first = proof.opening_table[selector.layer1_opening_index].opening
        if (
            source_initial.pair_index != target_initial.pair_index
            or source_initial.positive_value != target_initial.positive
            or source_initial.negative_value != target_initial.negative
            or source_first.pair_index != target_first.pair_index
            or source_first.positive_value != target_first.positive
            or source_first.negative_value != target_first.negative
        ):
            return CheckResult(
                OutcomeClass.REFUSED,
                boundary,
                "FRI-IOR-GENERATION-032",
                "a sampled source answer pair differs from its authenticated target opening",
            )
        entries.append(
            CompiledOccurrenceMapEntry(
                occurrence.ordinal,
                occurrence.initial_domain_index,
                selector.layer0_opening_index,
                selector.layer1_opening_index,
                _layer_query_identity(source_initial),
                target_initial.identity,
                _layer_query_identity(source_first),
                target_first.identity,
            )
        )
    return tuple(entries)


def _exact_declaration_ids(
    candidate: NativeToCommittedExecutionCandidate,
) -> bool:
    return (
        candidate.commitment_compilation_declaration_id
        == COMMITMENT_COMPILATION_DECLARATION.identity
        and candidate.grinding_augmentation_declaration_id
        == GRINDING_AUGMENTATION_DECLARATION.identity
        and candidate.fiat_shamir_construction_declaration_id
        == FIAT_SHAMIR_CONSTRUCTION_DECLARATION.identity
        and candidate.checked_fiat_shamir_construction_id
        == CHECKED_FIAT_SHAMIR_CONSTRUCTION.identity
    )


def check_native_to_committed_execution(
    candidate: object,
    limits: object = DEFAULT_VALIDATION_LIMITS,
) -> CompilationExecutionAdmission:
    """Check one private/public construction correspondence under fresh meters."""

    boundary = "generation:concrete-construction-check"
    if not isinstance(candidate, NativeToCommittedExecutionCandidate):
        return _failed(
            CheckResult(
                OutcomeClass.MALFORMED,
                boundary,
                "FRI-IOR-GENERATION-017",
                "concrete construction checking requires a formed candidate",
            )
        )
    if type(limits) is not ResourceLimits:
        return _failed(
            CheckResult(
                OutcomeClass.MALFORMED,
                boundary,
                "FRI-IOR-GENERATION-018",
                "the authoritative checker requires exact immutable resource limits",
            )
        )

    try:
        resources = ResourceCounter(limits)
        public_inputs = candidate.public_artifacts.public_inputs
        proof = candidate.public_artifacts.proof

        if candidate.source_trace.profile.identity != public_inputs.profile.identity:
            return _failed(
                CheckResult(
                    OutcomeClass.KIND_MISMATCH,
                    boundary,
                    "FRI-IOR-GENERATION-019",
                    "source and target traces name different FRI profiles",
                )
            )
        profile_result = admit_exact_profile(public_inputs.profile)
        if profile_result.outcome is not OutcomeClass.AFFIRMATIVE:
            return _failed(profile_result)
        if (
            public_inputs.transcript_plan.identity
            != CANONICAL_CONSTRUCTION_PLAN.identity
        ):
            return _failed(
                CheckResult(
                    OutcomeClass.UNSUPPORTED,
                    boundary,
                    "FRI-IOR-GENERATION-020",
                    "the target names an unsupported transcript construction plan",
                )
            )
        if candidate.claimed_source_trace_id != candidate.source_trace.identity:
            return _failed(
                CheckResult(
                    OutcomeClass.REFUSED,
                    boundary,
                    "FRI-IOR-GENERATION-021",
                    "the recorded source-trace validation binding is stale",
                )
            )
        if candidate.claimed_public_inputs_id != public_inputs.identity:
            return _failed(
                CheckResult(
                    OutcomeClass.REFUSED,
                    boundary,
                    "FRI-IOR-GENERATION-022",
                    "the recorded target-input validation binding is stale",
                )
            )
        if candidate.claimed_proof_id != proof.identity:
            return _failed(
                CheckResult(
                    OutcomeClass.REFUSED,
                    boundary,
                    "FRI-IOR-GENERATION-023",
                    "the recorded target-proof validation binding is stale",
                )
            )
        if not _exact_declaration_ids(candidate):
            return _failed(
                CheckResult(
                    OutcomeClass.KIND_MISMATCH,
                    boundary,
                    "FRI-IOR-GENERATION-024",
                    "the candidate names a different construction declaration or checked Fiat--Shamir subject",
                )
            )

        target_transcript = derive_fiat_shamir_transcript(
            public_inputs.transcript_plan,
            public_inputs.statement,
            public_inputs.application_context,
            proof.cap0,
            proof.cap1,
            proof.terminal_coefficients,
            proof.grinding_nonce,
            resources,
        )
        if isinstance(target_transcript, CheckResult):
            return _failed(target_transcript)
        target_trace_id = _target_trace_identity(target_transcript)
        if candidate.claimed_target_trace_id != target_trace_id:
            return _failed(
                CheckResult(
                    OutcomeClass.REFUSED,
                    boundary,
                    "FRI-IOR-GENERATION-025",
                    "the recorded committed-trace validation binding is stale",
                )
            )

        query_indices = tuple(
            occurrence.initial_domain_index
            for occurrence in target_transcript.query_occurrences
        )
        expected_source = derive_honest_native_trace(
            candidate.private_material.coefficients,
            target_transcript.beta0,
            target_transcript.beta1,
            query_indices,
            resources,
        )
        if expected_source.identity != candidate.source_trace.identity:
            return _failed(
                CheckResult(
                    OutcomeClass.REFUSED,
                    boundary,
                    "FRI-IOR-GENERATION-026",
                    "the source trace is not the honest trace derived from the owner-local material and target coins",
                )
            )

        initial_values = tuple(
            entry.value for entry in candidate.source_trace.initial_oracle.entries
        )
        first_fold_values = tuple(
            entry.value for entry in candidate.source_trace.prover_oracle.entries
        )
        expected_tree0 = build_commitment(
            D0,
            initial_values,
            candidate.private_material.initial_layer_salts,
            resources,
        )
        expected_tree1 = build_commitment(
            D1,
            first_fold_values,
            candidate.private_material.first_fold_layer_salts,
            resources,
        )
        if expected_tree0.cap != proof.cap0 or expected_tree1.cap != proof.cap1:
            return _failed(
                CheckResult(
                    OutcomeClass.REFUSED,
                    boundary,
                    "FRI-IOR-GENERATION-027",
                    "the complete source oracles do not commit to the target caps",
                )
            )

        if (
            candidate.source_trace.beta0 != target_transcript.beta0
            or candidate.source_trace.beta1 != target_transcript.beta1
            or candidate.source_trace.terminal.coefficients
            != target_transcript.terminal_coefficients
            or tuple(
                draw.initial_domain_index for draw in candidate.source_trace.query_draws
            )
            != query_indices
        ):
            return _failed(
                CheckResult(
                    OutcomeClass.REFUSED,
                    boundary,
                    "FRI-IOR-GENERATION-028",
                    "fold challenges, terminal material, or query occurrences do not commute",
                )
            )

        source_result = verify_native_trace(candidate.source_trace, resources)
        target_result = verify_committed_fri(public_inputs, proof, resources)
        source_decision = (
            "Accept" if source_result.outcome is OutcomeClass.AFFIRMATIVE else "Reject"
        )
        target_decision = (
            "Accept" if target_result.outcome is OutcomeClass.AFFIRMATIVE else "Reject"
        )
        if (
            candidate.claimed_source_decision != source_decision
            or candidate.claimed_target_decision != target_decision
        ):
            return _failed(
                CheckResult(
                    OutcomeClass.REFUSED,
                    boundary,
                    "FRI-IOR-GENERATION-029",
                    "a recorded source or target decision is stale",
                )
            )
        if source_result.outcome is not OutcomeClass.AFFIRMATIVE:
            return _failed(source_result)
        if target_result.outcome is not OutcomeClass.AFFIRMATIVE:
            return _failed(target_result)
        if source_decision != target_decision:
            return _failed(
                CheckResult(
                    OutcomeClass.REFUSED,
                    boundary,
                    "FRI-IOR-GENERATION-033",
                    "the source and target decisions differ",
                )
            )

        source_queries = resolve_layer_query_answers(
            candidate.source_trace,
            resources,
        )
        if isinstance(source_queries, CheckResult):
            return _failed(source_queries)
        expected_map = _occurrence_map(source_queries, proof, target_transcript)
        if isinstance(expected_map, CheckResult):
            return _failed(expected_map)
        if candidate.occurrence_map != expected_map:
            return _failed(
                CheckResult(
                    OutcomeClass.REFUSED,
                    boundary,
                    "FRI-IOR-GENERATION-034",
                    "the declared occurrence map is not the exact checked correspondence",
                )
            )

        snapshot = FrozenResourceSnapshot.from_counter(resources)
        checked = CheckedNativeToCommittedExecution(
            candidate,
            limits,
            snapshot,
            _token=_CHECKED_EXECUTION_TOKEN,
        )
        return CompilationExecutionAdmission(
            affirmative(
                boundary,
                "FRI-IOR-GENERATION-100",
                "one native-to-committed, grinding, and Fiat--Shamir execution commutes and accepts",
                subject=checked.identity,
                semantic_execution_id=checked.semantic_execution_id,
                validation_basis_id=str(checked.validation_basis_id),
                source_trace_id=candidate.claimed_source_trace_id,
                target_trace_id=candidate.claimed_target_trace_id,
                target_proof_id=candidate.claimed_proof_id,
                mapped_top_level_occurrences=len(expected_map),
                source_decision=source_decision,
                target_decision=target_decision,
                decisions_equal=True,
                complete_commitment_caps_equal=True,
                sampled_answer_pairs_equal=True,
                challenge_and_query_trace_equal=True,
                resource_snapshot=snapshot.to_term(),
                establishes_general_compiler_correctness=False,
                establishes_commitment_security=False,
                establishes_proximity_theorem=False,
                establishes_protocol_security=False,
            ),
            checked,
        )
    except ModelFailure as error:
        return _typed_failure(error)
    except Exception as error:  # pragma: no cover - fault-injection boundary
        return _failed(
            checker_failure(
                boundary,
                f"unexpected concrete-construction failure: {type(error).__name__}",
            )
        )


def _initial_occurrence_map(
    source_trace: NativeFriTrace,
    proof: PublicFriProof,
    transcript: FiatShamirTranscript,
    resources: ResourceCounter,
) -> tuple[CompiledOccurrenceMapEntry, ...] | CheckResult:
    source_queries = resolve_layer_query_answers(source_trace, resources)
    if isinstance(source_queries, CheckResult):
        return source_queries
    return _occurrence_map(source_queries, proof, transcript)


def generate_honest_native_to_committed_execution(
    private_material: object,
    public_inputs: object,
    limits: object = DEFAULT_VALIDATION_LIMITS,
) -> CompilationExecutionAdmission:
    """Generate public artifacts and issue one checked concrete receipt.

    The function creates every mutable resource counter privately.  Its return
    value may contain owner-local audit material, but callers must use
    ``checked_execution.public_artifacts`` as the public verifier input.
    """

    boundary = "generation:honest-construction"
    if not isinstance(private_material, PrivateFriGenerationMaterial):
        return _failed(
            CheckResult(
                OutcomeClass.MALFORMED,
                boundary,
                "FRI-IOR-GENERATION-035",
                "honest generation requires owner-local private material",
            )
        )
    if not isinstance(public_inputs, CommittedFriPublicInputs):
        return _failed(
            CheckResult(
                OutcomeClass.MALFORMED,
                boundary,
                "FRI-IOR-GENERATION-036",
                "honest generation requires formed raw committed public inputs",
            )
        )
    if type(limits) is not ResourceLimits:
        return _failed(
            CheckResult(
                OutcomeClass.MALFORMED,
                boundary,
                "FRI-IOR-GENERATION-037",
                "honest generation requires exact immutable resource limits",
            )
        )

    try:
        profile_result = admit_exact_profile(public_inputs.profile)
        if profile_result.outcome is not OutcomeClass.AFFIRMATIVE:
            return _failed(profile_result)
        if (
            public_inputs.transcript_plan.identity
            != CANONICAL_CONSTRUCTION_PLAN.identity
        ):
            return _failed(
                CheckResult(
                    OutcomeClass.UNSUPPORTED,
                    boundary,
                    "FRI-IOR-GENERATION-038",
                    "honest generation supports only the exact transcript construction plan",
                )
            )
        resources = ResourceCounter(limits)
        coefficients = canonical_polynomial(
            private_material.coefficients,
            EXACT_PROFILE.initial_degree_bound_exclusive,
        )
        initial_values = tuple(
            evaluate_polynomial(coefficients, point, resources) for point in D0.points()
        )
        tree0 = build_commitment(
            D0,
            initial_values,
            private_material.initial_layer_salts,
            resources,
        )

        # These evaluator-owned staged values never escape.  They are required
        # by the causal prover schedule, while final authority comes from the
        # one-shot raw-input reconstruction below.
        first_round = _begin_transcript(
            public_inputs.transcript_plan,
            public_inputs.statement,
            public_inputs.application_context,
            tree0.cap,
            resources,
        )
        if isinstance(first_round, CheckResult):
            return _failed(first_round)
        first_fold_coefficients = _fold_coefficients(
            coefficients,
            first_round.beta0,
            D1.order // 2,
            resources,
        )
        first_fold_values = tuple(
            evaluate_polynomial(first_fold_coefficients, point, resources)
            for point in D1.points()
        )
        tree1 = build_commitment(
            D1,
            first_fold_values,
            private_material.first_fold_layer_salts,
            resources,
        )
        second_round = _continue_transcript(first_round, tree1.cap, resources)
        if isinstance(second_round, CheckResult):
            return _failed(second_round)
        terminal_coefficients = _fold_coefficients(
            first_fold_coefficients,
            second_round.beta1,
            D2.order // 2,
            resources,
        )

        transcript = construct_fiat_shamir_transcript(
            public_inputs.transcript_plan,
            public_inputs.statement,
            public_inputs.application_context,
            tree0.cap,
            tree1.cap,
            terminal_coefficients,
            resources,
        )
        if isinstance(transcript, CheckResult):
            return _failed(transcript)
        if (
            transcript.beta0 != first_round.beta0
            or transcript.beta1 != second_round.beta1
        ):
            return _failed(
                checker_failure(
                    boundary,
                    "the staged prover schedule disagrees with raw-input transcript replay",
                )
            )

        query_indices = tuple(
            occurrence.initial_domain_index
            for occurrence in transcript.query_occurrences
        )
        source_trace = derive_honest_native_trace(
            coefficients,
            transcript.beta0,
            transcript.beta1,
            query_indices,
            resources,
        )
        proof = _proof_from_trees(tree0, tree1, transcript)
        public_artifacts = PublicFriArtifacts(public_inputs, proof)
        occurrence_map = _initial_occurrence_map(
            source_trace,
            proof,
            transcript,
            resources,
        )
        if isinstance(occurrence_map, CheckResult):
            return _failed(occurrence_map)

        candidate = NativeToCommittedExecutionCandidate(
            private_material=private_material,
            source_trace=source_trace,
            public_artifacts=public_artifacts,
            occurrence_map=occurrence_map,
            claimed_source_trace_id=source_trace.identity,
            claimed_public_inputs_id=public_inputs.identity,
            claimed_proof_id=proof.identity,
            claimed_target_trace_id=_target_trace_identity(transcript),
            claimed_source_decision="Accept",
            claimed_target_decision="Accept",
            commitment_compilation_declaration_id=(
                COMMITMENT_COMPILATION_DECLARATION.identity
            ),
            grinding_augmentation_declaration_id=(
                GRINDING_AUGMENTATION_DECLARATION.identity
            ),
            fiat_shamir_construction_declaration_id=(
                FIAT_SHAMIR_CONSTRUCTION_DECLARATION.identity
            ),
            checked_fiat_shamir_construction_id=(
                CHECKED_FIAT_SHAMIR_CONSTRUCTION.identity
            ),
        )
        return check_native_to_committed_execution(candidate, limits)
    except ModelFailure as error:
        return _typed_failure(error)
    except Exception as error:  # pragma: no cover - fault-injection boundary
        return _failed(
            checker_failure(
                boundary,
                f"unexpected honest-generation failure: {type(error).__name__}",
            )
        )


__all__ = [
    "CheckedNativeToCommittedExecution",
    "CompilationExecutionAdmission",
    "CompiledOccurrenceMapEntry",
    "FrozenResourceSnapshot",
    "NativeToCommittedExecutionCandidate",
    "PRIMARY_APPLICATION_CONTEXT",
    "PRIMARY_COEFFICIENTS",
    "PRIMARY_STATEMENT",
    "PrivateFriGenerationMaterial",
    "PublicFriArtifacts",
    "ValidationSourceArtifact",
    "check_native_to_committed_execution",
    "generate_honest_native_to_committed_execution",
    "primary_private_generation_material",
    "primary_public_inputs",
]
