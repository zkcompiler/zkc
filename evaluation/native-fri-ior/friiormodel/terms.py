"""Canonical finite terms, typed outcomes, and bounded resource accounting.

This package is a deliberately small executable pressure case.  Its public
functions never use an exception's prose as the classification surface:
``OutcomeClass`` and the diagnostic code are stable, while ``detail`` remains
explanatory text.  The full operational partition keeps unsupported features,
missing dependencies, kind mismatches, malformed inputs, closed-law refusals,
deterministic limit exhaustion, and checker bugs distinct.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum
import hashlib
from types import MappingProxyType
from typing import Any, Mapping


MAX_TERM_BYTES = 1 << 16
MAX_TERM_NODES = 2048
MAX_TERM_DEPTH = 24


class OutcomeClass(str, Enum):
    """The outcome classes exposed by the finite evaluator."""

    AFFIRMATIVE = "Affirmative"
    UNSUPPORTED = "Unsupported"
    MISSING_DEPENDENCY = "MissingDependency"
    KIND_MISMATCH = "KindMismatch"
    MALFORMED = "Malformed"
    REFUSED = "Refused"
    DETERMINISTIC_LIMIT_EXCEEDED = "DeterministicLimitExceeded"
    CHECKER_FAILURE = "CheckerFailure"


class ModelFailure(Exception):
    """An expected typed failure at a named evaluator boundary."""

    def __init__(
        self,
        outcome: OutcomeClass,
        boundary: str,
        code: str,
        detail: str,
    ) -> None:
        if outcome is OutcomeClass.AFFIRMATIVE:
            raise ValueError("ModelFailure cannot carry an affirmative outcome")
        super().__init__(f"{code}: {detail}")
        self.outcome = outcome
        self.boundary = boundary
        self.code = code
        self.detail = detail

    def to_result(self) -> CheckResult:
        return CheckResult(
            outcome=self.outcome,
            boundary=self.boundary,
            code=self.code,
            detail=self.detail,
        )


_IDENTIFIER_CHARACTERS = frozenset(
    "abcdefghijklmnopqrstuvwxyz0123456789.-_"
)


def _validate_identifier(value: object, field_name: str, code: str) -> str:
    if (
        not isinstance(value, str)
        or not 1 <= len(value) <= 192
        or value[0] not in "abcdefghijklmnopqrstuvwxyz"
        or any(character not in _IDENTIFIER_CHARACTERS for character in value)
    ):
        raise ModelFailure(
            OutcomeClass.MALFORMED,
            "identity:formation",
            code,
            (
                f"{field_name} must be 1..192 lower-case ASCII identifier "
                "characters and begin with a letter"
            ),
        )
    return value


@dataclass(frozen=True, slots=True)
class SemanticId:
    """A typed semantic identity, not a digest-shaped ambient string."""

    subject_kind: str
    domain: str
    semantic_regime: str
    digest: bytes

    def __post_init__(self) -> None:
        _validate_identifier(
            self.subject_kind,
            "subject_kind",
            "FRI-IOR-IDENTITY-001",
        )
        _validate_identifier(self.domain, "domain", "FRI-IOR-IDENTITY-002")
        _validate_identifier(
            self.semantic_regime,
            "semantic_regime",
            "FRI-IOR-IDENTITY-003",
        )
        if not isinstance(self.digest, bytes) or len(self.digest) != 32:
            raise ModelFailure(
                OutcomeClass.MALFORMED,
                "identity:formation",
                "FRI-IOR-IDENTITY-004",
                "a semantic identity digest must contain exactly 32 bytes",
            )

    def to_term(self) -> dict[str, Any]:
        return {
            "kind": "SemanticId",
            "version": 1,
            "subject_kind": self.subject_kind,
            "domain": self.domain,
            "semantic_regime": self.semantic_regime,
            "digest": self.digest.hex(),
        }

    def to_text(self) -> str:
        """Render the fields without dropping kind or regime information."""

        return "/".join(
            (
                "semantic-id-v1",
                self.subject_kind,
                self.domain,
                self.semantic_regime,
                self.digest.hex(),
            )
        )

    def __str__(self) -> str:
        return self.to_text()


def _evidence_term(value: Any) -> Any:
    if isinstance(value, SemanticId):
        return value.to_term()
    if isinstance(value, Mapping):
        return {key: _evidence_term(item) for key, item in value.items()}
    if isinstance(value, (tuple, list)):
        return [_evidence_term(item) for item in value]
    return value


@dataclass(frozen=True)
class CheckResult:
    """A stable classification plus non-authoritative explanatory evidence."""

    outcome: OutcomeClass
    boundary: str
    code: str
    detail: str
    subject: SemanticId | None = None
    evidence: Mapping[str, Any] = field(default_factory=dict)

    def __post_init__(self) -> None:
        if self.subject is not None and not isinstance(self.subject, SemanticId):
            raise ModelFailure(
                OutcomeClass.MALFORMED,
                "result:formation",
                "FRI-IOR-IDENTITY-011",
                "a result subject must be a typed SemanticId or absent",
            )

    def to_term(self) -> dict[str, Any]:
        return {
            "outcome": self.outcome.value,
            "boundary": self.boundary,
            "code": self.code,
            "detail": self.detail,
            "subject": None if self.subject is None else self.subject.to_term(),
            "evidence": _evidence_term(self.evidence),
        }


def affirmative(
    boundary: str,
    code: str,
    detail: str,
    *,
    subject: SemanticId | None = None,
    **evidence: Any,
) -> CheckResult:
    return CheckResult(
        outcome=OutcomeClass.AFFIRMATIVE,
        boundary=boundary,
        code=code,
        detail=detail,
        subject=subject,
        evidence=evidence,
    )


def refused(boundary: str, code: str, detail: str) -> CheckResult:
    return CheckResult(OutcomeClass.REFUSED, boundary, code, detail)


def unsupported(boundary: str, code: str, detail: str) -> CheckResult:
    return CheckResult(OutcomeClass.UNSUPPORTED, boundary, code, detail)


def missing_dependency(boundary: str, code: str, detail: str) -> CheckResult:
    return CheckResult(OutcomeClass.MISSING_DEPENDENCY, boundary, code, detail)


def kind_mismatch(boundary: str, code: str, detail: str) -> CheckResult:
    return CheckResult(OutcomeClass.KIND_MISMATCH, boundary, code, detail)


def checker_failure(boundary: str, detail: str) -> CheckResult:
    """Classify an unexpected implementation fault without accepting input."""

    return CheckResult(
        OutcomeClass.CHECKER_FAILURE,
        boundary,
        "FRI-IOR-CHECKER-001",
        detail,
    )


def malformed(boundary: str, code: str, detail: str) -> ModelFailure:
    return ModelFailure(OutcomeClass.MALFORMED, boundary, code, detail)


def refusal(boundary: str, code: str, detail: str) -> ModelFailure:
    return ModelFailure(OutcomeClass.REFUSED, boundary, code, detail)


def unsupported_failure(boundary: str, code: str, detail: str) -> ModelFailure:
    return ModelFailure(OutcomeClass.UNSUPPORTED, boundary, code, detail)


def deterministic_limit_failure(
    boundary: str,
    code: str,
    detail: str,
) -> ModelFailure:
    return ModelFailure(
        OutcomeClass.DETERMINISTIC_LIMIT_EXCEEDED,
        boundary,
        code,
        detail,
    )


def _u64(value: int) -> bytes:
    if type(value) is not int or not 0 <= value < 1 << 64:
        raise malformed(
            "term:encoding",
            "FRI-IOR-TERM-001",
            "a canonical length must be an unsigned 64-bit integer",
        )
    return value.to_bytes(8, "big")


def encode_term(value: Any) -> bytes:
    """Encode the package's closed finite identity-term language.

    Tuple and list share one sequence constructor.  Map keys are UTF-8 text
    and are sorted by their encoded key, so host-language insertion order has
    no effect on an identity.
    """

    nodes = 0

    def over_byte_bound() -> ModelFailure:
        return ModelFailure(
            OutcomeClass.DETERMINISTIC_LIMIT_EXCEEDED,
            "term:encoding",
            "FRI-IOR-TERM-005",
            "the canonical term exceeds its byte bound",
        )

    def extend_bounded(target: bytearray, addition: bytes) -> None:
        if len(target) + len(addition) > MAX_TERM_BYTES:
            raise over_byte_bound()
        target.extend(addition)

    def encode(current: Any, depth: int) -> bytes:
        nonlocal nodes
        nodes += 1
        if nodes > MAX_TERM_NODES or depth > MAX_TERM_DEPTH:
            raise ModelFailure(
                OutcomeClass.DETERMINISTIC_LIMIT_EXCEEDED,
                "term:encoding",
                "FRI-IOR-TERM-002",
                "the canonical term exceeds its node or depth bound",
            )

        if current is None:
            result = b"N"
        elif current is False:
            result = b"F"
        elif current is True:
            result = b"T"
        elif type(current) is int:
            sign = b"+" if current >= 0 else b"-"
            magnitude = abs(current)
            body_length = max(1, (magnitude.bit_length() + 7) // 8)
            if 10 + body_length > MAX_TERM_BYTES:
                raise over_byte_bound()
            body = b"\x00" if magnitude == 0 else magnitude.to_bytes(body_length, "big")
            result = b"I" + sign + _u64(len(body)) + body
        elif type(current) is str:
            if len(current) > MAX_TERM_BYTES:
                raise over_byte_bound()
            body = current.encode("utf-8")
            if 9 + len(body) > MAX_TERM_BYTES:
                raise over_byte_bound()
            result = b"S" + _u64(len(body)) + body
        elif type(current) is bytes:
            if 9 + len(current) > MAX_TERM_BYTES:
                raise over_byte_bound()
            result = b"B" + _u64(len(current)) + current
        elif type(current) in (tuple, list):
            if len(current) > MAX_TERM_NODES:
                raise ModelFailure(
                    OutcomeClass.DETERMINISTIC_LIMIT_EXCEEDED,
                    "term:encoding",
                    "FRI-IOR-TERM-002",
                    "the canonical term exceeds its node or depth bound",
                )
            encoded = bytearray(b"L" + _u64(len(current)))
            for child_value in current:
                child = encode(child_value, depth + 1)
                extend_bounded(encoded, _u64(len(child)))
                extend_bounded(encoded, child)
            result = bytes(encoded)
        elif type(current) in (dict, MappingProxyType):
            if len(current) > MAX_TERM_NODES:
                raise ModelFailure(
                    OutcomeClass.DETERMINISTIC_LIMIT_EXCEEDED,
                    "term:encoding",
                    "FRI-IOR-TERM-002",
                    "the canonical term exceeds its node or depth bound",
                )
            if not all(isinstance(key, str) for key in current):
                raise malformed(
                    "term:encoding",
                    "FRI-IOR-TERM-003",
                    "canonical maps require text keys",
                )
            encoded_keys: list[tuple[bytes, str]] = []
            key_bytes_total = 0
            for key in current:
                if len(key) > MAX_TERM_BYTES:
                    raise over_byte_bound()
                key_bytes = key.encode("utf-8")
                key_bytes_total += len(key_bytes)
                if key_bytes_total > MAX_TERM_BYTES:
                    raise over_byte_bound()
                encoded_keys.append((key_bytes, key))
            encoded = bytearray(b"M" + _u64(len(encoded_keys)))
            for _, key in sorted(encoded_keys):
                key_body = encode(key, depth + 1)
                value_body = encode(current[key], depth + 1)
                extend_bounded(encoded, _u64(len(key_body)))
                extend_bounded(encoded, key_body)
                extend_bounded(encoded, _u64(len(value_body)))
                extend_bounded(encoded, value_body)
            result = bytes(encoded)
        else:
            raise malformed(
                "term:encoding",
                "FRI-IOR-TERM-004",
                f"unsupported canonical term type: {type(current)!r}",
            )

        if len(result) > MAX_TERM_BYTES:
            raise over_byte_bound()
        return result

    return encode(value, 0)


SEMANTIC_REGIME_TERM = {
    "name": "zkc.fri-ior.closed-finite-term",
    "version": 1,
    "hash": "sha256",
    "term_abi": "tagged-length-delimited-sorted-text-map.v1",
    "max_bytes": MAX_TERM_BYTES,
    "max_nodes": MAX_TERM_NODES,
    "max_depth": MAX_TERM_DEPTH,
}
SEMANTIC_REGIME_ID = (
    "zkc.fri-ior.closed-finite-term.v1.sha256."
    + hashlib.sha256(
        b"zkc.fri-ior.semantic-regime\x00" + encode_term(SEMANTIC_REGIME_TERM)
    ).hexdigest()
)


def semantic_id(subject_kind: str, domain: str, preimage: Any) -> SemanticId:
    """Hash one typed canonical preimage under the supported semantic regime."""

    kind = _validate_identifier(
        subject_kind,
        "subject_kind",
        "FRI-IOR-IDENTITY-001",
    )
    identity_domain = _validate_identifier(
        domain,
        "domain",
        "FRI-IOR-IDENTITY-002",
    )
    kind_bytes = kind.encode("ascii")
    domain_bytes = identity_domain.encode("ascii")
    regime = SEMANTIC_REGIME_ID.encode("ascii")
    digest = hashlib.sha256(
        b"zkc.fri-ior.identity\x00"
        + _u64(len(regime))
        + regime
        + _u64(len(kind_bytes))
        + kind_bytes
        + _u64(len(domain_bytes))
        + domain_bytes
        + encode_term(preimage)
    ).digest()
    return SemanticId(
        subject_kind=kind,
        domain=identity_domain,
        semantic_regime=SEMANTIC_REGIME_ID,
        digest=digest,
    )


def check_semantic_id(
    candidate: object,
    *,
    expected_subject_kind: str,
    expected_domain: str,
) -> CheckResult:
    """Check kind and regime without collapsing formed mismatches to malformed."""

    boundary = "identity:compatibility"
    if not isinstance(candidate, SemanticId):
        return CheckResult(
            OutcomeClass.MALFORMED,
            boundary,
            "FRI-IOR-IDENTITY-005",
            "identity compatibility requires a formed SemanticId",
        )
    try:
        kind = _validate_identifier(
            expected_subject_kind,
            "expected_subject_kind",
            "FRI-IOR-IDENTITY-006",
        )
        domain = _validate_identifier(
            expected_domain,
            "expected_domain",
            "FRI-IOR-IDENTITY-007",
        )
        if candidate.semantic_regime != SEMANTIC_REGIME_ID:
            return unsupported(
                boundary,
                "FRI-IOR-IDENTITY-008",
                "the semantic identity uses an unsupported semantic regime",
            )
        if candidate.subject_kind != kind:
            return kind_mismatch(
                boundary,
                "FRI-IOR-IDENTITY-009",
                "the semantic identity has the wrong subject kind",
            )
        if candidate.domain != domain:
            return kind_mismatch(
                boundary,
                "FRI-IOR-IDENTITY-010",
                "the semantic identity has the wrong identity domain",
            )
        return affirmative(
            boundary,
            "FRI-IOR-IDENTITY-100",
            "the semantic identity kind, domain, and regime match",
            subject=candidate,
        )
    except ModelFailure as error:
        return error.to_result()


@dataclass(frozen=True)
class ResourceLimits:
    """Finite limits for operations that this package can perform."""

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

    def __post_init__(self) -> None:
        if type(self) is not ResourceLimits:
            raise malformed(
                "resources:formation",
                "FRI-IOR-RESOURCE-009",
                "resource limits must use the exact closed carrier type",
            )
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
        ):
            value = getattr(self, name)
            if type(value) is not int or value < 0:
                raise malformed(
                    "resources:formation",
                    "FRI-IOR-RESOURCE-001",
                    f"{name} must be a non-negative integer",
                )

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


HARD_RESOURCE_LIMITS = ResourceLimits(
    field_operations=4096,
    hash_calls=256,
    hash_bytes=1 << 16,
    merkle_nodes=256,
    transcript_frames=256,
    sampler_attempts=4096,
    grinding_trials=1 << 20,
    logical_query_occurrences=256,
    unique_openings=128,
    proof_bytes=1 << 20,
)


@dataclass
class ResourceCounter:
    """An evaluator-internal atomic counter under immutable selected limits.

    The mutable object is cooperative instrumentation when passed through a
    low-level API; it is not itself evidence.  An authoritative top-level
    validation operation must create the exact carrier privately and publish
    only its frozen snapshot after the complete operation.
    """

    limits: ResourceLimits = HARD_RESOURCE_LIMITS
    field_operations: int = 0
    hash_calls: int = 0
    hash_bytes: int = 0
    merkle_nodes: int = 0
    transcript_frames: int = 0
    sampler_attempts: int = 0
    grinding_trials: int = 0
    logical_query_occurrences: int = 0
    unique_openings: int = 0
    proof_bytes: int = 0

    def __post_init__(self) -> None:
        if type(self) is not ResourceCounter:
            raise malformed(
                "resources:formation",
                "FRI-IOR-RESOURCE-010",
                "resource counters must use the exact evaluator-owned carrier type",
            )
        if type(self.limits) is not ResourceLimits:
            raise malformed(
                "resources:formation",
                "FRI-IOR-RESOURCE-002",
                "a resource counter requires a ResourceLimits value",
            )
        for name in self.limits.to_term():
            if getattr(self.limits, name) > getattr(HARD_RESOURCE_LIMITS, name):
                raise deterministic_limit_failure(
                    "resources:admission",
                    "FRI-IOR-RESOURCE-003",
                    f"requested {name} exceeds the evaluator hard cap",
                )
            current = getattr(self, name)
            if type(current) is not int or current < 0:
                raise malformed(
                    "resources:formation",
                    "FRI-IOR-RESOURCE-004",
                    f"initial {name} must be a non-negative integer",
                )
            if current > getattr(self.limits, name):
                raise ModelFailure(
                    OutcomeClass.DETERMINISTIC_LIMIT_EXCEEDED,
                    "resources:formation",
                    "FRI-IOR-RESOURCE-005",
                    f"initial {name} exceeds its selected limit",
                )

    def _reserve(self, **charges: int) -> None:
        unknown = set(charges).difference(self.limits.to_term())
        if unknown:
            raise malformed(
                "resources:accounting",
                "FRI-IOR-RESOURCE-006",
                f"unknown resource dimensions: {sorted(unknown)!r}",
            )
        for name, amount in charges.items():
            if type(amount) is not int or amount < 0:
                raise malformed(
                    "resources:accounting",
                    "FRI-IOR-RESOURCE-007",
                    f"the {name} charge must be a non-negative integer",
                )

        proposed = {
            name: getattr(self, name) + charges.get(name, 0)
            for name in self.limits.to_term()
        }
        for name, value in proposed.items():
            if value > getattr(self.limits, name):
                raise ModelFailure(
                    OutcomeClass.DETERMINISTIC_LIMIT_EXCEEDED,
                    "resources:accounting",
                    "FRI-IOR-RESOURCE-008",
                    f"{name} would exceed the selected resource limit",
                )
        for name, value in proposed.items():
            setattr(self, name, value)

    def consume_field_operations(self, operations: int) -> None:
        self._reserve(field_operations=operations)

    def consume_hash(self, payload_bytes: int, *, merkle_nodes: int = 0) -> None:
        """Charge one hash and only explicitly identified Merkle nodes."""

        self._reserve(
            hash_calls=1,
            hash_bytes=payload_bytes,
            merkle_nodes=merkle_nodes,
        )

    def consume_transcript_frames(self, frames: int) -> None:
        self._reserve(transcript_frames=frames)

    def consume_sampler_attempts(self, attempts: int) -> None:
        self._reserve(sampler_attempts=attempts)

    def consume_grinding_trials(self, trials: int) -> None:
        self._reserve(grinding_trials=trials)

    def consume_logical_query_occurrences(self, occurrences: int) -> None:
        self._reserve(logical_query_occurrences=occurrences)

    def consume_unique_openings(self, openings: int) -> None:
        self._reserve(unique_openings=openings)

    def consume_proof_bytes(self, byte_count: int) -> None:
        self._reserve(proof_bytes=byte_count)

    def consume_query_opening_resources(
        self,
        *,
        logical_query_occurrences: int,
        unique_openings: int,
        proof_bytes: int,
    ) -> None:
        """Atomically charge occurrence semantics and deduplicated material."""

        self._reserve(
            logical_query_occurrences=logical_query_occurrences,
            unique_openings=unique_openings,
            proof_bytes=proof_bytes,
        )

    def snapshot(self) -> dict[str, int]:
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
