"""Finite adversarial model for the Fiat--Shamir assurance boundary.

This package demonstrates why transcript-structure checks, concrete binding,
sampler adequacy, theorem applicability, projection, and realization
conformance are different judgments.  It is deliberately small and finite.  It
is not a cryptographic implementation, a proof of security, a profile compiler,
or an authority source for zkc.
"""

from __future__ import annotations

from collections import Counter
from dataclasses import dataclass, fields
from enum import Enum
import hashlib
from typing import Callable, Iterable, Mapping, Sequence, TypeVar


class Outcome(str, Enum):
    AFFIRMATIVE = "Affirmative"
    NEGATIVE = "Negative"
    MISSING_DEPENDENCY = "MissingDependency"
    CANNOT_ANSWER = "CannotAnswer"
    REFUSED = "Refused"
    MALFORMED = "Malformed"


@dataclass(frozen=True)
class Answer:
    outcome: Outcome
    value: object | None = None
    reasons: tuple[str, ...] = ()


def affirmative(value: object) -> Answer:
    return Answer(Outcome.AFFIRMATIVE, value)


def negative(*reasons: str) -> Answer:
    return Answer(Outcome.NEGATIVE, reasons=tuple(sorted(set(reasons))))


@dataclass(frozen=True, order=True)
class Frame:
    tag: str
    coordinate: str
    payload: bytes


@dataclass(frozen=True)
class ChallengePrefix:
    challenge: str
    frames: tuple[Frame, ...]


def check_exact_prefix(expected: ChallengePrefix, actual: ChallengePrefix) -> Answer:
    if not expected.challenge or not actual.challenge:
        return Answer(Outcome.MALFORMED, reasons=("empty-challenge-coordinate",))
    if expected.challenge != actual.challenge:
        return negative("challenge-coordinate")
    if expected.frames == actual.frames:
        return affirmative(expected)

    reasons: set[str] = set()
    expected_counter = Counter(expected.frames)
    actual_counter = Counter(actual.frames)
    if expected_counter - actual_counter:
        reasons.add("omitted-or-substituted-frame")
    if actual_counter - expected_counter:
        reasons.add("injected-or-duplicated-frame")
    if expected_counter == actual_counter:
        reasons.add("reordered-frame")
    return negative(*reasons)


@dataclass(frozen=True, order=True)
class StatementRoute:
    external_slot: str
    binding_coordinate: str


@dataclass(frozen=True)
class ClosedStatementManifest:
    expected_routes: tuple[StatementRoute, ...]


def check_closed_statement_correspondence(
    manifest: ClosedStatementManifest,
    supplied_routes: Sequence[StatementRoute],
    prefix: ChallengePrefix,
) -> Answer:
    expected = manifest.expected_routes
    supplied = tuple(supplied_routes)
    if not expected or len(set(expected)) != len(expected):
        return Answer(
            Outcome.MALFORMED,
            reasons=("statement-manifest-is-empty-or-duplicated",),
        )
    if len(set(supplied)) != len(supplied):
        return Answer(Outcome.MALFORMED, reasons=("duplicate-statement-route",))

    expected_set = set(expected)
    supplied_set = set(supplied)
    reasons: set[str] = set()
    if expected_set - supplied_set:
        reasons.add("missing-external-statement-route")
    if supplied_set - expected_set:
        reasons.add("extra-or-substituted-statement-route")

    statement_coordinates = {
        frame.coordinate for frame in prefix.frames if frame.tag == "statement"
    }
    expected_coordinates = {route.binding_coordinate for route in expected}
    if expected_coordinates - statement_coordinates:
        reasons.add("statement-route-not-present-in-prefix")
    if statement_coordinates - expected_coordinates:
        reasons.add("undeclared-statement-frame")
    if reasons:
        return negative(*reasons)
    return affirmative(tuple(sorted(expected)))


def _u32(value: int) -> bytes:
    if value < 0 or value >= 2**32:
        raise ValueError("value is outside the finite u32 instrument")
    return value.to_bytes(4, "big")


def _length_prefix(value: bytes) -> bytes:
    return _u32(len(value)) + value


def canonical_frame_encoding(frames: Sequence[Frame]) -> bytes:
    """A finite typed length-delimited control encoding."""

    encoded = bytearray(_u32(len(frames)))
    for frame in frames:
        encoded.extend(_length_prefix(frame.tag.encode("utf-8")))
        encoded.extend(_length_prefix(frame.coordinate.encode("utf-8")))
        encoded.extend(_length_prefix(frame.payload))
    return bytes(encoded)


def unframed_payload_encoding(frames: Sequence[Frame]) -> bytes:
    """An intentionally ambiguous encoding used only as a falsifier."""

    return b"".join(frame.payload for frame in frames)


T = TypeVar("T")


@dataclass(frozen=True)
class Alias:
    left: object
    right: object
    image: object


def find_aliases(domain: Iterable[T], encoder: Callable[[T], object]) -> tuple[Alias, ...]:
    seen: dict[object, T] = {}
    aliases: list[Alias] = []
    for item in domain:
        image = encoder(item)
        prior = seen.get(image)
        if prior is not None and prior != item:
            aliases.append(Alias(prior, item, image))
        else:
            seen[image] = item
    return tuple(aliases)


def complete_limb_projection(stream: tuple[int, ...]) -> bytes:
    if any(value < 0 or value >= 2**16 for value in stream):
        raise ValueError("limb is outside the selected finite domain")
    return _u32(len(stream)) + b"".join(value.to_bytes(2, "big") for value in stream)


def trailing_zero_aliased_projection(stream: tuple[int, ...]) -> bytes:
    """Models a no-length-marker tail in which missing and zero limbs alias."""

    values = list(stream)
    while values and values[-1] == 0:
        values.pop()
    return b"".join(value.to_bytes(2, "big") for value in values)


def full_width_field_projection(value: int) -> bytes:
    if value < 0 or value >= 2**16:
        raise ValueError("field representative is outside the selected domain")
    return value.to_bytes(2, "big")


def high_bit_truncated_projection(value: int) -> bytes:
    """Models a floor-sized limb projection that silently drops high bits."""

    if value < 0 or value >= 2**16:
        raise ValueError("field representative is outside the selected domain")
    return bytes((value & 0xFF,))


class SamplerExpectation(str, Enum):
    TOTAL_EXACT_UNIFORM = "TotalExactUniform"
    CONDITIONAL_UNIFORM_WITH_FAILURE_TERM = "ConditionalUniformWithFailureTerm"


@dataclass(frozen=True)
class SamplerReport:
    challenge_domain: tuple[int, ...]
    counts: tuple[tuple[int, int], ...]
    failures: int
    draws: int


def analyze_sampler(
    draw_space: Iterable[int],
    challenge_domain: Sequence[int],
    decoder: Callable[[int], int | None],
) -> SamplerReport:
    domain = tuple(challenge_domain)
    if not domain or len(set(domain)) != len(domain):
        raise ValueError("challenge domain must be nonempty and unique")
    counter = Counter({value: 0 for value in domain})
    failures = 0
    draws = 0
    for draw in draw_space:
        draws += 1
        decoded = decoder(draw)
        if decoded is None:
            failures += 1
        elif decoded not in counter:
            raise ValueError("decoder returned a value outside the challenge domain")
        else:
            counter[decoded] += 1
    return SamplerReport(domain, tuple(sorted(counter.items())), failures, draws)


def qualify_sampler(
    report: SamplerReport,
    expectation: SamplerExpectation,
    *,
    explicit_failure_term: bool = False,
) -> Answer:
    counts = tuple(count for _, count in report.counts)
    if report.draws == 0 or not counts:
        return Answer(Outcome.MALFORMED, reasons=("empty-sampler-experiment",))
    if len(set(counts)) != 1:
        return negative("biased-challenge-distribution")
    if expectation is SamplerExpectation.TOTAL_EXACT_UNIFORM:
        if report.failures:
            return negative("sampler-is-not-total")
        return affirmative(report)
    if report.failures and not explicit_failure_term:
        return Answer(
            Outcome.CANNOT_ANSWER,
            reasons=("sampler-failure-term-is-unmodeled",),
        )
    return affirmative(report)


@dataclass(frozen=True)
class LogicalQuery:
    session_id: bytes
    instance: bytes
    prefix: tuple[Frame, ...]
    namespace: bytes


def canonical_query_index(query: LogicalQuery) -> bytes:
    frames = (
        Frame("session", "session", query.session_id),
        Frame("instance", "statement-root", query.instance),
        *query.prefix,
        Frame("namespace", "draw", query.namespace),
    )
    return canonical_frame_encoding(frames)


def weak_query_index(query: LogicalQuery) -> bytes:
    """Drops session, instance, coordinates, tags, and namespace."""

    return unframed_payload_encoding(query.prefix)


@dataclass(frozen=True)
class FSStaticContract:
    construction_id: str
    frame_law_id: str
    derived_prefix_law_id: str
    namespace_law_id: str
    absorb_algorithm_id: str
    squeeze_algorithm_id: str
    advance_algorithm_id: str
    sampler_law_id: str
    failure_type_id: str


@dataclass(frozen=True)
class OIRStaticProjection:
    construction_id: str
    frame_law_id: str
    derived_prefix_law_id: str
    namespace_law_id: str
    absorb_algorithm_id: str
    squeeze_algorithm_id: str
    advance_algorithm_id: str
    sampler_law_id: str
    failure_type_id: str


def exact_oir_projection(contract: FSStaticContract) -> OIRStaticProjection:
    return OIRStaticProjection(
        **{field.name: getattr(contract, field.name) for field in fields(contract)}
    )


def check_projection(
    contract: FSStaticContract, projection: OIRStaticProjection
) -> Answer:
    mismatches = tuple(
        field.name
        for field in fields(contract)
        if getattr(contract, field.name) != getattr(projection, field.name)
    )
    if mismatches:
        return negative(*(f"projection:{name}" for name in mismatches))
    return affirmative(projection)


@dataclass(frozen=True)
class ConformanceVector:
    query: LogicalQuery
    expected_challenge: int


@dataclass(frozen=True)
class RealizationCandidate:
    construction_id: str
    algorithm_ids: tuple[str, str, str]
    query_index: Callable[[LogicalQuery], bytes]
    challenge: Callable[[bytes], int]
    consumes_entire_proof: bool


def check_realization(
    contract: FSStaticContract,
    candidate: RealizationCandidate,
    vectors: Sequence[ConformanceVector],
) -> Answer:
    if not vectors:
        return Answer(Outcome.MALFORMED, reasons=("empty-conformance-vector-set",))
    reasons: set[str] = set()
    if candidate.construction_id != contract.construction_id:
        reasons.add("realization-construction-identity")
    expected_algorithms = (
        contract.absorb_algorithm_id,
        contract.squeeze_algorithm_id,
        contract.advance_algorithm_id,
    )
    if candidate.algorithm_ids != expected_algorithms:
        reasons.add("realization-algorithm-identity")
    if not candidate.consumes_entire_proof:
        reasons.add("parser-did-not-reach-end-of-input")
    for vector in vectors:
        expected_index = canonical_query_index(vector.query)
        actual_index = candidate.query_index(vector.query)
        if actual_index != expected_index:
            reasons.add("logical-query-index-mismatch")
            continue
        if candidate.challenge(actual_index) != vector.expected_challenge:
            reasons.add("challenge-vector-mismatch")
    if reasons:
        return negative(*reasons)
    return affirmative({"vector_count": len(vectors)})


def byte_challenge(index: bytes) -> int:
    return hashlib.sha256(index).digest()[0] % 8


@dataclass(frozen=True)
class PremiseEvidence:
    premise: str
    established: bool
    evidence_kind: str


def qualify_claim(
    required_premises: Sequence[str],
    evidence: Mapping[str, PremiseEvidence],
) -> Answer:
    required = tuple(required_premises)
    if not required or len(set(required)) != len(required):
        return Answer(Outcome.MALFORMED, reasons=("invalid-premise-catalog",))
    missing = tuple(sorted(set(required) - set(evidence)))
    if missing:
        return Answer(
            Outcome.MISSING_DEPENDENCY,
            reasons=tuple(f"missing:{item}" for item in missing),
        )
    substituted = tuple(
        sorted(
            name
            for name in required
            if evidence[name].premise != name or not evidence[name].evidence_kind
        )
    )
    if substituted:
        return Answer(
            Outcome.REFUSED,
            reasons=tuple(f"substituted:{item}" for item in substituted),
        )
    false = tuple(sorted(name for name in required if not evidence[name].established))
    if false:
        return negative(*(f"falsified:{item}" for item in false))
    return affirmative(tuple(evidence[name] for name in required))


CLASSICAL_FS_ACTIVATION_PREMISES = (
    "structural-prefix-completeness",
    "closed-statement-correspondence",
    "encoding-adequacy",
    "challenge-sampler-adequacy",
    "adaptive-random-oracle-process-correspondence",
    "interactive-source-property",
    "theorem-source-validation",
    "theorem-applicability",
    "oir-projection-preservation",
    "realization-conformance",
)


QROM_ADDITIONAL_PREMISES = (
    "quantum-adversary-model",
    "qrom-theorem-source-validation",
    "qrom-theorem-applicability",
    "quantum-query-loss-accounting",
)


def evidence(
    premises: Sequence[str],
    *,
    kind: str = "bounded-control",
) -> dict[str, PremiseEvidence]:
    return {
        premise: PremiseEvidence(premise, True, kind) for premise in premises
    }
