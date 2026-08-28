"""One exact native logical-oracle execution of the finite FRI profile.

This module models the interaction before any oracle-commitment compilation.
Publishing an oracle therefore fixes an immutable, exact-domain function and
grants logical query access.  It does not disclose the carrier, emit a digest,
or claim a cryptographic binding property.

The executable verdict is deliberately narrower than a FRI theorem.  An
affirmative result says that this verifier accepted these four sampled query
occurrences.  The structural claim and reduction records name the intended
fold chain; they establish neither proximity preservation nor an outer
computation relation.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum
from typing import Any

from .field import (
    Fp,
    Fp2,
    binary_fold,
    canonical_polynomial,
    evaluate_polynomial,
    polynomial_degree,
)
from .profile import (
    D0,
    D1,
    D2,
    EXACT_PROFILE,
    EvaluationDomain,
    FriIorProfile,
    admit_exact_profile,
)
from .terms import (
    CheckResult,
    ModelFailure,
    OutcomeClass,
    ResourceCounter,
    SemanticId,
    affirmative,
    checker_failure,
    malformed,
    refusal,
    semantic_id,
)


INITIAL_ORACLE_NAME = "O0"
PROVER_ORACLE_NAME = "O1"
FIRST_CHALLENGE_NAME = "beta0"
SECOND_CHALLENGE_NAME = "beta1"
TERMINAL_NAME = "terminal"

# Folding a coefficient pair performs one extension multiplication and one
# extension addition in this evaluator's abstract field-operation basis.
COEFFICIENT_FOLD_FIELD_OPERATIONS = 2


class OraclePublicationMode(str, Enum):
    """The native publication effect supported by this model."""

    LOGICAL_ACCESS = "LogicalAccess"


class OracleOrigin(str, Enum):
    """Who supplies the oracle carrier before its fixation occurrence."""

    INITIAL_ORACLE = "InitialOracle"
    PROVER_ORACLE = "ProverOracle"


class NativeEventKind(str, Enum):
    PUBLISH_ORACLE = "PublishOracle"
    FRESH_CHALLENGE = "FreshChallenge"
    TERMINAL_MATERIAL = "TerminalMaterial"
    RANDOM_QUERY_DRAW = "RandomQueryDraw"


class NativeOracleLayer(str, Enum):
    """The two logical-oracle layers queried by the native verifier."""

    INITIAL = "InitialLayer"
    FIRST_FOLD = "FirstFoldLayer"


class NativeVerdict(str, Enum):
    ACCEPT = "Accept"
    REJECT = "Reject"


@dataclass(frozen=True, slots=True)
class OracleEntry:
    """One entry in the declared canonical enumeration of an oracle domain."""

    point: Fp
    value: Fp2

    def __post_init__(self) -> None:
        if not isinstance(self.point, Fp) or not isinstance(self.value, Fp2):
            raise malformed(
                "native:oracle-formation",
                "FRI-IOR-NATIVE-001",
                "an oracle entry requires an Fp point and an Fp2 answer",
            )


@dataclass(frozen=True, slots=True)
class DeclaredStrategyDependency:
    """Caller-declared dependencies for deterministic cold replay.

    This metadata can be checked for internal order consistency.  It is not an
    observation of a host strategy and establishes no non-anticipation claim.
    """

    subject: str
    authored_at: int
    declared_read_set: tuple[str, ...]

    def __post_init__(self) -> None:
        if not isinstance(self.subject, str) or not self.subject:
            raise malformed(
                "native:declared-strategy-dependency-formation",
                "FRI-IOR-NATIVE-002",
                "declared strategy dependencies require a non-empty subject name",
            )
        if type(self.authored_at) is not int or self.authored_at < 0:
            raise malformed(
                "native:declared-strategy-dependency-formation",
                "FRI-IOR-NATIVE-003",
                "declared strategy dependencies require a non-negative event index",
            )
        if not isinstance(self.declared_read_set, tuple) or not all(
            isinstance(item, str) and item for item in self.declared_read_set
        ):
            raise malformed(
                "native:declared-strategy-dependency-formation",
                "FRI-IOR-NATIVE-004",
                "a declared strategy read set is a tuple of non-empty object names",
            )


@dataclass(frozen=True, slots=True)
class LogicalOracle:
    """An evaluator-internal carrier published through logical access only.

    ``entries`` are present so this executable checker can answer declared
    queries.  They are not part of :meth:`publication_observation`, which is
    the protocol-visible effect of publication.
    """

    name: str
    domain: EvaluationDomain
    origin: OracleOrigin
    entries: tuple[OracleEntry, ...]
    declared_strategy_dependency: DeclaredStrategyDependency | None = None
    publication_mode: OraclePublicationMode = OraclePublicationMode.LOGICAL_ACCESS

    def __post_init__(self) -> None:
        if not isinstance(self.name, str) or not self.name:
            raise malformed(
                "native:oracle-formation",
                "FRI-IOR-NATIVE-005",
                "a logical oracle requires a non-empty name",
            )
        if not isinstance(self.domain, EvaluationDomain):
            raise malformed(
                "native:oracle-formation",
                "FRI-IOR-NATIVE-006",
                "a logical oracle requires an EvaluationDomain",
            )
        if not isinstance(self.origin, OracleOrigin):
            raise malformed(
                "native:oracle-formation",
                "FRI-IOR-NATIVE-007",
                "a logical oracle requires a typed OracleOrigin",
            )
        if not isinstance(self.publication_mode, OraclePublicationMode):
            raise malformed(
                "native:oracle-formation",
                "FRI-IOR-NATIVE-008",
                "a logical oracle requires a typed publication mode",
            )
        if not isinstance(self.entries, tuple) or not all(
            isinstance(entry, OracleEntry) for entry in self.entries
        ):
            raise malformed(
                "native:oracle-formation",
                "FRI-IOR-NATIVE-009",
                "a logical oracle carrier is a tuple of OracleEntry values",
            )
        if self.declared_strategy_dependency is not None and not isinstance(
            self.declared_strategy_dependency, DeclaredStrategyDependency
        ):
            raise malformed(
                "native:oracle-formation",
                "FRI-IOR-NATIVE-010",
                "oracle replay metadata must be a DeclaredStrategyDependency",
            )

    def publication_observation(self) -> dict[str, Any]:
        """Return metadata for fixation and query access, never the carrier."""

        return {
            "oracle_name": self.name,
            "domain_name": self.domain.name,
            "origin": self.origin.value,
            "publication_mode": self.publication_mode.value,
            "effects": (
                "fix-immutable-oracle",
                "grant-declared-logical-query-access",
            ),
        }

    def logical_answer_at(self, canonical_index: int) -> Fp2:
        """Exercise the query capability without producing a full carrier."""

        if type(canonical_index) is not int:
            raise malformed(
                "native:logical-query",
                "FRI-IOR-NATIVE-051",
                "a logical-oracle query index must be an integer",
            )
        if not 0 <= canonical_index < len(self.entries):
            raise refusal(
                "native:logical-query",
                "FRI-IOR-NATIVE-052",
                "a logical-oracle query index is unavailable",
            )
        return self.entries[canonical_index].value


@dataclass(frozen=True, slots=True)
class FreshChallenge:
    """A caller-supplied value interpreted as one verifier-fresh challenge."""

    name: str
    value: Fp2

    def __post_init__(self) -> None:
        if not isinstance(self.name, str) or not self.name:
            raise malformed(
                "native:challenge-formation",
                "FRI-IOR-NATIVE-011",
                "a fresh challenge requires a non-empty name",
            )
        if not isinstance(self.value, Fp2):
            raise malformed(
                "native:challenge-formation",
                "FRI-IOR-NATIVE-012",
                "a fresh challenge value must be an Fp2 element",
            )


@dataclass(frozen=True, slots=True)
class TerminalPolynomial:
    """Bounded syntax with declared replay dependencies and a late semantic check."""

    coefficients: tuple[Fp2, ...]
    declared_strategy_dependency: DeclaredStrategyDependency

    def __post_init__(self) -> None:
        canonical_polynomial(
            self.coefficients,
            EXACT_PROFILE.terminal_max_coefficient_count,
        )
        if not isinstance(
            self.declared_strategy_dependency,
            DeclaredStrategyDependency,
        ):
            raise malformed(
                "native:terminal-formation",
                "FRI-IOR-NATIVE-013",
                "terminal replay metadata requires a DeclaredStrategyDependency",
            )


@dataclass(frozen=True, slots=True)
class RandomQueryDraw:
    """One top-level verifier-random draw, before layer-query expansion."""

    ordinal: int
    initial_domain_index: int

    def __post_init__(self) -> None:
        if type(self.ordinal) is not int or self.ordinal < 0:
            raise malformed(
                "native:query-formation",
                "FRI-IOR-NATIVE-014",
                "a random-query ordinal must be a non-negative integer",
            )
        if type(self.initial_domain_index) is not int:
            raise malformed(
                "native:query-formation",
                "FRI-IOR-NATIVE-015",
                "a random-query index must be an integer",
            )


@dataclass(frozen=True, slots=True)
class LayerQueryAnswerOccurrence:
    """One ordered antipodal-pair query and its two logical answers.

    This is an evaluator- and checked-compilation-facing record.  It is not a
    protocol publication and does not disclose either oracle's full carrier.
    Repeated top-level draws produce repeated occurrence records even when
    their pair indices and answers are equal.
    """

    top_level_ordinal: int
    layer: NativeOracleLayer
    oracle_name: str
    pair_index: int
    positive_answer_index: int
    negative_answer_index: int
    positive_value: Fp2
    negative_value: Fp2

    def __post_init__(self) -> None:
        if type(self.top_level_ordinal) is not int or self.top_level_ordinal < 0:
            raise malformed(
                "native:layer-query-formation",
                "FRI-IOR-NATIVE-053",
                "a layer-query occurrence requires a non-negative top-level ordinal",
            )
        if not isinstance(self.layer, NativeOracleLayer):
            raise malformed(
                "native:layer-query-formation",
                "FRI-IOR-NATIVE-053",
                "a layer-query occurrence requires a typed native oracle layer",
            )
        expected_oracle, half_order = (
            (INITIAL_ORACLE_NAME, D1.order)
            if self.layer is NativeOracleLayer.INITIAL
            else (PROVER_ORACLE_NAME, D2.order)
        )
        if self.oracle_name != expected_oracle:
            raise malformed(
                "native:layer-query-formation",
                "FRI-IOR-NATIVE-053",
                "a layer-query occurrence names the wrong oracle for its layer",
            )
        if (
            type(self.pair_index) is not int
            or type(self.positive_answer_index) is not int
            or type(self.negative_answer_index) is not int
            or not 0 <= self.pair_index < half_order
            or self.positive_answer_index != self.pair_index
            or self.negative_answer_index != self.pair_index + half_order
        ):
            raise malformed(
                "native:layer-query-formation",
                "FRI-IOR-NATIVE-053",
                "layer-query answer indices must be the ordered antipodal pair",
            )
        if not isinstance(self.positive_value, Fp2) or not isinstance(
            self.negative_value, Fp2
        ):
            raise malformed(
                "native:layer-query-formation",
                "FRI-IOR-NATIVE-053",
                "layer-query answers must be canonical Fp2 values",
            )

    @property
    def ordered_answers(self) -> tuple[tuple[int, Fp2], tuple[int, Fp2]]:
        return (
            (self.positive_answer_index, self.positive_value),
            (self.negative_answer_index, self.negative_value),
        )


@dataclass(frozen=True, slots=True)
class NativeEvent:
    index: int
    kind: NativeEventKind
    subject: str

    def __post_init__(self) -> None:
        if type(self.index) is not int or self.index < 0:
            raise malformed(
                "native:event-formation",
                "FRI-IOR-NATIVE-016",
                "an event index must be a non-negative integer",
            )
        if not isinstance(self.kind, NativeEventKind):
            raise malformed(
                "native:event-formation",
                "FRI-IOR-NATIVE-017",
                "a native event requires a typed event kind",
            )
        if not isinstance(self.subject, str) or not self.subject:
            raise malformed(
                "native:event-formation",
                "FRI-IOR-NATIVE-018",
                "a native event requires a non-empty subject name",
            )


@dataclass(frozen=True, slots=True)
class StructuralProximityClaim:
    """A role declaration, not evidence that the role's property is true."""

    oracle_name: str = INITIAL_ORACLE_NAME
    domain_name: str = D0.name
    degree_bound_exclusive: int = EXACT_PROFILE.initial_degree_bound_exclusive
    establishes_proximity: bool = field(default=False, init=False)
    implies_outer_relation: bool = field(default=False, init=False)

    def to_term(self) -> dict[str, Any]:
        return {
            "kind": "RSProximityClaim",
            "oracle": self.oracle_name,
            "domain": self.domain_name,
            "degree_bound_exclusive": self.degree_bound_exclusive,
            "establishes_proximity": self.establishes_proximity,
            "implies_outer_relation": self.implies_outer_relation,
        }


@dataclass(frozen=True, slots=True)
class StructuralFoldReduction:
    """The declared position of one fold, with no theorem capability."""

    source: str
    challenge: str
    target: str
    establishes_proximity_preservation: bool = field(default=False, init=False)

    def to_term(self) -> dict[str, Any]:
        return {
            "kind": "FoldReduction",
            "source": self.source,
            "challenge": self.challenge,
            "target": self.target,
            "establishes_proximity_preservation": (
                self.establishes_proximity_preservation
            ),
        }


@dataclass(frozen=True, slots=True)
class StructuralFoldChain:
    claim: StructuralProximityClaim
    reductions: tuple[StructuralFoldReduction, ...]

    def __post_init__(self) -> None:
        if not isinstance(self.claim, StructuralProximityClaim):
            raise malformed(
                "native:claim-formation",
                "FRI-IOR-NATIVE-019",
                "a fold chain requires a StructuralProximityClaim",
            )
        if not isinstance(self.reductions, tuple) or not all(
            isinstance(reduction, StructuralFoldReduction)
            for reduction in self.reductions
        ):
            raise malformed(
                "native:claim-formation",
                "FRI-IOR-NATIVE-020",
                "a fold chain requires a tuple of StructuralFoldReduction values",
            )

    def to_term(self) -> dict[str, Any]:
        return {
            "claim": self.claim.to_term(),
            "reductions": [reduction.to_term() for reduction in self.reductions],
            "authority": "structural-role-and-order-only",
        }


def canonical_structural_fold_chain() -> StructuralFoldChain:
    return StructuralFoldChain(
        claim=StructuralProximityClaim(),
        reductions=(
            StructuralFoldReduction(
                INITIAL_ORACLE_NAME,
                FIRST_CHALLENGE_NAME,
                PROVER_ORACLE_NAME,
            ),
            StructuralFoldReduction(
                PROVER_ORACLE_NAME,
                SECOND_CHALLENGE_NAME,
                TERMINAL_NAME,
            ),
        ),
    )


def canonical_event_log() -> tuple[NativeEvent, ...]:
    events = [
        NativeEvent(0, NativeEventKind.PUBLISH_ORACLE, INITIAL_ORACLE_NAME),
        NativeEvent(1, NativeEventKind.FRESH_CHALLENGE, FIRST_CHALLENGE_NAME),
        NativeEvent(2, NativeEventKind.PUBLISH_ORACLE, PROVER_ORACLE_NAME),
        NativeEvent(3, NativeEventKind.FRESH_CHALLENGE, SECOND_CHALLENGE_NAME),
        NativeEvent(4, NativeEventKind.TERMINAL_MATERIAL, TERMINAL_NAME),
    ]
    events.extend(
        NativeEvent(
            5 + ordinal,
            NativeEventKind.RANDOM_QUERY_DRAW,
            f"query-draw[{ordinal}]",
        )
        for ordinal in range(EXACT_PROFILE.ordered_query_count)
    )
    return tuple(events)


@dataclass(frozen=True, slots=True)
class NativeFriTrace:
    """A complete caller-supplied native interaction trace."""

    profile: FriIorProfile
    initial_oracle: LogicalOracle
    first_challenge: FreshChallenge
    prover_oracle: LogicalOracle
    second_challenge: FreshChallenge
    terminal: TerminalPolynomial
    query_draws: tuple[RandomQueryDraw, ...]
    events: tuple[NativeEvent, ...]
    structural_chain: StructuralFoldChain

    def __post_init__(self) -> None:
        expected_types = (
            (self.profile, FriIorProfile),
            (self.initial_oracle, LogicalOracle),
            (self.first_challenge, FreshChallenge),
            (self.prover_oracle, LogicalOracle),
            (self.second_challenge, FreshChallenge),
            (self.terminal, TerminalPolynomial),
            (self.structural_chain, StructuralFoldChain),
        )
        if not all(isinstance(value, expected) for value, expected in expected_types):
            raise malformed(
                "native:trace-formation",
                "FRI-IOR-NATIVE-021",
                "a native trace contains a value of the wrong semantic kind",
            )
        if not isinstance(self.query_draws, tuple) or not all(
            isinstance(draw, RandomQueryDraw) for draw in self.query_draws
        ):
            raise malformed(
                "native:trace-formation",
                "FRI-IOR-NATIVE-022",
                "native query draws must be a tuple of RandomQueryDraw values",
            )
        if not isinstance(self.events, tuple) or not all(
            isinstance(event, NativeEvent) for event in self.events
        ):
            raise malformed(
                "native:trace-formation",
                "FRI-IOR-NATIVE-023",
                "the event log must be a tuple of NativeEvent values",
            )

    @property
    def beta0(self) -> Fp2:
        return self.first_challenge.value

    @property
    def beta1(self) -> Fp2:
        return self.second_challenge.value

    @property
    def identity(self) -> SemanticId:
        """Identify the exact trace and native verdict inputs, not a run."""

        return semantic_id(
            "native-fri-trace",
            "fri-ior.native-trace.v1",
            _native_trace_identity_preimage(self),
        )


def _declared_dependency_term(
    dependency: DeclaredStrategyDependency | None,
) -> dict[str, Any] | None:
    if dependency is None:
        return None
    return {
        "subject": dependency.subject,
        "authored_at": dependency.authored_at,
        "declared_read_set": list(dependency.declared_read_set),
        "authority": "caller-declared-cold-replay-metadata",
        "establishes_strategy_nonanticipation": False,
    }


def _oracle_identity_term(oracle: LogicalOracle) -> dict[str, Any]:
    return {
        "name": oracle.name,
        "domain": oracle.domain.to_term(),
        "origin": oracle.origin.value,
        "publication_mode": oracle.publication_mode.value,
        "entries": [
            {
                "point": entry.point.value,
                "value": entry.value.to_term(),
            }
            for entry in oracle.entries
        ],
        "declared_strategy_dependency": _declared_dependency_term(
            oracle.declared_strategy_dependency
        ),
    }


def _native_trace_identity_preimage(trace: NativeFriTrace) -> dict[str, Any]:
    return {
        "kind": "NativeFriTrace",
        "version": 1,
        "profile_dependency": trace.profile.identity.to_term(),
        "core_shape": {
            "model": "two-round-native-logical-oracle-fri",
            "publication_effect": "fix-and-grant-logical-query-access",
            "query_expansion": "each-random-draw-to-o0-pair-then-o1-pair",
            "pair_answer_order": "positive-then-antipodal-negative",
            "verdict_check_order": [
                "exact-trace-shape",
                "first-fold-equality",
                "second-fold-terminal-equality",
                "terminal-semantic-degree-bound",
            ],
            "verdict_scope": "sampled-equations-only",
        },
        "initial_oracle": _oracle_identity_term(trace.initial_oracle),
        "first_challenge": {
            "name": trace.first_challenge.name,
            "value": trace.first_challenge.value.to_term(),
        },
        "prover_oracle": _oracle_identity_term(trace.prover_oracle),
        "second_challenge": {
            "name": trace.second_challenge.name,
            "value": trace.second_challenge.value.to_term(),
        },
        "terminal": {
            "coefficients": [
                coefficient.to_term() for coefficient in trace.terminal.coefficients
            ],
            "declared_strategy_dependency": _declared_dependency_term(
                trace.terminal.declared_strategy_dependency
            ),
        },
        "ordered_random_query_draws": [
            {
                "ordinal": draw.ordinal,
                "initial_domain_index": draw.initial_domain_index,
            }
            for draw in trace.query_draws
        ],
        "events": [
            {
                "index": event.index,
                "kind": event.kind.value,
                "subject": event.subject,
            }
            for event in trace.events
        ],
        "structural_records": trace.structural_chain.to_term(),
    }


def _oracle_from_values(
    name: str,
    domain: EvaluationDomain,
    origin: OracleOrigin,
    values: tuple[Fp2, ...],
    declared_dependency: DeclaredStrategyDependency | None,
) -> LogicalOracle:
    entries = tuple(
        OracleEntry(point, value)
        for point, value in zip(domain.points(), values, strict=True)
    )
    return LogicalOracle(name, domain, origin, entries, declared_dependency)


def _trim_polynomial(coefficients: list[Fp2]) -> tuple[Fp2, ...]:
    while len(coefficients) > 1 and coefficients[-1] == Fp2.zero():
        coefficients.pop()
    return tuple(coefficients)


def _fold_coefficients(
    coefficients: tuple[Fp2, ...],
    challenge: Fp2,
    target_count: int,
    resources: ResourceCounter,
) -> tuple[Fp2, ...]:
    padded = list(coefficients) + [Fp2.zero()] * (2 * target_count - len(coefficients))
    resources.consume_field_operations(target_count * COEFFICIENT_FOLD_FIELD_OPERATIONS)
    folded = [
        padded[2 * index] + challenge * padded[2 * index + 1]
        for index in range(target_count)
    ]
    return _trim_polynomial(folded)


def derive_honest_native_trace(
    coefficients: tuple[Fp2, ...],
    beta0: Fp2,
    beta1: Fp2,
    query_draws: tuple[int, ...],
    resources: ResourceCounter,
) -> NativeFriTrace:
    """Derive the honest trace for supplied fresh coins and query draws.

    The polynomial is construction-private material.  It is used to produce
    the invocation-supplied initial oracle but does not become a protocol
    message or an inferred witness for any outer relation.
    """

    if not isinstance(resources, ResourceCounter):
        raise malformed(
            "native:honest-derivation",
            "FRI-IOR-NATIVE-024",
            "honest derivation requires a caller-owned ResourceCounter",
        )
    polynomial = canonical_polynomial(
        coefficients,
        EXACT_PROFILE.initial_degree_bound_exclusive,
    )
    if not isinstance(beta0, Fp2) or not isinstance(beta1, Fp2):
        raise malformed(
            "native:honest-derivation",
            "FRI-IOR-NATIVE-026",
            "honest derivation requires two Fp2 fresh challenges",
        )
    if not isinstance(query_draws, tuple) or not all(
        type(index) is int for index in query_draws
    ):
        raise malformed(
            "native:honest-derivation",
            "FRI-IOR-NATIVE-027",
            "honest query draws must be a tuple of integer domain indices",
        )
    if len(query_draws) != EXACT_PROFILE.ordered_query_count or any(
        not 0 <= index < D0.order for index in query_draws
    ):
        raise refusal(
            "native:honest-derivation",
            "FRI-IOR-NATIVE-028",
            "honest query draws must contain exactly four in-domain occurrences",
        )

    initial_values = tuple(
        evaluate_polynomial(polynomial, point, resources) for point in D0.points()
    )
    initial = _oracle_from_values(
        INITIAL_ORACLE_NAME,
        D0,
        OracleOrigin.INITIAL_ORACLE,
        initial_values,
        None,
    )

    first_layer_values = tuple(
        binary_fold(
            D0.points()[pair_index],
            initial_values[pair_index],
            initial_values[pair_index + D1.order],
            beta0,
            resources,
        )
        for pair_index in range(D1.order)
    )
    first_dependency = DeclaredStrategyDependency(
        PROVER_ORACLE_NAME,
        2,
        (INITIAL_ORACLE_NAME, FIRST_CHALLENGE_NAME),
    )
    first_layer = _oracle_from_values(
        PROVER_ORACLE_NAME,
        D1,
        OracleOrigin.PROVER_ORACLE,
        first_layer_values,
        first_dependency,
    )

    first_coefficients = _fold_coefficients(polynomial, beta0, D1.order // 2, resources)
    terminal_coefficients = _fold_coefficients(
        first_coefficients,
        beta1,
        D2.order // 2,
        resources,
    )
    terminal = TerminalPolynomial(
        terminal_coefficients,
        DeclaredStrategyDependency(
            TERMINAL_NAME,
            4,
            (PROVER_ORACLE_NAME, SECOND_CHALLENGE_NAME),
        ),
    )

    return NativeFriTrace(
        profile=EXACT_PROFILE,
        initial_oracle=initial,
        first_challenge=FreshChallenge(FIRST_CHALLENGE_NAME, beta0),
        prover_oracle=first_layer,
        second_challenge=FreshChallenge(SECOND_CHALLENGE_NAME, beta1),
        terminal=terminal,
        query_draws=tuple(
            RandomQueryDraw(ordinal, index) for ordinal, index in enumerate(query_draws)
        ),
        events=canonical_event_log(),
        structural_chain=canonical_structural_fold_chain(),
    )


def _reject(code: str, detail: str, **evidence: Any) -> CheckResult:
    return CheckResult(
        outcome=OutcomeClass.REFUSED,
        boundary="native:verification",
        code=code,
        detail=detail,
        evidence={"protocol_verdict": NativeVerdict.REJECT.value, **evidence},
    )


def _validate_oracle(
    oracle: LogicalOracle,
    *,
    expected_name: str,
    expected_domain: EvaluationDomain,
    expected_origin: OracleOrigin,
    expects_declared_dependency: bool,
) -> CheckResult | None:
    if oracle.publication_mode is not OraclePublicationMode.LOGICAL_ACCESS:
        return _reject(
            "FRI-IOR-NATIVE-029",
            "native FRI admits only fixation with logical query access",
        )
    if oracle.name != expected_name or oracle.domain != expected_domain:
        return _reject(
            "FRI-IOR-NATIVE-030",
            "an oracle does not occupy its exact declared name and domain",
        )
    if oracle.origin is not expected_origin:
        return _reject(
            "FRI-IOR-NATIVE-031",
            "initial and prover-authored oracle origins are not interchangeable",
            oracle=expected_name,
        )
    if (
        oracle.declared_strategy_dependency is not None
    ) is not expects_declared_dependency:
        return _reject(
            "FRI-IOR-NATIVE-032",
            "oracle replay-dependency metadata disagrees with its declared origin",
            oracle=expected_name,
        )
    expected_points = expected_domain.points()
    actual_points = tuple(entry.point for entry in oracle.entries)
    if actual_points != expected_points:
        return _reject(
            "FRI-IOR-NATIVE-033",
            "an exact logical oracle must contain every domain point once in canonical order",
            oracle=expected_name,
            expected_entry_count=len(expected_points),
            actual_entry_count=len(actual_points),
        )
    return None


def _validate_event_log(trace: NativeFriTrace) -> CheckResult | None:
    publications = tuple(
        event.subject
        for event in trace.events
        if event.kind is NativeEventKind.PUBLISH_ORACLE
    )
    if len(set(publications)) != len(publications):
        return _reject(
            "FRI-IOR-NATIVE-034",
            "a fixed logical oracle cannot be published or replaced a second time",
        )
    if trace.events != canonical_event_log():
        return _reject(
            "FRI-IOR-NATIVE-035",
            "native events do not have the required oracle, challenge, terminal, and query order",
        )
    return None


def _validate_declared_strategy_dependency(
    dependency: DeclaredStrategyDependency,
    *,
    expected_subject: str,
    expected_authored_at: int,
) -> CheckResult | None:
    if (
        dependency.subject != expected_subject
        or dependency.authored_at != expected_authored_at
    ):
        return _reject(
            "FRI-IOR-NATIVE-036",
            "declared replay dependencies are attached to the wrong event occurrence",
            subject=expected_subject,
        )
    if len(set(dependency.declared_read_set)) != len(dependency.declared_read_set):
        return _reject(
            "FRI-IOR-NATIVE-037",
            "a declared strategy read set must not repeat an object",
            subject=expected_subject,
        )
    occurrence_index = {
        INITIAL_ORACLE_NAME: 0,
        FIRST_CHALLENGE_NAME: 1,
        PROVER_ORACLE_NAME: 2,
        SECOND_CHALLENGE_NAME: 3,
        TERMINAL_NAME: 4,
        **{
            f"query-draw[{ordinal}]": 5 + ordinal
            for ordinal in range(EXACT_PROFILE.ordered_query_count)
        },
    }
    for read in dependency.declared_read_set:
        if read not in occurrence_index:
            return _reject(
                "FRI-IOR-NATIVE-038",
                "a declared strategy read names an object outside the protocol view",
                subject=expected_subject,
                read=read,
            )
        if occurrence_index[read] >= dependency.authored_at:
            return _reject(
                "FRI-IOR-NATIVE-039",
                "declared replay dependencies name a current or future object",
                subject=expected_subject,
                read=read,
            )
    return None


def _validate_trace_shape(trace: NativeFriTrace) -> CheckResult | None:
    profile_result = admit_exact_profile(trace.profile)
    if profile_result.outcome is not OutcomeClass.AFFIRMATIVE:
        return profile_result
    if (
        trace.first_challenge.name != FIRST_CHALLENGE_NAME
        or trace.second_challenge.name != SECOND_CHALLENGE_NAME
    ):
        return _reject(
            "FRI-IOR-NATIVE-041",
            "fresh challenges do not occupy their exact declared occurrences",
        )

    for oracle, name, domain, origin, authored in (
        (
            trace.initial_oracle,
            INITIAL_ORACLE_NAME,
            D0,
            OracleOrigin.INITIAL_ORACLE,
            False,
        ),
        (
            trace.prover_oracle,
            PROVER_ORACLE_NAME,
            D1,
            OracleOrigin.PROVER_ORACLE,
            True,
        ),
    ):
        invalid = _validate_oracle(
            oracle,
            expected_name=name,
            expected_domain=domain,
            expected_origin=origin,
            expects_declared_dependency=authored,
        )
        if invalid is not None:
            return invalid

    invalid_events = _validate_event_log(trace)
    if invalid_events is not None:
        return invalid_events

    assert trace.prover_oracle.declared_strategy_dependency is not None
    for dependency, subject, event_index in (
        (
            trace.prover_oracle.declared_strategy_dependency,
            PROVER_ORACLE_NAME,
            2,
        ),
        (trace.terminal.declared_strategy_dependency, TERMINAL_NAME, 4),
    ):
        invalid_dependency = _validate_declared_strategy_dependency(
            dependency,
            expected_subject=subject,
            expected_authored_at=event_index,
        )
        if invalid_dependency is not None:
            return invalid_dependency

    if len(trace.query_draws) != EXACT_PROFILE.ordered_query_count:
        return _reject(
            "FRI-IOR-NATIVE-042",
            "the native profile requires exactly four random query draws",
        )
    if tuple(draw.ordinal for draw in trace.query_draws) != tuple(
        range(EXACT_PROFILE.ordered_query_count)
    ):
        return _reject(
            "FRI-IOR-NATIVE-043",
            "random query draws must retain canonical ordinal order",
        )
    if any(not 0 <= draw.initial_domain_index < D0.order for draw in trace.query_draws):
        return _reject(
            "FRI-IOR-NATIVE-044",
            "a random query draw lies outside the initial domain",
        )

    if trace.structural_chain != canonical_structural_fold_chain():
        return _reject(
            "FRI-IOR-NATIVE-045",
            "the structural claim/reduction chain does not name the exact two folds",
        )
    return None


def _resolve_layer_query_answers(
    trace: NativeFriTrace,
) -> tuple[LayerQueryAnswerOccurrence, ...]:
    records: list[LayerQueryAnswerOccurrence] = []
    for draw in trace.query_draws:
        initial_pair_index = draw.initial_domain_index % D1.order
        first_fold_pair_index = initial_pair_index % D2.order
        records.extend(
            (
                LayerQueryAnswerOccurrence(
                    top_level_ordinal=draw.ordinal,
                    layer=NativeOracleLayer.INITIAL,
                    oracle_name=INITIAL_ORACLE_NAME,
                    pair_index=initial_pair_index,
                    positive_answer_index=initial_pair_index,
                    negative_answer_index=initial_pair_index + D1.order,
                    positive_value=trace.initial_oracle.logical_answer_at(
                        initial_pair_index
                    ),
                    negative_value=trace.initial_oracle.logical_answer_at(
                        initial_pair_index + D1.order
                    ),
                ),
                LayerQueryAnswerOccurrence(
                    top_level_ordinal=draw.ordinal,
                    layer=NativeOracleLayer.FIRST_FOLD,
                    oracle_name=PROVER_ORACLE_NAME,
                    pair_index=first_fold_pair_index,
                    positive_answer_index=first_fold_pair_index,
                    negative_answer_index=first_fold_pair_index + D2.order,
                    positive_value=trace.prover_oracle.logical_answer_at(
                        first_fold_pair_index
                    ),
                    negative_value=trace.prover_oracle.logical_answer_at(
                        first_fold_pair_index + D2.order
                    ),
                ),
            )
        )
    return tuple(records)


def resolve_layer_query_answers(
    candidate: object,
    resources: ResourceCounter,
) -> tuple[LayerQueryAnswerOccurrence, ...] | CheckResult:
    """Resolve compilation-facing pair answers after exact trace admission.

    The function exposes only the two queried antipodal pairs for each random
    draw.  It neither publishes nor returns either complete logical-oracle
    carrier.  Shape admission and the complete eight-occurrence resource
    reservation happen before the first oracle access.
    """

    boundary = "native:query-resolution"
    if not isinstance(candidate, NativeFriTrace):
        return CheckResult(
            OutcomeClass.MALFORMED,
            boundary,
            "FRI-IOR-NATIVE-054",
            "layer-query resolution requires a NativeFriTrace",
        )
    if not isinstance(resources, ResourceCounter):
        return CheckResult(
            OutcomeClass.MALFORMED,
            boundary,
            "FRI-IOR-NATIVE-055",
            "layer-query resolution requires a caller-owned ResourceCounter",
        )

    try:
        invalid = _validate_trace_shape(candidate)
        if invalid is not None:
            return invalid
        occurrence_count = 2 * len(candidate.query_draws)
        resources.consume_logical_query_occurrences(occurrence_count)
        return _resolve_layer_query_answers(candidate)
    except ModelFailure as error:
        return error.to_result()
    except Exception as error:  # pragma: no cover - fault-injection boundary
        return checker_failure(
            boundary,
            f"unexpected layer-query resolution failure: {type(error).__name__}",
        )


def verify_native_trace(
    candidate: object,
    resources: ResourceCounter,
) -> CheckResult:
    """Execute the exact native verifier over a caller-supplied trace."""

    boundary = "native:verification"
    if not isinstance(candidate, NativeFriTrace):
        return CheckResult(
            OutcomeClass.MALFORMED,
            boundary,
            "FRI-IOR-NATIVE-046",
            "native verification requires a NativeFriTrace",
        )
    if not isinstance(resources, ResourceCounter):
        return CheckResult(
            OutcomeClass.MALFORMED,
            boundary,
            "FRI-IOR-NATIVE-047",
            "native verification requires a caller-owned ResourceCounter",
        )

    try:
        layer_queries = resolve_layer_query_answers(candidate, resources)
        if isinstance(layer_queries, CheckResult):
            return layer_queries

        # Each draw expands to one O0 and one O1 pair query.  Equal draws stay
        # distinct, but every pair is fetched exactly once per occurrence.
        for draw, initial_query, first_fold_query in zip(
            candidate.query_draws,
            layer_queries[::2],
            layer_queries[1::2],
            strict=True,
        ):
            initial_index = draw.initial_domain_index
            first_index = initial_index % D1.order

            expected_first = binary_fold(
                D0.points()[initial_query.pair_index],
                initial_query.positive_value,
                initial_query.negative_value,
                candidate.beta0,
                resources,
            )
            first_fold_answers = dict(first_fold_query.ordered_answers)
            if expected_first != first_fold_answers[first_index]:
                return _reject(
                    "FRI-IOR-NATIVE-048",
                    "the first sampled binary-fold equation does not hold",
                    query_ordinal=draw.ordinal,
                    initial_domain_index=initial_index,
                )

            expected_terminal_value = binary_fold(
                D1.points()[first_fold_query.pair_index],
                first_fold_query.positive_value,
                first_fold_query.negative_value,
                candidate.beta1,
                resources,
            )
            terminal_value = evaluate_polynomial(
                candidate.terminal.coefficients,
                D2.points()[first_fold_query.pair_index],
                resources,
            )
            if expected_terminal_value != terminal_value:
                return _reject(
                    "FRI-IOR-NATIVE-049",
                    "the second sampled binary-fold equation does not hold",
                    query_ordinal=draw.ordinal,
                    initial_domain_index=initial_index,
                )

        if (
            polynomial_degree(candidate.terminal.coefficients)
            >= EXACT_PROFILE.terminal_degree_bound_exclusive
        ):
            return _reject(
                "FRI-IOR-NATIVE-050",
                "the terminal polynomial violates the semantic degree bound",
                terminal_degree=polynomial_degree(candidate.terminal.coefficients),
                degree_bound_exclusive=EXACT_PROFILE.terminal_degree_bound_exclusive,
            )

        query_indices = tuple(
            draw.initial_domain_index for draw in candidate.query_draws
        )
        unique_layer_pairs = {
            (query.layer, query.pair_index) for query in layer_queries
        }
        return affirmative(
            boundary,
            "FRI-IOR-NATIVE-100",
            "the exact native logical-oracle verifier accepted this trace",
            subject=candidate.identity,
            profile_dependency=candidate.profile.identity,
            protocol_verdict=NativeVerdict.ACCEPT.value,
            random_query_draw_count=len(query_indices),
            unique_random_query_index_count=len(set(query_indices)),
            ordered_random_query_indices=query_indices,
            logical_query_occurrence_count=len(layer_queries),
            unique_logical_pair_count=len(unique_layer_pairs),
            fold_checks=2 * len(query_indices),
            authentication_checks=0,
            declared_dependency_order_checked=True,
            establishes_strategy_nonanticipation=False,
            establishes_proximity=False,
            establishes_proximity_preservation=False,
            infers_outer_relation=False,
        )
    except ModelFailure as error:
        return error.to_result()
    except Exception as error:  # pragma: no cover - exercised with fault injection
        return checker_failure(
            boundary,
            f"unexpected native-verifier failure: {type(error).__name__}",
        )


__all__ = [
    "DeclaredStrategyDependency",
    "FIRST_CHALLENGE_NAME",
    "INITIAL_ORACLE_NAME",
    "LayerQueryAnswerOccurrence",
    "LogicalOracle",
    "NativeEvent",
    "NativeEventKind",
    "NativeFriTrace",
    "NativeOracleLayer",
    "NativeVerdict",
    "OracleEntry",
    "OracleOrigin",
    "OraclePublicationMode",
    "PROVER_ORACLE_NAME",
    "RandomQueryDraw",
    "SECOND_CHALLENGE_NAME",
    "StructuralFoldChain",
    "StructuralFoldReduction",
    "StructuralProximityClaim",
    "TERMINAL_NAME",
    "TerminalPolynomial",
    "canonical_event_log",
    "canonical_structural_fold_chain",
    "derive_honest_native_trace",
    "resolve_layer_query_answers",
    "verify_native_trace",
]
