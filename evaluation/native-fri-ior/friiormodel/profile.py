"""The one exact finite FRI algebra profile admitted by this package.

The profile is intentionally concrete.  A different generator, round count,
query-vector law, or fold evaluator is a well-formed but unsupported proposal;
it is not silently interpreted as this profile.  Commitment and transcript
choices are separate semantic subjects.  Request-local evaluator limits are
deliberately not profile semantics.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any

from .field import (
    EXTENSION_NONRESIDUE,
    MAX_POLYNOMIAL_COEFFICIENTS,
    MODULUS,
    PRIMITIVE_GENERATOR,
    Fp,
)
from .terms import (
    CheckResult,
    ModelFailure,
    OutcomeClass,
    ResourceLimits,
    SemanticId,
    affirmative,
    checker_failure,
    malformed,
    semantic_id,
    unsupported,
)


ALGEBRA_PROFILE_NAME = "zkc.fri-ior.f97-binary-two-round-algebra.v1"
FOLDING_ARITY = 2
INITIAL_DEGREE_BOUND_EXCLUSIVE = 8
TERMINAL_MAX_COEFFICIENT_COUNT = 5
TERMINAL_DEGREE_BOUND_EXCLUSIVE = 2
ROUND_COUNT = 2
ORDERED_QUERY_COUNT = 4
@dataclass(frozen=True, slots=True)
class SemanticLaw:
    """One versioned, closed semantic rule selected by the finite profile.

    A law identity names the mathematical or encoding rule itself.  It is not
    an implementation-source digest and says nothing about which checker
    implements the rule.  The ordered parameter and clause sequences are part
    of the law preimage, so changing an encoding byte, an equation, an order,
    or a projection rotates the law and every profile that selects it.
    """

    name: str
    version: int
    parameters: tuple[tuple[str, str | int | bool], ...]
    clauses: tuple[str, ...]

    def __post_init__(self) -> None:
        if (
            not isinstance(self.name, str)
            or not self.name
            or len(self.name) > 192
            or any(
                character not in "abcdefghijklmnopqrstuvwxyz0123456789.-_"
                for character in self.name
            )
        ):
            raise malformed(
                "profile:semantic-law-formation",
                "FRI-IOR-PROFILE-037",
                "a semantic law requires a bounded lower-case ASCII name",
            )
        if type(self.version) is not int or self.version <= 0:
            raise malformed(
                "profile:semantic-law-formation",
                "FRI-IOR-PROFILE-038",
                "a semantic law version must be a positive integer",
            )
        if (
            type(self.parameters) is not tuple
            or not self.parameters
            or any(
                type(item) is not tuple
                or len(item) != 2
                or not isinstance(item[0], str)
                or not item[0]
                or type(item[1]) not in (str, int, bool)
                for item in self.parameters
            )
            or len({item[0] for item in self.parameters}) != len(self.parameters)
        ):
            raise malformed(
                "profile:semantic-law-formation",
                "FRI-IOR-PROFILE-039",
                "semantic-law parameters must be a unique canonical scalar tuple",
            )
        if (
            type(self.clauses) is not tuple
            or not self.clauses
            or any(not isinstance(clause, str) or not clause for clause in self.clauses)
            or len(set(self.clauses)) != len(self.clauses)
        ):
            raise malformed(
                "profile:semantic-law-formation",
                "FRI-IOR-PROFILE-040",
                "a semantic law requires a non-empty unique clause sequence",
            )

    def to_term(self) -> dict[str, Any]:
        return {
            "name": self.name,
            "version": self.version,
            "parameters": [
                {"name": name, "value": value} for name, value in self.parameters
            ],
            "clauses": list(self.clauses),
        }

    @property
    def identity(self) -> SemanticId:
        return semantic_id(
            "fri-ior-semantic-law",
            "fri-ior.semantic-law.v1",
            self.to_term(),
        )


@dataclass(frozen=True, slots=True)
class OccurrenceMapLaw(SemanticLaw):
    """A semantic law whose subject is specifically an occurrence map."""

    @property
    def identity(self) -> SemanticId:
        return semantic_id(
            "fri-occurrence-map-law",
            "fri-ior.occurrence-map-law.v1",
            self.to_term(),
        )


BINARY_FOLD_EVALUATOR_LAW = SemanticLaw(
    name="binary-fri-fold-evaluator",
    version=1,
    parameters=(
        ("base-field", "F97"),
        ("extension-field", "F97-u-mod-u2-minus-5"),
        ("source-pair", "x-then-minus-x"),
        ("target-point", "x-squared"),
        ("challenge-type", "F97Extension2"),
    ),
    clauses=(
        "x-must-be-nonzero",
        "even-equals-positive-plus-negative-times-inverse-of-two",
        "odd-equals-positive-minus-negative-times-inverse-of-two-x",
        "fold-output-equals-even-plus-challenge-times-odd",
    ),
)

DIRECT_QUERY_VECTOR_LAW = SemanticLaw(
    name="ordered-direct-query-vector",
    version=1,
    parameters=(
        ("owner", "native-public-environment"),
        ("distribution", "independent-uniform-with-replacement"),
        ("domain-size", 16),
        ("occurrence-count", ORDERED_QUERY_COUNT),
        ("occurrence-identity", "zero-based-vector-ordinal"),
    ),
    clauses=(
        "the-public-environment-supplies-one-index-per-vector-ordinal",
        "each-index-is-sampled-uniformly-from-the-initial-domain",
        "draws-are-independent-and-sampling-is-with-replacement",
        "equal-indices-remain-distinct-occurrences",
        "vector-order-and-multiplicity-are-semantic",
    ),
)

QUERY_ANSWER_PROJECTION_LAW = OccurrenceMapLaw(
    name="fri-layer-query-answer-projection",
    version=1,
    parameters=(
        ("initial-domain-order", 16),
        ("first-fold-domain-order", 8),
        ("terminal-domain-order", 4),
        ("layer-order", "initial-then-first-fold"),
        ("pair-answer-order", "positive-then-antipodal-negative"),
    ),
    clauses=(
        "initial-layer-pair-index-is-top-level-index-modulo-eight",
        "initial-layer-answer-indices-are-pair-index-then-pair-index-plus-eight",
        "first-fold-layer-pair-index-is-top-level-index-modulo-four",
        "first-fold-layer-answer-indices-are-pair-index-then-pair-index-plus-four",
        "top-level-ordinal-order-and-multiplicity-are-preserved-across-both-layers",
    ),
)

TERMINAL_EVALUATOR_LAW = SemanticLaw(
    name="fri-terminal-polynomial-evaluator",
    version=1,
    parameters=(
        ("coefficient-field", "F97Extension2"),
        ("coefficient-order", "ascending-degree"),
        ("evaluation-algorithm", "horner-from-highest-coefficient"),
        ("maximum-coefficient-count", TERMINAL_MAX_COEFFICIENT_COUNT),
        ("degree-bound-exclusive", TERMINAL_DEGREE_BOUND_EXCLUSIVE),
        ("zero-polynomial", "one-zero-coefficient-with-degree-minus-one"),
        ("evaluation-domain", "D2"),
    ),
    clauses=(
        "nonzero-polynomial-final-coefficient-must-be-nonzero",
        "terminal-point-is-D2-at-top-level-query-index-modulo-four",
        "terminal-evaluation-must-equal-the-second-binary-fold-output",
        "terminal-degree-must-be-strictly-less-than-two",
    ),
)

EXACT_ALGEBRA_LAWS = (
    BINARY_FOLD_EVALUATOR_LAW,
    DIRECT_QUERY_VECTOR_LAW,
    QUERY_ANSWER_PROJECTION_LAW,
    TERMINAL_EVALUATOR_LAW,
)

# This is a request-local evaluator default, not part of ``FriAlgebraProfile`` and
# not an input to the profile's semantic identity.  A later ValidationBasis may
# select any admitted limits at or below the evaluator hard caps.
DEFAULT_VALIDATION_LIMITS = ResourceLimits(
    field_operations=1024,
    hash_calls=128,
    hash_bytes=1 << 15,
    merkle_nodes=128,
    transcript_frames=128,
    sampler_attempts=1024,
    grinding_trials=1 << 16,
    logical_query_occurrences=64,
    unique_openings=64,
    proof_bytes=1 << 16,
)


@dataclass(frozen=True, slots=True)
class EvaluationDomain:
    """A power-of-two multiplicative subgroup in fixed canonical order."""

    name: str
    generator: Fp
    order: int

    def __post_init__(self) -> None:
        if not isinstance(self.name, str) or not self.name:
            raise malformed(
                "profile:domain-formation",
                "FRI-IOR-PROFILE-001",
                "an evaluation domain requires a non-empty name",
            )
        if not isinstance(self.generator, Fp):
            raise malformed(
                "profile:domain-formation",
                "FRI-IOR-PROFILE-002",
                "an evaluation-domain generator must be an Fp element",
            )
        if (
            type(self.order) is not int
            or self.order < 2
            or self.order & (self.order - 1)
        ):
            raise malformed(
                "profile:domain-formation",
                "FRI-IOR-PROFILE-003",
                "an evaluation-domain order must be a power of two of at least two",
            )
        if self.generator**self.order != Fp(1):
            raise malformed(
                "profile:domain-formation",
                "FRI-IOR-PROFILE-004",
                "the declared generator does not generate a subgroup of its order",
            )
        if self.generator ** (self.order // 2) == Fp(1):
            raise malformed(
                "profile:domain-formation",
                "FRI-IOR-PROFILE-005",
                "the declared generator has order smaller than the domain",
            )

    def points(self) -> tuple[Fp, ...]:
        return tuple(self.generator**index for index in range(self.order))

    def antipodal_index_pairs(self) -> tuple[tuple[int, int], ...]:
        half = self.order // 2
        return tuple((index, index + half) for index in range(half))

    def to_term(self) -> dict[str, Any]:
        return {
            "name": self.name,
            "generator": self.generator.value,
            "order": self.order,
            "point_order": "successive-generator-powers",
            "pairing": "first-half-index-with-index-plus-half-order",
        }


@dataclass(frozen=True, slots=True)
class FriAlgebraProfile:
    """The algebra, fold, direct-query, and terminal choices of native FRI."""

    name: str
    modulus: int
    primitive_generator: int
    extension_nonresidue: int
    domains: tuple[EvaluationDomain, ...]
    folding_arity: int
    initial_degree_bound_exclusive: int
    terminal_max_coefficient_count: int
    terminal_degree_bound_exclusive: int
    round_count: int
    ordered_query_count: int
    query_occurrences_preserve_order_and_multiplicity: bool
    semantic_laws: tuple[SemanticLaw, ...]

    def __post_init__(self) -> None:
        integer_fields = (
            "modulus",
            "primitive_generator",
            "extension_nonresidue",
            "folding_arity",
            "initial_degree_bound_exclusive",
            "terminal_max_coefficient_count",
            "terminal_degree_bound_exclusive",
            "round_count",
            "ordered_query_count",
        )
        if not isinstance(self.name, str) or not self.name:
            raise malformed(
                "profile:formation",
                "FRI-IOR-PROFILE-006",
                "a finite profile requires a non-empty name",
            )
        if any(type(getattr(self, name)) is not int for name in integer_fields):
            raise malformed(
                "profile:formation",
                "FRI-IOR-PROFILE-007",
                "numeric profile parameters must be integers",
            )
        if (
            len(self.name) > 192
            or any(
                character not in "abcdefghijklmnopqrstuvwxyz0123456789.-_"
                for character in self.name
            )
        ):
            raise malformed(
                "profile:formation",
                "FRI-IOR-PROFILE-024",
                "a profile name must be a bounded lower-case ASCII identifier",
            )
        if self.modulus != MODULUS:
            raise malformed(
                "profile:formation",
                "FRI-IOR-PROFILE-025",
                "this finite profile carrier uses Fp values and therefore requires modulus 97",
            )
        if not 1 < self.primitive_generator < self.modulus or (
            pow(self.primitive_generator, self.modulus - 1, self.modulus) != 1
            or pow(self.primitive_generator, (self.modulus - 1) // 2, self.modulus)
            == 1
            or pow(self.primitive_generator, (self.modulus - 1) // 3, self.modulus)
            == 1
        ):
            raise malformed(
                "profile:formation",
                "FRI-IOR-PROFILE-026",
                "the declared primitive generator must have order 96 in F_97",
            )
        if not 0 < self.extension_nonresidue < self.modulus or pow(
            self.extension_nonresidue,
            (self.modulus - 1) // 2,
            self.modulus,
        ) != self.modulus - 1:
            raise malformed(
                "profile:formation",
                "FRI-IOR-PROFILE-027",
                "the quadratic extension parameter must be a non-residue in F_97",
            )
        if not isinstance(self.domains, tuple) or not all(
            isinstance(domain, EvaluationDomain) for domain in self.domains
        ):
            raise malformed(
                "profile:formation",
                "FRI-IOR-PROFILE-008",
                "domains must be a canonical sequence of EvaluationDomain values",
            )
        if self.round_count < 1 or self.ordered_query_count < 1:
            raise malformed(
                "profile:formation",
                "FRI-IOR-PROFILE-012",
                "a profile requires at least one round and one query occurrence",
            )
        if len(self.domains) != self.round_count + 1:
            raise malformed(
                "profile:formation",
                "FRI-IOR-PROFILE-009",
                "binary folding requires one more domain than folding rounds",
            )
        if len({domain.name for domain in self.domains}) != len(self.domains):
            raise malformed(
                "profile:formation",
                "FRI-IOR-PROFILE-029",
                "evaluation-domain names must be unique",
            )
        if self.folding_arity != 2:
            raise malformed(
                "profile:formation",
                "FRI-IOR-PROFILE-010",
                "this object graph only forms binary-fold profiles",
            )
        if self.initial_degree_bound_exclusive <= 0:
            raise malformed(
                "profile:formation",
                "FRI-IOR-PROFILE-011",
                "the initial exclusive degree bound must be positive",
            )
        if self.initial_degree_bound_exclusive > self.domains[0].order:
            raise malformed(
                "profile:formation",
                "FRI-IOR-PROFILE-030",
                "the initial degree bound cannot exceed the initial evaluation domain",
            )
        if self.terminal_max_coefficient_count <= 0:
            raise malformed(
                "profile:formation",
                "FRI-IOR-PROFILE-019",
                "the terminal syntax must permit at least one coefficient",
            )
        if self.terminal_max_coefficient_count > MAX_POLYNOMIAL_COEFFICIENTS:
            raise malformed(
                "profile:formation",
                "FRI-IOR-PROFILE-031",
                "the terminal syntax exceeds the finite polynomial carrier",
            )
        if self.terminal_degree_bound_exclusive <= 0:
            raise malformed(
                "profile:formation",
                "FRI-IOR-PROFILE-020",
                "the terminal semantic degree bound must be positive",
            )
        if self.terminal_degree_bound_exclusive > self.domains[-1].order:
            raise malformed(
                "profile:formation",
                "FRI-IOR-PROFILE-032",
                "the terminal degree bound cannot exceed the final evaluation domain",
            )
        if self.terminal_max_coefficient_count < self.terminal_degree_bound_exclusive:
            raise malformed(
                "profile:formation",
                "FRI-IOR-PROFILE-023",
                "the terminal syntax cannot encode every polynomial inside its semantic bound",
            )
        expected_terminal_bound = self.initial_degree_bound_exclusive
        for _ in range(self.round_count):
            if expected_terminal_bound % self.folding_arity:
                raise malformed(
                    "profile:formation",
                    "FRI-IOR-PROFILE-021",
                    "the degree bound must divide exactly across every fold",
                )
            expected_terminal_bound //= self.folding_arity
        if self.terminal_degree_bound_exclusive != expected_terminal_bound:
            raise malformed(
                "profile:formation",
                "FRI-IOR-PROFILE-022",
                "the terminal semantic degree bound disagrees with the fold chain",
            )
        if self.ordered_query_count > 256:
            raise malformed(
                "profile:formation",
                "FRI-IOR-PROFILE-033",
                "the query-occurrence count exceeds the finite carrier",
            )
        if self.query_occurrences_preserve_order_and_multiplicity is not True:
            raise malformed(
                "profile:formation",
                "FRI-IOR-PROFILE-013",
                "query occurrences must preserve both order and multiplicity",
            )
        for current, following in zip(self.domains, self.domains[1:]):
            if current.order != 2 * following.order:
                raise malformed(
                    "profile:domain-chain",
                    "FRI-IOR-PROFILE-015",
                    "each binary fold must halve the evaluation-domain order",
                )
            if current.generator * current.generator != following.generator:
                raise malformed(
                    "profile:domain-chain",
                    "FRI-IOR-PROFILE-016",
                    "each target domain generator must square from its source",
                )
        if (
            type(self.semantic_laws) is not tuple
            or not self.semantic_laws
            or any(
                type(law) not in (SemanticLaw, OccurrenceMapLaw)
                for law in self.semantic_laws
            )
            or len({law.name for law in self.semantic_laws})
            != len(self.semantic_laws)
            or tuple(law.name for law in self.semantic_laws)
            != tuple(law.name for law in EXACT_ALGEBRA_LAWS)
            or len(self.semantic_laws) != 4
            or type(self.semantic_laws[2]) is not OccurrenceMapLaw
            or any(
                type(law) is not SemanticLaw
                for law in (
                    self.semantic_laws[0],
                    self.semantic_laws[1],
                    self.semantic_laws[3],
                )
            )
        ):
            raise malformed(
                "profile:formation",
                "FRI-IOR-PROFILE-041",
                "an algebra profile requires every exact semantic-law role once and in order",
            )
        fold_parameters = dict(self.semantic_laws[0].parameters)
        query_parameters = dict(self.semantic_laws[1].parameters)
        answer_parameters = dict(self.semantic_laws[2].parameters)
        terminal_parameters = dict(self.semantic_laws[3].parameters)
        if (
            fold_parameters.get("base-field") != "F97"
            or fold_parameters.get("extension-field")
            != "F97-u-mod-u2-minus-5"
            or query_parameters.get("domain-size") != self.domains[0].order
            or query_parameters.get("occurrence-count") != self.ordered_query_count
            or answer_parameters.get("initial-domain-order") != self.domains[0].order
            or answer_parameters.get("first-fold-domain-order")
            != self.domains[1].order
            or answer_parameters.get("terminal-domain-order") != self.domains[2].order
            or terminal_parameters.get("maximum-coefficient-count")
            != self.terminal_max_coefficient_count
            or terminal_parameters.get("degree-bound-exclusive")
            != self.terminal_degree_bound_exclusive
            or terminal_parameters.get("evaluation-domain") != self.domains[-1].name
        ):
            raise malformed(
                "profile:formation",
                "FRI-IOR-PROFILE-042",
                "semantic-law parameters contradict their algebra-profile fields",
            )

    def to_term(self) -> dict[str, Any]:
        return {
            "name": self.name,
            "field": {
                "modulus": self.modulus,
                "primitive_generator": self.primitive_generator,
                "extension": {
                    "degree": 2,
                    "polynomial": [
                        -self.extension_nonresidue,
                        0,
                        1,
                    ],
                },
            },
            "domains": [domain.to_term() for domain in self.domains],
            "folding_arity": self.folding_arity,
            "initial_degree_bound_exclusive": self.initial_degree_bound_exclusive,
            "terminal_representation": {
                "max_coefficient_count": self.terminal_max_coefficient_count,
                "zero_polynomial": "one-zero-coefficient",
                "nonzero_polynomial": "final-coefficient-must-be-nonzero",
            },
            "terminal_degree_bound_exclusive": self.terminal_degree_bound_exclusive,
            "round_count": self.round_count,
            "ordered_query_count": self.ordered_query_count,
            "query_occurrences_preserve_order_and_multiplicity": (
                self.query_occurrences_preserve_order_and_multiplicity
            ),
            # The profile binds law identities, not duplicated law bodies.  The
            # immutable ``SemanticLaw`` subjects above own those terms.  This
            # keeps repeated profile references compact without weakening the
            # identity edge: changing a law body rotates its ID and therefore
            # rotates this profile.
            "semantic_law_ids": [law.identity.to_term() for law in self.semantic_laws],
        }

    @property
    def identity(self) -> SemanticId:
        return semantic_id(
            "fri-algebra-profile",
            "fri-ior.algebra-profile.v1",
            self.to_term(),
        )


D0 = EvaluationDomain("D0", Fp(8), 16)
D1 = EvaluationDomain("D1", Fp(64), 8)
D2 = EvaluationDomain("D2", Fp(22), 4)

EXACT_ALGEBRA_PROFILE = FriAlgebraProfile(
    name=ALGEBRA_PROFILE_NAME,
    modulus=MODULUS,
    primitive_generator=PRIMITIVE_GENERATOR,
    extension_nonresidue=EXTENSION_NONRESIDUE,
    domains=(D0, D1, D2),
    folding_arity=FOLDING_ARITY,
    initial_degree_bound_exclusive=INITIAL_DEGREE_BOUND_EXCLUSIVE,
    terminal_max_coefficient_count=TERMINAL_MAX_COEFFICIENT_COUNT,
    terminal_degree_bound_exclusive=TERMINAL_DEGREE_BOUND_EXCLUSIVE,
    round_count=ROUND_COUNT,
    ordered_query_count=ORDERED_QUERY_COUNT,
    query_occurrences_preserve_order_and_multiplicity=True,
    semantic_laws=EXACT_ALGEBRA_LAWS,
)

# Transitional spelling for carriers outside this module.  Both names denote
# the same executable algebra type and object; there is no second profile or
# second semantic identity.
FriIorProfile = FriAlgebraProfile
EXACT_PROFILE = EXACT_ALGEBRA_PROFILE


def admit_exact_profile(candidate: object) -> CheckResult:
    """Admit only the exact finite profile, with typed fail-closed outcomes."""

    boundary = "profile:admission"
    if not isinstance(candidate, FriAlgebraProfile):
        return CheckResult(
            OutcomeClass.MALFORMED,
            boundary,
            "FRI-IOR-PROFILE-017",
            "profile admission requires a FriAlgebraProfile value",
        )
    try:
        candidate_term = candidate.to_term()
        exact_term = EXACT_ALGEBRA_PROFILE.to_term()
        if candidate_term != exact_term:
            return unsupported(
                boundary,
                "FRI-IOR-PROFILE-018",
                "the well-formed profile is not the exact profile this evaluator supports",
            )
        return affirmative(
            boundary,
            "FRI-IOR-PROFILE-100",
            "the exact finite FRI/IOR profile is admitted",
            subject=candidate.identity,
        )
    except ModelFailure as error:
        return error.to_result()
    except Exception as error:  # pragma: no cover - exercised with fault injection
        return checker_failure(
            boundary,
            f"unexpected profile-admission failure: {type(error).__name__}",
        )
