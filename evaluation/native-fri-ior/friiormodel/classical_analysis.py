"""Typed bounded Analysis pressure instruments for exact classical FRI.

This module deliberately forms questions and checks finite arithmetic only.  A
structural Algorithm 1 correspondence is not theorem truth, theorem
applicability, or a security judgment.  Likewise, a non-vacuous substitution
does not establish that the cited theorem applies to the selected protocol.
The soundness objects below are candidate questions, not durable catalog or
profile instances.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum
from fractions import Fraction
from math import gcd
from typing import Any

from .classical import (
    DEGREE_BOUNDS,
    DOMAIN_ORDERS,
    EXACT_CLASSICAL_FRI_PROFILE,
    FOLD_ROUNDS,
    GOLDILOCKS_MODULUS,
    LAYER_QUERY_OCCURRENCES,
    QUERY_REPETITIONS,
    ClassicalFriProfile,
    ClassicalNativeCore,
    EXACT_CLASSICAL_NATIVE_CORE,
)
from .classical_relations import (
    ClassicalProtocolRelationBinding,
    ExactRsProximityRelationInstance,
)
from .terms import (
    CheckResult,
    ModelFailure,
    OutcomeClass,
    SemanticId,
    affirmative,
    encode_term,
    kind_mismatch,
    malformed,
    refused,
    semantic_id,
)


GOLDILOCKS_FIELD_SIZE = GOLDILOCKS_MODULUS
DIRECT_FRI_SOURCE_DIGEST = (
    "bb7a7e87b9000c98106de99c9af9d289def2a1b91919a3507ee78bf9bfd16947"
)


def _semantic_ref(value: SemanticId) -> dict[str, Any]:
    if not isinstance(value, SemanticId):
        raise malformed(
            "classical-analysis:formation",
            "FRI-IOR-CLASSICAL-ANALYSIS-001",
            "an Analysis semantic reference requires a SemanticId",
        )
    return value.to_term()


class ClassicalPropertyFamily(str, Enum):
    """The two property families activated by this bounded control."""

    ROUND_BY_ROUND_SOUNDNESS = "RoundByRoundSoundness"
    RESTRICTED_STATE_RESTORATION_SOUNDNESS = (
        "RestrictedStateRestorationSoundness"
    )


class AnalysisEvaluationStatus(str, Enum):
    NOT_EVALUATED = "NotEvaluated"


class TheoremTruthStatus(str, Enum):
    NOT_ESTABLISHED = "NotEstablished"


class TheoremApplicabilityStatus(str, Enum):
    NOT_EVALUATED = "NotEvaluated"


class QuantitativeBoundClassification(str, Enum):
    NONVACUOUS = "NonVacuous"
    VACUOUS = "Vacuous"


@dataclass(frozen=True, slots=True)
class CanonicalRational:
    numerator: int
    denominator: int

    def __post_init__(self) -> None:
        if (
            type(self.numerator) is not int
            or type(self.denominator) is not int
            or self.denominator <= 0
            or gcd(abs(self.numerator), self.denominator) != 1
        ):
            raise malformed(
                "classical-analysis:rational-formation",
                "FRI-IOR-CLASSICAL-ANALYSIS-002",
                "a canonical rational requires a positive coprime denominator",
            )

    @classmethod
    def from_fraction(cls, value: Fraction) -> CanonicalRational:
        if type(value) is not Fraction:
            raise malformed(
                "classical-analysis:rational-formation",
                "FRI-IOR-CLASSICAL-ANALYSIS-003",
                "rational conversion requires an exact Fraction",
            )
        return cls(value.numerator, value.denominator)

    def to_term(self) -> dict[str, int]:
        return {
            "numerator": self.numerator,
            "denominator": self.denominator,
        }


@dataclass(frozen=True, slots=True)
class AnalysisExperimentProfile:
    name: str
    strategy_class: str
    scheduler_law: str
    observation_law: str
    resource_coordinates: tuple[str, ...]

    def __post_init__(self) -> None:
        if (
            type(self.name) is not str
            or not self.name
            or type(self.strategy_class) is not str
            or not self.strategy_class
            or type(self.scheduler_law) is not str
            or not self.scheduler_law
            or type(self.observation_law) is not str
            or not self.observation_law
            or type(self.resource_coordinates) is not tuple
            or not self.resource_coordinates
            or not all(
                type(item) is str and item for item in self.resource_coordinates
            )
            or len(set(self.resource_coordinates)) != len(self.resource_coordinates)
        ):
            raise malformed(
                "classical-analysis:experiment-formation",
                "FRI-IOR-CLASSICAL-ANALYSIS-004",
                "an experiment requires a closed non-duplicated typed description",
            )
        encode_term(self.to_term())

    def to_term(self) -> dict[str, Any]:
        return {
            "name": self.name,
            "strategy_class": self.strategy_class,
            "scheduler_law": self.scheduler_law,
            "observation_law": self.observation_law,
            "resource_coordinates": list(self.resource_coordinates),
        }

    @property
    def identity(self) -> SemanticId:
        return semantic_id(
            "analysis-experiment-profile",
            "fri-ior.classical-analysis.experiment.v1",
            self.to_term(),
        )


ROUND_BY_ROUND_EXPERIMENT = AnalysisExperimentProfile(
    "classical-fri-round-by-round-doomed-prefix",
    "adaptive-prover-strategy-with-nonanticipation",
    "round-indexed-doomed-prefix-persistence",
    "acceptance-on-a-delta-far-reed-solomon-oracle",
    (
        "round-index",
        "logical-query-occurrences",
        "field-operations",
    ),
)

RESTRICTED_RESTORATION_EXPERIMENT = AnalysisExperimentProfile(
    "classical-fri-restricted-state-restoration",
    "adaptive-prover-strategy-with-restorable-state",
    "branch-extension-budget-and-no-empty-state-return",
    "acceptance-after-restricted-restoration",
    (
        "restoration-branch-extensions",
        "logical-query-occurrences",
        "field-operations",
    ),
)


@dataclass(frozen=True, slots=True)
class DirectFriTheoremSchema:
    """Semantic theorem statement; source bytes are deliberately absent."""

    result_family: ClassicalPropertyFamily = field(
        default=ClassicalPropertyFamily.ROUND_BY_ROUND_SOUNDNESS,
        init=False,
    )
    algorithm_profile: str = field(
        default="smooth-multiplicative-binary-fri-algorithm-one",
        init=False,
    )
    experiment_law: str = field(
        default="round-by-round-doomed-prefix-soundness",
        init=False,
    )
    quantitative_law: str = field(
        default=(
            "max(((m+1/2)^7*N^2)/(3*rho^(3/2)*field_size),"
            "(1-delta)^ell)"
        ),
        init=False,
    )
    quantified_parameters: tuple[str, ...] = field(
        default=(
            "n",
            "k",
            "eta",
            "m",
            "N",
            "rho",
            "field_size",
            "delta",
            "ell",
        ),
        init=False,
    )
    standing_side_conditions: tuple[str, ...] = field(
        default=(
            "eta-is-positive",
            "eta-is-less-than-sqrt-rho-over-two-m",
            "delta-is-less-than-one-minus-sqrt-rho-minus-eta",
            "k-is-at-most-n-over-two",
        ),
        init=False,
    )

    def to_term(self) -> dict[str, Any]:
        return {
            "result_family": self.result_family.value,
            "algorithm_profile": self.algorithm_profile,
            "experiment_law": self.experiment_law,
            "quantitative_law": self.quantitative_law,
            "quantified_parameters": list(self.quantified_parameters),
            "standing_side_conditions": list(self.standing_side_conditions),
        }

    @property
    def identity(self) -> SemanticId:
        return semantic_id(
            "analysis-theorem-schema",
            "fri-ior.classical-analysis.direct-fri-theorem.v1",
            self.to_term(),
        )


DIRECT_FRI_THEOREM_SCHEMA = DirectFriTheoremSchema()


@dataclass(frozen=True, slots=True)
class TheoremSourceValidation:
    theorem_schema_id: SemanticId
    artifact_digest: str
    source_revision: str
    ordered_locators: tuple[str, ...]

    def __post_init__(self) -> None:
        _semantic_ref(self.theorem_schema_id)
        if (
            type(self.artifact_digest) is not str
            or len(self.artifact_digest) != 64
            or any(character not in "0123456789abcdef" for character in self.artifact_digest)
            or type(self.source_revision) is not str
            or not self.source_revision
            or type(self.ordered_locators) is not tuple
            or not self.ordered_locators
            or not all(type(item) is str and item for item in self.ordered_locators)
        ):
            raise malformed(
                "classical-analysis:source-validation-formation",
                "FRI-IOR-CLASSICAL-ANALYSIS-005",
                "source validation requires exact digest, revision, and locators",
            )
        encode_term(self.to_term())

    def to_term(self) -> dict[str, Any]:
        return {
            "theorem_schema_id": _semantic_ref(self.theorem_schema_id),
            "artifact_digest": self.artifact_digest,
            "source_revision": self.source_revision,
            "ordered_locators": list(self.ordered_locators),
        }

    @property
    def identity(self) -> SemanticId:
        return semantic_id(
            "analysis-theorem-source-validation",
            "fri-ior.classical-analysis.source-validation.v1",
            self.to_term(),
        )


DIRECT_FRI_SOURCE_VALIDATION = TheoremSourceValidation(
    DIRECT_FRI_THEOREM_SCHEMA.identity,
    DIRECT_FRI_SOURCE_DIGEST,
    "eprint-2023-1071-revision-7",
    ("Theorem 4.1", "Section 5.7 Algorithm 1"),
)


_STRUCTURAL_CORRESPONDENCE_TOKEN = object()


@dataclass(frozen=True, slots=True, init=False)
class CheckedAlgorithmOneStructuralCorrespondence:
    """Checked exact shape only; never a theorem or property capability."""

    profile_id: SemanticId
    native_core_id: SemanticId
    fold_count: int
    committed_oracle_layers: int
    terminal_kind: str
    query_repetitions: int
    logical_layer_query_occurrences: int

    def __init__(
        self,
        profile_id: SemanticId,
        native_core_id: SemanticId,
        *,
        _token: object,
    ) -> None:
        if _token is not _STRUCTURAL_CORRESPONDENCE_TOKEN:
            raise malformed(
                "classical-analysis:structural-correspondence-formation",
                "FRI-IOR-CLASSICAL-ANALYSIS-006",
                "structural correspondence is checker-issued",
            )
        object.__setattr__(self, "profile_id", profile_id)
        object.__setattr__(self, "native_core_id", native_core_id)
        object.__setattr__(self, "fold_count", FOLD_ROUNDS)
        object.__setattr__(self, "committed_oracle_layers", FOLD_ROUNDS)
        object.__setattr__(self, "terminal_kind", "scalar")
        object.__setattr__(self, "query_repetitions", QUERY_REPETITIONS)
        object.__setattr__(
            self,
            "logical_layer_query_occurrences",
            LAYER_QUERY_OCCURRENCES,
        )
        encode_term(self.to_term())

    def to_term(self) -> dict[str, Any]:
        return {
            "profile_id": _semantic_ref(self.profile_id),
            "native_core_id": _semantic_ref(self.native_core_id),
            "fold_count": self.fold_count,
            "committed_oracle_layers": self.committed_oracle_layers,
            "terminal_kind": self.terminal_kind,
            "query_repetitions": self.query_repetitions,
            "logical_layer_query_occurrences": (
                self.logical_layer_query_occurrences
            ),
            "establishes_theorem_truth": False,
            "establishes_theorem_applicability": False,
            "establishes_security_property": False,
        }

    @property
    def identity(self) -> SemanticId:
        return semantic_id(
            "checked-protocol-correspondence",
            "fri-ior.classical-analysis.algorithm-one-shape.v1",
            self.to_term(),
        )


@dataclass(frozen=True, slots=True)
class StructuralCorrespondenceAdmission:
    result: CheckResult
    checked: CheckedAlgorithmOneStructuralCorrespondence | None


def check_algorithm_one_structural_correspondence(
    profile: object,
    native_core: object,
) -> StructuralCorrespondenceAdmission:
    boundary = "classical-analysis:algorithm-one-correspondence"
    if type(profile) is not ClassicalFriProfile:
        return StructuralCorrespondenceAdmission(
            CheckResult(
                OutcomeClass.MALFORMED,
                boundary,
                "FRI-IOR-CLASSICAL-ANALYSIS-007",
                "Algorithm 1 correspondence requires a ClassicalFriProfile",
            ),
            None,
        )
    if profile.identity != EXACT_CLASSICAL_FRI_PROFILE.identity:
        return StructuralCorrespondenceAdmission(
            refused(
                boundary,
                "FRI-IOR-CLASSICAL-ANALYSIS-008",
                "the supplied profile is not the exact three-fold scalar-terminal control",
            ),
            None,
        )
    if (
        type(native_core) is not ClassicalNativeCore
        or native_core.identity != EXACT_CLASSICAL_NATIVE_CORE.identity
        or native_core.profile_id != profile.identity
    ):
        return StructuralCorrespondenceAdmission(
            kind_mismatch(
                boundary,
                "FRI-IOR-CLASSICAL-ANALYSIS-022",
                "Algorithm 1 correspondence requires the exact native Core",
            ),
            None,
        )
    checked = CheckedAlgorithmOneStructuralCorrespondence(
        profile.identity,
        native_core.identity,
        _token=_STRUCTURAL_CORRESPONDENCE_TOKEN,
    )
    return StructuralCorrespondenceAdmission(
        affirmative(
            boundary,
            "FRI-IOR-CLASSICAL-ANALYSIS-100",
            "the exact finite profile has the selected Algorithm 1 structural shape",
            subject=checked.identity,
            theorem_true=None,
            theorem_applicable=None,
            property_established=None,
        ),
        checked,
    )


@dataclass(frozen=True, slots=True)
class RoundByRoundSoundnessQuestion:
    profile_id: SemanticId
    native_core_id: SemanticId
    relation_instance_id: SemanticId
    relation_binding_id: SemanticId
    structural_correspondence_id: SemanticId
    experiment_id: SemanticId = field(
        default=ROUND_BY_ROUND_EXPERIMENT.identity,
        init=False,
    )
    family: ClassicalPropertyFamily = field(
        default=ClassicalPropertyFamily.ROUND_BY_ROUND_SOUNDNESS,
        init=False,
    )
    evaluation_status: AnalysisEvaluationStatus = field(
        default=AnalysisEvaluationStatus.NOT_EVALUATED,
        init=False,
    )

    def __post_init__(self) -> None:
        for value in (
            self.profile_id,
            self.native_core_id,
            self.relation_instance_id,
            self.relation_binding_id,
            self.structural_correspondence_id,
            self.experiment_id,
        ):
            _semantic_ref(value)
        encode_term(self.to_term())

    def to_term(self) -> dict[str, Any]:
        return {
            "family": self.family.value,
            "profile_id": _semantic_ref(self.profile_id),
            "native_core_id": _semantic_ref(self.native_core_id),
            "relation_instance_id": _semantic_ref(self.relation_instance_id),
            "relation_binding_id": _semantic_ref(self.relation_binding_id),
            "structural_correspondence_id": _semantic_ref(
                self.structural_correspondence_id
            ),
            "experiment_id": _semantic_ref(self.experiment_id),
            "evaluation_status": self.evaluation_status.value,
            "catalog_status": "CandidateQuestion",
            "durable_promotion_ready": False,
            "establishes_property": False,
        }

    @property
    def identity(self) -> SemanticId:
        return semantic_id(
            "analysis-question",
            "fri-ior.classical-analysis.round-by-round.v1",
            self.to_term(),
        )


def form_round_by_round_soundness_question(
    profile: object,
    native_core_id: object,
    relation_instance: object,
    relation_binding: object,
    structural_correspondence: object,
) -> RoundByRoundSoundnessQuestion:
    if type(profile) is not ClassicalFriProfile:
        raise malformed(
            "classical-analysis:question-formation",
            "FRI-IOR-CLASSICAL-ANALYSIS-009",
            "round-by-round formation requires a ClassicalFriProfile",
        )
    if (
        type(structural_correspondence)
        is not CheckedAlgorithmOneStructuralCorrespondence
        or structural_correspondence.profile_id != profile.identity
        or structural_correspondence.native_core_id != native_core_id
    ):
        raise ModelFailure(
            OutcomeClass.KIND_MISMATCH,
            "classical-analysis:question-formation",
            "FRI-IOR-CLASSICAL-ANALYSIS-010",
            "the question requires the matching checked structural correspondence",
        )
    if not isinstance(native_core_id, SemanticId):
        raise malformed(
            "classical-analysis:question-formation",
            "FRI-IOR-CLASSICAL-ANALYSIS-011",
            "round-by-round question formation requires a native Core identity",
        )
    if (
        type(relation_instance) is not ExactRsProximityRelationInstance
        or type(relation_binding) is not ClassicalProtocolRelationBinding
        or relation_binding.relation_instance_id != relation_instance.identity
        or relation_binding.native_core_id != native_core_id
    ):
        raise ModelFailure(
            OutcomeClass.KIND_MISMATCH,
            "classical-analysis:question-formation",
            "FRI-IOR-CLASSICAL-ANALYSIS-023",
            "the question requires its exact RS relation instance and binding",
        )
    return RoundByRoundSoundnessQuestion(
        profile.identity,
        native_core_id,
        relation_instance.identity,
        relation_binding.identity,
        structural_correspondence.identity,
    )


@dataclass(frozen=True, slots=True)
class RestrictedStateRestorationSoundnessQuestion:
    source_round_by_round_question_id: SemanticId
    branch_extension_budget: int
    experiment_id: SemanticId = field(
        default=RESTRICTED_RESTORATION_EXPERIMENT.identity,
        init=False,
    )
    family: ClassicalPropertyFamily = field(
        default=ClassicalPropertyFamily.RESTRICTED_STATE_RESTORATION_SOUNDNESS,
        init=False,
    )
    evaluation_status: AnalysisEvaluationStatus = field(
        default=AnalysisEvaluationStatus.NOT_EVALUATED,
        init=False,
    )

    def __post_init__(self) -> None:
        _semantic_ref(self.source_round_by_round_question_id)
        _semantic_ref(self.experiment_id)
        if type(self.branch_extension_budget) is not int or self.branch_extension_budget <= 0:
            raise malformed(
                "classical-analysis:question-formation",
                "FRI-IOR-CLASSICAL-ANALYSIS-012",
                "restricted restoration requires a positive branch-extension budget",
            )
        encode_term(self.to_term())

    def to_term(self) -> dict[str, Any]:
        return {
            "family": self.family.value,
            "source_round_by_round_question_id": _semantic_ref(
                self.source_round_by_round_question_id
            ),
            "branch_extension_budget": self.branch_extension_budget,
            "experiment_id": _semantic_ref(self.experiment_id),
            "scheduler_law": "no-empty-state-return",
            "evaluation_status": self.evaluation_status.value,
            "catalog_status": "CandidateQuestion",
            "durable_promotion_ready": False,
            "establishes_source_property": False,
            "establishes_target_property": False,
        }

    @property
    def identity(self) -> SemanticId:
        return semantic_id(
            "analysis-question",
            "fri-ior.classical-analysis.restricted-restoration.v1",
            self.to_term(),
        )


def form_restricted_state_restoration_question(
    source_question: object,
    branch_extension_budget: int,
) -> RestrictedStateRestorationSoundnessQuestion:
    if type(source_question) is not RoundByRoundSoundnessQuestion:
        raise malformed(
            "classical-analysis:question-formation",
            "FRI-IOR-CLASSICAL-ANALYSIS-013",
            "restoration formation requires a round-by-round question",
        )
    return RestrictedStateRestorationSoundnessQuestion(
        source_question.identity,
        branch_extension_budget,
    )


@dataclass(frozen=True, slots=True)
class DirectFriQuantitativeQuestion:
    round_by_round_question_id: SemanticId
    structural_correspondence_id: SemanticId
    theorem_schema_id: SemanticId = field(
        default=DIRECT_FRI_THEOREM_SCHEMA.identity,
        init=False,
    )
    source_validation_id: SemanticId = field(
        default=DIRECT_FRI_SOURCE_VALIDATION.identity,
        init=False,
    )
    theorem_truth_status: TheoremTruthStatus = field(
        default=TheoremTruthStatus.NOT_ESTABLISHED,
        init=False,
    )
    theorem_applicability_status: TheoremApplicabilityStatus = field(
        default=TheoremApplicabilityStatus.NOT_EVALUATED,
        init=False,
    )

    def __post_init__(self) -> None:
        for value in (
            self.round_by_round_question_id,
            self.structural_correspondence_id,
            self.theorem_schema_id,
            self.source_validation_id,
        ):
            _semantic_ref(value)
        encode_term(self.to_term())

    def to_term(self) -> dict[str, Any]:
        return {
            "round_by_round_question_id": _semantic_ref(
                self.round_by_round_question_id
            ),
            "structural_correspondence_id": _semantic_ref(
                self.structural_correspondence_id
            ),
            "theorem_schema_id": _semantic_ref(self.theorem_schema_id),
            "source_validation_id": _semantic_ref(self.source_validation_id),
            "theorem_truth_status": self.theorem_truth_status.value,
            "theorem_applicability_status": (
                self.theorem_applicability_status.value
            ),
            "property_established": False,
        }

    @property
    def identity(self) -> SemanticId:
        return semantic_id(
            "analysis-quantitative-question",
            "fri-ior.classical-analysis.direct-fri-quantitative.v1",
            self.to_term(),
        )


def form_direct_fri_quantitative_question(
    round_by_round_question: object,
    structural_correspondence: object,
) -> DirectFriQuantitativeQuestion:
    if type(round_by_round_question) is not RoundByRoundSoundnessQuestion:
        raise malformed(
            "classical-analysis:quantitative-question-formation",
            "FRI-IOR-CLASSICAL-ANALYSIS-014",
            "a direct-FRI question requires a round-by-round question",
        )
    if (
        type(structural_correspondence)
        is not CheckedAlgorithmOneStructuralCorrespondence
        or round_by_round_question.structural_correspondence_id
        != structural_correspondence.identity
    ):
        raise ModelFailure(
            OutcomeClass.KIND_MISMATCH,
            "classical-analysis:quantitative-question-formation",
            "FRI-IOR-CLASSICAL-ANALYSIS-015",
            "the direct-FRI question requires the same structural correspondence",
        )
    return DirectFriQuantitativeQuestion(
        round_by_round_question.identity,
        structural_correspondence.identity,
    )


@dataclass(frozen=True, slots=True)
class DirectFriBoundEvaluation:
    question_id: SemanticId
    profile_id: SemanticId
    field_size: int
    domain_size: int
    rate: CanonicalRational
    theorem_m: int
    protocol_fold_rounds: int
    domain_log: int
    degree_log: int
    localization_arity: int
    localization_log: int
    johnson_slack_eta: CanonicalRational
    eta_range_condition_holds: bool
    delta_range_condition_holds: bool
    standing_k_at_most_n_over_two: bool
    distance: CanonicalRational
    query_repetitions: int
    first_term_squared: CanonicalRational
    second_term: CanonicalRational
    selected_upper_bound: CanonicalRational
    dominant_term: str
    classification: QuantitativeBoundClassification
    theorem_truth_status: TheoremTruthStatus = field(
        default=TheoremTruthStatus.NOT_ESTABLISHED,
        init=False,
    )
    theorem_applicability_status: TheoremApplicabilityStatus = field(
        default=TheoremApplicabilityStatus.NOT_EVALUATED,
        init=False,
    )

    def __post_init__(self) -> None:
        _semantic_ref(self.question_id)
        _semantic_ref(self.profile_id)
        if (
            self.question_id.subject_kind != "analysis-quantitative-question"
            or self.profile_id != EXACT_CLASSICAL_FRI_PROFILE.identity
            or self.field_size != GOLDILOCKS_FIELD_SIZE
            or self.domain_size != DOMAIN_ORDERS[0]
            or self.rate != CanonicalRational(1, 8)
            or self.theorem_m != 3
            or self.protocol_fold_rounds != FOLD_ROUNDS
            or self.domain_log != 6
            or self.degree_log != 3
            or self.localization_arity != 2
            or self.localization_log != 1
            or self.johnson_slack_eta != CanonicalRational(1, 20)
            or not self.eta_range_condition_holds
            or not self.delta_range_condition_holds
            or not self.standing_k_at_most_n_over_two
            or self.distance != CanonicalRational(1, 2)
            or self.query_repetitions != QUERY_REPETITIONS
            or self.first_term_squared
            != CanonicalRational(
                355584218417856512,
                3062541300862339246411675480114971279369,
            )
            or self.second_term != CanonicalRational(1, 16)
            or self.selected_upper_bound != CanonicalRational(1, 16)
            or self.dominant_term != "repetition-term"
            or self.classification is not QuantitativeBoundClassification.NONVACUOUS
        ):
            raise malformed(
                "classical-analysis:bound-evaluation-formation",
                "FRI-IOR-CLASSICAL-ANALYSIS-024",
                "the exact selected bound evaluation has fixed checked coordinates",
            )
        encode_term(self.to_term())

    def to_term(self) -> dict[str, Any]:
        return {
            "question_id": _semantic_ref(self.question_id),
            "profile_id": _semantic_ref(self.profile_id),
            "parameters": {
                "field_size": self.field_size,
                "N": self.domain_size,
                "rho": self.rate.to_term(),
                "n": self.domain_log,
                "k": self.degree_log,
                "eta": self.johnson_slack_eta.to_term(),
                "m": self.theorem_m,
                "delta": self.distance.to_term(),
                "ell": self.query_repetitions,
            },
            "profile_coordinates": {
                "fold_rounds": self.protocol_fold_rounds,
                "localization_arity": self.localization_arity,
                "localization_log": self.localization_log,
            },
            "first_term_squared": self.first_term_squared.to_term(),
            "second_term": self.second_term.to_term(),
            "selected_upper_bound": self.selected_upper_bound.to_term(),
            "dominant_term": self.dominant_term,
            "classification": self.classification.value,
            "checked_side_conditions": {
                "eta-is-positive": self.johnson_slack_eta.numerator > 0,
                "eta-is-less-than-sqrt-rho-over-two-m": (
                    self.eta_range_condition_holds
                ),
                "delta-is-less-than-one-minus-sqrt-rho-minus-eta": (
                    self.delta_range_condition_holds
                ),
                "k-is-at-most-n-over-two": (
                    self.standing_k_at_most_n_over_two
                ),
            },
            "theorem_truth_status": self.theorem_truth_status.value,
            "theorem_applicability_status": (
                self.theorem_applicability_status.value
            ),
            "property_established": False,
            "nonvacuity_only": True,
        }

    @property
    def identity(self) -> SemanticId:
        return semantic_id(
            "analysis-bound-evaluation",
            "fri-ior.classical-analysis.direct-fri-bound.v1",
            self.to_term(),
        )


def evaluate_selected_goldilocks_direct_fri_bound(
    question: object,
) -> tuple[DirectFriBoundEvaluation, CheckResult]:
    """Classify the exact selected substitution using rational comparisons.

    The first term contains ``rho^(3/2)``.  Since all quantities are positive,
    comparing its square to one is exact and avoids floating-point or an
    invented radical codec.
    """

    boundary = "classical-analysis:direct-fri-bound"
    if type(question) is not DirectFriQuantitativeQuestion:
        raise malformed(
            boundary,
            "FRI-IOR-CLASSICAL-ANALYSIS-016",
            "bound evaluation requires the exact direct-FRI question",
        )

    field_size = GOLDILOCKS_FIELD_SIZE
    domain_size = DOMAIN_ORDERS[0]
    rate = Fraction(DEGREE_BOUNDS[0], domain_size)
    theorem_m = 3
    protocol_fold_rounds = FOLD_ROUNDS
    domain_log = domain_size.bit_length() - 1
    degree_log = DEGREE_BOUNDS[0].bit_length() - 1
    localization_arity = 2
    localization_log = 1
    johnson_slack_eta = Fraction(1, 20)
    standing_k_at_most_n_over_two = degree_log * 2 <= domain_log
    # Both comparisons are exact because all compared terms are positive.
    eta_range_condition_holds = (
        2 * theorem_m * johnson_slack_eta
    ) ** 2 < rate
    distance = Fraction(1, 2)
    delta_margin = 1 - johnson_slack_eta - distance
    delta_range_condition_holds = delta_margin > 0 and rate < delta_margin**2
    query_repetitions = QUERY_REPETITIONS

    nonradical = (
        Fraction(2 * theorem_m + 1, 2) ** 7
        * domain_size**2
        / (3 * field_size)
    )
    first_term_squared = nonradical**2 / rate**3
    second_term = (1 - distance) ** query_repetitions
    first_term_is_smaller = first_term_squared < second_term**2
    if not first_term_is_smaller:
        raise RuntimeError("the selected direct-FRI dominant term changed")
    selected_upper_bound = second_term
    classification = (
        QuantitativeBoundClassification.NONVACUOUS
        if selected_upper_bound < 1
        else QuantitativeBoundClassification.VACUOUS
    )
    if not (
        eta_range_condition_holds
        and delta_range_condition_holds
        and standing_k_at_most_n_over_two
    ):
        raise RuntimeError("the selected direct-FRI side-condition witness is false")
    evaluation = DirectFriBoundEvaluation(
        question.identity,
        EXACT_CLASSICAL_FRI_PROFILE.identity,
        field_size,
        domain_size,
        CanonicalRational.from_fraction(rate),
        theorem_m,
        protocol_fold_rounds,
        domain_log,
        degree_log,
        localization_arity,
        localization_log,
        CanonicalRational.from_fraction(johnson_slack_eta),
        eta_range_condition_holds,
        delta_range_condition_holds,
        standing_k_at_most_n_over_two,
        CanonicalRational.from_fraction(distance),
        query_repetitions,
        CanonicalRational.from_fraction(first_term_squared),
        CanonicalRational.from_fraction(second_term),
        CanonicalRational.from_fraction(selected_upper_bound),
        "repetition-term",
        classification,
    )
    return evaluation, affirmative(
        boundary,
        "FRI-IOR-CLASSICAL-ANALYSIS-101",
        "the selected exact arithmetic substitution was classified",
        subject=evaluation.identity,
        classification=classification.value,
        selected_upper_bound=CanonicalRational.from_fraction(
            selected_upper_bound
        ).to_term(),
        theorem_true=None,
        theorem_applicable=None,
        property_established=None,
        nonvacuity_established=(
            classification is QuantitativeBoundClassification.NONVACUOUS
        ),
    )


@dataclass(frozen=True, slots=True)
class BcsShortcutRequest:
    source_property: str
    target_property: str
    construction_id: SemanticId

    def __post_init__(self) -> None:
        if (
            self.source_property != "NativeProximitySoundness"
            or self.target_property != "CommittedInteractiveSoundness"
        ):
            raise malformed(
                "classical-analysis:bcs-shortcut-formation",
                "FRI-IOR-CLASSICAL-ANALYSIS-017",
                "the shortcut request has an unsupported property edge",
            )
        _semantic_ref(self.construction_id)


def refuse_bcs_commitment_shortcut(candidate: object) -> CheckResult:
    boundary = "classical-analysis:bcs-shortcut"
    if type(candidate) is not BcsShortcutRequest:
        return CheckResult(
            OutcomeClass.MALFORMED,
            boundary,
            "FRI-IOR-CLASSICAL-ANALYSIS-018",
            "BCS shortcut checking requires a formed request",
        )
    return refused(
        boundary,
        "FRI-IOR-CLASSICAL-ANALYSIS-019",
        (
            "a checked commitment construction does not transport native "
            "proximity soundness to committed-interactive soundness; the BCS "
            "theorem consumes restricted state-restoration security and also "
            "requires its exact noninteractive random-oracle target"
        ),
    )


def refuse_question_as_property_transport(
    source_question: object,
    target_question: object,
) -> CheckResult:
    boundary = "classical-analysis:question-coercion"
    if (
        type(source_question) is not RoundByRoundSoundnessQuestion
        or type(target_question) is not RestrictedStateRestorationSoundnessQuestion
    ):
        return kind_mismatch(
            boundary,
            "FRI-IOR-CLASSICAL-ANALYSIS-020",
            "the coercion check requires the exact two question families",
        )
    return refused(
        boundary,
        "FRI-IOR-CLASSICAL-ANALYSIS-021",
        "question formation supplies neither a source judgment nor a transport theorem",
    )


__all__ = [
    "AnalysisEvaluationStatus",
    "AnalysisExperimentProfile",
    "BcsShortcutRequest",
    "CanonicalRational",
    "CheckedAlgorithmOneStructuralCorrespondence",
    "ClassicalPropertyFamily",
    "DIRECT_FRI_SOURCE_VALIDATION",
    "DIRECT_FRI_THEOREM_SCHEMA",
    "DirectFriBoundEvaluation",
    "DirectFriQuantitativeQuestion",
    "DirectFriTheoremSchema",
    "GOLDILOCKS_FIELD_SIZE",
    "QuantitativeBoundClassification",
    "RESTRICTED_RESTORATION_EXPERIMENT",
    "ROUND_BY_ROUND_EXPERIMENT",
    "RestrictedStateRestorationSoundnessQuestion",
    "RoundByRoundSoundnessQuestion",
    "StructuralCorrespondenceAdmission",
    "TheoremApplicabilityStatus",
    "TheoremSourceValidation",
    "TheoremTruthStatus",
    "check_algorithm_one_structural_correspondence",
    "evaluate_selected_goldilocks_direct_fri_bound",
    "form_direct_fri_quantitative_question",
    "form_restricted_state_restoration_question",
    "form_round_by_round_soundness_question",
    "refuse_bcs_commitment_shortcut",
    "refuse_question_as_property_transport",
]
