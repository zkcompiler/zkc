"""Typed Analysis questions for the finite native FRI/IOR pressure case.

This module forms experiments, property questions, theorem schemas, source
anchors, applicability obligations, and exact quantitative expressions.  It
does not execute an adversarial game or establish a theorem.  In particular,
an affirmative result from this module means only that a finite term is
well-formed or that a named arithmetic calculation was reproduced.

The implementation deliberately has no dependency on private generation,
native execution traces, commitments, openings, or a committed verifier.
Those objects may eventually be operands of separately checked applicability
judgments; they are not evidence authored by question formation.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from math import gcd
from typing import Any

from .profile import EXACT_PROFILE
from .provenance import ArtifactContentId
from .terms import (
    CheckResult,
    ModelFailure,
    OutcomeClass,
    SemanticId,
    affirmative,
    kind_mismatch,
    malformed,
    semantic_id,
)


class Capability(str, Enum):
    PUBLIC_COIN = "PublicCoin"
    LOGICAL_ORACLE = "LogicalOracle"
    PROOF_SUPPLIED_OPENING = "ProofSuppliedOpening"
    COMMITMENT_CHECK = "CommitmentCheck"
    DOOMED_PREFIX = "DoomedPrefix"
    REACHED_PREFIX_SCHEDULER = "ReachedPrefixScheduler"
    CLASSICAL_RANDOM_ORACLE = "ClassicalRandomOracle"
    QUANTUM_RANDOM_ORACLE = "QuantumRandomOracle"
    GRINDING_TRIAL = "GrindingTrial"
    EXTRACTOR = "Extractor"
    TRANSCRIPT_TREE = "TranscriptTree"
    HONEST_VERIFIER_VIEW = "HonestVerifierView"
    MALICIOUS_VERIFIER_STRATEGY = "MaliciousVerifierStrategy"


class ResourceCoordinate(str, Enum):
    LOGICAL_QUERY_OCCURRENCES = "LogicalQueryOccurrences"
    UNIQUE_OPENED_POSITIONS = "UniqueOpenedPositions"
    AUTHENTICATION_NODES = "AuthenticationNodes"
    COMMITMENT_HASH_INVOCATIONS = "CommitmentHashInvocations"
    CLASSICAL_RANDOM_ORACLE_QUERIES = "ClassicalRandomOracleQueries"
    QUANTUM_RANDOM_ORACLE_QUERIES = "QuantumRandomOracleQueries"
    RESTORATION_BRANCH_EXTENSIONS = "RestorationBranchExtensions"
    GRINDING_TRIALS = "GrindingTrials"
    PROOF_OF_WORK_CHECKS = "ProofOfWorkChecks"
    EXTRACTOR_INVOCATIONS = "ExtractorInvocations"
    EXTRACTOR_ADVERSARY_CALLS = "ExtractorAdversaryCalls"
    PROOF_SYMBOLS = "ProofSymbols"
    PROOF_BYTES = "ProofBytes"
    RUNNING_TIME = "RunningTime"
    MEMORY = "Memory"


class ExperimentKind(str, Enum):
    NATIVE_IOPP = "NativeIopp"
    ROUND_BY_ROUND_VECTOR = "RoundByRoundVector"
    RESTRICTED_RESTORATION = "RestrictedRestoration"
    UNRESTRICTED_RESTORATION = "UnrestrictedRestoration"
    COMMITTED_INTERACTIVE = "CommittedInteractive"
    GRINDING_AUGMENTED_COMMITTED = "GrindingAugmentedCommitted"
    CLASSICAL_ROM = "ClassicalRom"
    QROM = "Qrom"
    CLASSICAL_ROM_KNOWLEDGE = "ClassicalRomKnowledge"
    SPECIAL_SOUNDNESS = "GeneralizedSpecialSoundness"
    HONEST_VERIFIER = "HonestVerifier"
    MALICIOUS_VERIFIER = "MaliciousVerifier"


class ErrorShape(str, Enum):
    BOOLEAN = "Boolean"
    SCALAR = "ScalarProbability"
    ROUND_VECTOR = "RoundIndexedProbabilityVector"
    KNOWLEDGE_WITH_EXTRACTOR = "KnowledgeErrorWithExtractor"


class PropertyKind(str, Enum):
    NATIVE_COMPLETENESS = "NativeIoppCompleteness"
    NATIVE_PROXIMITY_SOUNDNESS = "NativeIoppProximitySoundness"
    ROUND_BY_ROUND_VECTOR_SOUNDNESS = "RoundByRoundVectorSoundness"
    RESTRICTED_RESTORATION_SOUNDNESS = "RestrictedRestorationSoundness"
    UNRESTRICTED_RESTORATION_SOUNDNESS = "UnrestrictedRestorationSoundness"
    COMMITTED_INTERACTIVE_SOUNDNESS = "CommittedInteractiveSoundness"
    GRINDING_ADJUSTED_SOUNDNESS = "GrindingAdjustedCommittedSoundness"
    CLASSICAL_ROM_SOUNDNESS = "AdaptiveClassicalRomSoundness"
    QROM_SOUNDNESS = "AdaptiveQromSoundness"
    CLASSICAL_ROM_KNOWLEDGE = "AdaptiveClassicalRomKnowledgeSoundness"
    GENERALIZED_SPECIAL_SOUNDNESS = "GeneralizedSpecialSoundness"
    HONEST_VERIFIER_ZERO_KNOWLEDGE = "HonestVerifierZeroKnowledge"
    MALICIOUS_VERIFIER_ZERO_KNOWLEDGE = "MaliciousVerifierZeroKnowledge"


class EvaluationStatus(str, Enum):
    NOT_EVALUATED = "NotEvaluated"
    UNSUPPORTED = "Unsupported"
    UNPROVED = "Unproved"


class SourceStatus(str, Enum):
    PAPER_STATED = "PaperStated"


class AssumptionStatus(str, Enum):
    RETAINED_THEOREM_TRUTH_ASSUMPTION = "RetainedTheoremTruthAssumption"


class ObligationKind(str, Enum):
    EXACT_SOURCE_BYTES = "ExactSourceBytes"
    THEOREM_TRANSCRIPTION = "TheoremTranscription"
    THEOREM_TRUTH = "TheoremTruth"
    SOURCE_EXPERIMENT_CORRESPONDENCE = "SourceExperimentCorrespondence"
    TARGET_EXPERIMENT_CORRESPONDENCE = "TargetExperimentCorrespondence"
    PROTOCOL_CORRESPONDENCE = "ProtocolCorrespondence"
    RELATION_CORRESPONDENCE = "RelationCorrespondence"
    OCCURRENCE_MAP = "OccurrenceMap"
    SIDE_CONDITION = "SideCondition"
    RESOURCE_TRANSFORM = "ResourceTransform"
    LOSS_TRANSFORM = "LossTransform"
    GRINDING_PLACEMENT = "GrindingPlacement"
    RANDOM_ORACLE_MODEL = "RandomOracleModel"
    EXTRACTOR_RELATION = "ExtractorRelation"
    HIDDEN_CONSTANTS = "HiddenConstants"


class ObligationStatus(str, Enum):
    OPEN = "Open"
    LOCALLY_REFUTED = "LocallyRefuted"
    LOCALLY_CHECKED = "LocallyChecked"


class QuantityKind(str, Enum):
    NATURAL = "Natural"
    BIT_LENGTH = "BitLength"
    BIT_LENGTH_VECTOR = "BitLengthVector"
    PROBABILITY = "Probability"
    PROBABILITY_VECTOR = "ProbabilityVector"
    EXPECTED_CALLS = "ExpectedCalls"
    ASYMPTOTIC_BOUND = "AsymptoticBound"


class BoundShape(str, Enum):
    SCALAR = "Scalar"
    ROUND_VECTOR = "RoundVector"
    ASYMPTOTIC = "Asymptotic"
    EXPECTED_COST = "ExpectedCost"


class BoundLaw(str, Enum):
    ORIGINAL_FRI_REJECTION = "OriginalFriRejectionLowerBound"
    DIRECT_FRI_ROUND_BY_ROUND = "DirectFriRoundByRoundError"
    ROUND_BY_ROUND_TO_RESTORATION = "RoundByRoundToRestoration"
    COMMITMENT_COMPILATION = "CommitmentCompilationLoss"
    BCS_CLASSICAL_ROM = "BcsClassicalRomCompilation"
    DIRECT_FRI_CLASSICAL_ROM = "DirectFriClassicalRom"
    SPECIAL_SOUNDNESS_QROM = "SpecialSoundnessToQromAsymptotic"
    MULTIROUND_FS_KNOWLEDGE = "MultiRoundFsKnowledge"
    GRINDING_VECTOR = "GrindingVectorErrors"
    GRINDING_CLASSICAL_ROM = "GrindingClassicalRom"


class BoundClassification(str, Enum):
    NOT_EVALUATED = "NotEvaluated"
    VACUOUS_BOUND = "VacuousBound"
    UNSUPPORTED_CONCRETE_BOUND = "UnsupportedConcreteBound"


@dataclass(frozen=True, slots=True)
class Rational:
    numerator: int
    denominator: int = 1

    def __post_init__(self) -> None:
        if type(self.numerator) is not int or type(self.denominator) is not int:
            raise malformed(
                "analysis:rational-formation",
                "FRI-IOR-ANALYSIS-001",
                "a rational value requires integer numerator and denominator",
            )
        if self.denominator <= 0:
            raise malformed(
                "analysis:rational-formation",
                "FRI-IOR-ANALYSIS-002",
                "a rational denominator must be positive",
            )
        common = gcd(abs(self.numerator), self.denominator)
        if common != 1:
            raise malformed(
                "analysis:rational-formation",
                "FRI-IOR-ANALYSIS-003",
                "a rational value must be in lowest terms",
            )

    def to_term(self) -> dict[str, int]:
        return {"numerator": self.numerator, "denominator": self.denominator}


@dataclass(frozen=True, slots=True)
class ExperimentProfile:
    name: str
    kind: ExperimentKind
    indexed_relation: str
    code_family: str
    distance_metric: str
    instance_predicate: str
    witness_type: str | None
    quantifier_prefix: tuple[str, ...]
    strategy_abi: tuple[str, ...]
    capabilities: tuple[Capability, ...]
    scheduler_law: str
    abort_law: str
    invalid_move_law: str
    sampling_failure_law: str
    nontermination_law: str
    terminal_law: str
    observation: str
    win_event: str
    resources: tuple[ResourceCoordinate, ...]

    def __post_init__(self) -> None:
        text_fields = (
            self.name,
            self.indexed_relation,
            self.code_family,
            self.distance_metric,
            self.instance_predicate,
            self.scheduler_law,
            self.abort_law,
            self.invalid_move_law,
            self.sampling_failure_law,
            self.nontermination_law,
            self.terminal_law,
            self.observation,
            self.win_event,
        )
        if any(not isinstance(value, str) or not value for value in text_fields):
            raise malformed(
                "analysis:experiment-formation",
                "FRI-IOR-ANALYSIS-004",
                "an experiment profile requires non-empty finite law names",
            )
        if self.witness_type is not None and (
            not isinstance(self.witness_type, str) or not self.witness_type
        ):
            raise malformed(
                "analysis:experiment-formation",
                "FRI-IOR-ANALYSIS-005",
                "an experiment witness type must be absent or non-empty text",
            )
        _formed_unique_tuple(self.quantifier_prefix, str, "quantifier prefix")
        _formed_unique_tuple(self.strategy_abi, str, "strategy ABI")
        _formed_unique_tuple(self.capabilities, Capability, "capabilities")
        _formed_unique_tuple(self.resources, ResourceCoordinate, "resource basis")

    def to_term(self) -> dict[str, Any]:
        return {
            "name": self.name,
            "kind": self.kind.value,
            "indexed_relation": self.indexed_relation,
            "code_family": self.code_family,
            "distance_metric": self.distance_metric,
            "instance_predicate": self.instance_predicate,
            "witness_type": self.witness_type,
            "quantifier_prefix": list(self.quantifier_prefix),
            "strategy_abi": list(self.strategy_abi),
            "capabilities": [item.value for item in self.capabilities],
            "scheduler_law": self.scheduler_law,
            "abort_law": self.abort_law,
            "invalid_move_law": self.invalid_move_law,
            "sampling_failure_law": self.sampling_failure_law,
            "nontermination_law": self.nontermination_law,
            "terminal_law": self.terminal_law,
            "observation": self.observation,
            "win_event": self.win_event,
            "resources": [item.value for item in self.resources],
        }

    @property
    def identity(self) -> SemanticId:
        return semantic_id(
            "analysis-experiment-profile",
            "fri-ior.analysis-experiment.v1",
            self.to_term(),
        )


_PROPERTY_SIGNATURES: dict[PropertyKind, tuple[ExperimentKind, ErrorShape]] = {
    PropertyKind.NATIVE_COMPLETENESS: (ExperimentKind.NATIVE_IOPP, ErrorShape.SCALAR),
    PropertyKind.NATIVE_PROXIMITY_SOUNDNESS: (
        ExperimentKind.NATIVE_IOPP,
        ErrorShape.SCALAR,
    ),
    PropertyKind.ROUND_BY_ROUND_VECTOR_SOUNDNESS: (
        ExperimentKind.ROUND_BY_ROUND_VECTOR,
        ErrorShape.ROUND_VECTOR,
    ),
    PropertyKind.RESTRICTED_RESTORATION_SOUNDNESS: (
        ExperimentKind.RESTRICTED_RESTORATION,
        ErrorShape.SCALAR,
    ),
    PropertyKind.UNRESTRICTED_RESTORATION_SOUNDNESS: (
        ExperimentKind.UNRESTRICTED_RESTORATION,
        ErrorShape.SCALAR,
    ),
    PropertyKind.COMMITTED_INTERACTIVE_SOUNDNESS: (
        ExperimentKind.COMMITTED_INTERACTIVE,
        ErrorShape.SCALAR,
    ),
    PropertyKind.GRINDING_ADJUSTED_SOUNDNESS: (
        ExperimentKind.GRINDING_AUGMENTED_COMMITTED,
        ErrorShape.ROUND_VECTOR,
    ),
    PropertyKind.CLASSICAL_ROM_SOUNDNESS: (
        ExperimentKind.CLASSICAL_ROM,
        ErrorShape.SCALAR,
    ),
    PropertyKind.QROM_SOUNDNESS: (ExperimentKind.QROM, ErrorShape.SCALAR),
    PropertyKind.CLASSICAL_ROM_KNOWLEDGE: (
        ExperimentKind.CLASSICAL_ROM_KNOWLEDGE,
        ErrorShape.KNOWLEDGE_WITH_EXTRACTOR,
    ),
    PropertyKind.GENERALIZED_SPECIAL_SOUNDNESS: (
        ExperimentKind.SPECIAL_SOUNDNESS,
        ErrorShape.KNOWLEDGE_WITH_EXTRACTOR,
    ),
    PropertyKind.HONEST_VERIFIER_ZERO_KNOWLEDGE: (
        ExperimentKind.HONEST_VERIFIER,
        ErrorShape.BOOLEAN,
    ),
    PropertyKind.MALICIOUS_VERIFIER_ZERO_KNOWLEDGE: (
        ExperimentKind.MALICIOUS_VERIFIER,
        ErrorShape.BOOLEAN,
    ),
}


@dataclass(frozen=True, slots=True)
class PropertyQuestion:
    name: str
    kind: PropertyKind
    experiment: ExperimentProfile
    error_shape: ErrorShape
    evaluation_status: EvaluationStatus = EvaluationStatus.NOT_EVALUATED

    def __post_init__(self) -> None:
        if not isinstance(self.name, str) or not self.name:
            raise malformed(
                "analysis:property-question-formation",
                "FRI-IOR-ANALYSIS-006",
                "a property question requires a non-empty name",
            )
        expected = _PROPERTY_SIGNATURES.get(self.kind)
        if expected is None or expected != (self.experiment.kind, self.error_shape):
            raise ModelFailure(
                OutcomeClass.KIND_MISMATCH,
                "analysis:property-question-formation",
                "FRI-IOR-ANALYSIS-007",
                "the property kind, experiment kind, and error shape do not match",
            )
        if self.evaluation_status not in (
            EvaluationStatus.NOT_EVALUATED,
            EvaluationStatus.UNSUPPORTED,
            EvaluationStatus.UNPROVED,
        ):
            raise malformed(
                "analysis:property-question-formation",
                "FRI-IOR-ANALYSIS-008",
                "the property question has an unsupported evaluation status",
            )

    def to_term(self) -> dict[str, Any]:
        return {
            "name": self.name,
            "kind": self.kind.value,
            "experiment_id": self.experiment.identity.to_term(),
            "error_shape": self.error_shape.value,
            "evaluation_status": self.evaluation_status.value,
            "established_property": None,
            "outer_relation_conclusion": None,
        }

    @property
    def identity(self) -> SemanticId:
        return semantic_id(
            "analysis-property-question",
            "fri-ior.analysis-property-question.v1",
            self.to_term(),
        )


@dataclass(frozen=True, slots=True)
class SourceAnchor:
    paper_id: str
    title: str
    revision: str
    artifact_content_id: ArtifactContentId
    locators: tuple[str, ...]
    status: SourceStatus = SourceStatus.PAPER_STATED

    def __post_init__(self) -> None:
        if any(
            not isinstance(value, str) or not value
            for value in (self.paper_id, self.title, self.revision)
        ):
            raise malformed(
                "analysis:source-anchor-formation",
                "FRI-IOR-ANALYSIS-009",
                "a source anchor requires exact non-empty publication fields",
            )
        if not isinstance(self.artifact_content_id, ArtifactContentId):
            raise malformed(
                "analysis:source-anchor-formation",
                "FRI-IOR-ANALYSIS-010",
                "a source anchor requires an exact ArtifactContentId",
            )
        _formed_unique_tuple(self.locators, str, "source locators")

    def to_term(self) -> dict[str, Any]:
        return {
            "paper_id": self.paper_id,
            "title": self.title,
            "revision": self.revision,
            "artifact_content_id": str(self.artifact_content_id),
            "locators": list(self.locators),
            "status": self.status.value,
            "truth_discharge": None,
        }

    @property
    def identity(self) -> SemanticId:
        return semantic_id(
            "analysis-source-anchor",
            "fri-ior.analysis-source-anchor.v1",
            self.to_term(),
        )


@dataclass(frozen=True, slots=True)
class BoundBinder:
    name: str
    quantity: QuantityKind
    resource: ResourceCoordinate | None = None

    def __post_init__(self) -> None:
        if not isinstance(self.name, str) or not self.name:
            raise malformed(
                "analysis:bound-formation",
                "FRI-IOR-ANALYSIS-011",
                "a bound binder requires a non-empty name",
            )

    def to_term(self) -> dict[str, Any]:
        return {
            "name": self.name,
            "quantity": self.quantity.value,
            "resource": None if self.resource is None else self.resource.value,
        }


_BOUND_DEFINITIONS: dict[BoundLaw, tuple[BoundShape, str, tuple[BoundBinder, ...]]] = {
    BoundLaw.ORIGINAL_FRI_REJECTION: (
        BoundShape.SCALAR,
        "min(delta,delta0)-3*N/field_size",
        (
            BoundBinder("delta", QuantityKind.PROBABILITY),
            BoundBinder("delta0", QuantityKind.PROBABILITY),
            BoundBinder("N", QuantityKind.NATURAL),
            BoundBinder("field_size", QuantityKind.NATURAL),
        ),
    ),
    BoundLaw.DIRECT_FRI_ROUND_BY_ROUND: (
        BoundShape.SCALAR,
        "max(((m+1/2)^7*N^2)/(3*rho^(3/2)*field_size),(1-delta)^ell)",
        (
            BoundBinder("m", QuantityKind.NATURAL),
            BoundBinder("N", QuantityKind.NATURAL),
            BoundBinder("rho", QuantityKind.PROBABILITY),
            BoundBinder("field_size", QuantityKind.NATURAL),
            BoundBinder("delta", QuantityKind.PROBABILITY),
            BoundBinder(
                "ell",
                QuantityKind.NATURAL,
                ResourceCoordinate.LOGICAL_QUERY_OCCURRENCES,
            ),
        ),
    ),
    BoundLaw.ROUND_BY_ROUND_TO_RESTORATION: (
        BoundShape.SCALAR,
        "b*max_i(epsilon_i)",
        (
            BoundBinder("epsilon_vector", QuantityKind.PROBABILITY_VECTOR),
            BoundBinder(
                "b",
                QuantityKind.NATURAL,
                ResourceCoordinate.RESTORATION_BRANCH_EXTENSIONS,
            ),
        ),
    ),
    BoundLaw.COMMITMENT_COMPILATION: (
        BoundShape.SCALAR,
        "source_error+commitment_binding_loss+opening_correspondence_loss",
        (
            BoundBinder("source_error", QuantityKind.PROBABILITY),
            BoundBinder("commitment_binding_loss", QuantityKind.PROBABILITY),
            BoundBinder("opening_correspondence_loss", QuantityKind.PROBABILITY),
        ),
    ),
    BoundLaw.BCS_CLASSICAL_ROM: (
        BoundShape.SCALAR,
        "restricted_restoration_error+3*(Q^2+1)*2^(-kappa)",
        (
            BoundBinder("restricted_restoration_error", QuantityKind.PROBABILITY),
            BoundBinder(
                "Q",
                QuantityKind.NATURAL,
                ResourceCoordinate.CLASSICAL_RANDOM_ORACLE_QUERIES,
            ),
            BoundBinder("kappa", QuantityKind.BIT_LENGTH),
        ),
    ),
    BoundLaw.DIRECT_FRI_CLASSICAL_ROM: (
        BoundShape.SCALAR,
        "Q*epsilon_rbr+3*(Q^2+1)*2^(-kappa)",
        (
            BoundBinder("epsilon_rbr", QuantityKind.PROBABILITY),
            BoundBinder(
                "Q",
                QuantityKind.NATURAL,
                ResourceCoordinate.CLASSICAL_RANDOM_ORACLE_QUERIES,
            ),
            BoundBinder("kappa", QuantityKind.BIT_LENGTH),
        ),
    ),
    BoundLaw.SPECIAL_SOUNDNESS_QROM: (
        BoundShape.ASYMPTOTIC,
        "O(t^2*epsilon+t^3*2^(-kappa))",
        (
            BoundBinder("epsilon", QuantityKind.PROBABILITY),
            BoundBinder(
                "t",
                QuantityKind.NATURAL,
                ResourceCoordinate.QUANTUM_RANDOM_ORACLE_QUERIES,
            ),
            BoundBinder("kappa", QuantityKind.BIT_LENGTH),
        ),
    ),
    BoundLaw.MULTIROUND_FS_KNOWLEDGE: (
        BoundShape.EXPECTED_COST,
        "K+Q*(K-1)",
        (
            BoundBinder("K", QuantityKind.NATURAL),
            BoundBinder(
                "Q",
                QuantityKind.NATURAL,
                ResourceCoordinate.CLASSICAL_RANDOM_ORACLE_QUERIES,
            ),
        ),
    ),
    BoundLaw.GRINDING_VECTOR: (
        BoundShape.ROUND_VECTOR,
        "component_i=epsilon_i*2^(-z_i)",
        (
            BoundBinder("epsilon_vector", QuantityKind.PROBABILITY_VECTOR),
            BoundBinder("difficulty_vector", QuantityKind.BIT_LENGTH_VECTOR),
        ),
    ),
    BoundLaw.GRINDING_CLASSICAL_ROM: (
        BoundShape.SCALAR,
        "T*max_i(epsilon_i*2^(-z_i))+3*(T^2+1)*2^(-kappa)",
        (
            BoundBinder("epsilon_vector", QuantityKind.PROBABILITY_VECTOR),
            BoundBinder("difficulty_vector", QuantityKind.BIT_LENGTH_VECTOR),
            BoundBinder(
                "T",
                QuantityKind.NATURAL,
                ResourceCoordinate.CLASSICAL_RANDOM_ORACLE_QUERIES,
            ),
            BoundBinder("kappa", QuantityKind.BIT_LENGTH),
        ),
    ),
}


@dataclass(frozen=True, slots=True)
class QuantitativeBoundExpression:
    law: BoundLaw
    shape: BoundShape
    formula: str
    binders: tuple[BoundBinder, ...]

    def __post_init__(self) -> None:
        expected = _BOUND_DEFINITIONS.get(self.law)
        if expected != (self.shape, self.formula, self.binders):
            raise malformed(
                "analysis:bound-formation",
                "FRI-IOR-ANALYSIS-012",
                "a quantitative expression must use its exact registered law",
            )

    @classmethod
    def for_law(cls, law: BoundLaw) -> "QuantitativeBoundExpression":
        shape, formula, binders = _BOUND_DEFINITIONS[law]
        return cls(law, shape, formula, binders)

    def to_term(self) -> dict[str, Any]:
        return {
            "law": self.law.value,
            "shape": self.shape.value,
            "formula": self.formula,
            "binders": [binder.to_term() for binder in self.binders],
            "classification": BoundClassification.NOT_EVALUATED.value,
        }

    @property
    def identity(self) -> SemanticId:
        return semantic_id(
            "analysis-bound-expression",
            "fri-ior.analysis-bound-expression.v1",
            self.to_term(),
        )


@dataclass(frozen=True, slots=True)
class ApplicabilityObligation:
    name: str
    kind: ObligationKind
    status: ObligationStatus
    reason: str

    def __post_init__(self) -> None:
        if any(
            not isinstance(value, str) or not value
            for value in (self.name, self.reason)
        ):
            raise malformed(
                "analysis:obligation-formation",
                "FRI-IOR-ANALYSIS-013",
                "an applicability obligation requires a name and reason",
            )

    def to_term(self) -> dict[str, str]:
        return {
            "name": self.name,
            "kind": self.kind.value,
            "status": self.status.value,
            "reason": self.reason,
        }


@dataclass(frozen=True, slots=True)
class RetainedAssumption:
    name: str
    theorem_schema_id: SemanticId
    source_anchor_id: SemanticId
    status: AssumptionStatus = AssumptionStatus.RETAINED_THEOREM_TRUTH_ASSUMPTION

    def __post_init__(self) -> None:
        if not isinstance(self.name, str) or not self.name:
            raise malformed(
                "analysis:assumption-formation",
                "FRI-IOR-ANALYSIS-014",
                "a retained assumption requires a non-empty name",
            )
        if not isinstance(self.theorem_schema_id, SemanticId) or not isinstance(
            self.source_anchor_id, SemanticId
        ):
            raise malformed(
                "analysis:assumption-formation",
                "FRI-IOR-ANALYSIS-015",
                "a retained assumption requires typed theorem and source identities",
            )

    def to_term(self) -> dict[str, Any]:
        return {
            "name": self.name,
            "theorem_schema_id": self.theorem_schema_id.to_term(),
            "source_anchor_id": self.source_anchor_id.to_term(),
            "status": self.status.value,
            "discharges_theorem_truth": False,
        }

    @property
    def identity(self) -> SemanticId:
        return semantic_id(
            "analysis-retained-assumption",
            "fri-ior.analysis-retained-assumption.v1",
            self.to_term(),
        )


@dataclass(frozen=True, slots=True)
class TheoremQuestion:
    name: str
    source: SourceAnchor
    source_property: PropertyQuestion
    target_property: PropertyQuestion
    binders: tuple[str, ...]
    required_views: tuple[str, ...]
    required_maps: tuple[str, ...]
    side_conditions: tuple[str, ...]
    bound: QuantitativeBoundExpression
    conclusion_law: str
    obligations: tuple[ApplicabilityObligation, ...]
    evaluation_status: EvaluationStatus = EvaluationStatus.UNPROVED

    def __post_init__(self) -> None:
        if any(
            not isinstance(value, str) or not value
            for value in (self.name, self.conclusion_law)
        ):
            raise malformed(
                "analysis:theorem-question-formation",
                "FRI-IOR-ANALYSIS-016",
                "a theorem question requires exact name and conclusion law",
            )
        for values, label in (
            (self.binders, "theorem binders"),
            (self.required_views, "required views"),
            (self.required_maps, "required maps"),
            (self.side_conditions, "side conditions"),
        ):
            _formed_unique_tuple(values, str, label)
        _formed_unique_tuple(
            self.obligations, ApplicabilityObligation, "applicability obligations"
        )
        if not self.obligations:
            raise malformed(
                "analysis:theorem-question-formation",
                "FRI-IOR-ANALYSIS-017",
                "a theorem question cannot omit applicability obligations",
            )

    def schema_term(self) -> dict[str, Any]:
        return {
            "name": self.name,
            "source_property_id": self.source_property.identity.to_term(),
            "target_property_id": self.target_property.identity.to_term(),
            "binders": list(self.binders),
            "required_views": list(self.required_views),
            "required_maps": list(self.required_maps),
            "side_conditions": list(self.side_conditions),
            "bound_id": self.bound.identity.to_term(),
            "conclusion_law": self.conclusion_law,
        }

    @property
    def schema_identity(self) -> SemanticId:
        return semantic_id(
            "analysis-theorem-schema",
            "fri-ior.analysis-theorem-schema.v1",
            self.schema_term(),
        )

    def to_term(self) -> dict[str, Any]:
        return {
            "schema_id": self.schema_identity.to_term(),
            "source_anchor_id": self.source.identity.to_term(),
            "obligations": [item.to_term() for item in self.obligations],
            "evaluation_status": self.evaluation_status.value,
            "theorem_true": None,
            "applicable": None,
            "property_established": None,
        }

    @property
    def identity(self) -> SemanticId:
        return semantic_id(
            "analysis-theorem-question",
            "fri-ior.analysis-theorem-question.v1",
            self.to_term(),
        )


@dataclass(frozen=True, slots=True)
class BoundEvaluation:
    expression_id: SemanticId
    profile_id: SemanticId
    classification: BoundClassification
    exact_parameters: tuple[tuple[str, Rational | int], ...]
    derived_facts: tuple[str, ...]
    theorem_applicability: None = None
    property_established: None = None

    def to_term(self) -> dict[str, Any]:
        parameters: list[dict[str, Any]] = []
        for name, value in self.exact_parameters:
            parameters.append(
                {
                    "name": name,
                    "value": value.to_term() if isinstance(value, Rational) else value,
                }
            )
        return {
            "expression_id": self.expression_id.to_term(),
            "profile_id": self.profile_id.to_term(),
            "classification": self.classification.value,
            "exact_parameters": parameters,
            "derived_facts": list(self.derived_facts),
            "theorem_applicability": self.theorem_applicability,
            "property_established": self.property_established,
        }

    @property
    def identity(self) -> SemanticId:
        return semantic_id(
            "analysis-bound-evaluation",
            "fri-ior.analysis-bound-evaluation.v1",
            self.to_term(),
        )


def _formed_unique_tuple(values: object, item_type: type, label: str) -> None:
    if not isinstance(values, tuple) or not values:
        raise malformed(
            "analysis:finite-carrier-formation",
            "FRI-IOR-ANALYSIS-018",
            f"{label} must be a non-empty finite tuple",
        )
    if any(not isinstance(value, item_type) for value in values):
        raise malformed(
            "analysis:finite-carrier-formation",
            "FRI-IOR-ANALYSIS-019",
            f"{label} contains a value of the wrong kind",
        )
    if len(set(values)) != len(values):
        raise malformed(
            "analysis:finite-carrier-formation",
            "FRI-IOR-ANALYSIS-020",
            f"{label} contains duplicates",
        )
    if item_type is str and any(not value for value in values):
        raise malformed(
            "analysis:finite-carrier-formation",
            "FRI-IOR-ANALYSIS-021",
            f"{label} contains empty text",
        )


def check_property_coercion(
    source: PropertyQuestion,
    requested_kind: PropertyKind,
) -> CheckResult:
    """Accept only exact property identity; implication requires a theorem edge."""

    boundary = "analysis:property-coercion"
    if not isinstance(source, PropertyQuestion) or not isinstance(
        requested_kind, PropertyKind
    ):
        return CheckResult(
            OutcomeClass.MALFORMED,
            boundary,
            "FRI-IOR-ANALYSIS-022",
            "property compatibility requires a question and a property kind",
        )
    if source.kind is not requested_kind:
        return kind_mismatch(
            boundary,
            "FRI-IOR-ANALYSIS-023",
            "distinct property kinds cannot be coerced without an explicit theorem edge",
        )
    return affirmative(
        boundary,
        "FRI-IOR-ANALYSIS-100",
        "the requested kind is exactly the formed property kind",
        subject=source.identity,
        property_established=None,
    )


def check_question_formation(candidate: object) -> CheckResult:
    """Return affirmative evidence only for a well-formed Analysis question."""

    boundary = "analysis:question-formation"
    if not isinstance(candidate, (PropertyQuestion, TheoremQuestion)):
        return CheckResult(
            OutcomeClass.MALFORMED,
            boundary,
            "FRI-IOR-ANALYSIS-024",
            "question formation requires a property or theorem question",
        )
    return affirmative(
        boundary,
        "FRI-IOR-ANALYSIS-101",
        "the finite Analysis question and its typed identity are formed",
        subject=candidate.identity,
        theorem_true=None,
        applicable=None,
        security_established=None,
        outer_relation_established=None,
    )


def canonical_experiments() -> dict[ExperimentKind, ExperimentProfile]:
    """Return the exact finite experiment-question catalog."""

    ordinary_laws = {
        "abort_law": "abort-is-loss-for-prover-strategy",
        "invalid_move_law": "invalid-prover-move-is-loss",
        "sampling_failure_law": "sampling-failure-is-distinct-experiment-failure",
        "nontermination_law": "nontermination-is-loss-within-resource-bound",
        "terminal_law": "verifier-accept-or-reject-only",
    }
    relation = "parameterized-reed-solomon-proximity-relation"
    code = "parameterized-reed-solomon-code-family"
    distance = "relative-hamming-distance-on-declared-domain"
    common_strategy = (
        "fixed-oracles",
        "prior-prover-messages",
        "prior-verifier-coins",
        "logical-query-answers",
        "auxiliary-input",
        "advice",
    )
    common_resources = (
        ResourceCoordinate.LOGICAL_QUERY_OCCURRENCES,
        ResourceCoordinate.RUNNING_TIME,
        ResourceCoordinate.MEMORY,
    )

    def profile(
        name: str,
        kind: ExperimentKind,
        *,
        quantifiers: tuple[str, ...],
        capabilities: tuple[Capability, ...],
        scheduler: str,
        observation: str,
        win: str,
        resources: tuple[ResourceCoordinate, ...],
        witness: str | None = None,
        strategy: tuple[str, ...] = common_strategy,
    ) -> ExperimentProfile:
        return ExperimentProfile(
            name=name,
            kind=kind,
            indexed_relation=relation,
            code_family=code,
            distance_metric=distance,
            instance_predicate="true-or-delta-far-instance-by-property-question",
            witness_type=witness,
            quantifier_prefix=quantifiers,
            strategy_abi=strategy,
            capabilities=capabilities,
            scheduler_law=scheduler,
            observation=observation,
            win_event=win,
            resources=resources,
            **ordinary_laws,
        )

    profiles = (
        profile(
            "native-iopp",
            ExperimentKind.NATIVE_IOPP,
            quantifiers=("parameters", "instance", "prover-strategy", "verifier-coins"),
            capabilities=(Capability.PUBLIC_COIN, Capability.LOGICAL_ORACLE),
            scheduler="one-forward-native-interaction",
            observation="native-logical-oracle-transcript-and-verdict",
            win="property-question-specific-native-verdict-event",
            resources=common_resources,
        ),
        profile(
            "round-by-round-vector",
            ExperimentKind.ROUND_BY_ROUND_VECTOR,
            quantifiers=(
                "parameters",
                "round-index",
                "doomed-prefix",
                "legal-next-prover-message",
                "next-verifier-coin",
            ),
            capabilities=(
                Capability.PUBLIC_COIN,
                Capability.LOGICAL_ORACLE,
                Capability.DOOMED_PREFIX,
            ),
            scheduler="theorem-owned-doomed-prefix-family",
            observation="round-indexed-doomed-prefix-escape-event",
            win="escape-from-doomed-set-at-selected-round",
            resources=common_resources,
        ),
        profile(
            "restricted-restoration",
            ExperimentKind.RESTRICTED_RESTORATION,
            quantifiers=("parameters", "instance", "strategy", "branch-extension"),
            capabilities=(
                Capability.PUBLIC_COIN,
                Capability.LOGICAL_ORACLE,
                Capability.REACHED_PREFIX_SCHEDULER,
            ),
            scheduler="reached-prefix-branching-with-no-empty-return-after-first-iteration",
            observation="reached-prefix-set",
            win="reached-set-contains-accepting-leaf",
            resources=common_resources
            + (ResourceCoordinate.RESTORATION_BRANCH_EXTENSIONS,),
        ),
        profile(
            "unrestricted-restoration",
            ExperimentKind.UNRESTRICTED_RESTORATION,
            quantifiers=("parameters", "instance", "strategy", "branch-extension"),
            capabilities=(
                Capability.PUBLIC_COIN,
                Capability.LOGICAL_ORACLE,
                Capability.REACHED_PREFIX_SCHEDULER,
            ),
            scheduler="reached-prefix-branching-with-empty-state-return-permitted",
            observation="reached-prefix-set",
            win="reached-set-contains-accepting-leaf",
            resources=common_resources
            + (ResourceCoordinate.RESTORATION_BRANCH_EXTENSIONS,),
        ),
        profile(
            "committed-interactive",
            ExperimentKind.COMMITTED_INTERACTIVE,
            quantifiers=("parameters", "instance", "prover-strategy", "verifier-coins"),
            capabilities=(
                Capability.PUBLIC_COIN,
                Capability.PROOF_SUPPLIED_OPENING,
                Capability.COMMITMENT_CHECK,
            ),
            scheduler="one-forward-committed-interaction",
            observation="commitments-openings-and-verdict",
            win="committed-verifier-accepts-false-instance",
            resources=(
                ResourceCoordinate.UNIQUE_OPENED_POSITIONS,
                ResourceCoordinate.AUTHENTICATION_NODES,
                ResourceCoordinate.COMMITMENT_HASH_INVOCATIONS,
                ResourceCoordinate.PROOF_SYMBOLS,
                ResourceCoordinate.PROOF_BYTES,
                ResourceCoordinate.RUNNING_TIME,
                ResourceCoordinate.MEMORY,
            ),
        ),
        profile(
            "grinding-augmented-committed",
            ExperimentKind.GRINDING_AUGMENTED_COMMITTED,
            quantifiers=("parameters", "instance", "prover-strategy", "work-trials"),
            capabilities=(
                Capability.PUBLIC_COIN,
                Capability.PROOF_SUPPLIED_OPENING,
                Capability.COMMITMENT_CHECK,
                Capability.GRINDING_TRIAL,
            ),
            scheduler="work-seed-then-nonce-before-protected-coin",
            observation="commitments-work-transcript-openings-and-verdict",
            win="work-augmented-verifier-accepts-false-instance",
            resources=(
                ResourceCoordinate.GRINDING_TRIALS,
                ResourceCoordinate.PROOF_OF_WORK_CHECKS,
                ResourceCoordinate.UNIQUE_OPENED_POSITIONS,
                ResourceCoordinate.COMMITMENT_HASH_INVOCATIONS,
                ResourceCoordinate.PROOF_BYTES,
            ),
        ),
        profile(
            "adaptive-classical-rom",
            ExperimentKind.CLASSICAL_ROM,
            quantifiers=("parameters", "instance", "adversary", "random-oracle"),
            capabilities=(
                Capability.PROOF_SUPPLIED_OPENING,
                Capability.COMMITMENT_CHECK,
                Capability.CLASSICAL_RANDOM_ORACLE,
            ),
            scheduler="adaptive-classical-random-oracle-experiment",
            observation="classical-oracle-query-log-proof-and-verdict",
            win="noninteractive-verifier-accepts-false-instance",
            resources=(
                ResourceCoordinate.CLASSICAL_RANDOM_ORACLE_QUERIES,
                ResourceCoordinate.UNIQUE_OPENED_POSITIONS,
                ResourceCoordinate.AUTHENTICATION_NODES,
                ResourceCoordinate.PROOF_BYTES,
                ResourceCoordinate.RUNNING_TIME,
                ResourceCoordinate.MEMORY,
            ),
        ),
        profile(
            "adaptive-qrom",
            ExperimentKind.QROM,
            quantifiers=(
                "parameters",
                "instance",
                "quantum-adversary",
                "quantum-random-oracle",
            ),
            capabilities=(
                Capability.PROOF_SUPPLIED_OPENING,
                Capability.COMMITMENT_CHECK,
                Capability.QUANTUM_RANDOM_ORACLE,
            ),
            scheduler="adaptive-quantum-random-oracle-experiment",
            observation="declared-classical-output-and-quantum-query-budget",
            win="noninteractive-verifier-accepts-false-instance",
            resources=(
                ResourceCoordinate.QUANTUM_RANDOM_ORACLE_QUERIES,
                ResourceCoordinate.UNIQUE_OPENED_POSITIONS,
                ResourceCoordinate.PROOF_BYTES,
                ResourceCoordinate.RUNNING_TIME,
                ResourceCoordinate.MEMORY,
            ),
            strategy=common_strategy + ("quantum-superposition-oracle-abi",),
        ),
        profile(
            "adaptive-classical-rom-knowledge",
            ExperimentKind.CLASSICAL_ROM_KNOWLEDGE,
            quantifiers=(
                "parameters",
                "instance",
                "adversary",
                "extractor",
                "random-oracle",
            ),
            capabilities=(
                Capability.CLASSICAL_RANDOM_ORACLE,
                Capability.EXTRACTOR,
            ),
            scheduler="adaptive-classical-rom-extraction-experiment",
            observation="proof-verdict-extractor-output-and-cost",
            win="accepting-proof-without-valid-extracted-witness",
            resources=(
                ResourceCoordinate.CLASSICAL_RANDOM_ORACLE_QUERIES,
                ResourceCoordinate.EXTRACTOR_INVOCATIONS,
                ResourceCoordinate.EXTRACTOR_ADVERSARY_CALLS,
                ResourceCoordinate.RUNNING_TIME,
                ResourceCoordinate.MEMORY,
            ),
            witness="indexed-relation-witness",
        ),
        profile(
            "generalized-special-soundness",
            ExperimentKind.SPECIAL_SOUNDNESS,
            quantifiers=(
                "parameters",
                "instance",
                "accepting-transcript-tree",
                "extractor",
            ),
            capabilities=(
                Capability.LOGICAL_ORACLE,
                Capability.TRANSCRIPT_TREE,
                Capability.EXTRACTOR,
            ),
            scheduler="theorem-owned-accepting-transcript-tree-experiment",
            observation="fork-cardinalities-and-extractor-output",
            win="required-forks-exist-without-valid-extracted-witness",
            resources=(
                ResourceCoordinate.EXTRACTOR_INVOCATIONS,
                ResourceCoordinate.EXTRACTOR_ADVERSARY_CALLS,
                ResourceCoordinate.RUNNING_TIME,
                ResourceCoordinate.MEMORY,
            ),
            witness="indexed-relation-witness",
        ),
        profile(
            "honest-verifier-zero-knowledge",
            ExperimentKind.HONEST_VERIFIER,
            quantifiers=("parameters", "true-instance", "honest-verifier-coins"),
            capabilities=(Capability.HONEST_VERIFIER_VIEW,),
            scheduler="honest-verifier-view-experiment",
            observation="honest-verifier-view",
            win="question-specific-view-distinguishing-event",
            resources=(ResourceCoordinate.RUNNING_TIME, ResourceCoordinate.MEMORY),
            witness="indexed-relation-witness",
        ),
        profile(
            "malicious-verifier-zero-knowledge",
            ExperimentKind.MALICIOUS_VERIFIER,
            quantifiers=("parameters", "true-instance", "malicious-verifier-strategy"),
            capabilities=(Capability.MALICIOUS_VERIFIER_STRATEGY,),
            scheduler="malicious-verifier-interaction-experiment",
            observation="malicious-verifier-view",
            win="question-specific-view-distinguishing-event",
            resources=(ResourceCoordinate.RUNNING_TIME, ResourceCoordinate.MEMORY),
            witness="indexed-relation-witness",
        ),
    )
    return {item.kind: item for item in profiles}


def canonical_property_questions() -> dict[PropertyKind, PropertyQuestion]:
    experiments = canonical_experiments()
    statuses = {
        PropertyKind.QROM_SOUNDNESS: EvaluationStatus.UNSUPPORTED,
        PropertyKind.CLASSICAL_ROM_KNOWLEDGE: EvaluationStatus.UNSUPPORTED,
    }
    return {
        kind: PropertyQuestion(
            name=kind.value,
            kind=kind,
            experiment=experiments[signature[0]],
            error_shape=signature[1],
            evaluation_status=statuses.get(kind, EvaluationStatus.NOT_EVALUATED),
        )
        for kind, signature in _PROPERTY_SIGNATURES.items()
    }


def canonical_source_anchors() -> dict[str, SourceAnchor]:
    def artifact(digest: str) -> ArtifactContentId:
        return ArtifactContentId(digest)

    anchors = (
        SourceAnchor(
            "icalp-fri-2018-14",
            "Fast Reed-Solomon Interactive Oracle Proofs of Proximity",
            "ICALP 2018",
            artifact(
                "e244896fb6e7fcab7fe4de00e31a36003b941b6550e062fdb5ee66d78641498d"
            ),
            ("Theorem 2",),
        ),
        SourceAnchor(
            "bcs-iop-2016-116-r2",
            "Interactive Oracle Proofs",
            "ePrint 2016/116 revision 2",
            artifact(
                "a2dc9bd042665081664287281b9bcf64735be2c818ce9207cce57cc43939fa2f"
            ),
            ("Section 5.4", "Section 7", "Theorem 7.1"),
        ),
        SourceAnchor(
            "fri-fs-2023-1071-r7",
            "Fiat-Shamir Security of FRI and Related SNARKs",
            "ePrint 2023/1071 revision 7",
            artifact(
                "bb7a7e87b9000c98106de99c9af9d289def2a1b91919a3507ee78bf9bfd16947"
            ),
            ("Theorem 3.15", "Theorem 4.1", "Corollary 4.3", "Theorem 5.11"),
        ),
        SourceAnchor(
            "afk-multi-round-fs-2021-1377-v2",
            "Fiat-Shamir Transformation of Multi-Round Interactive Proofs",
            "ePrint 2021/1377 version 2",
            artifact(
                "93837e2dd7c0e99ef3d06bbb4f235d9ed0dcafb8b96e56d867e7548751e9122c"
            ),
            ("Equation (1)", "Theorem 2", "Theorem 3"),
        ),
        SourceAnchor(
            "ethstark-2021-582-r3",
            "ethSTARK Documentation",
            "ePrint 2021/582 archive revision 3",
            artifact(
                "23b1bd72be468c3b1781bfd76c075a843bb529e8dedc763629c67a080b4f0099"
            ),
            ("Section 6.1", "Section 6.3", "Theorem 6", "Theorem 8"),
        ),
    )
    return {item.paper_id: item for item in anchors}


def _open_obligations(
    *items: tuple[str, ObligationKind, str],
) -> tuple[ApplicabilityObligation, ...]:
    return tuple(
        ApplicabilityObligation(name, kind, ObligationStatus.OPEN, reason)
        for name, kind, reason in items
    )


def canonical_theorem_questions() -> dict[str, TheoremQuestion]:
    properties = canonical_property_questions()
    sources = canonical_source_anchors()

    common = _open_obligations(
        (
            "theorem-truth",
            ObligationKind.THEOREM_TRUTH,
            "the selected source is retained as an unproved theorem-truth assumption",
        ),
        (
            "protocol-correspondence",
            ObligationKind.PROTOCOL_CORRESPONDENCE,
            "no checked correspondence to the theorem's protocol has been supplied",
        ),
        (
            "side-conditions",
            ObligationKind.SIDE_CONDITION,
            "the theorem-owned side conditions have not all been discharged",
        ),
    )

    def question(
        name: str,
        source: str,
        source_property: PropertyKind,
        target_property: PropertyKind,
        law: BoundLaw,
        *,
        binders: tuple[str, ...],
        views: tuple[str, ...],
        maps: tuple[str, ...],
        conditions: tuple[str, ...],
        conclusion: str,
        obligations: tuple[ApplicabilityObligation, ...] = common,
        status: EvaluationStatus = EvaluationStatus.UNPROVED,
    ) -> TheoremQuestion:
        return TheoremQuestion(
            name,
            sources[source],
            properties[source_property],
            properties[target_property],
            binders,
            views,
            maps,
            conditions,
            QuantitativeBoundExpression.for_law(law),
            conclusion,
            obligations,
            status,
        )

    questions = (
        question(
            "original-fri-native-proximity",
            "icalp-fri-2018-14",
            PropertyKind.NATIVE_PROXIMITY_SOUNDNESS,
            PropertyKind.NATIVE_PROXIMITY_SOUNDNESS,
            BoundLaw.ORIGINAL_FRI_REJECTION,
            binders=("field", "additive-code-family", "rho", "N", "delta"),
            views=("native-logical-oracle-view",),
            maps=("source-code-family-to-experiment",),
            conditions=(
                "binary-additive-family",
                "R-at-least-two",
                "rho-N-greater-than-sixteen",
            ),
            conclusion="conditional-native-rejection-lower-bound",
        ),
        question(
            "direct-fri-round-by-round",
            "fri-fs-2023-1071-r7",
            PropertyKind.NATIVE_PROXIMITY_SOUNDNESS,
            PropertyKind.ROUND_BY_ROUND_VECTOR_SOUNDNESS,
            BoundLaw.DIRECT_FRI_ROUND_BY_ROUND,
            binders=(
                "field",
                "smooth-multiplicative-family",
                "m",
                "rho",
                "delta",
                "ell",
            ),
            views=("native-logical-oracle-view", "doomed-prefix-view"),
            maps=("round-prefix-map", "logical-query-occurrence-map"),
            conditions=("theorem-4.1-smooth-multiplicative-hypotheses",),
            conclusion="conditional-round-by-round-error-vector",
        ),
        question(
            "round-by-round-to-restricted-restoration",
            "fri-fs-2023-1071-r7",
            PropertyKind.ROUND_BY_ROUND_VECTOR_SOUNDNESS,
            PropertyKind.RESTRICTED_RESTORATION_SOUNDNESS,
            BoundLaw.ROUND_BY_ROUND_TO_RESTORATION,
            binders=("epsilon-vector", "branch-extension-budget"),
            views=("doomed-prefix-view", "restricted-reached-prefix-view"),
            maps=("round-prefix-to-reached-prefix",),
            conditions=("restricted-restoration-scheduler",),
            conclusion="conditional-restoration-error-at-most-b-times-max-round-error",
        ),
        question(
            "round-by-round-to-unrestricted-restoration",
            "fri-fs-2023-1071-r7",
            PropertyKind.ROUND_BY_ROUND_VECTOR_SOUNDNESS,
            PropertyKind.UNRESTRICTED_RESTORATION_SOUNDNESS,
            BoundLaw.ROUND_BY_ROUND_TO_RESTORATION,
            binders=("epsilon-vector", "branch-extension-budget"),
            views=("doomed-prefix-view", "unrestricted-reached-prefix-view"),
            maps=("round-prefix-to-reached-prefix",),
            conditions=("unrestricted-restoration-scheduler",),
            conclusion="conditional-restoration-error-at-most-b-times-max-round-error",
        ),
        question(
            "commitment-compilation-preservation",
            "bcs-iop-2016-116-r2",
            PropertyKind.NATIVE_PROXIMITY_SOUNDNESS,
            PropertyKind.COMMITTED_INTERACTIVE_SOUNDNESS,
            BoundLaw.COMMITMENT_COMPILATION,
            binders=("source-protocol", "commitment-profile", "occurrence-map"),
            views=("native-logical-oracle-view", "authenticated-opening-view"),
            maps=(
                "oracle-to-cap",
                "occurrence-to-opening",
                "native-to-committed-verdict",
            ),
            conditions=("commitment-assumptions", "hash-purpose-separation"),
            conclusion="open-commitment-compilation-property-preservation-question",
            obligations=common
            + _open_obligations(
                (
                    "occurrence-map",
                    ObligationKind.OCCURRENCE_MAP,
                    "logical occurrences and deduplicated physical openings require a checked map",
                ),
                (
                    "relation-correspondence",
                    ObligationKind.RELATION_CORRESPONDENCE,
                    "source and target relation meanings have not been equated",
                ),
            ),
        ),
        question(
            "bcs-restricted-restoration-to-classical-rom",
            "bcs-iop-2016-116-r2",
            PropertyKind.RESTRICTED_RESTORATION_SOUNDNESS,
            PropertyKind.CLASSICAL_ROM_SOUNDNESS,
            BoundLaw.BCS_CLASSICAL_ROM,
            binders=("restricted-restoration-error", "Q", "kappa"),
            views=("restricted-restoration-view", "classical-random-oracle-view"),
            maps=(
                "iop-oracle-message-to-authenticated-commitment",
                "logical-query-to-opening",
            ),
            conditions=(
                "restricted-restoration-security",
                "separate-coin-and-hash-oracles",
            ),
            conclusion="conditional-bcs-classical-rom-soundness-bound",
            obligations=common
            + _open_obligations(
                (
                    "random-oracle-model",
                    ObligationKind.RANDOM_ORACLE_MODEL,
                    "SHA-256 fixture execution is not a classical random-oracle experiment",
                ),
                (
                    "occurrence-map",
                    ObligationKind.OCCURRENCE_MAP,
                    "the exact generalized commitment profile requires a checked occurrence map",
                ),
            ),
        ),
        question(
            "grinding-over-vector-errors",
            "ethstark-2021-582-r3",
            PropertyKind.ROUND_BY_ROUND_VECTOR_SOUNDNESS,
            PropertyKind.GRINDING_ADJUSTED_SOUNDNESS,
            BoundLaw.GRINDING_VECTOR,
            binders=("epsilon-vector", "difficulty-vector"),
            views=("round-by-round-view", "work-seed-and-nonce-view"),
            maps=("protected-coin-placement-map",),
            conditions=(
                "work-before-protected-coin",
                "theorem-random-oracle-experiment",
            ),
            conclusion="conditional-componentwise-grinding-error-scaling",
            obligations=common
            + _open_obligations(
                (
                    "grinding-placement",
                    ObligationKind.GRINDING_PLACEMENT,
                    "a nonce predicate alone does not discharge theorem placement",
                ),
            ),
        ),
        question(
            "direct-fri-classical-rom",
            "fri-fs-2023-1071-r7",
            PropertyKind.ROUND_BY_ROUND_VECTOR_SOUNDNESS,
            PropertyKind.CLASSICAL_ROM_SOUNDNESS,
            BoundLaw.DIRECT_FRI_CLASSICAL_ROM,
            binders=("epsilon-rbr", "Q", "kappa"),
            views=("committed-transcript-view", "classical-random-oracle-view"),
            maps=(
                "transcript-to-random-oracle-query",
                "logical-to-authenticated-query",
            ),
            conditions=(
                "exact-fri-algorithm",
                "exact-commitment-transform",
                "classical-rom",
            ),
            conclusion="conditional-classical-rom-soundness-bound",
            obligations=common
            + _open_obligations(
                (
                    "random-oracle-model",
                    ObligationKind.RANDOM_ORACLE_MODEL,
                    "SHA-256 fixture execution is not a classical random-oracle experiment",
                ),
            ),
        ),
        question(
            "fri-qrom-asymptotic",
            "fri-fs-2023-1071-r7",
            PropertyKind.GENERALIZED_SPECIAL_SOUNDNESS,
            PropertyKind.QROM_SOUNDNESS,
            BoundLaw.SPECIAL_SOUNDNESS_QROM,
            binders=("epsilon", "quantum-query-budget", "kappa"),
            views=("classical-rom-view", "quantum-superposition-oracle-view"),
            maps=("adjusted-quantum-query-budget-map",),
            conditions=("adaptive-qrom-experiment", "source-special-soundness-premise"),
            conclusion="unsupported-unproved-asymptotic-qrom-question",
            obligations=common
            + _open_obligations(
                (
                    "hidden-constants",
                    ObligationKind.HIDDEN_CONSTANTS,
                    "the asymptotic expression has no concrete local bound",
                ),
                (
                    "quantum-oracle-abi",
                    ObligationKind.RANDOM_ORACLE_MODEL,
                    "the evaluator implements no quantum-superposition oracle ABI",
                ),
            ),
            status=EvaluationStatus.UNSUPPORTED,
        ),
        question(
            "multi-round-fs-knowledge",
            "afk-multi-round-fs-2021-1377-v2",
            PropertyKind.GENERALIZED_SPECIAL_SOUNDNESS,
            PropertyKind.CLASSICAL_ROM_KNOWLEDGE,
            BoundLaw.MULTIROUND_FS_KNOWLEDGE,
            binders=("special-soundness-vector", "challenge-cardinalities", "Q", "K"),
            views=("classical-rom-view", "extractor-view"),
            maps=("accepted-proof-to-witness",),
            conditions=(
                "generalized-special-soundness",
                "consistent-random-oracle-answers",
            ),
            conclusion="unsupported-unproved-classical-rom-knowledge-question",
            obligations=common
            + _open_obligations(
                (
                    "extractor-relation",
                    ObligationKind.EXTRACTOR_RELATION,
                    "the finite FRI witness has no admitted extractor relation",
                ),
            ),
            status=EvaluationStatus.UNSUPPORTED,
        ),
    )
    return {item.name: item for item in questions}


def retained_assumptions() -> tuple[RetainedAssumption, ...]:
    return tuple(
        RetainedAssumption(
            f"retained-truth-of-{question.name}",
            question.schema_identity,
            question.source.identity,
        )
        for question in canonical_theorem_questions().values()
    )


def evaluate_tiny_f97_round_by_round_bound(
    expression: QuantitativeBoundExpression,
) -> tuple[BoundEvaluation, CheckResult]:
    """Reproduce the dossier's exact vacuity classification without floats.

    For ``m=3, N=16, rho=1/2, |F|=97`` the first term is
    ``(3294172/291)*sqrt(2)``.  The integer inequality
    ``2*3294172^2 > (16009*291)^2`` proves that term is greater than
    16009.  The other term is exactly ``(9/10)^4 = 6561/10000``.
    Neither calculation checks any theorem premise.
    """

    boundary = "analysis:local-bound-evaluation"
    expected = QuantitativeBoundExpression.for_law(BoundLaw.DIRECT_FRI_ROUND_BY_ROUND)
    if expression != expected:
        raise ModelFailure(
            OutcomeClass.KIND_MISMATCH,
            boundary,
            "FRI-IOR-ANALYSIS-025",
            "the finite evaluator supports only the direct FRI round-by-round expression",
        )

    radical_numerator = 3_294_172
    radical_denominator = 291
    threshold = 16_009
    if 2 * radical_numerator**2 <= (threshold * radical_denominator) ** 2:
        raise RuntimeError("internal exact inequality for the F97 bound is false")

    evaluation = BoundEvaluation(
        expression.identity,
        EXACT_PROFILE.identity,
        BoundClassification.VACUOUS_BOUND,
        (
            ("field_size", 97),
            ("N", 16),
            ("rho", Rational(1, 2)),
            ("m", 3),
            ("delta", Rational(1, 10)),
            ("ell", 4),
        ),
        (
            "first-term-equals-(3294172/291)*sqrt(2)",
            "first-term-is-greater-than-16009-by-exact-integer-squaring",
            "second-term-equals-6561/10000",
            "displayed-maximum-is-greater-than-one",
            "original-fri-binary-additive-side-conditions-are-not-satisfied",
            "honest-positive-fixture-does-not-supply-a-delta-far-premise",
        ),
    )
    result = affirmative(
        boundary,
        "FRI-IOR-ANALYSIS-102",
        "the exact local substitution was reproduced and its probability bound is vacuous",
        subject=evaluation.identity,
        classification=evaluation.classification.value,
        theorem_true=None,
        theorem_applicable=None,
        property_established=None,
        non_vacuity_established=None,
    )
    return evaluation, result


def local_original_fri_obligations() -> tuple[ApplicabilityObligation, ...]:
    """Return the exact locally refuted source-hypothesis checks for F97."""

    return (
        ApplicabilityObligation(
            "binary-additive-family",
            ObligationKind.SIDE_CONDITION,
            ObligationStatus.LOCALLY_REFUTED,
            "the selected profile uses an odd field and a multiplicative subgroup",
        ),
        ApplicabilityObligation(
            "rho-is-two-to-minus-R-with-R-at-least-two",
            ObligationKind.SIDE_CONDITION,
            ObligationStatus.LOCALLY_REFUTED,
            "the selected rate is one half",
        ),
        ApplicabilityObligation(
            "rho-N-greater-than-sixteen",
            ObligationKind.SIDE_CONDITION,
            ObligationStatus.LOCALLY_REFUTED,
            "the selected product rho*N equals eight",
        ),
        ApplicabilityObligation(
            "delta-far-premise",
            ObligationKind.SIDE_CONDITION,
            ObligationStatus.OPEN,
            "the positive fixture is an honestly generated low-degree word",
        ),
    )


__all__ = [
    "ApplicabilityObligation",
    "AssumptionStatus",
    "BoundBinder",
    "BoundClassification",
    "BoundEvaluation",
    "BoundLaw",
    "BoundShape",
    "Capability",
    "ErrorShape",
    "EvaluationStatus",
    "ExperimentKind",
    "ExperimentProfile",
    "ObligationKind",
    "ObligationStatus",
    "PropertyKind",
    "PropertyQuestion",
    "QuantityKind",
    "QuantitativeBoundExpression",
    "Rational",
    "ResourceCoordinate",
    "RetainedAssumption",
    "SourceAnchor",
    "SourceStatus",
    "TheoremQuestion",
    "canonical_experiments",
    "canonical_property_questions",
    "canonical_source_anchors",
    "canonical_theorem_questions",
    "check_property_coercion",
    "check_question_formation",
    "evaluate_tiny_f97_round_by_round_bound",
    "local_original_fri_obligations",
    "retained_assumptions",
]
