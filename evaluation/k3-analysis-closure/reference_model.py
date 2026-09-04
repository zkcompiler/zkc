"""Bounded executable research model for Analysis semantic closure.

This module imports the dependent-surface model, and through it the PIR
Protocol/Fiat--Shamir and executable-Foundation models. It adds only the
minimum Analysis-owned consumer structures needed to pressure source ingress,
strategy/experiment identity, relation-bound property formation, theorem
applicability, property transport, and explicit loss-export occurrence ingress.

The model is deliberately finite.  Fixture theorem rules remain explicit
hypotheses.  No semantic-reference label, run record, replay result, or
structural Fresh/Fiat--Shamir pair is treated as proof of a property.
"""

from __future__ import annotations

from contextlib import contextmanager
from contextvars import ContextVar
from dataclasses import dataclass, field, fields as dataclass_fields, replace
from enum import Enum
from fractions import Fraction
from functools import lru_cache, wraps
import hashlib
import importlib.util
from pathlib import Path
import re
import sys
from types import MappingProxyType
from typing import Callable, Iterable


# ---------------------------------------------------------------------------
# Exact dependent-surface, PIR, and Foundation imports
# ---------------------------------------------------------------------------


_K3_NAME = "_zkc_k3_dependent_surfaces"
_K3_PATH = (
    Path(__file__).resolve().parents[1] / "k3-dependent-surfaces" / "reference_model.py"
)
if _K3_NAME in sys.modules:
    k3 = sys.modules[_K3_NAME]
else:
    _spec = importlib.util.spec_from_file_location(_K3_NAME, _K3_PATH)
    if _spec is None or _spec.loader is None:  # pragma: no cover - host failure
        raise ImportError(f"cannot load dependent-surface model from {_K3_PATH}")
    k3 = importlib.util.module_from_spec(_spec)
    sys.modules[_K3_NAME] = k3
    _spec.loader.exec_module(k3)

k2 = k3.k2
k1 = k3.k1

_FINITE_COVER_NAME = "_zkc_finite_cover_portable_arithmetic"
_FINITE_COVER_PATH = (
    Path(__file__).resolve().parents[1]
    / "finite-cover-analysis"
    / "portable_arithmetic.py"
)
if _FINITE_COVER_NAME in sys.modules:
    finite_cover = sys.modules[_FINITE_COVER_NAME]
else:
    _finite_cover_spec = importlib.util.spec_from_file_location(
        _FINITE_COVER_NAME, _FINITE_COVER_PATH
    )
    if (
        _finite_cover_spec is None or _finite_cover_spec.loader is None
    ):  # pragma: no cover - host failure
        raise ImportError(
            f"cannot load finite-cover arithmetic model from {_FINITE_COVER_PATH}"
        )
    finite_cover = importlib.util.module_from_spec(_finite_cover_spec)
    sys.modules[_FINITE_COVER_NAME] = finite_cover
    _finite_cover_spec.loader.exec_module(finite_cover)


# ---------------------------------------------------------------------------
# Common finite helpers and refusal classes
# ---------------------------------------------------------------------------


MAX_SOURCE_READS = 128
MAX_QUANTIFIERS = 16
MAX_HYPOTHESES = 64
MAX_LOSS_USES = 128
MAX_EXPRESSION_NODES = 256


class AnalysisError(ValueError):
    """Base class for one malformed or forged Analysis input."""


class SourceIngressError(AnalysisError):
    pass


class ExperimentError(AnalysisError):
    pass


class QuantitativeError(AnalysisError):
    pass


class PropertyError(AnalysisError):
    pass


class TheoremError(AnalysisError):
    pass


class AuthorityError(AnalysisError):
    pass


_LOCAL_COMPONENT_KIND_ALIASES = {
    f"analysis.{name}": f"probe.analysis.{name}"
    for name in (
        "adversary-running-algorithm",
        "bounded-property-profile",
        "bounded-property-theorem-assumption",
        "concrete-family-member-subject",
        "event-profile",
        "expected-invocation-bound",
        "experiment-body",
        "experiment-body-bundle",
        "failure-profile",
        "family-theorem-applicability-input",
        "family-member-relation",
        "family-member-selector",
        "family-member-subject",
        "family-member-term",
        "family-ro-index-domain",
        "formula-parameter-domain",
        "fs-correspondence",
        "lazy-random-function-process",
        "model-instantiation",
        "abstract-family-role-coordinate",
        "native-role-coordinate",
        "abstract-resolved-role",
        "native-resolved-role",
        "oracle-query-abi",
        "output-distribution-profile",
        "probability-space",
        "pointwise-formula-correspondence",
        "property-conclusion",
        "quantitative-transform",
        "query-encoding",
        "random-oracle-capability-contract",
        "resource-basis",
        "resource-dimension",
        "semantic-rule",
        "setup-profile",
        "theorem-operator-binding",
        "theorem-substitution",
        "value-domain-profile",
    )
}


def _ascii(text: str, what: str) -> str:
    if (
        type(text) is not str
        or not text
        or any(ord(ch) < 0x21 or ord(ch) > 0x7E for ch in text)
    ):
        raise AnalysisError(f"{what} must be nonempty printable ASCII without spaces")
    return text


def _printable_ascii(text: str, what: str) -> str:
    if (
        type(text) is not str
        or not text
        or text != text.strip(" ")
        or any(ord(ch) < 0x20 or ord(ch) > 0x7E for ch in text)
    ):
        raise AnalysisError(
            f"{what} must be nonempty printable ASCII without edge spaces"
        )
    return text


def _id_datum(
    identifier: object,
    expected_subject_kind: str | tuple[str, ...] | None = None,
) -> object:
    if type(identifier) is not k1.TypedContentId:
        raise AnalysisError(
            "semantic reference must be one exact Foundation TypedContentId"
        )
    identifier.__post_init__()
    if identifier.semantic_regime != k1.SEMANTIC_REGIME_ID:
        raise AnalysisError("semantic reference belongs to an unsupported regime")
    if expected_subject_kind is not None:
        expected = (
            (expected_subject_kind,)
            if type(expected_subject_kind) is str
            else expected_subject_kind
        )
        admitted = tuple(
            kind
            for item in expected
            for kind in (
                item,
                _LOCAL_COMPONENT_KIND_ALIASES.get(item, item),
            )
        )
        if identifier.subject_kind not in admitted:
            raise AnalysisError(
                f"semantic reference has kind {identifier.subject_kind!r}; "
                f"expected one of {admitted!r}"
            )
    return k1.BytesValue(identifier.internal_reference())


def _analysis_declaration_body(label: str, contract: str) -> object:
    return k1.DatumRecord(
        (
            (0, k1.Symbol(_ascii(label, "Analysis declaration label"))),
            (1, k1.Symbol(_ascii(contract, "Analysis declaration contract"))),
        )
    )


def _profile_catalogs(
    catalogs: dict[str, tuple[tuple[str, str], ...]],
) -> object:
    """Compile exact sorted inline declaration catalogs for one profile."""

    entries = []
    for catalog_kind in sorted(catalogs, key=lambda item: item.encode("ascii")):
        declarations = catalogs[catalog_kind]
        if not declarations:
            raise AnalysisError("Analysis declaration catalogs must be nonempty")
        entries.append(
            k1.DatumRecord(
                (
                    (0, k1.Symbol(catalog_kind)),
                    (
                        1,
                        k1.DatumSeq(
                            tuple(
                                _analysis_declaration_body(label, contract)
                                for label, contract in declarations
                            )
                        ),
                    ),
                )
            )
        )
    return k1.DatumSeq(tuple(entries))


def _profile_law_source(
    profile_name: str,
    laws: tuple[str, ...],
    *,
    declaration_catalogs: dict[str, tuple[tuple[str, str], ...]] | None = None,
    body_schema_kinds: tuple[str, ...] = (),
    adequacy_evaluator_schemas: tuple[tuple[str, object, object], ...] = (),
) -> bytes:
    """Encode the complete finite Analysis-language law source.

    The inline Foundation declaration catalogs remain the lookup index.  This body
    independently commits their exact ordered entries, the closed law list,
    every evaluator schema, and the kind-to-body compiler table.  Host code is
    therefore only an implementation of an authenticated finite algebra.
    """

    catalogs = declaration_catalogs or {}
    declaration_contracts = []
    for declaration_kind in sorted(catalogs):
        for ordinal, (label, contract) in enumerate(catalogs[declaration_kind]):
            declaration_contracts.append(
                k1.DatumRecord(
                    (
                        (0, k1.Symbol(declaration_kind)),
                        (1, k1.Nat(ordinal)),
                        (2, _analysis_declaration_body(label, contract)),
                    )
                )
            )
    body_schemas = []
    for subject_kind in sorted(body_schema_kinds):
        descriptor = ANALYSIS_BODY_SCHEMA_DESCRIPTORS.get(subject_kind)
        if descriptor is None:
            raise AnalysisError(
                f"Analysis body schema {subject_kind!r} has no exact descriptor"
            )
        constructor, ordered_fields = descriptor
        body_schemas.append(
            k1.DatumRecord(
                (
                    (0, k1.Symbol(subject_kind)),
                    (1, k1.Nat(0)),
                    (2, k1.Symbol(constructor)),
                    (
                        3,
                        k1.DatumSeq(tuple(k1.Symbol(item) for item in ordered_fields)),
                    ),
                )
            )
        )
    return k1.encode_datum(
        k1.DatumRecord(
            (
                (0, k1.Nat(0)),
                (1, k1.DatumSeq(tuple(declaration_contracts))),
                (
                    2,
                    k1.DatumSeq(
                        tuple(
                            k1.DatumRecord(
                                (
                                    (0, k1.Nat(ordinal)),
                                    (1, k1.Symbol(item)),
                                    (2, k1.Symbol(item)),
                                )
                            )
                            for ordinal, item in enumerate(laws)
                        )
                    ),
                ),
                (
                    3,
                    k1.DatumSeq(
                        tuple(
                            k1.DatumRecord(
                                (
                                    (0, k1.Nat(ordinal)),
                                    (1, k1.Symbol(name)),
                                    (2, input_schema),
                                    (3, failure_partition),
                                )
                            )
                            for ordinal, (
                                name,
                                input_schema,
                                failure_partition,
                            ) in enumerate(adequacy_evaluator_schemas)
                        )
                    ),
                ),
                (4, k1.DatumSeq(tuple(body_schemas))),
            )
        )
    )


def _profile_imports(*profiles: object) -> tuple[object, ...]:
    return tuple(
        sorted(
            (profile.identity for profile in profiles),
            key=lambda identifier: identifier.internal_reference(),
        )
    )


ANALYSIS_BODY_SCHEMA_DESCRIPTORS = {
    "analysis.adequacy-evaluator": (
        "AnalysisAdequacyEvaluatorBody",
        (
            "input-schema",
            "supported-input-profile-ids",
            "output-schema",
            "portable-algorithm-ref",
            "evaluation-contract-id",
            "exact-direct-module-roots",
            "success-value",
            "failure-partition",
        ),
    ),
    "analysis.source-profile": (
        "AnalysisSourceProfileBody",
        (
            "family-tag",
            "slot-schemas",
            "closed-field-read-set",
            "adequacy-evaluator-id",
        ),
    ),
    "analysis.semantic-read-manifest": (
        "AnalysisSemanticReadManifestBody",
        ("source-profile-id", "exact-subjects", "slots"),
    ),
    "analysis.source-support": (
        "AnalysisSourceSupportBody",
        (
            "semantic-read-manifest-id",
            "bindings",
            "derived-owner-policy-dependency-closure",
        ),
    ),
    "analysis.checked-result-coordinate": (
        "AnalysisCheckedResultCoordinateBody",
        (
            "result-id",
            "proposition-id",
            "semantic-basis-id",
            "support-id",
            "validation-basis-id",
            "qualification",
            "outcome-kind",
        ),
    ),
    "analysis.capability-requirement-payload": (
        "AnalysisCapabilityRequirementPayloadBody",
        (
            "proposition-id",
            "qualification-requirement-ref",
            "named-consumer",
            "typed-purpose",
        ),
    ),
    "analysis.source-authority-contract": (
        "AnalysisSourceAuthorityContractBody",
        (
            "owner-coordinate",
            "checked-result-coordinate-id",
            "capability-requirement-payload-id",
            "immediate-policy-ids",
            "transitive-policy-ids",
        ),
    ),
    "analysis.owner-policy-closure": (
        "AnalysisOwnerPolicyClosureBody",
        ("owner-coordinate", "policy-ids", "derivation-law"),
    ),
    "analysis.portable-source-authority-binding": (
        "PortableAnalysisSourceAuthorityBindingBody",
        (
            "owner-domain",
            "capability-family",
            "owner-source-coordinate",
            "owner-binding-payload",
            "operation-policy",
            "owner-policy-closure",
            "capability-requirement",
        ),
    ),
    "analysis.strategy-class": (
        "StrategyClassProfileBody",
        (
            "role",
            "dependent-parameter-schema",
            "strategy-abi",
            "private-state-type",
            "initial-advice-type",
            "allowed-views",
            "allowed-oracles-and-capabilities",
            "legal-move-relation",
            "stop-and-noncompletion-law",
            "resource-dimensions",
        ),
    ),
    "analysis.distribution-profile": (
        "AnalysisDistributionProfileBody",
        (
            "output-type",
            "exact-support-predicate",
            "exact-probability-mass-or-measure-law",
            "parameter-and-security-parameter-coordinates",
            "independence-and-correlation-declarations",
            "sampling-or-oracle-denotation",
            "failure-and-nontermination-law",
        ),
    ),
    "analysis.extractor-profile": (
        "AnalysisExtractorProfileBody",
        (
            "input-and-output-types",
            "private-state-and-randomness-types",
            "allowed-source-and-oracle-capabilities",
            "counterfactual-rights",
            "state-preservation-relation",
            "output-distribution-preservation-relation",
            "witness-success-relation",
            "termination-and-asymptotic-resource-law",
            "counterfactual-capability-contract-and-property-family-scope",
        ),
    ),
    "analysis.positive-polynomial-profile": (
        "AnalysisPositivePolynomialProfileBody",
        (
            "input-sort",
            "coefficient-domain",
            "value-shape",
            "canonical-degree-rule",
            "evaluation",
            "positivity-rule",
            "admitted-coefficient-and-degree-bounds",
        ),
    ),
    "analysis.positive-polynomial": (
        "AnalysisPositivePolynomialBody",
        ("profile-id", "coefficients-low-to-high"),
    ),
    "analysis.experiment-profile": (
        "AnalysisExperimentProfileBody",
        (
            "family",
            "source-profile-id",
            "quantifier-prefix",
            "role-interfaces",
            "setup-and-input-sampling",
            "randomness-ownership-and-independence",
            "public-coin-or-oracle-model",
            "scheduler",
            "generated-execution-relation",
            "observation-and-win-event",
            "failure-abort-and-noncompletion-law",
            "termination-law",
            "resource-basis",
            "output-type",
        ),
    ),
    "analysis.asymptotic-protocol-family": (
        "AnalysisAsymptoticProtocolFamilyDefinitionBody",
        ("family-language", "canonical-family-payload"),
    ),
    "analysis.family-read-manifest-schema": (
        "AnalysisFamilyReadManifestSchemaBody",
        ("family-definition-id", "member-source-profile-id"),
    ),
    "analysis.challenge-domain": (
        "AnalysisChallengeDomainBody",
        (
            "source-challenge-ref",
            "value-type",
            "source-nominal-domain-ref",
            "model-values",
            "adequacy-evaluator-id",
            "semantic-status",
        ),
    ),
    "analysis.fixed-public-setup": (
        "AFKFixedPublicSetupBody",
        (
            "exact-static-sources",
            "exact-public-invocation-sources",
            "derived-projection",
            "required-selection-schedule",
            "visibility-map",
        ),
    ),
    "analysis.quantitative-formula": (
        "AnalysisQuantitativeFormulaBody",
        (
            "result-sort",
            "parameter-schema",
            "declared-parameter-independence",
            "expression",
        ),
    ),
    "analysis.logical-nat-literal": (
        "AnalysisLogicalNatLiteralBody",
        ("meta-natural",),
    ),
    "analysis.native-subject-projection": (
        "AnalysisNativeSubjectProjectionBody",
        (
            "core-id",
            "fresh-protocol-id",
            "fiat-shamir-protocol-id",
            "fresh-binding-id",
            "fiat-shamir-binding-id",
            "fresh-manifest-id",
            "pair-manifest-id",
            "fresh-plan-binding-id",
            "fiat-shamir-plan-binding-id",
        ),
    ),
    "analysis.family-instance-role-map": (
        "FamilyInstanceRoleMapProposalBody",
        (
            "family-id",
            "logical-index-id",
            "native-subject-refs",
            "native-length-value",
            "role",
            "abstract-role-ref",
            "native-role-ref",
            "map-clause-coordinate",
            "information-loss",
        ),
    ),
    "analysis.pointwise-quantitative-normalization": (
        "AFKPointwiseQuantitativeNormalizationContractBody",
        (
            "logical-index-substitution",
            "challenge-cardinality-substitution",
            "positive-polynomial-profile-substitution",
            "positive-polynomial-value-substitution",
            "resource-substitution",
            "canonical-formula-normalization",
            "required-equal-normal-forms",
        ),
    ),
    "analysis.consumer": ("AnalysisConsumerIntakeBody", ("consumer",)),
    "analysis.use-purpose": ("AnalysisUsePurposeIntakeBody", ("purpose",)),
    "analysis.question": (
        "AnalysisQuestionBody",
        ("family", "exact-subjects", "context", "family-payload"),
    ),
    "analysis.goal": ("AnalysisGoalBody", ("question-id",)),
    "analysis.hypothesis-context": (
        "AnalysisHypothesisContextBody",
        ("nodes", "derived-roots"),
    ),
    "analysis.proposition": (
        "AnalysisPropositionBody",
        ("goal-id", "hypothesis-context-id"),
    ),
    "analysis.theorem-schema": (
        "AnalysisTheoremSchemaBody",
        (
            "local-binding-catalog",
            "source-property-schema",
            "target-property-schema",
            "source-experiment-schema",
            "target-experiment-schema",
            "required-source-view-schemas",
            "map-schemas",
            "side-condition-and-parameter-schemas",
            "local-quantitative-operator-catalog",
            "typed-resource-and-loss-transform-program",
            "exact-conclusion-reconstruction-law",
        ),
    ),
    "analysis.theorem-source-validation": (
        "AnalysisTheoremSourceValidationBody",
        ("theorem-schema-id", "source-authority", "truth-discharge-metadata"),
    ),
    "analysis.loss-semantic-import": (
        "AnalysisLossSemanticImportBody",
        (
            "relations-bridge-id",
            "lossy-use-scope-and-occurrence-coordinate-schema",
            "direction",
            "source-semantics",
            "declared-result-sort",
            "admitted-interpretation-rule",
            "exact-parameter-substitution",
            "per-occurrence-expression",
        ),
    ),
    "analysis.semantic-basis": (
        "AnalysisSemanticBasisBody",
        (
            "family",
            "exact-question-id",
            "rule-source",
            "exact-premise-schemas",
            "source-read-purposes",
            "conclusion-schema",
            "typed-transform-program",
        ),
    ),
    "analysis.support-instantiation": (
        "AnalysisSupportInstantiationBody",
        (
            "semantic-basis-id",
            "proposition-id",
            "non-hypothesis-premise-bindings",
            "established-hypothesis-node-bindings",
            "assumed-hypothesis-node-bindings",
            "source-support-bindings",
        ),
    ),
    "analysis.validation-basis": (
        "AnalysisValidationBasisBody",
        (
            "admitted-checker-contract-ids-and-abis",
            "exact-translation-contracts",
            "finite-control-contracts",
            "theorem-source-validation-ids",
            "residual-trust-roots",
        ),
    ),
    "analysis.operation-policy": (
        "AnalysisOperationPolicyBody",
        (
            "supported-families-and-models",
            "named-consumer-and-typed-purpose-permissions",
            "capability-freshness-and-lifetime",
            "disclosure-policy",
            "unknown-question-disposition",
            "persistence-policy",
            "cold-replay-policy",
        ),
    ),
    "analysis.judgment-record": (
        "AnalysisJudgmentRecordBody",
        (
            "proposition-id",
            "polarity",
            "exact-family-conclusion",
            "inherited-hypothesis-context-id",
            "typed-quantitative-result",
            "semantic-basis-id",
            "support-coordinate",
            "validation-basis-id",
            "qualification",
            "operation-policy-id",
            "derived-source-policy-dependency-closure",
        ),
    ),
}

ANALYSIS_SUBJECT_KINDS = tuple(sorted(ANALYSIS_BODY_SCHEMA_DESCRIPTORS))

ANALYSIS_TRANSPORT_ONLY_SUBJECT_KINDS = tuple(
    sorted(
        (
            "analysis.family-instance-role-map",
            "analysis.logical-nat-literal",
            "analysis.native-subject-projection",
            "analysis.pointwise-quantitative-normalization",
            "analysis.theorem-schema",
            "analysis.theorem-source-validation",
        )
    )
)

ANALYSIS_PROPERTY_SUBJECT_KINDS = tuple(
    item
    for item in ANALYSIS_SUBJECT_KINDS
    if item not in ANALYSIS_TRANSPORT_ONLY_SUBJECT_KINDS
)

ANALYSIS_KERNEL_SUBJECT_KINDS = tuple(("analysis.hypothesis-context",))

ANALYSIS_TRANSPORT_SUBJECT_KINDS = tuple(
    sorted(
        (
            "analysis.asymptotic-protocol-family",
            "analysis.adequacy-evaluator",
            "analysis.checked-result-coordinate",
            "analysis.consumer",
            "analysis.family-instance-role-map",
            "analysis.family-read-manifest-schema",
            "analysis.goal",
            "analysis.judgment-record",
            "analysis.hypothesis-context",
            "analysis.experiment-profile",
            "analysis.distribution-profile",
            "analysis.extractor-profile",
            "analysis.logical-nat-literal",
            "analysis.loss-semantic-import",
            "analysis.capability-requirement-payload",
            "analysis.native-subject-projection",
            "analysis.operation-policy",
            "analysis.owner-policy-closure",
            "analysis.pointwise-quantitative-normalization",
            "analysis.portable-source-authority-binding",
            "analysis.proposition",
            "analysis.question",
            "analysis.quantitative-formula",
            "analysis.semantic-basis",
            "analysis.source-authority-contract",
            "analysis.source-profile",
            "analysis.strategy-class",
            "analysis.support-instantiation",
            "analysis.theorem-schema",
            "analysis.use-purpose",
            "analysis.validation-basis",
        )
    )
)

ANALYSIS_THEOREM_SOURCE_VALIDATION_SUBJECT_KINDS = (
    "analysis.capability-requirement-payload",
    "analysis.checked-result-coordinate",
    "analysis.consumer",
    "analysis.judgment-record",
    "analysis.operation-policy",
    "analysis.owner-policy-closure",
    "analysis.portable-source-authority-binding",
    "analysis.source-authority-contract",
    "analysis.support-instantiation",
    "analysis.theorem-source-validation",
    "analysis.use-purpose",
    "analysis.validation-basis",
)

ANALYSIS_KERNEL_DECLARATION_CATALOGS = {
    "analysis.residual-trust-root": (
        ("python-runtime-and-reference-model", "explicit-validation-trust-root"),
    ),
    "analysis.semantic-law": (
        ("checker-input-v0", "closed-checker-input-schema"),
        ("checker-output-v0", "closed-checker-output-schema"),
        ("capability-freshness-v0", "live-token-lifetime-law"),
        ("disclosure-v0", "bounded-disclosure-law"),
        ("unknown-question-v0", "refuse-unknown-question"),
        ("persistence-v0", "portable-inert-only"),
        ("cold-replay-v0", "revalidate-inert-no-live-authority"),
        (
            "derived-used-policy-closure-v0",
            "canonical-exact-used-owner-policy-closure",
        ),
    ),
}

ANALYSIS_PROPERTY_DECLARATION_CATALOGS = {
    "analysis.qualification-requirement": (
        ("exact-inherited-conditional", "exact-qualification-match"),
    ),
    "analysis.native-rule": (
        ("existential-extractor-introduction", "exact-bounded-native-rule"),
        ("conditional-family-instance-correspondence", "exact-bounded-native-rule"),
        ("checked-finite-cover-certificate", "exact-bounded-native-rule"),
        ("checked-finite-cover-universal-discharge", "exact-bounded-native-rule"),
    ),
    "analysis.named-consumer": (
        ("pir-analysis-source-view", "typed-intake-consumer"),
        ("finite-special-soundness", "analysis-premise-consumer"),
        ("finite-fixed-extractor", "analysis-premise-consumer"),
    ),
    "analysis.qualification": (
        ("finite-special-soundness-result", "conditional-affirmative"),
        ("conditional-assumed-external-all-n", "conditional-affirmative"),
        ("finite-cover-certificate-result", "conditional-affirmative"),
        ("finite-fixed-extractor-universal-result", "conditional-affirmative"),
    ),
    "analysis.property-family": (
        ("k-out-of-n-special-soundness", "exact-family-semantics"),
        ("fixed-extractor-universal-correctness", "exact-family-semantics"),
        (
            "adaptive-knowledge-extraction-at-fixed-length-q-lt-n",
            "exact-family-semantics",
        ),
        ("challenge-domain-correspondence", "exact-family-semantics"),
        ("acceptance-relation-correspondence", "exact-family-semantics"),
        ("algebra-and-canonical-encoding-laws", "exact-family-semantics"),
        ("polynomial-time-relation-membership", "exact-family-semantics"),
        ("polynomial-time-source-verifier", "exact-family-semantics"),
        ("polynomial-time-extractor", "exact-family-semantics"),
    ),
    "analysis.resource-operation": (
        ("fresh-no-random-oracle-query", "exact-resource-operation"),
        ("adaptive-random-oracle-query", "exact-resource-operation"),
        ("adversary-running-algorithm", "exact-resource-operation"),
    ),
    "analysis.semantic-law": (
        ("source-profile-input-v0", "closed-source-profile-input-schema"),
        (
            "schnorr-relation-source-profile-input-v0",
            "closed-schnorr-relation-source-profile-input-schema",
        ),
        (
            "afk-fresh-fs-source-profile-input-v0",
            "closed-afk-fresh-fs-source-profile-input-schema",
        ),
        (
            "analysis-attempt-failure-partition-v0",
            "closed-analysis-attempt-failure-partition",
        ),
        ("source-free-premise-reason", "closed-source-free-reason"),
        ("finite-challenge-domain-v0", "owner-bound-cardinality-derivation"),
        ("k-out-of-n-conclusion-v0", "exact-family-conclusion-schema"),
        (
            "fixed-extractor-universal-conclusion-v0",
            "exact-family-conclusion-schema",
        ),
        (
            "finite-cover-certificate-conclusion-v0",
            "exact-family-conclusion-schema",
        ),
        (
            "finite-cover-target-reconstruction-v0",
            "exact-subject-parametric-cover-reconstruction",
        ),
        ("finite-cover-cover-schema-v0", "exact-finite-cover-schema"),
        ("finite-cover-candidate-schema-v0", "exact-candidate-schema"),
        ("finite-cover-success-schema-v0", "exact-success-schema"),
        ("finite-cover-coverage-certificate-v0", "exact-certificate-schema"),
        ("finite-cover-factorization-certificate-v0", "exact-certificate-schema"),
        ("finite-cover-transfer-certificate-v0", "exact-certificate-schema"),
        ("finite-cover-operation-binding-v0", "exact-checker-binding-law"),
        ("finite-cover-stream-progress-v0", "exact-stream-progress-law"),
        ("finite-cover-raw-domain-v0", "exact-raw-domain-predicate"),
        (
            "finite-cover-representative-domain-v0",
            "exact-representative-domain-predicate",
        ),
        ("finite-cover-output-congruence-v0", "exact-output-congruence-law"),
        (
            "finite-cover-representative-success-v0",
            "exact-representative-success-predicate",
        ),
        ("finite-cover-raw-success-v0", "exact-raw-success-predicate"),
        ("adaptive-knowledge-conclusion-v0", "exact-family-conclusion-schema"),
        (
            "afk-fixed-public-setup-projection-v0",
            "exact-owner-coordinate-fixed-setup-projection",
        ),
        (
            "pre-prover-and-oracle-fixed-selection-v0",
            "exact-fixed-selection-schedule",
        ),
        (
            "coordinate-public-visibility-v0",
            "exact-coordinate-public-visibility-map",
        ),
    ),
    "analysis.source-family": (
        ("bounded-concrete-owner-sources", "exact-concrete-source-family"),
        (
            "schnorr-relation-special-soundness-source",
            "exact-schnorr-relation-source-family",
        ),
        (
            "afk-adaptive-fresh-fs-source",
            "exact-afk-fresh-fs-source-family",
        ),
    ),
    "analysis.strategy-role": (
        ("accepted-transcript-pair-domain", "deterministic-value-domain-role"),
        ("adaptive-classical-online-prover", "adaptive-prover-strategy-role"),
    ),
    "analysis.typed-purpose": (
        ("fresh-public-setup-view", "pir-owner-view-use"),
        ("fiat-shamir-public-setup-view", "pir-owner-view-use"),
        ("fresh-execution-view", "pir-owner-view-use"),
        ("fiat-shamir-execution-view", "pir-owner-view-use"),
        ("fiat-shamir-fs-construction-view", "pir-owner-view-use"),
        ("core-public-coin-view", "pir-owner-view-use"),
        ("transcript-declaration-view", "pir-owner-view-use"),
        ("schnorr-relation-definition-view", "relations-owner-view-use"),
        ("finite-special-soundness", "analysis-result-use"),
        ("fixed-extractor-universal-correctness", "analysis-result-use"),
    ),
}

ANALYSIS_TRANSPORT_DECLARATION_CATALOGS = {
    "analysis.asymptotic-family-language": (
        ("afk-schnorr-family-v0", "closed-selected-family-language"),
    ),
    "analysis.afk-family-role-catalog": (
        ("selected-afk-twenty-role-catalog-v0", "closed-twenty-role-catalog"),
    ),
    "analysis.afk-family-role-map-clause": (
        (
            "selected-afk-twenty-role-map-clause-catalog-v0",
            "closed-twenty-clause-catalog",
        ),
    ),
    "analysis.native-rule": (
        ("exact-theorem-applicability-check", "exact-bounded-native-rule"),
        ("afk-family-property-transport", "exact-bounded-native-rule"),
        ("dependent-family-member-specialization", "exact-bounded-native-rule"),
    ),
    "analysis.named-consumer": (
        ("afk-family-property-transport", "analysis-premise-consumer"),
        ("afk-member-specialization", "analysis-premise-consumer"),
    ),
    "analysis.property-family": (
        ("asymptotic-k-out-of-n-special-soundness", "exact-family-semantics"),
        ("adaptive-knowledge-soundness-q-lt-n", "exact-family-semantics"),
        ("theorem-applicability", "exact-family-semantics"),
        ("theorem-truth", "exact-family-semantics"),
        ("family-instance-correspondence", "exact-family-semantics"),
        ("total-single-valued-family-denotation", "exact-family-semantics"),
        ("family-projection-coherence", "exact-family-semantics"),
        ("uniform-prime-order-schnorr-family", "exact-family-semantics"),
        (
            "uniform-polynomial-time-relation-membership",
            "exact-family-semantics",
        ),
        ("uniform-polynomial-time-verifier", "exact-family-semantics"),
        ("fresh-uniform-independent-public-coin", "exact-family-semantics"),
        ("exact-classical-random-oracle-process", "exact-family-semantics"),
        ("fixed-public-setup-independence", "exact-family-semantics"),
        (
            "total-uniform-challenge-sampler-adequacy",
            "exact-family-semantics",
        ),
        ("fixed-family-challenge-cardinality", "exact-family-semantics"),
        (
            "finite-bounded-random-oracle-index-and-efficient-operations",
            "exact-family-semantics",
        ),
        (
            "afk-experiment-observation-correspondence",
            "exact-family-semantics",
        ),
        ("family-denotation-at-index", "exact-family-semantics"),
        ("family-projection-at-index", "exact-family-semantics"),
        ("family-instance-role-map-adequacy", "exact-family-semantics"),
        (
            "family-instance-quantitative-normalization-adequacy",
            "exact-family-semantics",
        ),
        ("family-instance-process-correspondence", "exact-family-semantics"),
    ),
    "analysis.qualification": (
        ("afk-family-applicability-result", "conditional-affirmative"),
        ("afk-family-instance-correspondence-result", "conditional-affirmative"),
    ),
    "analysis.semantic-law": (
        ("theorem-truth-conclusion-v0", "exact-family-conclusion-schema"),
        ("family-applicability-conclusion-v0", "exact-family-conclusion-schema"),
        (
            "family-instance-correspondence-conclusion-v0",
            "exact-family-conclusion-schema",
        ),
        ("fixed-member-knowledge-conclusion-v0", "exact-family-conclusion-schema"),
        (
            "afk-family-source-profile-input-v0",
            "closed-afk-family-source-profile-input-schema",
        ),
        (
            "afk-family-target-profile-input-v0",
            "closed-afk-family-target-profile-input-schema",
        ),
        (
            "analysis-attempt-failure-partition-v0",
            "closed-analysis-attempt-failure-partition",
        ),
    ),
    "analysis.source-family": (
        ("afk-fresh-family-sources", "exact-afk-fresh-abstract-source-family"),
        ("afk-fs-target-family-sources", "exact-afk-fs-abstract-source-family"),
    ),
    "analysis.typed-purpose": (
        ("exact-family-applicability", "analysis-premise-use"),
        ("all-n-two-special-soundness-source", "analysis-premise-use"),
        ("selected-afk-theorem-truth", "analysis-premise-use"),
        ("exact-family-knowledge-transport", "analysis-result-use"),
        ("afk-family-target-specialization", "analysis-result-use"),
        ("afk-exact-family-member-specialization", "analysis-result-use"),
    ),
    "analysis.quantitative-sort": (
        ("logical-natural", "closed-logical-natural-sort"),
        ("probability", "closed-probability-sort"),
        (
            "signed-probability-lower-bound",
            "closed-signed-probability-lower-bound-sort",
        ),
    ),
    "analysis.theorem-local-binding-kind": tuple(
        (label, "closed-afk-v2-local-binding-kind")
        for label in (
            "asymptotic-family-parameter",
            "logical-nat-parameter",
            "positive-polynomial-parameter",
            "uniform-source-extractor",
            "accepting-distinct-transcript-pair",
            "uniform-black-box-target-extractor",
            "statement-role",
            "relation-witness-role",
            "commitment-role",
            "challenge-role",
            "response-role",
            "acceptance-role",
            "fixed-public-setup-role",
            "fresh-interaction-role",
            "fiat-shamir-interaction-role",
            "full-random-oracle-process-role",
            "proof-role",
            "auxiliary-output-role",
            "verifier-output-role",
            "relation-role",
            "random-oracle-index-role",
            "random-oracle-statement-index-role",
            "random-oracle-commitment-index-role",
            "verifier-role",
            "challenge-sampler-role",
            "bounded-bitstring-index-contract-role",
            "challenge-cardinality-role",
            "query-count-resource-role",
            "expected-count-resource-role",
            "query-count-parameter",
            "input-free-adaptive-oracle-prover",
        )
    ),
    "analysis.theorem-local-denotation-schema": tuple(
        (
            f"afk-local-binding-{ordinal}",
            f"closed-afk-v2-denotation-{role}",
        )
        for ordinal, role in enumerate(
            (
                "asymptotic-family-parameter",
                "logical-nat-parameter",
                "positive-polynomial-parameter",
                "uniform-source-extractor",
                "accepting-distinct-transcript-pair",
                "uniform-black-box-target-extractor",
                "statement-role",
                "relation-witness-role",
                "commitment-role",
                "challenge-role",
                "response-role",
                "acceptance-role",
                "fixed-public-setup-role",
                "fresh-interaction-role",
                "fiat-shamir-interaction-role",
                "full-random-oracle-process-role",
                "proof-role",
                "auxiliary-output-role",
                "verifier-output-role",
                "relation-role",
                "random-oracle-index-role",
                "random-oracle-statement-index-role",
                "random-oracle-commitment-index-role",
                "verifier-role",
                "challenge-sampler-role",
                "bounded-bitstring-index-contract-role",
                "challenge-cardinality-role",
                "query-count-resource-role",
                "expected-count-resource-role",
                "query-count-parameter",
                "input-free-adaptive-oracle-prover",
            )
        )
    ),
    "analysis.theorem-property-schema": (
        ("afk-source-property-v0", "closed-afk-v2-property-component"),
        ("afk-target-property-v0", "closed-afk-v2-property-component"),
    ),
    "analysis.theorem-experiment-schema": (
        ("afk-source-experiment-v0", "closed-afk-v2-experiment-component"),
        ("afk-target-experiment-v0", "closed-afk-v2-experiment-component"),
    ),
    "analysis.theorem-source-view-schema": tuple(
        (f"afk-source-view-{ordinal}", "closed-afk-v2-source-view-component")
        for ordinal in range(11)
    ),
    "analysis.theorem-map-schema": tuple(
        (f"afk-map-{ordinal}", "closed-afk-v2-map-component") for ordinal in range(3)
    ),
    "analysis.theorem-side-condition-schema": tuple(
        (f"afk-side-condition-{ordinal}", "closed-afk-v2-side-condition-component")
        for ordinal in range(8)
    ),
    "analysis.theorem-transform-program": (
        ("afk-transform-program-v0", "closed-afk-v2-transform-component"),
    ),
    "analysis.theorem-conclusion-law": (
        ("afk-conclusion-law-v0", "closed-afk-v2-conclusion-component"),
    ),
    "analysis.theorem-template-expression": tuple(
        (f"afk-local-operator-{ordinal}", "closed-afk-v2-typed-template-expression")
        for ordinal in range(4)
    ),
}

ANALYSIS_THEOREM_SOURCE_VALIDATION_DECLARATION_CATALOGS = {
    "analysis.theorem-source-kind": (
        ("iacr-eprint-pdf", "iacr-eprint-archive-pdf-source"),
    ),
    "analysis.qualification": (
        ("conditional-assumed-theorem-truth", "conditional-affirmative"),
        ("afk-family-transport-result", "conditional-affirmative"),
        ("afk-member-specialization-result", "conditional-affirmative"),
    ),
}

# The semantic-law bytes commit the same finite kind/body table enforced by
# ``analysis_domain_body_v0``.  These assignments intentionally supersede the
# early law-name-only bootstrap values above; profile construction below uses
# only these complete encodings.
ANALYSIS_KERNEL_LAW_SOURCE = _profile_law_source(
    "zkc.analysis.kernel-law.v0",
    (
        "canonical-question-goal-proposition-formation",
        "exact-qualified-outcome-taxonomy",
        "inert-authority-envelope-and-invocation-only-live-capability",
        "semantic-basis-excludes-validation-occurrences",
        "derived-used-policy-closure-v0",
    ),
    declaration_catalogs=ANALYSIS_KERNEL_DECLARATION_CATALOGS,
    body_schema_kinds=ANALYSIS_KERNEL_SUBJECT_KINDS,
)
ANALYSIS_PROPERTY_LAW_SOURCE = _profile_law_source(
    "zkc.analysis.bounded-property-law.v0",
    (
        "relation-bound-property-and-experiment-formation",
        "exact-used-static-view-and-relations-dependencies",
        "bounded-quantitative-expression-and-resource-basis",
        "independent-premises-are-not-derived-proofs",
        "checked-finite-cover-requires-coverage-factorization-and-transfer",
        "finite-cover-receipts-are-occurrence-evidence-not-semantic-authority",
        "fixed-extractor-finite-result-has-no-efficiency-or-family-lift",
    ),
    declaration_catalogs=ANALYSIS_PROPERTY_DECLARATION_CATALOGS,
    body_schema_kinds=ANALYSIS_PROPERTY_SUBJECT_KINDS,
    adequacy_evaluator_schemas=(
        (
            "bounded-concrete-source-profile-adequacy-v0",
            k1.Symbol("source-profile-input-v0"),
            k1.Symbol("analysis-attempt-failure-partition-v0"),
        ),
        (
            "bounded-challenge-domain-adequacy-v0",
            k1.Symbol("finite-challenge-domain-v0"),
            k1.Symbol("analysis-attempt-failure-partition-v0"),
        ),
    ),
)
ANALYSIS_TRANSPORT_LAW_SOURCE = _profile_law_source(
    "zkc.analysis.bounded-transport-law.v0",
    (
        "formed-false-applicability-is-refused",
        "exact-used-premise-and-policy-closure-is-derived",
        "theorem-truth-remains-an-independent-premise",
        "live-capabilities-never-enter-semantic-or-judgment-identities",
    ),
    declaration_catalogs=ANALYSIS_TRANSPORT_DECLARATION_CATALOGS,
    body_schema_kinds=ANALYSIS_TRANSPORT_SUBJECT_KINDS,
    adequacy_evaluator_schemas=(
        (
            "afk-fresh-family-source-profile-adequacy-v0",
            k1.Symbol("afk-family-source-profile-input-v0"),
            k1.Symbol("analysis-attempt-failure-partition-v0"),
        ),
        (
            "afk-fs-target-family-source-profile-adequacy-v0",
            k1.Symbol("afk-family-target-profile-input-v0"),
            k1.Symbol("analysis-attempt-failure-partition-v0"),
        ),
    ),
)
ANALYSIS_THEOREM_SOURCE_VALIDATION_LAW_SOURCE = _profile_law_source(
    "zkc.analysis.afk-theorem-source-validation-law.v0",
    (
        "theorem-source-metadata-is-validation-not-theorem-meaning",
        "statement-digest-is-derived-from-admitted-theorem-schema",
        "imported-paper-only-truth-needs-an-explicit-assumption",
        "validation-language-changes-cannot-rotate-semantic-transport-identities",
    ),
    declaration_catalogs=ANALYSIS_THEOREM_SOURCE_VALIDATION_DECLARATION_CATALOGS,
    body_schema_kinds=ANALYSIS_THEOREM_SOURCE_VALIDATION_SUBJECT_KINDS,
)


@dataclass(frozen=True)
class AnalysisSemanticProfiles:
    k3b_profiles: object
    kernel: object
    property: object
    transport: object
    theorem_source_validation: object

    def __post_init__(self) -> None:
        if type(self.k3b_profiles) is not k3.K3BSemanticProfiles or any(
            type(item) is not k1.SemanticLanguageProfile
            for item in (
                self.kernel,
                self.property,
                self.transport,
                self.theorem_source_validation,
            )
        ):
            raise AnalysisError("Analysis semantic profiles have the wrong exact shape")
        if self.kernel.profile_imports:
            raise AnalysisError("the Analysis kernel profile must be import-free")
        if self.property.profile_imports != _profile_imports(
            self.kernel,
            self.k3b_profiles.relations_correspondence,
            self.k3b_profiles.k2_profiles.interaction,
            self.k3b_profiles.k2_profiles.transcript_fs,
            self.k3b_profiles.k2_profiles.public_view,
        ):
            raise AnalysisError(
                "the Analysis property profile must import kernel, Relations, "
                "and every directly interpreted PIR view profile"
            )
        if self.transport.profile_imports != _profile_imports(self.property):
            raise AnalysisError(
                "the Analysis transport profile must import the property profile"
            )
        if self.theorem_source_validation.profile_imports != _profile_imports(
            self.transport
        ):
            raise AnalysisError(
                "the theorem-source validation profile must import transport"
            )

    @property
    def kernel_bundle(self) -> dict[object, object]:
        return {self.kernel.identity: self.kernel}

    @property
    def property_bundle(self) -> dict[object, object]:
        relations_bundle = k3.k3b_root_profile_preimages(self.k3b_profiles)[
            self.k3b_profiles.relations_correspondence.identity
        ]
        return {
            **relations_bundle,
            self.k3b_profiles.k2_profiles.public_view.identity:
                self.k3b_profiles.k2_profiles.public_view,
            self.kernel.identity: self.kernel,
            self.property.identity: self.property,
        }

    @property
    def transport_bundle(self) -> dict[object, object]:
        return {
            **self.property_bundle,
            self.transport.identity: self.transport,
        }

    @property
    def theorem_source_validation_bundle(self) -> dict[object, object]:
        return {
            **self.transport_bundle,
            self.theorem_source_validation.identity: self.theorem_source_validation,
        }

    @property
    def bundle(self) -> dict[object, object]:
        return self.theorem_source_validation_bundle


def make_k3c_analysis_semantic_profiles(
    *,
    k3b_profiles: object = k3.K3B_SEMANTIC_PROFILES,
    kernel_law: bytes = ANALYSIS_KERNEL_LAW_SOURCE,
    property_law: bytes = ANALYSIS_PROPERTY_LAW_SOURCE,
    transport_law: bytes = ANALYSIS_TRANSPORT_LAW_SOURCE,
    theorem_source_validation_law: bytes = (
        ANALYSIS_THEOREM_SOURCE_VALIDATION_LAW_SOURCE
    ),
) -> AnalysisSemanticProfiles:
    if type(k3b_profiles) is not k3.K3BSemanticProfiles:
        raise AnalysisError("Analysis needs one exact Relations profile bundle")
    kernel = k1.SemanticLanguageProfile(
        k1.Symbol("zkc.analysis.kernel"),
        0,
        (),
        tuple(k1.Symbol(item) for item in ANALYSIS_KERNEL_SUBJECT_KINDS),
        _profile_catalogs(ANALYSIS_KERNEL_DECLARATION_CATALOGS),
        kernel_law,
    )
    property_profile = k1.SemanticLanguageProfile(
        k1.Symbol("zkc.analysis.bounded-property"),
        0,
        _profile_imports(
            kernel,
            k3b_profiles.relations_correspondence,
            k3b_profiles.k2_profiles.interaction,
            k3b_profiles.k2_profiles.transcript_fs,
            k3b_profiles.k2_profiles.public_view,
        ),
        tuple(k1.Symbol(item) for item in ANALYSIS_PROPERTY_SUBJECT_KINDS),
        _profile_catalogs(ANALYSIS_PROPERTY_DECLARATION_CATALOGS),
        property_law,
    )
    transport = k1.SemanticLanguageProfile(
        k1.Symbol("zkc.analysis.bounded-transport"),
        0,
        _profile_imports(property_profile),
        tuple(k1.Symbol(item) for item in ANALYSIS_TRANSPORT_SUBJECT_KINDS),
        _profile_catalogs(ANALYSIS_TRANSPORT_DECLARATION_CATALOGS),
        transport_law,
    )
    theorem_source_validation = k1.SemanticLanguageProfile(
        k1.Symbol("zkc.analysis.afk-theorem-source-validation"),
        0,
        _profile_imports(transport),
        tuple(
            k1.Symbol(item) for item in ANALYSIS_THEOREM_SOURCE_VALIDATION_SUBJECT_KINDS
        ),
        _profile_catalogs(ANALYSIS_THEOREM_SOURCE_VALIDATION_DECLARATION_CATALOGS),
        theorem_source_validation_law,
    )
    return AnalysisSemanticProfiles(
        k3b_profiles,
        kernel,
        property_profile,
        transport,
        theorem_source_validation,
    )


ANALYSIS_SEMANTIC_PROFILES = make_k3c_analysis_semantic_profiles()
ANALYSIS_KERNEL_PROFILE = ANALYSIS_SEMANTIC_PROFILES.kernel
ANALYSIS_KERNEL_PROFILE_ID = ANALYSIS_KERNEL_PROFILE.identity
ANALYSIS_PROPERTY_PROFILE = ANALYSIS_SEMANTIC_PROFILES.property
ANALYSIS_PROPERTY_PROFILE_ID = ANALYSIS_PROPERTY_PROFILE.identity
ANALYSIS_TRANSPORT_PROFILE = ANALYSIS_SEMANTIC_PROFILES.transport
ANALYSIS_TRANSPORT_PROFILE_ID = ANALYSIS_TRANSPORT_PROFILE.identity
ANALYSIS_THEOREM_SOURCE_VALIDATION_PROFILE = (
    ANALYSIS_SEMANTIC_PROFILES.theorem_source_validation
)
ANALYSIS_THEOREM_SOURCE_VALIDATION_PROFILE_ID = (
    ANALYSIS_THEOREM_SOURCE_VALIDATION_PROFILE.identity
)
ANALYSIS_KERNEL_PROFILE_BUNDLE = ANALYSIS_SEMANTIC_PROFILES.kernel_bundle
ANALYSIS_PROPERTY_PROFILE_BUNDLE = ANALYSIS_SEMANTIC_PROFILES.property_bundle
ANALYSIS_TRANSPORT_PROFILE_BUNDLE = ANALYSIS_SEMANTIC_PROFILES.transport_bundle
ANALYSIS_THEOREM_SOURCE_VALIDATION_PROFILE_BUNDLE = (
    ANALYSIS_SEMANTIC_PROFILES.theorem_source_validation_bundle
)
ANALYSIS_PROFILE_BUNDLE = ANALYSIS_SEMANTIC_PROFILES.bundle
ANALYSIS_PROFILE_PREIMAGES = ANALYSIS_PROFILE_BUNDLE


def _analysis_profile_bundle_snapshot(
    profile_bundle: object,
) -> tuple[tuple[object, object], ...]:
    """Form one immutable, value-keyed profile-closure cache key."""

    if type(profile_bundle) is not dict:
        raise AnalysisError("Analysis profile bundle has the wrong exact shape")
    try:
        snapshot = tuple(
            sorted(
                profile_bundle.items(),
                key=lambda entry: entry[0].internal_reference(),
            )
        )
        hash(snapshot)
    except (AttributeError, TypeError, k1.CanonicalError) as error:
        raise AnalysisError(
            "Analysis profile bundle is not immutable canonical data"
        ) from error
    return snapshot


@lru_cache(maxsize=64)
def _authenticated_analysis_profile_context(
    profile_id: object,
    profile_snapshot: tuple[tuple[object, object], ...],
) -> object:
    """Authenticate one inert profile closure once per exact value snapshot.

    The cache contains no invocation capability, issuer, mutable registry, or
    theorem result.  A changed profile body or identity changes the tuple key;
    unsuccessful authentication is never cached.
    """

    return k1.effective_semantic_context(
        profile_id,
        dict(profile_snapshot),
        semantic_regime=k1.SEMANTIC_REGIME_ID,
    )


_FAMILY_DERIVATION_VALUES: ContextVar[dict[tuple[object, ...], object] | None] = (
    ContextVar("analysis_family_derivation_values", default=None)
)
_FAMILY_DERIVATION_MISSING = object()


@contextmanager
def _family_derivation_scope() -> Iterable[None]:
    """Share pure family derivations only within one live operation."""

    current = _FAMILY_DERIVATION_VALUES.get()
    if current is not None:
        yield
        return
    token = _FAMILY_DERIVATION_VALUES.set({})
    try:
        yield
    finally:
        _FAMILY_DERIVATION_VALUES.reset(token)


def _family_derivation_value(
    key: tuple[object, ...],
    form: Callable[[], object],
) -> object:
    cache = _FAMILY_DERIVATION_VALUES.get()
    if cache is None:
        return form()
    prior = cache.get(key, _FAMILY_DERIVATION_MISSING)
    if prior is not _FAMILY_DERIVATION_MISSING:
        return prior
    value = form()
    cache[key] = value
    return value


def _family_static_value(
    label: str,
    *coordinates: object,
    form: Callable[[], object],
) -> object:
    """Share one inert family value during a single live operation.

    The active transport-profile identity is part of every key.  The cache is
    still deliberately request-local: it never survives a public validation
    operation and therefore cannot retain issuers, capabilities, registries,
    or a result formed under a later profile activation.
    """

    with _family_derivation_scope():
        return _family_derivation_value(
            (
                "family-static",
                label,
                ANALYSIS_TRANSPORT_PROFILE_ID,
                *coordinates,
            ),
            form,
        )


def _with_family_derivation_scope(
    function: Callable[..., object],
) -> Callable[..., object]:
    """Give one public operation a nonpersistent pure-derivation cache."""

    @wraps(function)
    def scoped(*args: object, **kwargs: object) -> object:
        with _family_derivation_scope():
            return function(*args, **kwargs)

    return scoped


def _active_analysis_profile_id(profile: object) -> object:
    """Resolve an active profile through its already authenticated coordinate."""

    if type(profile) is not k1.SemanticLanguageProfile:
        raise AnalysisError("Analysis profile has the wrong exact shape")
    candidates = (
        (ANALYSIS_KERNEL_PROFILE, ANALYSIS_KERNEL_PROFILE_ID),
        (ANALYSIS_PROPERTY_PROFILE, ANALYSIS_PROPERTY_PROFILE_ID),
        (ANALYSIS_TRANSPORT_PROFILE, ANALYSIS_TRANSPORT_PROFILE_ID),
        (
            ANALYSIS_THEOREM_SOURCE_VALIDATION_PROFILE,
            ANALYSIS_THEOREM_SOURCE_VALIDATION_PROFILE_ID,
        ),
    )
    for active, identifier in candidates:
        if profile is active:
            return identifier
    matches = tuple(
        identifier for active, identifier in candidates if profile == active
    )
    if len(matches) != 1:
        raise AnalysisError("unknown or ambiguous active Analysis profile")
    return matches[0]


def _bundled_semantic_profile_id(profile: object) -> object:
    """Resolve an exact profile already present in the authenticated bundle."""

    if type(profile) is not k1.SemanticLanguageProfile:
        raise AnalysisError("semantic profile has the wrong exact shape")
    identical = tuple(
        identifier
        for identifier, preimage in ANALYSIS_PROFILE_BUNDLE.items()
        if preimage is profile
    )
    if len(identical) == 1:
        return identical[0]
    matches = tuple(
        identifier
        for identifier, preimage in ANALYSIS_PROFILE_BUNDLE.items()
        if preimage == profile
    )
    if len(matches) != 1:
        raise AnalysisError("semantic profile is absent or ambiguous in its bundle")
    return matches[0]


def _analysis_profile_declaration_ordinal(
    profile: object,
    declaration_kind: str,
    label: str,
) -> int:
    """Resolve one exact declaration label to its profile-local ordinal."""

    if type(profile) is not k1.SemanticLanguageProfile:
        raise AnalysisError("declaration owner must be one exact language profile")
    return _cached_analysis_profile_declaration_ordinal(
        profile, declaration_kind, label
    )


@lru_cache(maxsize=2048)
def _cached_analysis_profile_declaration_ordinal(
    profile: object,
    declaration_kind: str,
    label: str,
) -> int:
    """Resolve one immutable profile catalog entry once per exact value."""

    catalog = k1.profile_declaration_catalogs(profile).get(declaration_kind)
    if catalog is None:
        raise AnalysisError(
            f"Analysis declaration catalog {declaration_kind!r} is absent"
        )
    matches: list[int] = []
    for ordinal, body in enumerate(catalog.values):
        if type(body) is not k1.DatumRecord:
            raise AnalysisError("Analysis declaration body has the wrong shape")
        fields = dict(body.fields)
        if type(fields.get(0)) is not k1.Symbol:
            raise AnalysisError("Analysis declaration label has the wrong shape")
        if fields[0].value == label:
            matches.append(ordinal)
    if len(matches) != 1:
        raise AnalysisError(
            f"Analysis declaration {declaration_kind!r}/{label!r} is not unique"
        )
    return matches[0]


def _analysis_profile_import_closure(profile: object) -> frozenset[object]:
    """Return the exact authenticated import cone from the active Analysis bundle."""

    pending = list(profile.profile_imports)
    result: set[object] = set()
    while pending:
        profile_id = pending.pop()
        if profile_id in result:
            continue
        imported = ANALYSIS_PROFILE_BUNDLE.get(profile_id)
        if type(imported) is not k1.SemanticLanguageProfile:
            raise AnalysisError("Analysis profile import is absent from its bundle")
        result.add(profile_id)
        pending.extend(imported.profile_imports)
    return frozenset(result)


def analysis_profile_declaration_ref(
    selected_profile: object,
    owner_profile: object,
    declaration_kind: str,
    label: str,
) -> object:
    """Form one exact local/imported ref and reject ambient label lookup."""

    ordinal = _analysis_profile_declaration_ordinal(
        owner_profile, declaration_kind, label
    )
    selected_profile_id = _active_analysis_profile_id(selected_profile)
    owner_profile_id = _bundled_semantic_profile_id(owner_profile)
    if selected_profile_id == owner_profile_id:
        reference = k1.ProfileLocalDeclarationRef(declaration_kind, ordinal)
    else:
        if owner_profile_id not in _analysis_profile_import_closure(selected_profile):
            raise AnalysisError(
                "declaration owner is outside the selected profile cone"
            )
        reference = k1.ImportedProfileDeclarationRef(
            owner_profile_id, declaration_kind, ordinal
        )
    k1.profile_declaration_ref_datum(reference)
    return reference


def analysis_profile_declaration_ref_body(reference: object) -> object:
    try:
        return k1.profile_declaration_ref_datum(reference)
    except k1.ModelError as error:
        raise AnalysisError(str(error)) from error


def _analysis_datum(value: object, what: str) -> object:
    try:
        k1.encode_datum(value)
    except (k1.CanonicalError, TypeError) as error:
        raise AnalysisError(f"{what} is not one exact canonical datum") from error
    return value


@dataclass(frozen=True)
class AnalysisConsumerIntakeBodyV0:
    consumer: object


@dataclass(frozen=True)
class AnalysisUsePurposeIntakeBodyV0:
    purpose: object


@dataclass(frozen=True)
class AnalysisQuestionBodyV0:
    family: object
    exact_subjects: tuple[object, ...]
    context: object
    family_payload: object


@dataclass(frozen=True)
class AnalysisAdequacyEvaluatorBodyV0:
    input_schema: object
    supported_input_profile_ids: tuple[object, ...]
    output_schema: object
    portable_algorithm_ref: object
    evaluation_contract_id: object
    exact_direct_module_roots: tuple[object, ...]
    success_value: bool
    failure_partition: object


@dataclass(frozen=True)
class AnalysisSourceProfileBodyV0:
    family_tag: object
    slot_schemas: object
    closed_field_read_set: object
    adequacy_evaluator_id: object


@dataclass(frozen=True)
class AnalysisSemanticReadManifestBodyV0:
    source_profile_id: object
    exact_subjects: tuple[object, ...]
    slots: object


class AnalysisReadPurpose(str, Enum):
    SEMANTIC_MEANING = "SemanticMeaning"
    PREMISE_SUPPORT = "PremiseSupport"
    OCCURRENCE_EVIDENCE = "OccurrenceEvidence"


@dataclass(frozen=True)
class ConcreteReadPurpose:
    semantic_read_manifest_id: object
    semantic_read_slot_ordinal: int
    exact_purpose: AnalysisReadPurpose


@dataclass(frozen=True)
class FamilyReadPurpose:
    family_read_manifest_schema_id: object
    family_read_slot_ordinal: int
    exact_purpose: AnalysisReadPurpose


AnalysisReadPurposeRequirement = ConcreteReadPurpose | FamilyReadPurpose


@dataclass(frozen=True)
class NormalizedAnalysisReadPurpose:
    requirement: AnalysisReadPurposeRequirement
    exact_slot: object


@dataclass(frozen=True)
class AnalysisSourceSupportBodyV0:
    semantic_read_manifest_id: object
    bindings: object
    derived_owner_policy_dependency_closure: tuple[object, ...]


@dataclass(frozen=True)
class AnalysisCheckedResultCoordinateBodyV0:
    result_id: object
    proposition_id: object
    semantic_basis_id: object
    support_id: object
    validation_basis_id: object
    qualification: object
    outcome_kind: object


@dataclass(frozen=True)
class AnalysisCapabilityRequirementPayloadBodyV0:
    proposition_id: object
    qualification: object
    named_consumer: object
    typed_purpose: object


@dataclass(frozen=True)
class AnalysisSourceAuthorityContractBodyV0:
    owner_coordinate: object
    checked_result_coordinate_id: object
    capability_requirement_payload_id: object
    immediate_policy_ids: tuple[object, ...]
    transitive_policy_ids: tuple[object, ...]


@dataclass(frozen=True)
class AnalysisOwnerPolicyClosureBodyV0:
    owner_coordinate: object
    policy_ids: tuple[object, ...]
    derivation_law: object


@dataclass(frozen=True)
class AnalysisPortableSourceAuthorityBindingBodyV0:
    envelope: object


@dataclass(frozen=True)
class AnalysisStrategyClassBodyV0:
    role: object
    dependent_parameter_schema: object
    strategy_abi: object
    private_state_type: object
    initial_advice_type: object
    allowed_views: object
    allowed_oracles_and_capabilities: object
    legal_move_relation: object
    stop_and_noncompletion_law: object
    resource_dimensions: object


@dataclass(frozen=True)
class AnalysisDistributionProfileBodyV0:
    output_type: object
    exact_support_predicate: object
    exact_probability_mass_or_measure_law: object
    parameter_and_security_parameter_coordinates: object
    independence_and_correlation_declarations: object
    sampling_or_oracle_denotation: object
    failure_and_nontermination_law: object


@dataclass(frozen=True)
class AnalysisExtractorProfileBodyV0:
    input_and_output_types: object
    private_state_and_randomness_types: object
    allowed_source_and_oracle_capabilities: object
    counterfactual_rights: object
    state_preservation_relation: object
    output_distribution_preservation_relation: object
    witness_success_relation: object
    termination_and_asymptotic_resource_law: object
    counterfactual_capability_contract_and_property_family_scope: object


@dataclass(frozen=True)
class AnalysisPositivePolynomialProfileBodyV0:
    input_sort: object
    coefficient_domain: object
    value_shape: object
    canonical_degree_rule: object
    evaluation: object
    positivity_rule: object
    admitted_coefficient_and_degree_bounds: object


@dataclass(frozen=True)
class AnalysisPositivePolynomialBodyV0:
    profile_id: object
    coefficients_low_to_high: tuple[int, ...]


@dataclass(frozen=True)
class AnalysisExperimentProfileBodyV0:
    family: object
    source_profile_id: object
    quantifier_prefix: object
    role_interfaces: object
    setup_and_input_sampling: object
    randomness_ownership_and_independence: object
    public_coin_or_oracle_model: object
    scheduler: object
    generated_execution_relation: object
    observation_and_win_event: object
    failure_abort_and_noncompletion_law: object
    termination_law: object
    resource_basis: object
    output_type: object


@dataclass(frozen=True)
class AnalysisAsymptoticProtocolFamilyBodyV0:
    family_language: object
    canonical_family_payload: object


@dataclass(frozen=True)
class AnalysisFamilyReadManifestSchemaBodyV0:
    family_definition_id: object
    member_source_profile_id: object


@dataclass(frozen=True)
class AnalysisChallengeDomainBodyV0:
    source_challenge_ref: object
    value_type: object
    source_nominal_domain_ref: object
    model_values: tuple[int, ...]
    adequacy_evaluator_id: object
    semantic_status: object
    _issuer: object


_CHALLENGE_DOMAIN_BODY_ISSUER = object()


@dataclass(frozen=True)
class AnalysisFixedPublicSetupBodyV0:
    exact_static_sources: object
    exact_public_invocation_sources: object
    derived_projection: object
    required_selection_schedule: object
    visibility_map: object


@dataclass(frozen=True)
class AnalysisQuantitativeFormulaBodyV0:
    result_sort: object
    parameter_schema: object
    declared_parameter_independence: object
    expression: object


@dataclass(frozen=True)
class AnalysisLogicalNatLiteralBodyV0:
    value: int


@dataclass(frozen=True)
class AnalysisNativeSubjectProjectionBodyV0:
    core_id: object
    fresh_protocol_id: object
    fiat_shamir_protocol_id: object
    fresh_binding_id: object
    fiat_shamir_binding_id: object
    fresh_manifest_id: object
    pair_manifest_id: object
    fresh_plan_binding_id: object
    fiat_shamir_plan_binding_id: object


@dataclass(frozen=True)
class AnalysisFamilyInstanceRoleMapBodyV0:
    family_id: object
    logical_index_id: object
    native_subject_refs: object
    native_length_value: object
    role: object
    abstract_role_ref: object
    native_role_ref: object
    map_clause_coordinate: object
    information_loss: object


@dataclass(frozen=True)
class AnalysisPointwiseQuantitativeNormalizationBodyV0:
    logical_index_substitution: object
    challenge_cardinality_substitution: object
    positive_polynomial_profile_substitution: object
    positive_polynomial_value_substitution: object
    resource_substitution: object
    canonical_formula_normalization: object
    required_equal_normal_forms: object


@dataclass(frozen=True)
class AnalysisLossSemanticImportBodyV0:
    relations_bridge_id: object
    lossy_use_scope_and_occurrence_schema: object
    direction: object
    source_premise_and_quantitative_export_id: object
    result_sort: object
    interpretation_rule: object
    parameter_substitution: object
    per_occurrence_expression: object


@dataclass(frozen=True)
class AnalysisGoalBodyV0:
    question_id: object


@dataclass(frozen=True)
class AnalysisHypothesisNodeV0:
    local_ordinal: int
    goal_id: object
    dependency_ordinals: tuple[int, ...] = ()


@dataclass(frozen=True)
class AnalysisHypothesisContextBodyV0:
    nodes: tuple[AnalysisHypothesisNodeV0, ...]
    roots: tuple[int, ...]


@dataclass(frozen=True)
class AnalysisPropositionBodyV0:
    goal_id: object
    hypothesis_context_id: object


@dataclass(frozen=True)
class AnalysisSemanticBasisBodyV0:
    family: object
    exact_question_id: object
    rule_source: object
    exact_premise_schemas: object
    source_read_purposes: tuple[AnalysisReadPurposeRequirement, ...]
    conclusion_schema: object
    typed_transform_program: object


@dataclass(frozen=True)
class AnalysisSupportInstantiationBodyV0:
    semantic_basis_id: object
    proposition_id: object
    non_hypothesis_premise_bindings: object
    established_hypothesis_node_bindings: object
    assumed_hypothesis_node_bindings: object
    source_support_bindings: object


@dataclass(frozen=True)
class AnalysisValidationBasisBodyV0:
    admitted_checker_contract_ids_and_abis: object
    exact_translation_contracts: object
    finite_control_contracts: object
    theorem_source_validation_ids: object
    residual_trust_roots: object


@dataclass(frozen=True)
class AnalysisOperationPolicyBodyV0:
    supported_families_and_models: object
    named_consumer_and_typed_purpose_permissions: object
    capability_freshness_and_lifetime: object
    disclosure_policy: object
    unknown_question_disposition: object
    persistence_policy: object
    cold_replay_policy: object


@dataclass(frozen=True)
class AnalysisJudgmentRecordBodyV0:
    proposition_id: object
    polarity: object
    exact_family_conclusion: object
    inherited_hypothesis_context_id: object
    typed_quantitative_result: object
    semantic_basis_id: object
    support_coordinate: object
    validation_basis_id: object
    qualification: object
    operation_policy_id: object
    derived_source_policy_dependency_closure: object


@dataclass(frozen=True)
class AnalysisTheoremSchemaBodyV0:
    local_binding_catalog: object
    source_property_schema: object
    target_property_schema: object
    source_experiment_schema: object
    target_experiment_schema: object
    required_source_view_schemas: object
    map_schemas: object
    side_condition_and_parameter_schemas: object
    local_quantitative_operator_catalog: object
    typed_resource_and_loss_transform_program: object
    exact_conclusion_reconstruction_law: object


@dataclass(frozen=True)
class AnalysisTheoremSourceValidationBodyV0:
    theorem_schema_id: object
    source_authority: object
    truth_discharge_metadata: object


_ANALYSIS_EXACT_BODY_TYPES = {
    "analysis.adequacy-evaluator": AnalysisAdequacyEvaluatorBodyV0,
    "analysis.source-profile": AnalysisSourceProfileBodyV0,
    "analysis.semantic-read-manifest": AnalysisSemanticReadManifestBodyV0,
    "analysis.source-support": AnalysisSourceSupportBodyV0,
    "analysis.checked-result-coordinate": AnalysisCheckedResultCoordinateBodyV0,
    "analysis.capability-requirement-payload": AnalysisCapabilityRequirementPayloadBodyV0,
    "analysis.source-authority-contract": AnalysisSourceAuthorityContractBodyV0,
    "analysis.owner-policy-closure": AnalysisOwnerPolicyClosureBodyV0,
    "analysis.portable-source-authority-binding": AnalysisPortableSourceAuthorityBindingBodyV0,
    "analysis.strategy-class": AnalysisStrategyClassBodyV0,
    "analysis.distribution-profile": AnalysisDistributionProfileBodyV0,
    "analysis.extractor-profile": AnalysisExtractorProfileBodyV0,
    "analysis.positive-polynomial-profile": AnalysisPositivePolynomialProfileBodyV0,
    "analysis.positive-polynomial": AnalysisPositivePolynomialBodyV0,
    "analysis.experiment-profile": AnalysisExperimentProfileBodyV0,
    "analysis.asymptotic-protocol-family": AnalysisAsymptoticProtocolFamilyBodyV0,
    "analysis.family-read-manifest-schema": AnalysisFamilyReadManifestSchemaBodyV0,
    "analysis.challenge-domain": AnalysisChallengeDomainBodyV0,
    "analysis.fixed-public-setup": AnalysisFixedPublicSetupBodyV0,
    "analysis.quantitative-formula": AnalysisQuantitativeFormulaBodyV0,
    "analysis.logical-nat-literal": AnalysisLogicalNatLiteralBodyV0,
    "analysis.native-subject-projection": AnalysisNativeSubjectProjectionBodyV0,
    "analysis.family-instance-role-map": AnalysisFamilyInstanceRoleMapBodyV0,
    "analysis.pointwise-quantitative-normalization": AnalysisPointwiseQuantitativeNormalizationBodyV0,
    "analysis.consumer": AnalysisConsumerIntakeBodyV0,
    "analysis.use-purpose": AnalysisUsePurposeIntakeBodyV0,
    "analysis.question": AnalysisQuestionBodyV0,
    "analysis.goal": AnalysisGoalBodyV0,
    "analysis.hypothesis-context": AnalysisHypothesisContextBodyV0,
    "analysis.proposition": AnalysisPropositionBodyV0,
    "analysis.loss-semantic-import": AnalysisLossSemanticImportBodyV0,
    "analysis.semantic-basis": AnalysisSemanticBasisBodyV0,
    "analysis.support-instantiation": AnalysisSupportInstantiationBodyV0,
    "analysis.validation-basis": AnalysisValidationBasisBodyV0,
    "analysis.operation-policy": AnalysisOperationPolicyBodyV0,
    "analysis.judgment-record": AnalysisJudgmentRecordBodyV0,
    "analysis.theorem-schema": AnalysisTheoremSchemaBodyV0,
    "analysis.theorem-source-validation": AnalysisTheoremSourceValidationBodyV0,
}


def _analysis_hypothesis_context_body(
    body: AnalysisHypothesisContextBodyV0,
) -> object:
    if type(body.nodes) is not tuple or type(body.roots) is not tuple:
        raise PropertyError("hypothesis DAG must use immutable tuples")
    if len(body.nodes) > MAX_HYPOTHESES:
        raise PropertyError("hypothesis DAG exceeds its finite bound")
    if tuple(node.local_ordinal for node in body.nodes) != tuple(
        range(len(body.nodes))
    ):
        raise PropertyError("hypothesis node ordinals must be contiguous")
    goal_refs: set[bytes] = set()
    depended_on: set[int] = set()
    encoded_nodes = []
    for node in body.nodes:
        if type(node) is not AnalysisHypothesisNodeV0:
            raise PropertyError("hypothesis DAG contains a foreign node")
        _id_datum(node.goal_id, "analysis.goal")
        goal_ref = node.goal_id.internal_reference()
        if goal_ref in goal_refs:
            raise PropertyError("hypothesis DAG repeats a goal")
        goal_refs.add(goal_ref)
        if (
            type(node.dependency_ordinals) is not tuple
            or node.dependency_ordinals != tuple(sorted(set(node.dependency_ordinals)))
            or any(
                type(item) is not int or not 0 <= item < node.local_ordinal
                for item in node.dependency_ordinals
            )
        ):
            raise PropertyError(
                "hypothesis dependencies must be sorted unique earlier ordinals"
            )
        depended_on.update(node.dependency_ordinals)
        encoded_nodes.append(
            k1.DatumRecord(
                (
                    (0, k1.Nat(node.local_ordinal)),
                    (1, _id_datum(node.goal_id, "analysis.goal")),
                    (
                        2,
                        k1.DatumSeq(
                            tuple(k1.Nat(item) for item in node.dependency_ordinals)
                        ),
                    ),
                )
            )
        )
    derived_roots = tuple(
        ordinal for ordinal in range(len(body.nodes)) if ordinal not in depended_on
    )
    if body.roots != derived_roots:
        raise PropertyError("hypothesis roots must equal the derived outward frontier")
    reachable: set[int] = set()
    pending = list(body.roots)
    while pending:
        ordinal = pending.pop()
        if ordinal in reachable:
            continue
        if not 0 <= ordinal < len(body.nodes):
            raise PropertyError("hypothesis root is out of range")
        reachable.add(ordinal)
        pending.extend(body.nodes[ordinal].dependency_ordinals)
    if reachable != set(range(len(body.nodes))):
        raise PropertyError("hypothesis DAG contains an unreachable node")
    return k1.DatumRecord(
        (
            (0, k1.DatumSeq(tuple(encoded_nodes))),
            (1, k1.DatumSeq(tuple(k1.Nat(item) for item in body.roots))),
        )
    )


def _challenge_domain_atomic_coordinate_fields(
    value: object,
    leaf: k2.StaticViewAtomicLeaf,
) -> tuple[object, ...]:
    """Validate one exact atomic PublicCoinView challenge coordinate body."""

    if type(value) is not k1.DatumRecord or tuple(
        ordinal for ordinal, _ in value.fields
    ) != tuple(range(6)):
        raise AnalysisError("challenge-domain coordinate has the wrong exact shape")
    coordinate = dict(value.fields)
    owner = coordinate[0]
    if type(owner) is not k1.DatumRecord or tuple(
        ordinal for ordinal, _ in owner.fields
    ) != tuple(range(4)):
        raise AnalysisError("challenge-domain owner coordinate has the wrong shape")
    owner_fields = dict(owner.fields)
    expected_symbols = (
        (owner_fields[0], k2.StaticViewOwnerKind.CORE.value),
        (owner_fields[2], k2.StaticViewKind.PUBLIC_COIN.value),
        (coordinate[1], k2.StaticViewField.PC_CHALLENGES.value),
        (coordinate[5], leaf.value),
    )
    if any(
        type(actual) is not k1.Symbol or actual.value != expected
        for actual, expected in expected_symbols
    ):
        raise AnalysisError(
            "challenge-domain coordinate is not one exact Core PublicCoinView leaf"
        )
    if (
        type(owner_fields[1]) is not k1.BytesValue
        or type(owner_fields[3]) is not k1.BytesValue
        or type(coordinate[2]) is not k1.Nat
        or type(coordinate[3]) is not k1.Nat
        or coordinate[2].value < 0
        or coordinate[3].value < 0
        or type(coordinate[4]) is not k1.Symbol
    ):
        raise AnalysisError("challenge-domain coordinate has malformed owner fields")
    _ascii(coordinate[4].value, "challenge occurrence coordinate")
    return (
        owner,
        coordinate[1],
        coordinate[2],
        coordinate[3],
        coordinate[4],
    )


_COUNTERFACTUAL_RIGHT_CAPABILITY = {
    "ProgramSibling": "program-sibling",
    "Rerun": "root-rerun",
}


def _exact_symbol_sequence(value: object, what: str) -> tuple[str, ...]:
    if type(value) is not k1.DatumSeq or any(
        type(item) is not k1.Symbol for item in value.values
    ):
        raise AnalysisError(f"{what} must be one exact symbol sequence")
    result = tuple(item.value for item in value.values)
    for item in result:
        _ascii(item, what)
    return result


def analysis_domain_body_v0(subject_kind: str, body: object) -> object:
    """Compile the closed active Analysis Analysis body algebra."""

    expected = _ANALYSIS_EXACT_BODY_TYPES.get(subject_kind)
    if expected is None:
        raise AnalysisError(f"{subject_kind} has no active AnalysisBodyV0 arm")
    if type(body) is not expected:
        raise AnalysisError(
            f"{subject_kind} needs exact {expected.__name__}, not a raw host body"
        )
    if type(body) is AnalysisAdequacyEvaluatorBodyV0:
        if (
            type(body.supported_input_profile_ids) is not tuple
            or not body.supported_input_profile_ids
            or body.supported_input_profile_ids
            != tuple(
                sorted(
                    set(body.supported_input_profile_ids),
                    key=lambda item: item.internal_reference(),
                )
            )
            or body.success_value is not True
        ):
            raise AnalysisError("adequacy evaluator has a noncanonical profile set")
        result = k1.DatumRecord(
            (
                (0, analysis_profile_declaration_ref_body(body.input_schema)),
                (
                    1,
                    k1.DatumSeq(
                        tuple(
                            _id_datum(item, "foundation.semantic-language-profile")
                            for item in body.supported_input_profile_ids
                        )
                    ),
                ),
                (2, _analysis_datum(body.output_schema, "adequacy output schema")),
                (
                    3,
                    _id_datum(
                        body.portable_algorithm_ref, "foundation.portable-algorithm"
                    ),
                ),
                (
                    4,
                    _id_datum(
                        body.evaluation_contract_id, "foundation.evaluation-contract"
                    ),
                ),
                (
                    5,
                    k1.DatumSeq(
                        tuple(
                            _id_datum(item) for item in body.exact_direct_module_roots
                        )
                    ),
                ),
                (6, True),
                (7, analysis_profile_declaration_ref_body(body.failure_partition)),
            )
        )
    elif type(body) is AnalysisSourceProfileBodyV0:
        _admit_source_profile_read_purposes(body)
        result = k1.DatumRecord(
            (
                (0, analysis_profile_declaration_ref_body(body.family_tag)),
                (1, _analysis_datum(body.slot_schemas, "source slot schemas")),
                (
                    2,
                    _analysis_datum(
                        body.closed_field_read_set, "closed field read set"
                    ),
                ),
                (
                    3,
                    _id_datum(
                        body.adequacy_evaluator_id, "analysis.adequacy-evaluator"
                    ),
                ),
            )
        )
    elif type(body) is AnalysisSemanticReadManifestBodyV0:
        _admit_concrete_semantic_read_manifest(body)
        result = k1.DatumRecord(
            (
                (0, _id_datum(body.source_profile_id, "analysis.source-profile")),
                (
                    1,
                    k1.DatumSeq(tuple(_id_datum(item) for item in body.exact_subjects)),
                ),
                (2, _analysis_datum(body.slots, "semantic read slots")),
            )
        )
    elif type(body) is AnalysisSourceSupportBodyV0:
        closure = _canonical_identifier_set(
            body.derived_owner_policy_dependency_closure,
            what="source-support owner-policy closure",
        )
        if closure != body.derived_owner_policy_dependency_closure:
            raise AnalysisError("source-support owner-policy closure is not canonical")
        result = k1.DatumRecord(
            (
                (
                    0,
                    _id_datum(
                        body.semantic_read_manifest_id,
                        "analysis.semantic-read-manifest",
                    ),
                ),
                (1, _analysis_datum(body.bindings, "source-support bindings")),
                (2, k1.DatumSeq(tuple(_id_datum(item) for item in closure))),
            )
        )
    elif type(body) is AnalysisCheckedResultCoordinateBodyV0:
        result = k1.DatumRecord(
            (
                (0, _id_datum(body.result_id)),
                (1, _id_datum(body.proposition_id, "analysis.proposition")),
                (2, _id_datum(body.semantic_basis_id, "analysis.semantic-basis")),
                (3, _id_datum(body.support_id, "analysis.support-instantiation")),
                (4, _id_datum(body.validation_basis_id, "analysis.validation-basis")),
                (5, analysis_profile_declaration_ref_body(body.qualification)),
                (6, _analysis_datum(body.outcome_kind, "checked-result outcome kind")),
            )
        )
    elif type(body) is AnalysisCapabilityRequirementPayloadBodyV0:
        result = k1.DatumRecord(
            (
                (0, _id_datum(body.proposition_id, "analysis.proposition")),
                (1, analysis_profile_declaration_ref_body(body.qualification)),
                (2, analysis_profile_declaration_ref_body(body.named_consumer)),
                (3, analysis_profile_declaration_ref_body(body.typed_purpose)),
            )
        )
    elif type(body) is AnalysisSourceAuthorityContractBodyV0:
        immediate = _canonical_identifier_set(
            body.immediate_policy_ids, what="immediate policies"
        )
        transitive = _canonical_identifier_set(
            body.transitive_policy_ids, what="transitive policies"
        )
        if (
            immediate != body.immediate_policy_ids
            or transitive != body.transitive_policy_ids
            or set(immediate) & set(transitive)
        ):
            raise AnalysisError(
                "source-authority policy sets are not canonical and disjoint"
            )
        result = k1.DatumRecord(
            (
                (0, _id_datum(body.owner_coordinate)),
                (
                    1,
                    _id_datum(
                        body.checked_result_coordinate_id,
                        "analysis.checked-result-coordinate",
                    ),
                ),
                (
                    2,
                    _id_datum(
                        body.capability_requirement_payload_id,
                        "analysis.capability-requirement-payload",
                    ),
                ),
                (3, k1.DatumSeq(tuple(_id_datum(item) for item in immediate))),
                (4, k1.DatumSeq(tuple(_id_datum(item) for item in transitive))),
            )
        )
    elif type(body) is AnalysisOwnerPolicyClosureBodyV0:
        policies = _canonical_identifier_set(
            body.policy_ids, what="owner-policy closure"
        )
        if policies != body.policy_ids:
            raise AnalysisError("owner-policy closure is not canonical")
        result = k1.DatumRecord(
            (
                (0, _id_datum(body.owner_coordinate)),
                (1, k1.DatumSeq(tuple(_id_datum(item) for item in policies))),
                (
                    2,
                    _analysis_datum(body.derivation_law, "owner-policy derivation law"),
                ),
            )
        )
    elif type(body) is AnalysisPortableSourceAuthorityBindingBodyV0:
        try:
            result = k1.portable_source_authority_binding_body(body.envelope)
        except (k1.ModelError, k1.CanonicalError) as error:
            raise AnalysisError(str(error)) from error
    elif type(body) is AnalysisExtractorProfileBodyV0:
        capabilities = _exact_symbol_sequence(
            body.allowed_source_and_oracle_capabilities,
            "extractor capability",
        )
        rights = _exact_symbol_sequence(
            body.counterfactual_rights,
            "extractor counterfactual right",
        )
        if rights != tuple(sorted(set(rights))):
            raise AnalysisError(
                "extractor counterfactual rights must be canonical sorted unique"
            )
        if any(right not in _COUNTERFACTUAL_RIGHT_CAPABILITY for right in rights):
            raise AnalysisError(
                "extractor profile uses a retired counterfactual-right tag"
            )
        if any(
            _COUNTERFACTUAL_RIGHT_CAPABILITY[right] not in capabilities
            for right in rights
        ):
            raise AnalysisError(
                "extractor counterfactual right lacks its capability denotation"
            )
        result = k1.DatumRecord(
            tuple(
                (ordinal, _analysis_datum(value, f"{subject_kind} field {ordinal}"))
                for ordinal, value in enumerate(
                    getattr(body, field.name) for field in dataclass_fields(type(body))
                )
            )
        )
    elif type(body) in (
        AnalysisStrategyClassBodyV0,
        AnalysisDistributionProfileBodyV0,
        AnalysisPositivePolynomialProfileBodyV0,
        AnalysisExperimentProfileBodyV0,
        AnalysisFixedPublicSetupBodyV0,
        AnalysisFamilyInstanceRoleMapBodyV0,
        AnalysisPointwiseQuantitativeNormalizationBodyV0,
        AnalysisLossSemanticImportBodyV0,
    ):
        result = k1.DatumRecord(
            tuple(
                (ordinal, _analysis_datum(value, f"{subject_kind} field {ordinal}"))
                for ordinal, value in enumerate(
                    getattr(body, field.name) for field in dataclass_fields(type(body))
                )
            )
        )
    elif type(body) is AnalysisPositivePolynomialBodyV0:
        if (
            type(body.coefficients_low_to_high) is not tuple
            or not body.coefficients_low_to_high
        ):
            raise AnalysisError("positive polynomial needs nonempty coefficients")
        result = k1.DatumRecord(
            (
                (0, _id_datum(body.profile_id, "analysis.positive-polynomial-profile")),
                (
                    1,
                    k1.DatumSeq(
                        tuple(k1.Nat(item) for item in body.coefficients_low_to_high)
                    ),
                ),
            )
        )
    elif type(body) is AnalysisAsymptoticProtocolFamilyBodyV0:
        result = k1.DatumRecord(
            (
                (0, analysis_profile_declaration_ref_body(body.family_language)),
                (
                    1,
                    _analysis_datum(
                        body.canonical_family_payload, "canonical family payload"
                    ),
                ),
            )
        )
    elif type(body) is AnalysisFamilyReadManifestSchemaBodyV0:
        result = k1.DatumRecord(
            (
                (
                    0,
                    _id_datum(
                        body.family_definition_id, "analysis.asymptotic-protocol-family"
                    ),
                ),
                (
                    1,
                    _id_datum(body.member_source_profile_id, "analysis.source-profile"),
                ),
            )
        )
    elif type(body) is AnalysisChallengeDomainBodyV0:
        if body._issuer is not _CHALLENGE_DOMAIN_BODY_ISSUER:
            raise AuthorityError(
                "challenge domain was not issued from one live PublicCoinView"
            )
        challenge_coordinate = _challenge_domain_atomic_coordinate_fields(
            body.source_challenge_ref,
            k2.StaticViewAtomicLeaf.CHALLENGE_OCCURRENCE,
        )
        domain_coordinate = _challenge_domain_atomic_coordinate_fields(
            body.source_nominal_domain_ref,
            k2.StaticViewAtomicLeaf.CHALLENGE_DOMAIN,
        )
        if challenge_coordinate != domain_coordinate:
            raise PropertyError(
                "challenge and nominal-domain leaves select different view entries"
            )
        expected_status = analysis_profile_declaration_ref_body(
            analysis_profile_declaration_ref(
                ANALYSIS_PROPERTY_PROFILE,
                ANALYSIS_PROPERTY_PROFILE,
                "analysis.semantic-law",
                "finite-challenge-domain-v0",
            )
        )
        if (
            body.value_type != k1.value_type_datum(k1.NAT_U64)
            or body.adequacy_evaluator_id != _challenge_domain_adequacy_evaluator_id()
            or body.semantic_status != expected_status
        ):
            raise PropertyError(
                "challenge domain has the wrong carrier, evaluator, or semantic law"
            )
        if (
            type(body.model_values) is not tuple
            or len(body.model_values) < 2
            or body.model_values != tuple(range(len(body.model_values)))
        ):
            raise PropertyError("challenge domain needs exact canonical finite values")
        result = k1.DatumRecord(
            (
                (0, _analysis_datum(body.source_challenge_ref, "source challenge ref")),
                (1, _analysis_datum(body.value_type, "challenge value type")),
                (
                    2,
                    _analysis_datum(
                        body.source_nominal_domain_ref, "nominal challenge domain ref"
                    ),
                ),
                (3, k1.DatumSeq(tuple(k1.Nat(item) for item in body.model_values))),
                (
                    4,
                    _id_datum(
                        body.adequacy_evaluator_id, "analysis.adequacy-evaluator"
                    ),
                ),
                (5, _analysis_datum(body.semantic_status, "challenge semantic status")),
            )
        )
    elif type(body) is AnalysisQuantitativeFormulaBodyV0:
        result = k1.DatumRecord(
            tuple(
                (
                    ordinal,
                    _analysis_datum(value, f"quantitative formula field {ordinal}"),
                )
                for ordinal, value in enumerate(
                    (
                        body.result_sort,
                        body.parameter_schema,
                        body.declared_parameter_independence,
                        body.expression,
                    )
                )
            )
        )
    elif type(body) is AnalysisLogicalNatLiteralBodyV0:
        if type(body.value) is not int or body.value < 0:
            raise AnalysisError("logical-natural literal must be a natural")
        result = k1.DatumRecord(((0, k1.Nat(body.value)),))
    elif type(body) is AnalysisNativeSubjectProjectionBodyV0:
        result = k1.DatumRecord(
            (
                (0, _id_datum(body.core_id, "pir.interactive-core")),
                (1, _id_datum(body.fresh_protocol_id, "pir.protocol")),
                (2, _id_datum(body.fiat_shamir_protocol_id, "pir.protocol")),
                (3, _id_datum(body.fresh_binding_id, "relations.protocol-binding")),
                (
                    4,
                    _id_datum(
                        body.fiat_shamir_binding_id,
                        "relations.protocol-binding",
                    ),
                ),
                (
                    5,
                    _id_datum(
                        body.fresh_manifest_id,
                        "analysis.semantic-read-manifest",
                    ),
                ),
                (
                    6,
                    _id_datum(
                        body.pair_manifest_id,
                        "analysis.semantic-read-manifest",
                    ),
                ),
                (
                    7,
                    _id_datum(
                        body.fresh_plan_binding_id,
                        "relations.plan-witness-binding",
                    ),
                ),
                (
                    8,
                    _id_datum(
                        body.fiat_shamir_plan_binding_id,
                        "relations.plan-witness-binding",
                    ),
                ),
            )
        )
    elif type(body) is AnalysisConsumerIntakeBodyV0:
        result = k1.DatumRecord(
            ((0, analysis_profile_declaration_ref_body(body.consumer)),)
        )
    elif type(body) is AnalysisUsePurposeIntakeBodyV0:
        result = k1.DatumRecord(
            ((0, analysis_profile_declaration_ref_body(body.purpose)),)
        )
    elif type(body) is AnalysisQuestionBodyV0:
        if type(body.exact_subjects) is not tuple or not body.exact_subjects:
            raise PropertyError("Analysis question needs nonempty exact subjects")
        subjects = body.exact_subjects
        if len(set(subjects)) != len(subjects):
            raise PropertyError("Analysis question subjects must not repeat")
        result = k1.DatumRecord(
            (
                (0, analysis_profile_declaration_ref_body(body.family)),
                (1, k1.DatumSeq(tuple(_id_datum(item) for item in subjects))),
                (2, _analysis_datum(body.context, "Analysis question context")),
                (3, _analysis_datum(body.family_payload, "Analysis family payload")),
            )
        )
    elif type(body) is AnalysisGoalBodyV0:
        result = k1.DatumRecord(
            ((0, _id_datum(body.question_id, "analysis.question")),)
        )
    elif type(body) is AnalysisHypothesisContextBodyV0:
        result = _analysis_hypothesis_context_body(body)
    elif type(body) is AnalysisPropositionBodyV0:
        result = k1.DatumRecord(
            (
                (0, _id_datum(body.goal_id, "analysis.goal")),
                (
                    1,
                    _id_datum(
                        body.hypothesis_context_id, "analysis.hypothesis-context"
                    ),
                ),
            )
        )
    elif type(body) is AnalysisSemanticBasisBodyV0:
        _admit_semantic_basis_question_and_reads(body)
        result = k1.DatumRecord(
            (
                (0, analysis_profile_declaration_ref_body(body.family)),
                (1, _id_datum(body.exact_question_id, "analysis.question")),
                (2, _analysis_datum(body.rule_source, "Analysis rule source")),
                (3, _analysis_datum(body.exact_premise_schemas, "premise schemas")),
                (4, _read_purpose_requirements_body(body.source_read_purposes)),
                (5, analysis_profile_declaration_ref_body(body.conclusion_schema)),
                (6, _analysis_datum(body.typed_transform_program, "transform program")),
            )
        )
    elif type(body) is AnalysisSupportInstantiationBodyV0:
        result = k1.DatumRecord(
            (
                (0, _id_datum(body.semantic_basis_id, "analysis.semantic-basis")),
                (1, _id_datum(body.proposition_id, "analysis.proposition")),
                (
                    2,
                    _analysis_datum(
                        body.non_hypothesis_premise_bindings, "non-hypothesis bindings"
                    ),
                ),
                (
                    3,
                    _analysis_datum(
                        body.established_hypothesis_node_bindings,
                        "established hypothesis bindings",
                    ),
                ),
                (
                    4,
                    _analysis_datum(
                        body.assumed_hypothesis_node_bindings,
                        "assumed hypothesis bindings",
                    ),
                ),
                (
                    5,
                    _analysis_datum(
                        body.source_support_bindings, "source support bindings"
                    ),
                ),
            )
        )
    elif type(body) is AnalysisValidationBasisBodyV0:
        result = k1.DatumRecord(
            (
                (
                    0,
                    _analysis_datum(
                        body.admitted_checker_contract_ids_and_abis, "checker contracts"
                    ),
                ),
                (
                    1,
                    _analysis_datum(
                        body.exact_translation_contracts, "translation contracts"
                    ),
                ),
                (2, _analysis_datum(body.finite_control_contracts, "finite controls")),
                (
                    3,
                    _analysis_datum(
                        body.theorem_source_validation_ids, "theorem source validations"
                    ),
                ),
                (4, _analysis_datum(body.residual_trust_roots, "residual trust roots")),
            )
        )
    elif type(body) is AnalysisOperationPolicyBodyV0:
        result = k1.DatumRecord(
            tuple(
                (ordinal, _analysis_datum(value, "operation-policy field"))
                for ordinal, value in enumerate(
                    (
                        body.supported_families_and_models,
                        body.named_consumer_and_typed_purpose_permissions,
                        body.capability_freshness_and_lifetime,
                        body.disclosure_policy,
                        body.unknown_question_disposition,
                        body.persistence_policy,
                        body.cold_replay_policy,
                    )
                )
            )
        )
    elif type(body) is AnalysisJudgmentRecordBodyV0:
        result = k1.DatumRecord(
            tuple(
                (ordinal, _analysis_datum(value, "judgment-record field"))
                for ordinal, value in enumerate(
                    (
                        body.proposition_id,
                        body.polarity,
                        body.exact_family_conclusion,
                        body.inherited_hypothesis_context_id,
                        body.typed_quantitative_result,
                        body.semantic_basis_id,
                        body.support_coordinate,
                        body.validation_basis_id,
                        body.qualification,
                        body.operation_policy_id,
                        body.derived_source_policy_dependency_closure,
                    )
                )
            )
        )
    elif type(body) is AnalysisTheoremSchemaBodyV0:
        result = k1.DatumRecord(
            tuple(
                (
                    ordinal,
                    _analysis_datum(
                        value,
                        f"theorem semantic statement field {ordinal}",
                    ),
                )
                for ordinal, value in enumerate(
                    getattr(body, field.name)
                    for field in dataclass_fields(AnalysisTheoremSchemaBodyV0)
                )
            )
        )
    elif type(body) is AnalysisTheoremSourceValidationBodyV0:
        result = k1.DatumRecord(
            (
                (0, _id_datum(body.theorem_schema_id, "analysis.theorem-schema")),
                (1, _analysis_datum(body.source_authority, "theorem source authority")),
                (
                    2,
                    _analysis_datum(
                        body.truth_discharge_metadata, "truth discharge metadata"
                    ),
                ),
            )
        )
    else:  # pragma: no cover - closed by the table above
        raise AnalysisError("unknown exact Analysis body carrier")
    result = _analysis_datum(result, f"{subject_kind} compiled body")
    # A probe handle may authenticate an owner-local nested value while the
    # host constructs a body, but only that value (never the handle) is
    # portable.  This closes accidental `_id_datum` backdoors mechanically.
    if "_LOCAL_COMPONENT_BODY_REGISTRY" in globals():
        _reject_probe_reference_datum(result)
    return result


_ANALYSIS_FORMATION_REGISTRY: dict[bytes, tuple[str, object, object, object]] = {}


def _analysis_profile_rank(profile: object) -> int:
    profiles = (
        ANALYSIS_KERNEL_PROFILE,
        ANALYSIS_PROPERTY_PROFILE,
        ANALYSIS_TRANSPORT_PROFILE,
        ANALYSIS_THEOREM_SOURCE_VALIDATION_PROFILE,
    )
    try:
        return profiles.index(profile)
    except ValueError as error:
        raise AnalysisError("unknown active Analysis profile") from error


def _registered_profiles_in_value(value: object) -> tuple[object, ...]:
    result: dict[object, object] = {}

    def visit(item: object) -> None:
        if type(item) is k1.TypedContentId:
            entry = _ANALYSIS_FORMATION_REGISTRY.get(item.internal_reference())
            if entry is not None:
                result[_active_analysis_profile_id(entry[1])] = entry[1]
            return
        if type(item) is k1.BytesValue:
            entry = _ANALYSIS_FORMATION_REGISTRY.get(item.value)
            if entry is not None:
                result[_active_analysis_profile_id(entry[1])] = entry[1]
            return
        if type(item) is k1.DatumRecord:
            for _, child in item.fields:
                visit(child)
            return
        if type(item) is k1.DatumSeq:
            for child in item.values:
                visit(child)
            return
        if type(item) is k1.DatumVariant:
            visit(item.payload)
            return
        if type(item) is tuple:
            for child in item:
                visit(child)

    visit(value)
    return tuple(result.values())


def _require_constructor_profile(
    subject_kind: str, body: object, profile: object
) -> None:
    """Enforce the finite predecessor-derived profile rules.

    Overlapping supported-kind sets are reuse of one body grammar, not a
    caller choice.  Fixed-family constructors use fixed helpers; the shared
    predecessor-shaped bodies below additionally prove their direct profile
    from authenticated already-formed inputs.
    """

    required: object | None = None
    if type(body) is AnalysisGoalBodyV0:
        required = _formed_analysis_profile(body.question_id, "analysis.question")
    elif type(body) is AnalysisPropositionBodyV0:
        required = _formed_analysis_profile(body.goal_id, "analysis.goal")
        context_profile = _formed_analysis_profile(
            body.hypothesis_context_id, "analysis.hypothesis-context"
        )
        if context_profile != required:
            raise AnalysisError(
                "proposition hypothesis context has a different direct profile"
            )
    elif type(body) is AnalysisFamilyReadManifestSchemaBodyV0:
        _admit_family_manifest_schema_join(body)
        family_profile = _formed_analysis_profile(
            body.family_definition_id, "analysis.asymptotic-protocol-family"
        )
        source_profile = _formed_analysis_profile(
            body.member_source_profile_id, "analysis.source-profile"
        )
        if family_profile != source_profile:
            raise AnalysisError("family manifest predecessors disagree on profile")
        required = family_profile
    elif type(body) is AnalysisPositivePolynomialBodyV0:
        required = _formed_analysis_profile(
            body.profile_id, "analysis.positive-polynomial-profile"
        )
    elif type(body) is AnalysisSourceProfileBodyV0:
        required = _formed_analysis_profile(
            body.adequacy_evaluator_id, "analysis.adequacy-evaluator"
        )
    elif type(body) is AnalysisSupportInstantiationBodyV0:
        predecessor_profiles = (
            _formed_analysis_profile(body.semantic_basis_id, "analysis.semantic-basis"),
            _formed_analysis_profile(body.proposition_id, "analysis.proposition"),
            *_registered_profiles_in_value(
                (
                    body.non_hypothesis_premise_bindings,
                    body.established_hypothesis_node_bindings,
                    body.assumed_hypothesis_node_bindings,
                    body.source_support_bindings,
                )
            ),
        )
        required = max(predecessor_profiles, key=_analysis_profile_rank)
    elif type(body) is AnalysisJudgmentRecordBodyV0:
        predecessor_profiles = (
            _formed_analysis_profile(body.proposition_id, "analysis.proposition"),
            _formed_analysis_profile(body.semantic_basis_id, "analysis.semantic-basis"),
            _formed_analysis_profile(
                body.support_coordinate, "analysis.support-instantiation"
            ),
            _formed_analysis_profile(
                body.validation_basis_id, "analysis.validation-basis"
            ),
            _formed_analysis_profile(
                body.operation_policy_id, "analysis.operation-policy"
            ),
        )
        required = max(predecessor_profiles, key=_analysis_profile_rank)
        if any(
            candidate not in (required,)
            and _analysis_profile_rank(candidate) > _analysis_profile_rank(required)
            for candidate in predecessor_profiles
        ):  # pragma: no cover - defensive after max
            raise AnalysisError("judgment predecessors have incompatible profiles")
    elif type(body) is AnalysisCheckedResultCoordinateBodyV0:
        result_profiles = (
            _formed_analysis_profile(body.proposition_id, "analysis.proposition"),
            _formed_analysis_profile(body.semantic_basis_id, "analysis.semantic-basis"),
            _formed_analysis_profile(body.support_id, "analysis.support-instantiation"),
            _formed_analysis_profile(
                body.validation_basis_id, "analysis.validation-basis"
            ),
        )
        required = max(result_profiles, key=_analysis_profile_rank)
    elif type(body) is AnalysisSourceAuthorityContractBodyV0:
        required = _formed_analysis_profile(
            body.checked_result_coordinate_id, "analysis.checked-result-coordinate"
        )
        if (
            _formed_analysis_profile(
                body.capability_requirement_payload_id,
                "analysis.capability-requirement-payload",
            )
            != required
        ):
            raise AnalysisError("authority requirement does not inherit result profile")
    if required is not None and profile != required:
        raise AnalysisError(
            f"{subject_kind} requires profile {required.profile_family.value!r}"
        )


def _form_analysis_profiled_content_id(
    subject_kind: str,
    body: object,
    profile: object,
) -> object:
    if type(profile) is not k1.SemanticLanguageProfile:
        raise AnalysisError("Analysis identity needs one exact language profile")
    profile_id = _active_analysis_profile_id(profile)
    authenticated_profile = ANALYSIS_PROFILE_BUNDLE.get(profile_id)
    if authenticated_profile != profile or profile not in (
        ANALYSIS_KERNEL_PROFILE,
        ANALYSIS_PROPERTY_PROFILE,
        ANALYSIS_TRANSPORT_PROFILE,
        ANALYSIS_THEOREM_SOURCE_VALIDATION_PROFILE,
    ):
        raise AnalysisError(
            "Analysis formation needs one exact active Analysis profile preimage"
        )
    if subject_kind not in tuple(
        item.value for item in profile.supported_subject_kinds
    ):
        raise AnalysisError(
            f"Analysis profile {profile.profile_family.value!r} does not support "
            f"subject kind {subject_kind!r}"
        )
    _require_constructor_profile(subject_kind, body, profile)
    domain_body = analysis_domain_body_v0(subject_kind, body)
    identifier = k1.profiled_content_id(
        subject_kind,
        profile_id,
        domain_body,
        semantic_regime=k1.SEMANTIC_REGIME_ID,
    )
    profile_bundle = {
        ANALYSIS_KERNEL_PROFILE_ID: ANALYSIS_KERNEL_PROFILE_BUNDLE,
        ANALYSIS_PROPERTY_PROFILE_ID: ANALYSIS_PROPERTY_PROFILE_BUNDLE,
        ANALYSIS_TRANSPORT_PROFILE_ID: ANALYSIS_TRANSPORT_PROFILE_BUNDLE,
        ANALYSIS_THEOREM_SOURCE_VALIDATION_PROFILE_ID: (
            ANALYSIS_THEOREM_SOURCE_VALIDATION_PROFILE_BUNDLE
        ),
    }[profile_id]
    try:
        profile_snapshot = _analysis_profile_bundle_snapshot(profile_bundle)
        context = _authenticated_analysis_profile_context(profile_id, profile_snapshot)
        k1.authenticate_profiled_semantic_content_in_context(
            identifier,
            profile_id,
            domain_body,
            context,
            supported_profiles=(profile_id,),
        )
    except (k1.ModelError, k1.CanonicalError) as error:
        raise AnalysisError(
            "Analysis formation profile closure is not exact and authenticated"
        ) from error
    entry = (subject_kind, profile, body, identifier)
    key = identifier.internal_reference()
    prior = _ANALYSIS_FORMATION_REGISTRY.get(key)
    if prior is not None and prior != entry:
        raise AnalysisError("one Analysis identity resolved to incompatible formation")
    _ANALYSIS_FORMATION_REGISTRY[key] = entry
    return identifier


def analysis_profiled_content_id(
    subject_kind: str,
    body: object,
    profile: object,
) -> object:
    """Reject caller-selected raw formation.

    Concrete constructor cases below derive their exact profile and use the
    private former.  This public pressure-test seam deliberately cannot mint a
    same-shaped body under another merely supporting profile.
    """

    del subject_kind, body, profile
    raise AnalysisError(
        "raw Analysis profile selection is forbidden; use an exact constructor"
    )


def _formed_analysis_profile(identifier: object, subject_kind: str) -> object:
    if type(identifier) is k1.TypedContentId:
        _id_datum(identifier, subject_kind)
        key = identifier.internal_reference()
    elif type(identifier) is k1.BytesValue:
        # Some exact body compilers store an already canonical ContentRefV0
        # datum in their host carrier.  Profile derivation still resolves that
        # reference through the same formation registry; it does not treat the
        # bytes as an ambient or caller-asserted profile coordinate.
        key = identifier.value
    else:
        raise AnalysisError("Analysis predecessor is not one exact content ref")
    entry = _ANALYSIS_FORMATION_REGISTRY.get(key)
    if entry is None or entry[0] != subject_kind:
        raise AnalysisError("Analysis predecessor lacks exact formation evidence")
    return entry[1]


def _formed_analysis_body(identifier: object, subject_kind: str) -> object:
    _formed_analysis_profile(identifier, subject_kind)
    key = (
        identifier.internal_reference()
        if type(identifier) is k1.TypedContentId
        else identifier.value
    )
    return _ANALYSIS_FORMATION_REGISTRY[key][2]


_ANALYSIS_READ_PURPOSE_ORDINAL = {
    AnalysisReadPurpose.SEMANTIC_MEANING: 0,
    AnalysisReadPurpose.PREMISE_SUPPORT: 1,
    AnalysisReadPurpose.OCCURRENCE_EVIDENCE: 2,
}


def _read_purpose_variant(purpose: AnalysisReadPurpose) -> object:
    if type(purpose) is not AnalysisReadPurpose:
        raise AnalysisError("read purpose is not one exact closed case")
    return k1.DatumVariant(_ANALYSIS_READ_PURPOSE_ORDINAL[purpose], k1.UNIT)


def _record_field(record: object, ordinal: int, what: str) -> object:
    if type(record) is not k1.DatumRecord:
        raise AnalysisError(f"{what} is not one exact record")
    fields = dict(record.fields)
    if ordinal not in fields:
        raise AnalysisError(f"{what} lacks required field {ordinal}")
    return fields[ordinal]


def _slot_at(slots: object, ordinal: int, what: str) -> object:
    if type(ordinal) is not int or ordinal < 0:
        raise AnalysisError(f"{what} ordinal is not one natural")
    if type(slots) is not k1.DatumSeq:
        raise AnalysisError(f"{what} catalog is not one exact sequence")
    matches = tuple(
        slot
        for slot in slots.values
        if type(slot) is k1.DatumRecord
        and type(dict(slot.fields).get(0)) is k1.Nat
        and dict(slot.fields)[0].value == ordinal
    )
    if len(matches) != 1:
        raise AnalysisError(f"{what} ordinal does not resolve exactly once")
    return matches[0]


def _slot_schema_and_purpose(
    source_profile_id: object,
    ordinal: int,
    *,
    allow_occurrence_evidence: bool,
) -> tuple[object, AnalysisReadPurpose]:
    profile_body = _formed_analysis_body(
        source_profile_id,
        "analysis.source-profile",
    )
    if type(profile_body) is not AnalysisSourceProfileBodyV0:
        raise AnalysisError("read purpose source profile has a wrong exact body")
    slot_schema = _slot_at(
        profile_body.slot_schemas,
        ordinal,
        "source-profile slot",
    )
    encoded_purpose = _record_field(slot_schema, 3, "source-profile slot")
    if (
        type(encoded_purpose) is not k1.DatumVariant
        or encoded_purpose.payload != k1.UNIT
        or encoded_purpose.case not in tuple(_ANALYSIS_READ_PURPOSE_ORDINAL.values())
    ):
        raise AnalysisError("source-profile slot has no exact read purpose")
    purpose = next(
        item
        for item, tag in _ANALYSIS_READ_PURPOSE_ORDINAL.items()
        if tag == encoded_purpose.case
    )
    if (
        purpose is AnalysisReadPurpose.OCCURRENCE_EVIDENCE
        and not allow_occurrence_evidence
    ):
        raise AnalysisError(
            "family read purpose cannot claim concrete occurrence evidence"
        )
    return slot_schema, purpose


def _source_profile_declaration_labels(
    body: AnalysisSourceProfileBodyV0,
) -> tuple[object, str, str]:
    selected = _formed_analysis_profile(
        body.adequacy_evaluator_id, "analysis.adequacy-evaluator"
    )
    _, family_label, _ = _resolved_profile_declaration(
        selected,
        body.family_tag,
        "analysis.source-family",
    )
    evaluator = _formed_analysis_body(
        body.adequacy_evaluator_id, "analysis.adequacy-evaluator"
    )
    _, input_label, _ = _resolved_profile_declaration(
        selected,
        evaluator.input_schema,
        "analysis.semantic-law",
    )
    return selected, family_label, input_label


def _admit_source_profile_read_purposes(
    body: AnalysisSourceProfileBodyV0,
) -> None:
    """Admit one exact concrete or abstract active source-profile constructor."""

    slot_schemas = body.slot_schemas
    if type(slot_schemas) is not k1.DatumSeq or not slot_schemas.values:
        raise AnalysisError("source profile needs a nonempty exact slot sequence")
    selected_profile, family_label, input_label = _source_profile_declaration_labels(
        body
    )
    evaluator = _formed_analysis_body(
        body.adequacy_evaluator_id, "analysis.adequacy-evaluator"
    )
    _, failure_partition_label, _ = _resolved_profile_declaration(
        selected_profile,
        evaluator.failure_partition,
        "analysis.semantic-law",
    )
    if failure_partition_label != "analysis-attempt-failure-partition-v0":
        raise AnalysisError("source profile uses another adequacy failure partition")
    exact_failure_partition = analysis_profile_declaration_ref_body(
        evaluator.failure_partition
    )
    concrete_cases = {
        "schnorr-relation-special-soundness-source": (
            "schnorr-relation-source-profile-input-v0",
            _FRESH_SOURCE_SLOT_TOKENS,
        ),
        "afk-adaptive-fresh-fs-source": (
            "afk-fresh-fs-source-profile-input-v0",
            _AFK_FRESH_FS_SOURCE_SLOT_TOKENS,
        ),
    }
    abstract_cases = {
        "afk-fresh-family-sources": (
            "afk-family-source-profile-input-v0",
            "fresh-source",
        ),
        "afk-fs-target-family-sources": (
            "afk-family-target-profile-input-v0",
            "adaptive-fs-target",
        ),
    }
    experiment_case = family_label == "bounded-concrete-owner-sources"
    if (
        family_label not in concrete_cases
        and family_label not in abstract_cases
        and not experiment_case
    ):
        raise AnalysisError("source profile names no active constructor")
    ordinals: list[int] = []
    for slot in slot_schemas.values:
        if type(slot) is not k1.DatumRecord:
            raise AnalysisError("source-profile slot is not one exact record")
        ordinal = _record_field(slot, 0, "source-profile slot")
        if type(ordinal) is not k1.Nat:
            raise AnalysisError("source-profile slot ordinal is not one natural")
        encoded_purpose = _record_field(slot, 3, "source-profile slot")
        if (
            type(encoded_purpose) is not k1.DatumVariant
            or encoded_purpose.payload != k1.UNIT
            or encoded_purpose.case
            not in tuple(_ANALYSIS_READ_PURPOSE_ORDINAL.values())
        ):
            raise AnalysisError("source-profile slot has no exact read purpose")
        ordinals.append(ordinal.value)
    if tuple(ordinals) != tuple(range(len(ordinals))):
        raise AnalysisError("source-profile slot ordinals are not contiguous")

    if experiment_case:
        expected_names = (
            "strategy-class",
            "setup-and-input-sampling",
            "generated-execution-relation",
        )
        if input_label != "source-profile-input-v0" or len(slot_schemas.values) != 3:
            raise AnalysisError("experiment source profile has the wrong active shape")
        for ordinal, (slot, expected_name) in enumerate(
            zip(slot_schemas.values, expected_names, strict=True)
        ):
            fields = dict(slot.fields)
            if (
                tuple(fields) != (0, 1, 2, 3)
                or fields[0] != k1.Nat(ordinal)
                or fields[1] != k1.Symbol(expected_name)
                or fields[3]
                != _read_purpose_variant(AnalysisReadPurpose.SEMANTIC_MEANING)
            ):
                raise AnalysisError("experiment source-profile slot was substituted")
        strategy_slot, setup_slot, execution_slot = (
            dict(slot.fields) for slot in slot_schemas.values
        )
        strategy_ref = strategy_slot[2]
        _formed_analysis_body(strategy_ref, "analysis.strategy-class")
        active_strategy_kinds = {
            _id_datum(
                SPECIAL_SOUNDNESS_PAIR_INTERFACE,
                "analysis.strategy-class",
            ): "fresh-special-soundness-pair",
            _id_datum(
                ADAPTIVE_KNOWLEDGE_INTERFACE,
                "analysis.strategy-class",
            ): "adaptive-afk-pair",
        }
        expected_bundle_kind = active_strategy_kinds.get(strategy_ref)
        if expected_bundle_kind is None:
            raise AnalysisError(
                "experiment source profile uses no active strategy constructor"
            )
        expected_setup = _embedded_component_datum(
            SCHNORR_SETUP_PROFILE,
            "analysis.setup-profile",
        )
        if setup_slot[2] != expected_setup:
            raise AnalysisError(
                "experiment source profile uses another setup constructor"
            )
        bundle = execution_slot[2]
        if (
            type(bundle) is not k1.DatumVariant
            or bundle.case != 1
            or type(bundle.payload) is not k1.DatumRecord
            or tuple(dict(bundle.payload.fields)) != tuple(range(15))
        ):
            raise AnalysisError(
                "experiment source profile has no exact inline execution bundle"
            )
        bundle_fields = dict(bundle.payload.fields)
        if (
            bundle_fields[0] != k1.Symbol(expected_bundle_kind)
            or bundle_fields[2] != strategy_ref
        ):
            raise AnalysisError(
                "experiment source profile execution bundle is detached from its strategy"
            )
        expected_closed = k1.DatumSeq(
            tuple(
                k1.DatumRecord(((0, k1.Nat(index)), (1, k1.Nat(2))))
                for index in range(3)
            )
        )
        if body.closed_field_read_set != expected_closed:
            raise AnalysisError(
                "experiment source-profile closed fields were substituted"
            )
        return

    if family_label in concrete_cases:
        expected_input, expected_tokens = concrete_cases[family_label]
        if input_label != expected_input or len(slot_schemas.values) != len(
            expected_tokens
        ):
            raise AnalysisError("concrete source profile has the wrong active shape")
        expected_closed = []
        for ordinal, (slot, (kind, axis)) in enumerate(
            zip(slot_schemas.values, expected_tokens, strict=True)
        ):
            fields = dict(slot.fields)
            expected_axis = {"shared": 0, "fresh": 1, "fiat-shamir": 2}[axis]
            if (
                tuple(fields) != tuple(range(7))
                or fields[0] != k1.Nat(ordinal)
                or fields[1] != k1.Nat(_SOURCE_FACT_KIND_ORDINAL[kind])
                or fields[2] != k1.DatumVariant(expected_axis, k1.UNIT)
                or fields[3]
                != _read_purpose_variant(AnalysisReadPurpose.SEMANTIC_MEANING)
                or fields[4] != k1.DatumVariant(0, k1.UNIT)
                or fields[5] != k1.DatumVariant(0, k1.UNIT)
                or fields[6] != exact_failure_partition
            ):
                raise AnalysisError(
                    "concrete source-profile slot shape was substituted"
                )
            expected_closed.append(k1.DatumRecord(((0, fields[1]), (1, fields[2]))))
        if body.closed_field_read_set != k1.DatumSeq(tuple(expected_closed)):
            raise AnalysisError(
                "concrete source-profile closed fields were substituted"
            )
        return

    expected_input, expected_axis = abstract_cases[family_label]
    if (
        input_label != expected_input
        or len(slot_schemas.values) != 2
        or type(body.closed_field_read_set) is not k1.DatumSeq
    ):
        raise AnalysisError("abstract family source profile has the wrong active shape")
    first, second = slot_schemas.values
    first_fields = dict(first.fields)
    second_fields = dict(second.fields)
    if (
        tuple(first_fields) != (0, 1, 2, 3)
        or tuple(second_fields) != (0, 1, 2, 3)
        or first_fields[0] != k1.Nat(0)
        or first_fields[1] != k1.Symbol(expected_axis)
        or second_fields[0] != k1.Nat(1)
        or second_fields[1] != k1.Symbol("family-ro-index-domain")
        or first_fields[3]
        != _read_purpose_variant(AnalysisReadPurpose.SEMANTIC_MEANING)
        or second_fields[3]
        != _read_purpose_variant(AnalysisReadPurpose.SEMANTIC_MEANING)
    ):
        raise AnalysisError(
            "abstract family source-profile slot or read purpose was substituted"
        )
    family = _formed_analysis_body(
        first_fields[2], "analysis.asymptotic-protocol-family"
    )
    family_payload = family.canonical_family_payload
    if (
        type(family_payload) is not k1.DatumRecord
        or _record_field(family_payload, 8, "asymptotic family payload")
        != second_fields[2]
    ):
        raise AnalysisError("abstract source profile is detached from its family")
    expected_closed = k1.DatumSeq(
        (
            k1.DatumRecord(((0, k1.Nat(0)), (1, k1.Nat(2)))),
            k1.DatumRecord(((0, k1.Nat(1)), (1, k1.Nat(2)))),
        )
    )
    if body.closed_field_read_set != expected_closed:
        raise AnalysisError("abstract source-profile closed fields were substituted")


def _admit_concrete_semantic_read_manifest(
    body: AnalysisSemanticReadManifestBodyV0,
) -> None:
    if type(body.exact_subjects) is not tuple or not body.exact_subjects:
        raise AnalysisError("semantic read manifest needs nonempty subjects")
    profile = _formed_analysis_body(body.source_profile_id, "analysis.source-profile")
    _, family_label, _ = _source_profile_declaration_labels(profile)
    if family_label not in (
        "schnorr-relation-special-soundness-source",
        "afk-adaptive-fresh-fs-source",
    ):
        raise AnalysisError("concrete manifest cannot use an abstract source profile")
    if type(body.slots) is not k1.DatumSeq or len(body.slots.values) != len(
        profile.slot_schemas.values
    ):
        raise AnalysisError("concrete manifest/profile join is not total")
    owners: list[object] = []
    seen: set[bytes] = set()
    owner_kind = {
        SourceFactKind.CORE: "pir.interactive-core",
        SourceFactKind.PROTOCOL: "pir.protocol",
        SourceFactKind.CONSTRUCTION: "pir.transcript-construction",
        SourceFactKind.RELATION_BINDING: "relations.protocol-binding",
        SourceFactKind.PLAN_WITNESS_BINDING: "relations.plan-witness-binding",
        SourceFactKind.STATEMENT_EDGE: "relations.protocol-binding",
        SourceFactKind.CLAIM_EDGE: "relations.protocol-binding",
        SourceFactKind.WITNESS_EDGE: "relations.plan-witness-binding",
    }
    by_fact_ordinal = {
        ordinal: owner_kind[kind]
        for kind, ordinal in _SOURCE_FACT_KIND_ORDINAL.items()
        if kind in owner_kind
    }
    for ordinal, (slot, schema) in enumerate(
        zip(body.slots.values, profile.slot_schemas.values, strict=True)
    ):
        if type(slot) is not k1.DatumRecord or tuple(dict(slot.fields)) != (0, 1, 2):
            raise AnalysisError("concrete manifest slot has the wrong closed shape")
        fields = dict(slot.fields)
        schema_fields = dict(schema.fields)
        owner = fields[1]
        fact_ordinal = schema_fields[1]
        if (
            fields[0] != k1.Nat(ordinal)
            or fields[2] != schema_fields[2]
            or type(owner) is not k1.BytesValue
            or type(fact_ordinal) is not k1.Nat
        ):
            raise AnalysisError("concrete manifest/profile slot join was substituted")
        owner_body = _ANALYSIS_FORMATION_REGISTRY.get(owner.value)
        expected_kind = by_fact_ordinal.get(fact_ordinal.value)
        if owner_body is not None:
            actual_kind = owner_body[0]
        else:
            actual_kind = next(
                (
                    subject.subject_kind
                    for subject in body.exact_subjects
                    if subject.internal_reference() == owner.value
                ),
                None,
            )
        if actual_kind != expected_kind:
            raise AnalysisError("concrete manifest owner has the wrong slot kind")
        if owner.value not in seen:
            seen.add(owner.value)
            owners.append(owner)
    if tuple(_id_datum(item) for item in body.exact_subjects) != tuple(owners):
        raise AnalysisError(
            "concrete manifest exact-subject owner coverage is not exact"
        )


def _admit_family_manifest_schema_join(
    body: AnalysisFamilyReadManifestSchemaBodyV0,
) -> None:
    profile = _formed_analysis_body(
        body.member_source_profile_id, "analysis.source-profile"
    )
    _, family_label, _ = _source_profile_declaration_labels(profile)
    if family_label not in (
        "afk-fresh-family-sources",
        "afk-fs-target-family-sources",
    ):
        raise AnalysisError("family manifest schema needs an abstract source tag")
    first = _slot_at(profile.slot_schemas, 0, "family source-profile slot")
    if _record_field(first, 2, "family source-profile slot") != _id_datum(
        body.family_definition_id, "analysis.asymptotic-protocol-family"
    ):
        raise AnalysisError("family manifest schema is detached from its source family")


def concrete_manifest_read_purposes(
    manifest_id: object,
) -> tuple[ConcreteReadPurpose, ...]:
    """Derive every concrete requirement from one authenticated manifest/profile join."""

    manifest = _formed_analysis_body(
        manifest_id,
        "analysis.semantic-read-manifest",
    )
    if type(manifest) is not AnalysisSemanticReadManifestBodyV0:
        raise AnalysisError("concrete read source has the wrong manifest body")
    profile = _formed_analysis_body(
        manifest.source_profile_id,
        "analysis.source-profile",
    )
    if type(profile) is not AnalysisSourceProfileBodyV0:
        raise AnalysisError("concrete read source has the wrong profile body")
    if type(manifest.slots) is not k1.DatumSeq:
        raise AnalysisError("concrete read manifest has no exact slot sequence")
    if len(manifest.slots.values) != len(profile.slot_schemas.values):
        raise AnalysisError("concrete manifest/profile join is not total")
    result: list[ConcreteReadPurpose] = []
    for ordinal in range(len(profile.slot_schemas.values)):
        _slot_at(manifest.slots, ordinal, "semantic-read manifest slot")
        _, purpose = _slot_schema_and_purpose(
            manifest.source_profile_id,
            ordinal,
            allow_occurrence_evidence=True,
        )
        result.append(ConcreteReadPurpose(manifest_id, ordinal, purpose))
    return tuple(result)


def family_manifest_read_purposes(
    manifest_schema_id: object,
) -> tuple[FamilyReadPurpose, ...]:
    """Derive every abstract-family requirement from its authenticated profile."""

    schema = _formed_analysis_body(
        manifest_schema_id,
        "analysis.family-read-manifest-schema",
    )
    if type(schema) is not AnalysisFamilyReadManifestSchemaBodyV0:
        raise AnalysisError("family read source has the wrong manifest schema")
    profile = _formed_analysis_body(
        schema.member_source_profile_id,
        "analysis.source-profile",
    )
    if type(profile) is not AnalysisSourceProfileBodyV0:
        raise AnalysisError("family read source has the wrong profile body")
    result: list[FamilyReadPurpose] = []
    for ordinal in range(len(profile.slot_schemas.values)):
        _, purpose = _slot_schema_and_purpose(
            schema.member_source_profile_id,
            ordinal,
            allow_occurrence_evidence=False,
        )
        result.append(FamilyReadPurpose(manifest_schema_id, ordinal, purpose))
    return tuple(result)


def complete_read_purpose_requirements(
    *,
    concrete_manifest_ids: Iterable[object] = (),
    family_manifest_schema_ids: Iterable[object] = (),
) -> tuple[AnalysisReadPurposeRequirement, ...]:
    """Derive the complete canonical purpose set for exact rule source coordinates."""

    requirements = (
        *(
            requirement
            for manifest_id in concrete_manifest_ids
            for requirement in concrete_manifest_read_purposes(manifest_id)
        ),
        *(
            requirement
            for schema_id in family_manifest_schema_ids
            for requirement in family_manifest_read_purposes(schema_id)
        ),
    )
    return canonical_read_purpose_requirements(requirements)


def require_complete_read_purpose_requirements(
    requirements: tuple[AnalysisReadPurposeRequirement, ...],
    *,
    concrete_manifest_ids: Iterable[object] = (),
    family_manifest_schema_ids: Iterable[object] = (),
) -> None:
    expected = complete_read_purpose_requirements(
        concrete_manifest_ids=concrete_manifest_ids,
        family_manifest_schema_ids=family_manifest_schema_ids,
    )
    if requirements != expected:
        raise AnalysisError(
            "read purpose requirements omit, duplicate, reorder, or add a source slot"
        )


def _formed_analysis_id(identifier: object, subject_kind: str) -> object:
    """Recover one typed identifier only from an authenticated formation."""

    if type(identifier) is k1.TypedContentId:
        _id_datum(identifier, subject_kind)
        return identifier
    if type(identifier) is k1.BytesValue:
        entry = _ANALYSIS_FORMATION_REGISTRY.get(identifier.value)
        if entry is not None and entry[0] == subject_kind:
            return entry[3]
    raise AnalysisError("Analysis reference lacks one exact typed formation")


def _semantic_basis_read_sources(
    question_id: object,
) -> tuple[tuple[object, ...], tuple[object, ...]]:
    """Derive the complete read-source coordinates from one exact question.

    The active question algebra has four closed context cases.  The fourth is
    family-specific: correspondence questions carry both abstract and
    concrete manifests directly, while fixed-member specialization carries
    the selected concrete manifest inside its authenticated native projection.
    """

    question = _formed_analysis_body(question_id, "analysis.question")
    profile = _formed_analysis_profile(question_id, "analysis.question")
    _, family_label, _ = _resolved_profile_declaration(
        profile,
        question.family,
        "analysis.property-family",
    )
    context = question.context
    if type(context) is not k1.DatumVariant:
        raise AnalysisError("semantic-basis question has no closed context case")
    if context.case == 0:
        _record = context.payload
        # Source-free questions carry exactly one admitted reason reference.
        if type(_record) is not k1.DatumVariant and type(_record) is not k1.DatumRecord:
            # The current source-free carrier is a declaration-ref datum and
            # may be either local or imported.  Encoding it is the exact shape
            # check; it contributes no read source.
            _analysis_datum(_record, "source-free question reason")
        return (), ()
    if type(context.payload) is not k1.DatumRecord:
        raise AnalysisError("semantic-basis question context is not one record")
    fields = dict(context.payload.fields)
    if context.case == 1:
        if tuple(fields) != (0, 1) or type(fields[0]) is not k1.DatumSeq:
            raise AnalysisError("concrete semantic question context is incomplete")
        return tuple(
            _formed_analysis_id(item, "analysis.semantic-read-manifest")
            for item in fields[0].values
        ), ()
    if context.case == 2:
        if tuple(fields) != (0, 1, 2) or type(fields[1]) is not k1.DatumSeq:
            raise AnalysisError("family semantic question context is incomplete")
        return (), tuple(
            _formed_analysis_id(item, "analysis.family-read-manifest-schema")
            for item in fields[1].values
        )
    if context.case != 3:
        raise AnalysisError("semantic-basis question uses an unknown context case")
    if family_label == "family-instance-correspondence":
        if (
            tuple(fields) != (0, 1)
            or type(fields[0]) is not k1.DatumSeq
            or type(fields[1]) is not k1.DatumSeq
        ):
            raise AnalysisError("correspondence question read context is incomplete")
        return (
            tuple(
                _formed_analysis_id(item, "analysis.semantic-read-manifest")
                for item in fields[1].values
            ),
            tuple(
                _formed_analysis_id(item, "analysis.family-read-manifest-schema")
                for item in fields[0].values
            ),
        )
    if family_label == "adaptive-knowledge-extraction-at-fixed-length-q-lt-n":
        if tuple(fields) != (0, 1, 2, 3, 4):
            raise AnalysisError("fixed-member question context is incomplete")
        projection = fields[2]
        pair_manifest = _record_field(
            projection,
            6,
            "fixed-member native-subject projection",
        )
        return (
            _formed_analysis_id(pair_manifest, "analysis.semantic-read-manifest"),
        ), ()
    raise AnalysisError("semantic-basis context case is not valid for its family")


def _admit_semantic_basis_question_and_reads(
    body: AnalysisSemanticBasisBodyV0,
) -> None:
    """Bind a basis to one authenticated question and its complete read set."""

    question = _formed_analysis_body(body.exact_question_id, "analysis.question")
    question_profile = _formed_analysis_profile(
        body.exact_question_id, "analysis.question"
    )
    _, _, question_family_body = _resolved_profile_declaration(
        question_profile,
        question.family,
        "analysis.property-family",
    )
    basis_profile = _formed_analysis_profile(
        body.exact_question_id, "analysis.question"
    )
    _, _, basis_family_body = _resolved_profile_declaration(
        basis_profile,
        body.family,
        "analysis.property-family",
    )
    if basis_family_body != question_family_body:
        raise AnalysisError("semantic basis names a different exact question family")
    concrete, family = _semantic_basis_read_sources(body.exact_question_id)
    require_complete_read_purpose_requirements(
        body.source_read_purposes,
        concrete_manifest_ids=concrete,
        family_manifest_schema_ids=family,
    )


def _read_purpose_requirement_body(
    requirement: AnalysisReadPurposeRequirement,
) -> object:
    if type(requirement) is ConcreteReadPurpose:
        return k1.DatumVariant(
            0,
            k1.DatumRecord(
                (
                    (
                        0,
                        _id_datum(
                            requirement.semantic_read_manifest_id,
                            "analysis.semantic-read-manifest",
                        ),
                    ),
                    (1, k1.Nat(requirement.semantic_read_slot_ordinal)),
                    (2, _read_purpose_variant(requirement.exact_purpose)),
                )
            ),
        )
    if type(requirement) is FamilyReadPurpose:
        return k1.DatumVariant(
            1,
            k1.DatumRecord(
                (
                    (
                        0,
                        _id_datum(
                            requirement.family_read_manifest_schema_id,
                            "analysis.family-read-manifest-schema",
                        ),
                    ),
                    (1, k1.Nat(requirement.family_read_slot_ordinal)),
                    (2, _read_purpose_variant(requirement.exact_purpose)),
                )
            ),
        )
    raise AnalysisError("read purpose requirement has a foreign variant")


def normalize_read_purpose_requirements(
    requirements: Iterable[AnalysisReadPurposeRequirement],
) -> tuple[NormalizedAnalysisReadPurpose, ...]:
    if type(requirements) not in (tuple, list):
        requirements = tuple(requirements)
    normalized: list[NormalizedAnalysisReadPurpose] = []
    for requirement in requirements:
        if type(requirement) is ConcreteReadPurpose:
            manifest_body = _formed_analysis_body(
                requirement.semantic_read_manifest_id,
                "analysis.semantic-read-manifest",
            )
            if type(manifest_body) is not AnalysisSemanticReadManifestBodyV0:
                raise AnalysisError("concrete read purpose has a wrong manifest body")
            manifest_slot = _slot_at(
                manifest_body.slots,
                requirement.semantic_read_slot_ordinal,
                "semantic-read manifest slot",
            )
            profile_slot, declared_purpose = _slot_schema_and_purpose(
                manifest_body.source_profile_id,
                requirement.semantic_read_slot_ordinal,
                allow_occurrence_evidence=True,
            )
            exact_slot = k1.DatumRecord(((0, manifest_slot), (1, profile_slot)))
        elif type(requirement) is FamilyReadPurpose:
            schema_body = _formed_analysis_body(
                requirement.family_read_manifest_schema_id,
                "analysis.family-read-manifest-schema",
            )
            if type(schema_body) is not AnalysisFamilyReadManifestSchemaBodyV0:
                raise AnalysisError("family read purpose has a wrong manifest schema")
            exact_slot, declared_purpose = _slot_schema_and_purpose(
                schema_body.member_source_profile_id,
                requirement.family_read_slot_ordinal,
                allow_occurrence_evidence=False,
            )
        else:
            raise AnalysisError("read purpose requirement has a foreign variant")
        if requirement.exact_purpose is not declared_purpose:
            raise AnalysisError(
                "read purpose requirement disagrees with its authenticated slot"
            )
        normalized.append(NormalizedAnalysisReadPurpose(requirement, exact_slot))

    def normalized_key(item: NormalizedAnalysisReadPurpose) -> bytes:
        return k1.encode_datum(_read_purpose_requirement_body(item.requirement))

    ordered = tuple(sorted(normalized, key=normalized_key))
    keys = tuple(normalized_key(item) for item in ordered)
    if len(keys) != len(set(keys)):
        raise AnalysisError("read purpose requirements contain a duplicate atom")
    return ordered


def canonical_read_purpose_requirements(
    requirements: Iterable[AnalysisReadPurposeRequirement],
) -> tuple[AnalysisReadPurposeRequirement, ...]:
    return tuple(
        item.requirement for item in normalize_read_purpose_requirements(requirements)
    )


def _read_purpose_requirements_body(
    requirements: tuple[AnalysisReadPurposeRequirement, ...],
) -> object:
    if type(requirements) is not tuple:
        raise AnalysisError("read purpose requirements must use one immutable tuple")
    canonical = canonical_read_purpose_requirements(requirements)
    if requirements != canonical:
        raise AnalysisError(
            "read purpose requirements are not canonical sorted and unique"
        )
    return k1.DatumSeq(
        tuple(_read_purpose_requirement_body(item) for item in requirements)
    )


def _analysis_id(subject_kind: str, body: object) -> object:
    return _form_analysis_profiled_content_id(
        subject_kind,
        body,
        ANALYSIS_PROPERTY_PROFILE,
    )


def _analysis_kernel_id(subject_kind: str, body: object) -> object:
    return _form_analysis_profiled_content_id(
        subject_kind,
        body,
        ANALYSIS_KERNEL_PROFILE,
    )


def _analysis_transport_id(subject_kind: str, body: object) -> object:
    return _form_analysis_profiled_content_id(
        subject_kind,
        body,
        ANALYSIS_TRANSPORT_PROFILE,
    )


def _analysis_theorem_source_validation_id(subject_kind: str, body: object) -> object:
    return _form_analysis_profiled_content_id(
        subject_kind,
        body,
        ANALYSIS_THEOREM_SOURCE_VALIDATION_PROFILE,
    )


def fixture_ref(subject_kind: str, label: str) -> object:
    """Create an inert Foundation identity for a fixture meaning, never authority."""

    return k1.content_id(
        subject_kind,
        k1.encode_datum(
            k1.DatumRecord(((0, k1.Symbol(_ascii(label, "fixture label"))),))
        ),
        semantic_regime=k1.SEMANTIC_REGIME_ID,
    )


_LOCAL_COMPONENT_BODY_REGISTRY: dict[bytes, tuple[str, object]] = {}


def _local_component_id(component_kind: str, body: object) -> object:
    """Create a content-addressed local handle for a nested owner-body value.

    Such handles are never serialized by an AnalysisBodyV0 arm.  The enclosing
    durable body retrieves and embeds the authenticated canonical body itself;
    consequently this cache contributes no ambient semantic authority.
    """

    _ascii(component_kind, "local component kind")
    body = _analysis_datum(body, f"local {component_kind} body")
    identifier = k1.content_id(
        f"probe.analysis.{component_kind}",
        k1.encode_datum(body),
        semantic_regime=k1.SEMANTIC_REGIME_ID,
    )
    key = identifier.internal_reference()
    prior = _LOCAL_COMPONENT_BODY_REGISTRY.get(key)
    entry = (component_kind, body)
    if prior is not None and prior != entry:
        raise AnalysisError("local component handle was rebound")
    _LOCAL_COMPONENT_BODY_REGISTRY[key] = entry
    return identifier


def _local_component_body(identifier: object, component_kind: str) -> object:
    _id_datum(identifier, f"probe.analysis.{component_kind}")
    entry = _LOCAL_COMPONENT_BODY_REGISTRY.get(identifier.internal_reference())
    if entry is None or entry[0] != component_kind:
        raise AnalysisError("local component body is absent or has the wrong kind")
    expected = _local_component_id(component_kind, entry[1])
    if expected != identifier:
        raise AnalysisError("local component handle does not authenticate its body")
    return entry[1]


def _expand_probe_references(value: object) -> object:
    """Recursively replace every local handle with its authenticated body."""

    if type(value) is k1.BytesValue:
        entry = _LOCAL_COMPONENT_BODY_REGISTRY.get(value.value)
        if entry is None:
            return value
        return k1.DatumVariant(1, _expand_probe_references(entry[1]))
    if type(value) is k1.DatumRecord:
        return k1.DatumRecord(
            tuple(
                (ordinal, _expand_probe_references(item))
                for ordinal, item in value.fields
            )
        )
    if type(value) is k1.DatumSeq:
        return k1.DatumSeq(
            tuple(_expand_probe_references(item) for item in value.values)
        )
    if type(value) is k1.DatumVariant:
        return k1.DatumVariant(value.case, _expand_probe_references(value.payload))
    return value


def _reject_probe_reference_datum(value: object) -> None:
    """Reject process-local component handles from portable Analysis bodies."""

    if type(value) is k1.BytesValue:
        entry = _LOCAL_COMPONENT_BODY_REGISTRY.get(value.value)
        if entry is not None:
            raise AnalysisError(
                "process-local Analysis component handle "
                f"{entry[0]!r} cannot enter an AnalysisBodyV0 field"
            )
        return
    if type(value) is k1.DatumRecord:
        for _, item in value.fields:
            _reject_probe_reference_datum(item)
        return
    if type(value) is k1.DatumSeq:
        for item in value.values:
            _reject_probe_reference_datum(item)
        return
    if type(value) is k1.DatumVariant:
        _reject_probe_reference_datum(value.payload)


def _legacy_component_id(subject_kind: str, body: object) -> object:
    """Temporary API adapter for a nested value with no durable subject kind."""

    if not subject_kind.startswith("analysis."):
        raise AnalysisError("legacy component adapter needs an Analysis spelling")
    component_kind = subject_kind.removeprefix("analysis.")
    if subject_kind not in _LOCAL_COMPONENT_KIND_ALIASES:
        raise AnalysisError("legacy component is not in the finite compression table")
    return _local_component_id(component_kind, body)


class AttemptKind(str, Enum):
    AFFIRMATIVE = "affirmative"
    NEGATIVE = "negative"
    UNSUPPORTED = "unsupported"
    MISSING_DEPENDENCY = "missing-dependency"
    CANNOT_ANSWER = "cannot-answer"
    KIND_MISMATCH = "kind-mismatch"
    MALFORMED = "malformed"
    REFUSED = "refused"
    DETERMINISTIC_LIMIT_EXCEEDED = "deterministic-limit-exceeded"
    CHECKER_FAILURE = "checker-failure"


@dataclass(frozen=True)
class AttemptOutcome:
    kind: AttemptKind
    value: object | None = None
    detail: str = ""


def _affirmative(value: object) -> AttemptOutcome:
    return AttemptOutcome(AttemptKind.AFFIRMATIVE, value)


@dataclass(frozen=True)
class InertCheckedResult:
    """Portable coordinates of one completed result, never live authority."""

    result_id: object
    proposition_id: object
    semantic_basis_id: object
    support_id: object
    validation_basis_id: object
    qualification_id: object
    outcome_kind: AttemptKind
    semantic_profile: object


@dataclass(frozen=True)
class AnalysisCapabilityRequirementPayload:
    """Analysis-owned requirement payload embedded through Foundation's envelope."""

    proposition_id: object
    qualification_id: object
    named_consumer: object
    typed_purpose: object
    semantic_profile: object


@dataclass(frozen=True)
class AnalysisSourceAuthorityContract:
    """Analysis contract data; Foundation owns its portable envelope representation."""

    owner_id: object
    checked_result_coordinate_id: object
    capability_requirement: AnalysisCapabilityRequirementPayload
    immediate_policy_ids: tuple[object, ...]
    transitive_policy_ids: tuple[object, ...]
    semantic_profile: object


@dataclass(frozen=True)
class InvocationCapability:
    """Process-local authority used only as an invocation argument."""

    authority_binding_id: object
    source_binding: object
    capability_family: object
    named_consumer_id: object
    typed_purpose_id: object
    _token: object


_Analysis_REFERENCE_CHECKER_ALGORITHM = k1.build_mod_algorithm()
_Analysis_REFERENCE_CHECKER_ALGORITHM_ID = k1.authenticate_algorithm_identity(
    _Analysis_REFERENCE_CHECKER_ALGORITHM
)
_Analysis_REFERENCE_CHECKER_EVALUATION_CONTRACT_ID = (
    k1.DEFAULT_EVALUATION_CONTRACT.identity
)


def analysis_validation_basis_id(
    theorem_source_validation_ids: Iterable[object],
    *,
    profile: object,
) -> object:
    """Form the exact-used validation basis independently of semantic basis."""

    validations = _canonical_identifier_set(
        theorem_source_validation_ids,
        what="theorem-source validation set",
    )
    for identifier in validations:
        _id_datum(identifier, "analysis.theorem-source-validation")
    if profile not in (
        ANALYSIS_PROPERTY_PROFILE,
        ANALYSIS_TRANSPORT_PROFILE,
        ANALYSIS_THEOREM_SOURCE_VALIDATION_PROFILE,
    ):
        raise AuthorityError("validation basis selects an unsupported profile")
    checker_input = analysis_profile_declaration_ref(
        profile,
        ANALYSIS_KERNEL_PROFILE,
        "analysis.semantic-law",
        "checker-input-v0",
    )
    checker_output = analysis_profile_declaration_ref(
        profile,
        ANALYSIS_KERNEL_PROFILE,
        "analysis.semantic-law",
        "checker-output-v0",
    )
    residual_trust = analysis_profile_declaration_ref(
        profile,
        ANALYSIS_KERNEL_PROFILE,
        "analysis.residual-trust-root",
        "python-runtime-and-reference-model",
    )
    direct_roots = k1.direct_module_dependencies(_Analysis_REFERENCE_CHECKER_ALGORITHM)
    checker_contract = k1.DatumRecord(
        (
            (
                0,
                _id_datum(
                    _Analysis_REFERENCE_CHECKER_ALGORITHM_ID,
                    "foundation.portable-algorithm",
                ),
            ),
            (
                1,
                _id_datum(
                    _Analysis_REFERENCE_CHECKER_EVALUATION_CONTRACT_ID,
                    "foundation.evaluation-contract",
                ),
            ),
            (2, analysis_profile_declaration_ref_body(checker_input)),
            (3, analysis_profile_declaration_ref_body(checker_output)),
            (4, k1.DatumSeq(tuple(_id_datum(item) for item in direct_roots))),
        )
    )
    return _form_analysis_profiled_content_id(
        "analysis.validation-basis",
        AnalysisValidationBasisBodyV0(
            k1.DatumSeq((checker_contract,)),
            k1.DatumSeq(()),
            k1.DatumSeq(()),
            k1.DatumSeq(tuple(_id_datum(item) for item in validations)),
            k1.DatumSeq((analysis_profile_declaration_ref_body(residual_trust),)),
        ),
        profile,
    )


def _canonical_identifier_set(
    identifiers: Iterable[object], *, what: str
) -> tuple[object, ...]:
    values = tuple(identifiers)
    if len(values) > MAX_HYPOTHESES:
        raise AuthorityError(f"{what} exceeds its finite bound")
    for identifier in values:
        _id_datum(identifier)
    ordered = tuple(sorted(values, key=lambda item: item.internal_reference()))
    if len(ordered) != len(set(ordered)):
        raise AuthorityError(f"{what} must be duplicate-free")
    return ordered


@dataclass(frozen=True)
class QualificationSubjectContext:
    """Candidate-derived input to one finite qualification law."""

    semantic_profile: object
    proposition_id: object
    goal_id: object
    question_id: object
    family_label: str
    exact_subjects: tuple[object, ...]
    question_context: object
    question_payload: object
    inherited_hypothesis_context_id: object
    semantic_basis_id: object
    semantic_basis: AnalysisSemanticBasisBodyV0
    support_id: object
    support: AnalysisSupportInstantiationBodyV0
    validation_basis_id: object
    validation_basis: AnalysisValidationBasisBodyV0
    judgment_record: AnalysisJudgmentRecordBodyV0 | None
    result_id: object | None
    outcome_kind: AttemptKind | None


@dataclass(frozen=True)
class _QualificationLawSpec:
    qualification_label: str
    exact_family_label: str
    exact_subject_kinds: tuple[str, ...]
    exact_context_case: int
    native_rule_label: str | None
    conclusion_schema_label: str
    assumed_binding_mode: str
    exact_non_hypothesis_binding_count: int
    exact_source_support_binding_count: int
    requires_judgment_record: bool


_QUALIFICATION_LAW_SPECS = (
    _QualificationLawSpec(
        "finite-special-soundness-result",
        "k-out-of-n-special-soundness",
        ("pir.protocol", "relations.protocol-binding"),
        1,
        "existential-extractor-introduction",
        "k-out-of-n-conclusion-v0",
        "hypothesis-context",
        0,
        0,
        True,
    ),
    _QualificationLawSpec(
        "finite-cover-certificate-result",
        "fixed-extractor-universal-correctness",
        (
            "pir.protocol",
            "relations.definition",
            "relations.protocol-binding",
            "analysis.challenge-domain",
            "foundation.portable-algorithm",
        ),
        1,
        "checked-finite-cover-certificate",
        "finite-cover-certificate-conclusion-v0",
        "hypothesis-context",
        0,
        0,
        True,
    ),
    _QualificationLawSpec(
        "finite-fixed-extractor-universal-result",
        "fixed-extractor-universal-correctness",
        (
            "pir.protocol",
            "relations.definition",
            "relations.protocol-binding",
            "analysis.challenge-domain",
            "foundation.portable-algorithm",
        ),
        1,
        "checked-finite-cover-universal-discharge",
        "fixed-extractor-universal-conclusion-v0",
        "hypothesis-context",
        3,
        0,
        True,
    ),
    _QualificationLawSpec(
        "conditional-assumed-external-all-n",
        "asymptotic-k-out-of-n-special-soundness",
        ("analysis.asymptotic-protocol-family",),
        2,
        "conditional-family-instance-correspondence",
        "k-out-of-n-conclusion-v0",
        "hypothesis-context",
        0,
        1,
        False,
    ),
    _QualificationLawSpec(
        "conditional-assumed-theorem-truth",
        "theorem-truth",
        ("analysis.theorem-schema",),
        0,
        None,
        "theorem-truth-conclusion-v0",
        "self-theorem-assumption",
        0,
        0,
        False,
    ),
    _QualificationLawSpec(
        "afk-family-applicability-result",
        "theorem-applicability",
        ("analysis.theorem-schema", "analysis.asymptotic-protocol-family"),
        2,
        "exact-theorem-applicability-check",
        "family-applicability-conclusion-v0",
        "hypothesis-context",
        0,
        0,
        True,
    ),
    _QualificationLawSpec(
        "afk-family-transport-result",
        "adaptive-knowledge-soundness-q-lt-n",
        ("analysis.asymptotic-protocol-family",),
        2,
        None,
        "adaptive-knowledge-conclusion-v0",
        "hypothesis-context",
        3,
        3,
        True,
    ),
    _QualificationLawSpec(
        "afk-family-instance-correspondence-result",
        "family-instance-correspondence",
        (
            "analysis.asymptotic-protocol-family",
            "analysis.logical-nat-literal",
            "analysis.native-subject-projection",
            "analysis.challenge-domain",
            "analysis.fixed-public-setup",
        ),
        3,
        "conditional-family-instance-correspondence",
        "family-instance-correspondence-conclusion-v0",
        "hypothesis-context",
        0,
        4,
        True,
    ),
    _QualificationLawSpec(
        "afk-member-specialization-result",
        "adaptive-knowledge-extraction-at-fixed-length-q-lt-n",
        (
            "analysis.asymptotic-protocol-family",
            "analysis.logical-nat-literal",
            "analysis.native-subject-projection",
            "analysis.challenge-domain",
            "analysis.fixed-public-setup",
        ),
        3,
        "dependent-family-member-specialization",
        "fixed-member-knowledge-conclusion-v0",
        "hypothesis-context",
        2,
        1,
        True,
    ),
)


def _resolved_profile_declaration(
    selected_profile: object,
    reference: object,
    declaration_kind: str,
) -> tuple[object, str, object]:
    """Resolve one exact declaration ref to owner, label, and full body."""

    # Semantic bodies retain the canonical datum form of a declaration
    # reference.  Decode that closed representation before resolving it; do
    # not treat the encoded form as a caller-selected label.
    if type(reference) is k1.DatumVariant:
        payload = reference.payload
        if type(payload) is not k1.DatumRecord:
            raise AuthorityError("qualification declaration has a foreign reference")
        fields = dict(payload.fields)
        if (
            reference.case == 0
            and tuple(fields) == (0, 1)
            and type(fields[0]) is k1.Symbol
            and type(fields[1]) is k1.Nat
        ):
            reference = k1.ProfileLocalDeclarationRef(fields[0].value, fields[1].value)
        elif (
            reference.case == 1
            and tuple(fields) == (0, 1, 2)
            and type(fields[0]) is k1.BytesValue
            and type(fields[1]) is k1.Symbol
            and type(fields[2]) is k1.Nat
        ):
            imported_matches = tuple(
                profile_id
                for profile_id in _analysis_profile_import_closure(selected_profile)
                if profile_id.internal_reference() == fields[0].value
            )
            if len(imported_matches) != 1:
                raise AuthorityError("qualification declaration owner is not imported")
            reference = k1.ImportedProfileDeclarationRef(
                imported_matches[0], fields[1].value, fields[2].value
            )
        else:
            raise AuthorityError("qualification declaration has a foreign reference")

    if type(reference) is k1.ProfileLocalDeclarationRef:
        owner = selected_profile
        ordinal = reference.local_ordinal
        kind = reference.declaration_kind
    elif type(reference) is k1.ImportedProfileDeclarationRef:
        owner = ANALYSIS_PROFILE_BUNDLE.get(reference.profile_id)
        if (
            type(owner) is not k1.SemanticLanguageProfile
            or reference.profile_id
            not in _analysis_profile_import_closure(selected_profile)
        ):
            raise AuthorityError("qualification declaration owner is not imported")
        ordinal = reference.local_ordinal
        kind = reference.declaration_kind
    else:
        raise AuthorityError("qualification declaration has a foreign reference")
    if kind != declaration_kind:
        raise AuthorityError("qualification declaration has the wrong kind")
    label, body = _cached_resolved_profile_declaration(owner, declaration_kind, ordinal)
    return owner, label, body


@lru_cache(maxsize=4096)
def _cached_resolved_profile_declaration(
    owner: object,
    declaration_kind: str,
    ordinal: int,
) -> tuple[str, object]:
    """Resolve an immutable profile catalog coordinate by exact value."""

    if type(owner) is not k1.SemanticLanguageProfile:
        raise AuthorityError("qualification declaration owner is malformed")
    catalog = k1.profile_declaration_catalogs(owner).get(declaration_kind)
    if catalog is None or not 0 <= ordinal < len(catalog.values):
        raise AuthorityError("qualification declaration is outside its catalog")
    body = catalog.values[ordinal]
    label = _record_field(body, 0, "qualification declaration")
    if type(label) is not k1.Symbol:
        raise AuthorityError("qualification declaration label is malformed")
    return label.value, body


def _derive_qualification_subject_context(
    *,
    semantic_profile: object,
    proposition_id: object,
    semantic_basis_id: object,
    support_id: object,
    validation_basis_id: object,
    inherited_hypothesis_context_id: object | None = None,
    judgment_record: AnalysisJudgmentRecordBodyV0 | None = None,
    result_id: object | None = None,
    outcome_kind: AttemptKind | None = None,
) -> QualificationSubjectContext:
    """Derive qualification inputs only from an already formed candidate."""

    proposition = _formed_analysis_body(proposition_id, "analysis.proposition")
    goal = _formed_analysis_body(proposition.goal_id, "analysis.goal")
    question = _formed_analysis_body(goal.question_id, "analysis.question")
    basis = _formed_analysis_body(semantic_basis_id, "analysis.semantic-basis")
    support = _formed_analysis_body(support_id, "analysis.support-instantiation")
    validation = _formed_analysis_body(validation_basis_id, "analysis.validation-basis")
    _, family_label, _ = _resolved_profile_declaration(
        _formed_analysis_profile(goal.question_id, "analysis.question"),
        question.family,
        "analysis.property-family",
    )
    _, basis_family_label, _ = _resolved_profile_declaration(
        _formed_analysis_profile(semantic_basis_id, "analysis.semantic-basis"),
        basis.family,
        "analysis.property-family",
    )
    inherited = proposition.hypothesis_context_id
    if (
        inherited_hypothesis_context_id is not None
        and inherited_hypothesis_context_id != inherited
    ):
        raise AuthorityError("qualification inherited context was substituted")
    if (
        basis_family_label != family_label
        or basis.exact_question_id != goal.question_id
        or support.semantic_basis_id != semantic_basis_id
        or support.proposition_id != proposition_id
    ):
        raise AuthorityError("qualification subject basis or support was substituted")
    if judgment_record is not None:
        if type(judgment_record) is not AnalysisJudgmentRecordBodyV0:
            raise AuthorityError("qualification judgment record has the wrong shape")
        if (
            judgment_record.proposition_id != _id_datum(proposition_id)
            or judgment_record.inherited_hypothesis_context_id != _id_datum(inherited)
            or judgment_record.semantic_basis_id != _id_datum(semantic_basis_id)
            or judgment_record.support_coordinate != _id_datum(support_id)
            or judgment_record.validation_basis_id != _id_datum(validation_basis_id)
        ):
            raise AuthorityError("qualification judgment chain was substituted")
    return QualificationSubjectContext(
        semantic_profile,
        proposition_id,
        proposition.goal_id,
        goal.question_id,
        family_label,
        question.exact_subjects,
        question.context,
        question.family_payload,
        inherited,
        semantic_basis_id,
        basis,
        support_id,
        support,
        validation_basis_id,
        validation,
        judgment_record,
        result_id,
        outcome_kind,
    )


def _qualification_law(label: str) -> _QualificationLawSpec:
    matches = tuple(
        law for law in _QUALIFICATION_LAW_SPECS if law.qualification_label == label
    )
    if len(matches) != 1:
        raise AuthorityError("actual qualification has no unique executable law")
    return matches[0]


def _inverse_match_qualified_afk_family(family_id: object) -> AFKAsymptoticFamily:
    """Recover ``F`` only from its authenticated family constructor."""

    family_body = _formed_analysis_body(
        family_id, "analysis.asymptotic-protocol-family"
    )
    if type(family_body) is not AnalysisAsymptoticProtocolFamilyBodyV0:
        raise AuthorityError("qualification family has the wrong exact body")
    _, language_label, _ = _resolved_profile_declaration(
        ANALYSIS_TRANSPORT_PROFILE,
        family_body.family_language,
        "analysis.asymptotic-family-language",
    )
    payload = family_body.canonical_family_payload
    if language_label != "afk-schnorr-family-v0" or type(payload) is not k1.DatumRecord:
        raise AuthorityError("qualification family is not an AFK family constructor")
    fields = dict(payload.fields)
    if tuple(fields) != tuple(range(9)):
        raise AuthorityError("qualification family payload is incomplete")
    ro_payload = fields[8]
    if type(ro_payload) is not k1.DatumRecord:
        raise AuthorityError("qualification family RO-index domain is malformed")
    ro_fields = dict(ro_payload.fields)
    if tuple(ro_fields) != tuple(range(7)):
        raise AuthorityError("qualification family RO-index domain is incomplete")

    symbol_fields = (0, 1, 5, 6, 7)
    ro_symbol_fields = (0, 1, 3, 4, 5)
    if (
        any(type(fields[index]) is not k1.Symbol for index in symbol_fields)
        or type(fields[2]) is not k1.Symbol
        or type(fields[3]) is not k1.Nat
        or type(fields[4]) is not k1.Nat
        or any(type(ro_fields[index]) is not k1.Symbol for index in ro_symbol_fields)
        or type(ro_fields[2]) is not k1.DatumSeq
        or not ro_fields[2].values
        or any(type(item) is not k1.Nat for item in ro_fields[2].values)
        or type(ro_fields[6]) is not k1.DatumSeq
        or any(type(item) is not k1.Symbol for item in ro_fields[6].values)
    ):
        raise AuthorityError("qualification family payload has a foreign carrier")

    family = AFKAsymptoticFamily(
        fields[0].value,
        fields[1].value,
        fields[2].value,
        fields[3].value,
        fields[4].value,
        fields[5].value,
        fields[6].value,
        fields[7].value,
        FamilyROIndexDomain(
            ro_fields[0].value,
            ro_fields[1].value,
            tuple(item.value for item in ro_fields[2].values),
            ro_fields[3].value,
            ro_fields[4].value,
            ro_fields[5].value,
            tuple(item.value for item in ro_fields[6].values),
        ),
        _FAMILY_ISSUER,
    )
    if _family_body(family) != payload or family_definition_id(family) != family_id:
        raise AuthorityError("qualification family does not inverse-match its subject")
    return family


def _qualification_family(
    law: _QualificationLawSpec,
    context: QualificationSubjectContext,
) -> AFKAsymptoticFamily:
    """Inverse-match the invocation-local ``F`` selected by one law."""

    if law.qualification_label == "afk-family-applicability-result":
        if context.exact_subjects[0] != AFK_V2_THM4_CLASSICAL_ROM:
            raise AuthorityError("qualification applicability names another theorem")
        family_id = context.exact_subjects[1]
    elif law.qualification_label in (
        "conditional-assumed-external-all-n",
        "afk-family-transport-result",
    ):
        family_id = context.exact_subjects[0]
    else:
        raise AuthorityError("qualification law has no AFK family subject")
    return _inverse_match_qualified_afk_family(family_id)


def _family_source_hypotheses_for_qualification(
    family: AFKAsymptoticFamily,
) -> tuple[object, ...]:
    family_id = family_definition_id(family)
    labels = (
        "total-single-valued-family-denotation",
        "family-projection-coherence",
        "uniform-prime-order-schnorr-family",
        "uniform-polynomial-time-relation-membership",
        "uniform-polynomial-time-verifier",
    )
    return canonical_hypotheses(
        _exact_premise_goal_id(
            family_label,
            (family_id,),
            _family_semantic_context(family, axes=("fresh-source",)),
            k1.DatumRecord(((0, _id_datum(family_id)), (1, k1.Nat(ordinal)))),
            selected_profile=ANALYSIS_TRANSPORT_PROFILE,
        )
        for ordinal, family_label in enumerate(labels)
    )


def _family_transport_hypotheses_for_qualification(
    family: AFKAsymptoticFamily,
) -> tuple[object, ...]:
    return hypothesis_union(
        family_applicability_premise_ids(family),
        _family_source_hypotheses_for_qualification(family),
        (theorem_truth_goal_id(_AFK_GLOBAL_THEOREM_SCHEMA),),
    )


@dataclass(frozen=True)
class _QualificationExpectation:
    basis_id: object
    support_id: object | None
    conclusion: object | None
    quantitative: object | None
    operation_policy_id: object | None
    policy_closure: object
    external_result_id: object | None = None


def _qualification_family_source_basis_id(
    family: AFKAsymptoticFamily,
    hypotheses: tuple[object, ...],
) -> object:
    family_id = family_definition_id(family)
    return _analysis_transport_id(
        "analysis.semantic-basis",
        AnalysisSemanticBasisBodyV0(
            _family_declaration_ref(
                ANALYSIS_TRANSPORT_PROFILE,
                "asymptotic-k-out-of-n-special-soundness",
                owner_profile=ANALYSIS_TRANSPORT_PROFILE,
            ),
            family_question_id(family, "source-two-special-soundness"),
            _native_rule_source(
                ANALYSIS_TRANSPORT_PROFILE,
                ANALYSIS_PROPERTY_PROFILE,
                "conditional-family-instance-correspondence",
                k1.DatumRecord(
                    (
                        (
                            0,
                            _id_datum(family_id, "analysis.asymptotic-protocol-family"),
                        ),
                        (1, k1.Symbol("assumed-all-n-source-property")),
                    )
                ),
            ),
            _hypothesis_node_requirements(hypotheses, transport=True),
            complete_read_purpose_requirements(
                family_manifest_schema_ids=(
                    family_manifest_schema_id(family, "fresh-source"),
                ),
            ),
            _conclusion_schema_ref(
                ANALYSIS_TRANSPORT_PROFILE,
                ANALYSIS_PROPERTY_PROFILE,
                "k-out-of-n-conclusion-v0",
            ),
            k1.DatumRecord(
                (
                    (0, k1.Symbol("external-all-n-source-assumption")),
                    (1, _id_datum(family_id, "analysis.asymptotic-protocol-family")),
                )
            ),
        ),
    )


def _qualification_theorem_truth_basis_id(schema: FSTheoremSchema) -> object:
    schema_id = fs_theorem_schema_id(schema)
    return _analysis_transport_id(
        "analysis.semantic-basis",
        AnalysisSemanticBasisBodyV0(
            _family_declaration_ref(
                ANALYSIS_TRANSPORT_PROFILE,
                "theorem-truth",
                owner_profile=ANALYSIS_TRANSPORT_PROFILE,
            ),
            _analysis_transport_id(
                "analysis.question", theorem_truth_question_body(schema)
            ),
            _imported_theorem_rule_source(schema_id),
            k1.DatumSeq(()),
            (),
            _conclusion_schema_ref(
                ANALYSIS_TRANSPORT_PROFILE,
                ANALYSIS_TRANSPORT_PROFILE,
                "theorem-truth-conclusion-v0",
            ),
            k1.DatumRecord(
                (
                    (0, k1.Symbol("explicit-assumed-theorem-truth")),
                    (1, _id_datum(schema_id, "analysis.theorem-schema")),
                )
            ),
        ),
    )


def _qualification_predecessors(
    support: AnalysisSupportInstantiationBodyV0,
    *,
    nested: bool,
    expected_uses: tuple[tuple[str, str, str], ...],
) -> tuple[tuple[object, object, object, QualificationSubjectContext], ...]:
    entries = support.non_hypothesis_premise_bindings
    portable = support.source_support_bindings
    if type(entries) is not k1.DatumSeq:
        raise AuthorityError("qualification predecessor bindings are not a sequence")
    if len(entries.values) != len(expected_uses) or (
        not nested
        and (
            type(portable) is not k1.DatumSeq
            or len(portable.values) != len(entries.values)
        )
    ):
        raise AuthorityError(
            "qualification predecessor authority bindings are incomplete"
        )
    result = []
    for ordinal, entry in enumerate(entries.values):
        if type(entry) is not k1.DatumRecord:
            raise AuthorityError("qualification predecessor binding is not a record")
        fields = dict(entry.fields)
        if tuple(fields) != (0, 1) or fields[0] != k1.Nat(ordinal):
            raise AuthorityError("qualification predecessor ordinal was substituted")
        if nested:
            payload = fields[1]
            if type(payload) is not k1.DatumRecord or tuple(dict(payload.fields)) != (
                0,
                1,
            ):
                raise AuthorityError("qualification predecessor pair is incomplete")
            pair = dict(payload.fields)
            coordinate_value, portable_value = pair[0], pair[1]
        else:
            coordinate_value, portable_value = fields[1], portable.values[ordinal]
        coordinate = _formed_analysis_id(
            coordinate_value, "analysis.checked-result-coordinate"
        )
        portable_id = _formed_analysis_id(
            portable_value, "analysis.portable-source-authority-binding"
        )
        portable_body = _formed_analysis_body(
            portable_id, "analysis.portable-source-authority-binding"
        )
        envelope = portable_body.envelope
        if (
            type(envelope) is not k1.PortableSourceAuthorityBinding
            or envelope.owner_source_coordinate != coordinate
        ):
            raise AuthorityError("portable authority binding names another predecessor")
        expected_qualification, expected_consumer, expected_purpose = expected_uses[
            ordinal
        ]
        predecessor_context, predecessor_qualification = (
            _checked_result_qualification_context(coordinate)
        )
        _, actual_qualification, _ = _resolved_profile_declaration(
            predecessor_context.semantic_profile,
            predecessor_qualification,
            "analysis.qualification",
        )
        requirement_id = envelope.capability_requirement.owner_requirement
        requirement = _formed_analysis_body(
            requirement_id, "analysis.capability-requirement-payload"
        )
        requirement_profile = _formed_analysis_profile(
            requirement_id, "analysis.capability-requirement-payload"
        )
        _, requirement_label, _ = _resolved_profile_declaration(
            requirement_profile,
            requirement.qualification,
            "analysis.qualification-requirement",
        )
        _, consumer_label, _ = _resolved_profile_declaration(
            requirement_profile,
            requirement.named_consumer,
            "analysis.named-consumer",
        )
        _, purpose_label, _ = _resolved_profile_declaration(
            requirement_profile,
            requirement.typed_purpose,
            "analysis.typed-purpose",
        )
        contract = _formed_analysis_body(
            envelope.owner_binding_payload, "analysis.source-authority-contract"
        )
        closure = _formed_analysis_body(
            envelope.owner_policy_closure, "analysis.owner-policy-closure"
        )
        closure_profile = _formed_analysis_profile(
            envelope.owner_policy_closure, "analysis.owner-policy-closure"
        )
        contract_profile = _formed_analysis_profile(
            envelope.owner_binding_payload, "analysis.source-authority-contract"
        )
        expected_dependencies = _canonical_identifier_set(
            (*contract.immediate_policy_ids, *contract.transitive_policy_ids),
            what="portable predecessor policy closure",
        )
        if (
            envelope.owner_domain != k1.Symbol("analysis")
            or envelope.capability_family != k1.Symbol("checked-result-use")
            or envelope.capability_requirement.owner_domain != envelope.owner_domain
            or envelope.capability_requirement.capability_family
            != envelope.capability_family
            or type(envelope.operation_policy) is not k1.BoundOwnerOperationPolicy
            or len(contract.immediate_policy_ids) != 1
            or envelope.operation_policy.owner_policy_binding
            != contract.immediate_policy_ids[0]
            or contract.checked_result_coordinate_id != coordinate
            or contract.capability_requirement_payload_id != requirement_id
            or closure.owner_coordinate != contract.owner_coordinate
            or closure.policy_ids != expected_dependencies
            or closure.derivation_law
            != analysis_profile_declaration_ref_body(
                analysis_profile_declaration_ref(
                    closure_profile,
                    ANALYSIS_KERNEL_PROFILE,
                    "analysis.semantic-law",
                    "derived-used-policy-closure-v0",
                )
            )
            or contract_profile != predecessor_context.semantic_profile
            or requirement_profile != predecessor_context.semantic_profile
            or requirement.proposition_id != predecessor_context.proposition_id
            or requirement_label != "exact-inherited-conditional"
            or actual_qualification != expected_qualification
            or consumer_label != expected_consumer
            or purpose_label != expected_purpose
        ):
            raise AuthorityError(
                "portable predecessor authority contract or exact use was substituted"
            )
        result.append((coordinate, portable_id, envelope, predecessor_context))
    return tuple(result)


def _qualification_policy_closure(
    predecessors: tuple[
        tuple[object, object, object, QualificationSubjectContext], ...
    ],
) -> object:
    dependencies: list[object] = []
    for _, _, envelope, _ in predecessors:
        closure = _formed_analysis_body(
            envelope.owner_policy_closure, "analysis.owner-policy-closure"
        )
        dependencies.extend(closure.policy_ids)
    canonical = _canonical_identifier_set(
        dependencies, what="qualification source-policy closure"
    )
    return k1.DatumSeq(tuple(_id_datum(item) for item in canonical))


def _qualification_normalized_concrete_body(normalization_value: object) -> object:
    normalization_id = _formed_analysis_id(
        normalization_value, "analysis.pointwise-quantitative-normalization"
    )
    normalization = _formed_analysis_body(
        normalization_id, "analysis.pointwise-quantitative-normalization"
    )
    substitution = normalization.logical_index_substitution
    if type(substitution) is not k1.DatumRecord:
        raise AuthorityError(
            "pointwise normalization has no exact logical substitution"
        )
    fields = dict(substitution.fields)
    if tuple(fields) != (0, 1, 2, 3, 4):
        raise AuthorityError("pointwise normalization substitution is incomplete")
    return fields[4]


def _qualification_normalization_challenge_domain_id(
    normalization_value: object,
) -> object:
    normalization_id = _formed_analysis_id(
        normalization_value, "analysis.pointwise-quantitative-normalization"
    )
    normalization = _formed_analysis_body(
        normalization_id, "analysis.pointwise-quantitative-normalization"
    )
    value = _record_field(
        normalization.challenge_cardinality_substitution,
        1,
        "pointwise normalization challenge substitution",
    )
    return _formed_analysis_id(value, "analysis.challenge-domain")


def _qualification_embedded_fixed_setup_id(correspondence_value: object) -> object:
    if (
        type(correspondence_value) is not k1.DatumVariant
        or correspondence_value.case != 1
        or type(correspondence_value.payload) is not k1.DatumRecord
    ):
        raise AuthorityError("family correspondence payload has no exact embedded body")
    value = _record_field(
        correspondence_value.payload,
        19,
        "embedded FS correspondence",
    )
    return _formed_analysis_id(value, "analysis.fixed-public-setup")


def _qualification_assumed_node_bindings(
    nodes: tuple[AnalysisHypothesisNodeV0, ...],
    *,
    theorem_validation: bool,
) -> object:
    theorem_goal = theorem_truth_goal_id(_AFK_GLOBAL_THEOREM_SCHEMA)
    return k1.DatumSeq(
        tuple(
            k1.DatumRecord(
                (
                    (0, k1.Nat(node.local_ordinal)),
                    (
                        1,
                        k1.DatumRecord(
                            (
                                (0, _id_datum(node.goal_id, "analysis.goal")),
                                (1, k1.DatumVariant(0, k1.UNIT)),
                                (
                                    2,
                                    k1.DatumVariant(
                                        1,
                                        _id_datum(
                                            AFK_V2_THM4_SOURCE_VALIDATION,
                                            "analysis.theorem-source-validation",
                                        ),
                                    )
                                    if theorem_validation
                                    and node.goal_id == theorem_goal
                                    else k1.DatumVariant(0, k1.UNIT),
                                ),
                            )
                        ),
                    ),
                )
            )
            for node in nodes
        )
    )


def _qualification_exact_concrete_source_support_id(manifest_id: object) -> object:
    manifest = _formed_analysis_body(manifest_id, "analysis.semantic-read-manifest")
    profile = _formed_analysis_body(
        manifest.source_profile_id, "analysis.source-profile"
    )
    owners_by_slot: dict[tuple[int, int], object] = {}
    for slot, schema in zip(
        manifest.slots.values, profile.slot_schemas.values, strict=True
    ):
        slot_fields = dict(slot.fields)
        schema_fields = dict(schema.fields)
        fact = schema_fields[1]
        axis = schema_fields[2]
        if type(fact) is not k1.Nat or type(axis) is not k1.DatumVariant:
            raise AuthorityError("concrete source support slot schema is malformed")
        owners_by_slot.setdefault((fact.value, axis.case), slot_fields[1])
    core = _SOURCE_FACT_KIND_ORDINAL[SourceFactKind.CORE]
    protocol = _SOURCE_FACT_KIND_ORDINAL[SourceFactKind.PROTOCOL]
    construction = _SOURCE_FACT_KIND_ORDINAL[SourceFactKind.CONSTRUCTION]
    relation = _SOURCE_FACT_KIND_ORDINAL[SourceFactKind.RELATION_BINDING]
    plan = _SOURCE_FACT_KIND_ORDINAL[SourceFactKind.PLAN_WITNESS_BINDING]
    if len(manifest.slots.values) == len(_FRESH_SOURCE_SLOT_TOKENS):
        owner_order = ((core, 0), (protocol, 1), (relation, 1), (plan, 1))
    elif len(manifest.slots.values) == len(_AFK_FRESH_FS_SOURCE_SLOT_TOKENS):
        owner_order = (
            (core, 0),
            (construction, 2),
            (protocol, 1),
            (protocol, 2),
            (relation, 1),
            (relation, 2),
            (plan, 1),
            (plan, 2),
        )
    else:
        raise AuthorityError(
            "concrete source support manifest has another active shape"
        )
    try:
        ordered_owners = tuple(owners_by_slot[item] for item in owner_order)
    except KeyError as error:
        raise AuthorityError(
            "concrete source support manifest omits an owner field"
        ) from error
    bindings = k1.DatumSeq(
        tuple(
            k1.DatumRecord(((0, k1.Nat(ordinal)), (1, owner)))
            for ordinal, owner in enumerate(ordered_owners)
        )
    )
    return _analysis_id(
        "analysis.source-support",
        AnalysisSourceSupportBodyV0(manifest_id, bindings, ()),
    )


def _qualification_correspondence_support_id(
    context: QualificationSubjectContext,
    basis_id: object,
    payload: dict[int, object],
    hypothesis_context: AnalysisHypothesisContextBodyV0,
    concrete_reads: tuple[object, ...],
    family_reads: tuple[object, ...],
) -> object:
    profile_pairs = payload[9]
    if type(profile_pairs) is not k1.DatumRecord:
        raise AuthorityError("correspondence experiment profile join is malformed")
    pair_fields = dict(profile_pairs.fields)
    if (
        tuple(pair_fields) != (0, 1)
        or type(pair_fields[0]) is not k1.DatumSeq
        or type(pair_fields[1]) is not k1.DatumSeq
        or len(pair_fields[0].values) != 2
        or len(pair_fields[1].values) != 2
        or len(family_reads) != 2
        or len(concrete_reads) != 2
    ):
        raise AuthorityError("correspondence experiment profile join is incomplete")
    family_experiments = tuple(
        _formed_analysis_id(item, "analysis.experiment-profile")
        for item in pair_fields[0].values
    )
    concrete_experiments = tuple(
        _formed_analysis_id(item, "analysis.experiment-profile")
        for item in pair_fields[1].values
    )
    expected_family = tuple(
        k1.DatumVariant(
            0,
            _family_support_schema_binding(
                manifest_id,
                experiment_id,
                context.inherited_hypothesis_context_id,
                hypothesis_context.nodes,
            ),
        )
        for manifest_id, experiment_id in zip(
            family_reads, family_experiments, strict=True
        )
    )
    source_support = context.support.source_support_bindings
    if type(source_support) is not k1.DatumSeq or len(source_support.values) != 4:
        raise AuthorityError("correspondence source support is incomplete")
    expected_concrete = []
    for ordinal, (manifest_id, experiment_id) in enumerate(
        zip(concrete_reads, concrete_experiments, strict=True), start=2
    ):
        entry = source_support.values[ordinal]
        if (
            type(entry) is not k1.DatumVariant
            or entry.case != 1
            or type(entry.payload) is not k1.DatumRecord
        ):
            raise AuthorityError("correspondence concrete support arm is malformed")
        fields = dict(entry.payload.fields)
        if tuple(fields) != (0, 1, 2):
            raise AuthorityError("correspondence concrete support arm is incomplete")
        support_id = _formed_analysis_id(fields[2], "analysis.source-support")
        support_body = _formed_analysis_body(support_id, "analysis.source-support")
        expected_support_id = _qualification_exact_concrete_source_support_id(
            manifest_id
        )
        if (
            fields[0] != _id_datum(manifest_id, "analysis.semantic-read-manifest")
            or fields[1] != _id_datum(experiment_id, "analysis.experiment-profile")
            or support_body.semantic_read_manifest_id != manifest_id
            or support_body.derived_owner_policy_dependency_closure != ()
            or support_id != expected_support_id
        ):
            raise AuthorityError(
                "correspondence concrete source support is cross-axis or detached"
            )
        expected_concrete.append(
            k1.DatumVariant(
                1,
                k1.DatumRecord(
                    (
                        (0, _id_datum(manifest_id, "analysis.semantic-read-manifest")),
                        (1, _id_datum(experiment_id, "analysis.experiment-profile")),
                        (2, _id_datum(support_id, "analysis.source-support")),
                    )
                ),
            )
        )
    expected_source_support = k1.DatumSeq((*expected_family, *expected_concrete))
    if source_support != expected_source_support:
        raise AuthorityError(
            "correspondence source support order or axis was substituted"
        )
    assumed = _qualification_assumed_node_bindings(
        hypothesis_context.nodes, theorem_validation=False
    )
    return _analysis_support_instantiation_id(
        profile=context.semantic_profile,
        semantic_basis_id=basis_id,
        proposition_id=context.proposition_id,
        assumed_goals=tuple(node.goal_id for node in hypothesis_context.nodes),
        assumed_hypothesis_node_bindings=assumed,
        source_support_bindings=expected_source_support,
    )


def _qualification_fixed_support_id(
    context: QualificationSubjectContext,
    basis_id: object,
    hypothesis_context: AnalysisHypothesisContextBodyV0,
    concrete_reads: tuple[object, ...],
    predecessors: tuple[
        tuple[object, object, object, QualificationSubjectContext], ...
    ],
) -> object:
    if len(concrete_reads) != 1:
        raise AuthorityError("fixed-member support has another concrete read domain")
    expected_predecessors = k1.DatumSeq(
        tuple(
            k1.DatumRecord(
                (
                    (0, k1.Nat(ordinal)),
                    (
                        1,
                        k1.DatumRecord(
                            (
                                (
                                    0,
                                    _id_datum(
                                        coordinate,
                                        "analysis.checked-result-coordinate",
                                    ),
                                ),
                                (
                                    1,
                                    _id_datum(
                                        portable_id,
                                        "analysis.portable-source-authority-binding",
                                    ),
                                ),
                            )
                        ),
                    ),
                )
            )
            for ordinal, (coordinate, portable_id, _, _) in enumerate(predecessors)
        )
    )
    if context.support.non_hypothesis_premise_bindings != expected_predecessors:
        raise AuthorityError("fixed-member predecessor binding order was substituted")
    source_support = context.support.source_support_bindings
    if type(source_support) is not k1.DatumSeq or len(source_support.values) != 1:
        raise AuthorityError("fixed-member concrete source support is incomplete")
    support_id = _formed_analysis_id(
        source_support.values[0], "analysis.source-support"
    )
    support_body = _formed_analysis_body(support_id, "analysis.source-support")
    expected_support_id = _qualification_exact_concrete_source_support_id(
        concrete_reads[0]
    )
    if (
        support_body.semantic_read_manifest_id != concrete_reads[0]
        or support_body.derived_owner_policy_dependency_closure != ()
        or support_id != expected_support_id
    ):
        raise AuthorityError(
            "fixed-member source support names another concrete manifest"
        )
    expected_source_support = k1.DatumSeq(
        (_id_datum(support_id, "analysis.source-support"),)
    )
    if source_support != expected_source_support:
        raise AuthorityError("fixed-member source support encoding was substituted")
    assumed = _qualification_assumed_node_bindings(
        hypothesis_context.nodes, theorem_validation=True
    )
    return _analysis_support_instantiation_id(
        profile=context.semantic_profile,
        semantic_basis_id=basis_id,
        proposition_id=context.proposition_id,
        assumed_goals=tuple(node.goal_id for node in hypothesis_context.nodes),
        theorem_validations={
            theorem_truth_goal_id(
                _AFK_GLOBAL_THEOREM_SCHEMA
            ): AFK_V2_THM4_SOURCE_VALIDATION
        },
        non_hypothesis_premise_bindings=expected_predecessors,
        assumed_hypothesis_node_bindings=assumed,
        source_support_bindings=expected_source_support,
    )


def _exact_qualification_expectation(
    law: _QualificationLawSpec,
    context: QualificationSubjectContext,
    qualification: object,
) -> _QualificationExpectation:
    label = law.qualification_label
    empty_closure = k1.DatumSeq(())
    unit = k1.DatumVariant(0, k1.UNIT)

    if label == "finite-special-soundness-result":
        policy = _analysis_operation_policy_id(
            context.proposition_id,
            (("finite-special-soundness", ("finite-special-soundness",)),),
            profile=context.semantic_profile,
        )
        return _QualificationExpectation(
            schnorr_semantic_basis_id(_SCHNORR_PINNED_PROPOSITION),
            _analysis_support_instantiation_id(
                profile=context.semantic_profile,
                semantic_basis_id=context.semantic_basis_id,
                proposition_id=context.proposition_id,
                assumed_goals=_SCHNORR_PINNED_PROPOSITION.hypotheses,
            ),
            _expand_probe_references(
                _property_conclusion_body(_SCHNORR_PINNED_PROPOSITION.goal.conclusion)
            ),
            unit,
            policy,
            empty_closure,
        )

    if label == "finite-cover-certificate-result":
        kind = _certificate_kind_from_context(context)
        _validate_finite_cover_certificate_semantics(kind)
        proposition_id = finite_cover_certificate_proposition_id(
            _SCHNORR_PINNED_SOURCE,
            _SCHNORR_PINNED_PROFILE,
            kind,
        )
        basis = finite_cover_certificate_semantic_basis_id(
            _SCHNORR_PINNED_SOURCE,
            _SCHNORR_PINNED_PROFILE,
            kind,
        )
        policy = _finite_cover_operation_policy_id(proposition_id)
        return _QualificationExpectation(
            basis,
            _finite_cover_empty_support_id(basis, proposition_id),
            _finite_cover_certificate_conclusion(
                _SCHNORR_PINNED_SOURCE,
                _SCHNORR_PINNED_PROFILE,
                kind,
            ),
            unit,
            policy,
            empty_closure,
        )

    if label == "finite-fixed-extractor-universal-result":
        certificate_ids = _validate_finite_cover_certificate_bindings(
            context.support
        )
        _run_finite_cover_stream()
        proposition_id = fixed_extractor_proposition_id(
            _SCHNORR_PINNED_SOURCE, _SCHNORR_PINNED_PROFILE
        )
        basis = fixed_extractor_semantic_basis_id(
            _SCHNORR_PINNED_SOURCE, _SCHNORR_PINNED_PROFILE
        )
        policy = _finite_cover_operation_policy_id(proposition_id)
        return _QualificationExpectation(
            basis,
            finite_cover_support_id(
                _SCHNORR_PINNED_SOURCE,
                _SCHNORR_PINNED_PROFILE,
                certificate_ids,
            ),
            _fixed_extractor_conclusion_body(
                _SCHNORR_PINNED_SOURCE, _SCHNORR_PINNED_PROFILE
            ),
            unit,
            policy,
            empty_closure,
        )

    if label == "conditional-assumed-external-all-n":
        family = _qualification_family(law, context)
        hypotheses = _family_source_hypotheses_for_qualification(family)
        basis = _qualification_family_source_basis_id(family, hypotheses)
        if (
            type(context.support.source_support_bindings) is not k1.DatumSeq
            or len(context.support.source_support_bindings.values) != 1
        ):
            raise AuthorityError("external family result lacks one exact authority")
        authority = context.support.source_support_bindings.values[0]
        support = _analysis_support_instantiation_id(
            profile=context.semantic_profile,
            semantic_basis_id=basis,
            proposition_id=context.proposition_id,
            assumed_goals=hypotheses,
            source_support_bindings=k1.DatumSeq((authority,)),
        )
        result_id = k1.content_id(
            "analysis.external-family-source-result",
            k1.encode_datum(
                k1.DatumRecord(
                    (
                        (0, authority),
                        (1, _id_datum(context.proposition_id, "analysis.proposition")),
                        (2, _id_datum(basis, "analysis.semantic-basis")),
                        (3, _id_datum(support, "analysis.support-instantiation")),
                        (
                            4,
                            _id_datum(
                                context.validation_basis_id, "analysis.validation-basis"
                            ),
                        ),
                        (5, analysis_profile_declaration_ref_body(qualification)),
                        (6, k1.Symbol("conditional-assumed-all-n-source-result")),
                    )
                )
            ),
            semantic_regime=k1.SEMANTIC_REGIME_ID,
        )
        return _QualificationExpectation(
            basis, support, None, None, None, empty_closure, result_id
        )

    if label == "conditional-assumed-theorem-truth":
        schema = _AFK_GLOBAL_THEOREM_SCHEMA
        schema_id = fs_theorem_schema_id(schema)
        basis = _qualification_theorem_truth_basis_id(schema)
        source_validation = _require_selected_theorem_source_validation(schema)
        support = _analysis_support_instantiation_id(
            profile=context.semantic_profile,
            semantic_basis_id=basis,
            proposition_id=context.proposition_id,
            assumed_goals=(context.goal_id,),
            theorem_validations={context.goal_id: source_validation},
        )
        result_id = k1.content_id(
            "analysis.assumed-theorem-truth-treatment",
            k1.encode_datum(
                k1.DatumRecord(
                    (
                        (0, _id_datum(schema_id, "analysis.theorem-schema")),
                        (1, _id_datum(context.proposition_id, "analysis.proposition")),
                        (2, _id_datum(basis, "analysis.semantic-basis")),
                        (3, _id_datum(support, "analysis.support-instantiation")),
                        (
                            4,
                            _id_datum(
                                context.validation_basis_id, "analysis.validation-basis"
                            ),
                        ),
                        (5, analysis_profile_declaration_ref_body(qualification)),
                        (6, k1.Symbol("Assumed")),
                    )
                )
            ),
            semantic_regime=k1.SEMANTIC_REGIME_ID,
        )
        return _QualificationExpectation(
            basis, support, None, None, None, empty_closure, result_id
        )

    if label == "afk-family-applicability-result":
        family = _qualification_family(law, context)
        candidate = derive_family_applicability_input(
            _AFK_GLOBAL_THEOREM_SCHEMA, family
        )
        candidate_id = family_applicability_input_id(candidate)
        schema_id = fs_theorem_schema_id(_AFK_GLOBAL_THEOREM_SCHEMA)
        family_id = family_definition_id(family)
        basis = _family_applicability_semantic_basis_id(
            _AFK_GLOBAL_THEOREM_SCHEMA, family, candidate
        )
        policy = _analysis_operation_policy_id(
            context.proposition_id,
            (("afk-family-property-transport", ("exact-family-applicability",)),),
            profile=context.semantic_profile,
        )
        return _QualificationExpectation(
            basis,
            _family_applicability_support_id(
                basis, context.proposition_id, candidate.applicability_premise_ids
            ),
            k1.DatumRecord(
                (
                    (0, _id_datum(schema_id, "analysis.theorem-schema")),
                    (1, _id_datum(family_id, "analysis.asymptotic-protocol-family")),
                    (
                        2,
                        _embedded_component_datum(
                            candidate_id, "analysis.family-theorem-applicability-input"
                        ),
                    ),
                    (3, k1.Symbol("affirmative-exact-family-applicability")),
                )
            ),
            unit,
            policy,
            empty_closure,
        )

    if label == "afk-family-transport-result":
        family = _qualification_family(law, context)
        candidate = derive_family_applicability_input(
            _AFK_GLOBAL_THEOREM_SCHEMA, family
        )
        hypotheses = _family_transport_hypotheses_for_qualification(family)
        family_id = family_definition_id(family)
        operator_ids = tuple(
            family_operator_binding_id(binding)
            for binding in candidate.operator_bindings
        )
        operator_values = k1.DatumSeq(
            tuple(
                _embedded_component_datum(item, "analysis.theorem-operator-binding")
                for item in operator_ids
            )
        )
        basis = _family_judgment_basis_id(
            AFK_V2_THM4_CLASSICAL_ROM,
            family,
            family_id,
            family_source_property_proposition_id(
                family,
                _family_source_hypotheses_for_qualification(family),
            ),
            family_applicability_proposition_id(family, candidate),
            theorem_truth_proposition_id(_AFK_GLOBAL_THEOREM_SCHEMA),
            family_goal_id(family, "target-adaptive-knowledge-q-lt-N"),
        )
        predecessors = _qualification_predecessors(
            context.support,
            nested=False,
            expected_uses=(
                (
                    "afk-family-applicability-result",
                    "afk-family-property-transport",
                    "exact-family-applicability",
                ),
                (
                    "conditional-assumed-external-all-n",
                    "afk-family-property-transport",
                    "all-n-two-special-soundness-source",
                ),
                (
                    "conditional-assumed-theorem-truth",
                    "afk-family-property-transport",
                    "selected-afk-theorem-truth",
                ),
            ),
        )
        support = _analysis_support_instantiation_id(
            profile=context.semantic_profile,
            semantic_basis_id=basis,
            proposition_id=context.proposition_id,
            assumed_goals=hypotheses,
            theorem_validations={
                theorem_truth_goal_id(
                    _AFK_GLOBAL_THEOREM_SCHEMA
                ): AFK_V2_THM4_SOURCE_VALIDATION
            },
            non_hypothesis_premise_bindings=context.support.non_hypothesis_premise_bindings,
            source_support_bindings=context.support.source_support_bindings,
        )
        policy = _analysis_operation_policy_id(
            context.proposition_id,
            (("afk-member-specialization", ("afk-family-target-specialization",)),),
            profile=context.semantic_profile,
        )
        return _QualificationExpectation(
            basis,
            support,
            k1.DatumRecord(
                (
                    (
                        0,
                        _id_datum(AFK_V2_THM4_CLASSICAL_ROM, "analysis.theorem-schema"),
                    ),
                    (1, _id_datum(family_id, "analysis.asymptotic-protocol-family")),
                    (2, operator_values),
                    (3, k1.Symbol("adaptive-knowledge-soundness-q-lt-N")),
                )
            ),
            operator_values,
            policy,
            _qualification_policy_closure(predecessors),
        )

    question_context = dict(context.question_context.payload.fields)
    payload = dict(context.question_payload.fields)
    hypothesis_context = _formed_analysis_body(
        context.inherited_hypothesis_context_id, "analysis.hypothesis-context"
    )
    concrete_reads, family_reads = _semantic_basis_read_sources(context.question_id)

    if label == "afk-family-instance-correspondence-result":
        concrete_body = _qualification_normalized_concrete_body(payload[7])
        basis = _analysis_transport_id(
            "analysis.semantic-basis",
            AnalysisSemanticBasisBodyV0(
                _family_declaration_ref(
                    ANALYSIS_TRANSPORT_PROFILE,
                    "family-instance-correspondence",
                    owner_profile=ANALYSIS_TRANSPORT_PROFILE,
                ),
                context.question_id,
                _native_rule_source(
                    ANALYSIS_TRANSPORT_PROFILE,
                    ANALYSIS_PROPERTY_PROFILE,
                    "conditional-family-instance-correspondence",
                    k1.DatumRecord(((0, payload[0]), (1, payload[1]), (2, payload[2]))),
                ),
                _exact_hypothesis_node_requirements(
                    context.inherited_hypothesis_context_id, hypothesis_context.nodes
                ),
                complete_read_purpose_requirements(
                    concrete_manifest_ids=concrete_reads,
                    family_manifest_schema_ids=family_reads,
                ),
                _conclusion_schema_ref(
                    ANALYSIS_TRANSPORT_PROFILE,
                    ANALYSIS_TRANSPORT_PROFILE,
                    "family-instance-correspondence-conclusion-v0",
                ),
                k1.DatumRecord(
                    (
                        (0, payload[6]),
                        (1, payload[7]),
                        (2, k1.Symbol("conditional-one-member-correspondence-only")),
                    )
                ),
            ),
        )
        policy = _analysis_operation_policy_id(
            context.proposition_id,
            (
                (
                    "afk-member-specialization",
                    ("afk-exact-family-member-specialization",),
                ),
            ),
            profile=context.semantic_profile,
        )
        support = _qualification_correspondence_support_id(
            context,
            basis,
            payload,
            hypothesis_context,
            concrete_reads,
            family_reads,
        )
        return _QualificationExpectation(
            basis,
            support,
            k1.DatumRecord(
                (
                    (0, _id_datum(context.exact_subjects[0])),
                    (1, _id_datum(context.exact_subjects[1])),
                    (2, _expand_probe_references(_id_datum(context.exact_subjects[2]))),
                    (3, k1.DatumVariant(1, concrete_body)),
                    (4, payload[2]),
                )
            ),
            unit,
            policy,
            empty_closure,
        )

    if label != "afk-member-specialization-result":
        raise AuthorityError("qualification law has no exact result reconstruction")
    predecessors = _qualification_predecessors(
        context.support,
        nested=True,
        expected_uses=(
            (
                "afk-family-transport-result",
                "afk-member-specialization",
                "afk-family-target-specialization",
            ),
            (
                "afk-family-instance-correspondence-result",
                "afk-member-specialization",
                "afk-exact-family-member-specialization",
            ),
        ),
    )
    correspondence_context = predecessors[1][3]
    if correspondence_context.exact_subjects != context.exact_subjects:
        raise AuthorityError(
            "fixed-member correspondence predecessor names another exact subject tuple"
        )
    correspondence_payload = correspondence_context.question_payload
    if type(correspondence_payload) is not k1.DatumRecord:
        raise AuthorityError(
            "fixed-member correspondence predecessor payload is malformed"
        )
    correspondence_fields = dict(correspondence_payload.fields)
    if (
        tuple(correspondence_fields) != tuple(range(10))
        or question_context[3] != correspondence_fields[6]
        or question_context[4] != correspondence_fields[7]
    ):
        raise AuthorityError(
            "fixed-member correspondence predecessor has another exact question context"
        )
    concrete_body = _qualification_normalized_concrete_body(question_context[4])
    subject_id = _local_component_id("concrete-family-member-subject", concrete_body)
    transform = afk_quantitative_transform(
        k=2, challenge_count=8, subject_id=subject_id
    )
    transform_id = afk_quantitative_transform_id(transform)
    formula_map = afk_quantitative_formula_ids(transform)
    formula_ids = tuple(formula_map[role] for role in AFK_MEMBER_FORMULA_ROLES)
    conclusion_id = afk_target_conclusion_id(
        afk_knowledge_soundness_conclusion(transform)
    )
    conclusion_value = _embedded_component_datum(
        conclusion_id, "analysis.property-conclusion"
    )
    if payload[0] != conclusion_value:
        raise AuthorityError(
            "fixed-member question names another quantitative conclusion"
        )
    capability_requirements = tuple(
        k1.DatumVariant(
            1,
            k1.DatumRecord(
                (
                    (
                        0,
                        _id_datum(
                            envelope.capability_requirement.owner_requirement,
                            "analysis.capability-requirement-payload",
                        ),
                    ),
                    (
                        1,
                        _id_datum(
                            portable_id, "analysis.portable-source-authority-binding"
                        ),
                    ),
                )
            ),
        )
        for _, portable_id, envelope, _ in predecessors
    )
    basis = _analysis_transport_id(
        "analysis.semantic-basis",
        AnalysisSemanticBasisBodyV0(
            _family_declaration_ref(
                ANALYSIS_TRANSPORT_PROFILE,
                "adaptive-knowledge-extraction-at-fixed-length-q-lt-n",
                owner_profile=ANALYSIS_PROPERTY_PROFILE,
            ),
            context.question_id,
            _native_rule_source(
                ANALYSIS_TRANSPORT_PROFILE,
                ANALYSIS_TRANSPORT_PROFILE,
                "dependent-family-member-specialization",
                k1.DatumRecord(
                    (
                        (0, _id_datum(predecessors[0][3].proposition_id)),
                        (1, question_context[3]),
                        (2, question_context[4]),
                    )
                ),
            ),
            k1.DatumSeq(
                (
                    *_exact_hypothesis_node_requirements(
                        context.inherited_hypothesis_context_id,
                        hypothesis_context.nodes,
                    ).values,
                    *capability_requirements,
                )
            ),
            complete_read_purpose_requirements(concrete_manifest_ids=concrete_reads),
            _conclusion_schema_ref(
                ANALYSIS_TRANSPORT_PROFILE,
                ANALYSIS_TRANSPORT_PROFILE,
                "fixed-member-knowledge-conclusion-v0",
            ),
            k1.DatumRecord(
                (
                    (
                        0,
                        _embedded_component_datum(
                            transform_id, "analysis.quantitative-transform"
                        ),
                    ),
                    (1, conclusion_value),
                )
            ),
        ),
    )
    logical_index = _formed_analysis_body(
        context.exact_subjects[1], "analysis.logical-nat-literal"
    ).value
    policy = _analysis_operation_policy_id(
        context.proposition_id, (), profile=context.semantic_profile
    )
    support = _qualification_fixed_support_id(
        context,
        basis,
        hypothesis_context,
        concrete_reads,
        predecessors,
    )
    return _QualificationExpectation(
        basis,
        support,
        k1.DatumRecord(
            (
                (0, _id_datum(context.exact_subjects[0])),
                (1, k1.Nat(logical_index)),
                (2, k1.DatumVariant(1, concrete_body)),
                (3, conclusion_value),
            )
        ),
        k1.DatumRecord(
            (
                (
                    0,
                    _embedded_component_datum(
                        transform_id, "analysis.quantitative-transform"
                    ),
                ),
                (
                    1,
                    k1.DatumSeq(
                        tuple(
                            _id_datum(item, "analysis.quantitative-formula")
                            for item in formula_ids
                        )
                    ),
                ),
            )
        ),
        policy,
        _qualification_policy_closure(predecessors),
    )


def _require_exact_question_constructor(
    law: _QualificationLawSpec,
    context: QualificationSubjectContext,
) -> None:
    question_context = context.question_context
    if (
        type(question_context) is not k1.DatumVariant
        or question_context.case != law.exact_context_case
    ):
        raise AuthorityError("qualification question context has the wrong closed case")

    expected_proposition: object | None = None
    if law.qualification_label == "finite-special-soundness-result":
        expected_proposition = analysis_proposition_id(_SCHNORR_PINNED_PROPOSITION)
    elif law.qualification_label == "finite-cover-certificate-result":
        expected_proposition = finite_cover_certificate_proposition_id(
            _SCHNORR_PINNED_SOURCE,
            _SCHNORR_PINNED_PROFILE,
            _certificate_kind_from_context(context),
        )
    elif law.qualification_label == "finite-fixed-extractor-universal-result":
        expected_proposition = fixed_extractor_proposition_id(
            _SCHNORR_PINNED_SOURCE, _SCHNORR_PINNED_PROFILE
        )
    elif law.qualification_label == "conditional-assumed-external-all-n":
        family = _qualification_family(law, context)
        expected_proposition = family_source_property_proposition_id(
            family,
            _family_source_hypotheses_for_qualification(family),
        )
    elif law.qualification_label == "conditional-assumed-theorem-truth":
        expected_proposition = theorem_truth_proposition_id(_AFK_GLOBAL_THEOREM_SCHEMA)
    elif law.qualification_label == "afk-family-applicability-result":
        family = _qualification_family(law, context)
        candidate = derive_family_applicability_input(
            _AFK_GLOBAL_THEOREM_SCHEMA, family
        )
        expected_proposition = family_applicability_proposition_id(family, candidate)
    elif law.qualification_label == "afk-family-transport-result":
        family = _qualification_family(law, context)
        expected_proposition = family_target_property_proposition_id(
            family,
            _family_transport_hypotheses_for_qualification(family),
        )
    if (
        expected_proposition is not None
        and context.proposition_id != expected_proposition
    ):
        raise AuthorityError("qualification proposition is not its exact constructor")

    payload = context.question_payload
    if type(payload) is not k1.DatumRecord:
        raise AuthorityError("qualification question payload is not one exact record")
    payload_fields = dict(payload.fields)
    if (
        law.qualification_label == "family-instance-correspondence-result"
        or law.qualification_label == "afk-family-instance-correspondence-result"
    ):
        if tuple(payload_fields) != tuple(range(10)):
            raise AuthorityError("family correspondence payload is incomplete")
        if (
            _id_datum(context.exact_subjects[0]) != payload_fields[0]
            or _id_datum(context.exact_subjects[1]) != payload_fields[1]
            or _id_datum(context.exact_subjects[2]) != payload_fields[3]
            or context.exact_subjects[3]
            != _qualification_normalization_challenge_domain_id(payload_fields[7])
            or context.exact_subjects[4]
            != _qualification_embedded_fixed_setup_id(payload_fields[5])
        ):
            raise AuthorityError(
                "family correspondence challenge domain or fixed setup is detached"
            )
    elif law.qualification_label == "afk-member-specialization-result":
        if tuple(payload_fields) != (0, 1) or payload_fields[1] != k1.Symbol(
            "exact-fixed-member-specialization"
        ):
            raise AuthorityError("fixed-member question payload is incomplete")
        context_fields = dict(question_context.payload.fields)
        if (
            tuple(context_fields) != (0, 1, 2, 3, 4)
            or _id_datum(context.exact_subjects[0]) != context_fields[0]
            or _id_datum(context.exact_subjects[1]) != context_fields[1]
            or analysis_domain_body_v0(
                "analysis.native-subject-projection",
                _formed_analysis_body(
                    context.exact_subjects[2], "analysis.native-subject-projection"
                ),
            )
            != context_fields[2]
            or context.exact_subjects[3]
            != _qualification_normalization_challenge_domain_id(context_fields[4])
        ):
            raise AuthorityError("fixed-member question context is detached")


def _require_exact_basis_constructor(
    law: _QualificationLawSpec,
    context: QualificationSubjectContext,
    expectation: _QualificationExpectation,
) -> None:
    basis_profile = _formed_analysis_profile(
        context.semantic_basis_id, "analysis.semantic-basis"
    )
    _, conclusion_label, _ = _resolved_profile_declaration(
        basis_profile,
        context.semantic_basis.conclusion_schema,
        "analysis.semantic-law",
    )
    if conclusion_label != law.conclusion_schema_label:
        raise AuthorityError("qualification semantic basis has another conclusion ABI")
    rule_source = context.semantic_basis.rule_source
    if law.native_rule_label is None:
        if type(rule_source) is not k1.DatumVariant or rule_source.case != 1:
            raise AuthorityError("qualification needs one exact imported-theorem rule")
        expected_schema = AFK_V2_THM4_CLASSICAL_ROM
        if rule_source.payload != _id_datum(expected_schema, "analysis.theorem-schema"):
            raise AuthorityError("qualification imported another theorem schema")
    else:
        if (
            type(rule_source) is not k1.DatumVariant
            or rule_source.case != 0
            or type(rule_source.payload) is not k1.DatumRecord
        ):
            raise AuthorityError(
                "qualification needs one exact native-rule constructor"
            )
        rule_fields = dict(rule_source.payload.fields)
        if tuple(rule_fields) != (0, 1):
            raise AuthorityError("qualification native-rule payload is incomplete")
        _, rule_label, _ = _resolved_profile_declaration(
            basis_profile,
            rule_fields[0],
            "analysis.native-rule",
        )
        if rule_label != law.native_rule_label:
            raise AuthorityError(
                "qualification semantic basis uses another native rule"
            )
    if (
        type(context.semantic_basis.exact_premise_schemas) is not k1.DatumSeq
        or type(context.semantic_basis.typed_transform_program) is not k1.DatumRecord
    ):
        raise AuthorityError("qualification semantic basis has an incomplete exact ABI")

    if context.semantic_basis_id != expectation.basis_id:
        raise AuthorityError(
            "qualification semantic basis is not its exact constructor"
        )


def _support_binding_goals(value: object) -> tuple[object, ...]:
    if type(value) is not k1.DatumSeq:
        raise AuthorityError("qualification support binding catalog is not a sequence")
    goals: list[object] = []
    for ordinal, entry in enumerate(value.values):
        if type(entry) is not k1.DatumRecord:
            raise AuthorityError("qualification support binding is not a record")
        fields = dict(entry.fields)
        if tuple(fields) != (0, 1) or fields[0] != k1.Nat(ordinal):
            raise AuthorityError("qualification support binding ordinal is not exact")
        payload = fields[1]
        if type(payload) is not k1.DatumRecord:
            raise AuthorityError("qualification support binding payload is malformed")
        payload_fields = dict(payload.fields)
        if tuple(payload_fields) != (0, 1, 2):
            raise AuthorityError("qualification support binding payload is incomplete")
        goals.append(payload_fields[0])
    return tuple(goals)


def _require_exact_support_and_validation(
    law: _QualificationLawSpec,
    context: QualificationSubjectContext,
    expectation: _QualificationExpectation,
) -> None:
    support = context.support
    for value in (
        support.non_hypothesis_premise_bindings,
        support.established_hypothesis_node_bindings,
        support.assumed_hypothesis_node_bindings,
        support.source_support_bindings,
    ):
        if type(value) is not k1.DatumSeq:
            raise AuthorityError("qualification support has a non-sequence ABI field")
    if support.established_hypothesis_node_bindings.values:
        raise AuthorityError(
            "active qualification has an undeclared established binding"
        )
    if (
        len(support.non_hypothesis_premise_bindings.values)
        != law.exact_non_hypothesis_binding_count
        or len(support.source_support_bindings.values)
        != law.exact_source_support_binding_count
    ):
        raise AuthorityError("qualification support constructor has the wrong arity")
    actual_goals = _support_binding_goals(support.assumed_hypothesis_node_bindings)
    hypothesis_context = _formed_analysis_body(
        context.inherited_hypothesis_context_id,
        "analysis.hypothesis-context",
    )
    expected_goals = tuple(_id_datum(node.goal_id) for node in hypothesis_context.nodes)
    if law.assumed_binding_mode == "self-theorem-assumption":
        expected_goals = (_id_datum(context.goal_id),)
    if actual_goals != expected_goals:
        raise AuthorityError(
            "qualification support does not cover its exact hypotheses"
        )
    expected_validation = (
        finite_cover_validation_basis_id()
        if law.qualification_label
        in (
            "finite-cover-certificate-result",
            "finite-fixed-extractor-universal-result",
        )
        else analysis_validation_basis_id((), profile=context.semantic_profile)
    )
    if context.validation_basis_id != expected_validation:
        raise AuthorityError(
            "qualification validation basis is not its exact constructor"
        )
    if (
        expectation.support_id is not None
        and context.support_id != expectation.support_id
    ):
        raise AuthorityError("qualification support is not its exact constructor")


def _require_exact_judgment_constructor(
    law: _QualificationLawSpec,
    context: QualificationSubjectContext,
    qualification: object,
    expectation: _QualificationExpectation,
) -> None:
    judgment = context.judgment_record
    if law.requires_judgment_record != (judgment is not None):
        raise AuthorityError("qualification result has the wrong judgment carrier")
    if judgment is None:
        if (
            context.outcome_kind is not AttemptKind.AFFIRMATIVE
            or context.result_id != expectation.external_result_id
        ):
            raise AuthorityError(
                "external qualification result preimage was substituted"
            )
        return
    if judgment.polarity != k1.DatumVariant(
        0, k1.UNIT
    ) or judgment.qualification != analysis_profile_declaration_ref_body(qualification):
        raise AuthorityError("qualification judgment polarity or law was substituted")
    if (
        judgment.exact_family_conclusion != expectation.conclusion
        or judgment.typed_quantitative_result != expectation.quantitative
        or judgment.operation_policy_id
        != _id_datum(expectation.operation_policy_id, "analysis.operation-policy")
        or judgment.derived_source_policy_dependency_closure
        != expectation.policy_closure
    ):
        raise AuthorityError("qualification judgment result ABI was substituted")


def _require_actual_qualification(
    context: QualificationSubjectContext,
    qualification: object,
) -> None:
    _, label, _ = _resolved_profile_declaration(
        context.semantic_profile,
        qualification,
        "analysis.qualification",
    )
    law = _qualification_law(label)
    subject_kinds = tuple(item.subject_kind for item in context.exact_subjects)
    if (
        context.family_label != law.exact_family_label
        or subject_kinds != law.exact_subject_kinds
    ):
        raise AuthorityError(
            "actual qualification rejects this family, subject, or context"
        )
    _require_exact_question_constructor(law, context)
    expectation = _exact_qualification_expectation(law, context, qualification)
    _require_exact_basis_constructor(law, context, expectation)
    _require_exact_support_and_validation(law, context, expectation)
    _require_exact_judgment_constructor(law, context, qualification, expectation)


def _require_qualification_requirement(
    context: QualificationSubjectContext,
    actual_qualification: object,
    requirement: object,
) -> _QualificationLawSpec:
    _, requirement_label, _ = _resolved_profile_declaration(
        context.semantic_profile,
        requirement,
        "analysis.qualification-requirement",
    )
    if requirement_label != "exact-inherited-conditional":
        raise AuthorityError("qualification requirement has no executable law")
    _, actual_label, _ = _resolved_profile_declaration(
        context.semantic_profile,
        actual_qualification,
        "analysis.qualification",
    )
    law = _qualification_law(actual_label)
    subject_kinds = tuple(item.subject_kind for item in context.exact_subjects)
    if (
        context.family_label != law.exact_family_label
        or subject_kinds != law.exact_subject_kinds
    ):
        raise AuthorityError("exact-inherited requirement rejects this result subject")
    # This is a separate requirement law, not an alias for the actual
    # qualification declaration.  It independently reconstructs the same
    # closed candidate chain before permitting inheritance.
    _require_exact_question_constructor(law, context)
    expectation = _exact_qualification_expectation(law, context, actual_qualification)
    _require_exact_basis_constructor(law, context, expectation)
    _require_exact_support_and_validation(law, context, expectation)
    _require_exact_judgment_constructor(law, context, actual_qualification, expectation)
    return law


def _checked_result_qualification_context(
    checked_result_coordinate: object,
) -> tuple[QualificationSubjectContext, object]:
    body = _formed_analysis_body(
        checked_result_coordinate,
        "analysis.checked-result-coordinate",
    )
    profile = _formed_analysis_profile(
        checked_result_coordinate,
        "analysis.checked-result-coordinate",
    )
    judgment: AnalysisJudgmentRecordBodyV0 | None = None
    if getattr(body.result_id, "subject_kind", None) == "analysis.judgment-record":
        judgment = _formed_analysis_body(body.result_id, "analysis.judgment-record")
        if (
            judgment.proposition_id != _id_datum(body.proposition_id)
            or judgment.semantic_basis_id != _id_datum(body.semantic_basis_id)
            or judgment.support_coordinate != _id_datum(body.support_id)
            or judgment.validation_basis_id != _id_datum(body.validation_basis_id)
            or judgment.qualification
            != analysis_profile_declaration_ref_body(body.qualification)
        ):
            raise AuthorityError(
                "checked-result coordinate is detached from its judgment"
            )
    context = _derive_qualification_subject_context(
        semantic_profile=profile,
        proposition_id=body.proposition_id,
        semantic_basis_id=body.semantic_basis_id,
        support_id=body.support_id,
        validation_basis_id=body.validation_basis_id,
        judgment_record=judgment,
        result_id=body.result_id,
        outcome_kind=AttemptKind(body.outcome_kind.value),
    )
    _require_actual_qualification(context, body.qualification)
    return context, body.qualification


def checked_result_coordinate_id(result: InertCheckedResult) -> object:
    if (
        type(result) is not InertCheckedResult
        or type(result.outcome_kind) is not AttemptKind
        or type(result.semantic_profile) is not k1.SemanticLanguageProfile
    ):
        raise AuthorityError("checked-result coordinate has the wrong exact shape")
    if result.outcome_kind not in (AttemptKind.AFFIRMATIVE, AttemptKind.NEGATIVE):
        raise AuthorityError("only a completed semantic result has an inert coordinate")
    judgment: AnalysisJudgmentRecordBodyV0 | None = None
    if getattr(result.result_id, "subject_kind", None) == "analysis.judgment-record":
        judgment = _formed_analysis_body(result.result_id, "analysis.judgment-record")
        if (
            judgment.proposition_id != _id_datum(result.proposition_id)
            or judgment.semantic_basis_id != _id_datum(result.semantic_basis_id)
            or judgment.support_coordinate != _id_datum(result.support_id)
            or judgment.validation_basis_id != _id_datum(result.validation_basis_id)
            or judgment.qualification
            != analysis_profile_declaration_ref_body(result.qualification_id)
        ):
            raise AuthorityError("inert checked result is detached from its judgment")
    context = _derive_qualification_subject_context(
        semantic_profile=result.semantic_profile,
        proposition_id=result.proposition_id,
        semantic_basis_id=result.semantic_basis_id,
        support_id=result.support_id,
        validation_basis_id=result.validation_basis_id,
        judgment_record=judgment,
        result_id=result.result_id,
        outcome_kind=result.outcome_kind,
    )
    _require_actual_qualification(context, result.qualification_id)
    return _form_analysis_profiled_content_id(
        "analysis.checked-result-coordinate",
        AnalysisCheckedResultCoordinateBodyV0(
            result.result_id,
            result.proposition_id,
            result.semantic_basis_id,
            result.support_id,
            result.validation_basis_id,
            result.qualification_id,
            k1.Symbol(result.outcome_kind.value),
        ),
        result.semantic_profile,
    )


def analysis_capability_requirement_payload_id(
    requirement: AnalysisCapabilityRequirementPayload,
) -> object:
    if type(requirement) is not AnalysisCapabilityRequirementPayload:
        raise AuthorityError(
            "Analysis capability-requirement payload has the wrong exact shape"
        )
    if type(requirement.semantic_profile) is not k1.SemanticLanguageProfile:
        raise AuthorityError("capability requirement needs one exact profile")
    return _form_analysis_profiled_content_id(
        "analysis.capability-requirement-payload",
        AnalysisCapabilityRequirementPayloadBodyV0(
            requirement.proposition_id,
            requirement.qualification_id,
            requirement.named_consumer,
            requirement.typed_purpose,
        ),
        requirement.semantic_profile,
    )


@dataclass(frozen=True)
class _AnalysisUseContractCase:
    qualification_label: str
    consumer_label: str
    purpose_label: str
    policy_kind: str
    external_operation: str | None = None


_ANALYSIS_USE_CONTRACT_CASES = (
    _AnalysisUseContractCase(
        "finite-special-soundness-result",
        "finite-special-soundness",
        "finite-special-soundness",
        "analysis-operation-policy",
    ),
    _AnalysisUseContractCase(
        "conditional-assumed-external-all-n",
        "afk-family-property-transport",
        "all-n-two-special-soundness-source",
        "external-owner-policy",
        "use-assumed-all-n-source-result",
    ),
    _AnalysisUseContractCase(
        "conditional-assumed-theorem-truth",
        "afk-family-property-transport",
        "selected-afk-theorem-truth",
        "external-owner-policy",
        "use-selected-theorem-truth-treatment",
    ),
    _AnalysisUseContractCase(
        "afk-family-applicability-result",
        "afk-family-property-transport",
        "exact-family-applicability",
        "analysis-operation-policy",
    ),
    _AnalysisUseContractCase(
        "afk-family-transport-result",
        "afk-member-specialization",
        "afk-family-target-specialization",
        "analysis-operation-policy",
    ),
    _AnalysisUseContractCase(
        "afk-family-instance-correspondence-result",
        "afk-member-specialization",
        "afk-exact-family-member-specialization",
        "analysis-operation-policy",
    ),
)


def _operation_policy_permits_exact_use(
    policy_id: object,
    named_consumer: object,
    typed_purpose: object,
) -> None:
    policy = _formed_analysis_body(policy_id, "analysis.operation-policy")
    permissions = policy.named_consumer_and_typed_purpose_permissions
    if type(permissions) is not k1.DatumSeq:
        raise AuthorityError("operation policy has no finite permission table")
    consumer_body = analysis_profile_declaration_ref_body(named_consumer)
    purpose_body = analysis_profile_declaration_ref_body(typed_purpose)
    matches = []
    for entry in permissions.values:
        if type(entry) is not k1.DatumRecord:
            raise AuthorityError("operation-policy permission is malformed")
        fields = dict(entry.fields)
        if tuple(fields) != (0, 1) or type(fields[1]) is not k1.DatumSeq:
            raise AuthorityError("operation-policy permission has the wrong ABI")
        if fields[0] == consumer_body and purpose_body in fields[1].values:
            matches.append(entry)
    if len(matches) != 1:
        raise AuthorityError("operation policy does not permit this exact typed use")


def _require_exact_use_contract(
    *,
    law: _QualificationLawSpec,
    context: QualificationSubjectContext,
    requirement: AnalysisCapabilityRequirementPayload,
    binding: AnalysisSourceAuthorityContract,
    immediate: tuple[object, ...],
) -> None:
    _, consumer_label, _ = _resolved_profile_declaration(
        context.semantic_profile,
        requirement.named_consumer,
        "analysis.named-consumer",
    )
    _, purpose_label, _ = _resolved_profile_declaration(
        context.semantic_profile,
        requirement.typed_purpose,
        "analysis.typed-purpose",
    )
    matches = tuple(
        case
        for case in _ANALYSIS_USE_CONTRACT_CASES
        if (
            case.qualification_label == law.qualification_label
            and case.consumer_label == consumer_label
            and case.purpose_label == purpose_label
        )
    )
    if len(matches) != 1:
        raise AuthorityError("result qualification has no exact consumer/use contract")
    case = matches[0]
    if case.policy_kind == "analysis-operation-policy":
        judgment = context.judgment_record
        if judgment is None or judgment.operation_policy_id not in tuple(
            _id_datum(item, "analysis.operation-policy") for item in immediate
        ):
            raise AuthorityError("exact use lacks its immediate operation policy")
        _operation_policy_permits_exact_use(
            judgment.operation_policy_id,
            requirement.named_consumer,
            requirement.typed_purpose,
        )
        return
    if case.policy_kind != "external-owner-policy" or case.external_operation is None:
        raise AuthorityError("exact use contract has an unknown policy constructor")
    expected = _assumed_external_operation_policy_id(
        binding.owner_id,
        case.external_operation,
    )
    if expected not in immediate:
        raise AuthorityError("external result lacks its exact owner operation policy")


def analysis_source_authority_contract_id(
    binding: AnalysisSourceAuthorityContract,
) -> object:
    if type(binding) is not AnalysisSourceAuthorityContract:
        raise AuthorityError("Analysis source-authority contract has the wrong shape")
    immediate = _canonical_identifier_set(
        binding.immediate_policy_ids, what="immediate source-policy dependency set"
    )
    transitive = _canonical_identifier_set(
        binding.transitive_policy_ids, what="transitive source-policy dependency set"
    )
    if (
        immediate != binding.immediate_policy_ids
        or transitive != binding.transitive_policy_ids
    ):
        raise AuthorityError("source-policy dependencies are not canonical")
    if set(immediate) & set(transitive):
        raise AuthorityError(
            "immediate and transitive source-policy dependencies overlap"
        )
    if type(binding.semantic_profile) is not k1.SemanticLanguageProfile:
        raise AuthorityError("source-authority contract needs one exact profile")
    context, actual_qualification = _checked_result_qualification_context(
        binding.checked_result_coordinate_id
    )
    requirement = binding.capability_requirement
    if (
        requirement.semantic_profile != binding.semantic_profile
        or requirement.proposition_id != context.proposition_id
    ):
        raise AuthorityError("authority requirement names another result subject")
    law = _require_qualification_requirement(
        context,
        actual_qualification,
        requirement.qualification_id,
    )
    _require_exact_use_contract(
        law=law,
        context=context,
        requirement=requirement,
        binding=binding,
        immediate=immediate,
    )
    return _form_analysis_profiled_content_id(
        "analysis.source-authority-contract",
        AnalysisSourceAuthorityContractBodyV0(
            binding.owner_id,
            binding.checked_result_coordinate_id,
            analysis_capability_requirement_payload_id(binding.capability_requirement),
            immediate,
            transitive,
        ),
        binding.semantic_profile,
    )


def _binding_policy_closure_id(binding: AnalysisSourceAuthorityContract) -> object:
    dependencies = _canonical_identifier_set(
        (
            *binding.immediate_policy_ids,
            *binding.transitive_policy_ids,
        ),
        what="owner policy closure",
    )
    return _form_analysis_profiled_content_id(
        "analysis.owner-policy-closure",
        AnalysisOwnerPolicyClosureBodyV0(
            binding.owner_id,
            dependencies,
            analysis_profile_declaration_ref_body(
                analysis_profile_declaration_ref(
                    binding.semantic_profile,
                    ANALYSIS_KERNEL_PROFILE,
                    "analysis.semantic-law",
                    "derived-used-policy-closure-v0",
                )
            ),
        ),
        binding.semantic_profile,
    )


def k1_portable_source_authority_binding(
    binding: AnalysisSourceAuthorityContract,
) -> object:
    """Deterministically embed the Analysis contract in Foundation's common envelope."""

    contract_id = analysis_source_authority_contract_id(binding)
    if len(binding.immediate_policy_ids) != 1:
        raise AuthorityError(
            "the bounded Analysis authority contract needs one owner policy"
        )
    requirement = k1.OwnerCapabilityRequirement(
        k1.Symbol("analysis"),
        k1.Symbol("checked-result-use"),
        analysis_capability_requirement_payload_id(binding.capability_requirement),
    )
    envelope = k1.PortableSourceAuthorityBinding(
        k1.Symbol("analysis"),
        k1.Symbol("checked-result-use"),
        binding.checked_result_coordinate_id,
        contract_id,
        k1.BoundOwnerOperationPolicy(binding.immediate_policy_ids[0]),
        _binding_policy_closure_id(binding),
        requirement,
    )
    try:
        k1.portable_source_authority_binding_body(envelope)
    except (k1.ModelError, k1.CanonicalError) as error:
        raise AuthorityError(str(error)) from error
    return envelope


def portable_source_authority_binding_id(
    binding: AnalysisSourceAuthorityContract,
) -> object:
    envelope = k1_portable_source_authority_binding(binding)
    return _form_analysis_profiled_content_id(
        "analysis.portable-source-authority-binding",
        AnalysisPortableSourceAuthorityBindingBodyV0(envelope),
        binding.semantic_profile,
    )


def derive_source_policy_closure(
    bindings: Iterable[AnalysisSourceAuthorityContract],
) -> tuple[object, ...]:
    """Derive, rather than accept, the aggregate closure of exact-used sources."""

    dependencies: dict[bytes, object] = {}
    for binding in bindings:
        portable_source_authority_binding_id(binding)
        for dependency in (
            *binding.immediate_policy_ids,
            *binding.transitive_policy_ids,
        ):
            dependencies.setdefault(dependency.internal_reference(), dependency)
    return _canonical_identifier_set(
        dependencies.values(), what="derived source-policy closure"
    )


_ANALYSIS_CONSUMER_DECLARATION_OWNERS = {
    "pir-analysis-source-view": lambda: ANALYSIS_PROPERTY_PROFILE,
    "finite-special-soundness": lambda: ANALYSIS_PROPERTY_PROFILE,
    "finite-fixed-extractor": lambda: ANALYSIS_PROPERTY_PROFILE,
    "afk-family-property-transport": lambda: ANALYSIS_TRANSPORT_PROFILE,
    "afk-member-specialization": lambda: ANALYSIS_TRANSPORT_PROFILE,
}

_ANALYSIS_PURPOSE_DECLARATION_OWNERS = {
    "fresh-public-setup-view": lambda: ANALYSIS_PROPERTY_PROFILE,
    "fiat-shamir-public-setup-view": lambda: ANALYSIS_PROPERTY_PROFILE,
    "fresh-execution-view": lambda: ANALYSIS_PROPERTY_PROFILE,
    "fiat-shamir-execution-view": lambda: ANALYSIS_PROPERTY_PROFILE,
    "fiat-shamir-fs-construction-view": lambda: ANALYSIS_PROPERTY_PROFILE,
    "core-public-coin-view": lambda: ANALYSIS_PROPERTY_PROFILE,
    "transcript-declaration-view": lambda: ANALYSIS_PROPERTY_PROFILE,
    "schnorr-relation-definition-view": lambda: ANALYSIS_PROPERTY_PROFILE,
    "finite-special-soundness": lambda: ANALYSIS_PROPERTY_PROFILE,
    "fixed-extractor-universal-correctness": lambda: ANALYSIS_PROPERTY_PROFILE,
    "exact-family-applicability": lambda: ANALYSIS_TRANSPORT_PROFILE,
    "all-n-two-special-soundness-source": lambda: ANALYSIS_TRANSPORT_PROFILE,
    "selected-afk-theorem-truth": lambda: ANALYSIS_TRANSPORT_PROFILE,
    "exact-family-knowledge-transport": lambda: ANALYSIS_TRANSPORT_PROFILE,
    "afk-family-target-specialization": lambda: ANALYSIS_TRANSPORT_PROFILE,
    "afk-exact-family-member-specialization": (lambda: ANALYSIS_TRANSPORT_PROFILE),
}


def _analysis_intake_id(
    subject_kind: str,
    declaration: object,
    selected_profile: object,
) -> object:
    if subject_kind == "analysis.consumer":
        body = AnalysisConsumerIntakeBodyV0(declaration)
    elif subject_kind == "analysis.use-purpose":
        body = AnalysisUsePurposeIntakeBodyV0(declaration)
    else:
        raise AuthorityError("unknown Analysis intake-coordinate kind")
    return _form_analysis_profiled_content_id(subject_kind, body, selected_profile)


def analysis_consumer_intake_id(
    label: str, *, selected_profile: object | None = None
) -> object:
    """Nominalize one exact consumer declaration only at a foreign-owner seam."""

    owner_factory = _ANALYSIS_CONSUMER_DECLARATION_OWNERS.get(label)
    owner = None if owner_factory is None else owner_factory()
    if owner is None:
        raise AuthorityError("unknown Analysis consumer declaration")
    selected = owner if selected_profile is None else selected_profile
    reference = analysis_profile_declaration_ref(
        selected,
        owner,
        "analysis.named-consumer",
        label,
    )
    return _analysis_intake_id("analysis.consumer", reference, selected)


def analysis_use_purpose_intake_id(
    label: str, *, selected_profile: object | None = None
) -> object:
    """Nominalize one exact purpose declaration only at a foreign-owner seam."""

    owner_factory = _ANALYSIS_PURPOSE_DECLARATION_OWNERS.get(label)
    owner = None if owner_factory is None else owner_factory()
    if owner is None:
        raise AuthorityError("unknown Analysis purpose declaration")
    selected = owner if selected_profile is None else selected_profile
    reference = analysis_profile_declaration_ref(
        selected,
        owner,
        "analysis.typed-purpose",
        label,
    )
    return _analysis_intake_id("analysis.use-purpose", reference, selected)


def _use_coordinate(
    subject_kind: str,
    label: str,
    *,
    selected_profile: object | None = None,
) -> object:
    if subject_kind == "analysis.consumer":
        return analysis_consumer_intake_id(label, selected_profile=selected_profile)
    if subject_kind == "analysis.use-purpose":
        return analysis_use_purpose_intake_id(label, selected_profile=selected_profile)
    raise AuthorityError("unknown Analysis intake-coordinate kind")


_POLICY_CONTEXT_SUBJECT_KINDS = frozenset(
    {
        "analysis.asymptotic-protocol-family",
        "analysis.challenge-domain",
        "analysis.experiment-profile",
        "analysis.fixed-public-setup",
        "analysis.source-profile",
        "analysis.theorem-schema",
    }
)


def _policy_subject_closure(proposition_id: object) -> tuple[object, ...]:
    proposition = _formed_analysis_body(proposition_id, "analysis.proposition")
    goal = _formed_analysis_body(proposition.goal_id, "analysis.goal")
    question = _formed_analysis_body(goal.question_id, "analysis.question")
    subjects: dict[bytes, object] = {
        item.internal_reference(): item for item in question.exact_subjects
    }

    def visit(value: object) -> None:
        if type(value) is k1.TypedContentId:
            key = value.internal_reference()
        elif type(value) is k1.BytesValue:
            key = value.value
        else:
            key = b""
        entry = _ANALYSIS_FORMATION_REGISTRY.get(key)
        if entry is not None and entry[0] in _POLICY_CONTEXT_SUBJECT_KINDS:
            subjects[key] = entry[3]
        if type(value) is k1.DatumRecord:
            for _, child in value.fields:
                visit(child)
        elif type(value) is k1.DatumSeq:
            for child in value.values:
                visit(child)
        elif type(value) is k1.DatumVariant:
            visit(value.payload)
        elif type(value) is tuple:
            for child in value:
                visit(child)

    visit(question.context)
    return _canonical_identifier_set(
        subjects.values(), what="operation-policy subject closure"
    )


def _analysis_operation_policy_id(
    proposition_id: object,
    permissions: tuple[tuple[str, tuple[str, ...]], ...],
    *,
    profile: object,
) -> object:
    proposition_profile = _formed_analysis_profile(
        proposition_id, "analysis.proposition"
    )
    if profile != proposition_profile and _active_analysis_profile_id(
        proposition_profile
    ) not in _analysis_profile_import_closure(profile):
        raise AuthorityError("operation policy is outside its proposition profile cone")
    if type(permissions) is not tuple:
        raise AuthorityError("operation-policy permissions must be one exact tuple")

    permission_entries = []
    seen_consumers: set[bytes] = set()
    for consumer_label, purpose_labels in permissions:
        owner_factory = _ANALYSIS_CONSUMER_DECLARATION_OWNERS.get(consumer_label)
        if owner_factory is None or type(purpose_labels) is not tuple:
            raise AuthorityError("operation policy names an unknown consumer")
        consumer = analysis_profile_declaration_ref(
            profile,
            owner_factory(),
            "analysis.named-consumer",
            consumer_label,
        )
        consumer_body = analysis_profile_declaration_ref_body(consumer)
        consumer_key = k1.encode_datum(consumer_body)
        if consumer_key in seen_consumers:
            raise AuthorityError("operation policy repeats one consumer")
        seen_consumers.add(consumer_key)
        purpose_bodies = []
        for purpose_label in purpose_labels:
            purpose_owner_factory = _ANALYSIS_PURPOSE_DECLARATION_OWNERS.get(
                purpose_label
            )
            if purpose_owner_factory is None:
                raise AuthorityError("operation policy names an unknown purpose")
            purpose_bodies.append(
                analysis_profile_declaration_ref_body(
                    analysis_profile_declaration_ref(
                        profile,
                        purpose_owner_factory(),
                        "analysis.typed-purpose",
                        purpose_label,
                    )
                )
            )
        canonical_purposes = tuple(sorted(set(purpose_bodies), key=k1.encode_datum))
        if canonical_purposes != tuple(purpose_bodies):
            raise AuthorityError("operation-policy purposes are not canonical")
        permission_entries.append(
            k1.DatumRecord(
                (
                    (0, consumer_body),
                    (1, k1.DatumSeq(canonical_purposes)),
                )
            )
        )
    canonical_permissions = tuple(sorted(permission_entries, key=k1.encode_datum))
    if canonical_permissions != tuple(permission_entries):
        raise AuthorityError("operation-policy consumers are not canonical")

    def law(label: str) -> object:
        return analysis_profile_declaration_ref_body(
            analysis_profile_declaration_ref(
                profile,
                ANALYSIS_KERNEL_PROFILE,
                "analysis.semantic-law",
                label,
            )
        )

    return _form_analysis_profiled_content_id(
        "analysis.operation-policy",
        AnalysisOperationPolicyBodyV0(
            k1.DatumSeq(
                tuple(
                    _id_datum(item) for item in _policy_subject_closure(proposition_id)
                )
            ),
            k1.DatumSeq(canonical_permissions),
            law("capability-freshness-v0"),
            law("disclosure-v0"),
            law("unknown-question-v0"),
            law("persistence-v0"),
            law("cold-replay-v0"),
        ),
        profile,
    )


def _assumed_external_operation_policy_id(owner_id: object, operation: str) -> object:
    """Fixture-owned exact policy premise; Analysis does not mint this fact."""

    _id_datum(owner_id)
    return k1.content_id(
        "analysis.external-owner-operation-policy",
        k1.encode_datum(
            k1.DatumRecord(
                (
                    (0, _id_datum(owner_id)),
                    (1, k1.Symbol(_ascii(operation, "external policy operation"))),
                    (2, k1.Symbol("assumed-external-owner-policy")),
                    (3, k1.Symbol("external-owner-authentication-required")),
                )
            )
        ),
        semantic_regime=k1.SEMANTIC_REGIME_ID,
    )


def _make_authority_binding(
    *,
    owner_id: object,
    checked_result: InertCheckedResult,
    consumer_label: str,
    purpose_label: str,
    immediate_policy_ids: Iterable[object],
    transitive_policy_ids: Iterable[object] = (),
) -> AnalysisSourceAuthorityContract:
    consumer_owner_factory = _ANALYSIS_CONSUMER_DECLARATION_OWNERS.get(consumer_label)
    purpose_owner_factory = _ANALYSIS_PURPOSE_DECLARATION_OWNERS.get(purpose_label)
    if consumer_owner_factory is None or purpose_owner_factory is None:
        raise AuthorityError("authority binding names an unknown typed use")
    consumer_owner = consumer_owner_factory()
    purpose_owner = purpose_owner_factory()
    # An owner binding inherits the completed result's exact direct profile.
    # It never remints a P/T result under a later consumer profile.  The active
    # finite constructors assign their typed use declarations to that same
    # semantic owner (or an imported predecessor) before this seam.
    selected_profile = checked_result.semantic_profile
    if selected_profile not in (
        ANALYSIS_PROPERTY_PROFILE,
        ANALYSIS_TRANSPORT_PROFILE,
        ANALYSIS_THEOREM_SOURCE_VALIDATION_PROFILE,
    ):
        raise AuthorityError("checked result has no active Analysis owner profile")
    imported = _analysis_profile_import_closure(selected_profile)
    if any(
        _bundled_semantic_profile_id(owner)
        != _active_analysis_profile_id(selected_profile)
        and _bundled_semantic_profile_id(owner) not in imported
        for owner in (consumer_owner, purpose_owner)
    ):
        raise AuthorityError(
            "typed consumer or purpose is downstream of the result owner"
        )
    requirement_qualification = analysis_profile_declaration_ref(
        selected_profile,
        ANALYSIS_PROPERTY_PROFILE,
        "analysis.qualification-requirement",
        "exact-inherited-conditional",
    )
    requirement = AnalysisCapabilityRequirementPayload(
        checked_result.proposition_id,
        requirement_qualification,
        analysis_profile_declaration_ref(
            selected_profile,
            consumer_owner,
            "analysis.named-consumer",
            consumer_label,
        ),
        analysis_profile_declaration_ref(
            selected_profile,
            purpose_owner,
            "analysis.typed-purpose",
            purpose_label,
        ),
        selected_profile,
    )
    binding = AnalysisSourceAuthorityContract(
        owner_id,
        checked_result_coordinate_id(checked_result),
        requirement,
        _canonical_identifier_set(
            immediate_policy_ids, what="immediate source-policy dependency set"
        ),
        _canonical_identifier_set(
            transitive_policy_ids, what="transitive source-policy dependency set"
        ),
        selected_profile,
    )
    portable_source_authority_binding_id(binding)
    return binding


def _issue_invocation_capability(
    binding: AnalysisSourceAuthorityContract, registry: dict[object, object]
) -> InvocationCapability:
    source_binding = k1_portable_source_authority_binding(binding)
    token = object()
    consumer_id = _analysis_intake_id(
        "analysis.consumer",
        binding.capability_requirement.named_consumer,
        binding.semantic_profile,
    )
    purpose_id = _analysis_intake_id(
        "analysis.use-purpose",
        binding.capability_requirement.typed_purpose,
        binding.semantic_profile,
    )
    capability = InvocationCapability(
        portable_source_authority_binding_id(binding),
        source_binding,
        source_binding.capability_family,
        consumer_id,
        purpose_id,
        token,
    )
    registry[token] = capability
    return capability


def _require_invocation_capability(
    capability: InvocationCapability,
    binding: AnalysisSourceAuthorityContract,
    registry: dict[object, object],
) -> None:
    context, actual_qualification = _checked_result_qualification_context(
        binding.checked_result_coordinate_id
    )
    _require_qualification_requirement(
        context,
        actual_qualification,
        binding.capability_requirement.qualification_id,
    )
    expected_source_binding = k1_portable_source_authority_binding(binding)
    expected_consumer_id = _analysis_intake_id(
        "analysis.consumer",
        binding.capability_requirement.named_consumer,
        binding.semantic_profile,
    )
    expected_purpose_id = _analysis_intake_id(
        "analysis.use-purpose",
        binding.capability_requirement.typed_purpose,
        binding.semantic_profile,
    )
    if (
        type(capability) is not InvocationCapability
        or registry.get(capability._token) is not capability
        or type(capability.source_binding) is not k1.PortableSourceAuthorityBinding
        or capability.source_binding != expected_source_binding
        or capability.authority_binding_id
        != portable_source_authority_binding_id(binding)
        or capability.capability_family != expected_source_binding.capability_family
        or capability.named_consumer_id != expected_consumer_id
        or capability.typed_purpose_id != expected_purpose_id
    ):
        raise AuthorityError("live capability is absent, stale, or binding-mismatched")


# ---------------------------------------------------------------------------
# Exact typed quantitative fragment
# ---------------------------------------------------------------------------


class QuantitativeSort(str, Enum):
    PROBABILITY = "probability"
    SIGNED_PROBABILITY_LOWER_BOUND = "signed-probability-lower-bound"
    QUERY_COUNT_ADVERSARY_RO = "query-count:adversary-ro"
    EXPECTED_COUNT_ADVERSARY_RUNNING_ALGORITHM = (
        "expected-count:adversary-running-algorithm"
    )
    SECURITY_PARAMETER = "security-parameter"


@dataclass(frozen=True)
class QVariable:
    name: str
    sort: QuantitativeSort
    resource_dimension_id: object | None = None
    query_abi_id: object | None = None
    subject_id: object | None = None
    counting_law: str | None = None


@dataclass(frozen=True)
class QNatural:
    value: int
    sort: QuantitativeSort
    resource_dimension_id: object | None = None
    query_abi_id: object | None = None
    subject_id: object | None = None
    counting_law: str | None = None


@dataclass(frozen=True)
class QRational:
    value: Fraction
    sort: QuantitativeSort


@dataclass(frozen=True)
class QSum:
    sort: QuantitativeSort
    terms: tuple["QuantitativeExpression", ...]


@dataclass(frozen=True)
class QScale:
    count: "QuantitativeExpression"
    term: "QuantitativeExpression"
    sort: QuantitativeSort


@dataclass(frozen=True)
class QExtractionLowerBound:
    success: "QuantitativeExpression"
    knowledge_error: "QuantitativeExpression"
    factor: Fraction
    sort: QuantitativeSort = QuantitativeSort.SIGNED_PROBABILITY_LOWER_BOUND


@dataclass(frozen=True)
class QSignedProbabilityDifferenceOverPositivePolynomial:
    success: "QuantitativeExpression"
    knowledge_error: "QuantitativeExpression"
    positive_polynomial_binder: str
    polynomial_argument: "QuantitativeExpression"
    sort: QuantitativeSort = QuantitativeSort.SIGNED_PROBABILITY_LOWER_BOUND


@dataclass(frozen=True)
class QExpectedAdversaryCallsUpperBound:
    query_bound: "QuantitativeExpression"
    offset: int
    resource_dimension_id: object
    actor_algorithm_id: object
    sort: QuantitativeSort = QuantitativeSort.EXPECTED_COUNT_ADVERSARY_RUNNING_ALGORITHM


@dataclass(frozen=True)
class QEventProbability:
    experiment_body_id: object
    experiment_side: str
    event_id: object
    projection: tuple[str, ...]
    dependent_parameters: tuple[tuple[str, str], ...]
    query_resource_dimension_id: object
    query_abi_id: object
    subject_id: object
    query_counting_law: str
    sort: QuantitativeSort = QuantitativeSort.PROBABILITY


QuantitativeExpression = (
    QVariable
    | QNatural
    | QRational
    | QSum
    | QScale
    | QExtractionLowerBound
    | QSignedProbabilityDifferenceOverPositivePolynomial
    | QExpectedAdversaryCallsUpperBound
    | QEventProbability
)


def _quant_nodes(expression: QuantitativeExpression) -> int:
    if type(expression) in (QVariable, QNatural, QRational):
        return 1
    if type(expression) is QSum:
        return 1 + sum(_quant_nodes(term) for term in expression.terms)
    if type(expression) is QScale:
        return 1 + _quant_nodes(expression.count) + _quant_nodes(expression.term)
    if type(expression) is QExtractionLowerBound:
        return (
            1
            + _quant_nodes(expression.success)
            + _quant_nodes(expression.knowledge_error)
        )
    if type(expression) is QSignedProbabilityDifferenceOverPositivePolynomial:
        return (
            1
            + _quant_nodes(expression.success)
            + _quant_nodes(expression.knowledge_error)
            + _quant_nodes(expression.polynomial_argument)
        )
    if type(expression) is QExpectedAdversaryCallsUpperBound:
        return 1 + _quant_nodes(expression.query_bound)
    if type(expression) is QEventProbability:
        return 1
    raise QuantitativeError("unknown quantitative expression constructor")


def admit_quantitative(expression: QuantitativeExpression) -> None:
    if _quant_nodes(expression) > MAX_EXPRESSION_NODES:
        raise QuantitativeError("quantitative expression exceeds its finite bound")
    if type(expression) is QVariable:
        _ascii(expression.name, "quantitative variable")
        if type(expression.sort) is not QuantitativeSort:
            raise QuantitativeError("quantitative variable has an unknown sort")
        if expression.sort is QuantitativeSort.QUERY_COUNT_ADVERSARY_RO:
            _id_datum(expression.resource_dimension_id, "analysis.resource-dimension")
            _id_datum(expression.query_abi_id, "analysis.oracle-query-abi")
            _id_datum(expression.subject_id)
            if expression.counting_law != "all-calls-including-repeats-and-off-image":
                raise QuantitativeError(
                    "query-count variable has a substituted counting law"
                )
        elif any(
            item is not None
            for item in (
                expression.resource_dimension_id,
                expression.query_abi_id,
                expression.subject_id,
                expression.counting_law,
            )
        ):
            raise QuantitativeError(
                "non-query variable cannot carry a query-count scope"
            )
        return
    if type(expression) is QNatural:
        if (
            type(expression.value) is not int
            or expression.value < 0
            or expression.sort
            not in (
                QuantitativeSort.QUERY_COUNT_ADVERSARY_RO,
                QuantitativeSort.EXPECTED_COUNT_ADVERSARY_RUNNING_ALGORITHM,
                QuantitativeSort.SECURITY_PARAMETER,
            )
        ):
            raise QuantitativeError("natural literal has a wrong value or sort")
        if expression.sort is QuantitativeSort.QUERY_COUNT_ADVERSARY_RO:
            _id_datum(expression.resource_dimension_id, "analysis.resource-dimension")
            _id_datum(expression.query_abi_id, "analysis.oracle-query-abi")
            _id_datum(expression.subject_id)
            if expression.counting_law not in (
                "all-calls-including-repeats-and-off-image",
                "no-random-oracle-calls",
            ):
                raise QuantitativeError(
                    "query-count literal has a substituted counting law"
                )
        elif any(
            item is not None
            for item in (
                expression.resource_dimension_id,
                expression.query_abi_id,
                expression.subject_id,
                expression.counting_law,
            )
        ):
            raise QuantitativeError(
                "non-query natural cannot carry a query-count scope"
            )
        return
    if type(expression) is QRational:
        if type(expression.value) is not Fraction:
            raise QuantitativeError("rational literal must use exact Fraction")
        if expression.sort not in (QuantitativeSort.PROBABILITY,):
            raise QuantitativeError("rational literal has a non-rational sort")
        if expression.value < 0:
            raise QuantitativeError("probability-like literal must be nonnegative")
        if expression.sort is QuantitativeSort.PROBABILITY and expression.value > 1:
            raise QuantitativeError("probability value must lie in [0,1]")
        return
    if type(expression) is QSum:
        if type(expression.sort) is not QuantitativeSort or not expression.terms:
            raise QuantitativeError("sum needs one known sort and at least one term")
        for term in expression.terms:
            admit_quantitative(term)
            if term.sort is not expression.sort:
                raise QuantitativeError("sum cannot silently coerce quantitative sorts")
        if expression.sort is QuantitativeSort.QUERY_COUNT_ADVERSARY_RO:
            scopes = {
                (
                    term.resource_dimension_id,
                    term.query_abi_id,
                    term.subject_id,
                    term.counting_law,
                )
                for term in expression.terms
                if type(term) in (QVariable, QNatural)
            }
            if len(scopes) != 1:
                raise QuantitativeError("query-count sum crosses resource scopes")
        return
    if type(expression) is QScale:
        admit_quantitative(expression.count)
        admit_quantitative(expression.term)
        if (
            expression.count.sort is not QuantitativeSort.QUERY_COUNT_ADVERSARY_RO
            or expression.term.sort is not QuantitativeSort.PROBABILITY
            or expression.sort is not expression.term.sort
        ):
            raise QuantitativeError(
                "scale requires QueryCount times one probability-like term"
            )
        return
    if type(expression) is QExtractionLowerBound:
        admit_quantitative(expression.success)
        admit_quantitative(expression.knowledge_error)
        if (
            expression.success.sort is not QuantitativeSort.PROBABILITY
            or expression.knowledge_error.sort is not QuantitativeSort.PROBABILITY
            or type(expression.factor) is not Fraction
            or expression.factor <= 0
            or expression.sort is not QuantitativeSort.SIGNED_PROBABILITY_LOWER_BOUND
        ):
            raise QuantitativeError(
                "extraction lower bound needs two Probability dimensions and a positive exact factor"
            )
        return
    if type(expression) is QSignedProbabilityDifferenceOverPositivePolynomial:
        admit_quantitative(expression.success)
        admit_quantitative(expression.knowledge_error)
        if (
            expression.success.sort is not QuantitativeSort.PROBABILITY
            or expression.knowledge_error.sort is not QuantitativeSort.PROBABILITY
            or expression.sort is not QuantitativeSort.SIGNED_PROBABILITY_LOWER_BOUND
        ):
            raise QuantitativeError(
                "AFK knowledge-success lower bound has wrong probability dimensions"
            )
        if expression.positive_polynomial_binder != "q_KS":
            raise QuantitativeError(
                "AFK divisor must reference the existential q_KS binder"
            )
        admit_quantitative(expression.polynomial_argument)
        if (
            expression.polynomial_argument.sort
            is not QuantitativeSort.SECURITY_PARAMETER
        ):
            raise QuantitativeError(
                "positive-polynomial divisor needs a SecurityParameter argument"
            )
        return
    if type(expression) is QExpectedAdversaryCallsUpperBound:
        admit_quantitative(expression.query_bound)
        if (
            expression.query_bound.sort is not QuantitativeSort.QUERY_COUNT_ADVERSARY_RO
            or type(expression.offset) is not int
            or expression.offset < 0
            or expression.sort
            is not QuantitativeSort.EXPECTED_COUNT_ADVERSARY_RUNNING_ALGORITHM
        ):
            raise QuantitativeError(
                "expected adversary calls need QueryCount input and exact nonnegative offset"
            )
        _id_datum(expression.resource_dimension_id, "analysis.resource-dimension")
        _id_datum(
            expression.actor_algorithm_id,
            "analysis.adversary-running-algorithm",
        )
        return
    if type(expression) is QEventProbability:
        _id_datum(expression.experiment_body_id, "analysis.experiment-body")
        _ascii(expression.experiment_side, "event-probability experiment side")
        _id_datum(expression.event_id, "analysis.event-profile")
        for coordinate in expression.projection:
            _ascii(coordinate, "event-probability projection")
        dependency_names = tuple(name for name, _ in expression.dependent_parameters)
        if len(dependency_names) != len(set(dependency_names)):
            raise QuantitativeError("event-probability parameters must be unique")
        for name, sort_name in expression.dependent_parameters:
            _ascii(name, "event-probability parameter")
            _ascii(sort_name, "event-probability parameter sort")
        _id_datum(
            expression.query_resource_dimension_id,
            "analysis.resource-dimension",
        )
        _id_datum(expression.query_abi_id, "analysis.oracle-query-abi")
        _id_datum(expression.subject_id)
        if expression.query_counting_law != "all-calls-including-repeats-and-off-image":
            raise QuantitativeError(
                "event probability has a substituted query-count law"
            )
        if expression.sort is not QuantitativeSort.PROBABILITY:
            raise QuantitativeError("event probability must have Probability sort")
        return
    raise QuantitativeError("unknown quantitative expression constructor")


def _fraction_body(value: Fraction) -> object:
    return k1.DatumRecord(
        ((0, k1.IntValue(value.numerator)), (1, k1.Nat(value.denominator)))
    )


def quantitative_body(expression: QuantitativeExpression) -> object:
    admit_quantitative(expression)
    if type(expression) is QVariable:
        return k1.DatumVariant(
            0,
            k1.DatumRecord(
                (
                    (0, k1.Symbol(expression.name)),
                    (1, k1.Symbol(expression.sort.value)),
                    (
                        2,
                        _embedded_component_datum(
                            expression.resource_dimension_id,
                            "analysis.resource-dimension",
                        )
                        if expression.resource_dimension_id is not None
                        else k1.DatumVariant(0, k1.DatumRecord(())),
                    ),
                    (
                        3,
                        _embedded_component_datum(
                            expression.query_abi_id,
                            "analysis.oracle-query-abi",
                        )
                        if expression.query_abi_id is not None
                        else k1.DatumVariant(0, k1.DatumRecord(())),
                    ),
                    (
                        4,
                        _portable_subject_datum(expression.subject_id)
                        if expression.subject_id is not None
                        else k1.DatumVariant(0, k1.DatumRecord(())),
                    ),
                    (
                        5,
                        k1.Symbol(expression.counting_law)
                        if expression.counting_law is not None
                        else k1.DatumVariant(0, k1.DatumRecord(())),
                    ),
                )
            ),
        )
    if type(expression) is QNatural:
        return k1.DatumVariant(
            1,
            k1.DatumRecord(
                (
                    (0, k1.Nat(expression.value)),
                    (1, k1.Symbol(expression.sort.value)),
                    (
                        2,
                        _embedded_component_datum(
                            expression.resource_dimension_id,
                            "analysis.resource-dimension",
                        )
                        if expression.resource_dimension_id is not None
                        else k1.DatumVariant(0, k1.DatumRecord(())),
                    ),
                    (
                        3,
                        _embedded_component_datum(
                            expression.query_abi_id,
                            "analysis.oracle-query-abi",
                        )
                        if expression.query_abi_id is not None
                        else k1.DatumVariant(0, k1.DatumRecord(())),
                    ),
                    (
                        4,
                        _portable_subject_datum(expression.subject_id)
                        if expression.subject_id is not None
                        else k1.DatumVariant(0, k1.DatumRecord(())),
                    ),
                    (
                        5,
                        k1.Symbol(expression.counting_law)
                        if expression.counting_law is not None
                        else k1.DatumVariant(0, k1.DatumRecord(())),
                    ),
                )
            ),
        )
    if type(expression) is QRational:
        return k1.DatumVariant(
            2,
            k1.DatumRecord(
                (
                    (0, _fraction_body(expression.value)),
                    (1, k1.Symbol(expression.sort.value)),
                )
            ),
        )
    if type(expression) is QSum:
        children = tuple(
            sorted(
                (quantitative_body(term) for term in expression.terms),
                key=k1.encode_datum,
            )
        )
        return k1.DatumVariant(
            3,
            k1.DatumRecord(
                ((0, k1.Symbol(expression.sort.value)), (1, k1.DatumSeq(children)))
            ),
        )
    if type(expression) is QScale:
        return k1.DatumVariant(
            4,
            k1.DatumRecord(
                (
                    (0, quantitative_body(expression.count)),
                    (1, quantitative_body(expression.term)),
                    (2, k1.Symbol(expression.sort.value)),
                )
            ),
        )
    if type(expression) is QExtractionLowerBound:
        return k1.DatumVariant(
            5,
            k1.DatumRecord(
                (
                    (0, quantitative_body(expression.success)),
                    (1, quantitative_body(expression.knowledge_error)),
                    (2, _fraction_body(expression.factor)),
                    (3, k1.Symbol(expression.sort.value)),
                )
            ),
        )
    if type(expression) is QSignedProbabilityDifferenceOverPositivePolynomial:
        return k1.DatumVariant(
            6,
            k1.DatumRecord(
                (
                    (0, quantitative_body(expression.success)),
                    (1, quantitative_body(expression.knowledge_error)),
                    (
                        2,
                        k1.Symbol(expression.positive_polynomial_binder),
                    ),
                    (
                        3,
                        quantitative_body(expression.polynomial_argument),
                    ),
                    (4, k1.Symbol(expression.sort.value)),
                )
            ),
        )
    if type(expression) is QExpectedAdversaryCallsUpperBound:
        return k1.DatumVariant(
            7,
            k1.DatumRecord(
                (
                    (0, quantitative_body(expression.query_bound)),
                    (1, k1.Nat(expression.offset)),
                    (2, k1.Symbol("upper-bound")),
                    (3, k1.Symbol(expression.sort.value)),
                    (
                        4,
                        _embedded_component_datum(
                            expression.resource_dimension_id,
                            "analysis.resource-dimension",
                        ),
                    ),
                    (
                        5,
                        _embedded_component_datum(
                            expression.actor_algorithm_id,
                            "analysis.adversary-running-algorithm",
                        ),
                    ),
                )
            ),
        )
    assert type(expression) is QEventProbability
    return k1.DatumVariant(
        8,
        k1.DatumRecord(
            (
                (0, k1.Symbol(expression.experiment_side)),
                (
                    1,
                    _embedded_component_datum(
                        expression.experiment_body_id, "analysis.experiment-body"
                    ),
                ),
                (
                    2,
                    _embedded_component_datum(
                        expression.event_id, "analysis.event-profile"
                    ),
                ),
                (3, _symbol_seq(expression.projection)),
                (
                    4,
                    k1.DatumSeq(
                        tuple(
                            k1.DatumRecord(
                                ((0, k1.Symbol(name)), (1, k1.Symbol(sort_name)))
                            )
                            for name, sort_name in expression.dependent_parameters
                        )
                    ),
                ),
                (5, k1.Symbol(expression.sort.value)),
                (
                    6,
                    _embedded_component_datum(
                        expression.query_resource_dimension_id,
                        "analysis.resource-dimension",
                    ),
                ),
                (
                    7,
                    _embedded_component_datum(
                        expression.query_abi_id, "analysis.oracle-query-abi"
                    ),
                ),
                (8, _portable_subject_datum(expression.subject_id)),
                (9, k1.Symbol(expression.query_counting_law)),
            )
        ),
    )


def quantitative_equal(
    left: QuantitativeExpression, right: QuantitativeExpression
) -> bool:
    return k1.encode_datum(quantitative_body(left)) == k1.encode_datum(
        quantitative_body(right)
    )


def qsum(*terms: QuantitativeExpression) -> QuantitativeExpression:
    if not terms:
        raise QuantitativeError("empty quantitative sum has no inferred sort")
    for term in terms:
        admit_quantitative(term)
    sort = terms[0].sort
    flattened: list[QuantitativeExpression] = []
    for term in terms:
        if term.sort is not sort:
            raise QuantitativeError("sum cannot silently coerce quantitative sorts")
        if type(term) is QSum and term.sort is sort:
            flattened.extend(term.terms)
        else:
            flattened.append(term)
    result = QSum(sort, tuple(flattened))
    admit_quantitative(result)
    return result


def quantitative_variable_sorts(
    expression: QuantitativeExpression,
) -> tuple[tuple[str, str], ...]:
    """Return the exact free-variable typing of one finite expression.

    A name cannot be reused at two sorts.  Formula admission consumes this
    mapping directly; looking only at names would permit a QueryCount to be
    silently declared as a security parameter (or vice versa).
    """

    admit_quantitative(expression)
    if type(expression) is QVariable:
        return ((expression.name, expression.sort.value),)
    if type(expression) in (QNatural, QRational):
        return ()
    if type(expression) is QEventProbability:
        return expression.dependent_parameters
    children: tuple[QuantitativeExpression, ...]
    if type(expression) is QSum:
        children = expression.terms
    elif type(expression) is QScale:
        children = (expression.count, expression.term)
    elif type(expression) in (
        QExtractionLowerBound,
        QSignedProbabilityDifferenceOverPositivePolynomial,
    ):
        children = (expression.success, expression.knowledge_error)
        if type(expression) is QSignedProbabilityDifferenceOverPositivePolynomial:
            children = children + (expression.polynomial_argument,)
    elif type(expression) is QExpectedAdversaryCallsUpperBound:
        children = (expression.query_bound,)
    else:  # pragma: no cover - admission above is exhaustive
        raise QuantitativeError("unknown expression in variable closure")
    result: dict[str, str] = {}
    for child in children:
        for name, sort_name in quantitative_variable_sorts(child):
            prior = result.get(name)
            if prior is not None and prior != sort_name:
                raise QuantitativeError(
                    f"quantitative variable {name!r} is used at incompatible sorts"
                )
            result[name] = sort_name
    if type(expression) is QSignedProbabilityDifferenceOverPositivePolynomial:
        binder = expression.positive_polynomial_binder
        prior = result.get(binder)
        if prior is not None and prior != "positive-polynomial":
            raise QuantitativeError(
                "q_KS binder is reused at an incompatible quantitative sort"
            )
        result[binder] = "positive-polynomial"
    return tuple(sorted(result.items()))


def quantitative_query_scopes(
    expression: QuantitativeExpression,
) -> tuple[tuple[object, object, object, str], ...]:
    """Collect exact QueryCount capability scopes from one expression."""

    admit_quantitative(expression)
    if type(expression) in (QVariable, QNatural):
        if expression.sort is not QuantitativeSort.QUERY_COUNT_ADVERSARY_RO:
            return ()
        assert expression.resource_dimension_id is not None
        assert expression.query_abi_id is not None
        assert expression.subject_id is not None
        assert expression.counting_law is not None
        return (
            (
                expression.resource_dimension_id,
                expression.query_abi_id,
                expression.subject_id,
                expression.counting_law,
            ),
        )
    if type(expression) is QEventProbability:
        return (
            (
                expression.query_resource_dimension_id,
                expression.query_abi_id,
                expression.subject_id,
                expression.query_counting_law,
            ),
        )
    if type(expression) is QRational:
        return ()
    if type(expression) is QSum:
        children = expression.terms
    elif type(expression) is QScale:
        children = (expression.count, expression.term)
    elif type(expression) in (
        QExtractionLowerBound,
        QSignedProbabilityDifferenceOverPositivePolynomial,
    ):
        children = (expression.success, expression.knowledge_error)
        if type(expression) is QSignedProbabilityDifferenceOverPositivePolynomial:
            children += (expression.polynomial_argument,)
    elif type(expression) is QExpectedAdversaryCallsUpperBound:
        children = (expression.query_bound,)
    else:  # pragma: no cover - admission is exhaustive
        raise QuantitativeError("unknown query-scope expression")
    scopes: dict[
        tuple[bytes, bytes, bytes, str], tuple[object, object, object, str]
    ] = {}
    for child in children:
        for dimension, abi, subject, law in quantitative_query_scopes(child):
            key = (
                dimension.internal_reference(),
                abi.internal_reference(),
                subject.internal_reference(),
                law,
            )
            scopes[key] = (dimension, abi, subject, law)
    return tuple(scopes[key] for key in sorted(scopes))


@dataclass(frozen=True)
class QuantitativeFormulaProfile:
    result_sort: QuantitativeSort
    exact_subject_id: object
    parameter_schema: tuple[tuple[str, str], ...]
    parameter_domain_ids: tuple[tuple[str, object], ...]
    implicit_dependencies: tuple[str, ...]
    declared_independence: tuple[str, ...]
    expression: QuantitativeExpression


_FORMULA_PARAMETER_DOMAIN_REGISTRY: dict[
    bytes, tuple[str, str, str, tuple[object, ...]]
] = {}
_FORMULA_RESULT_SORT_REGISTRY: dict[bytes, QuantitativeSort] = {}
_FORMULA_ROLE_REGISTRY: dict[bytes, tuple[str, object]] = {}
_FORMULA_PROFILE_REGISTRY: dict[bytes, QuantitativeFormulaProfile] = {}


def _contains_probability_count_scale(expression: QuantitativeExpression) -> bool:
    if type(expression) is QScale:
        return True
    if type(expression) in (QVariable, QNatural, QRational, QEventProbability):
        return False
    if type(expression) is QSum:
        return any(_contains_probability_count_scale(item) for item in expression.terms)
    if type(expression) is QExpectedAdversaryCallsUpperBound:
        return _contains_probability_count_scale(expression.query_bound)
    if type(expression) in (
        QExtractionLowerBound,
        QSignedProbabilityDifferenceOverPositivePolynomial,
    ):
        return _contains_probability_count_scale(
            expression.success
        ) or _contains_probability_count_scale(expression.knowledge_error)
    return False


def quantitative_formula_id(profile: QuantitativeFormulaProfile) -> object:
    """Give a proof-basis-neutral identity to one closed formula schema."""

    if type(profile) is not QuantitativeFormulaProfile:
        raise QuantitativeError("quantitative formula profile has the wrong shape")
    admit_quantitative(profile.expression)
    _id_datum(profile.exact_subject_id)
    if profile.expression.sort is not profile.result_sort:
        raise QuantitativeError("formula result sort disagrees with its expression")
    parameter_names = tuple(name for name, _ in profile.parameter_schema)
    if parameter_names != tuple(dict.fromkeys(parameter_names)) or any(
        not _ascii(name, "formula parameter") for name in parameter_names
    ):
        raise QuantitativeError("formula parameters must be ordered and unique")
    for _, sort_name in profile.parameter_schema:
        _ascii(sort_name, "formula parameter sort")
    free_typing = dict(quantitative_variable_sorts(profile.expression))
    declared_typing = dict(profile.parameter_schema)
    for name, actual_sort in free_typing.items():
        if declared_typing.get(name) != actual_sort:
            raise QuantitativeError(
                f"formula parameter {name!r} has a substituted quantitative sort"
            )
    domain_names = tuple(name for name, _ in profile.parameter_domain_ids)
    if domain_names != parameter_names:
        raise QuantitativeError(
            "formula parameter domains must cover the exact ordered parameter schema"
        )
    admitted_domains: dict[str, tuple[str, str, str, tuple[object, ...]]] = {}
    for name, domain_id in profile.parameter_domain_ids:
        _id_datum(domain_id, "analysis.formula-parameter-domain")
        record = _FORMULA_PARAMETER_DOMAIN_REGISTRY.get(domain_id.internal_reference())
        if record is None or record[0] != name or record[1] != declared_typing[name]:
            raise QuantitativeError(
                "formula parameter domain lacks exact registered typing authority"
            )
        admitted_domains[name] = record
    free = set(free_typing)
    implicit = set(profile.implicit_dependencies)
    independent = set(profile.declared_independence)
    parameters = set(parameter_names)
    if (
        not free <= parameters
        or not implicit <= parameters
        or free & independent
        or implicit & independent
        or independent != parameters - free - implicit
        or len(profile.implicit_dependencies) != len(implicit)
        or len(profile.declared_independence) != len(independent)
    ):
        raise QuantitativeError(
            "formula dependencies and declared independence do not close"
        )
    if _contains_probability_count_scale(profile.expression):
        q_domain = admitted_domains.get("Q")
        n_domain = admitted_domains.get("N")
        if (
            q_domain is None
            or q_domain[2] != "zero-less-than-or-equal-Q-strictly-less-than-N"
            or n_domain is None
            or n_domain[2] != "family-constant-N-is-8-and-at-least-two"
            or n_domain[3] != (family_definition_id(SELECTED_AFK_FAMILY),)
        ):
            raise QuantitativeError(
                "probability count ratio lacks the exact Q<N and N=8 domains"
            )
    if "Q" in admitted_domains:
        q_domain = admitted_domains["Q"]
        if q_domain[2] != "zero-less-than-or-equal-Q-strictly-less-than-N" or q_domain[
            3
        ] != (
            afk_query_bound_domain_id(8),
            AFK_ADVERSARY_RO_QUERY_DIMENSION_ID,
            afk_query_abi_id(8),
            profile.exact_subject_id,
        ):
            raise QuantitativeError(
                "Q domain detached from its exact subject, ABI, or resource dimension"
            )
        query_scopes = quantitative_query_scopes(profile.expression)
        if query_scopes != (
            (
                AFK_ADVERSARY_RO_QUERY_DIMENSION_ID,
                afk_query_abi_id(8),
                profile.exact_subject_id,
                "all-calls-including-repeats-and-off-image",
            ),
        ):
            raise QuantitativeError(
                "query-count expression detached from its exact capability scope"
            )
    if (
        profile.result_sort
        is QuantitativeSort.EXPECTED_COUNT_ADVERSARY_RUNNING_ALGORITHM
    ):
        if (
            type(profile.expression) is not QExpectedAdversaryCallsUpperBound
            or profile.expression.resource_dimension_id
            != AFK_ADVERSARY_RUNNING_CALL_DIMENSION_ID
            or profile.expression.actor_algorithm_id
            != subject_bound_afk_adversary_running_algorithm_id(
                8, profile.exact_subject_id
            )
        ):
            raise QuantitativeError(
                "expected-call formula detached from its actor or resource dimension"
            )
    identifier = _analysis_id(
        "analysis.quantitative-formula",
        AnalysisQuantitativeFormulaBodyV0(
            k1.Symbol(profile.result_sort.value),
            k1.DatumSeq(
                tuple(
                    k1.DatumRecord(
                        (
                            (0, k1.Nat(ordinal)),
                            (
                                1,
                                k1.DatumRecord(
                                    (
                                        (0, k1.Symbol(sort_name)),
                                        (
                                            1,
                                            _embedded_component_datum(
                                                dict(profile.parameter_domain_ids)[
                                                    parameter_name
                                                ],
                                                "analysis.formula-parameter-domain",
                                            ),
                                        ),
                                    )
                                ),
                            ),
                        )
                    )
                    for ordinal, (parameter_name, sort_name) in enumerate(
                        profile.parameter_schema
                    )
                )
            ),
            k1.DatumSeq(
                tuple(
                    k1.Nat(parameter_names.index(name))
                    for name in profile.declared_independence
                )
            ),
            quantitative_body(profile.expression),
        ),
    )
    key = identifier.internal_reference()
    prior_sort = _FORMULA_RESULT_SORT_REGISTRY.get(key)
    if prior_sort is not None and prior_sort is not profile.result_sort:
        raise QuantitativeError("formula identity was registered at two result sorts")
    _FORMULA_RESULT_SORT_REGISTRY[key] = profile.result_sort
    prior_profile = _FORMULA_PROFILE_REGISTRY.get(key)
    if prior_profile is not None and prior_profile != profile:
        # ``exact_subject_id`` is a host-side formation/checking coordinate,
        # not an extra field of AnalysisQuantitativeFormulaBody.  A genuinely
        # basis-neutral formula (for example the global source error 1/N) may
        # therefore be shared by two subjects.  Its compiled body is already
        # authenticated by the formation registry; retain the first host
        # witness instead of treating this legitimate semantic sharing as an
        # identity collision.
        if (
            _formed_analysis_body(identifier, "analysis.quantitative-formula")
            != _ANALYSIS_FORMATION_REGISTRY[key][2]
        ):  # pragma: no cover - defensive
            raise QuantitativeError("formula identity resolved to two semantic bodies")
    else:
        _FORMULA_PROFILE_REGISTRY[key] = profile
    return identifier


def resource_dimension_id(dimension: "ResourceDimension") -> object:
    if type(dimension) is not ResourceDimension:
        raise QuantitativeError("resource dimension has the wrong shape")
    return _legacy_component_id(
        "analysis.resource-dimension",
        k1.DatumRecord(
            (
                (0, k1.Symbol(_ascii(dimension.name, "resource name"))),
                (1, k1.Symbol(_ascii(dimension.value_sort, "resource sort"))),
                (2, k1.Symbol(_ascii(dimension.scope, "resource scope"))),
                (3, k1.Symbol(_ascii(dimension.aggregation, "resource aggregation"))),
                (4, k1.Symbol(_ascii(dimension.counter_event, "resource event"))),
            )
        ),
    )


@dataclass(frozen=True)
class ExpectedInvocationBound:
    experiment_body_id: object
    counted_algorithm_id: object
    resource_dimension_id: object
    comparator: str
    rhs_formula_id: object


_EXPECTED_INVOCATION_BOUND_REGISTRY: dict[bytes, ExpectedInvocationBound] = {}


def expected_invocation_bound_id(bound: ExpectedInvocationBound) -> object:
    if type(bound) is not ExpectedInvocationBound:
        raise QuantitativeError("expected-invocation bound has the wrong shape")
    _id_datum(bound.experiment_body_id, "analysis.experiment-body")
    _id_datum(
        bound.counted_algorithm_id,
        "analysis.adversary-running-algorithm",
    )
    _id_datum(bound.resource_dimension_id, "analysis.resource-dimension")
    _id_datum(bound.rhs_formula_id, "analysis.quantitative-formula")
    rhs_key = bound.rhs_formula_id.internal_reference()
    rhs_profile = _FORMULA_PROFILE_REGISTRY.get(rhs_key)
    if (
        _FORMULA_RESULT_SORT_REGISTRY.get(rhs_key)
        is not QuantitativeSort.EXPECTED_COUNT_ADVERSARY_RUNNING_ALGORITHM
        or _FORMULA_ROLE_REGISTRY.get(rhs_key, (None, None))[0]
        != "expected-adversary-calls-upper-bound"
        or rhs_profile is None
        or type(rhs_profile.expression) is not QExpectedAdversaryCallsUpperBound
        or rhs_profile.expression.resource_dimension_id != bound.resource_dimension_id
        or rhs_profile.expression.actor_algorithm_id != bound.counted_algorithm_id
        or bound.experiment_body_id
        != subject_bound_experiment_body_id(
            8, rhs_profile.exact_subject_id, "extractor-experiment"
        )
    ):
        raise QuantitativeError(
            "expected-invocation bound is detached from its formula, actor, resource, or experiment"
        )
    if bound.comparator != "less-than-or-equal":
        raise QuantitativeError("expected-invocation bound needs <= orientation")
    identifier = _legacy_component_id(
        "analysis.expected-invocation-bound",
        k1.DatumRecord(
            (
                (0, _id_datum(bound.experiment_body_id, "analysis.experiment-body")),
                (
                    1,
                    _id_datum(
                        bound.counted_algorithm_id,
                        "analysis.adversary-running-algorithm",
                    ),
                ),
                (
                    2,
                    _id_datum(
                        bound.resource_dimension_id, "analysis.resource-dimension"
                    ),
                ),
                (3, k1.Symbol(bound.comparator)),
                (4, _id_datum(bound.rhs_formula_id, "analysis.quantitative-formula")),
            )
        ),
    )
    key = identifier.internal_reference()
    prior = _EXPECTED_INVOCATION_BOUND_REGISTRY.get(key)
    if prior is not None and prior != bound:
        raise QuantitativeError("expected-invocation identity was registered twice")
    _EXPECTED_INVOCATION_BOUND_REGISTRY[key] = bound
    return identifier


# ---------------------------------------------------------------------------
# Source-owned facts and exact finite manifests
# ---------------------------------------------------------------------------


class SourceFactKind(str, Enum):
    CORE = "core"
    PROTOCOL = "protocol"
    CONSTRUCTION = "construction"
    RELATION_BINDING = "relation-binding"
    PLAN_WITNESS_BINDING = "plan-witness-binding"
    RELATION_INSTANCE = "relation-instance"
    STATEMENT_EDGE = "statement-edge"
    CLAIM_EDGE = "claim-edge"
    WITNESS_EDGE = "witness-edge"
    TERMINAL = "terminal"
    VALUE_BRIDGE = "value-bridge"


@dataclass(frozen=True)
class SourceRead:
    kind: SourceFactKind
    owner_id: object
    coordinate: str


@dataclass(frozen=True)
class SourceManifest:
    reads: tuple[SourceRead, ...]


_SOURCE_FACT_KIND_ORDINAL = {
    kind: ordinal for ordinal, kind in enumerate(SourceFactKind)
}


def _source_read_token(read: SourceRead) -> tuple[SourceFactKind, str]:
    """Resolve one bounded source read to a closed owner-coordinate case.

    Display/path strings are accepted only as the finite parser syntax used by
    the Relations fixture adapter.  The portable body contains the resulting enum
    coordinate, never the spelling.
    """

    if type(read) is not SourceRead or type(read.kind) is not SourceFactKind:
        raise SourceIngressError("source read has an unknown exact shape")
    coordinate = _ascii(read.coordinate, "source-read coordinate")
    fixed = {
        (SourceFactKind.CORE, "interactive-core"): "shared",
        (SourceFactKind.PROTOCOL, "fresh"): "fresh",
        (SourceFactKind.PROTOCOL, "fiat-shamir"): "fiat-shamir",
        (SourceFactKind.CONSTRUCTION, "transcript-construction"): "fiat-shamir",
        (SourceFactKind.RELATION_BINDING, "fresh-relation-binding"): "fresh",
        (
            SourceFactKind.RELATION_BINDING,
            "fiat-shamir-relation-binding",
        ): "fiat-shamir",
        (
            SourceFactKind.PLAN_WITNESS_BINDING,
            "fresh-plan-witness-binding",
        ): "fresh",
        (
            SourceFactKind.PLAN_WITNESS_BINDING,
            "fiat-shamir-plan-witness-binding",
        ): "fiat-shamir",
    }
    selected = fixed.get((read.kind, coordinate))
    if selected is not None:
        return read.kind, selected
    # The directional-loss probe predates the portable Fresh/Fresh+FS source
    # profiles.  Its bounded local validator still needs to rederive these
    # exact selected-case coordinates, but they cannot enter either portable
    # profile below: the ``unspecified`` axis deliberately prevents that.
    local_probe = {
        (SourceFactKind.RELATION_BINDING, "protocol-relation-binding"),
        (SourceFactKind.PLAN_WITNESS_BINDING, "plan-witness-binding"),
        (SourceFactKind.RELATION_INSTANCE, "knowledge-instance"),
        (SourceFactKind.TERMINAL, "terminal"),
        (SourceFactKind.VALUE_BRIDGE, "nat-to-bytes-lossy"),
    }
    if (read.kind, coordinate) in local_probe:
        return read.kind, "unspecified"
    edge_suffixes = {
        SourceFactKind.STATEMENT_EDGE: "knowledge-instance:statement:root:statement",
        SourceFactKind.CLAIM_EDGE: "knowledge-instance:initial:knowledge",
        SourceFactKind.WITNESS_EDGE: "secret:secret",
    }
    suffix = edge_suffixes.get(read.kind)
    if suffix is not None:
        for axis in ("fresh", "fiat-shamir"):
            if coordinate == f"{axis}:{suffix}":
                return read.kind, axis
        # A single-axis RelationPropertySource predates the paired owner view.
        # It remains usable for local validation, but cannot form one of the
        # two portable Analysis manifests below.
        if coordinate == suffix:
            return read.kind, "unspecified"
    raise SourceIngressError("source read is outside the closed Analysis slot catalog")


def _source_coordinate_body(read: SourceRead) -> object:
    kind, axis = _source_read_token(read)
    del kind
    cases = {"shared": 0, "fresh": 1, "fiat-shamir": 2, "unspecified": 3}
    return k1.DatumVariant(cases[axis], k1.UNIT)


def _source_read_body(read: SourceRead) -> object:
    _source_read_token(read)
    return k1.DatumRecord(
        (
            (0, k1.Nat(_SOURCE_FACT_KIND_ORDINAL[read.kind])),
            (1, _id_datum(read.owner_id)),
            (2, _source_coordinate_body(read)),
        )
    )


def _source_read_key(read: SourceRead) -> bytes:
    return k1.encode_datum(_source_read_body(read))


def source_manifest(reads: Iterable[SourceRead]) -> SourceManifest:
    result = tuple(sorted(tuple(reads), key=_source_read_key))
    admit_source_manifest(SourceManifest(result))
    return SourceManifest(result)


def admit_source_manifest(manifest: SourceManifest) -> None:
    if type(manifest) is not SourceManifest:
        raise SourceIngressError("source manifest has the wrong exact shape")
    if len(manifest.reads) > MAX_SOURCE_READS:
        raise SourceIngressError("source manifest exceeds its finite bound")
    keys = tuple(_source_read_key(read) for read in manifest.reads)
    if keys != tuple(sorted(keys)) or len(keys) != len(set(keys)):
        raise SourceIngressError("source manifest must be canonical and duplicate-free")


_FRESH_SOURCE_SLOT_TOKENS = (
    (SourceFactKind.CORE, "shared"),
    (SourceFactKind.PROTOCOL, "fresh"),
    (SourceFactKind.RELATION_BINDING, "fresh"),
    (SourceFactKind.PLAN_WITNESS_BINDING, "fresh"),
    (SourceFactKind.STATEMENT_EDGE, "fresh"),
    (SourceFactKind.CLAIM_EDGE, "fresh"),
    (SourceFactKind.WITNESS_EDGE, "fresh"),
)
_AFK_FRESH_FS_SOURCE_SLOT_TOKENS = _FRESH_SOURCE_SLOT_TOKENS + (
    (SourceFactKind.PROTOCOL, "fiat-shamir"),
    (SourceFactKind.CONSTRUCTION, "fiat-shamir"),
    (SourceFactKind.RELATION_BINDING, "fiat-shamir"),
    (SourceFactKind.PLAN_WITNESS_BINDING, "fiat-shamir"),
    (SourceFactKind.STATEMENT_EDGE, "fiat-shamir"),
    (SourceFactKind.CLAIM_EDGE, "fiat-shamir"),
    (SourceFactKind.WITNESS_EDGE, "fiat-shamir"),
)


def _source_manifest_profile_case(
    manifest: SourceManifest,
) -> tuple[str, tuple[SourceRead, ...], tuple[tuple[SourceFactKind, str], ...]]:
    """Select one of the two exact concrete source-profile constructors."""

    admit_source_manifest(manifest)
    by_token: dict[tuple[SourceFactKind, str], SourceRead] = {}
    for read in manifest.reads:
        token = _source_read_token(read)
        if token in by_token:
            raise SourceIngressError("source manifest repeats one closed slot")
        by_token[token] = read
    for name, expected in (
        ("schnorr-fresh", _FRESH_SOURCE_SLOT_TOKENS),
        ("afk-fresh-fs", _AFK_FRESH_FS_SOURCE_SLOT_TOKENS),
    ):
        if set(by_token) == set(expected):
            return name, tuple(by_token[item] for item in expected), expected
    raise SourceIngressError(
        "portable source manifest is neither the exact Fresh nor Fresh/FS catalog"
    )


def _source_profile_adequacy_evaluator_id(
    *,
    profile: object = ANALYSIS_PROPERTY_PROFILE,
    input_schema_label: str = "source-profile-input-v0",
    input_schema_owner: object = ANALYSIS_PROPERTY_PROFILE,
) -> object:
    if profile not in (
        ANALYSIS_PROPERTY_PROFILE,
        ANALYSIS_TRANSPORT_PROFILE,
    ):
        raise SourceIngressError("source adequacy evaluator selects a wrong profile")
    input_schema = analysis_profile_declaration_ref(
        profile,
        input_schema_owner,
        "analysis.semantic-law",
        input_schema_label,
    )
    failure_partition = analysis_profile_declaration_ref(
        profile,
        profile,
        "analysis.semantic-law",
        "analysis-attempt-failure-partition-v0",
    )
    return _form_analysis_profiled_content_id(
        "analysis.adequacy-evaluator",
        AnalysisAdequacyEvaluatorBodyV0(
            input_schema,
            (_active_analysis_profile_id(profile),),
            k1.value_type_datum(k1.BOOL),
            _Analysis_REFERENCE_CHECKER_ALGORITHM_ID,
            _Analysis_REFERENCE_CHECKER_EVALUATION_CONTRACT_ID,
            tuple(k1.direct_module_dependencies(_Analysis_REFERENCE_CHECKER_ALGORITHM)),
            True,
            failure_partition,
        ),
        profile,
    )


def _family_source_profile_adequacy_evaluator_id(axis: str) -> object:
    labels = {
        "fresh-source": "afk-family-source-profile-input-v0",
        "adaptive-fs-target": "afk-family-target-profile-input-v0",
    }
    label = labels.get(axis)
    if label is None:
        raise SourceIngressError("unsupported AFK family-source adequacy axis")
    return _source_profile_adequacy_evaluator_id(
        profile=ANALYSIS_TRANSPORT_PROFILE,
        input_schema_label=label,
        input_schema_owner=ANALYSIS_TRANSPORT_PROFILE,
    )


def source_profile_id(manifest: SourceManifest) -> object:
    """Form one of the two stable concrete-owner source profiles."""

    case_name, _, expected_slots = _source_manifest_profile_case(manifest)
    profile = ANALYSIS_PROPERTY_PROFILE
    family_labels = {
        "schnorr-fresh": "schnorr-relation-special-soundness-source",
        "afk-fresh-fs": "afk-adaptive-fresh-fs-source",
    }
    input_labels = {
        "schnorr-fresh": "schnorr-relation-source-profile-input-v0",
        "afk-fresh-fs": "afk-fresh-fs-source-profile-input-v0",
    }
    family_tag = analysis_profile_declaration_ref(
        profile,
        profile,
        "analysis.source-family",
        family_labels[case_name],
    )
    failure_partition = analysis_profile_declaration_ref_body(
        analysis_profile_declaration_ref(
            profile,
            profile,
            "analysis.semantic-law",
            "analysis-attempt-failure-partition-v0",
        )
    )
    slot_schemas = k1.DatumSeq(
        tuple(
            k1.DatumRecord(
                (
                    (0, k1.Nat(ordinal)),
                    (1, k1.Nat(_SOURCE_FACT_KIND_ORDINAL[kind])),
                    (
                        2,
                        k1.DatumVariant(
                            {"shared": 0, "fresh": 1, "fiat-shamir": 2}[axis],
                            k1.UNIT,
                        ),
                    ),
                    (3, k1.DatumVariant(0, k1.UNIT)),
                    (4, k1.DatumVariant(0, k1.UNIT)),
                    (5, k1.DatumVariant(0, k1.UNIT)),
                    (6, failure_partition),
                )
            )
            for ordinal, (kind, axis) in enumerate(expected_slots)
        )
    )
    closed_fields = k1.DatumSeq(
        tuple(
            k1.DatumRecord(
                (
                    (0, k1.Nat(_SOURCE_FACT_KIND_ORDINAL[kind])),
                    (
                        1,
                        k1.DatumVariant(
                            {"shared": 0, "fresh": 1, "fiat-shamir": 2}[axis],
                            k1.UNIT,
                        ),
                    ),
                )
            )
            for kind, axis in expected_slots
        )
    )
    return _analysis_id(
        "analysis.source-profile",
        AnalysisSourceProfileBodyV0(
            family_tag,
            slot_schemas,
            closed_fields,
            _source_profile_adequacy_evaluator_id(
                input_schema_label=input_labels[case_name],
            ),
        ),
    )


def source_manifest_id(manifest: SourceManifest) -> object:
    _, ordered_reads, _ = _source_manifest_profile_case(manifest)
    subjects_by_ref: dict[bytes, object] = {}
    for read in ordered_reads:
        subjects_by_ref.setdefault(read.owner_id.internal_reference(), read.owner_id)
    exact_subjects = tuple(subjects_by_ref.values())
    return _analysis_id(
        "analysis.semantic-read-manifest",
        AnalysisSemanticReadManifestBodyV0(
            source_profile_id(manifest),
            exact_subjects,
            k1.DatumSeq(
                tuple(
                    k1.DatumRecord(
                        (
                            (0, k1.Nat(ordinal)),
                            (1, _id_datum(read.owner_id)),
                            (2, _source_coordinate_body(read)),
                        )
                    )
                    for ordinal, read in enumerate(ordered_reads)
                )
            ),
        ),
    )


_PROTOCOL_SOURCE_ISSUER = object()


@dataclass(frozen=True)
class ProtocolAnalysisSource:
    core: object
    construction: object
    core_id: object
    construction_id: object
    fresh_protocol_id: object
    fiat_shamir_protocol_id: object
    _issuer: object


def derive_protocol_source(
    core: object, construction: object
) -> ProtocolAnalysisSource:
    k2.admit_core(core)
    construction.admit()
    if not k2.is_public_coin_eligible(core):
        raise SourceIngressError("Fresh-to-FS source Core is not public-coin eligible")
    return ProtocolAnalysisSource(
        core,
        construction,
        k2.core_id(core),
        k2.construction_id(core, construction),
        k3.protocol_id(core, None, k2.ChallengeInterpretation.FRESH),
        k3.protocol_id(core, construction, k2.ChallengeInterpretation.FIAT_SHAMIR),
        _PROTOCOL_SOURCE_ISSUER,
    )


def require_protocol_source(source: ProtocolAnalysisSource) -> None:
    if (
        type(source) is not ProtocolAnalysisSource
        or source._issuer is not _PROTOCOL_SOURCE_ISSUER
    ):
        raise AuthorityError("Protocol Analysis source lacks owner issuance")
    expected = derive_protocol_source(source.core, source.construction)
    if source != expected:
        raise SourceIngressError(
            "Protocol Analysis source disagrees with PIR/K3 derivation"
        )


_RELATION_SOURCE_ISSUER = object()


@dataclass(frozen=True)
class RelationPropertySource:
    case: object
    protocol_source: ProtocolAnalysisSource
    checked_plan: object
    checked_protocol_binding: object
    checked_plan_binding: object
    instance: str
    statement_slot: str
    claim: str
    witness_slot: str
    terminal: str
    manifest: SourceManifest
    _issuer: object


def _checked_case_axes(case: object) -> tuple[object, object]:
    if type(case) is not k3.DependentSurfaceCase or case.construction is None:
        raise SourceIngressError("relation property needs one exact Relations FS case")
    return case.construction, k2.ChallengeInterpretation.FIAT_SHAMIR


def _select_relation_coordinates(
    case: object,
    checked_protocol: object,
    checked_plan_binding: object,
    *,
    instance: str,
    statement_slot: str,
    claim: str,
    witness_slot: str,
    terminal: str,
) -> tuple[object, object, object, object, object]:
    binding = checked_protocol.binding
    instance_value = next(
        (item for item in binding.instances if item.name == instance), None
    )
    if instance_value is None:
        raise SourceIngressError("relation property names no exact relation instance")
    statement_edge = next(
        (
            edge
            for edge in binding.public_edges
            if edge.instance == instance and edge.slot == statement_slot
        ),
        None,
    )
    if statement_edge is None or type(statement_edge.source) is not k3.BindingRef:
        raise SourceIngressError("relation property lacks its exact Statement edge")
    claim_edge = next(
        (
            edge
            for edge in binding.claim_edges
            if edge.instance == instance and edge.claim.claim == claim
        ),
        None,
    )
    if claim_edge is None:
        raise SourceIngressError("relation property lacks its exact claim edge")
    witness_edge = next(
        (
            edge
            for edge in checked_plan_binding.binding.witness_edges
            if edge.slot == witness_slot
        ),
        None,
    )
    if witness_edge is None:
        raise SourceIngressError("relation property lacks its exact witness edge")
    terminal_occurrence = next(
        (item for item in case.core.schedule if item.name == terminal), None
    )
    if (
        terminal_occurrence is None
        or terminal_occurrence.kind is not k2.OccurrenceKind.TERMINAL
    ):
        raise SourceIngressError("relation property names no exact terminal occurrence")
    return instance_value, statement_edge, claim_edge, witness_edge, terminal_occurrence


def _relation_manifest(
    case: object,
    protocol_source: ProtocolAnalysisSource,
    checked_protocol: object,
    checked_plan_binding: object,
    selected: tuple[object, object, object, object, object],
) -> SourceManifest:
    instance, statement, claim, witness, terminal = selected
    reads = [
        SourceRead(SourceFactKind.CORE, protocol_source.core_id, "interactive-core"),
        SourceRead(
            SourceFactKind.PROTOCOL,
            protocol_source.fiat_shamir_protocol_id,
            "fiat-shamir",
        ),
        SourceRead(
            SourceFactKind.CONSTRUCTION,
            protocol_source.construction_id,
            "transcript-construction",
        ),
        SourceRead(
            SourceFactKind.RELATION_BINDING,
            checked_protocol.binding_id,
            "protocol-relation-binding",
        ),
        SourceRead(
            SourceFactKind.PLAN_WITNESS_BINDING,
            checked_plan_binding.binding_id,
            "plan-witness-binding",
        ),
        SourceRead(
            SourceFactKind.RELATION_INSTANCE,
            instance.relation_interface_id,
            instance.name,
        ),
        SourceRead(
            SourceFactKind.STATEMENT_EDGE,
            checked_protocol.binding_id,
            f"{statement.instance}:{statement.slot}:{statement.source.scope}:{statement.source.input_name}",
        ),
        SourceRead(
            SourceFactKind.CLAIM_EDGE,
            checked_protocol.binding_id,
            f"{claim.instance}:{claim.claim.origin.value}:{claim.claim.claim}",
        ),
        SourceRead(
            SourceFactKind.WITNESS_EDGE,
            checked_plan_binding.binding_id,
            f"{witness.slot}:{witness.witness_surface_key}",
        ),
        SourceRead(SourceFactKind.TERMINAL, protocol_source.core_id, terminal.name),
    ]
    for bridge in case.bridges:
        if bridge.lane is k3.ValueBridgeLane.DIRECTIONAL_LOSSY:
            reads.append(
                SourceRead(
                    SourceFactKind.VALUE_BRIDGE,
                    k3.value_bridge_id(bridge),
                    bridge.name,
                )
            )
    return source_manifest(reads)


def derive_relation_property_source(
    case: object,
    *,
    instance: str = "knowledge-instance",
    statement_slot: str = "statement",
    claim: str = "knowledge",
    witness_slot: str = "secret",
    terminal: str = "terminal",
) -> RelationPropertySource:
    construction, interpretation = _checked_case_axes(case)
    protocol_source = derive_protocol_source(case.core, construction)
    checked_plan = k3.check_plan_realizes(
        case.core, construction, interpretation, case.plan
    )
    checked_protocol = k3.check_protocol_relation_binding(
        case.core,
        construction,
        interpretation,
        case.relation_interfaces,
        case.bridges,
        case.protocol_binding,
    )
    k3.require_whole_protocol_binding(checked_protocol)
    if len(case.relation_interfaces) != 1:
        raise SourceIngressError("bounded relation property selects one Interface")
    surface = k3.derive_plan_witness_surface(
        case.core, construction, interpretation, case.plan
    )
    checked_plan_binding = k3.check_plan_witness_binding(
        surface,
        case.relation_interfaces[0],
        case.bridges,
        case.plan_binding,
    )
    k3.require_whole_plan_binding(checked_plan_binding)
    selected = _select_relation_coordinates(
        case,
        checked_protocol,
        checked_plan_binding,
        instance=instance,
        statement_slot=statement_slot,
        claim=claim,
        witness_slot=witness_slot,
        terminal=terminal,
    )
    manifest = _relation_manifest(
        case, protocol_source, checked_protocol, checked_plan_binding, selected
    )
    return RelationPropertySource(
        case,
        protocol_source,
        checked_plan,
        checked_protocol,
        checked_plan_binding,
        instance,
        statement_slot,
        claim,
        witness_slot,
        terminal,
        manifest,
        _RELATION_SOURCE_ISSUER,
    )


def require_relation_property_source(source: RelationPropertySource) -> None:
    if (
        type(source) is not RelationPropertySource
        or source._issuer is not _RELATION_SOURCE_ISSUER
    ):
        raise AuthorityError("relation Analysis source lacks owner issuance")
    require_protocol_source(source.protocol_source)
    k3.require_whole_protocol_binding(source.checked_protocol_binding)
    k3.require_whole_plan_binding(source.checked_plan_binding)
    expected = derive_relation_property_source(
        source.case,
        instance=source.instance,
        statement_slot=source.statement_slot,
        claim=source.claim,
        witness_slot=source.witness_slot,
        terminal=source.terminal,
    )
    if source != expected:
        raise SourceIngressError("relation Analysis source or manifest was substituted")


_PAIR_SOURCE_ISSUER = object()


@dataclass(frozen=True)
class FreshFsRelationSource:
    case: object
    protocol_source: ProtocolAnalysisSource
    fresh_plan: object
    fresh_checked_plan: object
    fresh_plan_binding: object
    fiat_shamir_checked_plan: object
    fiat_shamir_plan_binding: object
    fresh_binding: object
    fiat_shamir_binding: object
    fresh_manifest: SourceManifest
    fiat_shamir_manifest: SourceManifest
    pair_manifest: SourceManifest
    _issuer: object


def _axis_relation_manifest(
    protocol_source: ProtocolAnalysisSource,
    binding: object,
    plan_binding: object,
    axis: str,
) -> SourceManifest:
    reads = [
        SourceRead(SourceFactKind.CORE, protocol_source.core_id, "interactive-core"),
        SourceRead(
            SourceFactKind.PROTOCOL,
            protocol_source.fresh_protocol_id
            if axis == "fresh"
            else protocol_source.fiat_shamir_protocol_id,
            axis,
        ),
        SourceRead(
            SourceFactKind.RELATION_BINDING,
            binding.binding_id,
            f"{axis}-relation-binding",
        ),
        SourceRead(
            SourceFactKind.PLAN_WITNESS_BINDING,
            plan_binding.binding_id,
            f"{axis}-plan-witness-binding",
        ),
    ]
    if axis == "fiat-shamir":
        reads.append(
            SourceRead(
                SourceFactKind.CONSTRUCTION,
                protocol_source.construction_id,
                "transcript-construction",
            )
        )
    for edge in binding.binding.public_edges:
        if type(edge.source) is k3.BindingRef:
            reads.append(
                SourceRead(
                    SourceFactKind.STATEMENT_EDGE,
                    binding.binding_id,
                    f"{axis}:{edge.instance}:{edge.slot}:{edge.source.scope}:{edge.source.input_name}",
                )
            )
    for edge in binding.binding.claim_edges:
        reads.append(
            SourceRead(
                SourceFactKind.CLAIM_EDGE,
                binding.binding_id,
                f"{axis}:{edge.instance}:{edge.claim.origin.value}:{edge.claim.claim}",
            )
        )
    for edge in plan_binding.binding.witness_edges:
        reads.append(
            SourceRead(
                SourceFactKind.WITNESS_EDGE,
                plan_binding.binding_id,
                f"{axis}:{edge.slot}:{edge.witness_surface_key}",
            )
        )
    return source_manifest(reads)


def derive_fresh_fs_relation_source(case: object) -> FreshFsRelationSource:
    construction, _ = _checked_case_axes(case)
    protocol_source = derive_protocol_source(case.core, construction)
    fs_checked = k3.check_protocol_relation_binding(
        case.core,
        construction,
        k2.ChallengeInterpretation.FIAT_SHAMIR,
        case.relation_interfaces,
        case.bridges,
        case.protocol_binding,
    )
    k3.require_whole_protocol_binding(fs_checked)
    fs_checked_plan = k3.check_plan_realizes(
        case.core,
        construction,
        k2.ChallengeInterpretation.FIAT_SHAMIR,
        case.plan,
    )
    fs_surface = k3.derive_plan_witness_surface(
        case.core,
        construction,
        k2.ChallengeInterpretation.FIAT_SHAMIR,
        case.plan,
    )
    fs_plan_binding = k3.check_plan_witness_binding(
        fs_surface,
        case.relation_interfaces[0],
        case.bridges,
        case.plan_binding,
    )
    k3.require_whole_plan_binding(fs_plan_binding)
    fresh_raw = replace(
        case.protocol_binding, protocol_id=protocol_source.fresh_protocol_id
    )
    fresh_checked = k3.check_protocol_relation_binding(
        case.core,
        None,
        k2.ChallengeInterpretation.FRESH,
        case.relation_interfaces,
        case.bridges,
        fresh_raw,
    )
    k3.require_whole_protocol_binding(fresh_checked)
    fresh_plan = replace(case.plan, protocol_id=protocol_source.fresh_protocol_id)
    fresh_checked_plan = k3.check_plan_realizes(
        case.core,
        None,
        k2.ChallengeInterpretation.FRESH,
        fresh_plan,
    )
    fresh_surface = k3.derive_plan_witness_surface(
        case.core,
        None,
        k2.ChallengeInterpretation.FRESH,
        fresh_plan,
    )
    fresh_plan_binding_raw = replace(
        case.plan_binding,
        plan_witness_surface_id=k3.plan_witness_surface_id(fresh_surface),
    )
    fresh_plan_binding = k3.check_plan_witness_binding(
        fresh_surface,
        case.relation_interfaces[0],
        case.bridges,
        fresh_plan_binding_raw,
    )
    k3.require_whole_plan_binding(fresh_plan_binding)
    fs_shape = replace(
        fs_checked.binding, protocol_id=fresh_checked.binding.protocol_id
    )
    if fresh_checked.binding != fs_shape:
        raise SourceIngressError(
            "Fresh/FS relation bindings differ beyond Protocol axis"
        )
    fresh_manifest = _axis_relation_manifest(
        protocol_source, fresh_checked, fresh_plan_binding, "fresh"
    )
    fs_manifest = _axis_relation_manifest(
        protocol_source, fs_checked, fs_plan_binding, "fiat-shamir"
    )
    pair_reads = {
        _source_read_key(read): read
        for read in fresh_manifest.reads + fs_manifest.reads
    }
    pair_manifest = source_manifest(pair_reads.values())
    return FreshFsRelationSource(
        case,
        protocol_source,
        fresh_plan,
        fresh_checked_plan,
        fresh_plan_binding,
        fs_checked_plan,
        fs_plan_binding,
        fresh_checked,
        fs_checked,
        fresh_manifest,
        fs_manifest,
        pair_manifest,
        _PAIR_SOURCE_ISSUER,
    )


def require_fresh_fs_relation_source(source: FreshFsRelationSource) -> None:
    if (
        type(source) is not FreshFsRelationSource
        or source._issuer is not _PAIR_SOURCE_ISSUER
    ):
        raise AuthorityError("Fresh/FS Analysis source lacks owner issuance")
    require_protocol_source(source.protocol_source)
    k3.require_whole_protocol_binding(source.fresh_binding)
    k3.require_whole_protocol_binding(source.fiat_shamir_binding)
    k3.require_whole_plan_binding(source.fresh_plan_binding)
    k3.require_whole_plan_binding(source.fiat_shamir_plan_binding)
    expected = derive_fresh_fs_relation_source(source.case)
    if source != expected:
        raise SourceIngressError("Fresh/FS source or read closure was substituted")


# ---------------------------------------------------------------------------
# Strategy and experiment identity: never a supplied trace
# ---------------------------------------------------------------------------


class StrategyClass(str, Enum):
    ACCEPTING_TRANSCRIPT_PAIR_DOMAIN = "accepting-transcript-pair-domain"
    ADAPTIVE_CLASSICAL_ONLINE_PROVER = "adaptive-classical-online-prover"


class OracleModel(str, Enum):
    PUBLIC_COIN = "public-coin"
    CLASSICAL_ROM = "classical-rom"
    QROM = "qrom"


class RandomnessOwnership(str, Enum):
    VERIFIER = "verifier"
    RANDOM_ORACLE = "random-oracle"


class Scheduling(str, Enum):
    SINGLE_SESSION = "single-session"


class StatementTiming(str, Enum):
    OUTER_UNIVERSAL = "outer-universal"
    ADAPTIVE_PROVER_OUTPUT = "adaptive-prover-output"


class QuantifierKind(str, Enum):
    EXISTS_DETERMINISTIC_TRANSCRIPT_EXTRACTOR = (
        "exists-deterministic-transcript-extractor"
    )
    FOR_ALL_VALUE = "for-all-value"
    EXISTS_POSITIVE_POLYNOMIAL = "exists-positive-polynomial"
    EXISTS_UNIFORM_BLACK_BOX_EXTRACTOR = "exists-uniform-black-box-extractor"
    FOR_ALL_QUANTITATIVE_VALUE = "for-all-quantitative-value"
    FOR_ALL_ADAPTIVE_PROVERS = "for-all-adaptive-provers"
    OVER_RANDOM_ORACLE = "over-random-oracle"


@dataclass(frozen=True)
class Quantifier:
    kind: QuantifierKind
    binder: str
    domain_id: object


@dataclass(frozen=True)
class ExperimentModel:
    strategy_interface_id: object
    strategy_class: StrategyClass
    oracle_model: OracleModel
    randomness_ownership: RandomnessOwnership
    randomness_law_id: object
    scheduling: Scheduling
    statement_timing: StatementTiming
    setup_profile_id: object
    execution_body_id: object
    output_distribution_profile_id: object
    oracle_query_abi_id: object
    event_profile_id: object
    failure_profile_id: object
    resource_basis_id: object
    quantifiers: tuple[Quantifier, ...]
    parameters: tuple[tuple[str, int], ...]
    query_bound: QuantitativeExpression


def _embedded_component_datum(identifier: object, expected_subject: str) -> object:
    """Embed a local nested value, or reference one independently owned subject.

    `probe.analysis.*` identifiers are process-local content-addressed lookup keys.
    They are never serialized into an Analysis body: this function replaces
    them with the authenticated canonical body they index.
    """

    expected_probe = _LOCAL_COMPONENT_KIND_ALIASES.get(expected_subject)
    if expected_probe is not None and identifier.subject_kind == expected_probe:
        return k1.DatumVariant(
            1,
            _expand_probe_references(
                _local_component_body(
                    identifier,
                    expected_probe.removeprefix("probe.analysis."),
                )
            ),
        )
    return k1.DatumVariant(0, _id_datum(identifier, expected_subject))


def _portable_subject_datum(identifier: object) -> object:
    """Reference a durable/foreign subject or inline one owner-local value."""

    _id_datum(identifier)
    entry = _LOCAL_COMPONENT_BODY_REGISTRY.get(identifier.internal_reference())
    if entry is not None:
        return k1.DatumVariant(1, _expand_probe_references(entry[1]))
    return k1.DatumVariant(0, _id_datum(identifier))


def _quantifier_body(quantifier: Quantifier, local_ordinal: int) -> object:
    if (
        type(quantifier) is not Quantifier
        or type(quantifier.kind) is not QuantifierKind
    ):
        raise ExperimentError("experiment quantifier has an unknown shape")
    _ascii(quantifier.binder, "quantifier binder")
    if type(local_ordinal) is not int or local_ordinal < 0:
        raise ExperimentError("quantifier ordinal must be one natural number")
    expected_subject = {
        QuantifierKind.EXISTS_DETERMINISTIC_TRANSCRIPT_EXTRACTOR: (
            "analysis.extractor-profile"
        ),
        QuantifierKind.FOR_ALL_VALUE: "analysis.value-domain-profile",
        QuantifierKind.FOR_ALL_QUANTITATIVE_VALUE: (
            "analysis.formula-parameter-domain"
        ),
        QuantifierKind.EXISTS_POSITIVE_POLYNOMIAL: (
            "analysis.positive-polynomial-profile"
        ),
        QuantifierKind.EXISTS_UNIFORM_BLACK_BOX_EXTRACTOR: (
            "analysis.extractor-profile"
        ),
        QuantifierKind.FOR_ALL_ADAPTIVE_PROVERS: "analysis.strategy-class",
        QuantifierKind.OVER_RANDOM_ORACLE: "analysis.distribution-profile",
    }[quantifier.kind]
    return k1.DatumRecord(
        (
            (0, k1.Nat(local_ordinal)),
            (1, k1.Symbol(quantifier.kind.value)),
            (2, _embedded_component_datum(quantifier.domain_id, expected_subject)),
        )
    )


def admit_experiment_model(model: ExperimentModel) -> None:
    if type(model) is not ExperimentModel:
        raise ExperimentError("experiment model has the wrong exact shape")
    _id_datum(model.strategy_interface_id, "analysis.strategy-class")
    if (
        type(model.strategy_class) is not StrategyClass
        or type(model.oracle_model) is not OracleModel
        or type(model.randomness_ownership) is not RandomnessOwnership
        or type(model.scheduling) is not Scheduling
        or type(model.statement_timing) is not StatementTiming
    ):
        raise ExperimentError("experiment model has an unknown coordinate")
    for identifier, expected in (
        (model.randomness_law_id, "analysis.distribution-profile"),
        (model.setup_profile_id, "analysis.setup-profile"),
        (model.execution_body_id, "analysis.experiment-body-bundle"),
        (
            model.output_distribution_profile_id,
            "analysis.output-distribution-profile",
        ),
        (model.oracle_query_abi_id, "analysis.oracle-query-abi"),
        (model.event_profile_id, "analysis.event-profile"),
        (model.failure_profile_id, "analysis.failure-profile"),
        (model.resource_basis_id, "analysis.resource-basis"),
    ):
        _id_datum(identifier, expected)
    if len(model.quantifiers) > MAX_QUANTIFIERS:
        raise ExperimentError("experiment quantifier prefix exceeds its finite bound")
    binders = tuple(quantifier.binder for quantifier in model.quantifiers)
    if len(binders) != len(set(binders)):
        raise ExperimentError("experiment quantifier binders must be unique")
    for ordinal, quantifier in enumerate(model.quantifiers):
        _quantifier_body(quantifier, ordinal)
    if len(model.parameters) > MAX_QUANTIFIERS:
        raise ExperimentError("experiment parameter set exceeds its finite bound")
    parameter_names = tuple(name for name, _ in model.parameters)
    if parameter_names != tuple(sorted(parameter_names)) or len(parameter_names) != len(
        set(parameter_names)
    ):
        raise ExperimentError("experiment parameters must be canonical and unique")
    for name, value in model.parameters:
        _ascii(name, "experiment parameter")
        if type(value) is not int or value < 0:
            raise ExperimentError("experiment parameters must be natural numbers")
    admit_quantitative(model.query_bound)
    if model.query_bound.sort is not QuantitativeSort.QUERY_COUNT_ADVERSARY_RO:
        raise ExperimentError("experiment query bound must have QueryCount sort")
    if model.oracle_model is OracleModel.PUBLIC_COIN:
        if (
            model.randomness_ownership is not RandomnessOwnership.VERIFIER
            or type(model.query_bound) is not QNatural
            or model.query_bound.value != 0
        ):
            raise ExperimentError(
                "public-coin model has verifier randomness and zero oracle queries"
            )
    elif model.randomness_ownership is not RandomnessOwnership.RANDOM_ORACLE:
        raise ExperimentError("oracle model must assign randomness to its oracle")


def experiment_model_id(model: ExperimentModel) -> object:
    admit_experiment_model(model)
    selected_profile = ANALYSIS_PROPERTY_PROFILE
    family = family_profile_id(
        PropertyFamily.K_OUT_OF_N_SPECIAL_SOUNDNESS
        if model.strategy_class is StrategyClass.ACCEPTING_TRANSCRIPT_PAIR_DOMAIN
        else PropertyFamily.ADAPTIVE_NIROP_KNOWLEDGE_SOUNDNESS_Q_LT_N
    )
    source_family = analysis_profile_declaration_ref(
        selected_profile,
        selected_profile,
        "analysis.source-family",
        "bounded-concrete-owner-sources",
    )
    source_slots = k1.DatumSeq(
        (
            k1.DatumRecord(
                (
                    (0, k1.Nat(0)),
                    (1, k1.Symbol("strategy-class")),
                    (
                        2,
                        _id_datum(
                            model.strategy_interface_id, "analysis.strategy-class"
                        ),
                    ),
                    (3, _read_purpose_variant(AnalysisReadPurpose.SEMANTIC_MEANING)),
                )
            ),
            k1.DatumRecord(
                (
                    (0, k1.Nat(1)),
                    (1, k1.Symbol("setup-and-input-sampling")),
                    (
                        2,
                        _embedded_component_datum(
                            model.setup_profile_id, "analysis.setup-profile"
                        ),
                    ),
                    (3, _read_purpose_variant(AnalysisReadPurpose.SEMANTIC_MEANING)),
                )
            ),
            k1.DatumRecord(
                (
                    (0, k1.Nat(2)),
                    (1, k1.Symbol("generated-execution-relation")),
                    (
                        2,
                        _embedded_component_datum(
                            model.execution_body_id, "analysis.experiment-body-bundle"
                        ),
                    ),
                    (3, _read_purpose_variant(AnalysisReadPurpose.SEMANTIC_MEANING)),
                )
            ),
        )
    )
    source_profile = _analysis_id(
        "analysis.source-profile",
        AnalysisSourceProfileBodyV0(
            source_family,
            source_slots,
            k1.DatumSeq(
                tuple(
                    k1.DatumRecord(((0, k1.Nat(index)), (1, k1.Nat(2))))
                    for index in range(3)
                )
            ),
            _source_profile_adequacy_evaluator_id(),
        ),
    )
    quantifier_prefix = k1.DatumSeq(
        tuple(
            _quantifier_body(item, ordinal)
            for ordinal, item in enumerate(model.quantifiers)
        )
    )
    return _analysis_id(
        "analysis.experiment-profile",
        AnalysisExperimentProfileBodyV0(
            analysis_profile_declaration_ref_body(family),
            _id_datum(source_profile, "analysis.source-profile"),
            quantifier_prefix,
            k1.DatumSeq(
                (_id_datum(model.strategy_interface_id, "analysis.strategy-class"),)
            ),
            _embedded_component_datum(model.setup_profile_id, "analysis.setup-profile"),
            k1.DatumRecord(
                (
                    (0, k1.Symbol(model.randomness_ownership.value)),
                    (
                        1,
                        _id_datum(
                            model.randomness_law_id, "analysis.distribution-profile"
                        ),
                    ),
                    (2, k1.Symbol(model.statement_timing.value)),
                )
            ),
            k1.DatumRecord(
                (
                    (0, k1.Symbol(model.oracle_model.value)),
                    (
                        1,
                        _embedded_component_datum(
                            model.oracle_query_abi_id, "analysis.oracle-query-abi"
                        ),
                    ),
                    (2, quantitative_body(model.query_bound)),
                )
            ),
            k1.Symbol(model.scheduling.value),
            _embedded_component_datum(
                model.execution_body_id, "analysis.experiment-body-bundle"
            ),
            k1.DatumRecord(
                (
                    (
                        0,
                        _embedded_component_datum(
                            model.output_distribution_profile_id,
                            "analysis.output-distribution-profile",
                        ),
                    ),
                    (
                        1,
                        _embedded_component_datum(
                            model.event_profile_id, "analysis.event-profile"
                        ),
                    ),
                )
            ),
            _embedded_component_datum(
                model.failure_profile_id, "analysis.failure-profile"
            ),
            k1.Symbol("bounded-model-termination-and-noncompletion-law"),
            _embedded_component_datum(
                model.resource_basis_id, "analysis.resource-basis"
            ),
            _embedded_component_datum(
                model.output_distribution_profile_id,
                "analysis.output-distribution-profile",
            ),
        ),
    )


def _symbol_seq(items: tuple[str, ...]) -> object:
    return k1.DatumSeq(
        tuple(k1.Symbol(_ascii(item, "profile coordinate")) for item in items)
    )


def _counterfactual_rights_for_capabilities(
    capabilities: tuple[str, ...],
) -> object:
    return _symbol_seq(
        tuple(
            right
            for right, capability in _COUNTERFACTUAL_RIGHT_CAPABILITY.items()
            if capability in capabilities
        )
    )


@dataclass(frozen=True)
class ValueDomainProfile:
    value_type: str
    domain_predicate: str
    parameters: tuple[tuple[str, int], ...]


def value_domain_profile_id(profile: ValueDomainProfile) -> object:
    if type(profile) is not ValueDomainProfile:
        raise ExperimentError("value-domain profile has the wrong shape")
    return _legacy_component_id(
        "analysis.value-domain-profile",
        k1.DatumRecord(
            (
                (0, k1.Symbol(_ascii(profile.value_type, "value-domain type"))),
                (
                    1,
                    k1.Symbol(
                        _ascii(profile.domain_predicate, "value-domain predicate")
                    ),
                ),
                (
                    2,
                    k1.DatumSeq(
                        tuple(
                            k1.DatumRecord(
                                (
                                    (0, k1.Symbol(_ascii(name, "domain parameter"))),
                                    (1, k1.Nat(value)),
                                )
                            )
                            for name, value in profile.parameters
                        )
                    ),
                ),
            )
        ),
    )


@dataclass(frozen=True)
class DeterministicTranscriptExtractorProfile:
    inputs: tuple[str, ...]
    output: tuple[str, ...]
    algorithm: str
    resource_law: str
    deterministic: bool


def deterministic_extractor_profile_id(
    profile: DeterministicTranscriptExtractorProfile,
) -> object:
    if type(profile) is not DeterministicTranscriptExtractorProfile:
        raise ExperimentError("deterministic extractor profile has the wrong shape")
    return _analysis_id(
        "analysis.extractor-profile",
        AnalysisExtractorProfileBodyV0(
            k1.DatumRecord(
                ((0, _symbol_seq(profile.inputs)), (1, _symbol_seq(profile.output)))
            ),
            k1.DatumRecord(
                (
                    (0, k1.Symbol("unit-private-state")),
                    (1, k1.Symbol("unit-randomness")),
                )
            ),
            k1.DatumSeq(()),
            k1.DatumSeq(()),
            k1.Symbol("deterministic-stateless-evaluation"),
            k1.Symbol("deterministic-singleton-output-law"),
            k1.DatumRecord(
                (
                    (0, k1.Symbol(_ascii(profile.algorithm, "extractor algorithm"))),
                    (1, k1.Symbol("output-satisfies-selected-relation")),
                )
            ),
            k1.Symbol(_ascii(profile.resource_law, "extractor resource law")),
            k1.DatumRecord(
                (
                    (0, k1.Symbol("no-counterfactual-capability")),
                    (1, k1.Symbol("fixed-extractor-and-k-out-of-n-special-soundness")),
                    (2, profile.deterministic),
                )
            ),
        ),
    )


@dataclass(frozen=True)
class StrategyInterfaceProfile:
    role: str
    inputs: tuple[str, ...]
    allowed_views: tuple[str, ...]
    forbidden_views: tuple[str, ...]
    outputs: tuple[str, ...]
    output_constraints: tuple[str, ...]
    dependent_binders: tuple[str, ...]
    query_limit: str
    efficiency_restriction: str
    causal_generation_required: bool
    total_output_required: bool


def strategy_interface_profile_id(profile: StrategyInterfaceProfile) -> object:
    if type(profile) is not StrategyInterfaceProfile:
        raise ExperimentError("strategy-interface profile has the wrong shape")
    role_label = {
        "accepted-transcript-pair-domain": "accepted-transcript-pair-domain",
        "adaptive-q-query-prover": "adaptive-classical-online-prover",
    }.get(profile.role)
    if role_label is None:
        raise ExperimentError("strategy role is outside the bounded profile")
    role = analysis_profile_declaration_ref(
        ANALYSIS_PROPERTY_PROFILE,
        ANALYSIS_PROPERTY_PROFILE,
        "analysis.strategy-role",
        role_label,
    )
    parameter_schema = k1.DatumSeq(
        tuple(
            k1.DatumRecord(((0, k1.Nat(ordinal)), (1, k1.Symbol("logical-natural"))))
            for ordinal, _ in enumerate(profile.dependent_binders)
        )
    )
    return _analysis_id(
        "analysis.strategy-class",
        AnalysisStrategyClassBodyV0(
            analysis_profile_declaration_ref_body(role),
            parameter_schema,
            k1.DatumRecord(
                (
                    (0, _symbol_seq(profile.inputs)),
                    (1, _symbol_seq(profile.outputs)),
                    (2, _symbol_seq(profile.output_constraints)),
                    (3, _symbol_seq(profile.forbidden_views)),
                    (4, k1.Symbol(_ascii(profile.query_limit, "strategy query limit"))),
                    (
                        5,
                        k1.Symbol(
                            _ascii(
                                profile.efficiency_restriction,
                                "strategy efficiency restriction",
                            )
                        ),
                    ),
                    (6, profile.causal_generation_required),
                    (7, profile.total_output_required),
                )
            ),
            k1.Symbol("strategy-private-state"),
            k1.Symbol("strategy-initial-advice"),
            _symbol_seq(profile.allowed_views),
            k1.DatumSeq(
                (k1.Symbol("classical-random-oracle-query-capability"),)
                if "query-capability" in profile.allowed_views
                else ()
            ),
            k1.Symbol("typed-causal-next-message-or-stop"),
            k1.Symbol("total-output-or-declared-noncompletion"),
            k1.DatumRecord(
                (
                    (0, k1.Symbol(_ascii(profile.query_limit, "strategy query limit"))),
                    (
                        1,
                        k1.Symbol(
                            _ascii(
                                profile.efficiency_restriction,
                                "strategy efficiency restriction",
                            )
                        ),
                    ),
                )
            ),
        ),
    )


@dataclass(frozen=True)
class FiniteUniformChallengeLaw:
    values: tuple[int, ...]
    mass: Fraction
    owner: RandomnessOwnership
    independent_from: tuple[str, ...]
    access: str
    hidden_table_from_adversary: bool
    failures: tuple[str, ...]
    table_state: str
    existing_index_transition: str
    fresh_index_transition: str
    repeat_query_consistent: bool
    fresh_index_conditionally_uniform: bool
    adaptive_indices: bool


def distribution_profile_id(profile: FiniteUniformChallengeLaw) -> object:
    if (
        type(profile) is not FiniteUniformChallengeLaw
        or type(profile.owner) is not RandomnessOwnership
        or profile.values != tuple(range(len(profile.values)))
        or not profile.values
        or profile.mass != Fraction(1, len(profile.values))
        or profile.failures
    ):
        raise ExperimentError("challenge law is not exact finite total uniform")
    if profile.owner is RandomnessOwnership.RANDOM_ORACLE:
        if (
            profile.table_state != "persistent-finite-map-index-to-challenge"
            or profile.existing_index_transition != "lookup-return-stored-value"
            or profile.fresh_index_transition != "uniform-sample-insert-return"
            or not profile.repeat_query_consistent
            or not profile.fresh_index_conditionally_uniform
            or not profile.adaptive_indices
            or not profile.hidden_table_from_adversary
        ):
            raise ExperimentError(
                "classical-ROM law needs exact adaptive lazy random-function transitions"
            )
    elif (
        profile.table_state != "no-oracle-table"
        or profile.existing_index_transition != "not-applicable"
        or profile.fresh_index_transition != "one-independent-verifier-draw"
        or profile.repeat_query_consistent
        or not profile.fresh_index_conditionally_uniform
        or profile.adaptive_indices
        or profile.hidden_table_from_adversary
    ):
        raise ExperimentError("Fresh law is not one independent verifier draw")
    return _analysis_id(
        "analysis.distribution-profile",
        AnalysisDistributionProfileBodyV0(
            k1.DatumRecord(
                (
                    (0, k1.Symbol("finite-challenge-value")),
                    (1, k1.Nat(len(profile.values))),
                )
            ),
            k1.DatumSeq(tuple(k1.Nat(item) for item in profile.values)),
            _fraction_body(profile.mass),
            k1.DatumSeq(()),
            k1.DatumRecord(
                (
                    (0, k1.Symbol(profile.owner.value)),
                    (1, _symbol_seq(profile.independent_from)),
                    (2, profile.hidden_table_from_adversary),
                )
            ),
            k1.DatumRecord(
                (
                    (0, k1.Symbol(_ascii(profile.access, "randomness access"))),
                    (
                        1,
                        k1.Symbol(
                            _ascii(profile.table_state, "randomness table state")
                        ),
                    ),
                    (
                        2,
                        k1.Symbol(
                            _ascii(
                                profile.existing_index_transition,
                                "existing-index transition",
                            )
                        ),
                    ),
                    (
                        3,
                        k1.Symbol(
                            _ascii(
                                profile.fresh_index_transition, "fresh-index transition"
                            )
                        ),
                    ),
                    (4, profile.repeat_query_consistent),
                    (5, profile.fresh_index_conditionally_uniform),
                    (6, profile.adaptive_indices),
                )
            ),
            k1.DatumRecord(
                (
                    (0, _symbol_seq(profile.failures)),
                    (1, k1.Symbol("total-finite-sampling")),
                )
            ),
        ),
    )


@dataclass(frozen=True)
class SetupProfile:
    theorem_statement: str
    fixed_coordinates: tuple[str, ...]
    raw_relation_statement: str
    timing: str
    adversary_selected: bool
    oracle_correlated: bool
    mutable_within_instance: bool
    visible_view: str


def setup_profile_id(profile: SetupProfile) -> object:
    if type(profile) is not SetupProfile:
        raise ExperimentError("setup profile has the wrong shape")
    return _legacy_component_id(
        "analysis.setup-profile",
        k1.DatumRecord(
            (
                (0, k1.Symbol(_ascii(profile.theorem_statement, "statement choice"))),
                (1, _symbol_seq(profile.fixed_coordinates)),
                (2, k1.Symbol(_ascii(profile.raw_relation_statement, "raw statement"))),
                (3, k1.Symbol(_ascii(profile.timing, "setup timing"))),
                (4, profile.adversary_selected),
                (5, profile.oracle_correlated),
                (6, profile.mutable_within_instance),
                (7, k1.Symbol(_ascii(profile.visible_view, "setup view"))),
            )
        ),
    )


@dataclass(frozen=True)
class QueryABIProfile:
    logical_inputs: tuple[str, ...]
    fixed_setup_inputs: tuple[str, ...]
    carrier_components: tuple[str, ...]
    output_values: tuple[int, ...]
    access: str
    adversary_sees_hidden_table: bool
    statement_domain: str
    commitment_domain: str
    encoding_scope: str
    adversary_query_domain: str
    off_image_queries_allowed: bool
    all_queries_count_toward_bound: bool
    index_equality_law: str


def query_abi_profile_id(profile: QueryABIProfile) -> object:
    if type(profile) is not QueryABIProfile:
        raise ExperimentError("query ABI profile has the wrong shape")
    return _legacy_component_id(
        "analysis.oracle-query-abi",
        k1.DatumRecord(
            (
                (0, _symbol_seq(profile.logical_inputs)),
                (1, _symbol_seq(profile.fixed_setup_inputs)),
                (2, _symbol_seq(profile.carrier_components)),
                (3, k1.DatumSeq(tuple(k1.Nat(item) for item in profile.output_values))),
                (4, k1.Symbol(_ascii(profile.access, "query access"))),
                (5, profile.adversary_sees_hidden_table),
                (6, k1.Symbol(_ascii(profile.statement_domain, "statement domain"))),
                (
                    7,
                    k1.Symbol(_ascii(profile.commitment_domain, "commitment domain")),
                ),
                (8, k1.Symbol(_ascii(profile.encoding_scope, "encoding scope"))),
                (
                    9,
                    k1.Symbol(
                        _ascii(
                            profile.adversary_query_domain,
                            "adversary query domain",
                        )
                    ),
                ),
                (10, profile.off_image_queries_allowed),
                (11, profile.all_queries_count_toward_bound),
                (
                    12,
                    k1.Symbol(
                        _ascii(profile.index_equality_law, "query index equality")
                    ),
                ),
            )
        ),
    )


@dataclass(frozen=True)
class ProbabilitySpaceProfile:
    side: str
    coin_owners: tuple[str, ...]
    randomness_law_id: object
    oracle_state_instance: str
    disjoint_from_side: str
    termination_law: str


def probability_space_profile_id(profile: ProbabilitySpaceProfile) -> object:
    if type(profile) is not ProbabilitySpaceProfile:
        raise ExperimentError("probability-space profile has the wrong shape")
    _id_datum(profile.randomness_law_id, "analysis.distribution-profile")
    if profile.side == profile.disjoint_from_side:
        raise ExperimentError("AFK probability spaces must name distinct sides")
    return _legacy_component_id(
        "analysis.probability-space",
        k1.DatumRecord(
            (
                (0, k1.Symbol(_ascii(profile.side, "probability-space side"))),
                (1, _symbol_seq(profile.coin_owners)),
                (
                    2,
                    _id_datum(
                        profile.randomness_law_id,
                        "analysis.distribution-profile",
                    ),
                ),
                (
                    3,
                    k1.Symbol(
                        _ascii(profile.oracle_state_instance, "oracle state instance")
                    ),
                ),
                (
                    4,
                    k1.Symbol(
                        _ascii(profile.disjoint_from_side, "disjoint experiment side")
                    ),
                ),
                (
                    5,
                    k1.Symbol(_ascii(profile.termination_law, "termination law")),
                ),
            )
        ),
    )


class RandomOracleActor(str, Enum):
    ADAPTIVE_PROVER = "adaptive-prover"
    UNIFORM_BLACK_BOX_EXTRACTOR = "uniform-black-box-extractor"


class CounterfactualOperation(str, Enum):
    """Closed counterfactual operation catalog.

    Fork is deliberately absent: a fork is a checked relation between two
    accepted sibling receipts, not authority to mutate or resume an execution.
    Rewind is likewise absent because this model exposes only a reset to the
    authenticated root frame through ``RERUN``.
    """

    PROGRAM_SIBLING = "ProgramSibling"
    RERUN = "Rerun"


class CounterfactualTableScope(str, Enum):
    NONE = "none"
    EXACT_EXTRACTOR_INVOCATION = "exact-extractor-invocation"


class ProverTapeScope(str, Enum):
    NONE = "none"
    FIXED_SIBLINGS_FRESH_EXPERIMENT = (
        "fixed-among-sibling-reruns-fresh-across-experiments"
    )
    RESAMPLE_EACH_RERUN = "resample-each-rerun"


@dataclass(frozen=True)
class RandomOracleCapabilityContractProfile:
    actor_kind: RandomOracleActor
    challenge_count: int | None
    counterfactual_operations: tuple[CounterfactualOperation, ...]
    table_scope: CounterfactualTableScope
    tape_scope: ProverTapeScope


def random_oracle_capability_contract_id(
    profile: RandomOracleCapabilityContractProfile,
) -> object:
    if type(profile) is not RandomOracleCapabilityContractProfile:
        raise ExperimentError("random-oracle capability contract has wrong shape")
    if (
        type(profile.actor_kind) is not RandomOracleActor
        or any(
            type(operation) is not CounterfactualOperation
            for operation in profile.counterfactual_operations
        )
        or type(profile.table_scope) is not CounterfactualTableScope
        or type(profile.tape_scope) is not ProverTapeScope
    ):
        raise ExperimentError("random-oracle capability contract is not typed")
    prover_profile = RandomOracleCapabilityContractProfile(
        RandomOracleActor.ADAPTIVE_PROVER,
        None,
        (),
        CounterfactualTableScope.NONE,
        ProverTapeScope.NONE,
    )
    extractor_shape = (
        profile.actor_kind is RandomOracleActor.UNIFORM_BLACK_BOX_EXTRACTOR
        and type(profile.challenge_count) is int
        and profile.challenge_count >= 2
        and profile.counterfactual_operations
        == (
            CounterfactualOperation.PROGRAM_SIBLING,
            CounterfactualOperation.RERUN,
        )
        and profile.table_scope is CounterfactualTableScope.EXACT_EXTRACTOR_INVOCATION
        and profile.tape_scope is ProverTapeScope.FIXED_SIBLINGS_FRESH_EXPERIMENT
    )
    if profile != prover_profile and not extractor_shape:
        raise ExperimentError(
            "random-oracle programming/rerun contract was substituted"
        )
    challenge_count = (
        k1.DatumVariant(0, k1.Unit())
        if profile.challenge_count is None
        else k1.DatumVariant(1, k1.Nat(profile.challenge_count))
    )
    operational_laws = (
        "every-adaptive-prover-call-counts-including-repeats-and-off-image",
        "program-only-the-baseline-target-with-distinct-in-codomain-values",
        "all-nontarget-answers-shared-only-within-one-extractor-invocation",
        "fixed-strategy-root-and-tape-among-siblings-fresh-across-experiments",
        "exact-protocol-check-terminal-receipts-bind-query-carrier-and-challenge",
        "accepted-full-transcript-pair-is-derived-not-a-capability",
        "registered-lineages-do-not-claim-a-generic-strategy-engine",
        "no-generic-rewind-fork-qrom-execution-replay-or-concrete-hash-claim",
    )
    return _legacy_component_id(
        "analysis.random-oracle-capability-contract",
        k1.DatumRecord(
            (
                (0, k1.Symbol(profile.actor_kind.value)),
                (1, challenge_count),
                (
                    2,
                    _symbol_seq(
                        tuple(
                            operation.value
                            for operation in profile.counterfactual_operations
                        )
                    ),
                ),
                (3, k1.Symbol(profile.table_scope.value)),
                (4, k1.Symbol(profile.tape_scope.value)),
                (5, _symbol_seq(operational_laws)),
            )
        ),
    )


AFK_PROVER_RO_CAPABILITY_CONTRACT_ID = random_oracle_capability_contract_id(
    RandomOracleCapabilityContractProfile(
        RandomOracleActor.ADAPTIVE_PROVER,
        None,
        (),
        CounterfactualTableScope.NONE,
        ProverTapeScope.NONE,
    )
)
_AFK_EXTRACTOR_CONTRACT_CARDINALITY_REGISTRY: dict[bytes, int] = {}


def afk_extractor_ro_capability_contract_profile(
    challenge_count: int,
) -> RandomOracleCapabilityContractProfile:
    if type(challenge_count) is not int or challenge_count < 2:
        raise ExperimentError("AFK extractor contract requires N >= 2")
    return RandomOracleCapabilityContractProfile(
        RandomOracleActor.UNIFORM_BLACK_BOX_EXTRACTOR,
        challenge_count,
        (
            CounterfactualOperation.PROGRAM_SIBLING,
            CounterfactualOperation.RERUN,
        ),
        CounterfactualTableScope.EXACT_EXTRACTOR_INVOCATION,
        ProverTapeScope.FIXED_SIBLINGS_FRESH_EXPERIMENT,
    )


def afk_extractor_ro_capability_contract_id(challenge_count: int) -> object:
    identifier = random_oracle_capability_contract_id(
        afk_extractor_ro_capability_contract_profile(challenge_count)
    )
    key = identifier.internal_reference()
    prior = _AFK_EXTRACTOR_CONTRACT_CARDINALITY_REGISTRY.get(key)
    if prior is not None and prior != challenge_count:
        raise ExperimentError("AFK extractor contract identity has two codomains")
    _AFK_EXTRACTOR_CONTRACT_CARDINALITY_REGISTRY[key] = challenge_count
    return identifier


AFK_EXTRACTOR_RO_CAPABILITY_CONTRACT_ID = afk_extractor_ro_capability_contract_id(8)


@dataclass(frozen=True)
class LazyRandomFunctionProcessProfile:
    query_abi_id: object
    query_resource_dimension_id: object
    initial_state: str
    index_equality: str
    repeat_transition: str
    fresh_transition: str
    query_count_transition: str
    bound_binder: str
    over_bound: str
    capability_contract_id: object
    executable_scope: str


def lazy_random_function_process_profile_id(
    profile: LazyRandomFunctionProcessProfile,
) -> object:
    if type(profile) is not LazyRandomFunctionProcessProfile:
        raise ExperimentError("lazy random-function process has the wrong shape")
    _id_datum(profile.query_abi_id, "analysis.oracle-query-abi")
    _id_datum(profile.query_resource_dimension_id, "analysis.resource-dimension")
    _id_datum(
        profile.capability_contract_id,
        "analysis.random-oracle-capability-contract",
    )
    exact_transition_laws = (
        profile.initial_state,
        profile.index_equality,
        profile.repeat_transition,
        profile.fresh_transition,
        profile.query_count_transition,
        profile.bound_binder,
        profile.over_bound,
    )
    is_prover_process = (
        profile.capability_contract_id == AFK_PROVER_RO_CAPABILITY_CONTRACT_ID
    )
    is_extractor_process = (
        profile.capability_contract_id.internal_reference()
        in _AFK_EXTRACTOR_CONTRACT_CARDINALITY_REGISTRY
    )
    expected_scope = (
        "typed-classical-query-transition"
        if is_prover_process
        else "typed-classical-query-and-counterfactual-transitions"
    )
    if (
        exact_transition_laws
        != (
            "empty-finite-map",
            "byte-equality",
            "lookup-return-no-fresh-draw",
            "uniform-sample-insert-return",
            "increment-on-every-call-including-repeat-and-off-image",
            "Q",
            "refuse-before-Q-plus-one-query",
        )
        or (not is_prover_process and not is_extractor_process)
        or (profile.executable_scope != expected_scope)
    ):
        raise ExperimentError("lazy random-function process semantics were substituted")
    exact_common = exact_transition_laws + (profile.executable_scope,)
    return _legacy_component_id(
        "analysis.lazy-random-function-process",
        k1.DatumRecord(
            (
                (0, _id_datum(profile.query_abi_id, "analysis.oracle-query-abi")),
                (
                    1,
                    _id_datum(
                        profile.query_resource_dimension_id,
                        "analysis.resource-dimension",
                    ),
                ),
                (2, _symbol_seq(exact_common)),
                (
                    3,
                    _id_datum(
                        profile.capability_contract_id,
                        "analysis.random-oracle-capability-contract",
                    ),
                ),
            )
        ),
    )


@dataclass(frozen=True)
class SingleExperimentBodyProfile:
    side: str
    probability_space: ProbabilitySpaceProfile
    actor_id: object
    actor_kind: str
    actor_binder: str
    oracle_query_abi_id: object
    schedule: tuple[str, ...]
    output_schema: tuple[str, ...]
    event_ids: tuple[object, ...]
    resource_basis_id: object
    total_output_required: bool
    random_function_process: LazyRandomFunctionProcessProfile | None = None


def single_experiment_body_id(profile: SingleExperimentBodyProfile) -> object:
    if type(profile) is not SingleExperimentBodyProfile:
        raise ExperimentError("single experiment body has the wrong shape")
    space_id = probability_space_profile_id(profile.probability_space)
    if profile.side != profile.probability_space.side:
        raise ExperimentError("experiment body and probability-space sides disagree")
    if profile.actor_kind not in ("strategy", "extractor"):
        raise ExperimentError("experiment body actor kind is unsupported")
    _ascii(profile.actor_binder, "experiment actor binder")
    _id_datum(
        profile.actor_id,
        "analysis.strategy-class"
        if profile.actor_kind == "strategy"
        else "analysis.extractor-profile",
    )
    _id_datum(profile.oracle_query_abi_id, "analysis.oracle-query-abi")
    _id_datum(profile.resource_basis_id, "analysis.resource-basis")
    if not profile.event_ids or not profile.total_output_required:
        raise ExperimentError(
            "selected experiment bodies require total structured output"
        )
    for event_id in profile.event_ids:
        _id_datum(event_id, "analysis.event-profile")
    process_id: object | None = None
    if profile.side in ("prover-experiment", "extractor-experiment"):
        if profile.random_function_process is None:
            raise ExperimentError("adaptive AFK experiment lacks its lazy-RO process")
        process_id = lazy_random_function_process_profile_id(
            profile.random_function_process
        )
        expected_capability_contract_id = (
            AFK_PROVER_RO_CAPABILITY_CONTRACT_ID
            if profile.side == "prover-experiment"
            else profile.random_function_process.capability_contract_id
        )
        if profile.side == "extractor-experiment":
            contract_cardinality = _AFK_EXTRACTOR_CONTRACT_CARDINALITY_REGISTRY.get(
                expected_capability_contract_id.internal_reference()
            )
            if (
                contract_cardinality is None
                or profile.oracle_query_abi_id != afk_query_abi_id(contract_cardinality)
            ):
                raise ExperimentError(
                    "AFK extractor contract codomain disagrees with its query ABI"
                )
        if (
            profile.random_function_process.query_abi_id != profile.oracle_query_abi_id
            or profile.random_function_process.capability_contract_id
            != expected_capability_contract_id
        ):
            raise ExperimentError("AFK process capability detached from its actor")
    elif profile.random_function_process is not None:
        raise ExperimentError("non-ROM experiment cannot carry a lazy-RO process")
    return _legacy_component_id(
        "analysis.experiment-body",
        k1.DatumRecord(
            (
                (0, k1.Symbol(_ascii(profile.side, "experiment side"))),
                (1, _id_datum(space_id, "analysis.probability-space")),
                (2, k1.Symbol(profile.actor_kind)),
                (3, _id_datum(profile.actor_id)),
                (4, k1.Symbol(profile.actor_binder)),
                (
                    5,
                    _id_datum(profile.oracle_query_abi_id, "analysis.oracle-query-abi"),
                ),
                (6, _symbol_seq(profile.schedule)),
                (7, _symbol_seq(profile.output_schema)),
                (
                    8,
                    k1.DatumSeq(
                        tuple(
                            _id_datum(item, "analysis.event-profile")
                            for item in profile.event_ids
                        )
                    ),
                ),
                (9, _id_datum(profile.resource_basis_id, "analysis.resource-basis")),
                (10, profile.total_output_required),
                (
                    11,
                    _id_datum(process_id, "analysis.lazy-random-function-process")
                    if process_id is not None
                    else k1.Symbol("no-lazy-random-function-process"),
                ),
            )
        ),
    )


@dataclass(frozen=True)
class ExperimentExecutionBodyProfile:
    profile_kind: str
    probability_spaces: tuple[ProbabilitySpaceProfile, ...]
    strategy_interface_id: object
    oracle_query_abi_id: object
    output_distribution_profile_id: object
    event_ids: tuple[object, ...]
    extractor_profile_id: object
    distribution_law_id: object
    schedule: tuple[str, ...]
    output_schema: tuple[str, ...]
    resource_basis_id: object
    total_output_required: bool
    component_body_ids: tuple[object, ...]
    component_body_profiles: tuple[SingleExperimentBodyProfile, ...]
    distribution_equality_profile: DistributionEqualityProfile | None


def experiment_execution_body_id(
    profile: ExperimentExecutionBodyProfile,
) -> object:
    if type(profile) is not ExperimentExecutionBodyProfile:
        raise ExperimentError("experiment execution body has the wrong shape")
    _id_datum(profile.strategy_interface_id, "analysis.strategy-class")
    _id_datum(profile.oracle_query_abi_id, "analysis.oracle-query-abi")
    _id_datum(
        profile.output_distribution_profile_id,
        "analysis.output-distribution-profile",
    )
    _id_datum(profile.extractor_profile_id, "analysis.extractor-profile")
    _id_datum(profile.distribution_law_id, "analysis.distribution-profile")
    _id_datum(profile.resource_basis_id, "analysis.resource-basis")
    derived_component_ids = tuple(
        single_experiment_body_id(item) for item in profile.component_body_profiles
    )
    if derived_component_ids != profile.component_body_ids:
        raise ExperimentError(
            "experiment component IDs detached from owned body profiles"
        )
    if not profile.component_body_ids or len(profile.component_body_ids) != len(
        set(profile.component_body_ids)
    ):
        raise ExperimentError("experiment bundle needs distinct component bodies")
    for component_id in profile.component_body_ids:
        _id_datum(component_id, "analysis.experiment-body")
    space_ids = tuple(
        probability_space_profile_id(item) for item in profile.probability_spaces
    )
    if not space_ids or len(space_ids) != len(set(space_ids)):
        raise ExperimentError("experiment body needs distinct probability spaces")
    for event_id in profile.event_ids:
        _id_datum(event_id, "analysis.event-profile")
    if profile.profile_kind == "adaptive-afk-pair":
        if profile.distribution_equality_profile is None:
            raise ExperimentError("adaptive AFK body lacks its structured law equality")
        if len(profile.component_body_profiles) != 2:
            raise ExperimentError("adaptive AFK body needs exactly two owned bodies")
        derived_law_id = distribution_equality_profile_id(
            profile.distribution_equality_profile
        )
        prover_body, extractor_body = profile.component_body_profiles
        if (
            tuple(item.side for item in profile.probability_spaces)
            != ("prover-experiment", "extractor-experiment")
            or tuple(item.disjoint_from_side for item in profile.probability_spaces)
            != ("extractor-experiment", "prover-experiment")
            or len({item.oracle_state_instance for item in profile.probability_spaces})
            != 2
            or len({item.randomness_law_id for item in profile.probability_spaces}) != 1
            or not profile.total_output_required
            or profile.output_schema != ("x", "pi", "aux", "v", "w")
            or len(profile.component_body_ids) != 2
            or len(set(profile.component_body_ids)) != 2
            or profile.strategy_interface_id != ADAPTIVE_KNOWLEDGE_INTERFACE
            or profile.output_distribution_profile_id != AFK_OUTPUT_DISTRIBUTION_PROFILE
            or profile.extractor_profile_id != AFK_UNIFORM_BLACK_BOX_EXTRACTOR
            or profile.resource_basis_id != AFK_RESOURCE_BASIS
            or profile.event_ids
            != (
                AFK_PROVER_ACCEPT_EVENT,
                subject_bound_relation_success_event_id(AFK_THEOREM_SUBJECT_SCHEMA_ID),
            )
            or profile.distribution_law_id != derived_law_id
            or profile.distribution_equality_profile.left_experiment_body_id
            != derived_component_ids[0]
            or profile.distribution_equality_profile.right_experiment_body_id
            != derived_component_ids[1]
            or prover_body.probability_space != profile.probability_spaces[0]
            or extractor_body.probability_space != profile.probability_spaces[1]
            or (
                prover_body.actor_id,
                prover_body.actor_kind,
                prover_body.actor_binder,
            )
            != (ADAPTIVE_KNOWLEDGE_INTERFACE, "strategy", "Pa")
            or (
                extractor_body.actor_id,
                extractor_body.actor_kind,
                extractor_body.actor_binder,
            )
            != (AFK_UNIFORM_BLACK_BOX_EXTRACTOR, "extractor", "E")
            or prover_body.oracle_query_abi_id != profile.oracle_query_abi_id
            or extractor_body.oracle_query_abi_id != profile.oracle_query_abi_id
            or prover_body.resource_basis_id != profile.resource_basis_id
            or extractor_body.resource_basis_id != profile.resource_basis_id
            or prover_body.random_function_process is None
            or extractor_body.random_function_process is None
            or prover_body.random_function_process.query_resource_dimension_id
            != AFK_ADVERSARY_RO_QUERY_DIMENSION_ID
            or extractor_body.random_function_process.query_resource_dimension_id
            != AFK_ADVERSARY_RO_QUERY_DIMENSION_ID
            or prover_body.output_schema != ("x", "pi", "aux", "v")
            or extractor_body.output_schema != ("x", "pi", "aux", "v", "w")
            or prover_body.schedule
            != (
                "bind-fixed-setup-before-prover-and-oracle",
                "initialize-empty-private-random-function-table",
                "run-input-free-total-output-adaptive-prover",
                "count-every-classical-oracle-query",
                "lookup-or-uniform-insert-on-each-query",
                "verify-fiat-shamir-proof",
            )
            or extractor_body.schedule
            != (
                "bind-fixed-setup-before-prover-and-oracle",
                "initialize-separate-empty-private-random-function-table",
                "run-uniform-black-box-extractor-on-n-and-prover-oracle",
                "permit-theorem-granted-lazy-sampling-program-sibling-and-root-rerun",
                "count-every-adversary-running-call",
                "preserve-x-pi-aux-v-law-and-append-w",
            )
            or profile.schedule
            != (
                "bind-fixed-setup-before-prover-and-oracle",
                "initialize-disjoint-empty-random-function-tables",
                "run-input-free-total-output-adaptive-prover",
                "count-every-classical-oracle-query",
                "lookup-or-uniform-insert-on-each-query",
                "verify-fiat-shamir-proof",
                "run-one-uniform-black-box-extractor-in-second-space",
                "preserve-x-pi-aux-v-law-and-append-w",
            )
            or prover_body.probability_space.coin_owners
            != ("adaptive-prover", "lazy-random-function", "verifier")
            or extractor_body.probability_space.coin_owners
            != (
                "uniform-extractor",
                "black-box-adaptive-prover-reruns",
                "lazy-random-function",
                "verifier",
            )
            or prover_body.probability_space.termination_law
            != "total-output-adversary-with-no-runtime-bound"
            or extractor_body.probability_space.termination_law
            != "expected-polynomial-time-under-exact-afk-premises"
            or prover_body.event_ids != (AFK_PROVER_ACCEPT_EVENT,)
            or extractor_body.event_ids
            != (subject_bound_relation_success_event_id(AFK_THEOREM_SUBJECT_SCHEMA_ID),)
        ):
            raise ExperimentError(
                "adaptive AFK body needs two disjoint spaces with one shared random-function law"
            )
    return _legacy_component_id(
        "analysis.experiment-body-bundle",
        k1.DatumRecord(
            (
                (0, k1.Symbol(_ascii(profile.profile_kind, "experiment body kind"))),
                (
                    1,
                    k1.DatumSeq(
                        tuple(
                            _id_datum(item, "analysis.probability-space")
                            for item in space_ids
                        )
                    ),
                ),
                (
                    2,
                    _id_datum(profile.strategy_interface_id, "analysis.strategy-class"),
                ),
                (
                    3,
                    _id_datum(profile.oracle_query_abi_id, "analysis.oracle-query-abi"),
                ),
                (
                    4,
                    _id_datum(
                        profile.output_distribution_profile_id,
                        "analysis.output-distribution-profile",
                    ),
                ),
                (
                    5,
                    k1.DatumSeq(
                        tuple(
                            _id_datum(item, "analysis.event-profile")
                            for item in profile.event_ids
                        )
                    ),
                ),
                (
                    6,
                    _id_datum(
                        profile.extractor_profile_id, "analysis.extractor-profile"
                    ),
                ),
                (
                    7,
                    _id_datum(
                        profile.distribution_law_id, "analysis.distribution-profile"
                    ),
                ),
                (8, _symbol_seq(profile.schedule)),
                (9, _symbol_seq(profile.output_schema)),
                (10, _id_datum(profile.resource_basis_id, "analysis.resource-basis")),
                (11, profile.total_output_required),
                (
                    12,
                    k1.DatumSeq(
                        tuple(
                            _id_datum(item, "analysis.experiment-body")
                            for item in profile.component_body_ids
                        )
                    ),
                ),
                (
                    13,
                    k1.DatumSeq(
                        tuple(
                            _id_datum(
                                single_experiment_body_id(item),
                                "analysis.experiment-body",
                            )
                            for item in profile.component_body_profiles
                        )
                    ),
                ),
                (
                    14,
                    _id_datum(
                        distribution_equality_profile_id(
                            profile.distribution_equality_profile
                        ),
                        "analysis.distribution-profile",
                    )
                    if profile.distribution_equality_profile is not None
                    else k1.Symbol("no-distribution-equality"),
                ),
            )
        ),
    )


@dataclass(frozen=True)
class OutcomeProfile:
    prover_output: tuple[str, ...]
    extractor_output: tuple[str, ...]
    structured_outcomes: tuple[str, ...]
    nontermination: str
    win_event: str
    auxiliary_input_distribution: str


@dataclass(frozen=True)
class DistributionEqualityProfile:
    left_experiment_body_id: object
    right_experiment_body_id: object
    projection: tuple[str, ...]
    equality: str


def distribution_equality_profile_id(
    profile: DistributionEqualityProfile,
) -> object:
    if (
        type(profile) is not DistributionEqualityProfile
        or profile.left_experiment_body_id == profile.right_experiment_body_id
        or profile.projection != ("x", "pi", "aux", "v")
        or profile.equality != "exact-law-equality"
    ):
        raise ExperimentError("distribution-equality profile is not exact AFK law")
    _id_datum(profile.left_experiment_body_id, "analysis.experiment-body")
    _id_datum(profile.right_experiment_body_id, "analysis.experiment-body")
    return _analysis_id(
        "analysis.distribution-profile",
        AnalysisDistributionProfileBodyV0(
            k1.Symbol("afk-common-output-marginal"),
            k1.DatumRecord(
                (
                    (
                        0,
                        _embedded_component_datum(
                            profile.left_experiment_body_id,
                            "analysis.experiment-body",
                        ),
                    ),
                    (
                        1,
                        _embedded_component_datum(
                            profile.right_experiment_body_id,
                            "analysis.experiment-body",
                        ),
                    ),
                    (2, _symbol_seq(profile.projection)),
                )
            ),
            k1.Symbol(profile.equality),
            k1.DatumSeq(()),
            k1.Symbol("exact-shared-marginal-no-independence-claim"),
            k1.Symbol("derived-from-the-two-experiment-denotations"),
            k1.Symbol("nontermination-is-outside-the-admitted-strategy-class"),
        ),
    )


def outcome_profile_id(subject_kind: str, profile: OutcomeProfile) -> object:
    if type(profile) is not OutcomeProfile:
        raise ExperimentError("outcome profile has the wrong shape")
    return _legacy_component_id(
        subject_kind,
        k1.DatumRecord(
            (
                (0, _symbol_seq(profile.prover_output)),
                (1, _symbol_seq(profile.extractor_output)),
                (2, _symbol_seq(profile.structured_outcomes)),
                (3, k1.Symbol(_ascii(profile.nontermination, "nontermination law"))),
                (4, k1.Symbol(_ascii(profile.win_event, "win event"))),
                (
                    5,
                    k1.Symbol(
                        _ascii(
                            profile.auxiliary_input_distribution,
                            "auxiliary-input policy",
                        )
                    ),
                ),
            )
        ),
    )


def selected_event_profile_id(label: str, profile: OutcomeProfile) -> object:
    return _legacy_component_id(
        "analysis.event-profile",
        k1.DatumRecord(
            (
                (0, k1.Symbol(_ascii(label, "selected event"))),
                (
                    1,
                    _id_datum(
                        outcome_profile_id(
                            "analysis.output-distribution-profile", profile
                        ),
                        "analysis.output-distribution-profile",
                    ),
                ),
            )
        ),
    )


@dataclass(frozen=True)
class ResourceDimension:
    name: str
    value_sort: str
    scope: str
    aggregation: str
    counter_event: str


def resource_basis_id(dimensions: tuple[ResourceDimension, ...]) -> object:
    if not dimensions or any(
        type(item) is not ResourceDimension for item in dimensions
    ):
        raise ExperimentError("resource basis needs exact dimensions")
    return _legacy_component_id(
        "analysis.resource-basis",
        k1.DatumSeq(
            tuple(
                k1.DatumRecord(
                    (
                        (0, k1.Symbol(_ascii(item.name, "resource name"))),
                        (1, k1.Symbol(_ascii(item.value_sort, "resource sort"))),
                        (2, k1.Symbol(_ascii(item.scope, "resource scope"))),
                        (
                            3,
                            k1.Symbol(_ascii(item.aggregation, "resource aggregation")),
                        ),
                        (4, k1.Symbol(_ascii(item.counter_event, "resource event"))),
                    )
                )
                for item in dimensions
            )
        ),
    )


@dataclass(frozen=True)
class PositivePolynomialProfile:
    input_sort: str
    coefficients_low_to_high: tuple[int, ...]
    evaluation: str
    positivity: str


def positive_polynomial_profile_id(profile: PositivePolynomialProfile) -> object:
    if type(
        profile
    ) is not PositivePolynomialProfile or profile.coefficients_low_to_high != (1,):
        raise ExperimentError("selected positive polynomial must be q(n)=1")
    return _analysis_id(
        "analysis.positive-polynomial-profile",
        AnalysisPositivePolynomialProfileBodyV0(
            k1.Symbol(_ascii(profile.input_sort, "polynomial input sort")),
            k1.Symbol("natural-coefficients"),
            k1.Symbol("canonical-nonempty-low-to-high-sequence"),
            k1.Symbol("highest-nonzero-unless-degree-zero"),
            k1.Symbol(_ascii(profile.evaluation, "polynomial evaluation")),
            k1.Symbol(_ascii(profile.positivity, "polynomial positivity")),
            k1.DatumRecord(((0, k1.Nat(0)), (1, k1.Nat(0)), (2, k1.Nat(1)))),
        ),
    )


def positive_polynomial_id(profile_id: object, coefficients: tuple[int, ...]) -> object:
    _id_datum(profile_id, "analysis.positive-polynomial-profile")
    return _analysis_id(
        "analysis.positive-polynomial",
        AnalysisPositivePolynomialBodyV0(profile_id, coefficients),
    )


@dataclass(frozen=True)
class UniformBlackBoxExtractorProfile:
    inputs: tuple[str, ...]
    forbidden_inputs: tuple[str, ...]
    oracle_rights: tuple[str, ...]
    outputs: tuple[str, ...]
    preserves: tuple[str, ...]
    success_event: str
    termination_law: str
    resource_dimensions: tuple[str, ...]
    prover_rerun_coin_law: str
    uniform_across_provers: bool


def extractor_profile_id(profile: UniformBlackBoxExtractorProfile) -> object:
    if type(profile) is not UniformBlackBoxExtractorProfile:
        raise ExperimentError("extractor profile has the wrong shape")
    return _analysis_id(
        "analysis.extractor-profile",
        AnalysisExtractorProfileBodyV0(
            k1.DatumRecord(
                ((0, _symbol_seq(profile.inputs)), (1, _symbol_seq(profile.outputs)))
            ),
            k1.DatumRecord(
                (
                    (0, k1.Symbol("extractor-private-state")),
                    (1, k1.Symbol("extractor-private-randomness")),
                )
            ),
            _symbol_seq(profile.oracle_rights),
            _counterfactual_rights_for_capabilities(profile.oracle_rights),
            k1.Symbol("preserve-fixed-prover-strategy-and-source-state"),
            _symbol_seq(profile.preserves),
            k1.Symbol(_ascii(profile.success_event, "extractor success")),
            k1.DatumRecord(
                (
                    (
                        0,
                        k1.Symbol(
                            _ascii(profile.termination_law, "extractor termination")
                        ),
                    ),
                    (1, _symbol_seq(profile.resource_dimensions)),
                )
            ),
            k1.DatumRecord(
                (
                    (0, _symbol_seq(profile.forbidden_inputs)),
                    (
                        1,
                        k1.Symbol(
                            _ascii(
                                profile.prover_rerun_coin_law, "prover rerun coin law"
                            )
                        ),
                    ),
                    (2, profile.uniform_across_provers),
                    (3, k1.Symbol("adaptive-knowledge-soundness-q-lt-n")),
                )
            ),
        ),
    )


SPECIAL_SOUNDNESS_PAIR_PROFILE = StrategyInterfaceProfile(
    "accepted-transcript-pair-domain",
    ("same-statement", "same-commitment", "distinct-challenges", "accepted-responses"),
    ("exact-transcript-values",),
    ("prover-state", "future-trace", "hidden-verifier-state"),
    ("relation-witness",),
    (),
    (),
    "not-applicable",
    "deterministic-polynomial-time-extractor-only",
    False,
    True,
)
ADAPTIVE_KNOWLEDGE_PROFILE = StrategyInterfaceProfile(
    "adaptive-q-query-prover",
    (),
    ("fixed-public-setup", "prior-public-view", "query-capability"),
    ("hidden-oracle-table", "future-view", "extractor-state"),
    ("x", "pi", "aux"),
    (
        "length-of-x-equals-security-parameter-n",
        "randomized-adversary-coins-fixed-into-one-deterministic-next-message-strategy-before-extractor-reruns",
    ),
    ("n", "Q"),
    "at-most-Q-classical-random-oracle-queries",
    "no-PPT-restriction-on-adaptive-prover",
    True,
    True,
)
SPECIAL_SOUNDNESS_PAIR_INTERFACE = strategy_interface_profile_id(
    SPECIAL_SOUNDNESS_PAIR_PROFILE
)
ADAPTIVE_KNOWLEDGE_INTERFACE = strategy_interface_profile_id(ADAPTIVE_KNOWLEDGE_PROFILE)

SCHNORR_SETUP_SEMANTICS = SetupProfile(
    "raw-relation-statement-Y",
    (
        "g",
        "q",
        "p",
        "session",
        "application-domain",
        "core",
        "construction",
        "namespace",
        "framing",
        "challenge-condition",
    ),
    "Y",
    "fixed-before-prover-and-random-oracle",
    False,
    False,
    False,
    "fixed-public-setup-view",
)
SCHNORR_SETUP_PROFILE = setup_profile_id(SCHNORR_SETUP_SEMANTICS)

FRESH_OUTPUT_PROFILE_BODY = OutcomeProfile(
    ("x", "commitment", "challenge", "response", "verifier-output"),
    ("x", "w"),
    ("accepted-pair", "premise-failure"),
    "outside-deterministic-pair-domain",
    "extract-and-satisfy-relation",
    "none",
)
AFK_OUTPUT_PROFILE_BODY = OutcomeProfile(
    ("x", "pi", "aux", "v"),
    ("x", "pi", "aux", "v", "w"),
    ("accept", "reject", "abort", "failure"),
    "total-output-domain-excludes-divergent-provers",
    "accept-and-relation-x-w",
    "none",
)
FRESH_OUTPUT_DISTRIBUTION_PROFILE = outcome_profile_id(
    "analysis.output-distribution-profile", FRESH_OUTPUT_PROFILE_BODY
)
AFK_OUTPUT_DISTRIBUTION_PROFILE = outcome_profile_id(
    "analysis.output-distribution-profile", AFK_OUTPUT_PROFILE_BODY
)

NO_ORACLE_QUERY_ABI_BODY = QueryABIProfile(
    (),
    (),
    (),
    (),
    "no-random-oracle",
    False,
    "not-applicable",
    "not-applicable",
    "no-query-encoding",
    "not-applicable",
    False,
    False,
    "not-applicable",
)
K2_AFK_ORACLE_QUERY_ABI_BODY = QueryABIProfile(
    ("arbitrary-canonical-byte-string-index",),
    ("g", "q", "p", "session", "application-domain"),
    (
        "arbitrary-canonical-bytes",
        "verifier-image-derived-prefix",
        "challenge-namespace",
        "requested-bytes",
        "challenge-domain",
    ),
    tuple(range(8)),
    "classical-query-only",
    False,
    "canonical-q-subgroup-element-under-fixed-setup",
    "canonical-q-subgroup-element-under-fixed-setup",
    "verifier-image-exact-k2-framed-carrier-on-selected-valid-domain",
    "all-canonical-byte-strings-within-the-imported-Foundation-finite-term-bound",
    True,
    True,
    "byte-equality-shares-one-persistent-lazy-random-function-entry",
)
NO_ORACLE_QUERY_ABI = query_abi_profile_id(NO_ORACLE_QUERY_ABI_BODY)
FRESH_EXTRACTION_EVENT = selected_event_profile_id(
    "two-accepted-transcripts-extract-relation-witness",
    FRESH_OUTPUT_PROFILE_BODY,
)
AFK_EXTRACTION_EVENT = selected_event_profile_id(
    "adaptive-nirop-complete-output-law", AFK_OUTPUT_PROFILE_BODY
)
FRESH_FAILURE_PROFILE = outcome_profile_id(
    "analysis.failure-profile", FRESH_OUTPUT_PROFILE_BODY
)
AFK_FAILURE_PROFILE = outcome_profile_id(
    "analysis.failure-profile", AFK_OUTPUT_PROFILE_BODY
)

FRESH_RESOURCE_DIMENSIONS = (
    ResourceDimension(
        "accepted-transcripts",
        "exact-count",
        "source-pair",
        "exact",
        "transcript-member",
    ),
)
AFK_RESOURCE_DIMENSIONS = (
    ResourceDimension(
        "adversary-ro-queries",
        "query-count",
        "one-adversary-run",
        "maximum",
        "oracle-query",
    ),
    ResourceDimension(
        "adversary-running-calls",
        "expected-count",
        "one-extractor-run",
        "expected",
        "black-box-call",
    ),
    ResourceDimension(
        "verifier-calls",
        "expected-count",
        "one-extractor-run",
        "expected",
        "verifier-invocation",
    ),
    ResourceDimension(
        "expected-time",
        "expected-count",
        "one-extractor-run",
        "expected",
        "machine-step",
    ),
)
FRESH_RESOURCE_BASIS = resource_basis_id(FRESH_RESOURCE_DIMENSIONS)
AFK_RESOURCE_BASIS = resource_basis_id(AFK_RESOURCE_DIMENSIONS)
AFK_ADVERSARY_RO_QUERY_DIMENSION_ID = resource_dimension_id(
    next(
        item for item in AFK_RESOURCE_DIMENSIONS if item.name == "adversary-ro-queries"
    )
)
AFK_ADVERSARY_RUNNING_CALL_DIMENSION_ID = resource_dimension_id(
    next(
        item
        for item in AFK_RESOURCE_DIMENSIONS
        if item.name == "adversary-running-calls"
    )
)
FRESH_NO_ORACLE_QUERY_DIMENSION_ID = resource_dimension_id(
    ResourceDimension(
        "fresh-no-random-oracle-query-count",
        "query-count",
        "one-fresh-experiment",
        "exact",
        "random-oracle-query",
    )
)

AFK_Q_ONE_POLYNOMIAL_PROFILE = PositivePolynomialProfile(
    "logical-nat", (1,), "exact-checked-natural-horner", "constant-at-least-one"
)
AFK_POSITIVE_POLYNOMIAL_PROFILE_ID = positive_polynomial_profile_id(
    AFK_Q_ONE_POLYNOMIAL_PROFILE
)
AFK_POSITIVE_POLYNOMIAL_Q_ONE = positive_polynomial_id(
    AFK_POSITIVE_POLYNOMIAL_PROFILE_ID,
    (1,),
)
AFK_POSITIVE_POLYNOMIAL_DOMAIN_ID = AFK_POSITIVE_POLYNOMIAL_PROFILE_ID
AFK_Q_ONE_SUBSTITUTION = _local_component_id(
    "theorem-substitution",
    k1.DatumRecord(
        (
            (0, k1.Symbol("afk-v2-thm4-q-of-n-equals-one")),
            (
                1,
                _id_datum(
                    AFK_POSITIVE_POLYNOMIAL_Q_ONE,
                    "analysis.positive-polynomial",
                ),
            ),
        )
    ),
)


def schnorr_protocol_family_id(axis: str) -> object:
    """Return the exact producer-owned ProtocolId for the selected axis.

    Protocol-family meaning is not an Analysis-owned semantic subject.  The
    bounded instrument carries the exact PIR ProtocolId and lets the enclosing
    family/member body state its role.
    """

    if axis not in ("fresh", "fiat-shamir"):
        raise PropertyError("Schnorr protocol-family axis is unsupported")
    case = k3.schnorr_case()
    protocol_id = (
        k3.protocol_id(
            case.core,
            None,
            k2.ChallengeInterpretation.FRESH,
        )
        if axis == "fresh"
        else k3.protocol_id(
            case.core,
            case.construction,
            k2.ChallengeInterpretation.FIAT_SHAMIR,
        )
    )
    _id_datum(protocol_id, "pir.protocol")
    return protocol_id


SCHNORR_FRESH_PROTOCOL_FAMILY_ID = schnorr_protocol_family_id("fresh")
SCHNORR_FIAT_SHAMIR_PROTOCOL_FAMILY_ID = schnorr_protocol_family_id("fiat-shamir")
_SCHNORR_OWNER_CASE_FOR_NESTED_COORDINATES = k3.schnorr_case()
SCHNORR_RELATION_FAMILY_ID = _SCHNORR_OWNER_CASE_FOR_NESTED_COORDINATES.definitions[
    0
].definition_id


def schnorr_family_member_relation_id(
    protocol_family_id: object,
    relation_family_id: object = SCHNORR_RELATION_FAMILY_ID,
) -> object:
    _id_datum(protocol_family_id, "pir.protocol")
    _id_datum(relation_family_id, "relations.definition")
    relation_interface_id = k3.relation_interface_id(
        _SCHNORR_OWNER_CASE_FOR_NESTED_COORDINATES.relation_interfaces[0]
    )
    return _legacy_component_id(
        "analysis.family-member-relation",
        k1.DatumRecord(
            (
                (0, _id_datum(protocol_family_id, "pir.protocol")),
                (1, _id_datum(relation_family_id, "relations.definition")),
                (2, _id_datum(relation_interface_id, "relations.interface")),
                (3, k1.Symbol("forall-n-Member(F,n)-equals-S_n")),
                (4, k1.Symbol("uniform-codecs-relations-verifiers-and-extractors")),
                (5, k1.Symbol("not-established-by-the-fixed-n0-anchor")),
            )
        ),
    )


@dataclass(frozen=True)
class FamilyMemberSubjectProfile:
    protocol_family_id: object
    relation_family_id: object
    member_relation_id: object
    parameter_binder: str
    length_unit: str


def family_member_subject_id(profile: FamilyMemberSubjectProfile) -> object:
    if type(profile) is not FamilyMemberSubjectProfile:
        raise PropertyError("family-member subject has the wrong exact shape")
    expected_member_relation = schnorr_family_member_relation_id(
        profile.protocol_family_id, profile.relation_family_id
    )
    if profile.member_relation_id != expected_member_relation:
        raise PropertyError("family-member subject detached from its exact families")
    if profile.parameter_binder != "n" or profile.length_unit != "octet":
        raise PropertyError("selected AFK family uses n measured in octets")
    return _legacy_component_id(
        "analysis.family-member-subject",
        k1.DatumRecord(
            (
                (
                    0,
                    _id_datum(
                        profile.protocol_family_id,
                        "pir.protocol",
                    ),
                ),
                (
                    1,
                    _id_datum(
                        profile.relation_family_id,
                        "relations.definition",
                    ),
                ),
                (
                    2,
                    _id_datum(
                        profile.member_relation_id,
                        "analysis.family-member-relation",
                    ),
                ),
                (3, k1.Symbol(profile.parameter_binder)),
                (4, k1.Symbol(profile.length_unit)),
                (5, k1.Symbol("Member(F,n)=S_n")),
            )
        ),
    )


def family_member_term_id(subject_id: object, statement_length: int) -> object:
    """Form one diagnostic member term without claiming native Foundation/PIR admission."""

    _id_datum(subject_id, "analysis.family-member-subject")
    if type(statement_length) is not int or statement_length < 1:
        raise PropertyError("family-member term needs a positive statement length")
    return _legacy_component_id(
        "analysis.family-member-term",
        k1.DatumRecord(
            (
                (0, _id_datum(subject_id, "analysis.family-member-subject")),
                (1, k1.Nat(statement_length)),
                (
                    2,
                    k1.Symbol(
                        "symbolic-Analysis-member-not-native-Foundation-PIR-artifact"
                    ),
                ),
            )
        ),
    )


FRESH_THEOREM_SUBJECT_SCHEMA_ID = family_member_subject_id(
    FamilyMemberSubjectProfile(
        SCHNORR_FRESH_PROTOCOL_FAMILY_ID,
        SCHNORR_RELATION_FAMILY_ID,
        schnorr_family_member_relation_id(
            SCHNORR_FRESH_PROTOCOL_FAMILY_ID, SCHNORR_RELATION_FAMILY_ID
        ),
        "n",
        "octet",
    )
)
AFK_THEOREM_SUBJECT_SCHEMA_ID = family_member_subject_id(
    FamilyMemberSubjectProfile(
        SCHNORR_FIAT_SHAMIR_PROTOCOL_FAMILY_ID,
        SCHNORR_RELATION_FAMILY_ID,
        schnorr_family_member_relation_id(
            SCHNORR_FIAT_SHAMIR_PROTOCOL_FAMILY_ID,
            SCHNORR_RELATION_FAMILY_ID,
        ),
        "n",
        "octet",
    )
)
AFK_EXTRACTOR_PROFILE_BODY = UniformBlackBoxExtractorProfile(
    ("security-parameter", "black-box-adaptive-prover"),
    (
        "query-bound",
        "success-probability",
        "prover-code-as-data",
        "hidden-oracle-table",
    ),
    ("classical-query", "lazy-sampling", "program-sibling", "root-rerun"),
    ("x", "pi", "aux", "v", "w"),
    ("x", "pi", "aux", "v"),
    "accept-and-relation-x-w",
    "expected-polynomial-time-under-exact-afk-premises",
    (
        "adversary-ro-queries",
        "adversary-running-calls",
        "verifier-calls",
        "expected-time",
    ),
    "one-fixed-deterministic-prover-strategy-per-extractor-experiment-no-coin-resampling",
    True,
)
AFK_UNIFORM_BLACK_BOX_EXTRACTOR = extractor_profile_id(AFK_EXTRACTOR_PROFILE_BODY)
AFK_PROVER_ACCEPT_EVENT = selected_event_profile_id(
    "prover-verifier-accept", AFK_OUTPUT_PROFILE_BODY
)
AFK_KNOWLEDGE_SUCCESS_EVENT = selected_event_profile_id(
    "extractor-accept-and-relation-x-w", AFK_OUTPUT_PROFILE_BODY
)


def subject_bound_relation_success_event_id(subject_id: object) -> object:
    """Bind AFK success to one exact abstract or concrete relation subject."""

    subject_kinds = (
        "analysis.family-member-subject",
        "analysis.concrete-family-member-subject",
    )
    _id_datum(subject_id, subject_kinds)
    return _legacy_component_id(
        "analysis.event-profile",
        k1.DatumRecord(
            (
                (0, k1.Symbol("accept-and-RelationHolds-Member-F-n-x-w")),
                (1, _id_datum(subject_id, subject_kinds)),
                (
                    2,
                    _id_datum(
                        AFK_KNOWLEDGE_SUCCESS_EVENT,
                        "analysis.event-profile",
                    ),
                ),
                (3, _symbol_seq(("x", "pi", "aux", "v", "w"))),
            )
        ),
    )


SCHNORR_TRANSCRIPT_EXTRACTOR_PROFILE_BODY = DeterministicTranscriptExtractorProfile(
    ("accepted-transcript-pair",),
    ("relation-witness",),
    "x-equals-z-minus-z-prime-over-c-minus-c-prime-mod-q",
    "polynomial-time-in-canonical-group-arithmetic",
    True,
)
SCHNORR_TRANSCRIPT_EXTRACTOR_PROFILE_ID = deterministic_extractor_profile_id(
    SCHNORR_TRANSCRIPT_EXTRACTOR_PROFILE_BODY
)
FRESH_DETERMINISTIC_DISTRIBUTION_LAW = _analysis_id(
    "analysis.distribution-profile",
    AnalysisDistributionProfileBodyV0(
        k1.Symbol("accepted-transcript-pair"),
        k1.Symbol("exact-admitted-pair-domain"),
        k1.Symbol("deterministic-singleton-output-law"),
        k1.DatumSeq(()),
        k1.Symbol("no-random-output-correlation"),
        k1.Symbol("portable-deterministic-extractor-evaluation"),
        k1.Symbol("nonmember-and-malformed-inputs-outside-implication"),
    ),
)
SECURITY_PARAMETER_DOMAIN = ValueDomainProfile(
    "SecurityParameter", "n-greater-than-or-equal-to-one", ()
)
SECURITY_PARAMETER_DOMAIN_ID = value_domain_profile_id(SECURITY_PARAMETER_DOMAIN)


def fresh_pair_experiment_body_profile(
    challenge_count: int,
) -> SingleExperimentBodyProfile:
    randomness_law = fresh_randomness_law_id(challenge_count)
    space = ProbabilitySpaceProfile(
        "fresh-pair-domain",
        ("verifier",),
        randomness_law,
        "no-oracle-state",
        "none",
        "deterministic-domain-quantification",
    )
    return SingleExperimentBodyProfile(
        "fresh-pair-domain",
        space,
        SPECIAL_SOUNDNESS_PAIR_INTERFACE,
        "strategy",
        "Ext",
        NO_ORACLE_QUERY_ABI,
        (
            "bind-fixed-public-setup",
            "admit-two-accepting-transcripts",
            "require-same-statement-and-commitment",
            "require-distinct-legal-challenges",
            "run-one-deterministic-transcript-extractor",
            "check-relation-witness",
        ),
        ("x", "w"),
        (FRESH_EXTRACTION_EVENT,),
        FRESH_RESOURCE_BASIS,
        True,
    )


def fresh_execution_body_id(challenge_count: int) -> object:
    randomness_law = fresh_randomness_law_id(challenge_count)
    space = ProbabilitySpaceProfile(
        "fresh-pair-domain",
        ("verifier",),
        randomness_law,
        "no-oracle-state",
        "none",
        "deterministic-domain-quantification",
    )
    component_profile = fresh_pair_experiment_body_profile(challenge_count)
    component_id = single_experiment_body_id(component_profile)
    return experiment_execution_body_id(
        ExperimentExecutionBodyProfile(
            "fresh-special-soundness-pair",
            (space,),
            SPECIAL_SOUNDNESS_PAIR_INTERFACE,
            NO_ORACLE_QUERY_ABI,
            FRESH_OUTPUT_DISTRIBUTION_PROFILE,
            (FRESH_EXTRACTION_EVENT,),
            SCHNORR_TRANSCRIPT_EXTRACTOR_PROFILE_ID,
            FRESH_DETERMINISTIC_DISTRIBUTION_LAW,
            (
                "bind-fixed-public-setup",
                "admit-two-accepting-transcripts",
                "require-same-statement-and-commitment",
                "require-distinct-legal-challenges",
                "run-one-deterministic-transcript-extractor",
                "check-relation-witness",
            ),
            ("x", "w"),
            FRESH_RESOURCE_BASIS,
            True,
            (component_id,),
            (component_profile,),
            None,
        )
    )


def afk_prover_experiment_body_profile(
    challenge_count: int,
) -> SingleExperimentBodyProfile:
    randomness_law = afk_randomness_law_id(challenge_count)
    prover_space = ProbabilitySpaceProfile(
        "prover-experiment",
        ("adaptive-prover", "lazy-random-function", "verifier"),
        randomness_law,
        "prover-space-private-table",
        "extractor-experiment",
        "total-output-adversary-with-no-runtime-bound",
    )
    return SingleExperimentBodyProfile(
        "prover-experiment",
        prover_space,
        ADAPTIVE_KNOWLEDGE_INTERFACE,
        "strategy",
        "Pa",
        afk_query_abi_id(challenge_count),
        (
            "bind-fixed-setup-before-prover-and-oracle",
            "initialize-empty-private-random-function-table",
            "run-input-free-total-output-adaptive-prover",
            "count-every-classical-oracle-query",
            "lookup-or-uniform-insert-on-each-query",
            "verify-fiat-shamir-proof",
        ),
        ("x", "pi", "aux", "v"),
        (AFK_PROVER_ACCEPT_EVENT,),
        AFK_RESOURCE_BASIS,
        True,
        LazyRandomFunctionProcessProfile(
            afk_query_abi_id(challenge_count),
            AFK_ADVERSARY_RO_QUERY_DIMENSION_ID,
            "empty-finite-map",
            "byte-equality",
            "lookup-return-no-fresh-draw",
            "uniform-sample-insert-return",
            "increment-on-every-call-including-repeat-and-off-image",
            "Q",
            "refuse-before-Q-plus-one-query",
            AFK_PROVER_RO_CAPABILITY_CONTRACT_ID,
            "typed-classical-query-transition",
        ),
    )


def afk_prover_experiment_body_id(challenge_count: int) -> object:
    return single_experiment_body_id(
        afk_prover_experiment_body_profile(challenge_count)
    )


def afk_adversary_running_algorithm_id(challenge_count: int) -> object:
    """AFK's running algorithm A, not merely the prover P^a interface."""

    return _legacy_component_id(
        "analysis.adversary-running-algorithm",
        k1.DatumRecord(
            (
                (
                    0,
                    _id_datum(
                        ADAPTIVE_KNOWLEDGE_INTERFACE,
                        "analysis.strategy-class",
                    ),
                ),
                (
                    1,
                    _id_datum(
                        afk_prover_experiment_body_id(challenge_count),
                        "analysis.experiment-body",
                    ),
                ),
                (
                    2,
                    _id_datum(
                        afk_query_abi_id(challenge_count),
                        "analysis.oracle-query-abi",
                    ),
                ),
                (3, _id_datum(SCHNORR_SETUP_PROFILE, "analysis.setup-profile")),
                (4, _id_datum(AFK_PROVER_ACCEPT_EVENT, "analysis.event-profile")),
                (
                    5,
                    k1.Symbol("run-Pa-under-classical-lazy-RO-then-exact-FS-verifier"),
                ),
            )
        ),
    )


def afk_extractor_experiment_body_profile(
    challenge_count: int,
) -> SingleExperimentBodyProfile:
    randomness_law = afk_randomness_law_id(challenge_count)
    extractor_space = ProbabilitySpaceProfile(
        "extractor-experiment",
        (
            "uniform-extractor",
            "black-box-adaptive-prover-reruns",
            "lazy-random-function",
            "verifier",
        ),
        randomness_law,
        "extractor-space-private-table",
        "prover-experiment",
        "expected-polynomial-time-under-exact-afk-premises",
    )
    return SingleExperimentBodyProfile(
        "extractor-experiment",
        extractor_space,
        AFK_UNIFORM_BLACK_BOX_EXTRACTOR,
        "extractor",
        "E",
        afk_query_abi_id(challenge_count),
        (
            "bind-fixed-setup-before-prover-and-oracle",
            "initialize-separate-empty-private-random-function-table",
            "run-uniform-black-box-extractor-on-n-and-prover-oracle",
            "permit-theorem-granted-lazy-sampling-program-sibling-and-root-rerun",
            "count-every-adversary-running-call",
            "preserve-x-pi-aux-v-law-and-append-w",
        ),
        ("x", "pi", "aux", "v", "w"),
        (subject_bound_relation_success_event_id(AFK_THEOREM_SUBJECT_SCHEMA_ID),),
        AFK_RESOURCE_BASIS,
        True,
        LazyRandomFunctionProcessProfile(
            afk_query_abi_id(challenge_count),
            AFK_ADVERSARY_RO_QUERY_DIMENSION_ID,
            "empty-finite-map",
            "byte-equality",
            "lookup-return-no-fresh-draw",
            "uniform-sample-insert-return",
            "increment-on-every-call-including-repeat-and-off-image",
            "Q",
            "refuse-before-Q-plus-one-query",
            afk_extractor_ro_capability_contract_id(challenge_count),
            "typed-classical-query-and-counterfactual-transitions",
        ),
    )


def afk_extractor_experiment_body_id(challenge_count: int) -> object:
    return single_experiment_body_id(
        afk_extractor_experiment_body_profile(challenge_count)
    )


def afk_execution_body_profile(
    challenge_count: int,
) -> ExperimentExecutionBodyProfile:
    randomness_law = afk_randomness_law_id(challenge_count)
    prover_space = ProbabilitySpaceProfile(
        "prover-experiment",
        ("adaptive-prover", "lazy-random-function", "verifier"),
        randomness_law,
        "prover-space-private-table",
        "extractor-experiment",
        "total-output-adversary-with-no-runtime-bound",
    )
    extractor_space = ProbabilitySpaceProfile(
        "extractor-experiment",
        (
            "uniform-extractor",
            "black-box-adaptive-prover-reruns",
            "lazy-random-function",
            "verifier",
        ),
        randomness_law,
        "extractor-space-private-table",
        "prover-experiment",
        "expected-polynomial-time-under-exact-afk-premises",
    )
    prover_body = afk_prover_experiment_body_profile(challenge_count)
    extractor_body = afk_extractor_experiment_body_profile(challenge_count)
    prover_body_id = single_experiment_body_id(prover_body)
    extractor_body_id_value = single_experiment_body_id(extractor_body)
    distribution_profile = DistributionEqualityProfile(
        prover_body_id,
        extractor_body_id_value,
        ("x", "pi", "aux", "v"),
        "exact-law-equality",
    )
    return ExperimentExecutionBodyProfile(
        "adaptive-afk-pair",
        (prover_space, extractor_space),
        ADAPTIVE_KNOWLEDGE_INTERFACE,
        afk_query_abi_id(challenge_count),
        AFK_OUTPUT_DISTRIBUTION_PROFILE,
        (
            AFK_PROVER_ACCEPT_EVENT,
            subject_bound_relation_success_event_id(AFK_THEOREM_SUBJECT_SCHEMA_ID),
        ),
        AFK_UNIFORM_BLACK_BOX_EXTRACTOR,
        distribution_equality_profile_id(distribution_profile),
        (
            "bind-fixed-setup-before-prover-and-oracle",
            "initialize-disjoint-empty-random-function-tables",
            "run-input-free-total-output-adaptive-prover",
            "count-every-classical-oracle-query",
            "lookup-or-uniform-insert-on-each-query",
            "verify-fiat-shamir-proof",
            "run-one-uniform-black-box-extractor-in-second-space",
            "preserve-x-pi-aux-v-law-and-append-w",
        ),
        ("x", "pi", "aux", "v", "w"),
        AFK_RESOURCE_BASIS,
        True,
        (prover_body_id, extractor_body_id_value),
        (prover_body, extractor_body),
        distribution_profile,
    )


def afk_execution_body_id(challenge_count: int) -> object:
    return experiment_execution_body_id(afk_execution_body_profile(challenge_count))


def subject_bound_experiment_body_id(
    challenge_count: int, subject_id: object, side: str
) -> object:
    """Instantiate one AFK experiment-body schema at an exact subject."""

    _id_datum(
        subject_id,
        ("analysis.family-member-subject", "analysis.concrete-family-member-subject"),
    )
    if side == "prover-experiment":
        base_id = afk_prover_experiment_body_id(challenge_count)
    elif side == "extractor-experiment":
        base_id = afk_extractor_experiment_body_id(challenge_count)
    else:
        raise ExperimentError("subject-bound AFK body has an unknown side")
    return _legacy_component_id(
        "analysis.experiment-body",
        k1.DatumRecord(
            (
                (0, k1.Symbol("subject-bound-afk-experiment-body")),
                (1, _id_datum(subject_id)),
                (2, _id_datum(base_id, "analysis.experiment-body")),
                (3, k1.Symbol(side)),
            )
        ),
    )


def subject_bound_afk_extractor_profile_id(subject_id: object) -> object:
    _id_datum(
        subject_id,
        ("analysis.family-member-subject", "analysis.concrete-family-member-subject"),
    )
    subject_kind = (
        "analysis.concrete-family-member-subject"
        if subject_id.subject_kind
        == _LOCAL_COMPONENT_KIND_ALIASES["analysis.concrete-family-member-subject"]
        else "analysis.family-member-subject"
    )
    profile = AFK_EXTRACTOR_PROFILE_BODY
    return _analysis_id(
        "analysis.extractor-profile",
        AnalysisExtractorProfileBodyV0(
            k1.DatumRecord(
                ((0, _symbol_seq(profile.inputs)), (1, _symbol_seq(profile.outputs)))
            ),
            k1.DatumRecord(
                (
                    (0, k1.Symbol("extractor-private-state")),
                    (1, k1.Symbol("extractor-private-randomness")),
                )
            ),
            _symbol_seq(profile.oracle_rights),
            _counterfactual_rights_for_capabilities(profile.oracle_rights),
            k1.Symbol("preserve-fixed-prover-strategy-and-source-state"),
            _symbol_seq(profile.preserves),
            k1.Symbol(_ascii(profile.success_event, "extractor success")),
            k1.DatumRecord(
                (
                    (
                        0,
                        k1.Symbol(
                            _ascii(profile.termination_law, "extractor termination")
                        ),
                    ),
                    (1, _symbol_seq(profile.resource_dimensions)),
                )
            ),
            k1.DatumRecord(
                (
                    (0, _symbol_seq(profile.forbidden_inputs)),
                    (
                        1,
                        k1.Symbol(
                            _ascii(
                                profile.prover_rerun_coin_law, "prover rerun coin law"
                            )
                        ),
                    ),
                    (2, profile.uniform_across_provers),
                    (3, k1.Symbol("adaptive-knowledge-soundness-q-lt-n")),
                    (
                        4,
                        _embedded_component_datum(subject_id, subject_kind),
                    ),
                )
            ),
        ),
    )


def subject_bound_afk_distribution_law_id(
    challenge_count: int, subject_id: object
) -> object:
    _id_datum(
        subject_id,
        ("analysis.family-member-subject", "analysis.concrete-family-member-subject"),
    )
    return distribution_equality_profile_id(
        DistributionEqualityProfile(
            subject_bound_experiment_body_id(
                challenge_count, subject_id, "prover-experiment"
            ),
            subject_bound_experiment_body_id(
                challenge_count, subject_id, "extractor-experiment"
            ),
            ("x", "pi", "aux", "v"),
            "exact-law-equality",
        )
    )


def subject_bound_afk_adversary_running_algorithm_id(
    challenge_count: int, subject_id: object
) -> object:
    _id_datum(
        subject_id,
        ("analysis.family-member-subject", "analysis.concrete-family-member-subject"),
    )
    return _legacy_component_id(
        "analysis.adversary-running-algorithm",
        k1.DatumRecord(
            (
                (0, k1.Symbol("subject-bound-afk-adversary-running-algorithm")),
                (1, _id_datum(subject_id)),
                (
                    2,
                    _id_datum(
                        afk_adversary_running_algorithm_id(challenge_count),
                        "analysis.adversary-running-algorithm",
                    ),
                ),
                (
                    3,
                    _id_datum(
                        subject_bound_experiment_body_id(
                            challenge_count, subject_id, "prover-experiment"
                        ),
                        "analysis.experiment-body",
                    ),
                ),
            )
        ),
    )


def schnorr_pair_value_domain_id(k: int, challenge_count: int) -> object:
    if (
        type(k) is not int
        or k != 2
        or type(challenge_count) is not int
        or not 2 <= challenge_count <= 11
    ):
        raise ExperimentError("bounded Schnorr pair domain needs k=2 and 2 <= N <= 11")
    return value_domain_profile_id(
        ValueDomainProfile(
            "SchnorrSpecialSoundnessPair",
            "same-Y-and-A-distinct-legal-challenges-both-accepting-canonical-scalars",
            (("N", challenge_count), ("k", k), ("p", 23), ("q", 11)),
        )
    )


def afk_query_bound_domain_id(challenge_count: int) -> object:
    if type(challenge_count) is not int or challenge_count < 2:
        raise ExperimentError("AFK query domain requires N >= 2")
    return value_domain_profile_id(
        ValueDomainProfile(
            "QueryCount-AdversaryRO",
            "zero-less-than-or-equal-Q-strictly-less-than-N",
            (("N", challenge_count),),
        )
    )


def fresh_randomness_law_id(challenge_count: int) -> object:
    return distribution_profile_id(
        FiniteUniformChallengeLaw(
            tuple(range(challenge_count)),
            Fraction(1, challenge_count),
            RandomnessOwnership.VERIFIER,
            ("prover-state", "commitment", "private-randomness"),
            "fresh-public-coin-request-only",
            False,
            (),
            "no-oracle-table",
            "not-applicable",
            "one-independent-verifier-draw",
            False,
            True,
            False,
        )
    )


def afk_randomness_law_id(challenge_count: int) -> object:
    return distribution_profile_id(
        FiniteUniformChallengeLaw(
            tuple(range(challenge_count)),
            Fraction(1, challenge_count),
            RandomnessOwnership.RANDOM_ORACLE,
            ("adaptive-prover-state", "oracle-query-history-before-new-index"),
            "classical-query-only",
            True,
            (),
            "persistent-finite-map-index-to-challenge",
            "lookup-return-stored-value",
            "uniform-sample-insert-return",
            True,
            True,
            True,
        )
    )


def lazy_random_function_trace(
    challenge_count: int,
    query_indices: tuple[bytes, ...],
    fresh_draws: tuple[int, ...],
) -> tuple[int, ...]:
    """Execute one realized adaptive lazy-random-function trace.

    `query_indices` may contain any raw byte strings, including indices
    outside the verifier image.  A fresh draw is consumed only for the first
    occurrence of each byte-equal index; repeats return the stored value.
    This executes the ideal finite law only and says nothing about SHA-256 or
    the imported transcript-construction correspondence.
    """

    if type(challenge_count) is not int or challenge_count < 2:
        raise ExperimentError("lazy random function requires N >= 2")
    if any(
        type(index) is not bytes or len(index) > k1.MAX_CANONICAL_BYTES
        for index in query_indices
    ):
        raise ExperimentError("random-oracle query indices must be bounded exact bytes")
    if any(
        type(draw) is not int or not 0 <= draw < challenge_count for draw in fresh_draws
    ):
        raise ExperimentError("lazy random-function draws are outside C_N")
    table: dict[bytes, int] = {}
    outputs: list[int] = []
    draw_ordinal = 0
    for index in query_indices:
        if index not in table:
            if draw_ordinal >= len(fresh_draws):
                raise ExperimentError("one fresh oracle index lacks its uniform draw")
            table[index] = fresh_draws[draw_ordinal]
            draw_ordinal += 1
        outputs.append(table[index])
    if draw_ordinal != len(fresh_draws):
        raise ExperimentError(
            "unused fresh draws would change the modeled probability space"
        )
    return tuple(outputs)


class OracleCallActor(str, Enum):
    ADAPTIVE_PROVER = "adaptive-prover"
    VERIFIER = "verifier"


@dataclass(frozen=True)
class ClassicalOracleCall:
    actor: OracleCallActor
    index: bytes


@dataclass(frozen=True)
class ExactVerifierAcceptanceReceipt:
    receipt_id: bytes
    experiment_id: bytes
    invocation_ordinal: int
    source_projection_id: object
    profile_id: object
    correspondence_id: object
    target_index: bytes
    transcript: SchnorrTranscript
    check_coordinate: str
    terminal_coordinate: str
    _token: object = field(repr=False, compare=False)


@dataclass(frozen=True)
class BaselineExecutionReceipt:
    experiment_id: bytes
    frame_id: bytes
    strategy_root_id: bytes
    tape_lineage_id: bytes
    table_lineage_id: bytes
    table_state_before_id: bytes
    table_state_after_id: bytes
    target_index: bytes
    target_value: int
    transcript: SchnorrTranscript
    verifier_acceptance: ExactVerifierAcceptanceReceipt
    oracle_calls: tuple[ClassicalOracleCall, ...]
    oracle_outputs: tuple[int, ...]
    adversary_query_count: int
    invocation_ordinal: int
    _token: object = field(repr=False, compare=False)


@dataclass(frozen=True)
class ProgrammedSiblingFrame:
    experiment_id: bytes
    frame_id: bytes
    baseline_frame_id: bytes
    strategy_root_id: bytes
    tape_lineage_id: bytes
    table_lineage_id: bytes
    table_state_id: bytes
    target_index: bytes
    programmed_value: int
    _issuer: object = field(repr=False, compare=False)


@dataclass(frozen=True)
class RerunExecutionReceipt:
    experiment_id: bytes
    frame_id: bytes
    programmed_frame_id: bytes
    baseline_frame_id: bytes
    strategy_root_id: bytes
    tape_lineage_id: bytes
    table_lineage_id: bytes
    table_state_before_id: bytes
    table_state_after_id: bytes
    target_index: bytes
    programmed_value: int
    transcript: SchnorrTranscript
    verifier_acceptance: ExactVerifierAcceptanceReceipt
    oracle_calls: tuple[ClassicalOracleCall, ...]
    oracle_outputs: tuple[int, ...]
    adversary_query_count: int
    invocation_ordinal: int
    _token: object = field(repr=False, compare=False)


@dataclass(frozen=True)
class CounterfactualExecutionCapability:
    operation: CounterfactualOperation
    experiment_id: bytes
    contract_id: object
    baseline_frame_id: bytes
    strategy_root_id: bytes
    tape_lineage_id: bytes
    table_lineage_id: bytes
    programmed_frame: ProgrammedSiblingFrame | None
    required_state_ordinal: int | None
    _token: object = field(repr=False, compare=False)


@dataclass(frozen=True)
class ExtractorExperimentState:
    experiment_id: bytes
    contract_id: object
    challenge_count: int
    query_bound: int
    strategy_root_id: bytes
    tape_lineage_id: bytes
    table_lineage_id: bytes
    table_state_id: bytes
    shared_table: tuple[tuple[bytes, int], ...]
    baseline: BaselineExecutionReceipt | None
    programmed_values: tuple[int, ...]
    consumed_programmed_frame_ids: tuple[bytes, ...]
    adversary_invocation_count: int
    state_ordinal: int
    _issuer: object = field(repr=False, compare=False)


@dataclass(frozen=True)
class AcceptedSiblingPair:
    experiment_id: bytes
    target_index: bytes
    transcripts: tuple[SchnorrTranscript, SchnorrTranscript]
    frame_ids: tuple[bytes, bytes]
    strategy_root_id: bytes
    tape_lineage_id: bytes
    table_lineage_id: bytes


_COUNTERFACTUAL_OCCURRENCE_ISSUER = object()
_COUNTERFACTUAL_CAPABILITY_TOKENS: dict[object, CounterfactualExecutionCapability] = {}
_COUNTERFACTUAL_ACCEPTANCE_TOKENS: dict[object, ExactVerifierAcceptanceReceipt] = {}
_COUNTERFACTUAL_RUN_RECEIPT_TOKENS: dict[
    object, BaselineExecutionReceipt | RerunExecutionReceipt
] = {}
_CONSUMED_COUNTERFACTUAL_CAPABILITY_TOKENS: set[object] = set()
_COUNTERFACTUAL_CURRENT_STATES: dict[bytes, ExtractorExperimentState] = {}


def _register_counterfactual_capability(
    capability: CounterfactualExecutionCapability,
) -> CounterfactualExecutionCapability:
    _COUNTERFACTUAL_CAPABILITY_TOKENS[capability._token] = capability
    return capability


def _register_counterfactual_acceptance(
    receipt: ExactVerifierAcceptanceReceipt,
) -> ExactVerifierAcceptanceReceipt:
    _COUNTERFACTUAL_ACCEPTANCE_TOKENS[receipt._token] = receipt
    return receipt


def _register_counterfactual_run_receipt(
    receipt: BaselineExecutionReceipt | RerunExecutionReceipt,
) -> BaselineExecutionReceipt | RerunExecutionReceipt:
    _COUNTERFACTUAL_RUN_RECEIPT_TOKENS[receipt._token] = receipt
    return receipt


def _require_counterfactual_acceptance(
    receipt: ExactVerifierAcceptanceReceipt,
) -> None:
    if (
        type(receipt) is not ExactVerifierAcceptanceReceipt
        or _COUNTERFACTUAL_ACCEPTANCE_TOKENS.get(receipt._token) is not receipt
    ):
        raise ExperimentError("verifier acceptance receipt is absent or forged")


def _require_counterfactual_run_receipt(
    receipt: BaselineExecutionReceipt | RerunExecutionReceipt,
    expected_type: type[BaselineExecutionReceipt] | type[RerunExecutionReceipt],
) -> None:
    if (
        type(receipt) is not expected_type
        or _COUNTERFACTUAL_RUN_RECEIPT_TOKENS.get(receipt._token) is not receipt
    ):
        raise ExperimentError("counterfactual run receipt is absent or forged")


def _counterfactual_bytes(
    value: object, label: str, *, nonempty: bool = False
) -> bytes:
    if (
        type(value) is not bytes
        or len(value) > k1.MAX_CANONICAL_BYTES
        or (nonempty and not value)
    ):
        raise ExperimentError(f"{label} must be bounded exact bytes")
    return value


def _counterfactual_digest(label: str, *parts: bytes) -> bytes:
    digest = hashlib.sha256()
    domain = _ascii(label, "counterfactual occurrence domain").encode("ascii")
    digest.update(len(domain).to_bytes(8, "big"))
    digest.update(domain)
    for part in parts:
        if type(part) is not bytes:
            raise ExperimentError("counterfactual occurrence digest input is not bytes")
        digest.update(len(part).to_bytes(8, "big"))
        digest.update(part)
    return digest.digest()


def _counterfactual_nat(value: int, label: str) -> bytes:
    if type(value) is not int or value < 0:
        raise ExperimentError(f"{label} must be a natural")
    return str(value).encode("ascii")


def _canonical_oracle_table(
    entries: Iterable[tuple[bytes, int]], challenge_count: int
) -> tuple[tuple[bytes, int], ...]:
    materialized = tuple(entries)
    if any(
        type(item) is not tuple
        or len(item) != 2
        or type(item[0]) is not bytes
        or len(item[0]) > k1.MAX_CANONICAL_BYTES
        or type(item[1]) is not int
        or not 0 <= item[1] < challenge_count
        for item in materialized
    ):
        raise ExperimentError("random-oracle table has an invalid exact entry")
    ordered = tuple(sorted(materialized, key=lambda item: item[0]))
    if len({index for index, _ in ordered}) != len(ordered):
        raise ExperimentError("random-oracle table repeats an exact index")
    return ordered


def _oracle_table_state_id(
    table_lineage_id: bytes,
    entries: tuple[tuple[bytes, int], ...],
) -> bytes:
    parts: list[bytes] = [table_lineage_id]
    for index, value in entries:
        parts.extend((index, _counterfactual_nat(value, "oracle table value")))
    return _counterfactual_digest("analysis.counterfactual-oracle-table-state", *parts)


def _require_extractor_experiment_state(
    state: ExtractorExperimentState,
    *,
    require_current: bool = True,
) -> None:
    if (
        type(state) is not ExtractorExperimentState
        or state._issuer is not _COUNTERFACTUAL_OCCURRENCE_ISSUER
    ):
        raise ExperimentError("extractor experiment state was not issued here")
    if (
        require_current
        and _COUNTERFACTUAL_CURRENT_STATES.get(state.experiment_id) is not state
    ):
        raise ExperimentError("extractor experiment state is no longer current")
    if (
        type(state.challenge_count) is not int
        or state.challenge_count < 2
        or type(state.query_bound) is not int
        or not 0 <= state.query_bound < state.challenge_count
        or state.contract_id
        != afk_extractor_ro_capability_contract_id(state.challenge_count)
    ):
        raise ExperimentError("extractor experiment parameters were substituted")
    for value, label in (
        (state.experiment_id, "experiment identity"),
        (state.strategy_root_id, "strategy-root identity"),
        (state.tape_lineage_id, "tape lineage"),
        (state.table_lineage_id, "table lineage"),
        (state.table_state_id, "table-state identity"),
    ):
        if type(value) is not bytes or len(value) != hashlib.sha256().digest_size:
            raise ExperimentError(f"{label} has the wrong shape")
    canonical_table = _canonical_oracle_table(state.shared_table, state.challenge_count)
    if canonical_table != state.shared_table or state.table_state_id != (
        _oracle_table_state_id(state.table_lineage_id, canonical_table)
    ):
        raise ExperimentError("extractor experiment table state was substituted")
    if (
        type(state.adversary_invocation_count) is not int
        or state.adversary_invocation_count < 0
        or type(state.state_ordinal) is not int
        or state.state_ordinal < 0
        or any(
            type(value) is not int or not 0 <= value < state.challenge_count
            for value in state.programmed_values
        )
        or len(set(state.programmed_values)) != len(state.programmed_values)
        or any(
            type(frame_id) is not bytes or len(frame_id) != hashlib.sha256().digest_size
            for frame_id in state.consumed_programmed_frame_ids
        )
    ):
        raise ExperimentError("extractor experiment accounting was substituted")
    if state.baseline is None:
        if (
            state.shared_table
            or state.programmed_values
            or state.consumed_programmed_frame_ids
            or state.adversary_invocation_count != 0
            or state.state_ordinal != 0
        ):
            raise ExperimentError("unstarted extractor experiment has live history")
    elif (
        type(state.baseline) is not BaselineExecutionReceipt
        or state.baseline.experiment_id != state.experiment_id
        or state.baseline.strategy_root_id != state.strategy_root_id
        or state.baseline.tape_lineage_id != state.tape_lineage_id
        or state.baseline.table_lineage_id != state.table_lineage_id
        or not state.programmed_values
        or state.programmed_values[0] != state.baseline.target_value
        or state.adversary_invocation_count < 1
    ):
        raise ExperimentError("extractor experiment baseline lineage was substituted")
    if state.baseline is not None:
        _require_counterfactual_run_receipt(state.baseline, BaselineExecutionReceipt)
        _require_counterfactual_acceptance(state.baseline.verifier_acceptance)


def _register_initial_extractor_experiment_state(
    state: ExtractorExperimentState,
) -> ExtractorExperimentState:
    _require_extractor_experiment_state(state, require_current=False)
    _COUNTERFACTUAL_CURRENT_STATES[state.experiment_id] = state
    return state


def _advance_extractor_experiment_state(
    prior: ExtractorExperimentState,
    successor: ExtractorExperimentState,
) -> ExtractorExperimentState:
    _require_extractor_experiment_state(prior)
    _require_extractor_experiment_state(successor, require_current=False)
    if successor.experiment_id != prior.experiment_id:
        raise ExperimentError("extractor state transition changed experiment")
    _COUNTERFACTUAL_CURRENT_STATES[prior.experiment_id] = successor
    return successor


def begin_extractor_experiment(
    challenge_count: int,
    query_bound: int,
    *,
    invocation_nonce: bytes,
    strategy_root: bytes,
    prover_tape_nonce: bytes,
) -> ExtractorExperimentState:
    """Begin one exact extractor invocation with fresh caller-owned nonces.

    This finite instrument does not sample randomness.  The caller supplies a
    fresh invocation nonce and a fresh prover-tape nonce for each experiment;
    their raw values are retained in no state field.
    """

    if type(challenge_count) is not int or challenge_count < 2:
        raise ExperimentError("counterfactual experiment requires N >= 2")
    if type(query_bound) is not int or not 0 <= query_bound < challenge_count:
        raise ExperimentError("counterfactual experiment requires 0 <= Q < N")
    invocation_nonce = _counterfactual_bytes(
        invocation_nonce, "extractor invocation nonce", nonempty=True
    )
    strategy_root = _counterfactual_bytes(
        strategy_root, "prover strategy root", nonempty=True
    )
    prover_tape_nonce = _counterfactual_bytes(
        prover_tape_nonce, "prover tape nonce", nonempty=True
    )
    contract_id = afk_extractor_ro_capability_contract_id(challenge_count)
    strategy_root_commitment = _counterfactual_digest(
        "analysis.counterfactual-strategy-root-commitment", strategy_root
    )
    tape_commitment = _counterfactual_digest(
        "analysis.counterfactual-prover-tape-commitment", prover_tape_nonce
    )
    experiment_id = _counterfactual_digest(
        "analysis.counterfactual-extractor-experiment",
        contract_id.internal_reference(),
        invocation_nonce,
        _counterfactual_nat(challenge_count, "challenge count"),
        _counterfactual_nat(query_bound, "query bound"),
        strategy_root_commitment,
        tape_commitment,
    )
    strategy_root_id = _counterfactual_digest(
        "analysis.counterfactual-strategy-root",
        experiment_id,
        strategy_root_commitment,
    )
    tape_lineage_id = _counterfactual_digest(
        "analysis.counterfactual-prover-tape", experiment_id, tape_commitment
    )
    table_lineage_id = _counterfactual_digest(
        "analysis.counterfactual-oracle-table-lineage", experiment_id
    )
    empty_table: tuple[tuple[bytes, int], ...] = ()
    state = ExtractorExperimentState(
        experiment_id,
        contract_id,
        challenge_count,
        query_bound,
        strategy_root_id,
        tape_lineage_id,
        table_lineage_id,
        _oracle_table_state_id(table_lineage_id, empty_table),
        empty_table,
        None,
        (),
        (),
        0,
        0,
        _COUNTERFACTUAL_OCCURRENCE_ISSUER,
    )
    return _register_initial_extractor_experiment_state(state)


def _execute_counterfactual_oracle_calls(
    state: ExtractorExperimentState,
    calls: tuple[ClassicalOracleCall, ...],
    fresh_draws: tuple[int, ...],
    *,
    target_overlay: tuple[bytes, int] | None,
) -> tuple[tuple[tuple[bytes, int], ...], tuple[int, ...], int, bool]:
    _require_extractor_experiment_state(state)
    if type(calls) is not tuple or any(
        type(call) is not ClassicalOracleCall
        or type(call.actor) is not OracleCallActor
        or type(call.index) is not bytes
        or len(call.index) > k1.MAX_CANONICAL_BYTES
        for call in calls
    ):
        raise ExperimentError("counterfactual oracle call sequence is not typed")
    if type(fresh_draws) is not tuple or any(
        type(draw) is not int or not 0 <= draw < state.challenge_count
        for draw in fresh_draws
    ):
        raise ExperimentError("counterfactual fresh draws are outside C_N")
    if target_overlay is not None:
        target_index = _counterfactual_bytes(
            target_overlay[0], "programmed oracle index"
        )
        target_value = target_overlay[1]
        if type(target_value) is not int or not (
            0 <= target_value < state.challenge_count
        ):
            raise ExperimentError("programmed oracle value is outside C_N")
    else:
        target_index = b""
        target_value = -1
    table = dict(state.shared_table)
    outputs: list[int] = []
    draw_ordinal = 0
    adversary_queries = 0
    target_seen_by_prover = False
    for call in calls:
        if call.actor is OracleCallActor.ADAPTIVE_PROVER:
            if adversary_queries >= state.query_bound:
                raise ExperimentError("counterfactual run would exceed Q")
            adversary_queries += 1
            if target_overlay is not None and call.index == target_index:
                target_seen_by_prover = True
        if target_overlay is not None and call.index == target_index:
            output = target_value
        elif call.index in table:
            output = table[call.index]
        else:
            if draw_ordinal >= len(fresh_draws):
                raise ExperimentError("one fresh oracle index lacks its uniform draw")
            output = fresh_draws[draw_ordinal]
            draw_ordinal += 1
            table[call.index] = output
        outputs.append(output)
    if draw_ordinal != len(fresh_draws):
        raise ExperimentError(
            "unused fresh draws would change the modeled probability space"
        )
    return (
        _canonical_oracle_table(table.items(), state.challenge_count),
        tuple(outputs),
        adversary_queries,
        target_seen_by_prover,
    )


def _exact_counterfactual_query_carrier(
    source: FreshFsRelationSource,
    profile: SchnorrSpecialSoundnessProfile,
    correspondence: FSCorrespondence,
    transcript: SchnorrTranscript,
) -> bytes:
    require_schnorr_special_soundness_profile(source, profile)
    fs_correspondence_id(correspondence)
    if (
        native_subject_projection_id(source)
        != native_subject_projection_id(correspondence.fixed_public_setup._source)
        or correspondence.source_property_profile_id != profile.profile_id
    ):
        raise ExperimentError("verifier correspondence is detached from its source")
    if type(transcript) is not SchnorrTranscript:
        raise ExperimentError(
            "counterfactual verifier needs one exact Schnorr transcript"
        )
    selected = tuple(
        entry
        for entry in correspondence.query_encoding_table
        if entry.statement == transcript.statement
        and entry.commitment == transcript.commitment
    )
    if len(selected) != 1:
        raise ExperimentError(
            "transcript has no unique checked challenge-query carrier"
        )
    return selected[0].k2_challenge_query_carrier


def _issue_exact_verifier_acceptance(
    state: ExtractorExperimentState,
    source: FreshFsRelationSource,
    profile: SchnorrSpecialSoundnessProfile,
    correspondence: FSCorrespondence,
    transcript: SchnorrTranscript,
    target_index: bytes,
) -> ExactVerifierAcceptanceReceipt:
    _require_extractor_experiment_state(state)
    expected_target = _exact_counterfactual_query_carrier(
        source, profile, correspondence, transcript
    )
    if target_index != expected_target:
        raise ExperimentError("counterfactual target is not the checked query carrier")
    if (
        type(transcript.challenge) is not int
        or not 0 <= transcript.challenge < state.challenge_count
        or not exact_fresh_transcript_accepts(source, profile, transcript)
    ):
        raise ExperimentError(
            "exact protocol Check and Terminal do not accept the transcript"
        )
    source_projection_id = native_subject_projection_id(source)
    correspondence_id = fs_correspondence_id(correspondence)
    receipt_id = _counterfactual_digest(
        "analysis.counterfactual-exact-verifier-acceptance",
        state.experiment_id,
        _counterfactual_nat(
            state.adversary_invocation_count, "adversary invocation ordinal"
        ),
        source_projection_id.internal_reference(),
        profile.profile_id.internal_reference(),
        correspondence_id.internal_reference(),
        target_index,
        _counterfactual_nat(transcript.statement, "Schnorr statement"),
        _counterfactual_nat(transcript.commitment, "Schnorr commitment"),
        _counterfactual_nat(transcript.challenge, "Schnorr challenge"),
        _counterfactual_nat(transcript.response, "Schnorr response"),
        profile.check_coordinate.encode("ascii"),
        profile.terminal_coordinate.encode("ascii"),
    )
    receipt = ExactVerifierAcceptanceReceipt(
        receipt_id,
        state.experiment_id,
        state.adversary_invocation_count,
        source_projection_id,
        profile.profile_id,
        correspondence_id,
        target_index,
        transcript,
        profile.check_coordinate,
        profile.terminal_coordinate,
        object(),
    )
    return _register_counterfactual_acceptance(receipt)


def run_baseline(
    state: ExtractorExperimentState,
    calls: tuple[ClassicalOracleCall, ...],
    fresh_draws: tuple[int, ...],
    *,
    source: FreshFsRelationSource,
    profile: SchnorrSpecialSoundnessProfile,
    correspondence: FSCorrespondence,
    transcript: SchnorrTranscript,
) -> tuple[
    ExtractorExperimentState,
    BaselineExecutionReceipt,
    CounterfactualExecutionCapability,
]:
    _require_extractor_experiment_state(state)
    if state.baseline is not None:
        raise ExperimentError("one extractor experiment has exactly one baseline")
    target_index = _exact_counterfactual_query_carrier(
        source, profile, correspondence, transcript
    )
    next_table, outputs, query_count, _ = _execute_counterfactual_oracle_calls(
        state, calls, fresh_draws, target_overlay=None
    )
    prover_target_ordinals = tuple(
        ordinal
        for ordinal, call in enumerate(calls)
        if call.actor is OracleCallActor.ADAPTIVE_PROVER and call.index == target_index
    )
    if not prover_target_ordinals:
        raise ExperimentError("baseline target was not queried by the prover")
    target_value = outputs[prover_target_ordinals[0]]
    if target_value != transcript.challenge:
        raise ExperimentError("baseline oracle answer disagrees with the transcript")
    verifier_acceptance = _issue_exact_verifier_acceptance(
        state, source, profile, correspondence, transcript, target_index
    )
    table_after_id = _oracle_table_state_id(state.table_lineage_id, next_table)
    frame_id = _counterfactual_digest(
        "analysis.counterfactual-baseline-frame",
        state.experiment_id,
        state.contract_id.internal_reference(),
        state.strategy_root_id,
        state.tape_lineage_id,
        state.table_lineage_id,
        _counterfactual_nat(state.state_ordinal, "state ordinal"),
        state.table_state_id,
        table_after_id,
        target_index,
        verifier_acceptance.receipt_id,
    )
    receipt = BaselineExecutionReceipt(
        state.experiment_id,
        frame_id,
        state.strategy_root_id,
        state.tape_lineage_id,
        state.table_lineage_id,
        state.table_state_id,
        table_after_id,
        target_index,
        target_value,
        transcript,
        verifier_acceptance,
        calls,
        outputs,
        query_count,
        state.adversary_invocation_count,
        object(),
    )
    receipt = _register_counterfactual_run_receipt(receipt)
    assert type(receipt) is BaselineExecutionReceipt
    next_state = replace(
        state,
        table_state_id=table_after_id,
        shared_table=next_table,
        baseline=receipt,
        programmed_values=(target_value,),
        adversary_invocation_count=state.adversary_invocation_count + 1,
        state_ordinal=state.state_ordinal + 1,
    )
    next_state = _advance_extractor_experiment_state(state, next_state)
    capability = _register_counterfactual_capability(
        CounterfactualExecutionCapability(
            CounterfactualOperation.PROGRAM_SIBLING,
            state.experiment_id,
            state.contract_id,
            frame_id,
            state.strategy_root_id,
            state.tape_lineage_id,
            state.table_lineage_id,
            None,
            None,
            object(),
        )
    )
    return next_state, receipt, capability


def _require_counterfactual_capability(
    state: ExtractorExperimentState,
    capability: CounterfactualExecutionCapability,
    operation: CounterfactualOperation,
) -> None:
    _require_extractor_experiment_state(state)
    if (
        type(capability) is not CounterfactualExecutionCapability
        or _COUNTERFACTUAL_CAPABILITY_TOKENS.get(capability._token) is not capability
        or capability._token in _CONSUMED_COUNTERFACTUAL_CAPABILITY_TOKENS
        or capability.operation is not operation
        or capability.experiment_id != state.experiment_id
        or capability.contract_id != state.contract_id
        or capability.strategy_root_id != state.strategy_root_id
        or capability.tape_lineage_id != state.tape_lineage_id
        or capability.table_lineage_id != state.table_lineage_id
        or state.baseline is None
        or capability.baseline_frame_id != state.baseline.frame_id
        or (
            capability.required_state_ordinal is not None
            and capability.required_state_ordinal != state.state_ordinal
        )
    ):
        raise ExperimentError("counterfactual capability is unauthorized or stale")


def program_sibling(
    state: ExtractorExperimentState,
    capability: CounterfactualExecutionCapability,
    programmed_value: int,
) -> tuple[
    ExtractorExperimentState,
    ProgrammedSiblingFrame,
    CounterfactualExecutionCapability,
]:
    _require_counterfactual_capability(
        state, capability, CounterfactualOperation.PROGRAM_SIBLING
    )
    assert state.baseline is not None
    if (
        type(programmed_value) is not int
        or not 0 <= programmed_value < state.challenge_count
        or programmed_value in state.programmed_values
    ):
        raise ExperimentError(
            "programmed sibling value must be a new exact member of C_N"
        )
    frame_id = _counterfactual_digest(
        "analysis.counterfactual-programmed-sibling-frame",
        state.experiment_id,
        state.contract_id.internal_reference(),
        state.strategy_root_id,
        state.tape_lineage_id,
        state.table_lineage_id,
        _counterfactual_nat(state.state_ordinal, "state ordinal"),
        state.baseline.frame_id,
        state.table_state_id,
        state.baseline.target_index,
        _counterfactual_nat(programmed_value, "programmed value"),
    )
    frame = ProgrammedSiblingFrame(
        state.experiment_id,
        frame_id,
        state.baseline.frame_id,
        state.strategy_root_id,
        state.tape_lineage_id,
        state.table_lineage_id,
        state.table_state_id,
        state.baseline.target_index,
        programmed_value,
        _COUNTERFACTUAL_OCCURRENCE_ISSUER,
    )
    next_state = replace(
        state,
        programmed_values=state.programmed_values + (programmed_value,),
        state_ordinal=state.state_ordinal + 1,
    )
    next_state = _advance_extractor_experiment_state(state, next_state)
    rerun_capability = _register_counterfactual_capability(
        CounterfactualExecutionCapability(
            CounterfactualOperation.RERUN,
            state.experiment_id,
            state.contract_id,
            state.baseline.frame_id,
            state.strategy_root_id,
            state.tape_lineage_id,
            state.table_lineage_id,
            frame,
            next_state.state_ordinal,
            object(),
        )
    )
    return next_state, frame, rerun_capability


def rerun_programmed_sibling(
    state: ExtractorExperimentState,
    capability: CounterfactualExecutionCapability,
    calls: tuple[ClassicalOracleCall, ...],
    fresh_draws: tuple[int, ...],
    *,
    source: FreshFsRelationSource,
    profile: SchnorrSpecialSoundnessProfile,
    correspondence: FSCorrespondence,
    transcript: SchnorrTranscript,
) -> tuple[ExtractorExperimentState, RerunExecutionReceipt]:
    _require_counterfactual_capability(state, capability, CounterfactualOperation.RERUN)
    frame = capability.programmed_frame
    if (
        type(frame) is not ProgrammedSiblingFrame
        or frame._issuer is not _COUNTERFACTUAL_OCCURRENCE_ISSUER
        or frame.experiment_id != state.experiment_id
        or frame.baseline_frame_id != capability.baseline_frame_id
        or frame.strategy_root_id != state.strategy_root_id
        or frame.tape_lineage_id != state.tape_lineage_id
        or frame.table_lineage_id != state.table_lineage_id
        or frame.table_state_id != state.table_state_id
        or frame.frame_id in state.consumed_programmed_frame_ids
    ):
        raise ExperimentError("programmed sibling frame is foreign, stale, or consumed")
    expected_target = _exact_counterfactual_query_carrier(
        source, profile, correspondence, transcript
    )
    if expected_target != frame.target_index:
        raise ExperimentError("rerun transcript selects another query carrier")
    if transcript.challenge != frame.programmed_value:
        raise ExperimentError("rerun transcript challenge is not the programmed value")
    next_table, outputs, query_count, target_seen = (
        _execute_counterfactual_oracle_calls(
            state,
            calls,
            fresh_draws,
            target_overlay=(frame.target_index, frame.programmed_value),
        )
    )
    if not target_seen:
        raise ExperimentError("rerun target was not queried by the prover")
    verifier_acceptance = _issue_exact_verifier_acceptance(
        state, source, profile, correspondence, transcript, frame.target_index
    )
    table_after_id = _oracle_table_state_id(state.table_lineage_id, next_table)
    receipt_id = _counterfactual_digest(
        "analysis.counterfactual-rerun-frame",
        state.experiment_id,
        state.contract_id.internal_reference(),
        state.strategy_root_id,
        state.tape_lineage_id,
        state.table_lineage_id,
        frame.frame_id,
        state.table_state_id,
        table_after_id,
        verifier_acceptance.receipt_id,
    )
    receipt = RerunExecutionReceipt(
        state.experiment_id,
        receipt_id,
        frame.frame_id,
        frame.baseline_frame_id,
        state.strategy_root_id,
        state.tape_lineage_id,
        state.table_lineage_id,
        state.table_state_id,
        table_after_id,
        frame.target_index,
        frame.programmed_value,
        transcript,
        verifier_acceptance,
        calls,
        outputs,
        query_count,
        state.adversary_invocation_count,
        object(),
    )
    receipt = _register_counterfactual_run_receipt(receipt)
    assert type(receipt) is RerunExecutionReceipt
    next_state = replace(
        state,
        table_state_id=table_after_id,
        shared_table=next_table,
        consumed_programmed_frame_ids=(
            state.consumed_programmed_frame_ids + (frame.frame_id,)
        ),
        adversary_invocation_count=state.adversary_invocation_count + 1,
        state_ordinal=state.state_ordinal + 1,
    )
    next_state = _advance_extractor_experiment_state(state, next_state)
    _CONSUMED_COUNTERFACTUAL_CAPABILITY_TOKENS.add(capability._token)
    return next_state, receipt


def derive_accepted_sibling_pair(
    source: FreshFsRelationSource,
    profile: SchnorrSpecialSoundnessProfile,
    baseline: BaselineExecutionReceipt,
    rerun: RerunExecutionReceipt,
) -> AcceptedSiblingPair:
    """Derive a canonical pair; this function grants no execution right."""

    _require_counterfactual_run_receipt(baseline, BaselineExecutionReceipt)
    _require_counterfactual_run_receipt(rerun, RerunExecutionReceipt)
    _require_counterfactual_acceptance(baseline.verifier_acceptance)
    _require_counterfactual_acceptance(rerun.verifier_acceptance)
    require_schnorr_special_soundness_profile(source, profile)
    if (
        baseline.experiment_id != rerun.experiment_id
        or baseline.frame_id != rerun.baseline_frame_id
        or baseline.strategy_root_id != rerun.strategy_root_id
        or baseline.tape_lineage_id != rerun.tape_lineage_id
        or baseline.table_lineage_id != rerun.table_lineage_id
        or baseline.target_index != rerun.target_index
        or baseline.target_value == rerun.programmed_value
        or baseline.verifier_acceptance.profile_id != profile.profile_id
        or rerun.verifier_acceptance.profile_id != profile.profile_id
    ):
        raise ExperimentError("accepted sibling-pair relation does not hold")
    ordered = tuple(
        sorted(
            (
                (baseline.transcript, baseline.frame_id),
                (rerun.transcript, rerun.frame_id),
            ),
            key=lambda item: k1.encode_datum(k1.Nat(item[0].challenge)),
        )
    )
    transcripts = (ordered[0][0], ordered[1][0])
    if not schnorr_admitted_pair_predicate(
        source, profile, transcripts[0], transcripts[1]
    ):
        raise ExperimentError("issued runs do not form one exact admitted pair")
    return AcceptedSiblingPair(
        baseline.experiment_id,
        baseline.target_index,
        transcripts,
        (ordered[0][1], ordered[1][1]),
        baseline.strategy_root_id,
        baseline.tape_lineage_id,
        baseline.table_lineage_id,
    )


def two_distinct_lazy_query_joint_law(
    challenge_count: int,
) -> tuple[tuple[tuple[int, int], Fraction], ...]:
    """Enumerate the exact ideal joint law at two distinct realized indices."""

    afk_randomness_law_id(challenge_count)
    mass = Fraction(1, challenge_count * challenge_count)
    return tuple(
        ((first, second), mass)
        for first in range(challenge_count)
        for second in range(challenge_count)
    )


def afk_query_abi_id(challenge_count: int) -> object:
    return query_abi_profile_id(
        replace(
            K2_AFK_ORACLE_QUERY_ABI_BODY,
            output_values=tuple(range(challenge_count)),
        )
    )


def afk_query_count_variable(
    challenge_count: int,
    subject_id: object = AFK_THEOREM_SUBJECT_SCHEMA_ID,
) -> QVariable:
    _id_datum(subject_id)
    return QVariable(
        "Q",
        QuantitativeSort.QUERY_COUNT_ADVERSARY_RO,
        AFK_ADVERSARY_RO_QUERY_DIMENSION_ID,
        afk_query_abi_id(challenge_count),
        subject_id,
        "all-calls-including-repeats-and-off-image",
    )


def afk_query_count_literal(
    value: int,
    challenge_count: int,
    subject_id: object = AFK_THEOREM_SUBJECT_SCHEMA_ID,
) -> QNatural:
    _id_datum(subject_id)
    return QNatural(
        value,
        QuantitativeSort.QUERY_COUNT_ADVERSARY_RO,
        AFK_ADVERSARY_RO_QUERY_DIMENSION_ID,
        afk_query_abi_id(challenge_count),
        subject_id,
        "all-calls-including-repeats-and-off-image",
    )


def fresh_zero_query_count() -> QNatural:
    return QNatural(
        0,
        QuantitativeSort.QUERY_COUNT_ADVERSARY_RO,
        FRESH_NO_ORACLE_QUERY_DIMENSION_ID,
        NO_ORACLE_QUERY_ABI,
        FRESH_THEOREM_SUBJECT_SCHEMA_ID,
        "no-random-oracle-calls",
    )


def fresh_special_soundness_model(
    *, k: int = 2, challenge_count: int = 8
) -> ExperimentModel:
    return ExperimentModel(
        SPECIAL_SOUNDNESS_PAIR_INTERFACE,
        StrategyClass.ACCEPTING_TRANSCRIPT_PAIR_DOMAIN,
        OracleModel.PUBLIC_COIN,
        RandomnessOwnership.VERIFIER,
        fresh_randomness_law_id(challenge_count),
        Scheduling.SINGLE_SESSION,
        StatementTiming.OUTER_UNIVERSAL,
        SCHNORR_SETUP_PROFILE,
        fresh_execution_body_id(challenge_count),
        FRESH_OUTPUT_DISTRIBUTION_PROFILE,
        NO_ORACLE_QUERY_ABI,
        FRESH_EXTRACTION_EVENT,
        FRESH_FAILURE_PROFILE,
        FRESH_RESOURCE_BASIS,
        (
            Quantifier(
                QuantifierKind.EXISTS_DETERMINISTIC_TRANSCRIPT_EXTRACTOR,
                "deterministic-transcript-extractor",
                SCHNORR_TRANSCRIPT_EXTRACTOR_PROFILE_ID,
            ),
            Quantifier(
                QuantifierKind.FOR_ALL_VALUE,
                "accepted-transcript-pair",
                schnorr_pair_value_domain_id(k, challenge_count),
            ),
        ),
        (("N", challenge_count), ("k", k)),
        fresh_zero_query_count(),
    )


def adaptive_rom_knowledge_model(
    *, k: int = 2, challenge_count: int = 8
) -> ExperimentModel:
    return ExperimentModel(
        ADAPTIVE_KNOWLEDGE_INTERFACE,
        StrategyClass.ADAPTIVE_CLASSICAL_ONLINE_PROVER,
        OracleModel.CLASSICAL_ROM,
        RandomnessOwnership.RANDOM_ORACLE,
        afk_randomness_law_id(challenge_count),
        Scheduling.SINGLE_SESSION,
        StatementTiming.ADAPTIVE_PROVER_OUTPUT,
        SCHNORR_SETUP_PROFILE,
        afk_execution_body_id(challenge_count),
        AFK_OUTPUT_DISTRIBUTION_PROFILE,
        afk_query_abi_id(challenge_count),
        AFK_EXTRACTION_EVENT,
        AFK_FAILURE_PROFILE,
        AFK_RESOURCE_BASIS,
        (
            Quantifier(
                QuantifierKind.EXISTS_POSITIVE_POLYNOMIAL,
                "q_KS",
                AFK_POSITIVE_POLYNOMIAL_DOMAIN_ID,
            ),
            Quantifier(
                QuantifierKind.EXISTS_UNIFORM_BLACK_BOX_EXTRACTOR,
                "E",
                AFK_UNIFORM_BLACK_BOX_EXTRACTOR,
            ),
            Quantifier(
                QuantifierKind.FOR_ALL_QUANTITATIVE_VALUE,
                "n",
                _afk_formula_parameter_domains(challenge_count)["n"],
            ),
            Quantifier(
                QuantifierKind.FOR_ALL_QUANTITATIVE_VALUE,
                "Q",
                _afk_formula_parameter_domains(challenge_count)["Q"],
            ),
            Quantifier(
                QuantifierKind.FOR_ALL_ADAPTIVE_PROVERS,
                "Pa",
                ADAPTIVE_KNOWLEDGE_INTERFACE,
            ),
        ),
        (("N", challenge_count), ("k", k)),
        afk_query_count_variable(challenge_count),
    )


def _require_exact_special_soundness_model(model: ExperimentModel) -> None:
    admit_experiment_model(model)
    parameters = _model_parameters(model)
    if set(parameters) != {"N", "k"}:
        raise ExperimentError("special-soundness model needs exact k and N parameters")
    if model != fresh_special_soundness_model(
        k=parameters["k"], challenge_count=parameters["N"]
    ):
        raise ExperimentError(
            "special-soundness model differs from the selected quantifier profile"
        )


def _require_exact_adaptive_knowledge_model(model: ExperimentModel) -> None:
    admit_experiment_model(model)
    parameters = _model_parameters(model)
    if set(parameters) != {"N", "k"}:
        raise ExperimentError("adaptive-ROM model needs exact k and N parameters")
    if model != adaptive_rom_knowledge_model(
        k=parameters["k"],
        challenge_count=parameters["N"],
    ):
        raise ExperimentError(
            "adaptive-ROM model differs from the selected quantifier profile"
        )


def k2_static_view_support_hypothesis_id(
    source: FreshFsRelationSource,
) -> object:
    """Form the named concrete challenge-domain correspondence goal.

    Owner-view availability is source ingress/support, not a semantic goal.
    The retained source premise is therefore the exact challenge-model
    correspondence over the authenticated PIR coordinates.
    """

    require_fresh_fs_relation_source(source)
    required_view_coordinates = (
        (
            "PublicBindingView",
            (source.fresh_binding.binding_id, source.fiat_shamir_binding.binding_id),
        ),
        ("StrategyDecisionView", (source.protocol_source.core_id,)),
        ("PublicCoinView", (source.protocol_source.fresh_protocol_id,)),
        ("EffectView", (source.protocol_source.core_id,)),
        ("ClaimReductionView", (source.fresh_binding.binding_id,)),
        (
            "ExecutionView",
            (
                source.protocol_source.fresh_protocol_id,
                source.protocol_source.fiat_shamir_protocol_id,
            ),
        ),
        ("TranscriptDeclarationView", (source.protocol_source.construction_id,)),
        (
            "RequiredInfluenceView",
            (source.protocol_source.core_id, source.protocol_source.construction_id),
        ),
        ("ChallengeTransitionView", (source.protocol_source.core_id,)),
        (
            "FSConstructionView",
            (
                source.protocol_source.construction_id,
                source.protocol_source.fiat_shamir_protocol_id,
            ),
        ),
    )
    model = fresh_special_soundness_model(k=2, challenge_count=8)
    return _exact_premise_goal_id(
        "challenge-domain-correspondence",
        (
            source.protocol_source.core_id,
            source.protocol_source.fresh_protocol_id,
            source.protocol_source.fiat_shamir_protocol_id,
        ),
        _semantic_experiment_context(
            (source_manifest_id(source.fresh_manifest),),
            (experiment_model_id(model),),
        ),
        k1.DatumRecord(
            (
                (0, k1.Symbol("assumed-owner-issued-k2-static-source-views")),
                (
                    1,
                    _id_datum(source.protocol_source.core_id, "pir.interactive-core"),
                ),
                (
                    2,
                    _id_datum(
                        source.protocol_source.construction_id,
                        "pir.transcript-construction",
                    ),
                ),
                (
                    3,
                    _id_datum(
                        source_manifest_id(source.pair_manifest),
                        "analysis.semantic-read-manifest",
                    ),
                ),
                (4, k1.BytesValue(k2.core_body(source.case.core))),
                (
                    5,
                    k1.BytesValue(
                        k2.construction_body(source.case.core, source.case.construction)
                    ),
                ),
                (
                    6,
                    k1.DatumSeq(
                        tuple(
                            k1.DatumRecord(
                                (
                                    (0, k1.Symbol(view_kind)),
                                    (
                                        1,
                                        k1.DatumSeq(
                                            tuple(
                                                _id_datum(owner_id)
                                                for owner_id in owner_ids
                                            )
                                        ),
                                    ),
                                    (
                                        2,
                                        k1.Symbol(
                                            "missing-owner-issued-carrier-assumed"
                                        ),
                                    ),
                                )
                            )
                            for view_kind, owner_ids in required_view_coordinates
                        )
                    ),
                ),
                (
                    7,
                    k1.Symbol(
                        "PIR-ProverView-is-runtime-prefix-only-and-does-not-close-these-views"
                    ),
                ),
            )
        ),
        selected_profile=ANALYSIS_PROPERTY_PROFILE,
    )


def fresh_uniformity_correspondence_hypothesis_id(
    source: FreshFsRelationSource, model: ExperimentModel
) -> object:
    """Reject the obsolete pointwise Fresh-uniformity pseudo premise."""

    require_fresh_fs_relation_source(source)
    _require_exact_special_soundness_model(model)
    raise PropertyError("Fresh uniformity is an AFK family-applicability obligation")


# ---------------------------------------------------------------------------
# Analysis Question -> Goal -> Proposition and conditional fixture support
# ---------------------------------------------------------------------------


class PropertyFamily(str, Enum):
    K_OUT_OF_N_SPECIAL_SOUNDNESS = "k-out-of-n-special-soundness"
    ADAPTIVE_NIROP_KNOWLEDGE_SOUNDNESS_Q_LT_N = (
        "adaptive-nirop-knowledge-soundness:q-strictly-less-than-challenge-cardinality"
    )


def family_profile_id(family: PropertyFamily) -> object:
    if type(family) is not PropertyFamily:
        raise PropertyError("unknown Analysis property family")
    labels = {
        PropertyFamily.K_OUT_OF_N_SPECIAL_SOUNDNESS: "k-out-of-n-special-soundness",
        PropertyFamily.ADAPTIVE_NIROP_KNOWLEDGE_SOUNDNESS_Q_LT_N: "adaptive-knowledge-extraction-at-fixed-length-q-lt-n",
    }
    owner = ANALYSIS_PROPERTY_PROFILE
    return analysis_profile_declaration_ref(
        owner,
        owner,
        "analysis.property-family",
        labels[family],
    )


def _family_declaration_ref(
    selected_profile: object,
    label: str,
    *,
    owner_profile: object,
) -> object:
    return analysis_profile_declaration_ref(
        selected_profile,
        owner_profile,
        "analysis.property-family",
        label,
    )


_SCHNORR_STATEMENT_INTERFACE_INPUT = next(
    item
    for item in _SCHNORR_OWNER_CASE_FOR_NESTED_COORDINATES.interface.inputs
    if item.core_input == "statement"
)
_SCHNORR_STATEMENT_RELATION_SLOT = (
    _SCHNORR_OWNER_CASE_FOR_NESTED_COORDINATES.relation_interfaces[0].public_instance[0]
)
SCHNORR_FIXED_WIDTH_STATEMENT_CODEC_ID = _SCHNORR_STATEMENT_INTERFACE_INPUT.codec_id


def fixed_family_member_selector_id(source: FreshFsRelationSource, axis: str) -> object:
    require_fresh_fs_relation_source(source)
    if axis == "fresh":
        protocol_id = source.protocol_source.fresh_protocol_id
        binding_id = source.fresh_binding.binding_id
    elif axis == "fiat-shamir":
        protocol_id = source.protocol_source.fiat_shamir_protocol_id
        binding_id = source.fiat_shamir_binding.binding_id
    else:
        raise PropertyError("family-member selector axis is unsupported")
    return _fixed_family_member_selector_id(axis, protocol_id, binding_id)


def _fixed_family_member_selector_id(
    axis: str, protocol_id: object, binding_id: object
) -> object:
    if axis not in ("fresh", "fiat-shamir"):
        raise PropertyError("family-member selector axis is unsupported")
    protocol_family_id = (
        SCHNORR_FRESH_PROTOCOL_FAMILY_ID
        if axis == "fresh"
        else SCHNORR_FIAT_SHAMIR_PROTOCOL_FAMILY_ID
    )
    return _legacy_component_id(
        "analysis.family-member-selector",
        k1.DatumRecord(
            (
                (
                    0,
                    _id_datum(protocol_family_id, "pir.protocol"),
                ),
                (
                    1,
                    _id_datum(
                        SCHNORR_RELATION_FAMILY_ID,
                        "relations.definition",
                    ),
                ),
                (2, k1.Symbol("fixed-member-n0-bounded-witness-only")),
                (3, k1.Nat(1)),
                (4, k1.Symbol("statement-length-unit-octet")),
                (
                    5,
                    k1.DatumRecord(
                        (
                            (
                                0,
                                _id_datum(
                                    SCHNORR_FIXED_WIDTH_STATEMENT_CODEC_ID,
                                    "foundation.canonical-algorithm",
                                ),
                            ),
                            (
                                1,
                                k1.value_type_datum(
                                    _SCHNORR_STATEMENT_RELATION_SLOT.value_type
                                ),
                            ),
                            (2, k1.Nat(1)),
                            (3, k1.Nat(8)),
                        )
                    ),
                ),
                (
                    6,
                    k1.Symbol(
                        "every-canonical-subgroup-statement-encodes-to-one-octet"
                    ),
                ),
                (7, _id_datum(protocol_id, "pir.protocol")),
                (8, _id_datum(binding_id, "relations.protocol-binding")),
                (9, k1.Nat(23)),
                (10, k1.Nat(11)),
                (11, k1.Nat(2)),
                (12, k1.Nat(8)),
                (
                    13,
                    k1.Symbol(
                        "all-other-n-members-remain-an-explicit-family-hypothesis"
                    ),
                ),
            )
        ),
    )


@dataclass(frozen=True)
class SpecialSoundnessQuestionPayload:
    profile_id: object
    extraction_arity: int
    challenge_count: int
    extractor_profile_id: object
    extractor_algorithm_id: object


@dataclass(frozen=True)
class AFKKnowledgeSoundnessQuestionPayload:
    extractor_profile_id: object
    distribution_law_id: object
    prover_output_law: tuple[str, ...]
    extractor_output_law: tuple[str, ...]
    success_event_id: object
    comparator: str
    success_probability_formula_id: object
    knowledge_error_formula_id: object
    success_lower_bound_formula_id: object
    expected_invocation_bound_id: object


QuestionFamilyPayload = (
    SpecialSoundnessQuestionPayload | AFKKnowledgeSoundnessQuestionPayload
)


@dataclass(frozen=True)
class AnalysisQuestion:
    family: PropertyFamily
    subject_id: object
    scope: str
    protocol_family_id: object
    relation_family_id: object
    fixed_member_selector_id: object
    protocol_id: object
    relation_binding_id: object
    model_id: object
    semantic_read_closure_id: object
    quantifiers: tuple[Quantifier, ...]
    family_payload: QuestionFamilyPayload


@dataclass(frozen=True)
class SpecialSoundnessConclusion:
    profile_id: object
    extraction_arity: int
    challenge_count: int
    extractor_profile_id: object
    extractor_algorithm_id: object


@dataclass(frozen=True)
class AFKKnowledgeSoundnessConclusion:
    """Basis-neutral AFK Definition-10 target formula references.

    The signed expression is the right-hand side of a probability inequality;
    it is deliberately not itself a Probability.  The theorem-owned q=1
    substitution lives in the qualified semantic basis, never in this ordinary
    property conclusion.
    """

    extractor_profile_id: object
    distribution_law_id: object
    prover_output_law: tuple[str, ...]
    extractor_output_law: tuple[str, ...]
    success_event_id: object
    comparator: str
    success_probability_formula_id: object
    knowledge_error_formula_id: object
    success_lower_bound_formula_id: object
    expected_invocation_bound_id: object


PropertyConclusion = SpecialSoundnessConclusion | AFKKnowledgeSoundnessConclusion


@dataclass(frozen=True)
class AnalysisGoal:
    question: AnalysisQuestion
    conclusion: PropertyConclusion


@dataclass(frozen=True)
class AnalysisProposition:
    goal: AnalysisGoal
    hypotheses: tuple[object, ...]


def _hypothesis_key(identifier: object) -> bytes:
    _id_datum(identifier, "analysis.goal")
    return identifier.internal_reference()


def canonical_hypotheses(hypotheses: Iterable[object]) -> tuple[object, ...]:
    values = tuple(hypotheses)
    if len(values) > MAX_HYPOTHESES:
        raise PropertyError("hypothesis context exceeds its finite bound")
    ordered = tuple(sorted(values, key=_hypothesis_key))
    if len(ordered) != len(set(ordered)):
        raise PropertyError("hypothesis context must not contain duplicates")
    return ordered


def hypothesis_union(*contexts: Iterable[object]) -> tuple[object, ...]:
    """Canonical set union for separately admitted hypothesis contexts."""

    by_reference: dict[bytes, object] = {}
    for context in contexts:
        for identifier in canonical_hypotheses(context):
            by_reference[identifier.internal_reference()] = identifier
    return canonical_hypotheses(by_reference.values())


def _source_free_question_context(selected_profile: object) -> object:
    reason = analysis_profile_declaration_ref(
        selected_profile,
        ANALYSIS_PROPERTY_PROFILE,
        "analysis.semantic-law",
        "source-free-premise-reason",
    )
    return k1.DatumVariant(0, analysis_profile_declaration_ref_body(reason))


_PROPERTY_PREMISE_FAMILIES = frozenset(
    label
    for label, _ in ANALYSIS_PROPERTY_DECLARATION_CATALOGS["analysis.property-family"]
)
_TRANSPORT_PREMISE_FAMILIES = frozenset(
    label
    for label, _ in ANALYSIS_TRANSPORT_DECLARATION_CATALOGS["analysis.property-family"]
)


def _exact_premise_goal_id(
    family_label: str,
    exact_subjects: tuple[object, ...],
    context: object,
    payload: object,
    *,
    selected_profile: object,
) -> object:
    """Form one named finite family question and its question-only goal.

    This is only the common compiler for the closed family table.  It does not
    invent a generic premise family, a synthetic premise subject, or a
    source-free context.  Each caller supplies the exact durable family,
    subject projection, and one admitted family-specific context.
    """

    if family_label in _PROPERTY_PREMISE_FAMILIES:
        owner_profile = ANALYSIS_PROPERTY_PROFILE
    elif family_label in _TRANSPORT_PREMISE_FAMILIES:
        owner_profile = ANALYSIS_TRANSPORT_PROFILE
    else:
        raise PropertyError("premise constructor names no active family contract")
    if selected_profile not in (
        ANALYSIS_PROPERTY_PROFILE,
        ANALYSIS_TRANSPORT_PROFILE,
    ):
        raise PropertyError("premise constructor selected an unsupported profile")
    if (
        selected_profile is ANALYSIS_PROPERTY_PROFILE
        and owner_profile is not ANALYSIS_PROPERTY_PROFILE
    ):
        raise PropertyError("property profile cannot import a transport family")
    if type(exact_subjects) is not tuple or not exact_subjects:
        raise PropertyError("exact premise needs a nonempty subject sequence")
    for subject in exact_subjects:
        _id_datum(subject)
        if subject.subject_kind.startswith("probe.analysis."):
            raise PropertyError("probe-local subject cannot enter a premise question")
    compiled_payload = _expand_probe_references(
        _analysis_datum(payload, "premise payload")
    )
    _reject_probe_reference_datum(compiled_payload)
    family = analysis_profile_declaration_ref(
        selected_profile,
        owner_profile,
        "analysis.property-family",
        family_label,
    )
    identity = (
        _analysis_id
        if selected_profile is ANALYSIS_PROPERTY_PROFILE
        else _analysis_transport_id
    )
    question_id = identity(
        "analysis.question",
        AnalysisQuestionBodyV0(
            family,
            exact_subjects,
            _analysis_datum(context, "premise question context"),
            compiled_payload,
        ),
    )
    return identity("analysis.goal", AnalysisGoalBodyV0(question_id))


def _semantic_experiment_context(
    manifest_ids: tuple[object, ...],
    experiment_profile_ids: tuple[object, ...],
) -> object:
    for identifier in manifest_ids:
        _id_datum(identifier, "analysis.semantic-read-manifest")
    for identifier in experiment_profile_ids:
        _id_datum(identifier, "analysis.experiment-profile")
    return k1.DatumVariant(
        1,
        k1.DatumRecord(
            (
                (
                    0,
                    k1.DatumSeq(
                        tuple(
                            _id_datum(item, "analysis.semantic-read-manifest")
                            for item in manifest_ids
                        )
                    ),
                ),
                (
                    1,
                    k1.DatumSeq(
                        tuple(
                            _id_datum(item, "analysis.experiment-profile")
                            for item in experiment_profile_ids
                        )
                    ),
                ),
            )
        ),
    )


def _form_family_semantic_context(
    family: "AFKAsymptoticFamily",
    *,
    axes: tuple[str, ...],
) -> object:
    family_id = family_definition_id(family)
    return k1.DatumVariant(
        2,
        k1.DatumRecord(
            (
                (0, _id_datum(family_id, "analysis.asymptotic-protocol-family")),
                (
                    1,
                    k1.DatumSeq(
                        tuple(
                            _id_datum(
                                family_manifest_schema_id(family, axis),
                                "analysis.family-read-manifest-schema",
                            )
                            for axis in axes
                        )
                    ),
                ),
                (
                    2,
                    k1.DatumSeq(
                        tuple(
                            _id_datum(
                                family_experiment_profile_id(family, axis),
                                "analysis.experiment-profile",
                            )
                            for axis in axes
                        )
                    ),
                ),
            )
        ),
    )


def _family_semantic_context(
    family: "AFKAsymptoticFamily",
    *,
    axes: tuple[str, ...],
) -> object:
    return _family_static_value(
        "semantic-context",
        family,
        axes,
        form=lambda: _form_family_semantic_context(family, axes=axes),
    )


def fixture_hypothesis(label: str) -> object:
    """Return one exact but ordinarily unrequested source-verifier premise."""

    case = k3.schnorr_case()
    protocol_id = k3.protocol_id(
        case.core,
        None,
        k2.ChallengeInterpretation.FRESH,
    )
    return _exact_premise_goal_id(
        "polynomial-time-source-verifier",
        (protocol_id,),
        k1.DatumVariant(
            1,
            k1.DatumRecord(
                (
                    (0, k1.DatumSeq(())),
                    (1, k1.DatumSeq(())),
                )
            ),
        ),
        k1.DatumRecord(
            (
                (0, _id_datum(protocol_id, "pir.protocol")),
                (1, k1.Symbol(_ascii(label, "fixture premise label"))),
            )
        ),
        selected_profile=ANALYSIS_PROPERTY_PROFILE,
    )


def analysis_hypothesis_context_id(
    hypotheses: Iterable[object], *, transport: bool = False
) -> object:
    """Compile the exact bounded goal-node DAG for a flat premise frontier."""

    values = canonical_hypotheses(hypotheses)
    identity = _analysis_transport_id if transport else _analysis_id
    nodes = tuple(
        AnalysisHypothesisNodeV0(index, goal_id, ())
        for index, goal_id in enumerate(values)
    )
    return identity(
        "analysis.hypothesis-context",
        AnalysisHypothesisContextBodyV0(nodes, tuple(range(len(nodes)))),
    )


def analysis_question_id(question: AnalysisQuestion) -> object:
    if (
        type(question) is not AnalysisQuestion
        or type(question.family) is not PropertyFamily
    ):
        raise PropertyError("Analysis question has the wrong exact shape")
    _id_datum(question.protocol_family_id, "pir.protocol")
    _id_datum(question.relation_family_id, "relations.definition")
    _ascii(question.scope, "Analysis question scope")
    if question.family is PropertyFamily.K_OUT_OF_N_SPECIAL_SOUNDNESS:
        expected_subject = family_member_term_id(
            family_member_subject_id(
                FamilyMemberSubjectProfile(
                    question.protocol_family_id,
                    question.relation_family_id,
                    schnorr_family_member_relation_id(
                        question.protocol_family_id, question.relation_family_id
                    ),
                    "n",
                    "octet",
                )
            ),
            1,
        )
        if (
            question.scope != "fixed-member-anchor"
            or question.subject_id != expected_subject
        ):
            raise PropertyError("source question detached from its fixed family member")
        _id_datum(question.subject_id, "analysis.family-member-term")
    elif question.family is PropertyFamily.ADAPTIVE_NIROP_KNOWLEDGE_SOUNDNESS_Q_LT_N:
        expected_subject = family_member_subject_id(
            FamilyMemberSubjectProfile(
                question.protocol_family_id,
                question.relation_family_id,
                schnorr_family_member_relation_id(
                    question.protocol_family_id, question.relation_family_id
                ),
                "n",
                "octet",
            )
        )
        if (
            question.scope != "abstract-family-with-fixed-n0-anchor"
            or question.subject_id != expected_subject
        ):
            raise PropertyError("target question detached from Member(F,n)")
        _id_datum(question.subject_id, "analysis.family-member-subject")
    _id_datum(question.fixed_member_selector_id, "analysis.family-member-selector")
    _id_datum(question.protocol_id, "pir.protocol")
    _id_datum(question.relation_binding_id, "relations.protocol-binding")
    _id_datum(question.model_id, "analysis.experiment-profile")
    _id_datum(question.semantic_read_closure_id, "analysis.semantic-read-manifest")
    for ordinal, quantifier in enumerate(question.quantifiers):
        _quantifier_body(quantifier, ordinal)
    context = k1.DatumVariant(
        1,
        k1.DatumRecord(
            (
                (
                    0,
                    k1.DatumSeq(
                        (
                            _id_datum(
                                question.semantic_read_closure_id,
                                "analysis.semantic-read-manifest",
                            ),
                        )
                    ),
                ),
                (
                    1,
                    k1.DatumSeq(
                        (
                            _id_datum(
                                question.model_id,
                                "analysis.experiment-profile",
                            ),
                        )
                    ),
                ),
            )
        ),
    )
    family_payload = k1.DatumRecord(
        (
            (0, k1.Symbol(question.scope)),
            (
                1,
                _id_datum(question.protocol_family_id, "pir.protocol"),
            ),
            (
                2,
                _id_datum(question.relation_family_id, "relations.definition"),
            ),
            (
                3,
                _embedded_component_datum(
                    question.fixed_member_selector_id,
                    "analysis.family-member-selector",
                ),
            ),
            (4, _id_datum(question.protocol_id, "pir.protocol")),
            (
                5,
                _id_datum(question.relation_binding_id, "relations.protocol-binding"),
            ),
            (
                6,
                k1.DatumSeq(
                    tuple(
                        _quantifier_body(item, ordinal)
                        for ordinal, item in enumerate(question.quantifiers)
                    )
                ),
            ),
            (
                7,
                _expand_probe_references(
                    _property_conclusion_body(hypothesis_free_conclusion(question))
                ),
            ),
            (
                8,
                _embedded_component_datum(
                    question.subject_id,
                    "analysis.family-member-term"
                    if question.family is PropertyFamily.K_OUT_OF_N_SPECIAL_SOUNDNESS
                    else "analysis.family-member-subject",
                ),
            ),
        )
    )
    return _analysis_id(
        "analysis.question",
        AnalysisQuestionBodyV0(
            family_profile_id(question.family),
            (question.protocol_id, question.relation_binding_id),
            context,
            family_payload,
        ),
    )


def _property_conclusion_body(conclusion: PropertyConclusion) -> object:
    if type(conclusion) is SpecialSoundnessConclusion:
        if (
            type(conclusion.extraction_arity) is not int
            or type(conclusion.challenge_count) is not int
            or not 2 <= conclusion.extraction_arity <= conclusion.challenge_count
        ):
            raise PropertyError("special-soundness conclusion has invalid k or N")
        return k1.DatumVariant(
            0,
            k1.DatumRecord(
                (
                    (
                        0,
                        _id_datum(conclusion.profile_id, "analysis.experiment-profile"),
                    ),
                    (1, k1.Nat(conclusion.extraction_arity)),
                    (2, k1.Nat(conclusion.challenge_count)),
                    (
                        3,
                        _id_datum(
                            conclusion.extractor_profile_id,
                            "analysis.extractor-profile",
                        ),
                    ),
                    (
                        4,
                        _id_datum(
                            conclusion.extractor_algorithm_id,
                            "foundation.portable-algorithm",
                        ),
                    ),
                )
            ),
        )
    if type(conclusion) is AFKKnowledgeSoundnessConclusion:
        _id_datum(conclusion.extractor_profile_id, "analysis.extractor-profile")
        _id_datum(conclusion.distribution_law_id, "analysis.distribution-profile")
        _id_datum(conclusion.success_event_id, "analysis.event-profile")
        for formula_id in (
            conclusion.success_probability_formula_id,
            conclusion.knowledge_error_formula_id,
            conclusion.success_lower_bound_formula_id,
        ):
            _id_datum(formula_id, "analysis.quantitative-formula")
        formula_sorts = tuple(
            _FORMULA_RESULT_SORT_REGISTRY.get(item.internal_reference())
            for item in (
                conclusion.success_probability_formula_id,
                conclusion.knowledge_error_formula_id,
                conclusion.success_lower_bound_formula_id,
            )
        )
        if formula_sorts != (
            QuantitativeSort.PROBABILITY,
            QuantitativeSort.PROBABILITY,
            QuantitativeSort.SIGNED_PROBABILITY_LOWER_BOUND,
        ):
            raise PropertyError(
                "AFK conclusion formula result sorts do not match their roles"
            )
        formula_roles = tuple(
            _FORMULA_ROLE_REGISTRY.get(item.internal_reference())
            for item in (
                conclusion.success_probability_formula_id,
                conclusion.knowledge_error_formula_id,
                conclusion.success_lower_bound_formula_id,
            )
        )
        if (
            tuple(item[0] if item is not None else None for item in formula_roles)
            != (
                "extractor-success",
                "knowledge-error",
                "knowledge-success-lower-bound",
            )
            or any(item is None for item in formula_roles)
            or len({item[1] for item in formula_roles if item is not None}) != 1
        ):
            raise PropertyError(
                "AFK conclusion formulas do not carry their exact roles on one subject"
            )
        formula_subject = formula_roles[0][1]
        if (
            conclusion.extractor_profile_id
            != subject_bound_afk_extractor_profile_id(formula_subject)
            or conclusion.distribution_law_id
            != subject_bound_afk_distribution_law_id(8, formula_subject)
            or conclusion.success_event_id
            != subject_bound_relation_success_event_id(formula_subject)
        ):
            raise PropertyError(
                "AFK conclusion formulas are detached from its extractor, law, or event"
            )
        _id_datum(
            conclusion.expected_invocation_bound_id,
            "analysis.expected-invocation-bound",
        )
        invocation_bound = _EXPECTED_INVOCATION_BOUND_REGISTRY.get(
            conclusion.expected_invocation_bound_id.internal_reference()
        )
        if (
            invocation_bound is None
            or invocation_bound.experiment_body_id
            != subject_bound_experiment_body_id(
                8, formula_subject, "extractor-experiment"
            )
            or invocation_bound.counted_algorithm_id
            != subject_bound_afk_adversary_running_algorithm_id(8, formula_subject)
            or invocation_bound.resource_dimension_id
            != AFK_ADVERSARY_RUNNING_CALL_DIMENSION_ID
            or _FORMULA_ROLE_REGISTRY.get(
                invocation_bound.rhs_formula_id.internal_reference()
            )
            != ("expected-adversary-calls-upper-bound", formula_subject)
        ):
            raise PropertyError(
                "AFK conclusion invocation bound is detached from its exact subject"
            )
        if conclusion.prover_output_law != ("x", "pi", "aux", "v"):
            raise PropertyError("AFK prover-output law must preserve (x,pi,aux,v)")
        if conclusion.extractor_output_law != ("x", "pi", "aux", "v", "w"):
            raise PropertyError(
                "AFK extractor-output law must preserve (x,pi,aux,v) and append w"
            )
        if conclusion.comparator != "greater-than-or-equal":
            raise PropertyError("AFK knowledge-success conclusion needs >= orientation")
        return k1.DatumVariant(
            1,
            k1.DatumRecord(
                (
                    (
                        0,
                        _id_datum(
                            conclusion.extractor_profile_id,
                            "analysis.extractor-profile",
                        ),
                    ),
                    (
                        1,
                        _id_datum(
                            conclusion.distribution_law_id,
                            "analysis.distribution-profile",
                        ),
                    ),
                    (
                        2,
                        _id_datum(
                            conclusion.success_event_id, "analysis.event-profile"
                        ),
                    ),
                    (
                        3,
                        k1.DatumSeq(
                            tuple(
                                k1.Symbol(item) for item in conclusion.prover_output_law
                            )
                        ),
                    ),
                    (
                        4,
                        k1.DatumSeq(
                            tuple(
                                k1.Symbol(item)
                                for item in conclusion.extractor_output_law
                            )
                        ),
                    ),
                    (
                        5,
                        k1.Symbol(conclusion.comparator),
                    ),
                    (
                        6,
                        _id_datum(
                            conclusion.success_probability_formula_id,
                            "analysis.quantitative-formula",
                        ),
                    ),
                    (
                        7,
                        _id_datum(
                            conclusion.knowledge_error_formula_id,
                            "analysis.quantitative-formula",
                        ),
                    ),
                    (
                        8,
                        _id_datum(
                            conclusion.success_lower_bound_formula_id,
                            "analysis.quantitative-formula",
                        ),
                    ),
                    (
                        9,
                        _id_datum(
                            conclusion.expected_invocation_bound_id,
                            "analysis.expected-invocation-bound",
                        ),
                    ),
                )
            ),
        )
    raise PropertyError("Analysis goal has an unknown conclusion form")


def hypothesis_free_conclusion(question: AnalysisQuestion) -> PropertyConclusion:
    """Pure family-contract reconstruction from the authenticated question."""

    if type(question) is not AnalysisQuestion:
        raise PropertyError("Analysis question has the wrong exact shape")
    if question.family is PropertyFamily.K_OUT_OF_N_SPECIAL_SOUNDNESS:
        payload = question.family_payload
        if type(payload) is not SpecialSoundnessQuestionPayload:
            raise PropertyError(
                "special soundness question has the wrong family payload"
            )
        conclusion: PropertyConclusion = SpecialSoundnessConclusion(
            payload.profile_id,
            payload.extraction_arity,
            payload.challenge_count,
            payload.extractor_profile_id,
            payload.extractor_algorithm_id,
        )
    elif question.family is PropertyFamily.ADAPTIVE_NIROP_KNOWLEDGE_SOUNDNESS_Q_LT_N:
        payload = question.family_payload
        if type(payload) is not AFKKnowledgeSoundnessQuestionPayload:
            raise PropertyError(
                "adaptive knowledge-soundness question has the wrong family payload"
            )
        conclusion = AFKKnowledgeSoundnessConclusion(
            payload.extractor_profile_id,
            payload.distribution_law_id,
            payload.prover_output_law,
            payload.extractor_output_law,
            payload.success_event_id,
            payload.comparator,
            payload.success_probability_formula_id,
            payload.knowledge_error_formula_id,
            payload.success_lower_bound_formula_id,
            payload.expected_invocation_bound_id,
        )
    else:
        raise PropertyError("Analysis question has no bounded conclusion derivation")
    _property_conclusion_body(conclusion)
    return conclusion


def analysis_goal_id(goal: AnalysisGoal) -> object:
    if type(goal) is not AnalysisGoal:
        raise PropertyError("Analysis goal has the wrong exact shape")
    question_id = analysis_question_id(goal.question)
    expected_conclusion = hypothesis_free_conclusion(goal.question)
    if type(goal.conclusion) is not type(expected_conclusion) or (
        goal.conclusion != expected_conclusion
    ):
        raise PropertyError(
            "Analysis goal conclusion was substituted after question formation"
        )
    _property_conclusion_body(expected_conclusion)
    return _analysis_id(
        "analysis.goal",
        AnalysisGoalBodyV0(question_id),
    )


def analysis_proposition_id(proposition: AnalysisProposition) -> object:
    if type(proposition) is not AnalysisProposition:
        raise PropertyError("Analysis proposition has the wrong exact shape")
    goal_id = analysis_goal_id(proposition.goal)
    hypotheses = canonical_hypotheses(proposition.hypotheses)
    if hypotheses != proposition.hypotheses:
        raise PropertyError("Analysis proposition hypotheses are not canonical")
    context_id = analysis_hypothesis_context_id(hypotheses)
    return _analysis_id(
        "analysis.proposition",
        AnalysisPropositionBodyV0(goal_id, context_id),
    )


def _model_parameters(model: ExperimentModel) -> dict[str, int]:
    admit_experiment_model(model)
    return dict(model.parameters)


def form_special_soundness_proposition(
    source: FreshFsRelationSource,
    model: ExperimentModel,
    profile: SchnorrSpecialSoundnessProfile,
    hypotheses: Iterable[object] = (),
) -> AnalysisProposition:
    require_fresh_fs_relation_source(source)
    require_schnorr_special_soundness_profile(source, profile)
    _require_exact_special_soundness_model(model)
    parameters = _model_parameters(model)
    if (
        model.strategy_class is not StrategyClass.ACCEPTING_TRANSCRIPT_PAIR_DOMAIN
        or model.oracle_model is not OracleModel.PUBLIC_COIN
        or set(parameters) != {"N", "k"}
        or parameters["k"] < 2
        or parameters["N"] < parameters["k"]
    ):
        raise PropertyError(
            "special soundness needs the selected accepted-transcript-pair model"
        )
    if (
        parameters["k"] != profile.extraction_arity
        or parameters["N"] != profile.challenge_count
    ):
        raise PropertyError("special-soundness model disagrees with its exact profile")
    selected_hypotheses = canonical_hypotheses(hypotheses)
    relation_hypothesis = schnorr_relation_correspondence_hypothesis_id(profile)
    required_source_hypotheses = (
        relation_hypothesis,
        k2_static_view_support_hypothesis_id(source),
    )
    if any(
        required not in selected_hypotheses for required in required_source_hypotheses
    ):
        raise PropertyError(
            "the source property needs exact relation and owner-view hypotheses"
        )
    question = AnalysisQuestion(
        PropertyFamily.K_OUT_OF_N_SPECIAL_SOUNDNESS,
        family_member_term_id(FRESH_THEOREM_SUBJECT_SCHEMA_ID, 1),
        "fixed-member-anchor",
        SCHNORR_FRESH_PROTOCOL_FAMILY_ID,
        SCHNORR_RELATION_FAMILY_ID,
        fixed_family_member_selector_id(source, "fresh"),
        source.protocol_source.fresh_protocol_id,
        source.fresh_binding.binding_id,
        experiment_model_id(model),
        source_manifest_id(source.fresh_manifest),
        model.quantifiers,
        SpecialSoundnessQuestionPayload(
            profile.profile_id,
            profile.extraction_arity,
            profile.challenge_count,
            profile.extractor_profile_id,
            profile.extractor_algorithm_id,
        ),
    )
    conclusion = SpecialSoundnessConclusion(
        profile.profile_id,
        profile.extraction_arity,
        profile.challenge_count,
        profile.extractor_profile_id,
        profile.extractor_algorithm_id,
    )
    proposition = AnalysisProposition(
        AnalysisGoal(question, conclusion),
        selected_hypotheses,
    )
    analysis_proposition_id(proposition)
    return proposition


@dataclass(frozen=True)
class ConditionalRule:
    rule_id: object
    exact_proposition_id: object
    required_hypothesis_id: object
    semantic_basis_id: object


@dataclass(frozen=True)
class EstablishedJudgment:
    proposition: AnalysisProposition
    proposition_id: object
    rule_id: object
    semantic_basis_id: object
    conditional_hypotheses: tuple[object, ...]
    derivation_support: object
    validation_basis_id: object
    operation_policy_id: object
    qualification: object
    judgment_id: object
    _issuer: object


_JUDGMENT_ISSUER = object()


def _hypothesis_node_requirements(
    goals: Iterable[object], *, transport: bool
) -> object:
    values = canonical_hypotheses(goals)
    context_id = analysis_hypothesis_context_id(values, transport=transport)
    return k1.DatumSeq(
        tuple(
            k1.DatumVariant(
                0,
                k1.DatumRecord(
                    (
                        (
                            0,
                            _id_datum(context_id, "analysis.hypothesis-context"),
                        ),
                        (1, k1.Nat(ordinal)),
                        (2, _id_datum(goal_id, "analysis.goal")),
                    )
                ),
            )
            for ordinal, goal_id in enumerate(values)
        )
    )


def _exact_hypothesis_node_requirements(
    context_id: object,
    nodes: tuple[AnalysisHypothesisNodeV0, ...],
) -> object:
    """Bind requirements to an already authenticated non-flat context DAG."""

    _id_datum(context_id, "analysis.hypothesis-context")
    if tuple(node.local_ordinal for node in nodes) != tuple(range(len(nodes))):
        raise PropertyError("hypothesis-node requirements need exact local ordinals")
    return k1.DatumSeq(
        tuple(
            k1.DatumVariant(
                0,
                k1.DatumRecord(
                    (
                        (0, _id_datum(context_id, "analysis.hypothesis-context")),
                        (1, k1.Nat(node.local_ordinal)),
                        (2, _id_datum(node.goal_id, "analysis.goal")),
                    )
                ),
            )
            for node in nodes
        )
    )


def _native_rule_source(
    selected_profile: object,
    owner_profile: object,
    label: str,
    payload: object,
) -> object:
    rule = analysis_profile_declaration_ref(
        selected_profile,
        owner_profile,
        "analysis.native-rule",
        label,
    )
    return k1.DatumVariant(
        0,
        k1.DatumRecord(
            (
                (0, analysis_profile_declaration_ref_body(rule)),
                (1, _analysis_datum(payload, "native-rule payload")),
            )
        ),
    )


def _imported_theorem_rule_source(theorem_schema_id: object) -> object:
    return k1.DatumVariant(
        1,
        _id_datum(theorem_schema_id, "analysis.theorem-schema"),
    )


def _conclusion_schema_ref(
    selected_profile: object,
    owner_profile: object,
    label: str,
) -> object:
    return analysis_profile_declaration_ref(
        selected_profile,
        owner_profile,
        "analysis.semantic-law",
        label,
    )


def _analysis_support_instantiation_id(
    *,
    profile: object,
    semantic_basis_id: object,
    proposition_id: object,
    assumed_goals: Iterable[object] = (),
    theorem_validations: dict[object, object] | None = None,
    non_hypothesis_premise_bindings: object | None = None,
    established_hypothesis_node_bindings: object | None = None,
    assumed_hypothesis_node_bindings: object | None = None,
    source_support_bindings: object | None = None,
) -> object:
    goals = canonical_hypotheses(assumed_goals)
    validation_by_goal = {} if theorem_validations is None else theorem_validations
    if any(goal not in goals for goal in validation_by_goal):
        raise PropertyError("theorem validation names no assumed goal")
    assumed_entries = []
    for ordinal, goal_id in enumerate(goals):
        validation_id = validation_by_goal.get(goal_id)
        validation = (
            k1.DatumVariant(0, k1.UNIT)
            if validation_id is None
            else k1.DatumVariant(
                1,
                _id_datum(
                    validation_id,
                    "analysis.theorem-source-validation",
                ),
            )
        )
        assumed_entries.append(
            k1.DatumRecord(
                (
                    (0, k1.Nat(ordinal)),
                    (
                        1,
                        k1.DatumRecord(
                            (
                                (0, _id_datum(goal_id, "analysis.goal")),
                                (1, k1.DatumVariant(0, k1.UNIT)),
                                (2, validation),
                            )
                        ),
                    ),
                )
            )
        )
    body = AnalysisSupportInstantiationBodyV0(
        semantic_basis_id,
        proposition_id,
        non_hypothesis_premise_bindings or k1.DatumSeq(()),
        established_hypothesis_node_bindings or k1.DatumSeq(()),
        assumed_hypothesis_node_bindings or k1.DatumSeq(tuple(assumed_entries)),
        source_support_bindings or k1.DatumSeq(()),
    )
    return _form_analysis_profiled_content_id(
        "analysis.support-instantiation",
        body,
        profile,
    )


def _analysis_judgment_record_id(
    *,
    profile: object,
    proposition_id: object,
    exact_family_conclusion: object,
    inherited_hypothesis_context_id: object,
    typed_quantitative_result: object,
    semantic_basis_id: object,
    support_id: object,
    validation_basis_id: object,
    qualification: object,
    operation_policy_id: object,
    source_policy_closure: Iterable[object] = (),
) -> object:
    closure = _canonical_identifier_set(
        source_policy_closure,
        what="judgment source-policy dependency closure",
    )
    body = AnalysisJudgmentRecordBodyV0(
        _id_datum(proposition_id, "analysis.proposition"),
        k1.DatumVariant(0, k1.UNIT),
        _analysis_datum(exact_family_conclusion, "family conclusion"),
        _id_datum(
            inherited_hypothesis_context_id,
            "analysis.hypothesis-context",
        ),
        _analysis_datum(typed_quantitative_result, "quantitative result"),
        _id_datum(semantic_basis_id, "analysis.semantic-basis"),
        _id_datum(support_id, "analysis.support-instantiation"),
        _id_datum(validation_basis_id, "analysis.validation-basis"),
        analysis_profile_declaration_ref_body(qualification),
        _id_datum(operation_policy_id, "analysis.operation-policy"),
        k1.DatumSeq(tuple(_id_datum(item) for item in closure)),
    )
    qualification_context = _derive_qualification_subject_context(
        semantic_profile=profile,
        proposition_id=proposition_id,
        semantic_basis_id=semantic_basis_id,
        support_id=support_id,
        validation_basis_id=validation_basis_id,
        inherited_hypothesis_context_id=inherited_hypothesis_context_id,
        judgment_record=body,
    )
    _require_actual_qualification(qualification_context, qualification)
    return _form_analysis_profiled_content_id(
        "analysis.judgment-record",
        body,
        profile,
    )


def schnorr_semantic_basis_id(
    proposition: AnalysisProposition,
) -> object:
    """Rederive the exact basis for the selected conditional Schnorr theorem."""

    analysis_proposition_id(proposition)
    if (
        proposition.goal.question.family
        is not PropertyFamily.K_OUT_OF_N_SPECIAL_SOUNDNESS
        or type(proposition.goal.conclusion) is not SpecialSoundnessConclusion
        or proposition.goal.conclusion.extractor_profile_id
        != SCHNORR_TRANSCRIPT_EXTRACTOR_PROFILE_ID
        or proposition.goal.conclusion.extractor_algorithm_id
        != SCHNORR_EXTRACTOR_ALGORITHM
    ):
        raise PropertyError("Schnorr semantic basis needs the exact source conclusion")
    return _analysis_id(
        "analysis.semantic-basis",
        AnalysisSemanticBasisBodyV0(
            family_profile_id(PropertyFamily.K_OUT_OF_N_SPECIAL_SOUNDNESS),
            analysis_question_id(proposition.goal.question),
            _native_rule_source(
                ANALYSIS_PROPERTY_PROFILE,
                ANALYSIS_PROPERTY_PROFILE,
                "existential-extractor-introduction",
                k1.DatumRecord(
                    (
                        (
                            0,
                            _id_datum(
                                SCHNORR_TRANSCRIPT_EXTRACTOR_PROFILE_ID,
                                "analysis.extractor-profile",
                            ),
                        ),
                        (
                            1,
                            _id_datum(
                                SCHNORR_EXTRACTOR_ALGORITHM,
                                "foundation.portable-algorithm",
                            ),
                        ),
                    )
                ),
            ),
            _hypothesis_node_requirements(
                proposition.hypotheses,
                transport=False,
            ),
            complete_read_purpose_requirements(
                concrete_manifest_ids=(
                    proposition.goal.question.semantic_read_closure_id,
                ),
            ),
            _conclusion_schema_ref(
                ANALYSIS_PROPERTY_PROFILE,
                ANALYSIS_PROPERTY_PROFILE,
                "k-out-of-n-conclusion-v0",
            ),
            k1.DatumRecord(
                (
                    (0, k1.Symbol("schnorr-two-special-soundness-transform")),
                    (
                        1,
                        _id_datum(
                            SCHNORR_TWO_SPECIAL_SOUNDNESS_THEOREM_ID,
                            "analysis.external.theorem-assumption",
                        ),
                    ),
                )
            ),
        ),
    )


def establish_conditionally(
    proposition: AnalysisProposition, rule: ConditionalRule
) -> EstablishedJudgment:
    proposition_id = analysis_proposition_id(proposition)
    if type(rule) is not ConditionalRule:
        raise PropertyError("conditional basis has the wrong exact shape")
    expected_rule = schnorr_special_soundness_rule(proposition)
    if rule != expected_rule:
        raise PropertyError(
            "only the exact selected Schnorr conditional rule may issue"
        )
    _id_datum(rule.rule_id, "analysis.semantic-basis")
    _id_datum(rule.exact_proposition_id, "analysis.proposition")
    _id_datum(rule.required_hypothesis_id, "analysis.goal")
    _id_datum(rule.semantic_basis_id, "analysis.semantic-basis")
    if rule.exact_proposition_id != proposition_id:
        raise PropertyError("conditional rule names another exact proposition")
    if rule.required_hypothesis_id not in proposition.hypotheses:
        raise PropertyError("conditional theorem assumption was not retained")
    support_id = _analysis_support_instantiation_id(
        profile=ANALYSIS_PROPERTY_PROFILE,
        semantic_basis_id=rule.semantic_basis_id,
        proposition_id=proposition_id,
        assumed_goals=proposition.hypotheses,
    )
    validation_basis_id = analysis_validation_basis_id(
        (), profile=ANALYSIS_PROPERTY_PROFILE
    )
    policy_id = _analysis_operation_policy_id(
        proposition_id,
        (
            (
                "finite-special-soundness",
                ("finite-special-soundness",),
            ),
        ),
        profile=ANALYSIS_PROPERTY_PROFILE,
    )
    qualification = analysis_profile_declaration_ref(
        ANALYSIS_PROPERTY_PROFILE,
        ANALYSIS_PROPERTY_PROFILE,
        "analysis.qualification",
        "finite-special-soundness-result",
    )
    context_id = analysis_hypothesis_context_id(proposition.hypotheses)
    judgment_id = _analysis_judgment_record_id(
        profile=ANALYSIS_PROPERTY_PROFILE,
        proposition_id=proposition_id,
        exact_family_conclusion=_expand_probe_references(
            _property_conclusion_body(proposition.goal.conclusion)
        ),
        inherited_hypothesis_context_id=context_id,
        typed_quantitative_result=k1.DatumVariant(0, k1.UNIT),
        semantic_basis_id=rule.semantic_basis_id,
        support_id=support_id,
        validation_basis_id=validation_basis_id,
        qualification=qualification,
        operation_policy_id=policy_id,
    )
    return EstablishedJudgment(
        proposition,
        proposition_id,
        rule.rule_id,
        rule.semantic_basis_id,
        proposition.hypotheses,
        support_id,
        validation_basis_id,
        policy_id,
        qualification,
        judgment_id,
        _JUDGMENT_ISSUER,
    )


def require_established_judgment(judgment: EstablishedJudgment) -> None:
    if (
        type(judgment) is not EstablishedJudgment
        or judgment._issuer is not _JUDGMENT_ISSUER
    ):
        raise AuthorityError("property judgment lacks Analysis issuance")
    if judgment.proposition_id != analysis_proposition_id(judgment.proposition):
        raise PropertyError("property judgment proposition was substituted")
    _id_datum(judgment.rule_id, "analysis.semantic-basis")
    _id_datum(judgment.semantic_basis_id, "analysis.semantic-basis")
    if judgment.rule_id != judgment.semantic_basis_id:
        raise PropertyError("property judgment uses no selected fixed-source rule")
    if judgment.semantic_basis_id != schnorr_semantic_basis_id(judgment.proposition):
        raise PropertyError("Schnorr judgment semantic basis was substituted")
    if judgment.conditional_hypotheses != judgment.proposition.hypotheses:
        raise PropertyError("property judgment dropped conditional hypotheses")
    expected_rule = schnorr_special_soundness_rule(judgment.proposition)
    expected = establish_conditionally(judgment.proposition, expected_rule)
    if judgment.derivation_support != expected.derivation_support:
        raise PropertyError("Schnorr judgment derivation support was substituted")
    if (
        judgment.validation_basis_id != expected.validation_basis_id
        or judgment.operation_policy_id != expected.operation_policy_id
        or judgment.qualification != expected.qualification
        or judgment.judgment_id != expected.judgment_id
    ):
        raise PropertyError("Schnorr judgment record was substituted")


# ---------------------------------------------------------------------------
# Occurrence-derived typed loss import
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class LossUse:
    coordinate: str
    bridge_id: object
    source_premise_id: object
    quantitative_export_id: object


@dataclass(frozen=True)
class LossExportRule:
    export_id: object
    required_hypothesis_id: object


@dataclass(frozen=True)
class LossLedgerEntry:
    use: LossUse
    export_id: object


def _bridge_by_id(source: RelationPropertySource) -> dict[object, object]:
    result: dict[object, object] = {}
    for bridge in source.case.bridges:
        identifier = k3.value_bridge_id(bridge)
        if identifier in result:
            raise QuantitativeError("value-bridge registry contains duplicates")
        result[identifier] = bridge
    return result


def derive_loss_uses(source: RelationPropertySource) -> tuple[LossUse, ...]:
    require_relation_property_source(source)
    bridge_by_id = _bridge_by_id(source)
    candidates: list[tuple[str, object]] = []
    binding = source.checked_protocol_binding.binding
    for edge in binding.public_edges:
        candidates.append(
            (f"protocol-public:{edge.instance}:{edge.slot}", edge.value_relation)
        )
    for edge in binding.phase_edges:
        candidates.append(
            (f"protocol-phase:{edge.instance}:{edge.slot}", edge.value_relation)
        )
    for edge in source.checked_plan_binding.binding.witness_edges:
        candidates.append(
            (
                f"plan-witness:{edge.slot}:{edge.witness_surface_key}",
                edge.value_relation,
            )
        )
    uses: list[LossUse] = []
    for coordinate, relation in candidates:
        if relation.bridge_id is None:
            continue
        bridge = bridge_by_id.get(relation.bridge_id)
        if bridge is None:
            raise QuantitativeError("checked binding names no imported value bridge")
        if bridge.lane is not k3.ValueBridgeLane.DIRECTIONAL_LOSSY:
            continue
        if relation.direction is not k3.BridgeDirection.FORWARD:
            raise QuantitativeError(
                "lossy bridge occurrence must use its forward direction"
            )
        assert bridge.source_premise_id is not None
        assert bridge.quantitative_export_id is not None
        uses.append(
            LossUse(
                coordinate,
                k3.value_bridge_id(bridge),
                bridge.source_premise_id,
                bridge.quantitative_export_id,
            )
        )
    if len(uses) > MAX_LOSS_USES:
        raise QuantitativeError("loss occurrence set exceeds its finite bound")
    uses.sort(key=lambda item: item.coordinate)
    if len({item.coordinate for item in uses}) != len(uses):
        raise QuantitativeError("loss occurrence coordinates must be unique")
    return tuple(uses)


def price_loss_uses(
    source: RelationPropertySource,
    rules: tuple[LossExportRule, ...],
    assumptions: Iterable[object],
) -> AttemptOutcome:
    try:
        uses = derive_loss_uses(source)
        hypotheses = canonical_hypotheses(assumptions)
        rule_by_export: dict[object, LossExportRule] = {}
        for rule in rules:
            if type(rule) is not LossExportRule:
                raise QuantitativeError("loss export rule has the wrong shape")
            _id_datum(rule.export_id, "relations.loss-export")
            _id_datum(rule.required_hypothesis_id, "analysis.goal")
            if rule.export_id in rule_by_export:
                raise QuantitativeError("loss export rules must be unique")
            rule_by_export[rule.export_id] = rule
        entries: list[LossLedgerEntry] = []
        for use in uses:
            rule = rule_by_export.get(use.quantitative_export_id)
            if rule is None:
                return AttemptOutcome(
                    AttemptKind.CANNOT_ANSWER,
                    detail="one derived loss occurrence has no typed export rule",
                )
            if rule.required_hypothesis_id not in hypotheses:
                return AttemptOutcome(
                    AttemptKind.CANNOT_ANSWER,
                    detail="one loss export lacks its explicit source premise hypothesis",
                )
            entries.append(LossLedgerEntry(use, rule.export_id))
        if not entries:
            return AttemptOutcome(
                AttemptKind.CANNOT_ANSWER,
                detail="the selected relation source has no lossy occurrence to price",
            )
        return AttemptOutcome(
            AttemptKind.CANNOT_ANSWER,
            detail=(
                "loss occurrences are derived, but no owner-issued Relations "
                "semantic rule binds use, premise, bridge, sort, and formula"
            ),
        )
    except AuthorityError as error:
        return AttemptOutcome(AttemptKind.REFUSED, detail=str(error))
    except (AnalysisError, k2.ModelError, k3.K3Error) as error:
        return AttemptOutcome(AttemptKind.MALFORMED, detail=str(error))


def lossy_schnorr_case() -> object:
    """Make one K3-checked directional witness occurrence for loss pressure."""

    case = k3.schnorr_case()
    bridge = k3.ValueBridge(
        "nat-to-bytes-lossy",
        k3.ValueBridgeLane.DIRECTIONAL_LOSSY,
        k3.NAT,
        k3.BYTES,
        k3.fixture_semantic_ref("foundation.canonical-algorithm", "nat-to-bytes"),
        collision_relation_id=k3.fixture_semantic_ref(
            "relations.definition", "nat-to-bytes-collision"
        ),
        source_premise_id=k3.fixture_semantic_ref(
            "relations.loss-source-premise", "witness-preimage-availability"
        ),
        quantitative_export_id=k3.fixture_semantic_ref(
            "relations.loss-export", "witness-projection-advantage"
        ),
    )
    interface = replace(
        case.relation_interfaces[0],
        private_witness=(k3.RelationSlot("secret", k3.BYTES),),
    )
    relation_id = k3.relation_interface_id(interface)
    protocol_binding = replace(
        case.protocol_binding,
        relation_interface_ids=(relation_id,),
        instances=tuple(
            replace(item, relation_interface_id=relation_id)
            for item in case.protocol_binding.instances
        ),
    )
    plan_binding = replace(
        case.plan_binding,
        relation_interface_id=relation_id,
        witness_edges=(
            replace(
                case.plan_binding.witness_edges[0],
                value_relation=k3.ValueRelation(
                    k3.value_bridge_id(bridge), k3.BridgeDirection.FORWARD
                ),
            ),
        ),
    )
    return replace(
        case,
        relation_interfaces=(interface,),
        protocol_binding=protocol_binding,
        plan_binding=plan_binding,
        bridges=(bridge,),
    )


def total_uniform_schnorr_case() -> object:
    """Derive the bounded theorem fixture without hiding sampler failure.

    The stock PIR Schnorr fixture samples into modulus 11 by bounded rejection.
    This variant keeps the prime-order-11 group and verifier equation but uses
    challenge set [0,8), one sample byte, and one attempt.  Eight divides 256,
    so the decode is total and uniform if its input byte is uniform.  Whether
    the concrete SHA-256 squeeze realizes an ideal random oracle remains an
    explicit Analysis hypothesis; this helper does not establish it.
    """

    case = k3.schnorr_case()
    challenge_index = next(
        index
        for index, occurrence in enumerate(case.core.schedule)
        if occurrence.name == "challenge"
    )
    schedule = list(case.core.schedule)
    schedule[challenge_index] = replace(
        schedule[challenge_index], challenge_domain=k2.ChallengeDomain(8)
    )
    core = replace(case.core, schedule=tuple(schedule))
    construction = replace(
        case.construction,
        application_domain=b"zkc/k3-c/schnorr-total-uniform/v0",
        sample_bytes=1,
        max_attempts=1,
    )
    protocol_id = k3.protocol_id(
        core, construction, k2.ChallengeInterpretation.FIAT_SHAMIR
    )
    interface = k3.default_interface(
        core,
        construction,
        k2.ChallengeInterpretation.FIAT_SHAMIR,
        expose_all_transports=True,
    )
    plan = replace(case.plan, protocol_id=protocol_id)
    relation_interface = case.relation_interfaces[0]
    protocol_binding = replace(case.protocol_binding, protocol_id=protocol_id)
    surface = k3.derive_plan_witness_surface(
        core, construction, k2.ChallengeInterpretation.FIAT_SHAMIR, plan
    )
    plan_binding = replace(
        case.plan_binding,
        plan_witness_surface_id=k3.plan_witness_surface_id(surface),
    )
    return replace(
        case,
        core=core,
        construction=construction,
        interface=interface,
        plan=plan,
        relation_interfaces=(relation_interface,),
        protocol_binding=protocol_binding,
        plan_binding=plan_binding,
    )


# ---------------------------------------------------------------------------
# Exact bounded source profile: relation-bound Schnorr 2-special soundness
# ---------------------------------------------------------------------------


FINITE_COVER_ARITHMETIC = finite_cover.build_bundle(k1)
FINITE_COVER_PORTABLE_EVALUATOR = finite_cover.CheckedPortableEvaluator(
    k1, FINITE_COVER_ARITHMETIC
)
_SCHNORR_EXTRACTOR_ALGORITHM_BODY = FINITE_COVER_ARITHMETIC.candidate_algorithm
SCHNORR_EXTRACTOR_ALGORITHM = k1.authenticate_algorithm_identity(
    _SCHNORR_EXTRACTOR_ALGORITHM_BODY
)


@dataclass(frozen=True)
class SchnorrSpecialSoundnessProfile:
    profile_id: object
    relation_definition_id: object
    relation_interface_id: object
    fresh_protocol_id: object
    fresh_binding_id: object
    group_modulus: int
    subgroup_order: int
    generator: int
    challenge_count: int
    extraction_arity: int
    statement_coordinate: str
    commitment_coordinate: str
    challenge_coordinate: str
    response_coordinate: str
    extractor_profile_id: object
    extractor_algorithm_id: object
    statement_anchor_value: int
    challenge_domain_id: object
    check_coordinate: str
    terminal_coordinate: str
    _issuer: object


@dataclass(frozen=True)
class SchnorrTranscript:
    statement: int
    commitment: int
    challenge: int
    response: int


@dataclass(frozen=True)
class ExtractedSchnorrWitness:
    witness: int
    first: SchnorrTranscript
    second: SchnorrTranscript
    profile_id: object
    _issuer: object


_SCHNORR_PROFILE_ISSUER = object()
_SCHNORR_EXTRACTION_ISSUER = object()


def _schnorr_profile_body(profile: SchnorrSpecialSoundnessProfile) -> object:
    if type(profile) is not SchnorrSpecialSoundnessProfile:
        raise PropertyError("Schnorr source profile has the wrong exact shape")
    for value, what in (
        (profile.statement_coordinate, "statement coordinate"),
        (profile.commitment_coordinate, "commitment coordinate"),
        (profile.challenge_coordinate, "challenge coordinate"),
        (profile.response_coordinate, "response coordinate"),
        (profile.check_coordinate, "Check coordinate"),
        (profile.terminal_coordinate, "Terminal coordinate"),
    ):
        _ascii(value, what)
    if (
        type(profile.group_modulus) is not int
        or type(profile.subgroup_order) is not int
        or type(profile.generator) is not int
        or type(profile.challenge_count) is not int
        or type(profile.extraction_arity) is not int
        or profile.group_modulus <= 2
        or profile.subgroup_order <= 1
        or not 1 < profile.generator < profile.group_modulus
        or not 2 <= profile.extraction_arity <= profile.challenge_count
        or profile.challenge_count > profile.subgroup_order
        or type(profile.statement_anchor_value) is not int
        or not 0 <= profile.statement_anchor_value < (1 << 64)
    ):
        raise PropertyError("Schnorr source profile has invalid finite parameters")
    return k1.DatumRecord(
        (
            (
                0,
                analysis_profile_declaration_ref_body(
                    family_profile_id(PropertyFamily.K_OUT_OF_N_SPECIAL_SOUNDNESS)
                ),
            ),
            (1, _id_datum(profile.relation_definition_id, "relations.definition")),
            (2, _id_datum(profile.relation_interface_id, "relations.interface")),
            (3, _id_datum(profile.fresh_protocol_id, "pir.protocol")),
            (4, _id_datum(profile.fresh_binding_id, "relations.protocol-binding")),
            (5, k1.Nat(profile.group_modulus)),
            (6, k1.Nat(profile.subgroup_order)),
            (7, k1.Nat(profile.generator)),
            (8, k1.Nat(profile.challenge_count)),
            (9, k1.Nat(profile.extraction_arity)),
            (10, k1.Symbol(profile.statement_coordinate)),
            (11, k1.Symbol(profile.commitment_coordinate)),
            (12, k1.Symbol(profile.challenge_coordinate)),
            (13, k1.Symbol(profile.response_coordinate)),
            (
                14,
                _id_datum(profile.extractor_profile_id, "analysis.extractor-profile"),
            ),
            (
                15,
                _id_datum(
                    profile.extractor_algorithm_id, "foundation.portable-algorithm"
                ),
            ),
            (16, k1.Nat(profile.statement_anchor_value)),
            (
                17,
                _id_datum(
                    profile.challenge_domain_id,
                    "analysis.challenge-domain",
                ),
            ),
            (18, k1.Symbol(profile.check_coordinate)),
            (19, k1.Symbol(profile.terminal_coordinate)),
        )
    )


def _subject_bound_schnorr_pair_domain_id(
    profile: SchnorrSpecialSoundnessProfile,
) -> object:
    """Bind the quantified pair predicate to its exact semantic subjects."""

    body = _schnorr_profile_body(profile)
    predicate_law = analysis_profile_declaration_ref(
        ANALYSIS_PROPERTY_PROFILE,
        ANALYSIS_PROPERTY_PROFILE,
        "analysis.semantic-law",
        "finite-challenge-domain-v0",
    )
    return _legacy_component_id(
        "analysis.value-domain-profile",
        k1.DatumRecord(
            (
                (0, k1.Symbol("SchnorrSpecialSoundnessPair")),
                (1, body),
                (
                    2,
                    _id_datum(
                        profile.challenge_domain_id,
                        "analysis.challenge-domain",
                    ),
                ),
                (3, analysis_profile_declaration_ref_body(predicate_law)),
                (
                    4,
                    k1.Symbol(
                        "same-statement-and-commitment-distinct-challenges-"
                        "exact-protocol-check-terminal-canonical-challenge-order"
                    ),
                ),
            )
        ),
    )


def _schnorr_profile_id(profile: SchnorrSpecialSoundnessProfile) -> object:
    base = fresh_special_soundness_model(
        k=profile.extraction_arity,
        challenge_count=profile.challenge_count,
    )
    pair_domain_id = _subject_bound_schnorr_pair_domain_id(profile)
    quantifiers = tuple(
        replace(quantifier, domain_id=pair_domain_id)
        if quantifier.kind is QuantifierKind.FOR_ALL_VALUE
        else quantifier
        for quantifier in base.quantifiers
    )
    return experiment_model_id(replace(base, quantifiers=quantifiers))


def schnorr_relation_correspondence_hypothesis_id(
    profile: SchnorrSpecialSoundnessProfile,
) -> object:
    if (
        type(profile) is not SchnorrSpecialSoundnessProfile
        or profile._issuer is not _SCHNORR_PROFILE_ISSUER
        or profile.profile_id != _schnorr_profile_id(profile)
    ):
        raise AuthorityError("Schnorr relation hypothesis lacks an issued profile")
    source = derive_fresh_fs_relation_source(total_uniform_schnorr_case())
    if (
        source.protocol_source.fresh_protocol_id != profile.fresh_protocol_id
        or source.fresh_binding.binding_id != profile.fresh_binding_id
    ):
        raise AuthorityError("Schnorr relation premise selected another owner tuple")
    return _exact_premise_goal_id(
        "acceptance-relation-correspondence",
        (
            source.protocol_source.core_id,
            profile.fresh_protocol_id,
            profile.relation_definition_id,
            profile.relation_interface_id,
            profile.fresh_binding_id,
        ),
        _semantic_experiment_context(
            (source_manifest_id(source.fresh_manifest),),
            (profile.profile_id,),
        ),
        k1.DatumRecord(
            (
                (
                    0,
                    k1.DatumRecord(
                        (
                            (
                                0,
                                _id_datum(
                                    profile.relation_definition_id,
                                    "relations.definition",
                                ),
                            ),
                            (
                                1,
                                _id_datum(
                                    profile.relation_interface_id,
                                    "relations.interface",
                                ),
                            ),
                            (
                                2,
                                _id_datum(
                                    profile.fresh_binding_id,
                                    "relations.protocol-binding",
                                ),
                            ),
                        )
                    ),
                ),
                (
                    1,
                    _id_datum(profile.profile_id, "analysis.experiment-profile"),
                ),
            )
        ),
        selected_profile=ANALYSIS_PROPERTY_PROFILE,
    )


def derive_schnorr_special_soundness_profile(
    source: FreshFsRelationSource,
) -> SchnorrSpecialSoundnessProfile:
    """Select the exact Schnorr coordinates; do not prove the theorem."""

    require_fresh_fs_relation_source(source)
    case = source.case
    if (
        case.invocation is None
        or len(case.definitions) != 1
        or len(case.relation_interfaces) != 1
    ):
        raise PropertyError("bounded Schnorr profile needs one exact fixture relation")
    values = case.invocation.values
    if set(("g", "q", "p", "statement")) - set(values):
        raise PropertyError("bounded Schnorr fixture lacks public group coordinates")
    generator, order, modulus = values["g"], values["q"], values["p"]
    if any(type(item) is not int for item in (generator, order, modulus)):
        raise PropertyError("bounded Schnorr group coordinates must be exact integers")
    stock_case = k3.schnorr_case()
    if (modulus, order, generator) != (23, 11, 2):
        raise PropertyError("bounded Schnorr group must be exactly (p,q,g)=(23,11,2)")
    if (
        case.definitions != stock_case.definitions
        or case.relation_interfaces != stock_case.relation_interfaces
    ):
        raise PropertyError("bounded Schnorr relation definition or Interface changed")
    occurrence_by_name = {item.name: item for item in case.core.schedule}
    expected_kinds = {
        "commitment": k2.OccurrenceKind.PROVER_MESSAGE,
        "challenge": k2.OccurrenceKind.CHALLENGE,
        "response": k2.OccurrenceKind.PROVER_MESSAGE,
        "verify": k2.OccurrenceKind.CHECK,
        "terminal": k2.OccurrenceKind.TERMINAL,
    }
    if any(
        name not in occurrence_by_name or occurrence_by_name[name].kind is not kind
        for name, kind in expected_kinds.items()
    ):
        raise PropertyError("bounded Schnorr occurrence coordinates were changed")
    challenge = occurrence_by_name["challenge"]
    verify = occurrence_by_name["verify"]
    expected_core = stock_case.core
    expected_schedule = list(expected_core.schedule)
    expected_challenge_index = next(
        index
        for index, occurrence in enumerate(expected_schedule)
        if occurrence.name == "challenge"
    )
    expected_schedule[expected_challenge_index] = replace(
        expected_schedule[expected_challenge_index],
        challenge_domain=challenge.challenge_domain,
    )
    if case.core != replace(expected_core, schedule=tuple(expected_schedule)):
        raise PropertyError(
            "bounded Schnorr Core differs beyond the selected challenge set"
        )
    expected_check_refs = (
        k2.ValueRef.input("g"),
        k2.ValueRef.input("statement"),
        k2.ValueRef.occurrence("commitment"),
        k2.ValueRef.occurrence("challenge"),
        k2.ValueRef.occurrence("response"),
        k2.ValueRef.input("p"),
    )
    if (
        challenge.challenge_domain is None
        or verify.check_predicate is None
        or verify.check_predicate.kind is not k2.PredicateKind.SCHNORR
        or verify.check_predicate.refs != expected_check_refs
        or verify.check_predicate.parameters != (order,)
    ):
        raise PropertyError(
            "bounded Schnorr challenge or verifier equation was changed"
        )
    interface = case.relation_interfaces[0]
    if tuple((slot.name, slot.value_type) for slot in interface.public_instance) != (
        ("statement", k3.NAT),
    ) or tuple((slot.name, slot.value_type) for slot in interface.private_witness) != (
        ("secret", k3.NAT),
    ):
        raise PropertyError("bounded Schnorr relation interface was changed")
    binding = source.fresh_binding.binding
    plan_binding = source.fresh_plan_binding.binding
    if (
        len(binding.instances) != 1
        or binding.instances[0].name != "knowledge-instance"
        or binding.instances[0].relation_interface_id
        != k3.relation_interface_id(interface)
        or len(binding.public_edges) != 1
        or binding.public_edges[0].instance != "knowledge-instance"
        or binding.public_edges[0].slot != "statement"
        or type(binding.public_edges[0].source) is not k3.BindingRef
        or binding.public_edges[0].source.scope != "root"
        or binding.public_edges[0].source.input_name != "statement"
        or binding.public_edges[0].value_relation != k3.SAME_EXACT_TYPE
        or len(binding.claim_edges) != 1
        or binding.claim_edges[0].instance != "knowledge-instance"
        or binding.claim_edges[0].claim.origin is not k3.ClaimOrigin.INITIAL
        or binding.claim_edges[0].claim.claim != "knowledge"
        or len(plan_binding.witness_edges) != 1
        or plan_binding.witness_edges[0].slot != "secret"
        or plan_binding.witness_edges[0].witness_surface_key != "secret"
    ):
        raise PropertyError(
            "bounded Schnorr Statement, claim, or Witness map was changed"
        )
    statement_anchor = values["statement"]
    if type(statement_anchor) is not int or not 0 <= statement_anchor < (1 << 64):
        raise PropertyError(
            "bounded Schnorr Statement exceeds its exact NAT_U64 carrier"
        )
    challenge_domain_id = _schnorr_challenge_domain_id_from_projection(
        _source_schnorr_challenge_projection(source)
    )
    profile = SchnorrSpecialSoundnessProfile(
        None,
        case.definitions[0].definition_id,
        k3.relation_interface_id(interface),
        source.protocol_source.fresh_protocol_id,
        source.fresh_binding.binding_id,
        modulus,
        order,
        generator,
        challenge.challenge_domain.modulus,
        2,
        f"{binding.public_edges[0].instance}:{binding.public_edges[0].slot}",
        "commitment",
        "challenge",
        "response",
        SCHNORR_TRANSCRIPT_EXTRACTOR_PROFILE_ID,
        SCHNORR_EXTRACTOR_ALGORITHM,
        statement_anchor,
        challenge_domain_id,
        verify.name,
        occurrence_by_name["terminal"].name,
        _SCHNORR_PROFILE_ISSUER,
    )
    return replace(profile, profile_id=_schnorr_profile_id(profile))


def require_schnorr_special_soundness_profile(
    source: FreshFsRelationSource, profile: SchnorrSpecialSoundnessProfile
) -> None:
    if (
        type(profile) is not SchnorrSpecialSoundnessProfile
        or profile._issuer is not _SCHNORR_PROFILE_ISSUER
    ):
        raise AuthorityError("Schnorr source profile lacks Analysis issuance")
    expected = derive_schnorr_special_soundness_profile(source)
    if profile != expected or profile.profile_id != _schnorr_profile_id(profile):
        raise PropertyError("Schnorr source profile was substituted")


def _bound_schnorr_statement_value(
    source: FreshFsRelationSource,
    profile: SchnorrSpecialSoundnessProfile,
) -> int:
    """Resolve the exact instance Statement through the checked Fresh edge."""

    try:
        instance, slot = profile.statement_coordinate.split(":", 1)
    except ValueError as error:
        raise PropertyError("Schnorr Statement coordinate is malformed") from error
    selected = tuple(
        edge
        for edge in source.fresh_binding.binding.public_edges
        if edge.instance == instance and edge.slot == slot
    )
    if (
        len(selected) != 1
        or type(selected[0].source) is not k3.BindingRef
        or selected[0].value_relation != k3.SAME_EXACT_TYPE
    ):
        raise PropertyError("Schnorr profile has no unique checked Statement edge")
    binding_ref = selected[0].source
    if binding_ref.scope != "root":
        raise PropertyError("bounded Schnorr Statement must use the root scope")
    value = source.case.invocation.values.get(binding_ref.input_name)
    if type(value) is not int or value < 0:
        raise PropertyError("bound Schnorr Statement is not one exact natural")
    if value != profile.statement_anchor_value:
        raise PropertyError("bound Schnorr Statement disagrees with profile identity")
    return value


def _source_schnorr_challenge_projection(
    source: FreshFsRelationSource,
) -> k2.PublicCoinChallengeProjection:
    require_fresh_fs_relation_source(source)
    issued = _affirmative_pir_view(
        k2.issue_core_static_view(
            source.case.core,
            k2.StaticViewKind.PUBLIC_COIN,
            _Analysis_PUBLIC_COIN_VIEW_MANIFEST,
            consumer_id=_k3c_pir_view_consumer_id(),
            purpose_id=_k3c_pir_view_purpose_id("fresh", "public-coin-view"),
        ),
        "Core PublicCoinView",
    )
    projection = k2.resolve_public_coin_challenge_projection(
        issued,
        0,
        expected_consumer_id=_k3c_pir_view_consumer_id(),
        expected_purpose_id=_k3c_pir_view_purpose_id("fresh", "public-coin-view"),
    )
    challenge_ordinal, challenge = _fixed_setup_challenge(source)
    if (
        projection.challenge_coordinate.sequence_ordinal != 0
        or projection.challenge_coordinate.schedule_ordinal != challenge_ordinal
        or projection.challenge_coordinate.occurrence_name != challenge.name
        or projection.challenge_domain != challenge.challenge_domain
    ):
        raise PropertyError("Schnorr challenge projection selects another Core leaf")
    return projection


def _schnorr_fresh_owner_substitution(
    source: FreshFsRelationSource,
    profile: SchnorrSpecialSoundnessProfile,
    transcript: SchnorrTranscript,
) -> tuple[k2.ValueRef, dict[k2.ValueRef, k2.Value], k2.ValueRef]:
    """Build the exact protocol Check substitution from authenticated owner refs."""

    if type(transcript) is not SchnorrTranscript or any(
        type(item) is not int
        for item in (
            transcript.statement,
            transcript.commitment,
            transcript.challenge,
            transcript.response,
        )
    ):
        raise PropertyError("Schnorr transcript has the wrong exact shape")
    if any(
        not 0 <= item < (1 << 64)
        for item in (
            transcript.statement,
            transcript.commitment,
            transcript.challenge,
            transcript.response,
        )
    ):
        raise PropertyError(
            "Schnorr transcript field exceeds its exact NAT_U64 carrier"
        )
    checks = tuple(
        occurrence
        for occurrence in source.case.core.schedule
        if occurrence.kind is k2.OccurrenceKind.CHECK
    )
    terminals = tuple(
        occurrence
        for occurrence in source.case.core.schedule
        if occurrence.kind is k2.OccurrenceKind.TERMINAL
    )
    if len(checks) != 1 or len(terminals) != 1:
        raise PropertyError("bounded Schnorr lane needs one Check and one Terminal")
    check = checks[0]
    assert check.check_predicate is not None
    role_values = {
        profile.commitment_coordinate: transcript.commitment,
        profile.challenge_coordinate: transcript.challenge,
        profile.response_coordinate: transcript.response,
    }
    refs = tuple(dict.fromkeys((*check.guard.refs, *check.check_predicate.refs)))
    substitution: dict[k2.ValueRef, k2.Value] = {}
    for ref in refs:
        if ref.kind is k2.RefKind.INPUT:
            if ref.name == "statement":
                value = transcript.statement
            else:
                value = source.case.invocation.values.get(ref.name)
        else:
            value = role_values.get(ref.name)
        if value is None:
            raise PropertyError(
                "Schnorr Check has a value ref outside its exact owner closure"
            )
        substitution[ref] = value
    return (
        k2.ValueRef.occurrence(check.name),
        substitution,
        k2.ValueRef.occurrence(terminals[0].name),
    )


def exact_fresh_transcript_accepts(
    source: FreshFsRelationSource,
    profile: SchnorrSpecialSoundnessProfile,
    transcript: SchnorrTranscript,
) -> bool:
    """Evaluate only the exact Fresh-protocol Check and Terminal semantics."""

    require_schnorr_special_soundness_profile(source, profile)
    return _exact_fresh_transcript_accepts_after_profile_admission(
        source,
        profile,
        transcript,
    )


def _exact_fresh_transcript_accepts_after_profile_admission(
    source: FreshFsRelationSource,
    profile: SchnorrSpecialSoundnessProfile,
    transcript: SchnorrTranscript,
) -> bool:
    """Evaluate the owner path after the source/profile pair was admitted once."""

    if type(transcript) is not SchnorrTranscript or any(
        type(item) is not int
        for item in (
            transcript.statement,
            transcript.commitment,
            transcript.challenge,
            transcript.response,
        )
    ):
        raise PropertyError("Schnorr transcript has the wrong exact shape")
    if any(
        not 0 <= item < (1 << 64)
        for item in (
            transcript.statement,
            transcript.commitment,
            transcript.challenge,
            transcript.response,
        )
    ):
        return False
    if transcript.statement != _bound_schnorr_statement_value(source, profile):
        return False
    projection = _source_schnorr_challenge_projection(source)
    if not 0 <= transcript.challenge < projection.challenge_domain.modulus:
        return False
    check_ref, substitution, terminal_ref = _schnorr_fresh_owner_substitution(
        source, profile, transcript
    )
    check_result = k2.evaluate_check_ref(
        source.case.core,
        check_ref,
        substitution,
    )
    if check_result is not True:
        return False
    terminal = next(
        occurrence
        for occurrence in source.case.core.schedule
        if occurrence.name == terminal_ref.name
    )
    terminal_substitution = {
        ref: substitution[ref] for ref in terminal.guard.refs if ref in substitution
    }
    if len(terminal_substitution) != len(set(terminal.guard.refs)):
        raise PropertyError(
            "Schnorr Terminal guard escapes the exact Check substitution"
        )
    return (
        k2.evaluate_terminal_ref(
            source.case.core,
            terminal_ref,
            {check_ref: check_result},
            terminal_substitution,
        )
        is True
    )


def schnorr_admitted_pair_predicate(
    source: FreshFsRelationSource,
    profile: SchnorrSpecialSoundnessProfile,
    first: SchnorrTranscript,
    second: SchnorrTranscript,
) -> bool:
    """Recognize the one canonical accepted two-transcript representation."""

    require_schnorr_special_soundness_profile(source, profile)
    if type(first) is not SchnorrTranscript or type(second) is not SchnorrTranscript:
        raise PropertyError("Schnorr pair needs two exact transcripts")
    if (
        first.statement != second.statement
        or first.commitment != second.commitment
        or first.challenge == second.challenge
    ):
        return False
    projection = _source_schnorr_challenge_projection(source)
    if any(
        not 0 <= transcript.challenge < projection.challenge_domain.modulus
        for transcript in (first, second)
    ):
        return False
    first_challenge_body = k1.encode_datum(k1.Nat(first.challenge))
    second_challenge_body = k1.encode_datum(k1.Nat(second.challenge))
    if not first_challenge_body < second_challenge_body:
        return False
    return _exact_fresh_transcript_accepts_after_profile_admission(
        source, profile, first
    ) and _exact_fresh_transcript_accepts_after_profile_admission(
        source, profile, second
    )


def extract_schnorr_witness(
    source: FreshFsRelationSource,
    profile: SchnorrSpecialSoundnessProfile,
    first: SchnorrTranscript,
    second: SchnorrTranscript,
) -> AttemptOutcome:
    """Execute the selected two-transcript algebra, not its universal theorem."""

    try:
        if not schnorr_admitted_pair_predicate(source, profile, first, second):
            return AttemptOutcome(
                AttemptKind.CANNOT_ANSWER,
                detail="input is not one canonical admitted Schnorr pair",
            )
        denominator = (first.challenge - second.challenge) % profile.subgroup_order
        try:
            inverse = pow(denominator, -1, profile.subgroup_order)
        except ValueError:
            return AttemptOutcome(
                AttemptKind.CANNOT_ANSWER,
                detail="challenge difference is not invertible in the subgroup order",
            )
        witness = (
            (first.response - second.response) * inverse
        ) % profile.subgroup_order
        if pow(profile.generator, witness, profile.group_modulus) != first.statement:
            return AttemptOutcome(
                AttemptKind.CANNOT_ANSWER,
                detail="extracted value does not satisfy the bound Schnorr relation",
            )
        return _affirmative(
            ExtractedSchnorrWitness(
                witness, first, second, profile.profile_id, _SCHNORR_EXTRACTION_ISSUER
            )
        )
    except AuthorityError as error:
        return AttemptOutcome(AttemptKind.REFUSED, detail=str(error))
    except (k2.ModelError, k3.K3Error) as error:
        return AttemptOutcome(AttemptKind.MALFORMED, detail=str(error))
    except AnalysisError as error:
        return AttemptOutcome(AttemptKind.MALFORMED, detail=str(error))


# ---------------------------------------------------------------------------
# Checked finite-cover activation for one exact fixed extractor
# ---------------------------------------------------------------------------


FINITE_COVER_CERTIFICATE_KINDS = (
    "coverage",
    "quotient-factorization",
    "success-transfer",
)
FINITE_COVER_OPERATION_LABELS = (
    "representative-stream",
    "raw-domain",
    "representative-domain",
    "normalization",
    "representative-embedding",
    "candidate",
    "quotient-factorization",
    "representative-success",
    "success-transfer",
)


def _finite_cover_cache_coordinate(value: object) -> object:
    """Form a live-operation cache key, never a persistent semantic key."""

    if type(value) in (str, int, bytes, bool, type(None)):
        return value
    if type(value) is tuple:
        return tuple(_finite_cover_cache_coordinate(item) for item in value)
    internal_reference = getattr(value, "internal_reference", None)
    if callable(internal_reference):
        return (type(value).__name__, internal_reference())
    return (type(value).__name__, id(value))


def _with_finite_cover_derivation(
    label: str,
) -> Callable[[Callable[..., object]], Callable[..., object]]:
    """Memoize pure identity formation only during one live operation."""

    def decorate(function: Callable[..., object]) -> Callable[..., object]:
        @wraps(function)
        def scoped(*args: object, **kwargs: object) -> object:
            with _family_derivation_scope():
                key = (
                    "finite-cover",
                    label,
                    ANALYSIS_PROPERTY_PROFILE_ID,
                    tuple(_finite_cover_cache_coordinate(item) for item in args),
                    tuple(
                        (name, _finite_cover_cache_coordinate(value))
                        for name, value in sorted(kwargs.items())
                    ),
                )
                return _family_derivation_value(
                    key, lambda: function(*args, **kwargs)
                )

        return scoped

    return decorate


@dataclass(frozen=True)
class FiniteCoverStreamReceipt:
    validation_basis_id: object
    exact_representative_count: int
    ordered_representative_stream_digest: bytes
    ordered_evaluation_stream_digest: bytes
    terminal_count: int
    terminal_digest: bytes
    consumed_enumerator_steps: int
    consumed_member_evaluations: int


@dataclass(frozen=True)
class CheckedFixedExtractorJudgment:
    proposition_id: object
    semantic_basis_id: object
    support_id: object
    validation_basis_id: object
    qualification: object
    judgment_id: object
    certificate_judgment_ids: tuple[object, ...]
    stream_receipt: FiniteCoverStreamReceipt
    _issuer: object


_FINITE_COVER_JUDGMENT_ISSUER = object()


def _fixed_extractor_family_ref() -> object:
    return analysis_profile_declaration_ref(
        ANALYSIS_PROPERTY_PROFILE,
        ANALYSIS_PROPERTY_PROFILE,
        "analysis.property-family",
        "fixed-extractor-universal-correctness",
    )


@_with_finite_cover_derivation("exact-subjects")
def _finite_cover_exact_subjects(
    source: FreshFsRelationSource,
    profile: SchnorrSpecialSoundnessProfile,
) -> tuple[object, ...]:
    require_fresh_fs_relation_source(source)
    require_schnorr_special_soundness_profile(source, profile)
    return (
        source.protocol_source.fresh_protocol_id,
        profile.relation_definition_id,
        profile.fresh_binding_id,
        profile.challenge_domain_id,
        SCHNORR_EXTRACTOR_ALGORITHM,
    )


@_with_finite_cover_derivation("experiment-profile")
def fixed_extractor_experiment_profile_id(
    source: FreshFsRelationSource,
    profile: SchnorrSpecialSoundnessProfile,
) -> object:
    """Form the exact singleton-ForAllValue fixed-candidate experiment."""

    _finite_cover_exact_subjects(source, profile)
    base_id = experiment_model_id(
        fresh_special_soundness_model(
            k=profile.extraction_arity,
            challenge_count=profile.challenge_count,
        )
    )
    base = _formed_analysis_body(base_id, "analysis.experiment-profile")
    quantified_domain = Quantifier(
        QuantifierKind.FOR_ALL_VALUE,
        "accepted-transcript-pair",
        _subject_bound_schnorr_pair_domain_id(profile),
    )
    return _analysis_id(
        "analysis.experiment-profile",
        replace(
            base,
            family=analysis_profile_declaration_ref_body(
                _fixed_extractor_family_ref()
            ),
            quantifier_prefix=k1.DatumSeq((_quantifier_body(quantified_domain, 0),)),
            role_interfaces=k1.DatumSeq(
                (
                    _id_datum(
                        profile.extractor_profile_id,
                        "analysis.extractor-profile",
                    ),
                )
            ),
            failure_abort_and_noncompletion_law=k1.Symbol(
                "candidate-failure-on-one-member-is-an-exact-counterexample"
            ),
            termination_law=k1.Symbol(
                "total-on-this-exact-finite-domain-no-efficiency-conclusion"
            ),
            output_type=k1.Symbol(
                "deterministic-fixed-extractor-universal-judgment"
            ),
        ),
    )


@_with_finite_cover_derivation("fixed-conclusion")
def _fixed_extractor_conclusion_body(
    source: FreshFsRelationSource,
    profile: SchnorrSpecialSoundnessProfile,
) -> object:
    experiment_id = fixed_extractor_experiment_profile_id(source, profile)
    return k1.DatumVariant(
        2,
        k1.DatumRecord(
            (
                (
                    0,
                    _id_datum(experiment_id, "analysis.experiment-profile"),
                ),
                (
                    1,
                    _id_datum(
                        profile.extractor_profile_id,
                        "analysis.extractor-profile",
                    ),
                ),
                (
                    2,
                    _id_datum(
                        SCHNORR_EXTRACTOR_ALGORITHM,
                        "foundation.portable-algorithm",
                    ),
                ),
                (3, k1.Nat(profile.statement_anchor_value)),
                (4, k1.Nat(profile.challenge_count)),
                (5, k1.Symbol("affirmative-exact-finite-subject-only")),
            )
        ),
    )


@_with_finite_cover_derivation("fixed-question-payload")
def _fixed_extractor_question_payload(
    source: FreshFsRelationSource,
    profile: SchnorrSpecialSoundnessProfile,
) -> object:
    return k1.DatumRecord(
        (
            (0, k1.Symbol("fixed-extractor-universal")),
            (1, _id_datum(profile.profile_id, "analysis.experiment-profile")),
            (
                2,
                _id_datum(
                    profile.extractor_profile_id, "analysis.extractor-profile"
                ),
            ),
            (
                3,
                _id_datum(
                    SCHNORR_EXTRACTOR_ALGORITHM,
                    "foundation.portable-algorithm",
                ),
            ),
            (4, k1.value_type_datum(FINITE_COVER_ARITHMETIC.raw_pair_type)),
            (
                5,
                k1.value_type_datum(
                    FINITE_COVER_ARITHMETIC.representative_pair_type
                ),
            ),
            (6, _fixed_extractor_conclusion_body(source, profile)),
        )
    )


@_with_finite_cover_derivation("fixed-question")
def fixed_extractor_question_id(
    source: FreshFsRelationSource,
    profile: SchnorrSpecialSoundnessProfile,
) -> object:
    experiment_id = fixed_extractor_experiment_profile_id(source, profile)
    return _analysis_id(
        "analysis.question",
        AnalysisQuestionBodyV0(
            _fixed_extractor_family_ref(),
            _finite_cover_exact_subjects(source, profile),
            _semantic_experiment_context(
                (source_manifest_id(source.fresh_manifest),),
                (experiment_id,),
            ),
            _fixed_extractor_question_payload(source, profile),
        ),
    )


@_with_finite_cover_derivation("fixed-goal")
def fixed_extractor_goal_id(
    source: FreshFsRelationSource,
    profile: SchnorrSpecialSoundnessProfile,
) -> object:
    return _analysis_id(
        "analysis.goal",
        AnalysisGoalBodyV0(fixed_extractor_question_id(source, profile)),
    )


@_with_finite_cover_derivation("fixed-proposition")
def fixed_extractor_proposition_id(
    source: FreshFsRelationSource,
    profile: SchnorrSpecialSoundnessProfile,
) -> object:
    return _analysis_id(
        "analysis.proposition",
        AnalysisPropositionBodyV0(
            fixed_extractor_goal_id(source, profile),
            analysis_hypothesis_context_id(()),
        ),
    )


def _require_certificate_kind(kind: str) -> str:
    if type(kind) is not str or kind not in FINITE_COVER_CERTIFICATE_KINDS:
        raise PropertyError("finite-cover certificate kind is not active")
    return kind


@_with_finite_cover_derivation("certificate-question-payload")
def _finite_cover_certificate_question_payload(
    source: FreshFsRelationSource,
    profile: SchnorrSpecialSoundnessProfile,
    kind: str,
) -> object:
    _require_certificate_kind(kind)
    return k1.DatumRecord(
        (
            (0, k1.Symbol("finite-cover-certificate")),
            (1, k1.Symbol(kind)),
            (2, _id_datum(profile.profile_id, "analysis.experiment-profile")),
            (
                3,
                _id_datum(
                    SCHNORR_EXTRACTOR_ALGORITHM,
                    "foundation.portable-algorithm",
                ),
            ),
            (
                4,
                _id_datum(
                    fixed_extractor_proposition_id(source, profile),
                    "analysis.proposition",
                ),
            ),
        )
    )


@_with_finite_cover_derivation("certificate-question")
def finite_cover_certificate_question_id(
    source: FreshFsRelationSource,
    profile: SchnorrSpecialSoundnessProfile,
    kind: str,
) -> object:
    return _analysis_id(
        "analysis.question",
        AnalysisQuestionBodyV0(
            _fixed_extractor_family_ref(),
            _finite_cover_exact_subjects(source, profile),
            _semantic_experiment_context(
                (source_manifest_id(source.fresh_manifest),),
                (fixed_extractor_experiment_profile_id(source, profile),),
            ),
            _finite_cover_certificate_question_payload(source, profile, kind),
        ),
    )


@_with_finite_cover_derivation("certificate-goal")
def finite_cover_certificate_goal_id(
    source: FreshFsRelationSource,
    profile: SchnorrSpecialSoundnessProfile,
    kind: str,
) -> object:
    return _analysis_id(
        "analysis.goal",
        AnalysisGoalBodyV0(
            finite_cover_certificate_question_id(source, profile, kind)
        ),
    )


@_with_finite_cover_derivation("certificate-proposition")
def finite_cover_certificate_proposition_id(
    source: FreshFsRelationSource,
    profile: SchnorrSpecialSoundnessProfile,
    kind: str,
) -> object:
    return _analysis_id(
        "analysis.proposition",
        AnalysisPropositionBodyV0(
            finite_cover_certificate_goal_id(source, profile, kind),
            analysis_hypothesis_context_id(()),
        ),
    )


def _finite_cover_law_ref(label: str) -> object:
    return analysis_profile_declaration_ref_body(
        analysis_profile_declaration_ref(
            ANALYSIS_PROPERTY_PROFILE,
            ANALYSIS_PROPERTY_PROFILE,
            "analysis.semantic-law",
            label,
        )
    )


@_with_finite_cover_derivation("target-body")
def _finite_cover_target_body(
    source: FreshFsRelationSource,
    profile: SchnorrSpecialSoundnessProfile,
) -> object:
    proposition_id = fixed_extractor_proposition_id(source, profile)
    certificate_goals = tuple(
        finite_cover_certificate_goal_id(source, profile, kind)
        for kind in FINITE_COVER_CERTIFICATE_KINDS
    )
    return k1.DatumRecord(
        (
            (0, _id_datum(proposition_id, "analysis.proposition")),
            (
                1,
                _id_datum(
                    fixed_extractor_experiment_profile_id(source, profile),
                    "analysis.experiment-profile",
                ),
            ),
            (2, k1.value_type_datum(FINITE_COVER_ARITHMETIC.raw_pair_type)),
            (3, _finite_cover_law_ref("finite-cover-raw-domain-v0")),
            (4, _finite_cover_law_ref("finite-cover-cover-schema-v0")),
            (
                5,
                k1.value_type_datum(
                    FINITE_COVER_ARITHMETIC.representative_pair_type
                ),
            ),
            (6, _finite_cover_law_ref("finite-cover-representative-domain-v0")),
            (
                7,
                _id_datum(
                    FINITE_COVER_ARITHMETIC.normalization_algorithm.identity,
                    "foundation.portable-algorithm",
                ),
            ),
            (
                8,
                _id_datum(
                    FINITE_COVER_ARITHMETIC.embedding_algorithm.identity,
                    "foundation.portable-algorithm",
                ),
            ),
            (
                9,
                _id_datum(
                    FINITE_COVER_ARITHMETIC.representative_stream_algorithm.identity,
                    "foundation.portable-algorithm",
                ),
            ),
            (
                10,
                _id_datum(
                    profile.extractor_profile_id, "analysis.extractor-profile"
                ),
            ),
            (
                11,
                _id_datum(
                    SCHNORR_EXTRACTOR_ALGORITHM,
                    "foundation.portable-algorithm",
                ),
            ),
            (12, _finite_cover_law_ref("finite-cover-candidate-schema-v0")),
            (13, _finite_cover_law_ref("finite-cover-output-congruence-v0")),
            (14, _finite_cover_law_ref("finite-cover-representative-success-v0")),
            (15, _finite_cover_law_ref("finite-cover-raw-success-v0")),
            (
                16,
                k1.DatumSeq(
                    tuple(
                        _id_datum(item, "analysis.goal")
                        for item in certificate_goals
                    )
                ),
            ),
            (
                17,
                _id_datum(
                    FINITE_COVER_ARITHMETIC.module_id,
                    "foundation.semantic-module",
                ),
            ),
            (18, k1.Nat(308)),
            (19, k1.BytesValue(FINITE_COVER_ARITHMETIC.representative_stream_digest)),
        )
    )


@_with_finite_cover_derivation("certificate-conclusion")
def _finite_cover_certificate_conclusion(
    source: FreshFsRelationSource,
    profile: SchnorrSpecialSoundnessProfile,
    kind: str,
) -> object:
    return k1.DatumRecord(
        (
            (0, k1.Symbol(_require_certificate_kind(kind))),
            (
                1,
                _id_datum(
                    finite_cover_certificate_goal_id(source, profile, kind),
                    "analysis.goal",
                ),
            ),
            (2, _finite_cover_target_body(source, profile)),
            (3, k1.Symbol("affirmative-exact-certificate-only")),
        )
    )


@_with_finite_cover_derivation("checker-contract")
def _finite_cover_checker_contract_id(label: str) -> object:
    if label not in FINITE_COVER_OPERATION_LABELS:
        raise PropertyError("unknown finite-cover checker operation")
    body = k1.DatumRecord(
        (
            (0, k1.Symbol(label)),
            (1, _finite_cover_law_ref("finite-cover-operation-binding-v0")),
            (2, _finite_cover_semantic_operation_body(label)),
            (3, k1.Symbol("python-reference-provider-with-exact-closed-abi")),
        )
    )
    return k1.content_id(
        "analysis.finite-cover-checker-contract",
        k1.encode_datum(body),
        semantic_regime=k1.SEMANTIC_REGIME_ID,
    )


def _finite_cover_semantic_operation_body(label: str) -> object:
    if label == "representative-stream":
        return k1.DatumVariant(
            0,
            k1.DatumRecord(
                (
                    (
                        0,
                        _id_datum(
                            FINITE_COVER_ARITHMETIC.representative_stream_algorithm.identity,
                            "foundation.portable-algorithm",
                        ),
                    ),
                    (1, _finite_cover_law_ref("finite-cover-stream-progress-v0")),
                )
            ),
        )
    if label == "representative-domain":
        return k1.DatumVariant(
            2,
            k1.DatumRecord(
                (
                    (0, _finite_cover_law_ref("finite-cover-representative-domain-v0")),
                    (1, _finite_cover_law_ref("finite-cover-cover-schema-v0")),
                )
            ),
        )
    if label == "raw-domain":
        return k1.DatumVariant(
            1,
            k1.DatumRecord(
                (
                    (0, _finite_cover_law_ref("finite-cover-raw-domain-v0")),
                    (1, _finite_cover_law_ref("finite-cover-cover-schema-v0")),
                )
            ),
        )
    if label == "normalization":
        return k1.DatumVariant(
            3,
            k1.DatumRecord(
                (
                    (
                        0,
                        _id_datum(
                            FINITE_COVER_ARITHMETIC.normalization_algorithm.identity,
                            "foundation.portable-algorithm",
                        ),
                    ),
                    (1, _finite_cover_law_ref("finite-cover-cover-schema-v0")),
                )
            ),
        )
    if label == "representative-embedding":
        return k1.DatumVariant(
            4,
            k1.DatumRecord(
                (
                    (
                        0,
                        _id_datum(
                            FINITE_COVER_ARITHMETIC.embedding_algorithm.identity,
                            "foundation.portable-algorithm",
                        ),
                    ),
                    (1, _finite_cover_law_ref("finite-cover-cover-schema-v0")),
                )
            ),
        )
    if label == "candidate":
        return k1.DatumVariant(
            5,
            k1.DatumRecord(
                (
                    (
                        0,
                        _id_datum(
                            FINITE_COVER_ARITHMETIC.candidate_algorithm.identity,
                            "foundation.portable-algorithm",
                        ),
                    ),
                    (1, _finite_cover_law_ref("finite-cover-candidate-schema-v0")),
                )
            ),
        )
    if label == "quotient-factorization":
        return k1.DatumVariant(
            6,
            k1.DatumRecord(
                (
                    (0, _finite_cover_law_ref("finite-cover-raw-domain-v0")),
                    (
                        1,
                        _id_datum(
                            FINITE_COVER_ARITHMETIC.normalization_algorithm.identity,
                            "foundation.portable-algorithm",
                        ),
                    ),
                    (
                        2,
                        _id_datum(
                            FINITE_COVER_ARITHMETIC.embedding_algorithm.identity,
                            "foundation.portable-algorithm",
                        ),
                    ),
                    (
                        3,
                        _id_datum(
                            FINITE_COVER_ARITHMETIC.candidate_algorithm.identity,
                            "foundation.portable-algorithm",
                        ),
                    ),
                    (4, _finite_cover_law_ref("finite-cover-output-congruence-v0")),
                    (
                        5,
                        _finite_cover_law_ref(
                            "finite-cover-factorization-certificate-v0"
                        ),
                    ),
                )
            ),
        )
    if label == "representative-success":
        return k1.DatumVariant(
            7,
            k1.DatumRecord(
                (
                    (0, _finite_cover_law_ref("finite-cover-representative-success-v0")),
                    (1, _finite_cover_law_ref("finite-cover-success-schema-v0")),
                )
            ),
        )
    if label == "success-transfer":
        return k1.DatumVariant(
            8,
            k1.DatumRecord(
                (
                    (0, _finite_cover_law_ref("finite-cover-representative-success-v0")),
                    (1, _finite_cover_law_ref("finite-cover-output-congruence-v0")),
                    (2, _finite_cover_law_ref("finite-cover-raw-success-v0")),
                    (
                        3,
                        _finite_cover_law_ref(
                            "finite-cover-transfer-certificate-v0"
                        ),
                    ),
                )
            ),
        )
    raise PropertyError("unknown finite-cover checker operation")


@_with_finite_cover_derivation("validation-basis")
def finite_cover_validation_basis_id() -> object:
    checker_entries = k1.DatumSeq(
        tuple(
            k1.DatumRecord(
                (
                    (0, k1.Nat(ordinal)),
                    (1, k1.Symbol(label)),
                    (
                        2,
                        _finite_cover_semantic_operation_body(label),
                    ),
                    (
                        3,
                        _id_datum(
                            _finite_cover_checker_contract_id(label),
                            "analysis.finite-cover-checker-contract",
                        ),
                    ),
                )
            )
            for ordinal, label in enumerate(FINITE_COVER_OPERATION_LABELS)
        )
    )
    translations = k1.DatumSeq(
        tuple(
            k1.DatumRecord(
                (
                    (0, k1.Nat(ordinal)),
                    (1, k1.Symbol(label)),
                    (2, k1.Symbol("exact-canonical-input-translation")),
                    (3, k1.Symbol("exact-canonical-output-translation")),
                )
            )
            for ordinal, label in enumerate(FINITE_COVER_OPERATION_LABELS)
        )
    )
    controls = k1.DatumSeq(
        (
            k1.DatumRecord(
                (
                    (0, k1.Symbol("representative-stream-steps")),
                    (1, k1.Nat(309)),
                )
            ),
            k1.DatumRecord(
                (
                    (0, k1.Symbol("representative-member-evaluations")),
                    (1, k1.Nat(308)),
                )
            ),
        )
    )
    residual = analysis_profile_declaration_ref(
        ANALYSIS_PROPERTY_PROFILE,
        ANALYSIS_KERNEL_PROFILE,
        "analysis.residual-trust-root",
        "python-runtime-and-reference-model",
    )
    return _analysis_id(
        "analysis.validation-basis",
        AnalysisValidationBasisBodyV0(
            checker_entries,
            translations,
            controls,
            k1.DatumSeq(()),
            k1.DatumSeq((analysis_profile_declaration_ref_body(residual),)),
        ),
    )


@_with_finite_cover_derivation("operation-policy")
def _finite_cover_operation_policy_id(
    proposition_id: object,
) -> object:
    return _analysis_operation_policy_id(
        proposition_id,
        (
            (
                "finite-fixed-extractor",
                ("fixed-extractor-universal-correctness",),
            ),
        ),
        profile=ANALYSIS_PROPERTY_PROFILE,
    )


@_with_finite_cover_derivation("certificate-semantic-basis")
def finite_cover_certificate_semantic_basis_id(
    source: FreshFsRelationSource,
    profile: SchnorrSpecialSoundnessProfile,
    kind: str,
) -> object:
    proposition_id = fixed_extractor_proposition_id(source, profile)
    return _analysis_id(
        "analysis.semantic-basis",
        AnalysisSemanticBasisBodyV0(
            _fixed_extractor_family_ref(),
            finite_cover_certificate_question_id(source, profile, kind),
            _native_rule_source(
                ANALYSIS_PROPERTY_PROFILE,
                ANALYSIS_PROPERTY_PROFILE,
                "checked-finite-cover-certificate",
                k1.DatumRecord(
                    (
                        (0, k1.Symbol(_require_certificate_kind(kind))),
                        (1, _finite_cover_target_body(source, profile)),
                    )
                ),
            ),
            k1.DatumSeq(()),
            complete_read_purpose_requirements(
                concrete_manifest_ids=(source_manifest_id(source.fresh_manifest),)
            ),
            _conclusion_schema_ref(
                ANALYSIS_PROPERTY_PROFILE,
                ANALYSIS_PROPERTY_PROFILE,
                "finite-cover-certificate-conclusion-v0",
            ),
            k1.DatumRecord(
                (
                    (0, k1.Symbol("checked-finite-cover-certificate")),
                    (1, k1.Symbol(kind)),
                    (2, _id_datum(proposition_id, "analysis.proposition")),
                )
            ),
        ),
    )


@_with_finite_cover_derivation("fixed-semantic-basis")
def fixed_extractor_semantic_basis_id(
    source: FreshFsRelationSource,
    profile: SchnorrSpecialSoundnessProfile,
) -> object:
    certificate_goals = tuple(
        finite_cover_certificate_goal_id(source, profile, kind)
        for kind in FINITE_COVER_CERTIFICATE_KINDS
    )
    return _analysis_id(
        "analysis.semantic-basis",
        AnalysisSemanticBasisBodyV0(
            _fixed_extractor_family_ref(),
            fixed_extractor_question_id(source, profile),
            _native_rule_source(
                ANALYSIS_PROPERTY_PROFILE,
                ANALYSIS_PROPERTY_PROFILE,
                "checked-finite-cover-universal-discharge",
                _finite_cover_target_body(source, profile),
            ),
            k1.DatumSeq(
                tuple(
                    k1.DatumVariant(
                        1, _id_datum(goal_id, "analysis.goal")
                    )
                    for goal_id in certificate_goals
                )
            ),
            complete_read_purpose_requirements(
                concrete_manifest_ids=(source_manifest_id(source.fresh_manifest),)
            ),
            _conclusion_schema_ref(
                ANALYSIS_PROPERTY_PROFILE,
                ANALYSIS_PROPERTY_PROFILE,
                "fixed-extractor-universal-conclusion-v0",
            ),
            k1.DatumRecord(
                (
                    (0, k1.Symbol("checked-exact-finite-cover")),
                    (1, _finite_cover_target_body(source, profile)),
                    (
                        2,
                        k1.Symbol(
                            "no-efficiency-family-asymptotic-probabilistic-or-security-lift"
                        ),
                    ),
                )
            ),
        ),
    )


@_with_finite_cover_derivation("empty-support")
def _finite_cover_empty_support_id(
    semantic_basis_id: object,
    proposition_id: object,
) -> object:
    return _analysis_support_instantiation_id(
        profile=ANALYSIS_PROPERTY_PROFILE,
        semantic_basis_id=semantic_basis_id,
        proposition_id=proposition_id,
    )


@_with_finite_cover_derivation("support-bindings")
def _finite_cover_support_bindings(
    source: FreshFsRelationSource,
    profile: SchnorrSpecialSoundnessProfile,
    certificate_judgment_ids: tuple[object, ...],
) -> object:
    if (
        type(certificate_judgment_ids) is not tuple
        or len(certificate_judgment_ids) != 3
    ):
        raise PropertyError("finite-cover discharge needs exactly three certificates")
    return k1.DatumSeq(
        tuple(
            k1.DatumRecord(
                (
                    (0, k1.Nat(ordinal)),
                    (
                        1,
                        k1.DatumRecord(
                            (
                                (
                                    0,
                                    _id_datum(
                                        finite_cover_certificate_goal_id(
                                            source, profile, kind
                                        ),
                                        "analysis.goal",
                                    ),
                                ),
                                (
                                    1,
                                    _id_datum(
                                        judgment_id,
                                        "analysis.judgment-record",
                                    ),
                                ),
                            )
                        ),
                    ),
                )
            )
            for ordinal, (kind, judgment_id) in enumerate(
                zip(
                    FINITE_COVER_CERTIFICATE_KINDS,
                    certificate_judgment_ids,
                    strict=True,
                )
            )
        )
    )


@_with_finite_cover_derivation("support")
def finite_cover_support_id(
    source: FreshFsRelationSource,
    profile: SchnorrSpecialSoundnessProfile,
    certificate_judgment_ids: tuple[object, ...],
) -> object:
    return _analysis_support_instantiation_id(
        profile=ANALYSIS_PROPERTY_PROFILE,
        semantic_basis_id=fixed_extractor_semantic_basis_id(source, profile),
        proposition_id=fixed_extractor_proposition_id(source, profile),
        non_hypothesis_premise_bindings=_finite_cover_support_bindings(
            source, profile, certificate_judgment_ids
        ),
    )


def _datum_pair(value: object) -> tuple[SchnorrTranscript, SchnorrTranscript]:
    if type(value) is k1.CanonicalValue:
        datum = value.datum
    else:
        datum = value
    if type(datum) is not k1.DatumRecord or tuple(dict(datum.fields)) != (0, 1):
        raise PropertyError("finite-cover pair datum has another shape")

    def transcript(item: object) -> SchnorrTranscript:
        if type(item) is not k1.DatumRecord or tuple(dict(item.fields)) != (0, 1, 2, 3):
            raise PropertyError("finite-cover transcript datum has another shape")
        fields = dict(item.fields)
        if any(type(fields[index]) is not k1.Nat for index in range(4)):
            raise PropertyError("finite-cover transcript leaf is not a natural")
        return SchnorrTranscript(*(fields[index].value for index in range(4)))

    fields = dict(datum.fields)
    return transcript(fields[0]), transcript(fields[1])


def _raw_pair_value(
    first: SchnorrTranscript,
    second: SchnorrTranscript,
) -> object:
    datum = k1.DatumRecord(
        (
            (
                0,
                k1.DatumRecord(
                    tuple(
                        (index, k1.Nat(value))
                        for index, value in enumerate(
                            (
                                first.statement,
                                first.commitment,
                                first.challenge,
                                first.response,
                            )
                        )
                    )
                ),
            ),
            (
                1,
                k1.DatumRecord(
                    tuple(
                        (index, k1.Nat(value))
                        for index, value in enumerate(
                            (
                                second.statement,
                                second.commitment,
                                second.challenge,
                                second.response,
                            )
                        )
                    )
                ),
            ),
        )
    )
    return k1.admit_value(FINITE_COVER_ARITHMETIC.raw_pair_type, datum)


def _representative_value(datum: object) -> object:
    return k1.admit_value(
        FINITE_COVER_ARITHMETIC.representative_pair_type, datum
    )


def _portable_success(
    algorithm: object,
    inputs: tuple[object, ...],
    what: str,
) -> object:
    outcome = FINITE_COVER_PORTABLE_EVALUATOR.evaluate(algorithm, inputs)
    if outcome.kind != "success" or outcome.value is None:
        raise AuthorityError(
            f"finite-cover {what} did not complete successfully: {outcome.kind}"
        )
    return outcome.value


def _finite_cover_member_after_source_admission(
    profile: SchnorrSpecialSoundnessProfile,
    first: SchnorrTranscript,
    second: SchnorrTranscript,
) -> bool:
    """Execute the exact admitted pair law after authenticating its owner once.

    ``require_schnorr_special_soundness_profile`` proves that these coordinates
    are the selected Fresh Core's Schnorr Check, Terminal, statement edge, and
    challenge domain.  Reconstructing those owner views for every member would
    change no judgment and would turn a 308-element finite check into repeated
    profile formation work.
    """

    if type(first) is not SchnorrTranscript or type(second) is not SchnorrTranscript:
        raise PropertyError("finite-cover member needs two exact transcripts")
    values = (
        first.statement,
        first.commitment,
        first.challenge,
        first.response,
        second.statement,
        second.commitment,
        second.challenge,
        second.response,
    )
    if any(type(item) is not int or not 0 <= item < (1 << 64) for item in values):
        return False
    if (
        first.statement != profile.statement_anchor_value
        or second.statement != first.statement
        or second.commitment != first.commitment
        or not 0 <= first.challenge < profile.challenge_count
        or not 0 <= second.challenge < profile.challenge_count
        or k1.encode_datum(k1.Nat(first.challenge))
        >= k1.encode_datum(k1.Nat(second.challenge))
    ):
        return False

    def accepts(transcript: SchnorrTranscript) -> bool:
        return pow(
            profile.generator,
            transcript.response,
            profile.group_modulus,
        ) == (
            transcript.commitment
            * pow(
                transcript.statement,
                transcript.challenge,
                profile.group_modulus,
            )
        ) % profile.group_modulus

    return accepts(first) and accepts(second)


def _checked_quotient_factorization_receipt(
    profile: SchnorrSpecialSoundnessProfile,
) -> object:
    try:
        receipt = finite_cover.check_quotient_factorization_basis(
            k1,
            FINITE_COVER_ARITHMETIC,
            group_modulus=profile.group_modulus,
            subgroup_order=profile.subgroup_order,
            generator=profile.generator,
            statement=profile.statement_anchor_value,
            challenge_count=profile.challenge_count,
        )
    except (TypeError, ValueError) as error:
        raise AuthorityError(
            f"finite-cover quotient factorization basis failed: {error}"
        ) from error
    if (
        receipt.normalization_algorithm_id
        != FINITE_COVER_ARITHMETIC.normalization_algorithm.identity
        or receipt.embedding_algorithm_id
        != FINITE_COVER_ARITHMETIC.embedding_algorithm.identity
        or receipt.candidate_algorithm_id != SCHNORR_EXTRACTOR_ALGORITHM
    ):
        raise AuthorityError(
            "finite-cover quotient factorization binds another exact operation"
        )
    return receipt


def _validate_finite_cover_certificate_semantics(kind: str) -> None:
    """Validate one exact quotient law, never a broader theorem claim."""

    kind = _require_certificate_kind(kind)
    source = _SCHNORR_PINNED_SOURCE
    profile = _SCHNORR_PINNED_PROFILE
    require_schnorr_special_soundness_profile(source, profile)
    representatives = tuple(FINITE_COVER_ARITHMETIC.representative_datums)
    encoded_representatives = tuple(k1.encode_datum(item) for item in representatives)
    if (
        len(representatives) != 308
        or len(set(encoded_representatives)) != 308
        or encoded_representatives != tuple(sorted(encoded_representatives))
    ):
        raise AuthorityError("finite-cover canonical representatives are incomplete")

    if kind == "coverage":
        residue_members = []
        for commitment in range(profile.group_modulus):
            for first_challenge in range(profile.challenge_count):
                for second_challenge in range(
                    first_challenge + 1, profile.challenge_count
                ):
                    first_responses = tuple(
                        response
                        for response in range(profile.subgroup_order)
                        if pow(profile.generator, response, profile.group_modulus)
                        == (
                            commitment
                            * pow(
                                profile.statement_anchor_value,
                                first_challenge % profile.subgroup_order,
                                profile.group_modulus,
                            )
                        )
                        % profile.group_modulus
                    )
                    second_responses = tuple(
                        response
                        for response in range(profile.subgroup_order)
                        if pow(profile.generator, response, profile.group_modulus)
                        == (
                            commitment
                            * pow(
                                profile.statement_anchor_value,
                                second_challenge % profile.subgroup_order,
                                profile.group_modulus,
                            )
                        )
                        % profile.group_modulus
                    )
                    for first_response in first_responses:
                        for second_response in second_responses:
                            residue_members.append(
                                _raw_pair_value(
                                    SchnorrTranscript(
                                        profile.statement_anchor_value,
                                        commitment,
                                        first_challenge,
                                        first_response,
                                    ),
                                    SchnorrTranscript(
                                        profile.statement_anchor_value,
                                        commitment,
                                        second_challenge,
                                        second_response,
                                    ),
                                ).datum
                            )
        encoded_residue_members = tuple(
            sorted(k1.encode_datum(item) for item in residue_members)
        )
        if encoded_residue_members != encoded_representatives:
            raise AuthorityError(
                "finite-cover residues do not equal the exact accepted quotient"
            )
        for datum in representatives:
            representative = _representative_value(datum)
            embedded = _portable_success(
                FINITE_COVER_ARITHMETIC.embedding_algorithm,
                (representative,),
                "representative embedding",
            )
            first, second = _datum_pair(embedded)
            if not _finite_cover_member_after_source_admission(
                profile, first, second
            ):
                raise AuthorityError(
                    "finite-cover representative does not embed to a raw member"
                )
        return

    if kind == "quotient-factorization":
        _checked_quotient_factorization_receipt(profile)
        for datum in representatives:
            representative = _representative_value(datum)
            embedded = _portable_success(
                FINITE_COVER_ARITHMETIC.embedding_algorithm,
                (representative,),
                "representative embedding",
            )
            canonical_output = _portable_success(
                FINITE_COVER_ARITHMETIC.candidate_algorithm,
                (embedded,),
                "candidate",
            )
            normalized = _portable_success(
                FINITE_COVER_ARITHMETIC.normalization_algorithm,
                (embedded,),
                "normalization",
            )
            if normalized.datum != datum:
                raise AuthorityError(
                    "finite-cover representative embedding is not a normalization section"
                )
            normalized_embedding = _portable_success(
                FINITE_COVER_ARITHMETIC.embedding_algorithm,
                (normalized,),
                "normalized representative embedding",
            )
            normalized_output = _portable_success(
                FINITE_COVER_ARITHMETIC.candidate_algorithm,
                (normalized_embedding,),
                "normalized candidate",
            )
            if normalized_output.datum != canonical_output.datum:
                raise AuthorityError(
                    "finite-cover candidate disagrees on the canonical quotient section"
                )
        return

    for datum in representatives:
        representative = _representative_value(datum)
        embedded = _portable_success(
            FINITE_COVER_ARITHMETIC.embedding_algorithm,
            (representative,),
            "representative embedding",
        )
        output = _portable_success(
            FINITE_COVER_ARITHMETIC.candidate_algorithm,
            (embedded,),
            "candidate",
        )
        first, second = _datum_pair(embedded)
        if (
            output.datum.value != 3
            or pow(profile.generator, output.datum.value, profile.group_modulus)
            != first.statement
            or first.statement != second.statement
        ):
            raise AuthorityError(
                "finite-cover representative success does not transfer to the relation"
            )


def _run_finite_cover_stream() -> FiniteCoverStreamReceipt:
    source = _SCHNORR_PINNED_SOURCE
    profile = _SCHNORR_PINNED_PROFILE
    require_schnorr_special_soundness_profile(source, profile)
    state = 0
    seen_states: set[int] = set()
    seen_representatives: set[bytes] = set()
    stream_hash = hashlib.sha256()
    evaluation_hash = hashlib.sha256()
    evaluations = 0
    previous_body: bytes | None = None
    terminal_count = -1
    terminal_digest = b""
    while True:
        if state in seen_states or len(seen_states) >= 309:
            raise AuthorityError("finite-cover stream repeated or exceeded its state bound")
        seen_states.add(state)
        state_value = k1.admit_value(
            FINITE_COVER_ARITHMETIC.stream_state_type, k1.Nat(state)
        )
        outcome = FINITE_COVER_PORTABLE_EVALUATOR.evaluate(
            FINITE_COVER_ARITHMETIC.representative_stream_algorithm,
            (state_value,),
        )
        if outcome.kind != "success" or outcome.value is None:
            raise AuthorityError(
                f"finite-cover representative stream failed: {outcome.kind}"
            )
        result = outcome.value.datum
        if result.case == 1:
            fields = dict(result.payload.fields)
            terminal_count = fields[0].value
            terminal_digest = fields[1].value
            break
        if result.case != 0:
            raise AuthorityError("finite-cover stream emitted an unknown marker")
        fields = dict(result.payload.fields)
        representative = _representative_value(fields[0])
        successor = fields[1].value
        body = k1.encode_datum(representative.datum)
        if (
            body in seen_representatives
            or (previous_body is not None and body <= previous_body)
            or successor != state + 1
        ):
            raise AuthorityError(
                "finite-cover stream is duplicate, reordered, or has another successor"
            )
        seen_representatives.add(body)
        previous_body = body
        stream_hash.update(len(body).to_bytes(8, "big"))
        stream_hash.update(body)
        embedded = _portable_success(
            FINITE_COVER_ARITHMETIC.embedding_algorithm,
            (representative,),
            "representative embedding",
        )
        first, second = _datum_pair(embedded)
        if not _finite_cover_member_after_source_admission(
            profile, first, second
        ):
            raise AuthorityError("finite-cover stream yielded a nonmember")
        candidate = _portable_success(
            FINITE_COVER_ARITHMETIC.candidate_algorithm,
            (embedded,),
            "candidate",
        )
        if pow(profile.generator, candidate.datum.value, profile.group_modulus) != first.statement:
            raise AuthorityError("finite-cover stream candidate failed its relation")
        evaluation_body = k1.encode_datum(
            k1.DatumRecord(((0, representative.datum), (1, candidate.datum)))
        )
        evaluation_hash.update(len(evaluation_body).to_bytes(8, "big"))
        evaluation_hash.update(evaluation_body)
        evaluations += 1
        state = successor
    if (
        terminal_count != 308
        or terminal_digest != FINITE_COVER_ARITHMETIC.representative_stream_digest
        or stream_hash.digest() != terminal_digest
        or evaluations != 308
        or state != 308
    ):
        raise AuthorityError("finite-cover terminal receipt disagrees with the exact run")
    return FiniteCoverStreamReceipt(
        finite_cover_validation_basis_id(),
        evaluations,
        stream_hash.digest(),
        evaluation_hash.digest(),
        terminal_count,
        terminal_digest,
        len(seen_states),
        evaluations,
    )


def _certificate_kind_from_context(context: QualificationSubjectContext) -> str:
    payload = context.question_payload
    if type(payload) is not k1.DatumRecord:
        raise AuthorityError("finite-cover certificate payload is malformed")
    fields = dict(payload.fields)
    if (
        tuple(fields) != (0, 1, 2, 3, 4)
        or fields[0] != k1.Symbol("finite-cover-certificate")
        or type(fields[1]) is not k1.Symbol
    ):
        raise AuthorityError("finite-cover certificate payload is incomplete")
    return _require_certificate_kind(fields[1].value)


def _validate_finite_cover_certificate_bindings(
    support: AnalysisSupportInstantiationBodyV0,
) -> tuple[object, ...]:
    bindings = support.non_hypothesis_premise_bindings
    if type(bindings) is not k1.DatumSeq or len(bindings.values) != 3:
        raise AuthorityError("finite-cover support lacks three exact certificates")
    result = []
    for ordinal, (kind, entry) in enumerate(
        zip(FINITE_COVER_CERTIFICATE_KINDS, bindings.values, strict=True)
    ):
        if type(entry) is not k1.DatumRecord:
            raise AuthorityError("finite-cover certificate binding is malformed")
        fields = dict(entry.fields)
        if tuple(fields) != (0, 1) or fields[0] != k1.Nat(ordinal):
            raise AuthorityError("finite-cover certificate binding ordinal changed")
        payload = fields[1]
        if type(payload) is not k1.DatumRecord or tuple(dict(payload.fields)) != (0, 1):
            raise AuthorityError("finite-cover certificate binding payload is incomplete")
        payload_fields = dict(payload.fields)
        expected_goal = finite_cover_certificate_goal_id(
            _SCHNORR_PINNED_SOURCE, _SCHNORR_PINNED_PROFILE, kind
        )
        if payload_fields[0] != _id_datum(expected_goal, "analysis.goal"):
            raise AuthorityError("finite-cover certificate binds another goal")
        judgment_id = _formed_analysis_id(
            payload_fields[1], "analysis.judgment-record"
        )
        judgment = _formed_analysis_body(judgment_id, "analysis.judgment-record")
        context = _derive_qualification_subject_context(
            semantic_profile=ANALYSIS_PROPERTY_PROFILE,
            proposition_id=_formed_analysis_id(
                judgment.proposition_id, "analysis.proposition"
            ),
            semantic_basis_id=_formed_analysis_id(
                judgment.semantic_basis_id, "analysis.semantic-basis"
            ),
            support_id=_formed_analysis_id(
                judgment.support_coordinate, "analysis.support-instantiation"
            ),
            validation_basis_id=_formed_analysis_id(
                judgment.validation_basis_id, "analysis.validation-basis"
            ),
            judgment_record=judgment,
        )
        qualification = analysis_profile_declaration_ref(
            ANALYSIS_PROPERTY_PROFILE,
            ANALYSIS_PROPERTY_PROFILE,
            "analysis.qualification",
            "finite-cover-certificate-result",
        )
        _require_actual_qualification(context, qualification)
        if _certificate_kind_from_context(context) != kind:
            raise AuthorityError("finite-cover certificate kind was substituted")
        result.append(judgment_id)
    return tuple(result)


def _issue_finite_cover_certificate_judgment(kind: str) -> object:
    source = _SCHNORR_PINNED_SOURCE
    profile = _SCHNORR_PINNED_PROFILE
    proposition_id = finite_cover_certificate_proposition_id(source, profile, kind)
    basis_id = finite_cover_certificate_semantic_basis_id(source, profile, kind)
    support_id = _finite_cover_empty_support_id(basis_id, proposition_id)
    qualification = analysis_profile_declaration_ref(
        ANALYSIS_PROPERTY_PROFILE,
        ANALYSIS_PROPERTY_PROFILE,
        "analysis.qualification",
        "finite-cover-certificate-result",
    )
    return _analysis_judgment_record_id(
        profile=ANALYSIS_PROPERTY_PROFILE,
        proposition_id=proposition_id,
        exact_family_conclusion=_finite_cover_certificate_conclusion(
            source, profile, kind
        ),
        inherited_hypothesis_context_id=analysis_hypothesis_context_id(()),
        typed_quantitative_result=k1.DatumVariant(0, k1.UNIT),
        semantic_basis_id=basis_id,
        support_id=support_id,
        validation_basis_id=finite_cover_validation_basis_id(),
        qualification=qualification,
        operation_policy_id=_finite_cover_operation_policy_id(proposition_id),
    )


@_with_family_derivation_scope
def establish_checked_fixed_extractor() -> CheckedFixedExtractorJudgment:
    """Rerun the exact cover and issue one hypothesis-free ordinary judgment."""

    source = _SCHNORR_PINNED_SOURCE
    profile = _SCHNORR_PINNED_PROFILE
    certificate_ids = tuple(
        _issue_finite_cover_certificate_judgment(kind)
        for kind in FINITE_COVER_CERTIFICATE_KINDS
    )
    receipt = _run_finite_cover_stream()
    proposition_id = fixed_extractor_proposition_id(source, profile)
    basis_id = fixed_extractor_semantic_basis_id(source, profile)
    support_id = finite_cover_support_id(source, profile, certificate_ids)
    validation_basis_id = finite_cover_validation_basis_id()
    qualification = analysis_profile_declaration_ref(
        ANALYSIS_PROPERTY_PROFILE,
        ANALYSIS_PROPERTY_PROFILE,
        "analysis.qualification",
        "finite-fixed-extractor-universal-result",
    )
    judgment_id = _analysis_judgment_record_id(
        profile=ANALYSIS_PROPERTY_PROFILE,
        proposition_id=proposition_id,
        exact_family_conclusion=_fixed_extractor_conclusion_body(source, profile),
        inherited_hypothesis_context_id=analysis_hypothesis_context_id(()),
        typed_quantitative_result=k1.DatumVariant(0, k1.UNIT),
        semantic_basis_id=basis_id,
        support_id=support_id,
        validation_basis_id=validation_basis_id,
        qualification=qualification,
        operation_policy_id=_finite_cover_operation_policy_id(proposition_id),
    )
    return CheckedFixedExtractorJudgment(
        proposition_id,
        basis_id,
        support_id,
        validation_basis_id,
        qualification,
        judgment_id,
        certificate_ids,
        receipt,
        _FINITE_COVER_JUDGMENT_ISSUER,
    )


def require_checked_fixed_extractor(
    judgment: CheckedFixedExtractorJudgment,
) -> None:
    if (
        type(judgment) is not CheckedFixedExtractorJudgment
        or judgment._issuer is not _FINITE_COVER_JUDGMENT_ISSUER
    ):
        raise AuthorityError("fixed-extractor judgment lacks Analysis issuance")
    expected = establish_checked_fixed_extractor()
    if judgment != expected:
        raise AuthorityError("fixed-extractor judgment or receipt was substituted")


def schnorr_special_soundness_rule(
    proposition: AnalysisProposition,
) -> ConditionalRule:
    if (
        proposition.goal.question.family
        is not PropertyFamily.K_OUT_OF_N_SPECIAL_SOUNDNESS
    ):
        raise PropertyError("Schnorr source rule needs the selected property family")
    if proposition != _SCHNORR_PINNED_PROPOSITION:
        raise PropertyError(
            "Schnorr source rule is exact to the selected relation-bound proposition"
        )
    proposition_id = analysis_proposition_id(proposition)
    basis_id = schnorr_semantic_basis_id(proposition)
    return ConditionalRule(
        basis_id,
        proposition_id,
        ASSUMED_SCHNORR_TWO_SPECIAL_SOUNDNESS,
        basis_id,
    )


# ---------------------------------------------------------------------------
# Fresh-to-FS theorem applicability and property transport
# ---------------------------------------------------------------------------


_Analysis_EXECUTION_VIEW_MANIFEST = tuple(
    item for item in k2.StaticViewField if item.value.startswith("execution.")
)
_Analysis_FS_CONSTRUCTION_VIEW_MANIFEST = tuple(
    item for item in k2.StaticViewField if item.value.startswith("fs-construction.")
)
_Analysis_PUBLIC_COIN_VIEW_MANIFEST = tuple(
    item for item in k2.StaticViewField if item.value.startswith("public-coin.")
)
_Analysis_TRANSCRIPT_DECLARATION_VIEW_MANIFEST = tuple(
    item
    for item in k2.StaticViewField
    if item.value.startswith("transcript-declaration.")
)


def _k3c_pir_view_consumer_id() -> object:
    return analysis_consumer_intake_id("pir-analysis-source-view")


def _k3c_pir_view_purpose_id(axis: str, view_kind: str) -> object:
    labels = {
        ("fresh", "public-setup-invocation-view"): "fresh-public-setup-view",
        (
            "fiat-shamir",
            "public-setup-invocation-view",
        ): "fiat-shamir-public-setup-view",
        ("fresh", "execution-view"): "fresh-execution-view",
        ("fiat-shamir", "execution-view"): "fiat-shamir-execution-view",
        ("fiat-shamir", "check-fs-construction"): "fiat-shamir-fs-construction-view",
        ("fiat-shamir", "fs-construction-view"): "fiat-shamir-fs-construction-view",
        ("fresh", "public-coin-view"): "core-public-coin-view",
        ("fiat-shamir", "transcript-declaration-view"): "transcript-declaration-view",
        ("relations", "relation-definition-view"): "schnorr-relation-definition-view",
    }
    try:
        label = labels[(axis, view_kind)]
    except KeyError as error:
        raise AuthorityError("unknown PIR Analysis source-view purpose") from error
    return analysis_use_purpose_intake_id(label)


@dataclass(frozen=True)
class _PIRAnalysisSourceViews:
    """Invocation-only PIR bearer set; none of these objects enters an ID."""

    fresh_public_setup: object = field(compare=False, repr=False)
    fiat_shamir_public_setup: object = field(compare=False, repr=False)
    fresh_execution: object = field(compare=False, repr=False)
    fiat_shamir_execution: object = field(compare=False, repr=False)
    fs_construction: object = field(compare=False, repr=False)
    public_coin: object = field(compare=False, repr=False)
    transcript_declaration: object = field(compare=False, repr=False)
    relation_definition: object = field(compare=False, repr=False)


_VALIDATED_PIR_ANALYSIS_VIEW_SETS: dict[
    tuple[int, int], tuple[FreshFsRelationSource, _PIRAnalysisSourceViews]
] = {}


def _affirmative_pir_view(outcome: object, what: str) -> object:
    if (
        type(outcome) is not k2.QualifiedViewOutcome
        or outcome.kind is not k2.QualifiedViewOutcomeKind.AFFIRMATIVE
        or outcome.value is None
    ):
        raise SourceIngressError(f"PIR refused the required {what}")
    return outcome.value


def _issue_pir_analysis_source_views(
    source: FreshFsRelationSource,
) -> _PIRAnalysisSourceViews:
    require_fresh_fs_relation_source(source)
    consumer_id = _k3c_pir_view_consumer_id()

    def purpose(axis: str, view_kind: str) -> object:
        return _k3c_pir_view_purpose_id(axis, view_kind)

    fresh_setup = _affirmative_pir_view(
        k2.issue_public_setup_invocation_view(
            source.case.core,
            None,
            k2.ChallengeInterpretation.FRESH,
            source.case.invocation,
            consumer_id=consumer_id,
            purpose_id=purpose("fresh", "public-setup-invocation-view"),
        ),
        "Fresh public-setup invocation view",
    )
    fs_setup = _affirmative_pir_view(
        k2.issue_public_setup_invocation_view(
            source.case.core,
            source.case.construction,
            k2.ChallengeInterpretation.FIAT_SHAMIR,
            source.case.invocation,
            consumer_id=consumer_id,
            purpose_id=purpose("fiat-shamir", "public-setup-invocation-view"),
        ),
        "Fiat--Shamir public-setup invocation view",
    )
    fresh_execution = _affirmative_pir_view(
        k2.issue_execution_view(
            source.case.core,
            None,
            k2.ChallengeInterpretation.FRESH,
            _Analysis_EXECUTION_VIEW_MANIFEST,
            consumer_id=consumer_id,
            purpose_id=purpose("fresh", "execution-view"),
        ),
        "Fresh execution view",
    )
    fs_execution = _affirmative_pir_view(
        k2.issue_execution_view(
            source.case.core,
            source.case.construction,
            k2.ChallengeInterpretation.FIAT_SHAMIR,
            _Analysis_EXECUTION_VIEW_MANIFEST,
            consumer_id=consumer_id,
            purpose_id=purpose("fiat-shamir", "execution-view"),
        ),
        "Fiat--Shamir execution view",
    )
    checked = _affirmative_pir_view(
        k2.check_fs_construction(
            source.case.core,
            source.case.core,
            source.case.construction,
            consumer_id=consumer_id,
            purpose_id=purpose("fiat-shamir", "check-fs-construction"),
        ),
        "checked FS construction",
    )
    fs_construction = _affirmative_pir_view(
        k2.issue_fs_construction_view(
            checked,
            _Analysis_FS_CONSTRUCTION_VIEW_MANIFEST,
            expected_consumer_id=consumer_id,
            expected_purpose_id=purpose("fiat-shamir", "check-fs-construction"),
            view_consumer_id=consumer_id,
            view_purpose_id=purpose("fiat-shamir", "fs-construction-view"),
        ),
        "FS construction view",
    )
    public_coin = _affirmative_pir_view(
        k2.issue_core_static_view(
            source.case.core,
            k2.StaticViewKind.PUBLIC_COIN,
            _Analysis_PUBLIC_COIN_VIEW_MANIFEST,
            consumer_id=consumer_id,
            purpose_id=purpose("fresh", "public-coin-view"),
        ),
        "Core PublicCoinView",
    )
    transcript_declaration = _affirmative_pir_view(
        k2.issue_construction_static_view(
            source.case.core,
            source.case.construction,
            k2.StaticViewKind.TRANSCRIPT_DECLARATION,
            _Analysis_TRANSCRIPT_DECLARATION_VIEW_MANIFEST,
            consumer_id=consumer_id,
            purpose_id=purpose("fiat-shamir", "transcript-declaration-view"),
        ),
        "TranscriptDeclarationView",
    )
    relation_definition = _affirmative_pir_view(
        k3.issue_relation_definition_view(
            source.case.definition_sources[0],
            k3.schnorr_fixed_setup_manifest(source.case.definition_sources[0]),
            consumer_id=consumer_id,
            purpose_id=purpose("relations", "relation-definition-view"),
        ),
        "Relations definition view",
    )
    views = _PIRAnalysisSourceViews(
        fresh_setup,
        fs_setup,
        fresh_execution,
        fs_execution,
        fs_construction,
        public_coin,
        transcript_declaration,
        relation_definition,
    )
    _require_pir_analysis_source_views(source, views)
    return views


def _projection_entry_map(issued: object) -> dict[object, object]:
    return {item.field: item.value for item in issued.projection.entries}


def _require_pir_analysis_source_views(
    source: FreshFsRelationSource, views: _PIRAnalysisSourceViews
) -> None:
    if type(views) is not _PIRAnalysisSourceViews:
        raise AuthorityError("Analysis PIR source views have the wrong exact shape")
    cache_key = (id(source), id(views))
    cached = _VALIDATED_PIR_ANALYSIS_VIEW_SETS.get(cache_key)
    if cached is not None and cached[0] is source and cached[1] is views:
        return
    require_fresh_fs_relation_source(source)
    consumer_id = _k3c_pir_view_consumer_id()

    def purpose(axis: str, view_kind: str) -> object:
        return _k3c_pir_view_purpose_id(axis, view_kind)

    for issued, axis in (
        (views.fresh_public_setup, "fresh"),
        (views.fiat_shamir_public_setup, "fiat-shamir"),
    ):
        if not k2.validate_issued_public_setup_invocation_view(
            issued,
            expected_consumer_id=consumer_id,
            expected_purpose_id=purpose(axis, "public-setup-invocation-view"),
        ):
            raise AuthorityError(
                f"{axis} public-setup view lacks its exact live PIR authority"
            )
    expected_protocols = (
        source.protocol_source.fresh_protocol_id,
        source.protocol_source.fiat_shamir_protocol_id,
    )
    setup_views = (
        views.fresh_public_setup.view,
        views.fiat_shamir_public_setup.view,
    )
    if (
        tuple(item.protocol_id for item in setup_views) != expected_protocols
        or any(item.core_id != source.protocol_source.core_id for item in setup_views)
        or setup_views[0].entries != setup_views[1].entries
    ):
        raise SourceIngressError(
            "Fresh/FS public-setup views are detached or have unequal entries"
        )
    expected_entries = tuple(
        k2.PublicSetupInvocationEntry(
            k2.PublicSetupBindingRef(item.scope, item.name),
            item.role,
            item.value_sort,
            source.case.invocation.values[item.name],
        )
        for item in source.case.core.inputs
        if item.role in {k2.InputRole.PUBLIC_CONTEXT, k2.InputRole.PUBLIC_PARAMETER}
    )
    if setup_views[0].entries != expected_entries:
        raise SourceIngressError(
            "public-setup view omits, reorders, or substitutes an owner binding"
        )

    for issued, axis, protocol_id, interpretation in (
        (
            views.fresh_execution,
            "fresh",
            source.protocol_source.fresh_protocol_id,
            k2.ChallengeInterpretation.FRESH,
        ),
        (
            views.fiat_shamir_execution,
            "fiat-shamir",
            source.protocol_source.fiat_shamir_protocol_id,
            k2.ChallengeInterpretation.FIAT_SHAMIR,
        ),
    ):
        if not k2.validate_issued_pir_static_view(
            issued,
            expected_consumer_id=consumer_id,
            expected_purpose_id=purpose(axis, "execution-view"),
        ):
            raise AuthorityError(
                f"{axis} execution view lacks its exact live PIR authority"
            )
        coordinate = issued.projection.coordinate
        entries = _projection_entry_map(issued)
        if (
            coordinate.owner_kind is not k2.StaticViewOwnerKind.PROTOCOL
            or coordinate.owner_id != protocol_id
            or coordinate.view_kind is not k2.StaticViewKind.EXECUTION
            or issued.projection.manifest != _Analysis_EXECUTION_VIEW_MANIFEST
            or entries.get(k2.StaticViewField.EX_PROTOCOL_ID) != protocol_id
            or entries.get(k2.StaticViewField.EX_CORE_ID)
            != source.protocol_source.core_id
            or entries.get(k2.StaticViewField.EX_INTERPRETATION) is not interpretation
        ):
            raise SourceIngressError(
                f"{axis} ExecutionView is stale or Protocol-axis mismatched"
            )

    if not k2.validate_issued_pir_static_view(
        views.fs_construction,
        expected_consumer_id=consumer_id,
        expected_purpose_id=purpose("fiat-shamir", "fs-construction-view"),
    ):
        raise AuthorityError("FSConstructionView lacks its exact live PIR authority")
    fs_coordinate = views.fs_construction.projection.coordinate
    fs_entries = _projection_entry_map(views.fs_construction)
    if (
        fs_coordinate.owner_kind is not k2.StaticViewOwnerKind.FS_RESULT
        or fs_coordinate.view_kind is not k2.StaticViewKind.FS_CONSTRUCTION
        or views.fs_construction.projection.manifest
        != _Analysis_FS_CONSTRUCTION_VIEW_MANIFEST
        or fs_entries.get(k2.StaticViewField.FS_SOURCE_PROTOCOL)
        != source.protocol_source.fresh_protocol_id
        or fs_entries.get(k2.StaticViewField.FS_TARGET_PROTOCOL)
        != source.protocol_source.fiat_shamir_protocol_id
        or fs_entries.get(k2.StaticViewField.FS_SHARED_CORE)
        != source.protocol_source.core_id
        or fs_entries.get(k2.StaticViewField.FS_CONSTRUCTION_ID)
        != source.protocol_source.construction_id
    ):
        raise SourceIngressError("FSConstructionView is stale or axis-mismatched")

    for issued, kind, manifest, axis, purpose_kind in (
        (
            views.public_coin,
            k2.StaticViewKind.PUBLIC_COIN,
            _Analysis_PUBLIC_COIN_VIEW_MANIFEST,
            "fresh",
            "public-coin-view",
        ),
        (
            views.transcript_declaration,
            k2.StaticViewKind.TRANSCRIPT_DECLARATION,
            _Analysis_TRANSCRIPT_DECLARATION_VIEW_MANIFEST,
            "fiat-shamir",
            "transcript-declaration-view",
        ),
    ):
        if not k2.validate_issued_pir_static_view(
            issued,
            expected_consumer_id=consumer_id,
            expected_purpose_id=purpose(axis, purpose_kind),
        ):
            raise AuthorityError(f"{kind.value} lacks its exact live PIR authority")
        if (
            issued.projection.coordinate.view_kind is not kind
            or issued.projection.manifest != manifest
        ):
            raise SourceIngressError(f"{kind.value} is stale or manifest-mismatched")
    if (
        views.public_coin.projection.coordinate.owner_id
        != source.protocol_source.core_id
        or views.transcript_declaration.projection.coordinate.owner_id
        != source.protocol_source.construction_id
    ):
        raise SourceIngressError("fixed-setup static views name another owner")

    if not k3.validate_issued_relation_definition_view(
        views.relation_definition,
        expected_consumer_id=consumer_id,
        expected_purpose_id=purpose("relations", "relation-definition-view"),
    ):
        raise AuthorityError(
            "Relations definition view lacks its exact live owner authority"
        )
    expected_definition = source.case.definition_sources[0]
    expected_definition_id = k3.schnorr_relation_definition_id(expected_definition)
    if (
        views.relation_definition.view.coordinate.definition_id
        != expected_definition_id
        or source.case.definitions[0].definition_id != expected_definition_id
        or views.relation_definition.view.manifest
        != k3.schnorr_fixed_setup_manifest(expected_definition)
    ):
        raise SourceIngressError("Relations definition view names another setup")
    _VALIDATED_PIR_ANALYSIS_VIEW_SETS[cache_key] = (source, views)


@dataclass(frozen=True)
class FixedPublicSetup:
    core_id: object
    construction_id: object
    fresh_protocol_id: object
    fiat_shamir_protocol_id: object
    fresh_public_setup_view_id: object
    fiat_shamir_public_setup_view_id: object
    relation_definition_id: object
    _source_views: _PIRAnalysisSourceViews = field(compare=False, repr=False)
    _source: FreshFsRelationSource = field(compare=False, repr=False)

    @property
    def group_generator(self) -> int:
        return _fixed_setup_relation_value(self, k3.RelationDefinitionField.GENERATOR)

    @property
    def subgroup_order(self) -> int:
        return _fixed_setup_relation_value(
            self, k3.RelationDefinitionField.SCALAR_MODULUS
        )

    @property
    def group_modulus(self) -> int:
        return _fixed_setup_relation_value(
            self, k3.RelationDefinitionField.GROUP_MODULUS
        )

    @property
    def session(self) -> bytes:
        return _fixed_setup_public_value(self, "session", bytes)

    @property
    def application_domain(self) -> bytes:
        entries = _projection_entry_map(self._source_views.transcript_declaration)
        value = entries.get(k2.StaticViewField.TD_APPLICATION_DOMAIN)
        if type(value) is not bytes:
            raise TheoremError("TranscriptDeclarationView lacks application domain")
        return value

    @property
    def construction_body(self) -> bytes:
        return k2.construction_body(
            self._source.case.core, self._source.case.construction
        )

    @property
    def challenge_ordinal(self) -> int:
        return _fixed_setup_challenge(self._source)[0]

    @property
    def challenge_name(self) -> str:
        return _fixed_setup_challenge(self._source)[1].name

    @property
    def challenge_condition_refs(self) -> tuple[tuple[str, str], ...]:
        occurrence = _fixed_setup_challenge(self._source)[1]
        return tuple((item.kind.value, item.name) for item in occurrence.dependencies)

    @property
    def challenge_namespace(self) -> bytes:
        return k2.derive_occurrence_namespace(
            self._source.case.core,
            self._source.case.construction,
            self.challenge_ordinal,
            0,
        )

    @property
    def fixed_before_prover_and_oracle(self) -> bool:
        return _fixed_setup_derived_provenance(self)[0]

    @property
    def adversary_selected(self) -> bool:
        return _fixed_setup_derived_provenance(self)[1]

    @property
    def oracle_correlated(self) -> bool:
        return _fixed_setup_derived_provenance(self)[2]

    @property
    def mutable_within_instance(self) -> bool:
        return _fixed_setup_derived_provenance(self)[3]


def _fixed_setup_challenge(source: FreshFsRelationSource) -> tuple[int, object]:
    challenges = tuple(
        (ordinal, occurrence)
        for ordinal, occurrence in enumerate(source.case.core.schedule)
        if occurrence.kind is k2.OccurrenceKind.CHALLENGE
    )
    if len(challenges) != 1:
        raise TheoremError("bounded fixed setup requires one exact challenge")
    return challenges[0]


def _fixed_setup_static_source_manifest(
    source: FreshFsRelationSource,
) -> SourceManifest:
    if len(source.case.definitions) != 1 or len(source.case.relation_interfaces) != 1:
        raise TheoremError("bounded fixed setup requires one exact relation source")
    relation_interface_id = k3.relation_interface_id(source.case.relation_interfaces[0])
    return source_manifest(
        (
            SourceRead(
                SourceFactKind.CORE,
                source.protocol_source.core_id,
                "public-parameter:root:g",
            ),
            SourceRead(
                SourceFactKind.CORE,
                source.protocol_source.core_id,
                "public-parameter:root:q",
            ),
            SourceRead(
                SourceFactKind.CORE,
                source.protocol_source.core_id,
                "public-parameter:root:p",
            ),
            SourceRead(
                SourceFactKind.RELATION_INSTANCE,
                relation_interface_id,
                "knowledge-instance:group-parameter-semantics",
            ),
            SourceRead(
                SourceFactKind.RELATION_BINDING,
                source.fresh_binding.binding_id,
                "fresh-relation-group-parameter-source",
            ),
            SourceRead(
                SourceFactKind.RELATION_BINDING,
                source.fiat_shamir_binding.binding_id,
                "fiat-shamir-relation-group-parameter-source",
            ),
            SourceRead(
                SourceFactKind.CONSTRUCTION,
                source.protocol_source.construction_id,
                "application-domain",
            ),
        )
    )


def _fixed_setup_public_value(
    setup: FixedPublicSetup, input_name: str, expected_type: type
) -> object:
    entries = setup._source_views.fresh_public_setup.view.entries
    selected = tuple(
        item
        for item in entries
        if item.binding_ref.scope == "root"
        and item.binding_ref.input_name == input_name
    )
    if len(selected) != 1 or type(selected[0].value) is not expected_type:
        raise TheoremError(f"fixed setup lacks exact public input {input_name}")
    return selected[0].value


def _fixed_setup_relation_value(
    setup: FixedPublicSetup, field_coordinate: object
) -> int:
    entries = setup._source_views.relation_definition.view.entries
    selected = tuple(
        item for item in entries if item.coordinate.field is field_coordinate
    )
    if len(selected) != 1 or type(selected[0].value) is not int:
        raise TheoremError("Relations definition view lacks one exact setup field")
    return selected[0].value


def _fixed_setup_prefix_map(
    source: FreshFsRelationSource,
) -> tuple[tuple[str, tuple[str, ...]], ...]:
    challenge_ordinal, _ = _fixed_setup_challenge(source)
    prior_entries = tuple(
        k2.RunEntry(
            occurrence.name,
            occurrence.kind,
            k2.EntryStatus.EXECUTED,
            None,
        )
        for occurrence in source.case.core.schedule[:challenge_ordinal]
    )
    return tuple(
        (atom.kind, atom.coordinates)
        for atom in k2.required_influence_atoms(
            source.case.core,
            source.case.construction,
            challenge_ordinal,
            prior_entries,
        )
    )


def _fixed_setup_derived_provenance(
    setup: FixedPublicSetup,
) -> tuple[bool, bool, bool, bool]:
    return _derive_fixed_setup_provenance(
        setup._source,
        setup.challenge_ordinal,
        _fixed_setup_prefix_map(setup._source),
    )


def _k2_static_view_field_coordinate(
    issued: object, field_coordinate: object
) -> object:
    if (
        type(field_coordinate) is not k2.StaticViewField
        or field_coordinate not in issued.projection.manifest
    ):
        raise TheoremError("PIR static field is outside the issued manifest")
    coordinate = issued.projection.coordinate
    return k1.DatumRecord(
        (
            (0, k1.Symbol(coordinate.owner_kind.value)),
            (1, _id_datum(coordinate.owner_id)),
            (2, k1.Symbol(coordinate.view_kind.value)),
            (
                3,
                _id_datum(
                    coordinate.semantic_profile_id,
                    "foundation.semantic-language-profile",
                ),
            ),
            (4, k1.Symbol(field_coordinate.value)),
        )
    )


def _pir_static_atomic_coordinate_body(
    coordinate: k2.PIRStaticViewAtomicCoordinate,
) -> object:
    if type(coordinate) is not k2.PIRStaticViewAtomicCoordinate:
        raise TheoremError("PIR static atomic coordinate has the wrong exact shape")
    return k1.DatumRecord(
        (
            (
                0,
                k1.DatumRecord(
                    (
                        (0, k1.Symbol(coordinate.view_coordinate.owner_kind.value)),
                        (1, _id_datum(coordinate.view_coordinate.owner_id)),
                        (2, k1.Symbol(coordinate.view_coordinate.view_kind.value)),
                        (
                            3,
                            _id_datum(
                                coordinate.view_coordinate.semantic_profile_id,
                                "foundation.semantic-language-profile",
                            ),
                        ),
                    )
                ),
            ),
            (1, k1.Symbol(coordinate.field.value)),
            (2, k1.Nat(coordinate.sequence_ordinal)),
            (3, k1.Nat(coordinate.schedule_ordinal)),
            (4, k1.Symbol(coordinate.occurrence_name)),
            (5, k1.Symbol(coordinate.leaf.value)),
        )
    )


def _fixed_setup_challenge_projection(
    setup: FixedPublicSetup,
) -> k2.PublicCoinChallengeProjection:
    if type(setup) is not FixedPublicSetup:
        raise TheoremError("fixed setup challenge source has the wrong exact shape")
    _require_pir_analysis_source_views(setup._source, setup._source_views)
    expected_ordinal, expected_occurrence = _fixed_setup_challenge(setup._source)
    projection = k2.resolve_public_coin_challenge_projection(
        setup._source_views.public_coin,
        0,
        expected_consumer_id=_k3c_pir_view_consumer_id(),
        expected_purpose_id=_k3c_pir_view_purpose_id("fresh", "public-coin-view"),
    )
    coordinate = projection.challenge_coordinate
    if (
        coordinate.sequence_ordinal != 0
        or coordinate.schedule_ordinal != expected_ordinal
        or coordinate.occurrence_name != expected_occurrence.name
        or projection.domain_coordinate.view_coordinate != coordinate.view_coordinate
        or projection.domain_coordinate.sequence_ordinal != coordinate.sequence_ordinal
        or projection.domain_coordinate.schedule_ordinal != coordinate.schedule_ordinal
        or projection.domain_coordinate.occurrence_name != coordinate.occurrence_name
        or projection.challenge_domain != expected_occurrence.challenge_domain
    ):
        raise TheoremError("fixed setup challenge leaves select another Core entry")
    return projection


def _relation_definition_field_coordinate_body(coordinate: object) -> object:
    if (
        type(coordinate) is not k3.RelationDefinitionFieldCoordinate
        or type(coordinate.view_coordinate) is not k3.RelationDefinitionViewCoordinate
        or type(coordinate.field) is not k3.RelationDefinitionField
    ):
        raise TheoremError("Relations setup field coordinate is malformed")
    return k1.DatumRecord(
        (
            (
                0,
                _id_datum(
                    coordinate.view_coordinate.definition_id,
                    "relations.definition",
                ),
            ),
            (
                1,
                _id_datum(
                    coordinate.view_coordinate.semantic_profile_id,
                    "foundation.semantic-language-profile",
                ),
            ),
            (2, k1.Symbol(coordinate.field.value)),
        )
    )


def _fixed_setup_challenge_ref(setup: FixedPublicSetup) -> object:
    return _pir_static_atomic_coordinate_body(
        _fixed_setup_challenge_projection(setup).challenge_coordinate
    )


def _property_law_ref(label: str) -> object:
    return analysis_profile_declaration_ref_body(
        analysis_profile_declaration_ref(
            ANALYSIS_PROPERTY_PROFILE,
            ANALYSIS_PROPERTY_PROFILE,
            "analysis.semantic-law",
            label,
        )
    )


def fixed_public_setup_id(setup: FixedPublicSetup) -> object:
    if type(setup) is not FixedPublicSetup:
        raise TheoremError("AFK fixed public setup has the wrong exact shape")
    _require_pir_analysis_source_views(setup._source, setup._source_views)
    require_fresh_fs_relation_source(setup._source)
    fresh_setup = setup._source_views.fresh_public_setup
    fs_setup = setup._source_views.fiat_shamir_public_setup
    if (
        setup.core_id != setup._source.protocol_source.core_id
        or setup.construction_id != setup._source.protocol_source.construction_id
        or setup.fresh_protocol_id != setup._source.protocol_source.fresh_protocol_id
        or setup.fiat_shamir_protocol_id
        != setup._source.protocol_source.fiat_shamir_protocol_id
        or setup.fresh_public_setup_view_id != fresh_setup.view_id
        or setup.fiat_shamir_public_setup_view_id != fs_setup.view_id
        or setup.relation_definition_id
        != k3.schnorr_relation_definition_id(setup._source.case.definition_sources[0])
        or setup.group_generator != _fixed_setup_public_value(setup, "g", int)
        or setup.subgroup_order != _fixed_setup_public_value(setup, "q", int)
        or setup.group_modulus != _fixed_setup_public_value(setup, "p", int)
        or setup.group_generator <= 1
        or setup.subgroup_order <= 1
        or setup.group_modulus <= 2
        or type(setup.session) is not bytes
        or setup.application_domain
        != setup._source.case.construction.application_domain
        or not setup.fixed_before_prover_and_oracle
        or setup.adversary_selected
        or setup.oracle_correlated
        or setup.mutable_within_instance
    ):
        raise TheoremError("AFK fixed public setup is detached, mutable, or correlated")
    views = setup._source_views
    relation_coordinates = views.relation_definition.view.manifest
    fixed_static_sources = k1.DatumRecord(
        (
            (
                0,
                k1.DatumSeq(
                    tuple(
                        _relation_definition_field_coordinate_body(item)
                        for item in relation_coordinates
                    )
                ),
            ),
            (
                1,
                _k2_static_view_field_coordinate(
                    views.transcript_declaration,
                    k2.StaticViewField.TD_APPLICATION_DOMAIN,
                ),
            ),
        )
    )
    exact_static_sources = k1.DatumRecord(
        (
            (0, _id_datum(setup.core_id, "pir.interactive-core")),
            (1, _id_datum(setup.construction_id, "pir.transcript-construction")),
            (2, _fixed_setup_challenge_ref(setup)),
            (3, fixed_static_sources),
        )
    )
    exact_public_invocation_sources = k1.DatumRecord(
        (
            (
                0,
                _id_datum(
                    setup.fresh_public_setup_view_id,
                    "pir.public-setup-invocation-view",
                ),
            ),
            (
                1,
                _id_datum(
                    setup.fiat_shamir_public_setup_view_id,
                    "pir.public-setup-invocation-view",
                ),
            ),
        )
    )
    derived_projection = k1.DatumRecord(
        (
            (0, _property_law_ref("afk-fixed-public-setup-projection-v0")),
            (
                1,
                k1.DatumSeq((k1.Nat(0), k1.Nat(1), k1.Nat(2), k1.Nat(3))),
            ),
        )
    )
    return _analysis_id(
        "analysis.fixed-public-setup",
        AnalysisFixedPublicSetupBodyV0(
            exact_static_sources,
            exact_public_invocation_sources,
            derived_projection,
            _property_law_ref("pre-prover-and-oracle-fixed-selection-v0"),
            k1.DatumRecord(
                (
                    (0, _property_law_ref("coordinate-public-visibility-v0")),
                    (
                        1,
                        k1.DatumSeq(
                            tuple(
                                k1.Nat(index)
                                for index in range(len(relation_coordinates) + 2)
                            )
                        ),
                    ),
                )
            ),
        ),
    )


@dataclass(frozen=True)
class QueryEncodingEntry:
    statement: int
    commitment: int
    k2_challenge_query_carrier: bytes


@dataclass(frozen=True)
class _IssuedQueryEncodingTable:
    setup_id: object
    source_projection_id: object
    entries: tuple[QueryEncodingEntry, ...]
    _issuer: object


class _QueryCarrierStrategy:
    def __init__(self, commitment: int) -> None:
        self.commitment = commitment

    def move(self, occurrence: object, view: object) -> int:
        del view
        if occurrence.name == "commitment":
            return self.commitment
        if occurrence.name == "response":
            return 0
        raise k2.StrategyStopped("query-carrier strategy has no other move")


_QUERY_TABLE_ISSUER = object()
_QUERY_ENCODING_CACHE: dict[tuple[bytes, bytes], _IssuedQueryEncodingTable] = {}


def _canonical_setup_group_elements(setup: FixedPublicSetup) -> tuple[int, ...]:
    return tuple(
        value
        for value in range(1, setup.group_modulus)
        if pow(value, setup.subgroup_order, setup.group_modulus) == 1
    )


def _admit_query_encoding_table(
    setup: FixedPublicSetup, entries: tuple[QueryEncodingEntry, ...]
) -> None:
    fixed_public_setup_id(setup)
    group_elements = _canonical_setup_group_elements(setup)
    if len(group_elements) != setup.subgroup_order:
        raise TheoremError("fixed setup does not expose the exact q-element subgroup")
    expected_pairs = tuple(
        (statement, commitment)
        for statement in group_elements
        for commitment in group_elements
    )
    actual_pairs = tuple((item.statement, item.commitment) for item in entries)
    if actual_pairs != expected_pairs:
        raise TheoremError(
            "bounded query table must cover the canonical subgroup Cartesian domain in order"
        )
    carriers = tuple(item.k2_challenge_query_carrier for item in entries)
    if any(type(item) is not bytes or not item for item in carriers):
        raise TheoremError("bounded query table has a malformed PIR carrier")
    for carrier in carriers:
        if len(carrier) > k1.MAX_CANONICAL_BYTES:
            raise TheoremError(
                "raw PIR query-index encoding exceeds the Foundation byte bound"
            )
        try:
            if k1.encode_datum(k1.decode_datum(carrier)) != carrier:
                raise TheoremError(
                    "PIR query index is not one canonical datum encoding"
                )
        except k1.CanonicalError as error:
            raise TheoremError(
                "PIR query index is not one canonical datum encoding"
            ) from error
    if len(carriers) != len(set(carriers)):
        raise TheoremError(
            "bounded PIR query carrier is not injective on the selected valid domain"
        )


def _query_encoding_table(
    source: FreshFsRelationSource, setup: FixedPublicSetup
) -> tuple[QueryEncodingEntry, ...]:
    setup_id = fixed_public_setup_id(setup)
    source_projection_id = native_subject_projection_id(source)
    key = (
        setup_id.internal_reference(),
        source_projection_id.internal_reference(),
    )
    cached = _QUERY_ENCODING_CACHE.get(key)
    if cached is not None:
        if (
            type(cached) is _IssuedQueryEncodingTable
            and cached._issuer is _QUERY_TABLE_ISSUER
            and cached.setup_id == setup_id
            and cached.source_projection_id == source_projection_id
        ):
            _admit_query_encoding_table(setup, cached.entries)
            return cached.entries
        _QUERY_ENCODING_CACHE.pop(key, None)
    group_elements = _canonical_setup_group_elements(setup)
    entries: list[QueryEncodingEntry] = []
    for statement in group_elements:
        for commitment in group_elements:
            values = dict(source.case.invocation.values)
            values["statement"] = statement
            values["session"] = setup.session
            result = k2.generate(
                source.case.core,
                source.case.construction,
                k2.ChallengeInterpretation.FIAT_SHAMIR,
                k2.Invocation(values),
                _QueryCarrierStrategy(commitment),
            )
            if type(result) is not k2.Completed:
                raise TheoremError("PIR could not generate one bounded query carrier")
            challenge_entry = result.record.entries[setup.challenge_ordinal]
            if (
                challenge_entry.prefix_state is None
                or len(challenge_entry.draw_namespaces) != 1
                or challenge_entry.draw_namespaces[0] != setup.challenge_namespace
            ):
                raise TheoremError(
                    "PIR challenge carrier lacks exact prefix or namespace"
                )
            carrier = k1.encode_datum(
                k1.DatumRecord(
                    (
                        (0, k1.BytesValue(challenge_entry.prefix_state)),
                        (1, k1.BytesValue(challenge_entry.draw_namespaces[0])),
                        (2, k1.Nat(source.case.construction.sample_bytes)),
                        (
                            3,
                            k1.Nat(
                                source.case.core.schedule[
                                    setup.challenge_ordinal
                                ].challenge_domain.modulus
                            ),
                        ),
                    )
                )
            )
            entries.append(QueryEncodingEntry(statement, commitment, carrier))
    result = tuple(entries)
    _admit_query_encoding_table(setup, result)
    _QUERY_ENCODING_CACHE[key] = _IssuedQueryEncodingTable(
        setup_id, source_projection_id, result, _QUERY_TABLE_ISSUER
    )
    return result


def query_encoding_id(
    setup: FixedPublicSetup, entries: tuple[QueryEncodingEntry, ...]
) -> object:
    setup_id = fixed_public_setup_id(setup)
    _admit_query_encoding_table(setup, entries)
    return _legacy_component_id(
        "analysis.query-encoding",
        k1.DatumRecord(
            (
                (
                    0,
                    _id_datum(setup_id, "analysis.fixed-public-setup"),
                ),
                (
                    1,
                    k1.DatumSeq(
                        tuple(
                            k1.DatumRecord(
                                (
                                    (0, k1.Nat(item.statement)),
                                    (1, k1.Nat(item.commitment)),
                                    (
                                        2,
                                        k1.BytesValue(item.k2_challenge_query_carrier),
                                    ),
                                )
                            )
                            for item in entries
                        )
                    ),
                ),
            )
        ),
    )


@dataclass(frozen=True)
class FSCorrespondence:
    core_id: object
    construction_id: object
    fresh_protocol_id: object
    fiat_shamir_protocol_id: object
    fresh_binding_id: object
    fiat_shamir_binding_id: object
    fresh_plan_binding_id: object
    fiat_shamir_plan_binding_id: object
    occurrence_map: tuple[tuple[str, str, str], ...]
    statement_map: tuple[tuple[str, str, str], ...]
    claim_map: tuple[tuple[str, str, str], ...]
    witness_map: tuple[tuple[str, str], ...]
    source_property_profile_id: object
    application_domain: bytes
    construction_body: bytes
    construction_version: str
    challenge_namespace_map: tuple[tuple[str, int, bytes], ...]
    transcript_prefix_map: tuple[tuple[str, tuple[str, ...]], ...]
    statement_extension_map: tuple[str, ...]
    fixed_public_setup: FixedPublicSetup
    fixed_public_setup_id: object
    fresh_public_setup_view_id: object
    fiat_shamir_public_setup_view_id: object
    fresh_execution_view_binding_id: object
    fiat_shamir_execution_view_binding_id: object
    fs_construction_view_binding_id: object
    query_encoding_table: tuple[QueryEncodingEntry, ...]
    query_encoding_id: object
    sampler_map: tuple[tuple[str, int, int, int, bool], ...]
    query_index_map: tuple[str, str]
    extractor_algorithm_id: object
    auxiliary_distribution_map: tuple[str, ...]
    forking_semantics: str
    source_model_id: object
    target_model_id: object
    _pir_source_views: _PIRAnalysisSourceViews = field(compare=False, repr=False)


def _derive_fixed_setup_provenance(
    source: FreshFsRelationSource,
    challenge_ordinal: int,
    transcript_prefix_map: tuple[tuple[str, tuple[str, ...]], ...],
) -> tuple[bool, bool, bool, bool]:
    """Derive the selected setup timing flags from immutable PIR source data."""

    values = dict(source.case.invocation.values)
    required_values = {
        "g": int,
        "q": int,
        "p": int,
        "session": bytes,
    }
    values_are_fixed = all(
        name in values and type(values[name]) is expected
        for name, expected in required_values.items()
    )
    required_atoms = {
        ("public-parameter", ("root", "g")),
        ("public-parameter", ("root", "q")),
        ("public-parameter", ("root", "p")),
        ("public-context", ("root", "session")),
    }
    actual_atoms = set(transcript_prefix_map)
    prefix_binds_setup = required_atoms <= actual_atoms
    immutable_inputs = (
        type(source.case.invocation.values) is MappingProxyType
        and type(source.case.core.inputs) is tuple
        and type(source.case.core.scopes) is tuple
        and type(source.case.core.schedule) is tuple
        and type(source.case.core.extensions) is tuple
        and type(source.case.core.reductions) is tuple
        and type(source.case.core.claim_uses) is tuple
        and type(source.case.construction.application_domain) is bytes
        and type(source.case.construction.version) is str
    )
    exact_challenge_position = (
        type(challenge_ordinal) is int
        and challenge_ordinal in range(len(source.case.core.schedule))
        and source.case.core.schedule[challenge_ordinal].kind
        is k2.OccurrenceKind.CHALLENGE
    )
    setup_names = set(required_values)
    adversary_selected = any(
        kind == "prover-message" and any(name in setup_names for name in coordinates)
        for kind, coordinates in transcript_prefix_map
    )
    oracle_correlated = any(
        kind in {"oracle-answer", "fresh-challenge"}
        and any(name in setup_names for name in coordinates)
        for kind, coordinates in transcript_prefix_map
    )
    mutable_within_instance = not immutable_inputs
    fixed_before_prover_and_oracle = (
        values_are_fixed
        and prefix_binds_setup
        and immutable_inputs
        and exact_challenge_position
        and not adversary_selected
        and not oracle_correlated
    )
    return (
        fixed_before_prover_and_oracle,
        adversary_selected,
        oracle_correlated,
        mutable_within_instance,
    )


def derive_fs_correspondence(
    source: FreshFsRelationSource,
    source_model: ExperimentModel,
    target_model: ExperimentModel,
) -> FSCorrespondence:
    require_fresh_fs_relation_source(source)
    admit_experiment_model(source_model)
    admit_experiment_model(target_model)
    pir_source_views = _issue_pir_analysis_source_views(source)
    profile = derive_schnorr_special_soundness_profile(source)
    occurrence_map = tuple(
        (item.name, item.name, item.kind.value) for item in source.case.core.schedule
    )
    fresh_public = source.fresh_binding.binding.public_edges
    fs_public = source.fiat_shamir_binding.binding.public_edges
    fresh_claims = source.fresh_binding.binding.claim_edges
    fs_claims = source.fiat_shamir_binding.binding.claim_edges
    if fresh_public != fs_public or fresh_claims != fs_claims:
        raise TheoremError("Fresh/FS statement or claim correspondence is incomplete")
    statement_map = tuple(
        (edge.instance, edge.slot, edge.source.input_name)
        for edge in fresh_public
        if type(edge.source) is k3.BindingRef
    )
    claim_map = tuple(
        (edge.instance, edge.claim.origin.value, edge.claim.claim)
        for edge in fresh_claims
    )
    fresh_witnesses = source.fresh_plan_binding.binding.witness_edges
    fs_witnesses = source.fiat_shamir_plan_binding.binding.witness_edges
    if fresh_witnesses != fs_witnesses:
        raise TheoremError("Fresh/FS witness correspondence is incomplete")
    witness_map = tuple(
        (edge.slot, edge.witness_surface_key) for edge in fresh_witnesses
    )
    challenge_namespace_map = tuple(
        (
            occurrence.name,
            draw_ordinal,
            k2.derive_occurrence_namespace(
                source.case.core,
                source.case.construction,
                occurrence_ordinal,
                draw_ordinal,
            ),
        )
        for occurrence_ordinal, occurrence in enumerate(source.case.core.schedule)
        if occurrence.kind is k2.OccurrenceKind.CHALLENGE
        for draw_ordinal in range(source.case.construction.max_attempts)
    )
    challenge_ordinal = next(
        index
        for index, occurrence in enumerate(source.case.core.schedule)
        if occurrence.kind is k2.OccurrenceKind.CHALLENGE
    )
    prior_entries = tuple(
        k2.RunEntry(
            occurrence.name,
            occurrence.kind,
            k2.EntryStatus.EXECUTED,
            None,
        )
        for occurrence in source.case.core.schedule[:challenge_ordinal]
    )
    transcript_prefix_map = tuple(
        (atom.kind, atom.coordinates)
        for atom in k2.required_influence_atoms(
            source.case.core,
            source.case.construction,
            challenge_ordinal,
            prior_entries,
        )
    )
    sampler_map = tuple(
        (
            occurrence.name,
            occurrence.challenge_domain.modulus,
            source.case.construction.sample_bytes,
            source.case.construction.max_attempts,
            (
                source.case.construction.max_attempts == 1
                and (1 << (8 * source.case.construction.sample_bytes))
                % occurrence.challenge_domain.modulus
                == 0
            ),
        )
        for occurrence in source.case.core.schedule
        if occurrence.kind is k2.OccurrenceKind.CHALLENGE
        and occurrence.challenge_domain is not None
    )
    values = source.case.invocation.values
    session = values.get("session")
    if type(session) is not bytes:
        raise TheoremError("bounded AFK setup requires one exact byte session")
    setup = FixedPublicSetup(
        source.protocol_source.core_id,
        source.protocol_source.construction_id,
        source.protocol_source.fresh_protocol_id,
        source.protocol_source.fiat_shamir_protocol_id,
        pir_source_views.fresh_public_setup.view_id,
        pir_source_views.fiat_shamir_public_setup.view_id,
        k3.schnorr_relation_definition_id(source.case.definition_sources[0]),
        pir_source_views,
        source,
    )
    setup_id = fixed_public_setup_id(setup)
    encoding_table = _query_encoding_table(source, setup)
    encoding_id = query_encoding_id(setup, encoding_table)
    return FSCorrespondence(
        core_id=source.protocol_source.core_id,
        construction_id=source.protocol_source.construction_id,
        fresh_protocol_id=source.protocol_source.fresh_protocol_id,
        fiat_shamir_protocol_id=source.protocol_source.fiat_shamir_protocol_id,
        fresh_binding_id=source.fresh_binding.binding_id,
        fiat_shamir_binding_id=source.fiat_shamir_binding.binding_id,
        fresh_plan_binding_id=source.fresh_plan_binding.binding_id,
        fiat_shamir_plan_binding_id=source.fiat_shamir_plan_binding.binding_id,
        occurrence_map=occurrence_map,
        statement_map=statement_map,
        claim_map=claim_map,
        witness_map=witness_map,
        source_property_profile_id=profile.profile_id,
        application_domain=source.case.construction.application_domain,
        construction_body=k2.construction_body(
            source.case.core, source.case.construction
        ),
        construction_version=source.case.construction.version,
        challenge_namespace_map=challenge_namespace_map,
        transcript_prefix_map=transcript_prefix_map,
        statement_extension_map=tuple(
            coordinates[-1]
            for kind, coordinates in transcript_prefix_map
            if kind in {"public-parameter", "statement", "public-context"}
        ),
        fixed_public_setup=setup,
        fixed_public_setup_id=setup_id,
        fresh_public_setup_view_id=pir_source_views.fresh_public_setup.view_id,
        fiat_shamir_public_setup_view_id=pir_source_views.fiat_shamir_public_setup.view_id,
        fresh_execution_view_binding_id=(
            pir_source_views.fresh_execution.source_binding.owner_binding_payload
        ),
        fiat_shamir_execution_view_binding_id=(
            pir_source_views.fiat_shamir_execution.source_binding.owner_binding_payload
        ),
        fs_construction_view_binding_id=(
            pir_source_views.fs_construction.source_binding.owner_binding_payload
        ),
        query_encoding_table=encoding_table,
        query_encoding_id=encoding_id,
        sampler_map=sampler_map,
        query_index_map=("statement", "commitment"),
        extractor_algorithm_id=SCHNORR_EXTRACTOR_ALGORITHM,
        auxiliary_distribution_map=("x", "pi", "aux", "v", "w"),
        forking_semantics="afk-lazy-sampling-reprogramming-not-k2-replay",
        source_model_id=experiment_model_id(source_model),
        target_model_id=experiment_model_id(target_model),
        _pir_source_views=pir_source_views,
    )


def fs_correspondence_id(correspondence: FSCorrespondence) -> object:
    if type(correspondence) is not FSCorrespondence:
        raise TheoremError("FS correspondence has the wrong exact shape")
    for identifier, expected in (
        (correspondence.core_id, "pir.interactive-core"),
        (correspondence.construction_id, "pir.transcript-construction"),
        (correspondence.fresh_protocol_id, "pir.protocol"),
        (correspondence.fiat_shamir_protocol_id, "pir.protocol"),
        (correspondence.fresh_binding_id, "relations.protocol-binding"),
        (correspondence.fiat_shamir_binding_id, "relations.protocol-binding"),
        (correspondence.fresh_plan_binding_id, "relations.plan-witness-binding"),
        (
            correspondence.fiat_shamir_plan_binding_id,
            "relations.plan-witness-binding",
        ),
        (correspondence.source_model_id, "analysis.experiment-profile"),
        (correspondence.target_model_id, "analysis.experiment-profile"),
        (
            correspondence.source_property_profile_id,
            "analysis.experiment-profile",
        ),
        (
            correspondence.fresh_public_setup_view_id,
            "pir.public-setup-invocation-view",
        ),
        (
            correspondence.fiat_shamir_public_setup_view_id,
            "pir.public-setup-invocation-view",
        ),
        (
            correspondence.fresh_execution_view_binding_id,
            "pir.source-binding-payload",
        ),
        (
            correspondence.fiat_shamir_execution_view_binding_id,
            "pir.source-binding-payload",
        ),
        (
            correspondence.fs_construction_view_binding_id,
            "pir.source-binding-payload",
        ),
    ):
        _id_datum(identifier, expected)
    for mapping in (
        correspondence.occurrence_map,
        correspondence.statement_map,
        correspondence.claim_map,
        correspondence.witness_map,
    ):
        for entry in mapping:
            for coordinate in entry:
                _ascii(coordinate, "FS correspondence coordinate")
    for name, modulus, width, attempts, total_uniform in correspondence.sampler_map:
        _ascii(name, "FS sampler coordinate")
        if (
            type(modulus) is not int
            or modulus <= 1
            or type(width) is not int
            or width <= 0
            or type(attempts) is not int
            or attempts <= 0
            or type(total_uniform) is not bool
        ):
            raise TheoremError("FS sampler correspondence is malformed")
    if (
        type(correspondence.application_domain) is not bytes
        or not correspondence.application_domain
    ):
        raise TheoremError("FS correspondence lacks an exact application domain")
    if (
        type(correspondence.construction_body) is not bytes
        or not correspondence.construction_body
    ):
        raise TheoremError("FS correspondence lacks the imported PIR construction body")
    _ascii(correspondence.construction_version, "construction version")
    for name, ordinal, namespace in correspondence.challenge_namespace_map:
        _ascii(name, "challenge namespace coordinate")
        if (
            type(ordinal) is not int
            or ordinal < 0
            or type(namespace) is not bytes
            or not namespace
        ):
            raise TheoremError("challenge namespace map is malformed")
    if not correspondence.transcript_prefix_map:
        raise TheoremError("AFK correspondence lacks the exact PIR prefix map")
    for kind, coordinates in correspondence.transcript_prefix_map:
        _ascii(kind, "transcript influence kind")
        for coordinate in coordinates:
            _ascii(coordinate, "transcript influence coordinate")
    if tuple(kind for kind, _ in correspondence.transcript_prefix_map) != (
        "core-header",
        "construction-header",
        "application-domain",
        "scope-open",
        "public-parameter",
        "public-parameter",
        "public-parameter",
        "statement",
        "public-context",
        "prover-message",
        "challenge-condition",
    ) or correspondence.transcript_prefix_map[3:] != (
        ("scope-open", ("root",)),
        ("public-parameter", ("root", "g")),
        ("public-parameter", ("root", "q")),
        ("public-parameter", ("root", "p")),
        ("statement", ("root", "statement")),
        ("public-context", ("root", "session")),
        ("prover-message", ("commitment",)),
        ("challenge-condition", ("challenge", "input", "statement")),
    ):
        raise TheoremError("AFK correspondence has a substituted PIR prefix atom map")
    if correspondence.statement_extension_map != (
        "g",
        "q",
        "p",
        "statement",
        "session",
    ):
        raise TheoremError("AFK logical Statement extension map is incomplete")
    expected_setup_id = fixed_public_setup_id(correspondence.fixed_public_setup)
    setup_source = correspondence.fixed_public_setup._source
    source_views = correspondence._pir_source_views
    _require_pir_analysis_source_views(setup_source, source_views)
    if (
        correspondence.fixed_public_setup._source_views is not source_views
        or correspondence.fixed_public_setup_id != expected_setup_id
        or correspondence.fixed_public_setup.core_id != correspondence.core_id
        or correspondence.fixed_public_setup.construction_id
        != correspondence.construction_id
        or correspondence.fixed_public_setup.application_domain
        != correspondence.application_domain
        or correspondence.fixed_public_setup.construction_body
        != correspondence.construction_body
        or correspondence.fresh_protocol_id
        != setup_source.protocol_source.fresh_protocol_id
        or correspondence.fiat_shamir_protocol_id
        != setup_source.protocol_source.fiat_shamir_protocol_id
        or correspondence.fresh_binding_id != setup_source.fresh_binding.binding_id
        or correspondence.fiat_shamir_binding_id
        != setup_source.fiat_shamir_binding.binding_id
        or correspondence.fresh_plan_binding_id
        != setup_source.fresh_plan_binding.binding_id
        or correspondence.fiat_shamir_plan_binding_id
        != setup_source.fiat_shamir_plan_binding.binding_id
        or correspondence.fresh_public_setup_view_id
        != source_views.fresh_public_setup.view_id
        or correspondence.fiat_shamir_public_setup_view_id
        != source_views.fiat_shamir_public_setup.view_id
        or correspondence.fresh_execution_view_binding_id
        != source_views.fresh_execution.source_binding.owner_binding_payload
        or correspondence.fiat_shamir_execution_view_binding_id
        != source_views.fiat_shamir_execution.source_binding.owner_binding_payload
        or correspondence.fs_construction_view_binding_id
        != source_views.fs_construction.source_binding.owner_binding_payload
    ):
        raise TheoremError("AFK fixed setup was substituted or detached")
    expected_encoding_id = query_encoding_id(
        correspondence.fixed_public_setup,
        correspondence.query_encoding_table,
    )
    if correspondence.query_encoding_id != expected_encoding_id:
        raise TheoremError("bounded PIR query encoding identity was substituted")
    if correspondence.query_index_map != ("statement", "commitment"):
        raise TheoremError("AFK query index must be exactly (statement, commitment)")
    _id_datum(
        correspondence.extractor_algorithm_id,
        "foundation.portable-algorithm",
    )
    if correspondence.auxiliary_distribution_map != ("x", "pi", "aux", "v", "w"):
        raise TheoremError("AFK auxiliary-output map is incomplete")
    if (
        correspondence.forking_semantics
        != "afk-lazy-sampling-reprogramming-not-k2-replay"
    ):
        raise TheoremError("AFK forking semantics was conflated with execution replay")
    return _legacy_component_id(
        "analysis.fs-correspondence",
        k1.DatumRecord(
            (
                (0, _id_datum(correspondence.core_id, "pir.interactive-core")),
                (
                    1,
                    _id_datum(
                        correspondence.construction_id, "pir.transcript-construction"
                    ),
                ),
                (2, _id_datum(correspondence.fresh_protocol_id, "pir.protocol")),
                (3, _id_datum(correspondence.fiat_shamir_protocol_id, "pir.protocol")),
                (
                    4,
                    _id_datum(
                        correspondence.fresh_binding_id, "relations.protocol-binding"
                    ),
                ),
                (
                    5,
                    _id_datum(
                        correspondence.fiat_shamir_binding_id,
                        "relations.protocol-binding",
                    ),
                ),
                (
                    6,
                    k1.DatumSeq(
                        tuple(
                            k1.DatumSeq(tuple(k1.Symbol(x) for x in entry))
                            for entry in correspondence.occurrence_map
                        )
                    ),
                ),
                (
                    7,
                    k1.DatumSeq(
                        tuple(
                            k1.DatumSeq(tuple(k1.Symbol(x) for x in entry))
                            for entry in correspondence.statement_map
                        )
                    ),
                ),
                (
                    8,
                    k1.DatumSeq(
                        tuple(
                            k1.DatumSeq(tuple(k1.Symbol(x) for x in entry))
                            for entry in correspondence.claim_map
                        )
                    ),
                ),
                (
                    9,
                    k1.DatumSeq(
                        tuple(
                            k1.DatumSeq(tuple(k1.Symbol(x) for x in entry))
                            for entry in correspondence.witness_map
                        )
                    ),
                ),
                (
                    10,
                    _id_datum(
                        correspondence.source_property_profile_id,
                        "analysis.experiment-profile",
                    ),
                ),
                (
                    11,
                    k1.DatumRecord(
                        (
                            (0, k1.BytesValue(correspondence.application_domain)),
                            (1, k1.BytesValue(correspondence.construction_body)),
                            (2, k1.Symbol(correspondence.construction_version)),
                            (
                                3,
                                k1.DatumSeq(
                                    tuple(
                                        k1.DatumRecord(
                                            (
                                                (0, k1.Symbol(name)),
                                                (1, k1.Nat(ordinal)),
                                                (2, k1.BytesValue(namespace)),
                                            )
                                        )
                                        for name, ordinal, namespace in correspondence.challenge_namespace_map
                                    )
                                ),
                            ),
                            (
                                4,
                                k1.DatumSeq(
                                    tuple(
                                        k1.DatumRecord(
                                            (
                                                (0, k1.Symbol(kind)),
                                                (
                                                    1,
                                                    k1.DatumSeq(
                                                        tuple(
                                                            k1.Symbol(item)
                                                            for item in coordinates
                                                        )
                                                    ),
                                                ),
                                            )
                                        )
                                        for kind, coordinates in correspondence.transcript_prefix_map
                                    )
                                ),
                            ),
                            (
                                5,
                                k1.DatumSeq(
                                    tuple(
                                        k1.Symbol(item)
                                        for item in correspondence.statement_extension_map
                                    )
                                ),
                            ),
                        )
                    ),
                ),
                (
                    12,
                    k1.DatumSeq(
                        tuple(
                            k1.DatumRecord(
                                (
                                    (0, k1.Symbol(name)),
                                    (1, k1.Nat(modulus)),
                                    (2, k1.Nat(width)),
                                    (3, k1.Nat(attempts)),
                                    (4, total_uniform),
                                )
                            )
                            for name, modulus, width, attempts, total_uniform in correspondence.sampler_map
                        )
                    ),
                ),
                (
                    13,
                    k1.DatumSeq(
                        tuple(
                            k1.Symbol(item) for item in correspondence.query_index_map
                        )
                    ),
                ),
                (
                    14,
                    _id_datum(
                        correspondence.extractor_algorithm_id,
                        "foundation.portable-algorithm",
                    ),
                ),
                (
                    15,
                    k1.DatumSeq(
                        tuple(
                            k1.Symbol(item)
                            for item in correspondence.auxiliary_distribution_map
                        )
                    ),
                ),
                (16, k1.Symbol(correspondence.forking_semantics)),
                (
                    17,
                    _id_datum(
                        correspondence.source_model_id, "analysis.experiment-profile"
                    ),
                ),
                (
                    18,
                    _id_datum(
                        correspondence.target_model_id, "analysis.experiment-profile"
                    ),
                ),
                (
                    19,
                    _id_datum(
                        correspondence.fixed_public_setup_id,
                        "analysis.fixed-public-setup",
                    ),
                ),
                (
                    20,
                    _embedded_component_datum(
                        correspondence.query_encoding_id,
                        "analysis.query-encoding",
                    ),
                ),
                (
                    21,
                    _id_datum(
                        correspondence.fresh_plan_binding_id,
                        "relations.plan-witness-binding",
                    ),
                ),
                (
                    22,
                    _id_datum(
                        correspondence.fiat_shamir_plan_binding_id,
                        "relations.plan-witness-binding",
                    ),
                ),
                (
                    23,
                    _id_datum(
                        correspondence.fresh_public_setup_view_id,
                        "pir.public-setup-invocation-view",
                    ),
                ),
                (
                    24,
                    _id_datum(
                        correspondence.fiat_shamir_public_setup_view_id,
                        "pir.public-setup-invocation-view",
                    ),
                ),
                (
                    25,
                    _id_datum(
                        correspondence.fresh_execution_view_binding_id,
                        "pir.source-binding-payload",
                    ),
                ),
                (
                    26,
                    _id_datum(
                        correspondence.fiat_shamir_execution_view_binding_id,
                        "pir.source-binding-payload",
                    ),
                ),
                (
                    27,
                    _id_datum(
                        correspondence.fs_construction_view_binding_id,
                        "pir.source-binding-payload",
                    ),
                ),
            )
        ),
    )


def _assumed_theorem_hypothesis(
    theorem_schema_id: object,
    *,
    transport: bool = False,
) -> object:
    """Form one explicit truth assumption outside theorem applicability."""

    _id_datum(theorem_schema_id, "analysis.theorem-schema")
    if not transport:
        raise TheoremError("the selected theorem-truth goal is transport-owned")
    schema = afk_v2_theorem_schema()
    if fs_theorem_schema_id(schema) != theorem_schema_id:
        raise TheoremError("the theorem-truth request names another schema")
    return theorem_truth_goal_id(schema)


def _assumed_bounded_property_theorem_hypothesis(
    theorem_assumption_id: object,
) -> object:
    """Form the bounded property witness's explicit theorem premise.

    This is deliberately not an ``analysis.theorem-schema``: the latter is
    the closed AFK transport theorem language, whereas this finite Schnorr
    witness supplies one property-owned assumption contract.
    """

    _id_datum(
        theorem_assumption_id,
        "analysis.external.theorem-assumption",
    )
    source = _SCHNORR_PINNED_SOURCE
    profile = _SCHNORR_PINNED_PROFILE
    return _exact_premise_goal_id(
        "fixed-extractor-universal-correctness",
        (
            source.protocol_source.fresh_protocol_id,
            profile.relation_definition_id,
            profile.fresh_binding_id,
            profile.extractor_algorithm_id,
            theorem_assumption_id,
        ),
        _semantic_experiment_context(
            (source_manifest_id(source.fresh_manifest),),
            (profile.profile_id,),
        ),
        k1.DatumRecord(
            (
                (
                    0,
                    _id_datum(
                        theorem_assumption_id,
                        "analysis.external.theorem-assumption",
                    ),
                ),
                (1, k1.Symbol("assumed-bounded-property-theorem")),
            )
        ),
        selected_profile=ANALYSIS_PROPERTY_PROFILE,
    )


@dataclass(frozen=True)
class AFKQuantitativeTransform:
    k: int
    challenge_count: int
    subject_id: object
    query_bound: QuantitativeExpression
    source_er: QuantitativeExpression
    knowledge_error: QuantitativeExpression
    expected_adversary_calls: QuantitativeExpression
    source_success: QuantitativeExpression
    extractor_success: QuantitativeExpression
    lemma4_extraction_lower_bound: QuantitativeExpression
    positive_polynomial_id: object
    q_one_substitution_id: object
    knowledge_success_lower_bound: QuantitativeExpression


def afk_quantitative_transform(
    *,
    k: int,
    challenge_count: int,
    subject_id: object = AFK_THEOREM_SUBJECT_SCHEMA_ID,
) -> AFKQuantitativeTransform:
    if (
        type(k) is not int
        or type(challenge_count) is not int
        or k != 2
        or challenge_count != 8
    ):
        raise QuantitativeError("selected AFK lane requires exact k=2 and N=8")
    _id_datum(subject_id)
    query_bound = afk_query_count_variable(challenge_count, subject_id)
    er = QRational(Fraction(1, challenge_count), QuantitativeSort.PROBABILITY)
    q_plus_one = qsum(
        query_bound,
        afk_query_count_literal(1, challenge_count, subject_id),
    )
    knowledge_error = QScale(
        q_plus_one,
        er,
        QuantitativeSort.PROBABILITY,
    )
    calls = QExpectedAdversaryCallsUpperBound(
        query_bound,
        2,
        AFK_ADVERSARY_RUNNING_CALL_DIMENSION_ID,
        subject_bound_afk_adversary_running_algorithm_id(challenge_count, subject_id),
    )
    epsilon = QEventProbability(
        subject_bound_experiment_body_id(
            challenge_count, subject_id, "prover-experiment"
        ),
        "prover-experiment",
        AFK_PROVER_ACCEPT_EVENT,
        ("x", "pi", "aux", "v"),
        _AFK_FORMULA_PARAMETERS,
        AFK_ADVERSARY_RO_QUERY_DIMENSION_ID,
        afk_query_abi_id(challenge_count),
        subject_id,
        "all-calls-including-repeats-and-off-image",
    )
    extractor_success = QEventProbability(
        subject_bound_experiment_body_id(
            challenge_count, subject_id, "extractor-experiment"
        ),
        "extractor-experiment",
        subject_bound_relation_success_event_id(subject_id),
        ("x", "pi", "aux", "v", "w"),
        _AFK_EXTRACTOR_FORMULA_PARAMETERS,
        AFK_ADVERSARY_RO_QUERY_DIMENSION_ID,
        afk_query_abi_id(challenge_count),
        subject_id,
        "all-calls-including-repeats-and-off-image",
    )
    lemma4_lower = QExtractionLowerBound(
        epsilon,
        knowledge_error,
        Fraction(challenge_count, challenge_count - 1),
    )
    knowledge_lower = QSignedProbabilityDifferenceOverPositivePolynomial(
        epsilon,
        knowledge_error,
        "q_KS",
        QVariable("n", QuantitativeSort.SECURITY_PARAMETER),
    )
    for expression in (
        er,
        knowledge_error,
        calls,
        epsilon,
        extractor_success,
        lemma4_lower,
        knowledge_lower,
    ):
        admit_quantitative(expression)
    return AFKQuantitativeTransform(
        k,
        challenge_count,
        subject_id,
        query_bound,
        er,
        knowledge_error,
        calls,
        epsilon,
        extractor_success,
        lemma4_lower,
        AFK_POSITIVE_POLYNOMIAL_Q_ONE,
        AFK_Q_ONE_SUBSTITUTION,
        knowledge_lower,
    )


_AFK_FORMULA_PARAMETERS = (
    ("n", QuantitativeSort.SECURITY_PARAMETER.value),
    ("Q", QuantitativeSort.QUERY_COUNT_ADVERSARY_RO.value),
    ("N", "challenge-count"),
    ("Pa", "adaptive-prover"),
)
_AFK_KNOWLEDGE_FORMULA_PARAMETERS = (
    ("q_KS", "positive-polynomial"),
) + _AFK_FORMULA_PARAMETERS
_AFK_EXTRACTOR_FORMULA_PARAMETERS = _AFK_FORMULA_PARAMETERS + (
    ("E", "uniform-black-box-extractor-algorithm"),
)


def formula_parameter_domain_id(
    name: str,
    sort_name: str,
    predicate: str,
    *subjects: object,
) -> object:
    """Identify one exact parameter domain and its applicability predicate."""

    _ascii(name, "formula-domain parameter")
    _ascii(sort_name, "formula-domain sort")
    _ascii(predicate, "formula-domain predicate")
    for subject in subjects:
        _id_datum(subject)
    identifier = _legacy_component_id(
        "analysis.formula-parameter-domain",
        k1.DatumRecord(
            (
                (0, k1.Symbol(name)),
                (1, k1.Symbol(sort_name)),
                (2, k1.Symbol(predicate)),
                (3, k1.DatumSeq(tuple(_id_datum(item) for item in subjects))),
            )
        ),
    )
    _FORMULA_PARAMETER_DOMAIN_REGISTRY[identifier.internal_reference()] = (
        name,
        sort_name,
        predicate,
        tuple(subjects),
    )
    return identifier


def _challenge_domain_adequacy_evaluator_id() -> object:
    profile = ANALYSIS_PROPERTY_PROFILE
    input_schema = analysis_profile_declaration_ref(
        profile,
        profile,
        "analysis.semantic-law",
        "finite-challenge-domain-v0",
    )
    failure_partition = analysis_profile_declaration_ref(
        profile,
        profile,
        "analysis.semantic-law",
        "analysis-attempt-failure-partition-v0",
    )
    return _analysis_id(
        "analysis.adequacy-evaluator",
        AnalysisAdequacyEvaluatorBodyV0(
            input_schema,
            (_active_analysis_profile_id(profile),),
            k1.value_type_datum(k1.BOOL),
            _Analysis_REFERENCE_CHECKER_ALGORITHM_ID,
            _Analysis_REFERENCE_CHECKER_EVALUATION_CONTRACT_ID,
            tuple(k1.direct_module_dependencies(_Analysis_REFERENCE_CHECKER_ALGORITHM)),
            True,
            failure_partition,
        ),
    )


def selected_schnorr_challenge_domain_id(
    setup: FixedPublicSetup,
) -> object:
    """Form the finite model from exact live PIR PublicCoinView leaves."""

    fixed_public_setup_id(setup)
    return _schnorr_challenge_domain_id_from_projection(
        _fixed_setup_challenge_projection(setup)
    )


def _schnorr_challenge_domain_id_from_projection(
    projection: k2.PublicCoinChallengeProjection,
) -> object:
    if type(projection) is not k2.PublicCoinChallengeProjection:
        raise QuantitativeError("Schnorr challenge source is not one PIR projection")
    modulus = projection.challenge_domain.modulus
    if type(modulus) is not int or modulus < 2:
        raise QuantitativeError("Schnorr challenge domain needs at least two values")
    semantic_status = analysis_profile_declaration_ref(
        ANALYSIS_PROPERTY_PROFILE,
        ANALYSIS_PROPERTY_PROFILE,
        "analysis.semantic-law",
        "finite-challenge-domain-v0",
    )
    return _analysis_id(
        "analysis.challenge-domain",
        AnalysisChallengeDomainBodyV0(
            _pir_static_atomic_coordinate_body(projection.challenge_coordinate),
            k1.value_type_datum(k1.NAT_U64),
            _pir_static_atomic_coordinate_body(projection.domain_coordinate),
            tuple(range(modulus)),
            _challenge_domain_adequacy_evaluator_id(),
            analysis_profile_declaration_ref_body(semantic_status),
            _CHALLENGE_DOMAIN_BODY_ISSUER,
        ),
    )


def afk_family_challenge_cardinality_parameter_domain_id(
    family: AFKAsymptoticFamily,
) -> object:
    """Form abstract AFK ``N`` without treating it as a concrete challenge set."""

    if type(family) is not AFKAsymptoticFamily or family.challenge_cardinality < 2:
        raise QuantitativeError("AFK family cardinality needs one admitted family")
    return formula_parameter_domain_id(
        "N",
        "challenge-count",
        f"family-constant-N-is-{family.challenge_cardinality}-and-at-least-two",
        family_definition_id(family),
    )


def _afk_formula_parameter_domains(
    challenge_count: int,
    subject_id: object = AFK_THEOREM_SUBJECT_SCHEMA_ID,
) -> dict[str, object]:
    if type(challenge_count) is not int or challenge_count < 2:
        raise QuantitativeError("AFK formula domains require N >= 2")
    selected_family = SELECTED_AFK_FAMILY
    if challenge_count != selected_family.challenge_cardinality:
        raise QuantitativeError(
            "bounded formula domains require the selected fixed family cardinality"
        )
    return {
        "q_KS": formula_parameter_domain_id(
            "q_KS",
            "positive-polynomial",
            "positive-polynomial-in-statement-length-n",
            AFK_POSITIVE_POLYNOMIAL_DOMAIN_ID,
        ),
        "n": formula_parameter_domain_id(
            "n",
            QuantitativeSort.SECURITY_PARAMETER.value,
            "statement-length-in-fixed-width-octets-is-at-least-one",
            SECURITY_PARAMETER_DOMAIN_ID,
            subject_id,
        ),
        "Q": formula_parameter_domain_id(
            "Q",
            QuantitativeSort.QUERY_COUNT_ADVERSARY_RO.value,
            "zero-less-than-or-equal-Q-strictly-less-than-N",
            afk_query_bound_domain_id(challenge_count),
            AFK_ADVERSARY_RO_QUERY_DIMENSION_ID,
            afk_query_abi_id(challenge_count),
            subject_id,
        ),
        "N": afk_family_challenge_cardinality_parameter_domain_id(selected_family),
        "Pa": formula_parameter_domain_id(
            "Pa",
            "adaptive-prover",
            "input-free-total-output-at-most-Q-classical-queries-and-output-length-n",
            ADAPTIVE_KNOWLEDGE_INTERFACE,
            AFK_ADVERSARY_RO_QUERY_DIMENSION_ID,
            afk_query_abi_id(challenge_count),
            subject_id,
        ),
        "epsilon": formula_parameter_domain_id(
            "epsilon",
            QuantitativeSort.PROBABILITY.value,
            "exact-event-probability-in-closed-unit-interval",
            AFK_PROVER_ACCEPT_EVENT,
            subject_id,
        ),
        "E": formula_parameter_domain_id(
            "E",
            "uniform-black-box-extractor-algorithm",
            "one-uniform-algorithm-conforming-to-the-subject-bound-extractor-profile",
            subject_bound_afk_extractor_profile_id(subject_id),
            subject_id,
        ),
    }


def _formula_domains_for(
    parameter_schema: tuple[tuple[str, str], ...],
    challenge_count: int,
    subject_id: object,
) -> tuple[tuple[str, object], ...]:
    domains = _afk_formula_parameter_domains(challenge_count, subject_id)
    return tuple((name, domains[name]) for name, _ in parameter_schema)


def afk_quantitative_formula_ids(
    transform: AFKQuantitativeTransform,
) -> dict[str, object]:
    """Form neutral formula identities consumed by the target proposition."""

    _afk_transform_body(transform)
    source_er_parameters = (("N", "challenge-count"),)
    expected_call_parameters = (("Q", QuantitativeSort.QUERY_COUNT_ADVERSARY_RO.value),)
    formulas = {
        "source-er": QuantitativeFormulaProfile(
            QuantitativeSort.PROBABILITY,
            transform.subject_id,
            source_er_parameters,
            _formula_domains_for(
                source_er_parameters, transform.challenge_count, transform.subject_id
            ),
            ("N",),
            (),
            transform.source_er,
        ),
        "source-success": QuantitativeFormulaProfile(
            QuantitativeSort.PROBABILITY,
            transform.subject_id,
            _AFK_FORMULA_PARAMETERS,
            _formula_domains_for(
                _AFK_FORMULA_PARAMETERS, transform.challenge_count, transform.subject_id
            ),
            (),
            (),
            transform.source_success,
        ),
        "extractor-success": QuantitativeFormulaProfile(
            QuantitativeSort.PROBABILITY,
            transform.subject_id,
            _AFK_EXTRACTOR_FORMULA_PARAMETERS,
            _formula_domains_for(
                _AFK_EXTRACTOR_FORMULA_PARAMETERS,
                transform.challenge_count,
                transform.subject_id,
            ),
            (),
            (),
            transform.extractor_success,
        ),
        "knowledge-error": QuantitativeFormulaProfile(
            QuantitativeSort.PROBABILITY,
            transform.subject_id,
            _AFK_FORMULA_PARAMETERS[:-1],
            _formula_domains_for(
                _AFK_FORMULA_PARAMETERS[:-1],
                transform.challenge_count,
                transform.subject_id,
            ),
            ("N",),
            ("n",),
            transform.knowledge_error,
        ),
        "knowledge-success-lower-bound": QuantitativeFormulaProfile(
            QuantitativeSort.SIGNED_PROBABILITY_LOWER_BOUND,
            transform.subject_id,
            _AFK_KNOWLEDGE_FORMULA_PARAMETERS,
            _formula_domains_for(
                _AFK_KNOWLEDGE_FORMULA_PARAMETERS,
                transform.challenge_count,
                transform.subject_id,
            ),
            (),
            (),
            transform.knowledge_success_lower_bound,
        ),
        "expected-adversary-calls-upper-bound": QuantitativeFormulaProfile(
            QuantitativeSort.EXPECTED_COUNT_ADVERSARY_RUNNING_ALGORITHM,
            transform.subject_id,
            expected_call_parameters,
            _formula_domains_for(
                expected_call_parameters,
                transform.challenge_count,
                transform.subject_id,
            ),
            (),
            (),
            transform.expected_adversary_calls,
        ),
        "lemma4-transcript-extraction-lower-bound": QuantitativeFormulaProfile(
            QuantitativeSort.SIGNED_PROBABILITY_LOWER_BOUND,
            transform.subject_id,
            _AFK_FORMULA_PARAMETERS,
            _formula_domains_for(
                _AFK_FORMULA_PARAMETERS, transform.challenge_count, transform.subject_id
            ),
            (),
            (),
            transform.lemma4_extraction_lower_bound,
        ),
    }
    result: dict[str, object] = {}
    for name, profile in formulas.items():
        identifier = quantitative_formula_id(profile)
        key = identifier.internal_reference()
        role_record = (name, transform.subject_id)
        prior_role = _FORMULA_ROLE_REGISTRY.get(key)
        if (
            prior_role is not None
            and prior_role != role_record
            and prior_role[0] != name
        ):
            raise QuantitativeError(
                "one quantitative formula identity was assigned two semantic roles"
            )
        if prior_role is None:
            _FORMULA_ROLE_REGISTRY[key] = role_record
        result[name] = identifier
    return result


def afk_expected_invocation_bound_id(
    transform: AFKQuantitativeTransform,
) -> object:
    formula_ids = afk_quantitative_formula_ids(transform)
    dimension = next(
        item
        for item in AFK_RESOURCE_DIMENSIONS
        if item.name == "adversary-running-calls"
    )
    return expected_invocation_bound_id(
        ExpectedInvocationBound(
            subject_bound_experiment_body_id(
                transform.challenge_count,
                transform.subject_id,
                "extractor-experiment",
            ),
            subject_bound_afk_adversary_running_algorithm_id(
                transform.challenge_count, transform.subject_id
            ),
            resource_dimension_id(dimension),
            "less-than-or-equal",
            formula_ids["expected-adversary-calls-upper-bound"],
        )
    )


def _afk_transform_body(transform: AFKQuantitativeTransform) -> object:
    if type(transform) is not AFKQuantitativeTransform:
        raise QuantitativeError("AFK quantitative transform has the wrong shape")
    expected = afk_quantitative_transform(
        k=transform.k,
        challenge_count=transform.challenge_count,
        subject_id=transform.subject_id,
    )
    expressions = (
        (transform.source_er, expected.source_er),
        (transform.knowledge_error, expected.knowledge_error),
        (transform.expected_adversary_calls, expected.expected_adversary_calls),
        (transform.source_success, expected.source_success),
        (transform.extractor_success, expected.extractor_success),
        (
            transform.lemma4_extraction_lower_bound,
            expected.lemma4_extraction_lower_bound,
        ),
        (
            transform.knowledge_success_lower_bound,
            expected.knowledge_success_lower_bound,
        ),
    )
    if any(not quantitative_equal(actual, wanted) for actual, wanted in expressions):
        raise QuantitativeError(
            "AFK quantitative transform was authored or substituted"
        )
    if (
        transform.positive_polynomial_id != expected.positive_polynomial_id
        or transform.q_one_substitution_id != expected.q_one_substitution_id
    ):
        raise QuantitativeError("AFK positive-polynomial substitution was authored")
    return k1.DatumRecord(
        (
            (0, k1.Nat(transform.k)),
            (1, k1.Nat(transform.challenge_count)),
            (2, _id_datum(transform.subject_id)),
            (3, quantitative_body(transform.query_bound)),
            (4, quantitative_body(transform.source_er)),
            (5, quantitative_body(transform.knowledge_error)),
            (6, quantitative_body(transform.expected_adversary_calls)),
            (7, quantitative_body(transform.source_success)),
            (8, quantitative_body(transform.extractor_success)),
            (9, quantitative_body(transform.lemma4_extraction_lower_bound)),
            (
                10,
                _id_datum(
                    transform.positive_polynomial_id,
                    "analysis.positive-polynomial",
                ),
            ),
            (
                11,
                _embedded_component_datum(
                    transform.q_one_substitution_id,
                    "analysis.theorem-substitution",
                ),
            ),
            (12, quantitative_body(transform.knowledge_success_lower_bound)),
        )
    )


def afk_knowledge_soundness_conclusion(
    transform: AFKQuantitativeTransform,
) -> AFKKnowledgeSoundnessConclusion:
    """Derive, rather than accept, the exact Definition-10 target conclusion."""

    _afk_transform_body(transform)
    formula_ids = afk_quantitative_formula_ids(transform)
    conclusion = AFKKnowledgeSoundnessConclusion(
        subject_bound_afk_extractor_profile_id(transform.subject_id),
        subject_bound_afk_distribution_law_id(
            transform.challenge_count, transform.subject_id
        ),
        ("x", "pi", "aux", "v"),
        ("x", "pi", "aux", "v", "w"),
        subject_bound_relation_success_event_id(transform.subject_id),
        "greater-than-or-equal",
        formula_ids["extractor-success"],
        formula_ids["knowledge-error"],
        formula_ids["knowledge-success-lower-bound"],
        afk_expected_invocation_bound_id(transform),
    )
    _property_conclusion_body(conclusion)
    return conclusion


def afk_quantitative_transform_id(
    transform: AFKQuantitativeTransform,
) -> object:
    # The full typed AST is already authenticated by the exact durable
    # quantitative-formula IDs.  Re-embedding every recursive expression here
    # would duplicate those bodies and can exceed Foundation's cumulative canonical
    # byte bound.  This nested transform value therefore records the exact
    # derived formula coordinate map and substitutions once.
    _afk_transform_body(transform)
    formula_ids = afk_quantitative_formula_ids(transform)
    compact_body = k1.DatumRecord(
        (
            (0, k1.Nat(transform.k)),
            (1, k1.Nat(transform.challenge_count)),
            (2, _portable_subject_datum(transform.subject_id)),
            (
                3,
                k1.DatumSeq(
                    tuple(
                        k1.DatumRecord(
                            (
                                (0, k1.Symbol(role)),
                                (
                                    1,
                                    _id_datum(
                                        formula_ids[role],
                                        "analysis.quantitative-formula",
                                    ),
                                ),
                            )
                        )
                        for role in sorted(formula_ids)
                    )
                ),
            ),
            (
                4,
                _id_datum(
                    transform.positive_polynomial_id,
                    "analysis.positive-polynomial",
                ),
            ),
            (
                5,
                _embedded_component_datum(
                    transform.q_one_substitution_id,
                    "analysis.theorem-substitution",
                ),
            ),
        )
    )
    return _legacy_component_id(
        "analysis.quantitative-transform",
        compact_body,
    )


def afk_target_conclusion_id(
    conclusion: AFKKnowledgeSoundnessConclusion,
) -> object:
    return _legacy_component_id(
        "analysis.property-conclusion", _property_conclusion_body(conclusion)
    )


@dataclass(frozen=True)
class AFKPointwiseQuantities:
    query_bound: int
    knowledge_error: Fraction
    expected_adversary_calls: int
    lemma4_factor: Fraction


def instantiate_afk_at_query_bound(
    transform: AFKQuantitativeTransform, query_bound: int
) -> AFKPointwiseQuantities:
    """Evaluate the universal symbolic lane at one legal bounded Q.

    This is a diagnostic projection, not the target proposition and not a
    replacement for its universal Q binder.
    """

    _afk_transform_body(transform)
    if (
        type(query_bound) is not int
        or query_bound < 0
        or query_bound >= transform.challenge_count
    ):
        raise QuantitativeError("AFK query instantiation requires 0 <= Q < N")
    return AFKPointwiseQuantities(
        query_bound,
        Fraction(query_bound + 1, transform.challenge_count),
        query_bound + 2,
        Fraction(transform.challenge_count, transform.challenge_count - 1),
    )


_SCHNORR_PINNED_SOURCE = derive_fresh_fs_relation_source(total_uniform_schnorr_case())
_SCHNORR_PINNED_PROFILE = derive_schnorr_special_soundness_profile(
    _SCHNORR_PINNED_SOURCE
)
_SCHNORR_PINNED_MODEL = fresh_special_soundness_model(k=2, challenge_count=8)
_SCHNORR_PINNED_BASE_PROPOSITION = form_special_soundness_proposition(
    _SCHNORR_PINNED_SOURCE,
    _SCHNORR_PINNED_MODEL,
    _SCHNORR_PINNED_PROFILE,
    (
        schnorr_relation_correspondence_hypothesis_id(_SCHNORR_PINNED_PROFILE),
        k2_static_view_support_hypothesis_id(_SCHNORR_PINNED_SOURCE),
    ),
)


def _schnorr_two_special_soundness_theorem_assumption_body() -> object:
    return k1.DatumRecord(
        (
            (0, k1.Symbol("bounded-schnorr-two-special-soundness")),
            (
                1,
                _id_datum(
                    analysis_goal_id(_SCHNORR_PINNED_BASE_PROPOSITION.goal),
                    "analysis.goal",
                ),
            ),
            (
                2,
                _id_datum(
                    _SCHNORR_PINNED_PROFILE.profile_id,
                    "analysis.experiment-profile",
                ),
            ),
            (
                3,
                _id_datum(
                    experiment_model_id(_SCHNORR_PINNED_MODEL),
                    "analysis.experiment-profile",
                ),
            ),
            (
                4,
                _id_datum(
                    SCHNORR_EXTRACTOR_ALGORITHM,
                    "foundation.portable-algorithm",
                ),
            ),
            (5, k1.Symbol("truth-is-an-explicit-assumption")),
        )
    )


SCHNORR_TWO_SPECIAL_SOUNDNESS_THEOREM_ID = k1.content_id(
    "analysis.external.theorem-assumption",
    k1.encode_datum(_schnorr_two_special_soundness_theorem_assumption_body()),
    semantic_regime=k1.SEMANTIC_REGIME_ID,
)
ASSUMED_SCHNORR_TWO_SPECIAL_SOUNDNESS = _assumed_bounded_property_theorem_hypothesis(
    SCHNORR_TWO_SPECIAL_SOUNDNESS_THEOREM_ID
)
_SCHNORR_PINNED_PROPOSITION = form_special_soundness_proposition(
    _SCHNORR_PINNED_SOURCE,
    _SCHNORR_PINNED_MODEL,
    _SCHNORR_PINNED_PROFILE,
    (
        schnorr_relation_correspondence_hypothesis_id(_SCHNORR_PINNED_PROFILE),
        k2_static_view_support_hypothesis_id(_SCHNORR_PINNED_SOURCE),
        ASSUMED_SCHNORR_TWO_SPECIAL_SOUNDNESS,
    ),
)


# ---------------------------------------------------------------------------
# Global AFK theorem schema: no family, member, model, or formula coordinates
# ---------------------------------------------------------------------------


AFK_PDF_SHA256 = "93837e2dd7c0e99ef3d06bbb4f235d9ed0dcafb8b96e56d867e7548751e9122c"
AFK_PRIMARY_SOURCE_LOCATORS = (
    "Definition 4",
    "Definition 10",
    "Definition 11",
    "Section 4 Figure 3 and consistency prose immediately before Lemma 4",
    "Lemma 4",
    "Section 6.3 adaptive construction immediately before Theorem 4",
    "Remark 2",
    "Remark 6",
    "Theorem 4",
)


@dataclass(frozen=True)
class TheoremTemplateComponent:
    component_kind: str
    canonical_clauses: tuple[str, ...]


@dataclass(frozen=True)
class LocalOperatorTemplate:
    ordinal: int
    operand_sorts: tuple[str, ...]
    result_sort: str
    template_ast: str


def _template_component_body(component: TheoremTemplateComponent) -> object:
    if (
        type(component) is not TheoremTemplateComponent
        or type(component.component_kind) is not str
        or type(component.canonical_clauses) is not tuple
        or not component.canonical_clauses
        or any(type(item) is not str for item in component.canonical_clauses)
    ):
        raise TheoremError(
            "global theorem components must be closed structured string clauses"
        )
    candidates: tuple[tuple[str, str, tuple[TheoremTemplateComponent, ...]], ...] = (
        (
            "analysis.theorem-property-schema",
            "afk-source-property-v0",
            (AFK_SOURCE_PROPERTY_COMPONENT,),
        ),
        (
            "analysis.theorem-property-schema",
            "afk-target-property-v0",
            (AFK_TARGET_PROPERTY_COMPONENT,),
        ),
        (
            "analysis.theorem-experiment-schema",
            "afk-source-experiment-v0",
            (AFK_SOURCE_EXPERIMENT_COMPONENT,),
        ),
        (
            "analysis.theorem-experiment-schema",
            "afk-target-experiment-v0",
            (AFK_TARGET_EXPERIMENT_COMPONENT,),
        ),
        (
            "analysis.theorem-transform-program",
            "afk-transform-program-v0",
            (AFK_TRANSFORM_PROGRAM_COMPONENT,),
        ),
        (
            "analysis.theorem-conclusion-law",
            "afk-conclusion-law-v0",
            (AFK_CONCLUSION_LAW_COMPONENT,),
        ),
    )
    contract: object | None = None
    for declaration_kind, label, values in candidates:
        if component == values[0]:
            contract = analysis_profile_declaration_ref(
                ANALYSIS_TRANSPORT_PROFILE,
                ANALYSIS_TRANSPORT_PROFILE,
                declaration_kind,
                label,
            )
            break
    if contract is None:
        indexed_candidates = (
            (
                "analysis.theorem-source-view-schema",
                "afk-source-view",
                AFK_REQUIRED_SOURCE_VIEW_COMPONENTS,
            ),
            ("analysis.theorem-map-schema", "afk-map", AFK_MAP_COMPONENTS),
            (
                "analysis.theorem-side-condition-schema",
                "afk-side-condition",
                AFK_SIDE_CONDITION_COMPONENTS,
            ),
        )
        matches = tuple(
            (declaration_kind, f"{prefix}-{ordinal}")
            for declaration_kind, prefix, values in indexed_candidates
            for ordinal, value in enumerate(values)
            if component == value
        )
        if len(matches) != 1:
            raise TheoremError(
                "theorem component is absent from the closed transport catalog"
            )
        declaration_kind, label = matches[0]
        contract = analysis_profile_declaration_ref(
            ANALYSIS_TRANSPORT_PROFILE,
            ANALYSIS_TRANSPORT_PROFILE,
            declaration_kind,
            label,
        )
    # The selected declaration contract carries the complete finite component
    # interpretation.  Its lifted payload is Unit: no display clause, prose,
    # or host-only spelling enters the theorem semantic body.
    return k1.DatumRecord(
        (
            (0, analysis_profile_declaration_ref_body(contract)),
            (1, k1.DatumVariant(0, k1.Unit())),
        )
    )


def _theorem_template_operand_sort_body(sort: str) -> object:
    concrete = {
        "LogicalNat": "logical-natural",
        "Probability": "probability",
        "SignedProbabilityLowerBound": "signed-probability-lower-bound",
    }
    if sort in concrete:
        ref = analysis_profile_declaration_ref(
            ANALYSIS_TRANSPORT_PROFILE,
            ANALYSIS_TRANSPORT_PROFILE,
            "analysis.quantitative-sort",
            concrete[sort],
        )
        return k1.DatumVariant(0, analysis_profile_declaration_ref_body(ref))
    local = {
        "LocalChallengeCardinality(0)": (1, 26),
        "LocalQueryCount(0)": (2, 27),
        "LocalExpectedCount(0)": (3, 28),
        "LocalPositivePolynomial(LogicalNat)": (4, 2),
        "ExpectedCount(LocalAdversaryInvocation(1))": (3, 28),
    }
    selected = local.get(sort)
    if selected is None:
        raise TheoremError("unknown theorem-template operand sort")
    case, local_binding_ordinal = selected
    return k1.DatumVariant(case, k1.Nat(local_binding_ordinal))


def _local_operator_body(operator: LocalOperatorTemplate) -> object:
    if (
        type(operator) is not LocalOperatorTemplate
        or type(operator.ordinal) is not int
        or operator.ordinal < 0
        or type(operator.operand_sorts) is not tuple
        or not operator.operand_sorts
        or any(type(item) is not str for item in operator.operand_sorts)
        or type(operator.result_sort) is not str
        or type(operator.template_ast) is not str
    ):
        raise TheoremError("local theorem operator has a malformed closed template")
    expected = tuple(
        item for item in AFK_LOCAL_OPERATOR_CATALOG if item.ordinal == operator.ordinal
    )
    if len(expected) != 1 or operator != expected[0]:
        raise TheoremError("local theorem operator is outside the closed AFK catalog")
    expression_ref = analysis_profile_declaration_ref(
        ANALYSIS_TRANSPORT_PROFILE,
        ANALYSIS_TRANSPORT_PROFILE,
        "analysis.theorem-template-expression",
        f"afk-local-operator-{operator.ordinal}",
    )
    earlier_dependencies = {
        0: (),
        1: (0,),
        2: (0,),
        3: (),
    }[operator.ordinal]
    return k1.DatumRecord(
        (
            (0, k1.Nat(operator.ordinal)),
            (
                1,
                k1.DatumSeq(
                    tuple(
                        _theorem_template_operand_sort_body(item)
                        for item in operator.operand_sorts
                    )
                ),
            ),
            (2, _theorem_template_operand_sort_body(operator.result_sort)),
            (
                3,
                k1.DatumRecord(
                    (
                        (
                            0,
                            analysis_profile_declaration_ref_body(expression_ref),
                        ),
                        (
                            1,
                            k1.DatumSeq(
                                tuple(k1.Nat(item) for item in earlier_dependencies)
                            ),
                        ),
                    )
                ),
            ),
        )
    )


AFK_PROOF_STATUS_COMPONENT = TheoremTemplateComponent(
    "proof-status",
    (
        "authority-class-imported-paper-only",
        "admitted-proof-artifact-none",
        "truth-discharge-external-post-formation-proposition",
        "schema-admission-establishes-no-truth",
    ),
)
AFK_SOURCE_PROPERTY_COMPONENT = TheoremTemplateComponent(
    "source-property",
    (
        "local-asymptotic-family-binder-ordinal-0",
        "k-equals-2",
        "one-challenge-cardinality-role-fixed-across-logical-n",
        "exists-one-uniform-polynomial-time-deterministic-extractor",
        "forall-logical-n",
        "forall-accepted-same-statement-same-commitment-distinct-challenge-pair",
        "extract-one-relation-witness",
    ),
)
AFK_TARGET_PROPERTY_COMPONENT = TheoremTemplateComponent(
    "target-property",
    (
        "local-asymptotic-family-binder-ordinal-0",
        "adaptive-classical-rom-definition-10-q-strictly-less-than-N",
        "exists-positive-polynomial-qKS",
        "exists-one-uniform-black-box-extractor",
        "forall-logical-n-then-forall-Q-lt-N-then-forall-total-output-Pa",
        "statement-is-Pa-output-not-outer-universal",
        "preserve-x-pi-aux-v-law",
        "success-is-accept-and-local-relation-holds-x-w",
    ),
)
AFK_SOURCE_EXPERIMENT_COMPONENT = TheoremTemplateComponent(
    "source-experiment",
    (
        "three-move-public-coin-family",
        "order-statement-commitment-uniform-challenge-response",
        "challenge-set-finite-and-cardinality-fixed-across-n",
        "source-extractor-input-one-accepted-distinct-challenge-pair",
    ),
)
AFK_TARGET_EXPERIMENT_COMPONENT = TheoremTemplateComponent(
    "target-experiment",
    (
        "afk-definition-10-adaptive-classical-rom",
        "input-free-total-output-unbounded-time-Pa",
        "finite-index-domain-bitstrings-of-length-at-most-u-of-n",
        "finite-lazy-random-function-table-at-each-n",
        "all-image-and-off-image-queries-count-toward-Q",
        "two-distinct-probability-spaces-and-exact-output-law",
        "extractor-input-only-n-and-black-box-Pa",
        "extractor-reruns-one-fixed-deterministic-next-message-prover-state",
    ),
)
AFK_REQUIRED_SOURCE_VIEW_COMPONENTS = tuple(
    TheoremTemplateComponent("source-view", (role,))
    for role in (
        "Statement",
        "RelationWitness",
        "Commitment",
        "Challenge",
        "Response",
        "Acceptance",
        "FixedPublicSetup",
        "FreshInteraction",
        "FiatShamirInteraction",
        "FullRandomOracleProcess",
        "BoundedBitStringIndexContract",
    )
)
AFK_MAP_COMPONENTS = (
    TheoremTemplateComponent(
        "map",
        (
            "Statement-to-RandomOracleStatementIndex",
            "ExactInjectiveEncoding",
        ),
    ),
    TheoremTemplateComponent(
        "map",
        (
            "Commitment-to-RandomOracleCommitmentIndex",
            "ExactInjectiveEncoding",
        ),
    ),
    TheoremTemplateComponent(
        "map",
        (
            "Challenge-Response-Proof-VerifierOutput-Relation-Witness-Setup",
            "ExactTypedEquality",
        ),
    ),
)
AFK_SIDE_CONDITION_COMPONENTS = tuple(
    TheoremTemplateComponent("side-condition", (clause,))
    for clause in (
        "total-single-valued-coherent-family-denotation",
        "finite-challenge-set-cardinality-at-least-2-and-fixed-across-n",
        "public-coin-uniformity-and-independence",
        "uniform-efficient-source-extractor-relation-and-verifier",
        "finite-bounded-bitstring-random-oracle-index-with-efficient-encoder-equality-and-table",
        "exact-adaptive-classical-lazy-random-function-process",
        "framing-sampling-programming-and-rerun-adequacy",
        "restricted-domain-0-le-Q-lt-local-fixed-N",
    )
)
AFK_LOCAL_OPERATOR_CATALOG = (
    LocalOperatorTemplate(
        0,
        ("LocalQueryCount(0)", "LocalChallengeCardinality(0)"),
        "Probability",
        "bounded-ratio((Q+1),N);domain=0<=Q<N",
    ),
    LocalOperatorTemplate(
        1,
        (
            "Probability",
            "LogicalNat",
            "LocalQueryCount(0)",
            "LocalChallengeCardinality(0)",
            "LocalPositivePolynomial(LogicalNat)",
        ),
        "SignedProbabilityLowerBound",
        "divide((epsilon-operator0(Q,N)),qKS(n))",
    ),
    LocalOperatorTemplate(
        2,
        ("Probability", "LocalQueryCount(0)", "LocalChallengeCardinality(0)"),
        "SignedProbabilityLowerBound",
        "scale(N/(N-1),(epsilon-operator0(Q,N)))",
    ),
    LocalOperatorTemplate(
        3,
        ("LocalQueryCount(0)",),
        "ExpectedCount(LocalAdversaryInvocation(1))",
        "expected-count(Q+2)",
    ),
)
AFK_FAMILY_OPERATOR_SIGNATURES = (
    (("n:LogicalNat", "Q:QueryCount"), "Probability"),
    (
        ("epsilon:Probability", "n:LogicalNat", "Q:QueryCount"),
        "SignedProbabilityLowerBound",
    ),
    (
        ("epsilon:Probability", "n:LogicalNat", "Q:QueryCount"),
        "SignedProbabilityLowerBound",
    ),
    (("Q:QueryCount",), "ExpectedCount(AdversaryInvocations)"),
)
AFK_MEMBER_FORMULA_ROLES = (
    "knowledge-error",
    "knowledge-success-lower-bound",
    "lemma4-transcript-extraction-lower-bound",
    "expected-adversary-calls-upper-bound",
)
AFK_TRANSFORM_PROGRAM_COMPONENT = TheoremTemplateComponent(
    "transform-program",
    (
        "local-query-resource-role-0",
        "local-adversary-invocation-resource-role-1",
        "local-challenge-cardinality-role-0",
        "operator-ordinals-exactly-0-1-2-3",
        "target-quantifier-ordinal-0-binds-singleton-logical-nat-polynomial-one",
        "bind-each-local-operator-exactly-once",
        "import-no-ambient-loss",
        "retain-exact-output-marginal-equality",
    ),
)
AFK_CONCLUSION_LAW_COMPONENT = TheoremTemplateComponent(
    "conclusion-law",
    (
        "reconstruct-exact-target-property",
        "quantitative-results-operator-0-operator-1-operator-3",
        "retain-theorem-truth-source-property-model-map-efficiency-process-side-conditions",
        "schema-admission-implies-no-security-truth",
    ),
)


# Closed 31-entry theorem-local binder grammar from the selected AFK schema.
# Display prose and binder spellings are excluded; ordinal, role constructor,
# and earlier-ordinal dependency sequence are the semantic coordinates.
AFK_LOCAL_BINDING_CATALOG = (
    ("asymptotic-family-parameter", ()),
    ("logical-nat-parameter", (0,)),
    ("positive-polynomial-parameter", ()),
    ("uniform-source-extractor", (0,)),
    ("accepting-distinct-transcript-pair", (0, 1)),
    ("uniform-black-box-target-extractor", (0,)),
    ("statement-role", (0, 1)),
    ("relation-witness-role", (0, 1)),
    ("commitment-role", (0, 1)),
    ("challenge-role", (0, 1)),
    ("response-role", (0, 1)),
    ("acceptance-role", (0, 1)),
    ("fixed-public-setup-role", (0, 1)),
    ("fresh-interaction-role", (0, 1)),
    ("fiat-shamir-interaction-role", (0, 1)),
    ("full-random-oracle-process-role", (0, 1)),
    ("proof-role", (0, 1)),
    ("auxiliary-output-role", (0, 1)),
    ("verifier-output-role", (0, 1)),
    ("relation-role", (0, 1)),
    ("random-oracle-index-role", (0, 1)),
    ("random-oracle-statement-index-role", (0, 1)),
    ("random-oracle-commitment-index-role", (0, 1)),
    ("verifier-role", (0, 1)),
    ("challenge-sampler-role", (0, 1)),
    ("bounded-bitstring-index-contract-role", (0, 1, 20)),
    ("challenge-cardinality-role", (0,)),
    ("query-count-resource-role", (0, 15, 20, 25)),
    ("expected-count-resource-role", (0,)),
    ("query-count-parameter", (0, 1, 26, 27)),
    ("input-free-adaptive-oracle-prover", (0, 1, 20, 27, 29)),
)


def _afk_local_binding_catalog_body() -> object:
    return k1.DatumSeq(
        tuple(
            k1.DatumRecord(
                (
                    (0, k1.Nat(ordinal)),
                    (
                        1,
                        analysis_profile_declaration_ref_body(
                            analysis_profile_declaration_ref(
                                ANALYSIS_TRANSPORT_PROFILE,
                                ANALYSIS_TRANSPORT_PROFILE,
                                "analysis.theorem-local-binding-kind",
                                role,
                            )
                        ),
                    ),
                    (2, k1.DatumSeq(tuple(k1.Nat(item) for item in dependencies))),
                    (
                        3,
                        analysis_profile_declaration_ref_body(
                            analysis_profile_declaration_ref(
                                ANALYSIS_TRANSPORT_PROFILE,
                                ANALYSIS_TRANSPORT_PROFILE,
                                "analysis.theorem-local-denotation-schema",
                                f"afk-local-binding-{ordinal}",
                            )
                        ),
                    ),
                )
            )
            for ordinal, (role, dependencies) in enumerate(AFK_LOCAL_BINDING_CATALOG)
        )
    )


def _selected_statement_template_body(
    source_property: TheoremTemplateComponent = AFK_SOURCE_PROPERTY_COMPONENT,
    target_property: TheoremTemplateComponent = AFK_TARGET_PROPERTY_COMPONENT,
    source_experiment: TheoremTemplateComponent = AFK_SOURCE_EXPERIMENT_COMPONENT,
    target_experiment: TheoremTemplateComponent = AFK_TARGET_EXPERIMENT_COMPONENT,
    source_views: tuple[
        TheoremTemplateComponent, ...
    ] = AFK_REQUIRED_SOURCE_VIEW_COMPONENTS,
    maps: tuple[TheoremTemplateComponent, ...] = AFK_MAP_COMPONENTS,
    side_conditions: tuple[
        TheoremTemplateComponent, ...
    ] = AFK_SIDE_CONDITION_COMPONENTS,
    operators: tuple[LocalOperatorTemplate, ...] = AFK_LOCAL_OPERATOR_CATALOG,
    transform_program: TheoremTemplateComponent = AFK_TRANSFORM_PROGRAM_COMPONENT,
    conclusion_law: TheoremTemplateComponent = AFK_CONCLUSION_LAW_COMPONENT,
) -> object:
    return k1.DatumRecord(
        (
            (0, _afk_local_binding_catalog_body()),
            (1, _template_component_body(source_property)),
            (2, _template_component_body(target_property)),
            (3, _template_component_body(source_experiment)),
            (4, _template_component_body(target_experiment)),
            (
                5,
                k1.DatumSeq(
                    tuple(_template_component_body(item) for item in source_views)
                ),
            ),
            (
                6,
                k1.DatumSeq(tuple(_template_component_body(item) for item in maps)),
            ),
            (
                7,
                k1.DatumSeq(
                    tuple(_template_component_body(item) for item in side_conditions)
                ),
            ),
            (
                8,
                k1.DatumSeq(tuple(_local_operator_body(item) for item in operators)),
            ),
            (9, _template_component_body(transform_program)),
            (10, _template_component_body(conclusion_law)),
        )
    )


# Independent pin for the selected statement body.  Do not derive this constant
# from the body it authenticates: a statement edit must fail closed until a
# reviewer deliberately rotates the literal and the accompanying source record.
AFK_SELECTED_STATEMENT_CONTENT_SHA256 = (
    "13d270f6f386241d7c1d62e1a007432fd8522b1ad00b26f9ede5a91312505a1c"
)


@dataclass(frozen=True)
class AFKTheoremAuthority:
    stable_source_id: str
    bibliographic_version: int
    publication_date: str
    artifact_media_type: str
    artifact_sha256: str
    exact_locators: tuple[str, ...]
    statement_content_sha256: str


def _theorem_authority_body(authority: AFKTheoremAuthority) -> object:
    if (
        type(authority) is not AFKTheoremAuthority
        or type(authority.stable_source_id) is not str
        or not authority.stable_source_id.startswith("iacr-eprint:")
        or type(authority.bibliographic_version) is not int
        or authority.bibliographic_version < 0
        or type(authority.publication_date) is not str
        or type(authority.artifact_media_type) is not str
        or authority.artifact_media_type != "application/pdf"
        or type(authority.artifact_sha256) is not str
        or type(authority.exact_locators) is not tuple
        or not authority.exact_locators
        or any(type(item) is not str for item in authority.exact_locators)
        or type(authority.statement_content_sha256) is not str
        or len(authority.artifact_sha256) != 64
        or len(authority.statement_content_sha256) != 64
        or any(item not in "0123456789abcdef" for item in authority.artifact_sha256)
        or any(
            item not in "0123456789abcdef"
            for item in authority.statement_content_sha256
        )
    ):
        raise TheoremError("theorem source authority is not closed finite metadata")
    publication_kind = analysis_profile_declaration_ref(
        ANALYSIS_THEOREM_SOURCE_VALIDATION_PROFILE,
        ANALYSIS_THEOREM_SOURCE_VALIDATION_PROFILE,
        "analysis.theorem-source-kind",
        "iacr-eprint-pdf",
    )
    return k1.DatumRecord(
        (
            (0, analysis_profile_declaration_ref_body(publication_kind)),
            (
                1,
                k1.BytesValue(
                    _ascii(authority.stable_source_id, "stable source ID").encode(
                        "ascii"
                    )
                ),
            ),
            (
                2,
                k1.DatumRecord(
                    (
                        (
                            0,
                            k1.BytesValue(
                                str(authority.bibliographic_version).encode("ascii")
                            ),
                        ),
                        (
                            1,
                            k1.BytesValue(
                                _ascii(
                                    authority.publication_date,
                                    "publication date",
                                ).encode("ascii")
                            ),
                        ),
                    )
                ),
            ),
            (
                3,
                k1.BytesValue(
                    _ascii(authority.artifact_media_type, "artifact media type").encode(
                        "ascii"
                    )
                ),
            ),
            (4, k1.BytesValue(bytes.fromhex(authority.artifact_sha256))),
            (
                5,
                k1.DatumSeq(
                    tuple(
                        k1.BytesValue(
                            _printable_ascii(item, "source locator").encode("ascii")
                        )
                        for item in authority.exact_locators
                    )
                ),
            ),
        )
    )


AFK_SELECTED_AUTHORITY = AFKTheoremAuthority(
    "iacr-eprint:2021/1377",
    2,
    "2022-02-16",
    "application/pdf",
    AFK_PDF_SHA256,
    AFK_PRIMARY_SOURCE_LOCATORS,
    AFK_SELECTED_STATEMENT_CONTENT_SHA256,
)


@dataclass(frozen=True)
class FSTheoremSchema:
    authority: AFKTheoremAuthority
    proof_status: TheoremTemplateComponent
    source_property_template: TheoremTemplateComponent
    target_property_template: TheoremTemplateComponent
    source_experiment_template: TheoremTemplateComponent
    target_experiment_template: TheoremTemplateComponent
    required_source_view_templates: tuple[TheoremTemplateComponent, ...]
    map_templates: tuple[TheoremTemplateComponent, ...]
    side_condition_templates: tuple[TheoremTemplateComponent, ...]
    local_operator_catalog: tuple[LocalOperatorTemplate, ...]
    transform_program_template: TheoremTemplateComponent
    conclusion_law_template: TheoremTemplateComponent
    _issuer: object


_GLOBAL_SCHEMA_ISSUER = object()


def _expected_global_schema() -> FSTheoremSchema:
    return FSTheoremSchema(
        AFK_SELECTED_AUTHORITY,
        AFK_PROOF_STATUS_COMPONENT,
        AFK_SOURCE_PROPERTY_COMPONENT,
        AFK_TARGET_PROPERTY_COMPONENT,
        AFK_SOURCE_EXPERIMENT_COMPONENT,
        AFK_TARGET_EXPERIMENT_COMPONENT,
        AFK_REQUIRED_SOURCE_VIEW_COMPONENTS,
        AFK_MAP_COMPONENTS,
        AFK_SIDE_CONDITION_COMPONENTS,
        AFK_LOCAL_OPERATOR_CATALOG,
        AFK_TRANSFORM_PROGRAM_COMPONENT,
        AFK_CONCLUSION_LAW_COMPONENT,
        _GLOBAL_SCHEMA_ISSUER,
    )


def _global_schema_body(schema: FSTheoremSchema) -> object:
    """Return only the theorem's restricted semantic statement body.

    Source provenance, bibliographic metadata, artifact validation, and the
    current truth-discharge policy deliberately do not enter this body.
    """

    if (
        type(schema) is not FSTheoremSchema
        or schema._issuer is not _GLOBAL_SCHEMA_ISSUER
    ):
        raise TheoremError("global AFK schema has the wrong exact carrier")
    if (
        schema.source_property_template.component_kind != "source-property"
        or schema.target_property_template.component_kind != "target-property"
        or schema.source_experiment_template.component_kind != "source-experiment"
        or schema.target_experiment_template.component_kind != "target-experiment"
        or len(schema.required_source_view_templates) != 11
        or any(
            item.component_kind != "source-view"
            for item in schema.required_source_view_templates
        )
        or len(schema.map_templates) != 3
        or any(item.component_kind != "map" for item in schema.map_templates)
        or len(schema.side_condition_templates) != 8
        or any(
            item.component_kind != "side-condition"
            for item in schema.side_condition_templates
        )
        or schema.transform_program_template.component_kind != "transform-program"
        or schema.conclusion_law_template.component_kind != "conclusion-law"
        or tuple(item.ordinal for item in schema.local_operator_catalog) != (0, 1, 2, 3)
        or any(
            item.operand_sorts != expected.operand_sorts
            or item.result_sort != expected.result_sort
            for item, expected in zip(
                schema.local_operator_catalog,
                AFK_LOCAL_OPERATOR_CATALOG,
                strict=True,
            )
        )
    ):
        raise TheoremError("global AFK schema violates its restricted grammar")
    statement_body = _selected_statement_template_body(
        schema.source_property_template,
        schema.target_property_template,
        schema.source_experiment_template,
        schema.target_experiment_template,
        schema.required_source_view_templates,
        schema.map_templates,
        schema.side_condition_templates,
        schema.local_operator_catalog,
        schema.transform_program_template,
        schema.conclusion_law_template,
    )
    return statement_body


def theorem_statement_digest(schema: FSTheoremSchema) -> str:
    """Derive the statement digest from admitted semantic content."""

    domain_body = analysis_domain_body_v0(
        "analysis.theorem-schema", _theorem_schema_carrier(schema)
    )
    profiled_body = k1.profiled_semantic_body(
        ANALYSIS_TRANSPORT_PROFILE_ID,
        domain_body,
    )
    return hashlib.sha256(k1.encode_datum(profiled_body)).hexdigest()


def _theorem_source_validation_body(schema: FSTheoremSchema) -> object:
    schema_id = fs_theorem_schema_id(schema)
    derived_statement_digest = theorem_statement_digest(schema)
    if (
        type(schema.proof_status) is not TheoremTemplateComponent
        or schema.proof_status != AFK_PROOF_STATUS_COMPONENT
    ):
        raise TheoremError("the theorem source record has the wrong proof status")
    if schema.authority.statement_content_sha256 != derived_statement_digest:
        raise TheoremError(
            "the theorem source record does not match the admitted statement digest "
            f"{derived_statement_digest}"
        )
    return AnalysisTheoremSourceValidationBodyV0(
        schema_id,
        _theorem_authority_body(schema.authority),
        k1.DatumRecord(
            (
                (0, k1.Symbol("ImportedPaperOnly")),
                (1, k1.DatumVariant(0, k1.Unit())),
                (2, k1.Symbol("RetainedTheoremTruthAssumption")),
                (3, False),
            )
        ),
    )


def theorem_source_validation_id(schema: FSTheoremSchema) -> object:
    """Identify validation/support metadata separately from theorem meaning."""

    return _analysis_theorem_source_validation_id(
        "analysis.theorem-source-validation",
        _theorem_source_validation_body(schema),
    )


def _theorem_schema_carrier(schema: FSTheoremSchema) -> AnalysisTheoremSchemaBodyV0:
    body = _global_schema_body(schema)
    if type(body) is not k1.DatumRecord or tuple(
        ordinal for ordinal, _ in body.fields
    ) != tuple(range(11)):
        raise TheoremError("AFK theorem schema is not the exact 11-field body")
    return AnalysisTheoremSchemaBodyV0(*(value for _, value in body.fields))


def fs_theorem_schema_id(schema: FSTheoremSchema) -> object:
    return _analysis_transport_id(
        "analysis.theorem-schema",
        _theorem_schema_carrier(schema),
    )


def afk_v2_theorem_schema() -> FSTheoremSchema:
    return _AFK_GLOBAL_THEOREM_SCHEMA


_AFK_GLOBAL_THEOREM_SCHEMA = _expected_global_schema()
AFK_V2_THM4_CLASSICAL_ROM = fs_theorem_schema_id(_AFK_GLOBAL_THEOREM_SCHEMA)


def _require_selected_theorem_source_validation(
    schema: FSTheoremSchema,
) -> object:
    validation_id = theorem_source_validation_id(schema)
    if (
        fs_theorem_schema_id(schema) != AFK_V2_THM4_CLASSICAL_ROM
        or theorem_statement_digest(schema) != AFK_SELECTED_STATEMENT_CONTENT_SHA256
        or schema.authority != AFK_SELECTED_AUTHORITY
        or schema.authority.statement_content_sha256 != theorem_statement_digest(schema)
        or schema.proof_status != AFK_PROOF_STATUS_COMPONENT
    ):
        raise TheoremError(
            "theorem truth needs the exact selected source validation record"
        )
    return validation_id


AFK_V2_THM4_SOURCE_VALIDATION = _require_selected_theorem_source_validation(
    _AFK_GLOBAL_THEOREM_SCHEMA
)


def theorem_truth_question_body(schema: FSTheoremSchema) -> object:
    schema_id = fs_theorem_schema_id(schema)
    family_coordinate = _family_declaration_ref(
        ANALYSIS_TRANSPORT_PROFILE,
        "theorem-truth",
        owner_profile=ANALYSIS_TRANSPORT_PROFILE,
    )
    return AnalysisQuestionBodyV0(
        family_coordinate,
        (schema_id,),
        _source_free_question_context(ANALYSIS_TRANSPORT_PROFILE),
        k1.DatumRecord(((0, k1.Symbol("exact-selected-theorem-truth-question")),)),
    )


def theorem_truth_goal_id(schema: FSTheoremSchema) -> object:
    question_id = _analysis_transport_id(
        "analysis.question",
        theorem_truth_question_body(schema),
    )
    return _analysis_transport_id(
        "analysis.goal",
        AnalysisGoalBodyV0(question_id),
    )


def theorem_truth_proposition_id(schema: FSTheoremSchema) -> object:
    return _analysis_transport_id(
        "analysis.proposition",
        AnalysisPropositionBodyV0(
            theorem_truth_goal_id(schema),
            analysis_hypothesis_context_id((), transport=True),
        ),
    )


# The separately supplied theorem-truth premise is the exact semantic goal,
# not a second fixture-shaped hypothesis that merely mentions that goal.
ASSUMED_AFK_V2_THM4 = theorem_truth_goal_id(_AFK_GLOBAL_THEOREM_SCHEMA)


# ---------------------------------------------------------------------------
# Abstract family applicability: no native protocol or n0 coordinates
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class FamilyROIndexDomain:
    carrier: str
    length_bound: str
    length_bound_coefficients_low_to_high: tuple[int, ...]
    equality_law: str
    encoder_law: str
    table_law: str
    efficient_operations: tuple[str, ...]


def _family_ro_index_domain_body(profile: FamilyROIndexDomain) -> object:
    if (
        type(profile) is not FamilyROIndexDomain
        or profile.carrier != "finite-bitstrings"
        or profile.length_bound != "0<=bit-length<=u(n)"
        or type(profile.length_bound_coefficients_low_to_high) is not tuple
        or not profile.length_bound_coefficients_low_to_high
        or any(
            type(item) is not int or item < 0
            for item in profile.length_bound_coefficients_low_to_high
        )
        or not any(profile.length_bound_coefficients_low_to_high)
        or profile.equality_law != "bitstring-equality"
        or profile.encoder_law != "injective-prefix-free-family-index-encoder"
        or profile.table_law != "finite-lazy-function-table-at-each-n"
        or profile.efficient_operations != ("encode", "equality", "lookup", "sample")
    ):
        raise TheoremError(
            "AFK family needs a finite bounded-bitstring RO index and efficient operations"
        )
    return k1.DatumRecord(
        (
            (0, k1.Symbol(profile.carrier)),
            (1, k1.Symbol(profile.length_bound)),
            (
                2,
                k1.DatumSeq(
                    tuple(
                        k1.Nat(item)
                        for item in profile.length_bound_coefficients_low_to_high
                    )
                ),
            ),
            (3, k1.Symbol(profile.equality_law)),
            (4, k1.Symbol(profile.encoder_law)),
            (5, k1.Symbol(profile.table_law)),
            (6, _symbol_seq(profile.efficient_operations)),
        )
    )


def family_ro_index_bound_at(family: "AFKAsymptoticFamily", logical_index: int) -> int:
    if type(logical_index) is not int or logical_index < 1:
        raise TheoremError("family RO-index bound needs one positive logical index")
    family_definition_id(family)
    coefficients = family.ro_index_domain.length_bound_coefficients_low_to_high
    result = sum(
        coefficient * (logical_index**degree)
        for degree, coefficient in enumerate(coefficients)
    )
    if result <= 0:
        raise TheoremError("family RO-index bound must evaluate positively")
    return result


@dataclass(frozen=True)
class AFKAsymptoticFamily:
    label: str
    parameter_binder: str
    statement_length_unit: str
    extraction_arity: int
    challenge_cardinality: int
    challenge_cardinality_law: str
    projection_law: str
    relation_law: str
    ro_index_domain: FamilyROIndexDomain
    _issuer: object


_FAMILY_ISSUER = object()


def native_raw_query_index_bit_bound() -> int:
    """Bound raw canonical-datum bytes, not a nested ``BytesValue`` payload."""

    return 8 * k1.MAX_CANONICAL_BYTES


def form_afk_asymptotic_family(
    label: str,
    *,
    challenge_cardinality: int = 8,
) -> AFKAsymptoticFamily:
    family = AFKAsymptoticFamily(
        label,
        "n:LogicalNat",
        "octet",
        2,
        challenge_cardinality,
        "one-fixed-N-for-all-logical-n",
        "one-three-move-family-with-fresh-and-fs-interpretations",
        "uniform-relation-R_n-with-witness-membership",
        FamilyROIndexDomain(
            "finite-bitstrings",
            "0<=bit-length<=u(n)",
            (native_raw_query_index_bit_bound(),),
            "bitstring-equality",
            "injective-prefix-free-family-index-encoder",
            "finite-lazy-function-table-at-each-n",
            ("encode", "equality", "lookup", "sample"),
        ),
        _FAMILY_ISSUER,
    )
    family_definition_id(family)
    return family


def _family_body(family: AFKAsymptoticFamily) -> object:
    if (
        type(family) is not AFKAsymptoticFamily
        or family._issuer is not _FAMILY_ISSUER
        or family.parameter_binder != "n:LogicalNat"
        or family.statement_length_unit != "octet"
        or family.extraction_arity != 2
        or type(family.challenge_cardinality) is not int
        or family.challenge_cardinality < 2
        or family.challenge_cardinality_law != "one-fixed-N-for-all-logical-n"
        or family.projection_law
        != "one-three-move-family-with-fresh-and-fs-interpretations"
        or family.relation_law != "uniform-relation-R_n-with-witness-membership"
    ):
        raise TheoremError(
            "AFK family must keep k=2 and one challenge cardinality fixed across n"
        )
    return k1.DatumRecord(
        (
            (0, k1.Symbol(_ascii(family.label, "family label"))),
            (1, k1.Symbol(family.parameter_binder)),
            (2, k1.Symbol(family.statement_length_unit)),
            (3, k1.Nat(family.extraction_arity)),
            (4, k1.Nat(family.challenge_cardinality)),
            (5, k1.Symbol(family.challenge_cardinality_law)),
            (6, k1.Symbol(family.projection_law)),
            (7, k1.Symbol(family.relation_law)),
            (8, _family_ro_index_domain_body(family.ro_index_domain)),
        )
    )


def _form_family_definition_id(family: AFKAsymptoticFamily) -> object:
    family_language = analysis_profile_declaration_ref(
        ANALYSIS_TRANSPORT_PROFILE,
        ANALYSIS_TRANSPORT_PROFILE,
        "analysis.asymptotic-family-language",
        "afk-schnorr-family-v0",
    )
    return _analysis_transport_id(
        "analysis.asymptotic-protocol-family",
        AnalysisAsymptoticProtocolFamilyBodyV0(
            family_language,
            _family_body(family),
        ),
    )


def family_definition_id(family: AFKAsymptoticFamily) -> object:
    """Share the family identity only within one live derivation scope."""

    return _family_static_value(
        "definition-id",
        family,
        form=lambda: _form_family_definition_id(family),
    )


SELECTED_AFK_FAMILY = form_afk_asymptotic_family(
    "selected-prime-order-schnorr-family-N8"
)


def _form_family_ro_index_domain_id(family: AFKAsymptoticFamily) -> object:
    family_id = family_definition_id(family)
    return _legacy_component_id(
        "analysis.family-ro-index-domain",
        k1.DatumRecord(
            (
                (
                    0,
                    _id_datum(family_id, "analysis.asymptotic-protocol-family"),
                ),
                (1, _family_ro_index_domain_body(family.ro_index_domain)),
            )
        ),
    )


def family_ro_index_domain_id(family: AFKAsymptoticFamily) -> object:
    return _family_static_value(
        "ro-index-domain-id",
        family,
        form=lambda: _form_family_ro_index_domain_id(family),
    )


def _form_family_query_dimension_id(family: AFKAsymptoticFamily) -> object:
    return _legacy_component_id(
        "analysis.resource-dimension",
        k1.DatumRecord(
            (
                (
                    0,
                    _id_datum(
                        family_definition_id(family),
                        "analysis.asymptotic-protocol-family",
                    ),
                ),
                (1, k1.Symbol("random-oracle-query")),
                (2, k1.Symbol("hard-count-every-call-including-repeat-and-off-image")),
            )
        ),
    )


def family_query_dimension_id(family: AFKAsymptoticFamily) -> object:
    return _family_static_value(
        "query-dimension-id",
        family,
        form=lambda: _form_family_query_dimension_id(family),
    )


def _form_family_invocation_dimension_id(family: AFKAsymptoticFamily) -> object:
    return _legacy_component_id(
        "analysis.resource-dimension",
        k1.DatumRecord(
            (
                (
                    0,
                    _id_datum(
                        family_definition_id(family),
                        "analysis.asymptotic-protocol-family",
                    ),
                ),
                (1, k1.Symbol("adversary-running-invocation")),
                (2, k1.Symbol("expected-count")),
            )
        ),
    )


def family_invocation_dimension_id(family: AFKAsymptoticFamily) -> object:
    return _family_static_value(
        "invocation-dimension-id",
        family,
        form=lambda: _form_family_invocation_dimension_id(family),
    )


def _family_coordinate_id(role: str) -> object:
    if role not in (
        "source-two-special-soundness",
        "target-adaptive-knowledge-q-lt-N",
    ):
        raise TheoremError("unsupported AFK family goal role")
    if role == "source-two-special-soundness":
        return _family_declaration_ref(
            ANALYSIS_TRANSPORT_PROFILE,
            "asymptotic-k-out-of-n-special-soundness",
            owner_profile=ANALYSIS_TRANSPORT_PROFILE,
        )
    return _family_declaration_ref(
        ANALYSIS_TRANSPORT_PROFILE,
        "adaptive-knowledge-soundness-q-lt-n",
        owner_profile=ANALYSIS_TRANSPORT_PROFILE,
    )


def _form_family_question_id(family: AFKAsymptoticFamily, role: str) -> object:
    family_id = family_definition_id(family)
    family_coordinate = _family_coordinate_id(role)
    axis = (
        "fresh-source"
        if role == "source-two-special-soundness"
        else "adaptive-fs-target"
    )
    payload_entries: list[tuple[int, object]] = [
        (0, k1.Symbol(role)),
        (1, k1.Nat(family.challenge_cardinality)),
        (2, k1.Symbol("forall-logical-n")),
        (3, k1.Symbol("relation-bound")),
    ]
    if role == "target-adaptive-knowledge-q-lt-N":
        payload_entries.append(
            (
                4,
                k1.DatumSeq(
                    tuple(
                        _id_datum(
                            binding.formula_id,
                            "analysis.quantitative-formula",
                        )
                        for binding in family_operator_bindings(family)
                    )
                ),
            )
        )
    identity = _analysis_transport_id
    context = k1.DatumVariant(
        2,
        k1.DatumRecord(
            (
                (0, _id_datum(family_id, "analysis.asymptotic-protocol-family")),
                (
                    1,
                    k1.DatumSeq(
                        (
                            _id_datum(
                                family_manifest_schema_id(family, axis),
                                "analysis.family-read-manifest-schema",
                            ),
                        )
                    ),
                ),
                (
                    2,
                    k1.DatumSeq(
                        (
                            _id_datum(
                                family_experiment_profile_id(family, axis),
                                "analysis.experiment-profile",
                            ),
                        )
                    ),
                ),
            )
        ),
    )
    return identity(
        "analysis.question",
        AnalysisQuestionBodyV0(
            family_coordinate,
            (family_id,),
            context,
            k1.DatumRecord(tuple(payload_entries)),
        ),
    )


def family_question_id(family: AFKAsymptoticFamily, role: str) -> object:
    return _family_static_value(
        "question-id",
        family,
        role,
        form=lambda: _form_family_question_id(family, role),
    )


def _form_family_goal_id(family: AFKAsymptoticFamily, role: str) -> object:
    return _analysis_transport_id(
        "analysis.goal",
        AnalysisGoalBodyV0(family_question_id(family, role)),
    )


def family_goal_id(family: AFKAsymptoticFamily, role: str) -> object:
    return _family_static_value(
        "goal-id",
        family,
        role,
        form=lambda: _form_family_goal_id(family, role),
    )


def _form_family_experiment_profile_id(
    family: AFKAsymptoticFamily, axis: str
) -> object:
    if axis not in ("fresh-source", "adaptive-fs-target"):
        raise TheoremError("unsupported family experiment axis")
    family_id = family_definition_id(family)
    source_profile = family_member_source_profile_id(family, axis)
    strategy_id = (
        SPECIAL_SOUNDNESS_PAIR_INTERFACE
        if axis == "fresh-source"
        else ADAPTIVE_KNOWLEDGE_INTERFACE
    )
    return _analysis_transport_id(
        "analysis.experiment-profile",
        AnalysisExperimentProfileBodyV0(
            _id_datum(family_id, "analysis.asymptotic-protocol-family"),
            _id_datum(source_profile, "analysis.source-profile"),
            k1.DatumSeq(
                (
                    k1.DatumRecord(
                        (
                            (0, k1.Nat(0)),
                            (1, k1.Symbol("forall-logical-natural")),
                            (2, k1.Symbol("positive-logical-index")),
                        )
                    ),
                )
            ),
            k1.DatumSeq((_id_datum(strategy_id, "analysis.strategy-class"),)),
            k1.DatumRecord(
                (
                    (0, k1.Symbol(axis)),
                    (1, k1.Symbol("family-member-public-setup")),
                )
            ),
            k1.DatumRecord(
                (
                    (
                        0,
                        k1.Symbol(
                            "verifier-public-coin"
                            if axis == "fresh-source"
                            else "persistent-classical-random-oracle"
                        ),
                    ),
                    (1, k1.Symbol("family-indexed-independent-randomness")),
                )
            ),
            k1.DatumRecord(
                (
                    (
                        0,
                        k1.Symbol(
                            "public-coin" if axis == "fresh-source" else "classical-rom"
                        ),
                    ),
                    (1, _family_ro_index_domain_body(family.ro_index_domain)),
                )
            ),
            k1.Symbol("single-session"),
            k1.Symbol("family-indexed-generated-execution-relation"),
            k1.Symbol(
                "accepted-transcript-family-event"
                if axis == "fresh-source"
                else "adaptive-knowledge-success-family-event"
            ),
            k1.Symbol("explicit-abort-failure-and-noncompletion-law"),
            k1.Symbol("family-uniform-termination-contract"),
            k1.DatumRecord(
                (
                    (0, k1.Symbol("random-oracle-query")),
                    (1, k1.Symbol("adversary-running-invocation")),
                )
            ),
            k1.Symbol("family-property-outcome"),
        ),
    )


def family_experiment_profile_id(family: AFKAsymptoticFamily, axis: str) -> object:
    if axis not in ("fresh-source", "adaptive-fs-target"):
        raise TheoremError("unsupported family experiment axis")
    return _family_static_value(
        "experiment-profile-id",
        family,
        axis,
        form=lambda: _form_family_experiment_profile_id(family, axis),
    )


def _form_family_member_source_profile_id(
    family: AFKAsymptoticFamily, axis: str
) -> object:
    if axis not in ("fresh-source", "adaptive-fs-target"):
        raise TheoremError("unsupported family source-profile axis")
    family_id = family_definition_id(family)
    family_tag = analysis_profile_declaration_ref(
        ANALYSIS_TRANSPORT_PROFILE,
        ANALYSIS_TRANSPORT_PROFILE,
        "analysis.source-family",
        (
            "afk-fresh-family-sources"
            if axis == "fresh-source"
            else "afk-fs-target-family-sources"
        ),
    )
    return _analysis_transport_id(
        "analysis.source-profile",
        AnalysisSourceProfileBodyV0(
            family_tag,
            k1.DatumSeq(
                (
                    k1.DatumRecord(
                        (
                            (0, k1.Nat(0)),
                            (1, k1.Symbol(axis)),
                            (
                                2,
                                _id_datum(
                                    family_id,
                                    "analysis.asymptotic-protocol-family",
                                ),
                            ),
                            (
                                3,
                                _read_purpose_variant(
                                    AnalysisReadPurpose.SEMANTIC_MEANING
                                ),
                            ),
                        )
                    ),
                    k1.DatumRecord(
                        (
                            (0, k1.Nat(1)),
                            (1, k1.Symbol("family-ro-index-domain")),
                            (2, _family_ro_index_domain_body(family.ro_index_domain)),
                            (
                                3,
                                _read_purpose_variant(
                                    AnalysisReadPurpose.SEMANTIC_MEANING
                                ),
                            ),
                        )
                    ),
                )
            ),
            k1.DatumSeq(
                (
                    k1.DatumRecord(((0, k1.Nat(0)), (1, k1.Nat(2)))),
                    k1.DatumRecord(((0, k1.Nat(1)), (1, k1.Nat(2)))),
                )
            ),
            _family_source_profile_adequacy_evaluator_id(axis),
        ),
    )


def family_member_source_profile_id(family: AFKAsymptoticFamily, axis: str) -> object:
    if axis not in ("fresh-source", "adaptive-fs-target"):
        raise TheoremError("unsupported family source-profile axis")
    return _family_static_value(
        "member-source-profile-id",
        family,
        axis,
        form=lambda: _form_family_member_source_profile_id(family, axis),
    )


def _form_family_manifest_schema_id(family: AFKAsymptoticFamily, axis: str) -> object:
    if axis not in ("fresh-source", "adaptive-fs-target"):
        raise TheoremError("unsupported family manifest axis")
    return _analysis_transport_id(
        "analysis.family-read-manifest-schema",
        AnalysisFamilyReadManifestSchemaBodyV0(
            family_definition_id(family),
            family_member_source_profile_id(family, axis),
        ),
    )


def family_manifest_schema_id(family: AFKAsymptoticFamily, axis: str) -> object:
    if axis not in ("fresh-source", "adaptive-fs-target"):
        raise TheoremError("unsupported family manifest axis")
    return _family_static_value(
        "manifest-schema-id",
        family,
        axis,
        form=lambda: _form_family_manifest_schema_id(family, axis),
    )


@dataclass(frozen=True)
class AFKFamilyOperatorBinding:
    local_ordinal: int
    source_operator: LocalOperatorTemplate
    challenge_cardinality: int
    formula_id: object
    parameter_sorts: tuple[str, ...]
    result_sort: str
    instantiated_ast: str
    exact_substitution: tuple[str, ...]


LocalOperatorAst = tuple[object, ...]


def _parse_local_operator_template(
    operator: LocalOperatorTemplate,
    challenge_cardinality: int,
    *,
    _active_ordinals: frozenset[int] = frozenset(),
) -> LocalOperatorAst:
    """Parse the authenticated, deliberately tiny AFK local-expression grammar."""

    if operator.ordinal in _active_ordinals:
        raise TheoremError("AFK local operator catalog contains a cycle")
    active_ordinals = _active_ordinals | {operator.ordinal}
    text = operator.template_ast
    bounded = re.fullmatch(
        r"bounded-ratio\(\(([A-Za-z_][A-Za-z0-9_]*)\+(\d+)\),N\);"
        r"domain=0<=\1<N",
        text,
    )
    if bounded is not None:
        offset = int(bounded.group(2))
        if offset > MAX_EXPRESSION_NODES:
            raise TheoremError("AFK local operator literal exceeds the finite bound")
        return (
            "bounded-ratio",
            bounded.group(1),
            offset,
            challenge_cardinality,
            challenge_cardinality,
        )
    divided = re.fullmatch(r"divide\(\(epsilon-operator(\d+)\(Q,N\)\),qKS\(n\)\)", text)
    if divided is not None:
        referenced = int(divided.group(1))
        if referenced not in range(len(AFK_LOCAL_OPERATOR_CATALOG)):
            raise TheoremError("AFK local template references an unknown operator")
        # The selected transform authenticates qKS(n)=1. Canonical reduction
        # therefore removes division by one after expanding the referenced AST.
        return (
            "difference",
            _parse_local_operator_template(
                AFK_LOCAL_OPERATOR_CATALOG[referenced],
                challenge_cardinality,
                _active_ordinals=active_ordinals,
            ),
        )
    scaled = re.fullmatch(
        r"scale\(N/\(N-(\d+)\),\(epsilon-operator(\d+)\(Q,N\)\)\)", text
    )
    if scaled is not None:
        decrement = int(scaled.group(1))
        referenced = int(scaled.group(2))
        if (
            decrement > MAX_EXPRESSION_NODES
            or decrement >= challenge_cardinality
            or referenced not in range(len(AFK_LOCAL_OPERATOR_CATALOG))
        ):
            raise TheoremError("AFK local scaling template is not total")
        return (
            "scale-difference",
            Fraction(
                challenge_cardinality,
                challenge_cardinality - decrement,
            ),
            _parse_local_operator_template(
                AFK_LOCAL_OPERATOR_CATALOG[referenced],
                challenge_cardinality,
                _active_ordinals=active_ordinals,
            ),
        )
    expected = re.fullmatch(r"expected-count\(([A-Za-z_][A-Za-z0-9_]*)\+(\d+)\)", text)
    if expected is not None:
        offset = int(expected.group(2))
        if offset > MAX_EXPRESSION_NODES:
            raise TheoremError("AFK local operator literal exceeds the finite bound")
        return ("expected-count", expected.group(1), offset)
    raise TheoremError("AFK local operator template is outside the closed grammar")


def _canonical_local_operator_ast(expression: LocalOperatorAst) -> str:
    tag = expression[0]
    if tag == "bounded-ratio":
        _, variable, offset, denominator, domain_bound = expression
        return (
            f"bounded-ratio(({variable}+{offset}),{denominator});"
            f"domain=0<={variable}<{domain_bound}"
        )
    if tag == "difference":
        return f"(epsilon-{_canonical_local_operator_ast(expression[1])})"
    if tag == "scale-difference":
        factor = expression[1]
        return (
            f"scale({factor.numerator}/{factor.denominator},"
            f"(epsilon-{_canonical_local_operator_ast(expression[2])}))"
        )
    if tag == "expected-count":
        return f"expected-count({expression[1]}+{expression[2]})"
    raise TheoremError("AFK local operator AST has an unknown constructor")


def _instantiate_local_operator_ast(
    operator: LocalOperatorTemplate, challenge_cardinality: int
) -> str:
    """Parse, instantiate, and canonically reduce one authenticated local AST."""

    if (
        type(operator) is not LocalOperatorTemplate
        or operator.ordinal not in range(len(AFK_LOCAL_OPERATOR_CATALOG))
        or operator != AFK_LOCAL_OPERATOR_CATALOG[operator.ordinal]
        or type(challenge_cardinality) is not int
        or challenge_cardinality < 2
    ):
        raise TheoremError("AFK local operator cannot be instantiated")
    return _canonical_local_operator_ast(
        _parse_local_operator_template(operator, challenge_cardinality)
    )


def _family_formula_body(
    family: AFKAsymptoticFamily, operator: LocalOperatorTemplate
) -> AnalysisQuantitativeFormulaBodyV0:
    family_id = family_definition_id(family)
    q_dimension = family_query_dimension_id(family)
    invocation_dimension = family_invocation_dimension_id(family)
    if operator.ordinal not in range(len(AFK_FAMILY_OPERATOR_SIGNATURES)):
        raise TheoremError("family operator ordinal is outside the AFK catalog")
    parameters, result_sort = AFK_FAMILY_OPERATOR_SIGNATURES[operator.ordinal]
    expression = _instantiate_local_operator_ast(operator, family.challenge_cardinality)
    return AnalysisQuantitativeFormulaBodyV0(
        k1.Symbol(result_sort),
        k1.DatumSeq(
            tuple(
                k1.DatumRecord(((0, k1.Nat(ordinal)), (1, k1.Symbol(sort))))
                for ordinal, sort in enumerate(parameters)
            )
        ),
        k1.DatumRecord(
            (
                (0, _id_datum(family_id, "analysis.asymptotic-protocol-family")),
                (1, k1.Nat(family.challenge_cardinality)),
                (2, k1.Symbol("family-indexed-parameters-only")),
            )
        ),
        k1.DatumRecord(
            (
                (0, k1.Nat(operator.ordinal)),
                (1, k1.Symbol(expression)),
                (
                    2,
                    _embedded_component_datum(
                        q_dimension,
                        "analysis.resource-dimension",
                    ),
                ),
                (
                    3,
                    _embedded_component_datum(
                        invocation_dimension,
                        "analysis.resource-dimension",
                    ),
                ),
                (4, _local_operator_body(operator)),
            )
        ),
    )


def _form_family_operator_bindings(
    family: AFKAsymptoticFamily,
) -> tuple[AFKFamilyOperatorBinding, ...]:
    bindings = []
    for operator in AFK_LOCAL_OPERATOR_CATALOG:
        body = _family_formula_body(family, operator)
        formula_id = _analysis_transport_id("analysis.quantitative-formula", body)
        parameters, result_sort = AFK_FAMILY_OPERATOR_SIGNATURES[operator.ordinal]
        bindings.append(
            AFKFamilyOperatorBinding(
                operator.ordinal,
                operator,
                family.challenge_cardinality,
                formula_id,
                parameters,
                result_sort,
                _instantiate_local_operator_ast(operator, family.challenge_cardinality),
                (
                    "local-family-0=" + family.label,
                    "k=2",
                    f"N={family.challenge_cardinality}-constant-across-n",
                    "qKS=logical-nat-constant-one",
                ),
            )
        )
    return tuple(bindings)


def family_operator_bindings(
    family: AFKAsymptoticFamily,
) -> tuple[AFKFamilyOperatorBinding, ...]:
    return _family_static_value(
        "operator-bindings",
        family,
        form=lambda: _form_family_operator_bindings(family),
    )


def family_operator_binding_id(binding: AFKFamilyOperatorBinding) -> object:
    if type(binding) is not AFKFamilyOperatorBinding:
        raise TheoremError("family operator binding has the wrong exact shape")
    expected_parameters, expected_result = (
        AFK_FAMILY_OPERATOR_SIGNATURES[binding.local_ordinal]
        if type(binding.local_ordinal) is int and binding.local_ordinal in range(4)
        else ((), "")
    )
    if (
        binding.local_ordinal not in range(4)
        or binding.source_operator != AFK_LOCAL_OPERATOR_CATALOG[binding.local_ordinal]
        or type(binding.challenge_cardinality) is not int
        or binding.challenge_cardinality < 2
        or binding.instantiated_ast
        != _instantiate_local_operator_ast(
            binding.source_operator,
            binding.challenge_cardinality,
        )
        or binding.parameter_sorts != expected_parameters
        or binding.result_sort != expected_result
    ):
        raise TheoremError("family operator binding has the wrong exact shape")
    return _legacy_component_id(
        "analysis.theorem-operator-binding",
        k1.DatumRecord(
            (
                (0, k1.Nat(binding.local_ordinal)),
                (1, k1.Nat(binding.challenge_cardinality)),
                (
                    2,
                    _id_datum(binding.formula_id, "analysis.quantitative-formula"),
                ),
                (3, _symbol_seq(binding.parameter_sorts)),
                (4, k1.Symbol(binding.result_sort)),
                (5, k1.Symbol(binding.instantiated_ast)),
                (6, _symbol_seq(binding.exact_substitution)),
                (7, _local_operator_body(binding.source_operator)),
            )
        ),
    )


@dataclass(frozen=True)
class AFKFamilyParameterSubstitution:
    extraction_arity: int
    positive_polynomial_id: object
    positive_polynomial_domain_id: object
    challenge_cardinality: int
    challenge_cardinality_law: str
    query_dimension_id: object
    adversary_invocation_dimension_id: object
    ro_index_domain_id: object


def _parameter_substitution_body(
    substitution: AFKFamilyParameterSubstitution,
) -> object:
    if (
        type(substitution) is not AFKFamilyParameterSubstitution
        or substitution.extraction_arity != 2
        or type(substitution.challenge_cardinality) is not int
        or substitution.challenge_cardinality < 2
        or substitution.challenge_cardinality_law != "one-fixed-N-for-all-logical-n"
    ):
        raise TheoremError("AFK family parameter substitution is malformed")
    return k1.DatumRecord(
        (
            (0, k1.Nat(substitution.extraction_arity)),
            (
                1,
                _id_datum(
                    substitution.positive_polynomial_id,
                    "analysis.positive-polynomial",
                ),
            ),
            (
                2,
                _id_datum(
                    substitution.positive_polynomial_domain_id,
                    "analysis.positive-polynomial-profile",
                ),
            ),
            (3, k1.Nat(substitution.challenge_cardinality)),
            (4, k1.Symbol(substitution.challenge_cardinality_law)),
            (
                5,
                _id_datum(
                    substitution.query_dimension_id,
                    "analysis.resource-dimension",
                ),
            ),
            (
                6,
                _id_datum(
                    substitution.adversary_invocation_dimension_id,
                    "analysis.resource-dimension",
                ),
            ),
            (
                7,
                _id_datum(
                    substitution.ro_index_domain_id,
                    "analysis.family-ro-index-domain",
                ),
            ),
        )
    )


def _form_family_applicability_premise_ids(
    family: AFKAsymptoticFamily,
) -> tuple[object, ...]:
    family_id = family_definition_id(family)
    theorem_schema_id = fs_theorem_schema_id(afk_v2_theorem_schema())
    families = (
        "total-single-valued-family-denotation",
        "family-projection-coherence",
        "fixed-family-challenge-cardinality",
        "fresh-uniform-independent-public-coin",
        "exact-classical-random-oracle-process",
        "finite-bounded-random-oracle-index-and-efficient-operations",
        "fixed-public-setup-independence",
        "total-uniform-challenge-sampler-adequacy",
        "afk-experiment-observation-correspondence",
    )
    return canonical_hypotheses(
        _exact_premise_goal_id(
            family_label,
            (theorem_schema_id, family_id),
            _family_semantic_context(
                family,
                axes=("fresh-source", "adaptive-fs-target"),
            ),
            k1.DatumRecord(
                (
                    (
                        0,
                        _id_datum(
                            family_id,
                            "analysis.asymptotic-protocol-family",
                        ),
                    ),
                    (1, k1.Nat(ordinal)),
                )
            ),
            selected_profile=ANALYSIS_TRANSPORT_PROFILE,
        )
        for ordinal, family_label in enumerate(families)
    )


def family_applicability_premise_ids(
    family: AFKAsymptoticFamily,
) -> tuple[object, ...]:
    """Share the exact premise set only within one live derivation scope."""

    with _family_derivation_scope():
        return _family_derivation_value(
            (
                "family-applicability-premises",
                ANALYSIS_TRANSPORT_PROFILE_ID,
                family,
            ),
            lambda: _form_family_applicability_premise_ids(family),
        )


def family_source_property_proposition_id(
    family: AFKAsymptoticFamily,
    hypotheses: Iterable[object] = (),
) -> object:
    return _analysis_transport_id(
        "analysis.proposition",
        AnalysisPropositionBodyV0(
            family_goal_id(family, "source-two-special-soundness"),
            analysis_hypothesis_context_id(hypotheses, transport=True),
        ),
    )


def family_target_property_proposition_id(
    family: AFKAsymptoticFamily,
    hypotheses: Iterable[object] = (),
) -> object:
    return _analysis_transport_id(
        "analysis.proposition",
        AnalysisPropositionBodyV0(
            family_goal_id(family, "target-adaptive-knowledge-q-lt-N"),
            analysis_hypothesis_context_id(hypotheses, transport=True),
        ),
    )


@dataclass(frozen=True)
class AFKFamilyApplicabilityInput:
    theorem_schema_id: object
    family_definition_id: object
    source_property_goal_id: object
    target_property_goal_id: object
    source_experiment_profile_id: object
    target_experiment_profile_id: object
    family_read_manifest_schema_ids: tuple[object, object]
    applicability_premise_ids: tuple[object, ...]
    parameter_substitution: AFKFamilyParameterSubstitution
    operator_bindings: tuple[AFKFamilyOperatorBinding, ...]


def _form_family_applicability_input(
    schema: FSTheoremSchema,
    family: AFKAsymptoticFamily,
) -> AFKFamilyApplicabilityInput:
    schema_id = fs_theorem_schema_id(schema)
    family_id = family_definition_id(family)
    return AFKFamilyApplicabilityInput(
        schema_id,
        family_id,
        family_goal_id(family, "source-two-special-soundness"),
        family_goal_id(family, "target-adaptive-knowledge-q-lt-N"),
        family_experiment_profile_id(family, "fresh-source"),
        family_experiment_profile_id(family, "adaptive-fs-target"),
        (
            family_manifest_schema_id(family, "fresh-source"),
            family_manifest_schema_id(family, "adaptive-fs-target"),
        ),
        family_applicability_premise_ids(family),
        AFKFamilyParameterSubstitution(
            2,
            AFK_POSITIVE_POLYNOMIAL_Q_ONE,
            AFK_POSITIVE_POLYNOMIAL_DOMAIN_ID,
            family.challenge_cardinality,
            family.challenge_cardinality_law,
            family_query_dimension_id(family),
            family_invocation_dimension_id(family),
            family_ro_index_domain_id(family),
        ),
        family_operator_bindings(family),
    )


def derive_family_applicability_input(
    schema: FSTheoremSchema,
    family: AFKAsymptoticFamily,
) -> AFKFamilyApplicabilityInput:
    """Share one immutable input only within a live derivation scope."""

    with _family_derivation_scope():
        return _family_derivation_value(
            (
                "family-applicability-input",
                ANALYSIS_TRANSPORT_PROFILE_ID,
                schema,
                family,
            ),
            lambda: _form_family_applicability_input(schema, family),
        )


def _family_applicability_input_body(
    candidate: AFKFamilyApplicabilityInput,
) -> object:
    if type(candidate) is not AFKFamilyApplicabilityInput:
        raise TheoremError("family applicability input has the wrong shape")
    for binding in candidate.operator_bindings:
        family_operator_binding_id(binding)
    return k1.DatumRecord(
        (
            (
                0,
                _id_datum(candidate.theorem_schema_id, "analysis.theorem-schema"),
            ),
            (
                1,
                _id_datum(
                    candidate.family_definition_id,
                    "analysis.asymptotic-protocol-family",
                ),
            ),
            (2, _id_datum(candidate.source_property_goal_id, "analysis.goal")),
            (3, _id_datum(candidate.target_property_goal_id, "analysis.goal")),
            (
                4,
                _id_datum(
                    candidate.source_experiment_profile_id,
                    "analysis.experiment-profile",
                ),
            ),
            (
                5,
                _id_datum(
                    candidate.target_experiment_profile_id,
                    "analysis.experiment-profile",
                ),
            ),
            (
                6,
                k1.DatumSeq(
                    tuple(
                        _id_datum(item, "analysis.family-read-manifest-schema")
                        for item in candidate.family_read_manifest_schema_ids
                    )
                ),
            ),
            (7, _parameter_substitution_body(candidate.parameter_substitution)),
            (
                8,
                k1.DatumSeq(
                    tuple(
                        _embedded_component_datum(
                            family_operator_binding_id(item),
                            "analysis.theorem-operator-binding",
                        )
                        for item in candidate.operator_bindings
                    )
                ),
            ),
        )
    )


def family_applicability_input_id(
    candidate: AFKFamilyApplicabilityInput,
) -> object:
    return _legacy_component_id(
        "analysis.family-theorem-applicability-input",
        _family_applicability_input_body(candidate),
    )


def family_applicability_question_id(
    family: AFKAsymptoticFamily,
    candidate: AFKFamilyApplicabilityInput,
) -> object:
    family_id = family_definition_id(family)
    candidate_id = family_applicability_input_id(candidate)
    family_coordinate = _family_declaration_ref(
        ANALYSIS_TRANSPORT_PROFILE,
        "theorem-applicability",
        owner_profile=ANALYSIS_TRANSPORT_PROFILE,
    )
    context = k1.DatumVariant(
        2,
        k1.DatumRecord(
            (
                (0, _id_datum(family_id, "analysis.asymptotic-protocol-family")),
                (
                    1,
                    k1.DatumSeq(
                        tuple(
                            _id_datum(item, "analysis.family-read-manifest-schema")
                            for item in candidate.family_read_manifest_schema_ids
                        )
                    ),
                ),
                (
                    2,
                    k1.DatumSeq(
                        (
                            _id_datum(
                                candidate.source_experiment_profile_id,
                                "analysis.experiment-profile",
                            ),
                            _id_datum(
                                candidate.target_experiment_profile_id,
                                "analysis.experiment-profile",
                            ),
                        )
                    ),
                ),
            )
        ),
    )
    return _analysis_transport_id(
        "analysis.question",
        AnalysisQuestionBodyV0(
            family_coordinate,
            (candidate.theorem_schema_id, family_id),
            context,
            k1.DatumRecord(
                (
                    (
                        0,
                        _embedded_component_datum(
                            candidate_id,
                            "analysis.family-theorem-applicability-input",
                        ),
                    ),
                    (1, k1.Symbol("exact-afk-family-applicability")),
                )
            ),
        ),
    )


def family_applicability_goal_id(
    family: AFKAsymptoticFamily,
    candidate: AFKFamilyApplicabilityInput,
) -> object:
    return _analysis_transport_id(
        "analysis.goal",
        AnalysisGoalBodyV0(family_applicability_question_id(family, candidate)),
    )


def family_applicability_proposition_id(
    family: AFKAsymptoticFamily,
    candidate: AFKFamilyApplicabilityInput,
) -> object:
    return _analysis_transport_id(
        "analysis.proposition",
        AnalysisPropositionBodyV0(
            family_applicability_goal_id(family, candidate),
            analysis_hypothesis_context_id(
                candidate.applicability_premise_ids,
                transport=True,
            ),
        ),
    )


@dataclass(frozen=True)
class AFKFamilyApplicabilityPort:
    family: AFKAsymptoticFamily
    applicability_input: AFKFamilyApplicabilityInput
    retained_hypotheses: tuple[object, ...]
    purpose: str
    checked_result: InertCheckedResult
    authority_binding: AnalysisSourceAuthorityContract
    live_capability: InvocationCapability

    @property
    def port_id(self) -> object:
        return self.checked_result.result_id

    @property
    def theorem_schema_id(self) -> object:
        return self.applicability_input.theorem_schema_id

    @property
    def family_definition_id(self) -> object:
        return self.applicability_input.family_definition_id

    @property
    def applicability_input_id(self) -> object:
        return family_applicability_input_id(self.applicability_input)

    @property
    def semantic_basis_id(self) -> object:
        return self.checked_result.semantic_basis_id

    @property
    def support_id(self) -> object:
        return self.checked_result.support_id


_FAMILY_PORT_TOKENS: dict[object, object] = {}


def _k3c_evaluator_owner_id(role: str) -> object:
    return k1.content_id(
        "analysis.analysis-evaluator-owner",
        k1.encode_datum(
            k1.DatumRecord(
                (
                    (0, k1.Symbol("zkc.analysis.reference-evaluator")),
                    (1, k1.Nat(0)),
                    (2, k1.Symbol(_ascii(role, "evaluator owner role"))),
                    (
                        3,
                        _id_datum(
                            _Analysis_REFERENCE_CHECKER_ALGORITHM_ID,
                            "foundation.portable-algorithm",
                        ),
                    ),
                    (
                        4,
                        _id_datum(
                            _Analysis_REFERENCE_CHECKER_EVALUATION_CONTRACT_ID,
                            "foundation.evaluation-contract",
                        ),
                    ),
                )
            )
        ),
        semantic_regime=k1.SEMANTIC_REGIME_ID,
    )


_ANALYSIS_APPLICABILITY_OWNER_ID = _k3c_evaluator_owner_id(
    "family-applicability-checker"
)
_APPLICABILITY_QUALIFICATION_ID = analysis_profile_declaration_ref(
    ANALYSIS_TRANSPORT_PROFILE,
    ANALYSIS_TRANSPORT_PROFILE,
    "analysis.qualification",
    "afk-family-applicability-result",
)


def _family_applicability_semantic_basis_id(
    schema: FSTheoremSchema,
    family: AFKAsymptoticFamily,
    candidate: AFKFamilyApplicabilityInput,
) -> object:
    theorem_schema_id = fs_theorem_schema_id(schema)
    family_id = family_definition_id(family)
    return _analysis_transport_id(
        "analysis.semantic-basis",
        AnalysisSemanticBasisBodyV0(
            _family_declaration_ref(
                ANALYSIS_TRANSPORT_PROFILE,
                "theorem-applicability",
                owner_profile=ANALYSIS_TRANSPORT_PROFILE,
            ),
            family_applicability_question_id(family, candidate),
            _native_rule_source(
                ANALYSIS_TRANSPORT_PROFILE,
                ANALYSIS_TRANSPORT_PROFILE,
                "exact-theorem-applicability-check",
                k1.DatumRecord(
                    (
                        (0, _id_datum(theorem_schema_id, "analysis.theorem-schema")),
                        (
                            1,
                            _id_datum(
                                family_id,
                                "analysis.asymptotic-protocol-family",
                            ),
                        ),
                        (
                            2,
                            _embedded_component_datum(
                                family_applicability_input_id(candidate),
                                "analysis.family-theorem-applicability-input",
                            ),
                        ),
                    )
                ),
            ),
            _hypothesis_node_requirements(
                candidate.applicability_premise_ids,
                transport=True,
            ),
            complete_read_purpose_requirements(
                family_manifest_schema_ids=(candidate.family_read_manifest_schema_ids),
            ),
            _conclusion_schema_ref(
                ANALYSIS_TRANSPORT_PROFILE,
                ANALYSIS_TRANSPORT_PROFILE,
                "family-applicability-conclusion-v0",
            ),
            k1.DatumRecord(
                (
                    (0, k1.Symbol("bind-global-local-roles-to-one-abstract-family")),
                    (
                        1,
                        k1.DatumSeq(
                            tuple(
                                _embedded_component_datum(
                                    family_operator_binding_id(binding),
                                    "analysis.theorem-operator-binding",
                                )
                                for binding in candidate.operator_bindings
                            )
                        ),
                    ),
                )
            ),
        ),
    )


def _family_applicability_support_id(
    semantic_basis_id: object,
    proposition_id: object,
    hypotheses: tuple[object, ...],
) -> object:
    return _analysis_support_instantiation_id(
        profile=ANALYSIS_TRANSPORT_PROFILE,
        semantic_basis_id=semantic_basis_id,
        proposition_id=proposition_id,
        assumed_goals=hypotheses,
    )


def _family_applicability_result_id(
    schema_id: object,
    family_id: object,
    candidate_id: object,
    proposition_id: object,
    semantic_basis_id: object,
    support_id: object,
    validation_basis_id: object,
    operation_policy_id: object,
    hypotheses: tuple[object, ...],
) -> object:
    return _analysis_judgment_record_id(
        profile=ANALYSIS_TRANSPORT_PROFILE,
        proposition_id=proposition_id,
        exact_family_conclusion=k1.DatumRecord(
            (
                (0, _id_datum(schema_id, "analysis.theorem-schema")),
                (1, _id_datum(family_id, "analysis.asymptotic-protocol-family")),
                (
                    2,
                    _embedded_component_datum(
                        candidate_id,
                        "analysis.family-theorem-applicability-input",
                    ),
                ),
                (3, k1.Symbol("affirmative-exact-family-applicability")),
            )
        ),
        inherited_hypothesis_context_id=analysis_hypothesis_context_id(
            hypotheses, transport=True
        ),
        typed_quantitative_result=k1.DatumVariant(0, k1.UNIT),
        semantic_basis_id=semantic_basis_id,
        support_id=support_id,
        validation_basis_id=validation_basis_id,
        qualification=_APPLICABILITY_QUALIFICATION_ID,
        operation_policy_id=operation_policy_id,
    )


def _family_applicability_components(
    schema: FSTheoremSchema,
    family: AFKAsymptoticFamily,
    candidate: AFKFamilyApplicabilityInput,
    hypotheses: tuple[object, ...],
) -> tuple[InertCheckedResult, AnalysisSourceAuthorityContract]:
    schema_id = fs_theorem_schema_id(schema)
    family_id = family_definition_id(family)
    basis_id = _family_applicability_semantic_basis_id(schema, family, candidate)
    candidate_id = family_applicability_input_id(candidate)
    proposition_id = family_applicability_proposition_id(family, candidate)
    support_id = _family_applicability_support_id(basis_id, proposition_id, hypotheses)
    validation_basis_id = analysis_validation_basis_id(
        (), profile=ANALYSIS_TRANSPORT_PROFILE
    )
    operation_policy_id = _analysis_operation_policy_id(
        proposition_id,
        (
            (
                "afk-family-property-transport",
                ("exact-family-applicability",),
            ),
        ),
        profile=ANALYSIS_TRANSPORT_PROFILE,
    )
    result = InertCheckedResult(
        _family_applicability_result_id(
            schema_id,
            family_id,
            candidate_id,
            proposition_id,
            basis_id,
            support_id,
            validation_basis_id,
            operation_policy_id,
            hypotheses,
        ),
        proposition_id,
        basis_id,
        support_id,
        validation_basis_id,
        _APPLICABILITY_QUALIFICATION_ID,
        AttemptKind.AFFIRMATIVE,
        ANALYSIS_TRANSPORT_PROFILE,
    )
    binding = _make_authority_binding(
        owner_id=_ANALYSIS_APPLICABILITY_OWNER_ID,
        checked_result=result,
        consumer_label="afk-family-property-transport",
        purpose_label="exact-family-applicability",
        immediate_policy_ids=(operation_policy_id,),
    )
    return result, binding


@_with_family_derivation_scope
def check_afk_family_applicability(
    schema: FSTheoremSchema,
    family: AFKAsymptoticFamily,
    support_hypotheses: Iterable[object],
    *,
    candidate: AFKFamilyApplicabilityInput | None = None,
) -> AttemptOutcome:
    try:
        schema_id = fs_theorem_schema_id(schema)
        family_definition_id(family)
        if schema_id != AFK_V2_THM4_CLASSICAL_ROM:
            return AttemptOutcome(
                AttemptKind.UNSUPPORTED,
                detail="only the selected AFK-v2 semantic schema is supported",
            )
        expected = derive_family_applicability_input(schema, family)
        selected = expected if candidate is None else candidate
        _family_applicability_input_body(selected)
        if selected != expected:
            return AttemptOutcome(
                AttemptKind.REFUSED,
                detail=(
                    "family, experiment, index-domain, premise, parameter, "
                    "or operator binding does not instantiate the global theorem"
                ),
            )
        hypotheses = canonical_hypotheses(support_hypotheses)
        theorem_truth = ASSUMED_AFK_V2_THM4
        if theorem_truth in hypotheses:
            return AttemptOutcome(
                AttemptKind.REFUSED,
                detail="theorem truth is not applicability evidence",
            )
        required = expected.applicability_premise_ids
        if any(item not in hypotheses for item in required):
            return AttemptOutcome(
                AttemptKind.CANNOT_ANSWER,
                detail="one exact family applicability premise is unavailable",
            )
        if hypotheses != required:
            return AttemptOutcome(
                AttemptKind.REFUSED,
                detail="applicability support contains an extra or wrong premise",
            )
        result, binding = _family_applicability_components(
            schema,
            family,
            selected,
            hypotheses,
        )
        return _affirmative(
            AFKFamilyApplicabilityPort(
                family,
                selected,
                hypotheses,
                "afk-family-property-transport-only",
                result,
                binding,
                _issue_invocation_capability(binding, _FAMILY_PORT_TOKENS),
            )
        )
    except (AnalysisError, k2.ModelError, k3.K3Error) as error:
        return AttemptOutcome(AttemptKind.MALFORMED, detail=str(error))


@_with_family_derivation_scope
def require_family_applicability_port(
    port: AFKFamilyApplicabilityPort,
) -> None:
    if type(port) is not AFKFamilyApplicabilityPort:
        raise AuthorityError("family applicability port lacks Analysis issuance")
    expected_candidate = derive_family_applicability_input(
        _AFK_GLOBAL_THEOREM_SCHEMA, port.family
    )
    expected_hypotheses = family_applicability_premise_ids(port.family)
    if (
        port.applicability_input != expected_candidate
        or port.retained_hypotheses != expected_hypotheses
        or port.purpose != "afk-family-property-transport-only"
    ):
        raise TheoremError("family applicability port was substituted")
    expected_result, expected_binding = _family_applicability_components(
        _AFK_GLOBAL_THEOREM_SCHEMA,
        port.family,
        expected_candidate,
        expected_hypotheses,
    )
    if (
        port.checked_result != expected_result
        or port.authority_binding != expected_binding
    ):
        raise AuthorityError("family applicability authority binding is detached")
    _require_invocation_capability(
        port.live_capability, port.authority_binding, _FAMILY_PORT_TOKENS
    )


@dataclass(frozen=True)
class FamilySourcePropertyCapability:
    family: AFKAsymptoticFamily
    external_authority_id: object
    retained_hypotheses: tuple[object, ...]
    named_consumer: str
    typed_purpose: str
    checked_result: InertCheckedResult
    authority_binding: AnalysisSourceAuthorityContract
    live_capability: InvocationCapability

    @property
    def family_definition_id(self) -> object:
        return family_definition_id(self.family)

    @property
    def proposition_id(self) -> object:
        return self.checked_result.proposition_id

    @property
    def semantic_basis_id(self) -> object:
        return self.checked_result.semantic_basis_id

    @property
    def support_id(self) -> object:
        return self.checked_result.support_id

    @property
    def qualification_id(self) -> object:
        return self.checked_result.qualification_id


_EXTERNAL_SOURCE_CAP_TOKENS: dict[object, object] = {}


def _external_family_source_authority_id(label: str) -> object:
    """Form the exact external-owner coordinate used by the bounded fixture.

    The authority is deliberately not an ``analysis.*`` semantic subject:
    Analysis authenticates the assumption that it receives, but does not mint
    or reinterpret the external researcher's authority.
    """

    return k1.content_id(
        "analysis.external-proof-authority",
        k1.encode_datum(
            k1.DatumRecord(
                (
                    (0, k1.Symbol("zkc.analysis.external-family-source")),
                    (1, k1.Nat(0)),
                    (2, k1.Symbol(_ascii(label, "external authority label"))),
                    (3, k1.Symbol("assumed-authenticated-all-n-source-result")),
                )
            )
        ),
        semantic_regime=k1.SEMANTIC_REGIME_ID,
    )


def _family_source_components(
    family: AFKAsymptoticFamily,
    authority_id: object,
) -> tuple[tuple[object, ...], InertCheckedResult, AnalysisSourceAuthorityContract]:
    family_id = family_definition_id(family)
    _id_datum(authority_id, "analysis.external-proof-authority")
    source_families = (
        "total-single-valued-family-denotation",
        "family-projection-coherence",
        "uniform-prime-order-schnorr-family",
        "uniform-polynomial-time-relation-membership",
        "uniform-polynomial-time-verifier",
    )
    source_hypotheses = canonical_hypotheses(
        _exact_premise_goal_id(
            family_label,
            (family_id,),
            _family_semantic_context(family, axes=("fresh-source",)),
            k1.DatumRecord(
                (
                    (0, _id_datum(family_id, "analysis.asymptotic-protocol-family")),
                    (1, k1.Nat(ordinal)),
                )
            ),
            selected_profile=ANALYSIS_TRANSPORT_PROFILE,
        )
        for ordinal, family_label in enumerate(source_families)
    )
    proposition_id = family_source_property_proposition_id(family, source_hypotheses)
    basis_id = _analysis_transport_id(
        "analysis.semantic-basis",
        AnalysisSemanticBasisBodyV0(
            _family_declaration_ref(
                ANALYSIS_TRANSPORT_PROFILE,
                "asymptotic-k-out-of-n-special-soundness",
                owner_profile=ANALYSIS_TRANSPORT_PROFILE,
            ),
            family_question_id(family, "source-two-special-soundness"),
            _native_rule_source(
                ANALYSIS_TRANSPORT_PROFILE,
                ANALYSIS_PROPERTY_PROFILE,
                "conditional-family-instance-correspondence",
                k1.DatumRecord(
                    (
                        (
                            0,
                            _id_datum(
                                family_id,
                                "analysis.asymptotic-protocol-family",
                            ),
                        ),
                        (1, k1.Symbol("assumed-all-n-source-property")),
                    )
                ),
            ),
            _hypothesis_node_requirements(source_hypotheses, transport=True),
            complete_read_purpose_requirements(
                family_manifest_schema_ids=(
                    family_manifest_schema_id(family, "fresh-source"),
                ),
            ),
            _conclusion_schema_ref(
                ANALYSIS_TRANSPORT_PROFILE,
                ANALYSIS_PROPERTY_PROFILE,
                "k-out-of-n-conclusion-v0",
            ),
            k1.DatumRecord(
                (
                    (0, k1.Symbol("external-all-n-source-assumption")),
                    (
                        1,
                        _id_datum(
                            family_id,
                            "analysis.asymptotic-protocol-family",
                        ),
                    ),
                )
            ),
        ),
    )
    support_id = _analysis_support_instantiation_id(
        profile=ANALYSIS_TRANSPORT_PROFILE,
        semantic_basis_id=basis_id,
        proposition_id=proposition_id,
        assumed_goals=source_hypotheses,
        source_support_bindings=k1.DatumSeq(
            (_id_datum(authority_id, "analysis.external-proof-authority"),)
        ),
    )
    qualification_id = analysis_profile_declaration_ref(
        ANALYSIS_TRANSPORT_PROFILE,
        ANALYSIS_PROPERTY_PROFILE,
        "analysis.qualification",
        "conditional-assumed-external-all-n",
    )
    validation_basis_id = analysis_validation_basis_id(
        (), profile=ANALYSIS_TRANSPORT_PROFILE
    )
    result_id = k1.content_id(
        "analysis.external-family-source-result",
        k1.encode_datum(
            k1.DatumRecord(
                (
                    (0, _id_datum(authority_id, "analysis.external-proof-authority")),
                    (1, _id_datum(proposition_id, "analysis.proposition")),
                    (2, _id_datum(basis_id, "analysis.semantic-basis")),
                    (3, _id_datum(support_id, "analysis.support-instantiation")),
                    (
                        4,
                        _id_datum(
                            validation_basis_id,
                            "analysis.validation-basis",
                        ),
                    ),
                    (5, analysis_profile_declaration_ref_body(qualification_id)),
                    (6, k1.Symbol("conditional-assumed-all-n-source-result")),
                )
            )
        ),
        semantic_regime=k1.SEMANTIC_REGIME_ID,
    )
    result = InertCheckedResult(
        result_id,
        proposition_id,
        basis_id,
        support_id,
        validation_basis_id,
        qualification_id,
        AttemptKind.AFFIRMATIVE,
        ANALYSIS_TRANSPORT_PROFILE,
    )
    binding = _make_authority_binding(
        owner_id=authority_id,
        checked_result=result,
        consumer_label="afk-family-property-transport",
        purpose_label="all-n-two-special-soundness-source",
        immediate_policy_ids=(
            _assumed_external_operation_policy_id(
                authority_id, "use-assumed-all-n-source-result"
            ),
        ),
    )
    return source_hypotheses, result, binding


@_with_family_derivation_scope
def assume_external_family_source_capability_for_fixture(
    family: AFKAsymptoticFamily,
    *,
    authority_label: str,
) -> FamilySourcePropertyCapability:
    """Fixture-only external capability; never derived from the n0 extractor."""

    authority_id = _external_family_source_authority_id(authority_label)
    retained, result, binding = _family_source_components(family, authority_id)
    return FamilySourcePropertyCapability(
        family,
        authority_id,
        retained,
        "AFKFamilyTransportConsumer",
        "all-n-two-special-soundness-source",
        result,
        binding,
        _issue_invocation_capability(binding, _EXTERNAL_SOURCE_CAP_TOKENS),
    )


def require_family_source_capability(
    family: AFKAsymptoticFamily,
    capability: FamilySourcePropertyCapability,
) -> None:
    if (
        type(capability) is not FamilySourcePropertyCapability
        or capability.family_definition_id != family_definition_id(family)
        or capability.proposition_id
        != family_source_property_proposition_id(family, capability.retained_hypotheses)
        or capability.named_consumer != "AFKFamilyTransportConsumer"
        or capability.typed_purpose != "all-n-two-special-soundness-source"
    ):
        raise AuthorityError(
            "source capability is not an exact external all-n family result"
        )
    expected_hypotheses, expected_result, expected_binding = _family_source_components(
        family, capability.external_authority_id
    )
    if (
        capability.retained_hypotheses != expected_hypotheses
        or capability.checked_result != expected_result
        or capability.authority_binding != expected_binding
    ):
        raise AuthorityError(
            "external family source capability identity or support was substituted"
        )
    _require_invocation_capability(
        capability.live_capability,
        capability.authority_binding,
        _EXTERNAL_SOURCE_CAP_TOKENS,
    )


@dataclass(frozen=True)
class TheoremTruthTreatment:
    schema: FSTheoremSchema
    treatment: str
    retained_hypothesis_id: object
    checked_result: InertCheckedResult
    authority_binding: AnalysisSourceAuthorityContract
    live_capability: InvocationCapability

    @property
    def theorem_schema_id(self) -> object:
        return fs_theorem_schema_id(self.schema)

    @property
    def theorem_truth_goal_id(self) -> object:
        return theorem_truth_goal_id(self.schema)

    @property
    def support_ref(self) -> object:
        return self.checked_result.support_id


_TRUTH_TREATMENT_TOKENS: dict[object, object] = {}


def _imported_theorem_owner_id(
    schema: FSTheoremSchema, source_validation_id: object
) -> object:
    return k1.content_id(
        "analysis.imported-theorem-owner",
        k1.encode_datum(
            k1.DatumRecord(
                (
                    (0, k1.Symbol("zkc.analysis.imported-theorem-source")),
                    (1, k1.Nat(0)),
                    (
                        2,
                        _id_datum(
                            source_validation_id,
                            "analysis.theorem-source-validation",
                        ),
                    ),
                    (3, k1.Symbol(schema.authority.stable_source_id)),
                )
            )
        ),
        semantic_regime=k1.SEMANTIC_REGIME_ID,
    )


def _theorem_truth_components(
    schema: FSTheoremSchema,
) -> tuple[object, InertCheckedResult, AnalysisSourceAuthorityContract]:
    schema_id = fs_theorem_schema_id(schema)
    goal_id = theorem_truth_goal_id(schema)
    proposition_id = theorem_truth_proposition_id(schema)
    source_validation_id = _require_selected_theorem_source_validation(schema)
    hypothesis_id = goal_id
    basis_id = _analysis_transport_id(
        "analysis.semantic-basis",
        AnalysisSemanticBasisBodyV0(
            _family_declaration_ref(
                ANALYSIS_TRANSPORT_PROFILE,
                "theorem-truth",
                owner_profile=ANALYSIS_TRANSPORT_PROFILE,
            ),
            _analysis_transport_id(
                "analysis.question", theorem_truth_question_body(schema)
            ),
            _imported_theorem_rule_source(schema_id),
            k1.DatumSeq(()),
            (),
            _conclusion_schema_ref(
                ANALYSIS_TRANSPORT_PROFILE,
                ANALYSIS_TRANSPORT_PROFILE,
                "theorem-truth-conclusion-v0",
            ),
            k1.DatumRecord(
                (
                    (0, k1.Symbol("explicit-assumed-theorem-truth")),
                    (1, _id_datum(schema_id, "analysis.theorem-schema")),
                )
            ),
        ),
    )
    support_ref = _analysis_support_instantiation_id(
        profile=ANALYSIS_THEOREM_SOURCE_VALIDATION_PROFILE,
        semantic_basis_id=basis_id,
        proposition_id=proposition_id,
        assumed_goals=(hypothesis_id,),
        theorem_validations={hypothesis_id: source_validation_id},
    )
    qualification_id = analysis_profile_declaration_ref(
        ANALYSIS_THEOREM_SOURCE_VALIDATION_PROFILE,
        ANALYSIS_THEOREM_SOURCE_VALIDATION_PROFILE,
        "analysis.qualification",
        "conditional-assumed-theorem-truth",
    )
    # ImportedPaperOnly is an assumed theorem-truth premise.  Its exact source
    # validation occurs once in the assumed support binding above; the
    # checking attempt consumes no proof artifact, so the validation basis is
    # intentionally empty.
    validation_basis_id = analysis_validation_basis_id(
        (), profile=ANALYSIS_THEOREM_SOURCE_VALIDATION_PROFILE
    )
    result_id = k1.content_id(
        "analysis.assumed-theorem-truth-treatment",
        k1.encode_datum(
            k1.DatumRecord(
                (
                    (0, _id_datum(schema_id, "analysis.theorem-schema")),
                    (1, _id_datum(proposition_id, "analysis.proposition")),
                    (2, _id_datum(basis_id, "analysis.semantic-basis")),
                    (3, _id_datum(support_ref, "analysis.support-instantiation")),
                    (
                        4,
                        _id_datum(
                            validation_basis_id,
                            "analysis.validation-basis",
                        ),
                    ),
                    (5, analysis_profile_declaration_ref_body(qualification_id)),
                    (6, k1.Symbol("Assumed")),
                )
            )
        ),
        semantic_regime=k1.SEMANTIC_REGIME_ID,
    )
    result = InertCheckedResult(
        result_id,
        proposition_id,
        basis_id,
        support_ref,
        validation_basis_id,
        qualification_id,
        AttemptKind.AFFIRMATIVE,
        ANALYSIS_THEOREM_SOURCE_VALIDATION_PROFILE,
    )
    owner_id = _imported_theorem_owner_id(schema, source_validation_id)
    binding = _make_authority_binding(
        owner_id=owner_id,
        checked_result=result,
        consumer_label="afk-family-property-transport",
        purpose_label="selected-afk-theorem-truth",
        immediate_policy_ids=(
            _assumed_external_operation_policy_id(
                owner_id, "use-selected-theorem-truth-treatment"
            ),
        ),
    )
    return hypothesis_id, result, binding


def assume_afk_theorem_truth(
    schema: FSTheoremSchema,
) -> TheoremTruthTreatment:
    hypothesis_id, result, binding = _theorem_truth_components(schema)
    return TheoremTruthTreatment(
        schema,
        "Assumed",
        hypothesis_id,
        result,
        binding,
        _issue_invocation_capability(binding, _TRUTH_TREATMENT_TOKENS),
    )


def require_theorem_truth_treatment(
    schema: FSTheoremSchema, treatment: TheoremTruthTreatment
) -> None:
    expected_hypothesis, expected_result, expected_binding = _theorem_truth_components(
        schema
    )
    if (
        type(treatment) is not TheoremTruthTreatment
        or treatment.schema != schema
        or treatment.treatment != "Assumed"
        or treatment.checked_result != expected_result
        or treatment.authority_binding != expected_binding
        or treatment.retained_hypothesis_id != expected_hypothesis
    ):
        raise AuthorityError("theorem truth treatment is missing or belongs elsewhere")
    _require_invocation_capability(
        treatment.live_capability,
        treatment.authority_binding,
        _TRUTH_TREATMENT_TOKENS,
    )


@dataclass(frozen=True)
class AFKFamilyKnowledgeJudgment:
    judgment_id: object
    theorem_schema_id: object
    family: AFKAsymptoticFamily
    family_definition_id: object
    target_proposition_id: object
    operator_bindings: tuple[AFKFamilyOperatorBinding, ...]
    applicability_input: AFKFamilyApplicabilityInput
    applicability_checked_result: InertCheckedResult
    applicability_authority_binding: AnalysisSourceAuthorityContract
    source_external_authority_id: object
    source_retained_hypothesis_ids: tuple[object, ...]
    source_checked_result: InertCheckedResult
    source_authority_binding: AnalysisSourceAuthorityContract
    theorem_truth_retained_hypothesis_id: object
    theorem_truth_checked_result: InertCheckedResult
    theorem_truth_authority_binding: AnalysisSourceAuthorityContract
    semantic_basis_id: object
    validation_basis_id: object
    hypothesis_nodes: tuple[AnalysisHypothesisNodeV0, ...]
    retained_hypotheses: tuple[object, ...]


@dataclass(frozen=True)
class AFKFamilyKnowledgeCapability:
    judgment: AFKFamilyKnowledgeJudgment
    checked_result: InertCheckedResult
    authority_binding: AnalysisSourceAuthorityContract
    live_capability: InvocationCapability


_FAMILY_JUDGMENT_TOKENS: dict[object, object] = {}
_ANALYSIS_TRANSPORT_OWNER_ID = _k3c_evaluator_owner_id("afk-family-transport")
_FAMILY_TRANSPORT_QUALIFICATION_ID = analysis_profile_declaration_ref(
    ANALYSIS_THEOREM_SOURCE_VALIDATION_PROFILE,
    ANALYSIS_THEOREM_SOURCE_VALIDATION_PROFILE,
    "analysis.qualification",
    "afk-family-transport-result",
)


def _family_judgment_basis_id(
    theorem_schema_id: object,
    family: AFKAsymptoticFamily,
    family_id: object,
    source_proposition_id: object,
    applicability_proposition_id: object,
    theorem_truth_proposition_id_value: object,
    target_goal_id: object,
) -> object:
    return _analysis_transport_id(
        "analysis.semantic-basis",
        AnalysisSemanticBasisBodyV0(
            _family_declaration_ref(
                ANALYSIS_TRANSPORT_PROFILE,
                "adaptive-knowledge-soundness-q-lt-n",
                owner_profile=ANALYSIS_TRANSPORT_PROFILE,
            ),
            _formed_analysis_body(target_goal_id, "analysis.goal").question_id,
            _imported_theorem_rule_source(theorem_schema_id),
            k1.DatumSeq(
                (
                    _id_datum(source_proposition_id, "analysis.proposition"),
                    _id_datum(
                        applicability_proposition_id,
                        "analysis.proposition",
                    ),
                    _id_datum(
                        theorem_truth_proposition_id_value,
                        "analysis.proposition",
                    ),
                )
            ),
            complete_read_purpose_requirements(
                family_manifest_schema_ids=(
                    family_manifest_schema_id(family, "adaptive-fs-target"),
                ),
            ),
            _conclusion_schema_ref(
                ANALYSIS_TRANSPORT_PROFILE,
                ANALYSIS_PROPERTY_PROFILE,
                "adaptive-knowledge-conclusion-v0",
            ),
            k1.DatumRecord(
                (
                    (0, k1.Symbol("selected-afk-v2-family-transport-transform")),
                    (
                        1,
                        _id_datum(
                            family_id,
                            "analysis.asymptotic-protocol-family",
                        ),
                    ),
                    (2, _id_datum(target_goal_id, "analysis.goal")),
                )
            ),
        ),
    )


def _family_judgment_id(
    theorem_schema_id: object,
    family_id: object,
    operator_binding_ids: tuple[object, ...],
    target_proposition_id: object,
    semantic_basis_id: object,
    support_id: object,
    validation_basis_id: object,
    operation_policy_id: object,
    retained_hypotheses: tuple[object, ...],
    policy_closure: tuple[object, ...],
) -> object:
    canonical_policy_closure = _canonical_identifier_set(
        policy_closure, what="derived source-policy dependency closure"
    )
    if canonical_policy_closure != policy_closure:
        raise AuthorityError("family judgment policy closure is not canonical")
    return _analysis_judgment_record_id(
        profile=ANALYSIS_THEOREM_SOURCE_VALIDATION_PROFILE,
        proposition_id=target_proposition_id,
        exact_family_conclusion=k1.DatumRecord(
            (
                (
                    0,
                    _id_datum(
                        theorem_schema_id,
                        "analysis.theorem-schema",
                    ),
                ),
                (
                    1,
                    _id_datum(
                        family_id,
                        "analysis.asymptotic-protocol-family",
                    ),
                ),
                (
                    2,
                    k1.DatumSeq(
                        tuple(
                            _embedded_component_datum(
                                item,
                                "analysis.theorem-operator-binding",
                            )
                            for item in operator_binding_ids
                        )
                    ),
                ),
                (3, k1.Symbol("adaptive-knowledge-soundness-q-lt-N")),
            )
        ),
        inherited_hypothesis_context_id=analysis_hypothesis_context_id(
            retained_hypotheses, transport=True
        ),
        typed_quantitative_result=k1.DatumSeq(
            tuple(
                _embedded_component_datum(
                    item,
                    "analysis.theorem-operator-binding",
                )
                for item in operator_binding_ids
            )
        ),
        semantic_basis_id=semantic_basis_id,
        support_id=support_id,
        validation_basis_id=validation_basis_id,
        qualification=_FAMILY_TRANSPORT_QUALIFICATION_ID,
        operation_policy_id=operation_policy_id,
        source_policy_closure=canonical_policy_closure,
    )


def _family_transport_support_id(
    result_coordinates: tuple[object, object, object],
    retained_hypotheses: tuple[object, ...],
    semantic_basis_id: object,
    target_proposition_id: object,
    source_bindings: tuple[AnalysisSourceAuthorityContract, ...],
) -> object:
    non_hypothesis_bindings = k1.DatumSeq(
        tuple(
            k1.DatumRecord(
                (
                    (0, k1.Nat(ordinal)),
                    (
                        1,
                        _id_datum(
                            item,
                            "analysis.checked-result-coordinate",
                        ),
                    ),
                )
            )
            for ordinal, item in enumerate(result_coordinates)
        ),
    )
    source_support_bindings = k1.DatumSeq(
        tuple(
            _id_datum(
                portable_source_authority_binding_id(binding),
                "analysis.portable-source-authority-binding",
            )
            for binding in source_bindings
        )
    )
    theorem_goal = theorem_truth_goal_id(_AFK_GLOBAL_THEOREM_SCHEMA)
    return _analysis_support_instantiation_id(
        profile=ANALYSIS_THEOREM_SOURCE_VALIDATION_PROFILE,
        semantic_basis_id=semantic_basis_id,
        proposition_id=target_proposition_id,
        assumed_goals=retained_hypotheses,
        theorem_validations={theorem_goal: AFK_V2_THM4_SOURCE_VALIDATION},
        non_hypothesis_premise_bindings=non_hypothesis_bindings,
        source_support_bindings=source_support_bindings,
    )


@_with_family_derivation_scope
def transport_afk_family_knowledge(
    source_capability: FamilySourcePropertyCapability | None,
    applicability_port: AFKFamilyApplicabilityPort,
    theorem_truth: TheoremTruthTreatment | None,
) -> AttemptOutcome:
    try:
        require_family_applicability_port(applicability_port)
        family = applicability_port.family
        if source_capability is None:
            return AttemptOutcome(
                AttemptKind.CANNOT_ANSWER,
                detail="external all-n source-property capability is unavailable",
            )
        if type(source_capability) is not FamilySourcePropertyCapability:
            return AttemptOutcome(
                AttemptKind.REFUSED,
                detail="source carrier is not an all-n family source capability",
            )
        require_family_source_capability(family, source_capability)
        if theorem_truth is None:
            return AttemptOutcome(
                AttemptKind.CANNOT_ANSWER,
                detail="AFK theorem truth has no separate treatment",
            )
        require_theorem_truth_treatment(_AFK_GLOBAL_THEOREM_SCHEMA, theorem_truth)
        if theorem_truth.theorem_schema_id != applicability_port.theorem_schema_id:
            return AttemptOutcome(
                AttemptKind.REFUSED,
                detail="theorem truth treatment belongs to another schema",
            )
        retained = hypothesis_union(
            applicability_port.retained_hypotheses,
            source_capability.retained_hypotheses,
            (theorem_truth.retained_hypothesis_id,),
        )
        target_hypothesis_nodes = tuple(
            AnalysisHypothesisNodeV0(ordinal, goal_id, ())
            for ordinal, goal_id in enumerate(retained)
        )
        target_proposition_id = family_target_property_proposition_id(family, retained)
        source_bindings = (
            applicability_port.authority_binding,
            source_capability.authority_binding,
            theorem_truth.authority_binding,
        )
        policy_closure = derive_source_policy_closure(source_bindings)
        result_coordinates = (
            checked_result_coordinate_id(applicability_port.checked_result),
            checked_result_coordinate_id(source_capability.checked_result),
            checked_result_coordinate_id(theorem_truth.checked_result),
        )
        basis_id = _family_judgment_basis_id(
            applicability_port.theorem_schema_id,
            family,
            family_definition_id(family),
            source_capability.checked_result.proposition_id,
            applicability_port.checked_result.proposition_id,
            theorem_truth.checked_result.proposition_id,
            family_goal_id(family, "target-adaptive-knowledge-q-lt-N"),
        )
        validation_basis_id = analysis_validation_basis_id(
            (), profile=ANALYSIS_THEOREM_SOURCE_VALIDATION_PROFILE
        )
        if theorem_truth.checked_result.validation_basis_id != validation_basis_id:
            return AttemptOutcome(
                AttemptKind.REFUSED,
                detail="theorem-truth validation basis is not exact-used",
            )
        support_id = _family_transport_support_id(
            result_coordinates,
            retained,
            basis_id,
            target_proposition_id,
            source_bindings,
        )
        operation_policy_id = _analysis_operation_policy_id(
            target_proposition_id,
            (
                (
                    "afk-member-specialization",
                    ("afk-family-target-specialization",),
                ),
            ),
            profile=ANALYSIS_THEOREM_SOURCE_VALIDATION_PROFILE,
        )
        operator_binding_ids = tuple(
            family_operator_binding_id(binding)
            for binding in applicability_port.applicability_input.operator_bindings
        )
        judgment_id = _family_judgment_id(
            applicability_port.theorem_schema_id,
            family_definition_id(family),
            operator_binding_ids,
            target_proposition_id,
            basis_id,
            support_id,
            validation_basis_id,
            operation_policy_id,
            retained,
            policy_closure,
        )
        judgment = AFKFamilyKnowledgeJudgment(
            judgment_id=judgment_id,
            theorem_schema_id=applicability_port.theorem_schema_id,
            family=family,
            family_definition_id=family_definition_id(family),
            target_proposition_id=target_proposition_id,
            operator_bindings=applicability_port.applicability_input.operator_bindings,
            applicability_input=applicability_port.applicability_input,
            applicability_checked_result=applicability_port.checked_result,
            applicability_authority_binding=applicability_port.authority_binding,
            source_external_authority_id=source_capability.external_authority_id,
            source_retained_hypothesis_ids=source_capability.retained_hypotheses,
            source_checked_result=source_capability.checked_result,
            source_authority_binding=source_capability.authority_binding,
            theorem_truth_retained_hypothesis_id=theorem_truth.retained_hypothesis_id,
            theorem_truth_checked_result=theorem_truth.checked_result,
            theorem_truth_authority_binding=theorem_truth.authority_binding,
            semantic_basis_id=basis_id,
            validation_basis_id=validation_basis_id,
            hypothesis_nodes=target_hypothesis_nodes,
            retained_hypotheses=retained,
        )
        checked_result = InertCheckedResult(
            judgment_id,
            target_proposition_id,
            basis_id,
            support_id,
            validation_basis_id,
            _FAMILY_TRANSPORT_QUALIFICATION_ID,
            AttemptKind.AFFIRMATIVE,
            ANALYSIS_THEOREM_SOURCE_VALIDATION_PROFILE,
        )
        authority_binding = _make_authority_binding(
            owner_id=_ANALYSIS_TRANSPORT_OWNER_ID,
            checked_result=checked_result,
            consumer_label="afk-member-specialization",
            purpose_label="afk-family-target-specialization",
            immediate_policy_ids=(operation_policy_id,),
            transitive_policy_ids=derive_source_policy_closure(source_bindings),
        )
        return _affirmative(
            AFKFamilyKnowledgeCapability(
                judgment,
                checked_result,
                authority_binding,
                _issue_invocation_capability(
                    authority_binding, _FAMILY_JUDGMENT_TOKENS
                ),
            )
        )
    except AuthorityError as error:
        return AttemptOutcome(AttemptKind.REFUSED, detail=str(error))
    except (AnalysisError, k2.ModelError, k3.K3Error) as error:
        return AttemptOutcome(AttemptKind.MALFORMED, detail=str(error))


@_with_family_derivation_scope
def require_family_knowledge_judgment(
    judgment: AFKFamilyKnowledgeJudgment,
) -> None:
    if (
        type(judgment) is not AFKFamilyKnowledgeJudgment
        or judgment.family_definition_id != family_definition_id(judgment.family)
        or judgment.operator_bindings != family_operator_bindings(judgment.family)
        or judgment.theorem_schema_id != AFK_V2_THM4_CLASSICAL_ROM
    ):
        raise AuthorityError("family knowledge judgment is forged or detached")
    expected_applicability_input = derive_family_applicability_input(
        _AFK_GLOBAL_THEOREM_SCHEMA, judgment.family
    )
    expected_applicability_hypotheses = family_applicability_premise_ids(
        judgment.family
    )
    expected_applicability_result, expected_applicability_binding = (
        _family_applicability_components(
            _AFK_GLOBAL_THEOREM_SCHEMA,
            judgment.family,
            expected_applicability_input,
            expected_applicability_hypotheses,
        )
    )
    if (
        judgment.applicability_input != expected_applicability_input
        or judgment.applicability_checked_result != expected_applicability_result
        or judgment.applicability_authority_binding != expected_applicability_binding
    ):
        raise AuthorityError("family judgment has a detached applicability result")
    expected_source_hypotheses, expected_source_result, expected_source_binding = (
        _family_source_components(
            judgment.family,
            judgment.source_external_authority_id,
        )
    )
    expected_truth_hypothesis, expected_truth_result, expected_truth_binding = (
        _theorem_truth_components(_AFK_GLOBAL_THEOREM_SCHEMA)
    )
    expected_retained = hypothesis_union(
        expected_applicability_hypotheses,
        expected_source_hypotheses,
        (expected_truth_hypothesis,),
    )
    expected_hypothesis_nodes = tuple(
        AnalysisHypothesisNodeV0(ordinal, goal_id, ())
        for ordinal, goal_id in enumerate(expected_retained)
    )
    expected_target_proposition = family_target_property_proposition_id(
        judgment.family, expected_retained
    )
    source_bindings = (
        judgment.applicability_authority_binding,
        judgment.source_authority_binding,
        judgment.theorem_truth_authority_binding,
    )
    policy_closure = derive_source_policy_closure(source_bindings)
    result_coordinates = (
        checked_result_coordinate_id(judgment.applicability_checked_result),
        checked_result_coordinate_id(judgment.source_checked_result),
        checked_result_coordinate_id(judgment.theorem_truth_checked_result),
    )
    expected_basis = _family_judgment_basis_id(
        judgment.theorem_schema_id,
        judgment.family,
        judgment.family_definition_id,
        expected_source_result.proposition_id,
        expected_applicability_result.proposition_id,
        expected_truth_result.proposition_id,
        family_goal_id(judgment.family, "target-adaptive-knowledge-q-lt-N"),
    )
    expected_validation_basis = analysis_validation_basis_id(
        (), profile=ANALYSIS_THEOREM_SOURCE_VALIDATION_PROFILE
    )
    expected_support = _family_transport_support_id(
        result_coordinates,
        expected_retained,
        expected_basis,
        expected_target_proposition,
        source_bindings,
    )
    expected_operation_policy = _analysis_operation_policy_id(
        expected_target_proposition,
        (
            (
                "afk-member-specialization",
                ("afk-family-target-specialization",),
            ),
        ),
        profile=ANALYSIS_THEOREM_SOURCE_VALIDATION_PROFILE,
    )
    if (
        judgment.source_retained_hypothesis_ids != expected_source_hypotheses
        or judgment.source_checked_result != expected_source_result
        or judgment.source_authority_binding != expected_source_binding
        or judgment.theorem_truth_retained_hypothesis_id != expected_truth_hypothesis
        or judgment.theorem_truth_checked_result != expected_truth_result
        or judgment.theorem_truth_authority_binding != expected_truth_binding
        or judgment.target_proposition_id != expected_target_proposition
        or judgment.semantic_basis_id != expected_basis
        or judgment.validation_basis_id != expected_validation_basis
        or judgment.hypothesis_nodes != expected_hypothesis_nodes
        or judgment.retained_hypotheses != expected_retained
    ):
        raise TheoremError(
            "family judgment authority or retained support was substituted"
        )
    expected_judgment_id = _family_judgment_id(
        judgment.theorem_schema_id,
        judgment.family_definition_id,
        tuple(
            family_operator_binding_id(binding)
            for binding in judgment.operator_bindings
        ),
        judgment.target_proposition_id,
        judgment.semantic_basis_id,
        expected_support,
        judgment.validation_basis_id,
        expected_operation_policy,
        expected_retained,
        policy_closure,
    )
    if judgment.judgment_id != expected_judgment_id:
        raise TheoremError("family knowledge judgment identity was substituted")


def require_family_knowledge_capability(
    capability: AFKFamilyKnowledgeCapability,
) -> None:
    if type(capability) is not AFKFamilyKnowledgeCapability:
        raise AuthorityError("family knowledge capability has the wrong exact shape")
    require_family_knowledge_judgment(capability.judgment)
    judgment = capability.judgment
    result_coordinates = (
        checked_result_coordinate_id(judgment.applicability_checked_result),
        checked_result_coordinate_id(judgment.source_checked_result),
        checked_result_coordinate_id(judgment.theorem_truth_checked_result),
    )
    source_bindings = (
        judgment.applicability_authority_binding,
        judgment.source_authority_binding,
        judgment.theorem_truth_authority_binding,
    )
    expected_support = _family_transport_support_id(
        result_coordinates,
        judgment.retained_hypotheses,
        judgment.semantic_basis_id,
        judgment.target_proposition_id,
        source_bindings,
    )
    expected_result = InertCheckedResult(
        judgment.judgment_id,
        judgment.target_proposition_id,
        judgment.semantic_basis_id,
        expected_support,
        judgment.validation_basis_id,
        _FAMILY_TRANSPORT_QUALIFICATION_ID,
        AttemptKind.AFFIRMATIVE,
        ANALYSIS_THEOREM_SOURCE_VALIDATION_PROFILE,
    )
    operation_policy_id = _analysis_operation_policy_id(
        judgment.target_proposition_id,
        (
            (
                "afk-member-specialization",
                ("afk-family-target-specialization",),
            ),
        ),
        profile=ANALYSIS_THEOREM_SOURCE_VALIDATION_PROFILE,
    )
    expected_binding = _make_authority_binding(
        owner_id=_ANALYSIS_TRANSPORT_OWNER_ID,
        checked_result=expected_result,
        consumer_label="afk-member-specialization",
        purpose_label="afk-family-target-specialization",
        immediate_policy_ids=(operation_policy_id,),
        transitive_policy_ids=derive_source_policy_closure(source_bindings),
    )
    if (
        capability.checked_result != expected_result
        or capability.authority_binding != expected_binding
    ):
        raise AuthorityError("family knowledge capability is detached from its result")
    _require_invocation_capability(
        capability.live_capability,
        capability.authority_binding,
        _FAMILY_JUDGMENT_TOKENS,
    )


# ---------------------------------------------------------------------------
# Pointwise n0 specialization: all concrete Foundation/PIR/K3 coordinates live here
# ---------------------------------------------------------------------------


AFK_FAMILY_ROLE_NAMES = (
    "Statement",
    "Witness",
    "Relation",
    "PublicSetup",
    "Commitment",
    "ChallengeSet",
    "Response",
    "FreshExperiment",
    "FiatShamirExperiment",
    "Proof",
    "AuxiliaryOutput",
    "Verifier",
    "VerifierOutput",
    "RandomOracleIndex",
    "StatementLength",
    "RandomOracleQueryResource",
    "AdversaryInvocationResource",
    "ConstantOnePolynomialProfile",
    "ConstantOnePolynomialValueAtIndex",
    "FixedChallengeCardinality",
)
AFK_FAMILY_ROLE_MAP_CLAUSES = (
    "TypedCarrierEquivalence",
    "TypedCarrierEquivalence",
    "PredicateEquivalence",
    "ExactValueCorrespondence",
    "TypedCarrierEquivalence",
    "TypedCarrierEquivalence",
    "TypedCarrierEquivalence",
    "ExperimentProcessCorrespondence",
    "ExperimentProcessCorrespondence",
    "TypedCarrierEquivalence",
    "TypedCarrierEquivalence",
    "VerifierProcessCorrespondence",
    "TypedCarrierEquivalence",
    "TypedCarrierEquivalence",
    "ExactValueCorrespondence",
    "ResourceMeasureCorrespondence",
    "ResourceMeasureCorrespondence",
    "PositivePolynomialProfileSpecialization",
    "PositivePolynomialValueCorrespondence",
    "ExactValueCorrespondence",
)


def logical_nat_literal_id(value: int) -> object:
    """Form the one exact transport-owned logical-natural value."""

    return _analysis_transport_id(
        "analysis.logical-nat-literal",
        AnalysisLogicalNatLiteralBodyV0(value),
    )


def native_subject_projection_id(source: FreshFsRelationSource) -> object:
    require_fresh_fs_relation_source(source)
    return _analysis_transport_id(
        "analysis.native-subject-projection",
        AnalysisNativeSubjectProjectionBodyV0(
            core_id=source.protocol_source.core_id,
            fresh_protocol_id=source.protocol_source.fresh_protocol_id,
            fiat_shamir_protocol_id=source.protocol_source.fiat_shamir_protocol_id,
            fresh_binding_id=source.fresh_binding.binding_id,
            fiat_shamir_binding_id=source.fiat_shamir_binding.binding_id,
            fresh_manifest_id=source_manifest_id(source.fresh_manifest),
            pair_manifest_id=source_manifest_id(source.pair_manifest),
            fresh_plan_binding_id=source.fresh_plan_binding.binding_id,
            fiat_shamir_plan_binding_id=source.fiat_shamir_plan_binding.binding_id,
        ),
    )


def concrete_member_subject_id(
    family: AFKAsymptoticFamily,
    source: FreshFsRelationSource,
    correspondence: FSCorrespondence,
    source_selector_id: object,
    target_selector_id: object,
) -> object:
    """Bind the n0 property subject to the exact admitted native relation lane."""

    require_fresh_fs_relation_source(source)
    fs_correspondence_id(correspondence)
    if (
        source_selector_id != fixed_family_member_selector_id(source, "fresh")
        or target_selector_id != fixed_family_member_selector_id(source, "fiat-shamir")
        or correspondence.fresh_binding_id != source.fresh_binding.binding_id
        or correspondence.fiat_shamir_binding_id
        != source.fiat_shamir_binding.binding_id
    ):
        raise TheoremError(
            "concrete member subject is detached from its exact selectors or relation bindings"
        )
    relation_definition_ids = tuple(
        definition.definition_id for definition in source.case.definitions
    )
    relation_interface_ids = tuple(
        k3.relation_interface_id(interface)
        for interface in source.case.relation_interfaces
    )
    return _legacy_component_id(
        "analysis.concrete-family-member-subject",
        _expand_probe_references(
            k1.DatumRecord(
                (
                    (
                        0,
                        _id_datum(
                            family_definition_id(family),
                            "analysis.asymptotic-protocol-family",
                        ),
                    ),
                    (1, k1.Nat(1)),
                    (
                        2,
                        _id_datum(
                            native_subject_projection_id(source),
                            "analysis.native-subject-projection",
                        ),
                    ),
                    (
                        3,
                        _id_datum(
                            source_selector_id, "analysis.family-member-selector"
                        ),
                    ),
                    (
                        4,
                        _id_datum(
                            target_selector_id, "analysis.family-member-selector"
                        ),
                    ),
                    (
                        5,
                        k1.DatumSeq(
                            tuple(
                                _id_datum(item, "relations.definition")
                                for item in relation_definition_ids
                            )
                        ),
                    ),
                    (
                        6,
                        k1.DatumSeq(
                            tuple(
                                _id_datum(item, "relations.interface")
                                for item in relation_interface_ids
                            )
                        ),
                    ),
                    (
                        7,
                        _id_datum(
                            correspondence.fresh_binding_id,
                            "relations.protocol-binding",
                        ),
                    ),
                    (
                        8,
                        _id_datum(
                            correspondence.fiat_shamir_binding_id,
                            "relations.protocol-binding",
                        ),
                    ),
                    (
                        9,
                        _id_datum(
                            correspondence.fixed_public_setup_id,
                            "analysis.fixed-public-setup",
                        ),
                    ),
                    (10, k1.Symbol("exact-native-relation-member-at-n0")),
                )
            )
        ),
    )


@dataclass(frozen=True)
class FamilyInstanceRoleMap:
    ordinal: int
    role: str
    family_definition_id: object
    logical_index: int
    native_subject_projection_id: object
    abstract_coordinate_id: object
    native_coordinate_id: object
    abstract_resolved_id: object
    native_resolved_id: object
    map_clause: str
    information_loss: str


def _family_instance_role_map_id(mapping: FamilyInstanceRoleMap) -> object:
    if (
        type(mapping) is not FamilyInstanceRoleMap
        or mapping.ordinal not in range(len(AFK_FAMILY_ROLE_NAMES))
        or mapping.role != AFK_FAMILY_ROLE_NAMES[mapping.ordinal]
        or mapping.map_clause != AFK_FAMILY_ROLE_MAP_CLAUSES[mapping.ordinal]
        or mapping.logical_index != 1
        or mapping.information_loss != "ExactEquivalence"
    ):
        raise TheoremError("pointwise role map is missing, reordered, or malformed")
    logical_index_id = logical_nat_literal_id(mapping.logical_index)
    role_catalog_ref = analysis_profile_declaration_ref(
        ANALYSIS_TRANSPORT_PROFILE,
        ANALYSIS_TRANSPORT_PROFILE,
        "analysis.afk-family-role-catalog",
        "selected-afk-twenty-role-catalog-v0",
    )
    clause_catalog_ref = analysis_profile_declaration_ref(
        ANALYSIS_TRANSPORT_PROFILE,
        ANALYSIS_TRANSPORT_PROFILE,
        "analysis.afk-family-role-map-clause",
        "selected-afk-twenty-role-map-clause-catalog-v0",
    )
    native_subject_refs = analysis_domain_body_v0(
        "analysis.native-subject-projection",
        _formed_analysis_body(
            mapping.native_subject_projection_id,
            "analysis.native-subject-projection",
        ),
    )
    role_coordinate = k1.DatumRecord(
        (
            (0, analysis_profile_declaration_ref_body(role_catalog_ref)),
            (1, k1.Nat(mapping.ordinal)),
            (2, k1.Symbol(mapping.role)),
        )
    )
    expected_abstract_coordinate = k1.DatumRecord(
        (
            (
                0,
                _id_datum(
                    mapping.family_definition_id,
                    "analysis.asymptotic-protocol-family",
                ),
            ),
            (1, k1.Nat(mapping.logical_index)),
            (2, k1.Nat(mapping.ordinal)),
            (3, k1.Symbol(mapping.role)),
        )
    )
    expected_native_coordinate = k1.DatumRecord(
        (
            (
                0,
                _id_datum(
                    mapping.native_subject_projection_id,
                    "analysis.native-subject-projection",
                ),
            ),
            (1, k1.Nat(mapping.ordinal)),
            (2, k1.Symbol(mapping.role)),
        )
    )
    if (
        _local_component_body(
            mapping.abstract_coordinate_id,
            "abstract-family-role-coordinate",
        )
        != expected_abstract_coordinate
        or _local_component_body(
            mapping.native_coordinate_id,
            "native-role-coordinate",
        )
        != expected_native_coordinate
    ):
        raise TheoremError("pointwise role coordinate is detached")
    abstract_resolved = _local_component_body(
        mapping.abstract_resolved_id,
        "abstract-resolved-role",
    )
    native_resolved = _local_component_body(
        mapping.native_resolved_id,
        "native-resolved-role",
    )
    if (
        type(abstract_resolved) is not k1.DatumRecord
        or type(native_resolved) is not k1.DatumRecord
        or len(abstract_resolved.fields) != 2
        or len(native_resolved.fields) != 2
        or abstract_resolved.fields[0][1]
        != _id_datum(
            mapping.abstract_coordinate_id,
            "analysis.abstract-family-role-coordinate",
        )
        or native_resolved.fields[0][1]
        != _id_datum(mapping.native_coordinate_id, "analysis.native-role-coordinate")
    ):
        raise TheoremError("pointwise role resolution is detached")
    abstract_role_ref = k1.DatumRecord(
        (
            (
                0,
                _id_datum(
                    mapping.family_definition_id,
                    "analysis.asymptotic-protocol-family",
                ),
            ),
            (1, _id_datum(logical_index_id, "analysis.logical-nat-literal")),
            (2, role_coordinate),
        )
    )
    native_role_ref = k1.DatumRecord(
        (
            (0, native_subject_refs),
            (1, k1.Nat(1)),
            (2, role_coordinate),
        )
    )
    clause_coordinate = k1.DatumRecord(
        (
            (0, analysis_profile_declaration_ref_body(clause_catalog_ref)),
            (1, k1.Nat(mapping.ordinal)),
            (2, k1.Symbol(mapping.map_clause)),
        )
    )
    return _analysis_transport_id(
        "analysis.family-instance-role-map",
        AnalysisFamilyInstanceRoleMapBodyV0(
            _id_datum(
                mapping.family_definition_id,
                "analysis.asymptotic-protocol-family",
            ),
            _id_datum(logical_index_id, "analysis.logical-nat-literal"),
            native_subject_refs,
            k1.Nat(1),
            role_coordinate,
            abstract_role_ref,
            native_role_ref,
            clause_coordinate,
            k1.Symbol(mapping.information_loss),
        ),
    )


def family_instance_role_maps(
    family: AFKAsymptoticFamily,
    source: FreshFsRelationSource,
    correspondence: FSCorrespondence,
    *,
    logical_index: int = 1,
) -> tuple[FamilyInstanceRoleMap, ...]:
    if logical_index != 1:
        raise TheoremError("bounded executable correspondence exists only at n0=1")
    family_id = family_definition_id(family)
    projection_id = native_subject_projection_id(source)
    fs_correspondence_id(correspondence)
    if (
        correspondence.fresh_binding_id != source.fresh_binding.binding_id
        or correspondence.fiat_shamir_binding_id
        != source.fiat_shamir_binding.binding_id
    ):
        raise TheoremError("native role coordinates use a detached FS correspondence")
    relation_coordinates = k1.DatumRecord(
        (
            (
                0,
                k1.DatumSeq(
                    tuple(
                        _id_datum(item.definition_id, "relations.definition")
                        for item in source.case.definitions
                    )
                ),
            ),
            (
                1,
                k1.DatumSeq(
                    tuple(
                        _id_datum(k3.relation_interface_id(item), "relations.interface")
                        for item in source.case.relation_interfaces
                    )
                ),
            ),
        )
    )

    def occurrence_payload(name: str) -> object:
        selected = tuple(
            item for item in correspondence.occurrence_map if item[0] == name
        )
        if len(selected) != 1:
            raise TheoremError("native role resolution needs one exact occurrence")
        return k1.DatumRecord(
            tuple(
                (ordinal, k1.Symbol(value)) for ordinal, value in enumerate(selected[0])
            )
        )

    occurrence_coordinates = k1.DatumSeq(
        tuple(
            k1.DatumRecord(
                tuple((ordinal, k1.Symbol(value)) for ordinal, value in enumerate(item))
            )
            for item in correspondence.occurrence_map
        )
    )
    challenge_coordinates = tuple(
        (ordinal, occurrence)
        for ordinal, occurrence in enumerate(source.case.core.schedule)
        if occurrence.kind is k2.OccurrenceKind.CHALLENGE
    )
    if len(challenge_coordinates) != 1:
        raise TheoremError("selected member must expose one exact challenge domain")
    challenge_ordinal, challenge_occurrence = challenge_coordinates[0]
    if challenge_occurrence.challenge_domain is None:
        raise TheoremError("selected member challenge lacks a finite domain")
    if challenge_occurrence.challenge_domain.modulus != family.challenge_cardinality:
        raise TheoremError("native and family challenge cardinalities disagree")
    native_challenge_domain_id = selected_schnorr_challenge_domain_id(
        correspondence.fixed_public_setup
    )
    source_selector_id = fixed_family_member_selector_id(source, "fresh")
    target_selector_id = fixed_family_member_selector_id(source, "fiat-shamir")
    concrete_subject = concrete_member_subject_id(
        family,
        source,
        correspondence,
        source_selector_id,
        target_selector_id,
    )
    relation_semantics = k1.DatumRecord(
        (
            (0, k1.Symbol(family.relation_law)),
            (1, k1.Symbol(family.statement_length_unit)),
            (2, k1.Nat(logical_index)),
        )
    )
    projection_semantics = k1.DatumRecord(
        (
            (0, k1.Symbol(family.projection_law)),
            (1, k1.Nat(family.challenge_cardinality)),
            (2, k1.Nat(logical_index)),
        )
    )
    abstract_payloads = (
        k1.DatumRecord(((0, relation_semantics), (1, k1.Symbol("statement")))),
        k1.DatumRecord(((0, relation_semantics), (1, k1.Symbol("witness")))),
        relation_semantics,
        k1.DatumRecord(((0, projection_semantics), (1, k1.Symbol("public-setup")))),
        k1.DatumRecord(((0, projection_semantics), (1, k1.Symbol("commitment")))),
        k1.DatumRecord(
            (
                (0, k1.Nat(family.challenge_cardinality)),
                (1, k1.Symbol(family.challenge_cardinality_law)),
            )
        ),
        k1.DatumRecord(((0, projection_semantics), (1, k1.Symbol("response")))),
        k1.DatumRecord(((0, projection_semantics), (1, k1.Symbol("fresh")))),
        k1.DatumRecord(((0, projection_semantics), (1, k1.Symbol("fiat-shamir")))),
        k1.DatumRecord(((0, projection_semantics), (1, k1.Symbol("proof")))),
        k1.DatumRecord(((0, projection_semantics), (1, k1.Symbol("auxiliary-output")))),
        k1.DatumRecord(((0, projection_semantics), (1, k1.Symbol("verifier")))),
        k1.DatumRecord(((0, projection_semantics), (1, k1.Symbol("verifier-output")))),
        _id_datum(family_ro_index_domain_id(family), "analysis.family-ro-index-domain"),
        k1.DatumRecord(
            ((0, k1.Nat(logical_index)), (1, k1.Symbol(family.statement_length_unit)))
        ),
        _id_datum(family_query_dimension_id(family), "analysis.resource-dimension"),
        _id_datum(
            family_invocation_dimension_id(family), "analysis.resource-dimension"
        ),
        _id_datum(
            AFK_POSITIVE_POLYNOMIAL_PROFILE_ID,
            "analysis.positive-polynomial-profile",
        ),
        k1.DatumRecord(
            (
                (0, _id_datum(AFK_Q_ONE_SUBSTITUTION, "analysis.theorem-substitution")),
                (1, k1.Nat(logical_index)),
            )
        ),
        k1.Nat(family.challenge_cardinality),
    )
    native_payloads = (
        k1.DatumSeq(
            tuple(
                k1.DatumSeq(tuple(k1.Symbol(x) for x in item))
                for item in correspondence.statement_map
            )
        ),
        k1.DatumSeq(
            tuple(
                k1.DatumSeq(tuple(k1.Symbol(x) for x in item))
                for item in correspondence.witness_map
            )
        ),
        relation_coordinates,
        _id_datum(correspondence.fixed_public_setup_id, "analysis.fixed-public-setup"),
        occurrence_payload("commitment"),
        _id_datum(native_challenge_domain_id, "analysis.challenge-domain"),
        occurrence_payload("response"),
        k1.DatumRecord(
            (
                (0, _id_datum(correspondence.fresh_protocol_id, "pir.protocol")),
                (
                    1,
                    _id_datum(
                        correspondence.source_model_id, "analysis.experiment-profile"
                    ),
                ),
            )
        ),
        k1.DatumRecord(
            (
                (0, _id_datum(correspondence.fiat_shamir_protocol_id, "pir.protocol")),
                (
                    1,
                    _id_datum(
                        correspondence.target_model_id, "analysis.experiment-profile"
                    ),
                ),
            )
        ),
        k1.DatumRecord(
            (
                (0, _id_datum(correspondence.fiat_shamir_protocol_id, "pir.protocol")),
                (1, occurrence_coordinates),
            )
        ),
        _symbol_seq(correspondence.auxiliary_distribution_map),
        occurrence_payload("verify"),
        occurrence_payload("terminal"),
        k1.DatumRecord(
            (
                (
                    0,
                    _id_datum(
                        correspondence.query_encoding_id, "analysis.query-encoding"
                    ),
                ),
                (
                    1,
                    _id_datum(
                        afk_query_abi_id(family.challenge_cardinality),
                        "analysis.oracle-query-abi",
                    ),
                ),
                (2, _id_datum(projection_id, "analysis.native-subject-projection")),
            )
        ),
        k1.DatumRecord(
            (
                (0, k1.Nat(native_statement_octet_length(source))),
                (1, k1.Symbol("octet")),
                (2, _id_datum(projection_id, "analysis.native-subject-projection")),
            )
        ),
        k1.DatumRecord(
            (
                (
                    0,
                    _id_datum(
                        AFK_ADVERSARY_RO_QUERY_DIMENSION_ID,
                        "analysis.resource-dimension",
                    ),
                ),
                (1, _id_datum(projection_id, "analysis.native-subject-projection")),
                (
                    2,
                    _id_datum(
                        correspondence.query_encoding_id, "analysis.query-encoding"
                    ),
                ),
                (
                    3,
                    _id_datum(
                        afk_query_abi_id(family.challenge_cardinality),
                        "analysis.oracle-query-abi",
                    ),
                ),
            )
        ),
        k1.DatumRecord(
            (
                (
                    0,
                    _id_datum(
                        AFK_ADVERSARY_RUNNING_CALL_DIMENSION_ID,
                        "analysis.resource-dimension",
                    ),
                ),
                (1, _id_datum(projection_id, "analysis.native-subject-projection")),
                (
                    2,
                    _id_datum(
                        subject_bound_afk_adversary_running_algorithm_id(
                            family.challenge_cardinality, concrete_subject
                        ),
                        "analysis.adversary-running-algorithm",
                    ),
                ),
            )
        ),
        k1.DatumRecord(
            (
                (
                    0,
                    _id_datum(
                        AFK_POSITIVE_POLYNOMIAL_PROFILE_ID,
                        "analysis.positive-polynomial-profile",
                    ),
                ),
                (
                    1,
                    _id_datum(
                        concrete_subject, "analysis.concrete-family-member-subject"
                    ),
                ),
            )
        ),
        k1.DatumRecord(
            (
                (0, _id_datum(AFK_Q_ONE_SUBSTITUTION, "analysis.theorem-substitution")),
                (
                    1,
                    _id_datum(
                        concrete_subject, "analysis.concrete-family-member-subject"
                    ),
                ),
                (2, k1.Nat(1)),
            )
        ),
        k1.DatumRecord(
            (
                (0, _id_datum(native_challenge_domain_id, "analysis.challenge-domain")),
                (1, k1.Nat(challenge_occurrence.challenge_domain.modulus)),
            )
        ),
    )
    if (
        len(AFK_FAMILY_ROLE_NAMES) != 20
        or len(AFK_FAMILY_ROLE_MAP_CLAUSES) != 20
        or len(abstract_payloads) != 20
        or len(native_payloads) != 20
        or len(set(AFK_FAMILY_ROLE_NAMES)) != 20
    ):
        raise TheoremError("the twenty-role correspondence schema is incomplete")
    result = []
    for ordinal, role in enumerate(AFK_FAMILY_ROLE_NAMES):
        abstract_id = _legacy_component_id(
            "analysis.abstract-family-role-coordinate",
            k1.DatumRecord(
                (
                    (
                        0,
                        _id_datum(
                            family_id,
                            "analysis.asymptotic-protocol-family",
                        ),
                    ),
                    (1, k1.Nat(logical_index)),
                    (2, k1.Nat(ordinal)),
                    (3, k1.Symbol(role)),
                )
            ),
        )
        native_id = _legacy_component_id(
            "analysis.native-role-coordinate",
            k1.DatumRecord(
                (
                    (
                        0,
                        _id_datum(
                            projection_id,
                            "analysis.native-subject-projection",
                        ),
                    ),
                    (1, k1.Nat(ordinal)),
                    (2, k1.Symbol(role)),
                )
            ),
        )
        abstract_resolved_id = _legacy_component_id(
            "analysis.abstract-resolved-role",
            k1.DatumRecord(
                (
                    (
                        0,
                        _id_datum(
                            abstract_id, "analysis.abstract-family-role-coordinate"
                        ),
                    ),
                    (1, abstract_payloads[ordinal]),
                )
            ),
        )
        native_resolved_id = _legacy_component_id(
            "analysis.native-resolved-role",
            k1.DatumRecord(
                (
                    (0, _id_datum(native_id, "analysis.native-role-coordinate")),
                    (1, native_payloads[ordinal]),
                )
            ),
        )
        result.append(
            FamilyInstanceRoleMap(
                ordinal,
                role,
                family_id,
                logical_index,
                projection_id,
                abstract_id,
                native_id,
                abstract_resolved_id,
                native_resolved_id,
                AFK_FAMILY_ROLE_MAP_CLAUSES[ordinal],
                "ExactEquivalence",
            )
        )
    return tuple(result)


@dataclass(frozen=True)
class PointwiseFormulaCorrespondence:
    local_ordinal: int
    family_formula_id: object
    member_formula_id: object
    family_instantiated_ast: str
    member_normalized_ast: str
    exact_substitution: tuple[str, ...]


def _member_operator_normal_form(
    transform: AFKQuantitativeTransform, local_ordinal: int
) -> str:
    """Independently normalize one concrete typed expression.

    This path never reads the theorem template.  Equality with the separately
    parsed family AST is therefore a real comparison rather than X == X.
    """

    if (
        type(transform) is not AFKQuantitativeTransform
        or type(transform.challenge_count) is not int
        or transform.challenge_count < 2
        or local_ordinal not in range(len(AFK_LOCAL_OPERATOR_CATALOG))
    ):
        raise TheoremError("member operator ordinal is outside the AFK catalog")
    knowledge_error = transform.knowledge_error
    if (
        type(knowledge_error) is not QScale
        or type(knowledge_error.count) is not QSum
        or len(knowledge_error.count.terms) != 2
        or type(knowledge_error.term) is not QRational
        or knowledge_error.term.value.numerator != 1
        or knowledge_error.sort is not QuantitativeSort.PROBABILITY
    ):
        raise TheoremError("member knowledge-error AST is outside the local grammar")
    query_terms = tuple(
        item for item in knowledge_error.count.terms if type(item) is QVariable
    )
    literal_terms = tuple(
        item for item in knowledge_error.count.terms if type(item) is QNatural
    )
    if len(query_terms) != 1 or len(literal_terms) != 1:
        raise TheoremError("member knowledge-error count is not variable plus literal")
    query_term = query_terms[0]
    literal_term = literal_terms[0]
    knowledge_error_ast: LocalOperatorAst = (
        "bounded-ratio",
        query_term.name,
        literal_term.value,
        knowledge_error.term.value.denominator,
        transform.challenge_count,
    )
    if local_ordinal == 0:
        expression = knowledge_error
        member_ast = knowledge_error_ast
    elif local_ordinal == 1:
        expression = transform.knowledge_success_lower_bound
        if (
            type(expression) is not QSignedProbabilityDifferenceOverPositivePolynomial
            or expression.success != transform.source_success
            or expression.knowledge_error != knowledge_error
            or expression.positive_polynomial_binder != "q_KS"
            or expression.polynomial_argument
            != QVariable("n", QuantitativeSort.SECURITY_PARAMETER)
            or transform.positive_polynomial_id != AFK_POSITIVE_POLYNOMIAL_Q_ONE
            or transform.q_one_substitution_id != AFK_Q_ONE_SUBSTITUTION
        ):
            raise TheoremError("member knowledge-success AST is outside operator 1")
        member_ast = ("difference", knowledge_error_ast)
    elif local_ordinal == 2:
        expression = transform.lemma4_extraction_lower_bound
        if (
            type(expression) is not QExtractionLowerBound
            or expression.success != transform.source_success
            or expression.knowledge_error != knowledge_error
        ):
            raise TheoremError("member transcript-bound AST is outside operator 2")
        member_ast = (
            "scale-difference",
            expression.factor,
            knowledge_error_ast,
        )
    else:
        expression = transform.expected_adversary_calls
        if (
            type(expression) is not QExpectedAdversaryCallsUpperBound
            or type(expression.query_bound) is not QVariable
            or expression.resource_dimension_id
            != AFK_ADVERSARY_RUNNING_CALL_DIMENSION_ID
            or expression.actor_algorithm_id
            != subject_bound_afk_adversary_running_algorithm_id(
                transform.challenge_count, transform.subject_id
            )
        ):
            raise TheoremError("member invocation-bound AST is outside operator 3")
        member_ast = (
            "expected-count",
            expression.query_bound.name,
            expression.offset,
        )
    admit_quantitative(expression)
    return _canonical_local_operator_ast(member_ast)


def pointwise_formula_correspondences(
    family: AFKAsymptoticFamily,
    concrete_subject_id: object,
) -> tuple[PointwiseFormulaCorrespondence, ...]:
    _id_datum(concrete_subject_id, "analysis.concrete-family-member-subject")
    transform = afk_quantitative_transform(
        k=2,
        challenge_count=family.challenge_cardinality,
        subject_id=concrete_subject_id,
    )
    concrete = afk_quantitative_formula_ids(transform)
    member_by_ordinal = tuple(concrete[role] for role in AFK_MEMBER_FORMULA_ROLES)
    return tuple(
        PointwiseFormulaCorrespondence(
            binding.local_ordinal,
            binding.formula_id,
            member_by_ordinal[binding.local_ordinal],
            binding.instantiated_ast,
            _member_operator_normal_form(transform, binding.local_ordinal),
            (
                "member-index-n0=1",
                "statement-length=1-octet",
                f"N={family.challenge_cardinality}",
                "qKS-profile=constant-one",
                "checked-independent-canonical-AST-equality-after-substitution",
            ),
        )
        for binding in family_operator_bindings(family)
    )


def _pointwise_formula_correspondence_id(
    correspondence: PointwiseFormulaCorrespondence,
    family: AFKAsymptoticFamily,
    concrete_subject_id: object,
    fixed_setup: FixedPublicSetup,
) -> object:
    if type(correspondence) is not PointwiseFormulaCorrespondence:
        raise TheoremError(
            "pointwise formula correspondence is detached from its exact formulas or AST"
        )
    family_definition_id(family)
    _id_datum(concrete_subject_id, "analysis.concrete-family-member-subject")
    ordinal = correspondence.local_ordinal
    expected_binding = (
        family_operator_bindings(family)[ordinal]
        if type(ordinal) is int and ordinal in range(4)
        else None
    )
    transform = afk_quantitative_transform(
        k=2,
        challenge_count=family.challenge_cardinality,
        subject_id=concrete_subject_id,
    )
    expected_member_formula = (
        afk_quantitative_formula_ids(transform)[AFK_MEMBER_FORMULA_ROLES[ordinal]]
        if expected_binding is not None
        else None
    )
    expected_member_ast = (
        _member_operator_normal_form(transform, ordinal)
        if expected_binding is not None
        else None
    )
    expected_substitution = (
        "member-index-n0=1",
        "statement-length=1-octet",
        f"N={family.challenge_cardinality}",
        "qKS-profile=constant-one",
        "checked-independent-canonical-AST-equality-after-substitution",
    )
    if (
        expected_binding is None
        or correspondence.family_formula_id != expected_binding.formula_id
        or correspondence.member_formula_id != expected_member_formula
        or correspondence.family_instantiated_ast != expected_binding.instantiated_ast
        or correspondence.member_normalized_ast != expected_member_ast
        or correspondence.family_instantiated_ast
        != correspondence.member_normalized_ast
        or correspondence.exact_substitution != expected_substitution
    ):
        raise TheoremError(
            "pointwise formula correspondence is detached from its exact formulas or AST"
        )
    return pointwise_quantitative_normalization_id(
        family, concrete_subject_id, fixed_setup
    )


def pointwise_quantitative_normalization_id(
    family: AFKAsymptoticFamily,
    concrete_subject_id: object,
    fixed_setup: FixedPublicSetup,
) -> object:
    """Compile the four checked equalities into one durable AFK contract."""

    family_id = family_definition_id(family)
    concrete_subject = _expand_probe_references(
        _local_component_body(
            concrete_subject_id,
            "concrete-family-member-subject",
        )
    )
    logical_index_id = logical_nat_literal_id(1)
    challenge_domain_id = selected_schnorr_challenge_domain_id(fixed_setup)
    if (
        _fixed_setup_challenge_projection(fixed_setup).challenge_domain.modulus
        != family.challenge_cardinality
    ):
        raise TheoremError(
            "pointwise normalization maps unequal abstract and concrete cardinalities"
        )
    correspondences = pointwise_formula_correspondences(
        family,
        concrete_subject_id,
    )
    if len(correspondences) != 4:
        raise TheoremError("pointwise normalization needs exactly four formulas")
    equal_normal_forms = []
    expected_bindings = family_operator_bindings(family)
    transform = afk_quantitative_transform(
        k=2,
        challenge_count=family.challenge_cardinality,
        subject_id=concrete_subject_id,
    )
    member_formulas = afk_quantitative_formula_ids(transform)
    for ordinal, correspondence in enumerate(correspondences):
        expected_binding = expected_bindings[ordinal]
        expected_member_formula = member_formulas[AFK_MEMBER_FORMULA_ROLES[ordinal]]
        expected_member_ast = _member_operator_normal_form(transform, ordinal)
        if (
            correspondence.local_ordinal != ordinal
            or correspondence.family_formula_id != expected_binding.formula_id
            or correspondence.member_formula_id != expected_member_formula
            or correspondence.family_instantiated_ast
            != expected_binding.instantiated_ast
            or correspondence.member_normalized_ast != expected_member_ast
            or correspondence.family_instantiated_ast
            != correspondence.member_normalized_ast
        ):
            raise TheoremError("pointwise normalization equality was substituted")
        equal_normal_forms.append(
            k1.DatumRecord(
                (
                    (0, k1.Nat(ordinal)),
                    (
                        1,
                        _id_datum(
                            correspondence.family_formula_id,
                            "analysis.quantitative-formula",
                        ),
                    ),
                    (
                        2,
                        _id_datum(
                            correspondence.member_formula_id,
                            "analysis.quantitative-formula",
                        ),
                    ),
                    (3, k1.Symbol(correspondence.family_instantiated_ast)),
                    (4, k1.Symbol(correspondence.member_normalized_ast)),
                )
            )
        )
    query_resource = _expand_probe_references(
        _local_component_body(
            family_query_dimension_id(family),
            "resource-dimension",
        )
    )
    invocation_resource = _expand_probe_references(
        _local_component_body(
            family_invocation_dimension_id(family),
            "resource-dimension",
        )
    )
    body = AnalysisPointwiseQuantitativeNormalizationBodyV0(
        k1.DatumRecord(
            (
                (0, _id_datum(family_id, "analysis.asymptotic-protocol-family")),
                (1, _id_datum(logical_index_id, "analysis.logical-nat-literal")),
                (2, k1.Nat(1)),
                (3, k1.Nat(1)),
                (4, concrete_subject),
            )
        ),
        k1.DatumRecord(
            (
                (0, k1.Nat(family.challenge_cardinality)),
                (1, _id_datum(challenge_domain_id, "analysis.challenge-domain")),
                (2, k1.Nat(family.challenge_cardinality)),
            )
        ),
        k1.DatumRecord(
            (
                (
                    0,
                    _id_datum(
                        AFK_POSITIVE_POLYNOMIAL_PROFILE_ID,
                        "analysis.positive-polynomial-profile",
                    ),
                ),
                (
                    1,
                    _id_datum(
                        AFK_POSITIVE_POLYNOMIAL_PROFILE_ID,
                        "analysis.positive-polynomial-profile",
                    ),
                ),
            )
        ),
        k1.DatumRecord(
            (
                (
                    0,
                    _id_datum(
                        AFK_POSITIVE_POLYNOMIAL_Q_ONE,
                        "analysis.positive-polynomial",
                    ),
                ),
                (1, k1.Nat(1)),
                (2, k1.Nat(1)),
            )
        ),
        k1.DatumSeq(
            (
                k1.DatumRecord(
                    (
                        (0, query_resource),
                        (
                            1,
                            _expand_probe_references(
                                _local_component_body(
                                    AFK_ADVERSARY_RO_QUERY_DIMENSION_ID,
                                    "resource-dimension",
                                )
                            ),
                        ),
                    )
                ),
                k1.DatumRecord(
                    (
                        (0, invocation_resource),
                        (
                            1,
                            _expand_probe_references(
                                _local_component_body(
                                    AFK_ADVERSARY_RUNNING_CALL_DIMENSION_ID,
                                    "resource-dimension",
                                )
                            ),
                        ),
                    )
                ),
            )
        ),
        k1.DatumRecord(
            (
                (0, k1.Symbol("recursive-inline-acyclic-formulas")),
                (1, k1.Symbol("preserve-typed-count-and-probability-coercions")),
                (2, k1.Symbol("canonicalize-under-closed-quantitative-ast-v0")),
            )
        ),
        k1.DatumSeq(tuple(equal_normal_forms)),
    )
    return _analysis_transport_id(
        "analysis.pointwise-quantitative-normalization",
        body,
    )


def _family_instance_exact_subjects(
    family: AFKAsymptoticFamily,
    source: FreshFsRelationSource,
    correspondence: FSCorrespondence,
) -> tuple[object, ...]:
    """Return the one subject sequence shared by every instance premise."""

    require_fresh_fs_relation_source(source)
    fs_correspondence_id(correspondence)
    return (
        family_definition_id(family),
        logical_nat_literal_id(1),
        native_subject_projection_id(source),
        selected_schnorr_challenge_domain_id(correspondence.fixed_public_setup),
        correspondence.fixed_public_setup_id,
    )


def _family_instance_premise_goal_id(
    family: AFKAsymptoticFamily,
    source: FreshFsRelationSource,
    source_model: ExperimentModel,
    target_model: ExperimentModel,
    correspondence: FSCorrespondence,
    family_label: str,
    payload: object,
) -> object:
    """Compile one of the five exact pointwise family-premise families."""

    require_fresh_fs_relation_source(source)
    if correspondence != derive_fs_correspondence(source, source_model, target_model):
        raise TheoremError("family-instance premise selected another FS correspondence")
    family_id = family_definition_id(family)
    exact_subjects = _family_instance_exact_subjects(family, source, correspondence)
    context = k1.DatumVariant(
        3,
        k1.DatumRecord(
            (
                (0, _id_datum(family_id, "analysis.asymptotic-protocol-family")),
                (
                    1,
                    k1.DatumSeq(
                        tuple(
                            _id_datum(
                                family_manifest_schema_id(family, axis),
                                "analysis.family-read-manifest-schema",
                            )
                            for axis in ("fresh-source", "adaptive-fs-target")
                        )
                    ),
                ),
                (
                    2,
                    k1.DatumSeq(
                        (
                            _id_datum(
                                source_manifest_id(source.fresh_manifest),
                                "analysis.semantic-read-manifest",
                            ),
                            _id_datum(
                                source_manifest_id(source.pair_manifest),
                                "analysis.semantic-read-manifest",
                            ),
                        )
                    ),
                ),
                (
                    3,
                    k1.DatumSeq(
                        tuple(
                            _id_datum(
                                family_experiment_profile_id(family, axis),
                                "analysis.experiment-profile",
                            )
                            for axis in ("fresh-source", "adaptive-fs-target")
                        )
                    ),
                ),
                (
                    4,
                    k1.DatumSeq(
                        (
                            _id_datum(
                                experiment_model_id(source_model),
                                "analysis.experiment-profile",
                            ),
                            _id_datum(
                                experiment_model_id(target_model),
                                "analysis.experiment-profile",
                            ),
                        )
                    ),
                ),
            )
        ),
    )
    return _exact_premise_goal_id(
        family_label,
        exact_subjects,
        context,
        payload,
        selected_profile=ANALYSIS_TRANSPORT_PROFILE,
    )


def fixed_member_process_hypothesis_id(
    family: AFKAsymptoticFamily, correspondence: FSCorrespondence
) -> object:
    return _family_instance_premise_goal_id(
        family,
        _SCHNORR_PINNED_SOURCE,
        _SCHNORR_PINNED_MODEL,
        adaptive_rom_knowledge_model(k=2, challenge_count=8),
        correspondence,
        "family-instance-process-correspondence",
        k1.DatumRecord(
            (
                (
                    0,
                    _id_datum(
                        family_definition_id(family),
                        "analysis.asymptotic-protocol-family",
                    ),
                ),
                (
                    1,
                    _id_datum(
                        fs_correspondence_id(correspondence),
                        "analysis.fs-correspondence",
                    ),
                ),
                (
                    2,
                    k1.Symbol(
                        "assumed-full-adaptive-family-to-PIR-process-correspondence-at-n0"
                    ),
                ),
            )
        ),
    )


def fixed_member_role_adequacy_hypothesis_id(
    family: AFKAsymptoticFamily,
    source: FreshFsRelationSource,
    correspondence: FSCorrespondence,
) -> object:
    role_map_ids = tuple(
        _family_instance_role_map_id(item)
        for item in family_instance_role_maps(family, source, correspondence)
    )
    return _family_instance_premise_goal_id(
        family,
        source,
        _SCHNORR_PINNED_MODEL,
        adaptive_rom_knowledge_model(k=2, challenge_count=8),
        correspondence,
        "family-instance-role-map-adequacy",
        k1.DatumRecord(
            (
                (
                    0,
                    _id_datum(
                        family_definition_id(family),
                        "analysis.asymptotic-protocol-family",
                    ),
                ),
                (
                    1,
                    _id_datum(
                        native_subject_projection_id(source),
                        "analysis.native-subject-projection",
                    ),
                ),
                (
                    2,
                    k1.DatumSeq(
                        tuple(
                            _id_datum(
                                item,
                                "analysis.family-instance-role-map",
                            )
                            for item in role_map_ids
                        )
                    ),
                ),
                (
                    3,
                    k1.Symbol(
                        "assumed-semantic-equivalence-of-twenty-content-bound-role-maps"
                    ),
                ),
            )
        ),
    )


def fixed_member_formula_adequacy_hypothesis_id(
    family: AFKAsymptoticFamily,
    concrete_subject_id: object,
) -> object:
    source = _SCHNORR_PINNED_SOURCE
    correspondence = derive_fs_correspondence(
        source,
        _SCHNORR_PINNED_MODEL,
        adaptive_rom_knowledge_model(k=2, challenge_count=8),
    )
    normalization_id = pointwise_quantitative_normalization_id(
        family,
        concrete_subject_id,
        correspondence.fixed_public_setup,
    )
    return _family_instance_premise_goal_id(
        family,
        source,
        _SCHNORR_PINNED_MODEL,
        adaptive_rom_knowledge_model(k=2, challenge_count=8),
        correspondence,
        "family-instance-quantitative-normalization-adequacy",
        k1.DatumRecord(
            (
                (
                    0,
                    _id_datum(
                        family_definition_id(family),
                        "analysis.asymptotic-protocol-family",
                    ),
                ),
                (
                    1,
                    _id_datum(
                        normalization_id,
                        "analysis.pointwise-quantitative-normalization",
                    ),
                ),
                (
                    2,
                    k1.Symbol(
                        "checked-canonical-AST-equality-with-assumed-denotational-correspondence"
                    ),
                ),
            )
        ),
    )


@dataclass(frozen=True)
class FamilyInstanceCorrespondenceJudgment:
    """Portable conditional result for one exact family/member correspondence."""

    judgment_id: object
    family_definition_id: object
    logical_index: int
    logical_index_id: object
    native_statement_length: int
    native_subject_projection_id: object
    concrete_member_subject_id: object
    family_index_bound_at_n0: int
    native_index_bound: int
    family_experiment_profile_ids: tuple[object, object]
    concrete_experiment_profile_ids: tuple[object, object]
    fs_correspondence_id: object
    source_member_selector_id: object
    target_member_selector_id: object
    role_map_ids: tuple[object, ...]
    normalization_id: object
    exact_subjects: tuple[object, ...]
    family_manifest_schema_ids: tuple[object, ...]
    concrete_manifest_ids: tuple[object, ...]
    family_support_schema_bindings: tuple[object, object]
    concrete_support_coordinates: tuple[object, object]
    hypothesis_nodes: tuple[AnalysisHypothesisNodeV0, ...]
    retained_hypotheses: tuple[object, ...]
    proposition_id: object
    semantic_basis_id: object
    support_id: object
    validation_basis_id: object
    operation_policy_id: object
    qualification_id: object


@dataclass(frozen=True)
class ConcreteFamilyInstanceCorrespondence:
    judgment: FamilyInstanceCorrespondenceJudgment
    checked_result: InertCheckedResult
    authority_binding: AnalysisSourceAuthorityContract
    live_capability: InvocationCapability
    family: AFKAsymptoticFamily
    family_definition_id: object
    logical_index: int
    native_statement_length: int
    source: FreshFsRelationSource
    native_subject_projection_id: object
    concrete_member_subject_id: object
    family_index_bound_at_n0: int
    native_index_bound: int
    source_model: ExperimentModel
    target_model: ExperimentModel
    fs_correspondence: FSCorrespondence
    fs_correspondence_id: object
    source_member_selector_id: object
    target_member_selector_id: object
    role_maps: tuple[FamilyInstanceRoleMap, ...]
    formula_correspondences: tuple[PointwiseFormulaCorrespondence, ...]
    retained_hypotheses: tuple[object, ...]


_MEMBER_CORRESPONDENCE_TOKENS: dict[object, object] = {}
_MEMBER_CORRESPONDENCE_OWNER_ID = _k3c_evaluator_owner_id(
    "family-instance-correspondence"
)
_MEMBER_CORRESPONDENCE_QUALIFICATION_ID = analysis_profile_declaration_ref(
    ANALYSIS_TRANSPORT_PROFILE,
    ANALYSIS_TRANSPORT_PROFILE,
    "analysis.qualification",
    "afk-family-instance-correspondence-result",
)


def native_statement_octet_length(source: FreshFsRelationSource) -> int:
    require_fresh_fs_relation_source(source)
    statement = source.case.invocation.values.get("statement")
    if type(statement) is not int or statement < 0:
        raise TheoremError("native statement must be a nonnegative integer")
    return max(1, (statement.bit_length() + 7) // 8)


def fixed_member_length_embedding_hypothesis_id(
    family: AFKAsymptoticFamily,
    source: FreshFsRelationSource,
    concrete_subject_id: object,
) -> object:
    native_length = native_statement_octet_length(source)
    _id_datum(concrete_subject_id, "analysis.concrete-family-member-subject")
    if native_length != 1:
        raise TheoremError("selected n0 member requires one native statement octet")
    source_model = fresh_special_soundness_model(k=2, challenge_count=8)
    target_model = adaptive_rom_knowledge_model(k=2, challenge_count=8)
    correspondence = derive_fs_correspondence(source, source_model, target_model)
    return _family_instance_premise_goal_id(
        family,
        source,
        source_model,
        target_model,
        correspondence,
        "family-denotation-at-index",
        k1.DatumRecord(
            (
                (
                    0,
                    _id_datum(
                        family_definition_id(family),
                        "analysis.asymptotic-protocol-family",
                    ),
                ),
                (
                    1,
                    _id_datum(
                        concrete_subject_id,
                        "analysis.concrete-family-member-subject",
                    ),
                ),
                (2, k1.Nat(1)),
                (3, k1.Nat(native_length)),
                (
                    4,
                    k1.Symbol(
                        "checked-native-octet-length-with-assumed-family-index-embedding"
                    ),
                ),
            )
        ),
    )


def fixed_member_index_bound_hypothesis_id(
    family: AFKAsymptoticFamily,
    concrete_subject_id: object,
    family_index_bound_at_n0: int,
    native_index_bound: int,
) -> object:
    _id_datum(concrete_subject_id, "analysis.concrete-family-member-subject")
    if (
        type(family_index_bound_at_n0) is not int
        or type(native_index_bound) is not int
        or family_index_bound_at_n0 <= 0
        or native_index_bound <= 0
        or family_index_bound_at_n0 != family_ro_index_bound_at(family, 1)
        or family_index_bound_at_n0 != native_index_bound
    ):
        raise TheoremError(
            "pointwise oracle-index bounds must be positive and exactly agree"
        )
    source = _SCHNORR_PINNED_SOURCE
    correspondence = derive_fs_correspondence(
        source,
        _SCHNORR_PINNED_MODEL,
        adaptive_rom_knowledge_model(k=2, challenge_count=8),
    )
    return fixed_member_role_adequacy_hypothesis_id(
        family,
        source,
        correspondence,
    )


def _fixed_member_hypothesis_nodes(
    family: AFKAsymptoticFamily,
    source: FreshFsRelationSource,
    source_model: ExperimentModel,
    target_model: ExperimentModel,
    correspondence: FSCorrespondence,
    *,
    family_index_bound_at_n0: int | None = None,
) -> tuple[AnalysisHypothesisNodeV0, ...]:
    source_selector_id = fixed_family_member_selector_id(source, "fresh")
    target_selector_id = fixed_family_member_selector_id(source, "fiat-shamir")
    concrete_subject_id = concrete_member_subject_id(
        family,
        source,
        correspondence,
        source_selector_id,
        target_selector_id,
    )
    native_index_bound = native_raw_query_index_bit_bound()
    derived_family_bound = family_ro_index_bound_at(family, 1)
    selected_family_bound = (
        derived_family_bound
        if family_index_bound_at_n0 is None
        else family_index_bound_at_n0
    )
    if selected_family_bound != native_index_bound:
        raise TheoremError("family/native index bounds disagree at the selected member")
    family_id = family_definition_id(family)
    theorem_schema_id = fs_theorem_schema_id(afk_v2_theorem_schema())
    instance_projection_goal = _family_instance_premise_goal_id(
        family,
        source,
        source_model,
        target_model,
        correspondence,
        "family-projection-at-index",
        k1.DatumRecord(
            (
                (0, _id_datum(family_id, "analysis.asymptotic-protocol-family")),
                (1, k1.Nat(1)),
                (2, k1.Nat(native_statement_octet_length(source))),
            )
        ),
    )
    applicability_context = _family_semantic_context(
        family,
        axes=("fresh-source", "adaptive-fs-target"),
    )
    fixed_cardinality_goal = _exact_premise_goal_id(
        "fixed-family-challenge-cardinality",
        (theorem_schema_id, family_id),
        applicability_context,
        k1.DatumRecord(
            (
                (0, _id_datum(family_id, "analysis.asymptotic-protocol-family")),
                (1, k1.Nat(family.challenge_cardinality)),
            )
        ),
        selected_profile=ANALYSIS_TRANSPORT_PROFILE,
    )
    finite_index_goal = _exact_premise_goal_id(
        "finite-bounded-random-oracle-index-and-efficient-operations",
        (theorem_schema_id, family_id),
        applicability_context,
        k1.DatumRecord(
            (
                (0, _id_datum(family_id, "analysis.asymptotic-protocol-family")),
                (1, k1.Nat(selected_family_bound)),
                (2, k1.Nat(native_index_bound)),
            )
        ),
        selected_profile=ANALYSIS_TRANSPORT_PROFILE,
    )
    goals = (
        fixed_member_length_embedding_hypothesis_id(
            family, source, concrete_subject_id
        ),
        instance_projection_goal,
        k2_static_view_support_hypothesis_id(source),
        schnorr_relation_correspondence_hypothesis_id(
            derive_schnorr_special_soundness_profile(source)
        ),
        fixed_cardinality_goal,
        finite_index_goal,
        fixed_member_role_adequacy_hypothesis_id(family, source, correspondence),
        fixed_member_formula_adequacy_hypothesis_id(family, concrete_subject_id),
        fixed_member_process_hypothesis_id(family, correspondence),
    )
    dependencies = (
        (),
        (0,),
        (),
        (),
        (0, 1),
        (0, 1),
        (0, 1, 2, 3, 4, 5),
        (0, 1, 2, 4, 6),
        (0, 1, 5, 6),
    )
    return tuple(
        AnalysisHypothesisNodeV0(ordinal, goal_id, dependencies[ordinal])
        for ordinal, goal_id in enumerate(goals)
    )


@_with_family_derivation_scope
def fixed_member_required_hypotheses(
    family: AFKAsymptoticFamily,
    source: FreshFsRelationSource,
    source_model: ExperimentModel,
    target_model: ExperimentModel,
    correspondence: FSCorrespondence,
    *,
    family_index_bound_at_n0: int | None = None,
) -> tuple[object, ...]:
    nodes = _fixed_member_hypothesis_nodes(
        family,
        source,
        source_model,
        target_model,
        correspondence,
        family_index_bound_at_n0=family_index_bound_at_n0,
    )
    return canonical_hypotheses(node.goal_id for node in nodes)


@dataclass(frozen=True)
class _FamilyInstanceCorrespondenceCoordinates:
    family_definition_id: object
    logical_index: int
    logical_index_id: object
    native_statement_length: int
    native_subject_projection_id: object
    concrete_member_subject_id: object
    family_index_bound_at_n0: int
    native_index_bound: int
    family_experiment_profile_ids: tuple[object, object]
    concrete_experiment_profile_ids: tuple[object, object]
    fs_correspondence_id: object
    source_member_selector_id: object
    target_member_selector_id: object
    role_map_ids: tuple[object, ...]
    normalization_id: object
    exact_subjects: tuple[object, ...]
    family_manifest_schema_ids: tuple[object, ...]
    concrete_manifest_ids: tuple[object, ...]
    family_support_schema_bindings: tuple[object, object]
    concrete_support_coordinates: tuple[object, object]
    hypothesis_nodes: tuple[AnalysisHypothesisNodeV0, ...]
    retained_hypotheses: tuple[object, ...]


def _concrete_source_support_coordinate(
    source: FreshFsRelationSource,
    manifest: SourceManifest,
    *,
    axis: str,
) -> object:
    """Form inert support for one exact manifest after live owner validation."""

    require_fresh_fs_relation_source(source)
    if axis == "fresh" and manifest == source.fresh_manifest:
        owner_coordinates = (
            source.protocol_source.core_id,
            source.protocol_source.fresh_protocol_id,
            source.fresh_binding.binding_id,
            source.fresh_plan_binding.binding_id,
        )
    elif axis == "adaptive-fs-target" and manifest == source.pair_manifest:
        owner_coordinates = (
            source.protocol_source.core_id,
            source.protocol_source.construction_id,
            source.protocol_source.fresh_protocol_id,
            source.protocol_source.fiat_shamir_protocol_id,
            source.fresh_binding.binding_id,
            source.fiat_shamir_binding.binding_id,
            source.fresh_plan_binding.binding_id,
            source.fiat_shamir_plan_binding.binding_id,
        )
    else:
        raise AuthorityError("concrete source support selected another manifest axis")
    bindings = k1.DatumSeq(
        tuple(
            k1.DatumRecord(((0, k1.Nat(ordinal)), (1, _id_datum(coordinate))))
            for ordinal, coordinate in enumerate(owner_coordinates)
        )
    )
    return _analysis_id(
        "analysis.source-support",
        AnalysisSourceSupportBodyV0(source_manifest_id(manifest), bindings, ()),
    )


def _family_support_schema_binding(
    manifest_schema_id: object,
    experiment_profile_id_value: object,
    context_id: object,
    nodes: tuple[AnalysisHypothesisNodeV0, ...],
) -> object:
    return k1.DatumRecord(
        (
            (
                0,
                _id_datum(manifest_schema_id, "analysis.family-read-manifest-schema"),
            ),
            (
                1,
                _id_datum(experiment_profile_id_value, "analysis.experiment-profile"),
            ),
            (2, _id_datum(context_id, "analysis.hypothesis-context")),
            (
                3,
                k1.DatumSeq(
                    tuple(_id_datum(node.goal_id, "analysis.goal") for node in nodes)
                ),
            ),
        )
    )


def _family_instance_source_support_bindings(
    coordinates: _FamilyInstanceCorrespondenceCoordinates,
) -> object:
    return k1.DatumSeq(
        (
            *(
                k1.DatumVariant(0, binding)
                for binding in coordinates.family_support_schema_bindings
            ),
            *(
                k1.DatumVariant(
                    1,
                    k1.DatumRecord(
                        (
                            (
                                0,
                                _id_datum(
                                    manifest_id,
                                    "analysis.semantic-read-manifest",
                                ),
                            ),
                            (
                                1,
                                _id_datum(
                                    experiment_id,
                                    "analysis.experiment-profile",
                                ),
                            ),
                            (
                                2,
                                _id_datum(
                                    support_id,
                                    "analysis.source-support",
                                ),
                            ),
                        )
                    ),
                )
                for manifest_id, experiment_id, support_id in zip(
                    coordinates.concrete_manifest_ids,
                    coordinates.concrete_experiment_profile_ids,
                    coordinates.concrete_support_coordinates,
                    strict=True,
                )
            ),
        )
    )


def _family_instance_correspondence_coordinates(
    family: AFKAsymptoticFamily,
    source: FreshFsRelationSource,
    source_model: ExperimentModel,
    target_model: ExperimentModel,
    correspondence: FSCorrespondence,
    concrete_subject_id: object,
    family_index_bound_at_n0: int,
    native_index_bound: int,
    source_selector_id: object,
    target_selector_id: object,
    role_maps: tuple[FamilyInstanceRoleMap, ...],
    hypotheses: tuple[object, ...],
) -> _FamilyInstanceCorrespondenceCoordinates:
    family_id = family_definition_id(family)
    logical_index_id = logical_nat_literal_id(1)
    role_map_ids = tuple(_family_instance_role_map_id(item) for item in role_maps)
    normalization_id = pointwise_quantitative_normalization_id(
        family,
        concrete_subject_id,
        correspondence.fixed_public_setup,
    )
    family_manifests = tuple(
        family_manifest_schema_id(family, axis)
        for axis in ("fresh-source", "adaptive-fs-target")
    )
    concrete_manifests = (
        source_manifest_id(source.fresh_manifest),
        source_manifest_id(source.pair_manifest),
    )
    family_experiments = tuple(
        family_experiment_profile_id(family, axis)
        for axis in ("fresh-source", "adaptive-fs-target")
    )
    concrete_experiments = (
        experiment_model_id(source_model),
        experiment_model_id(target_model),
    )
    hypothesis_nodes = _fixed_member_hypothesis_nodes(
        family,
        source,
        source_model,
        target_model,
        correspondence,
        family_index_bound_at_n0=family_index_bound_at_n0,
    )
    if canonical_hypotheses(node.goal_id for node in hypothesis_nodes) != hypotheses:
        raise AuthorityError(
            "family-instance hypothesis DAG does not match its frontier"
        )
    instance_context_id = _analysis_transport_id(
        "analysis.hypothesis-context",
        AnalysisHypothesisContextBodyV0(hypothesis_nodes, (7, 8)),
    )
    family_supports = tuple(
        _family_support_schema_binding(
            manifest_id,
            experiment_id,
            instance_context_id,
            hypothesis_nodes,
        )
        for manifest_id, experiment_id in zip(
            family_manifests, family_experiments, strict=True
        )
    )
    concrete_supports = (
        _concrete_source_support_coordinate(
            source, source.fresh_manifest, axis="fresh"
        ),
        _concrete_source_support_coordinate(
            source, source.pair_manifest, axis="adaptive-fs-target"
        ),
    )
    exact_subjects = _family_instance_exact_subjects(family, source, correspondence)
    return _FamilyInstanceCorrespondenceCoordinates(
        family_id,
        1,
        logical_index_id,
        native_statement_octet_length(source),
        native_subject_projection_id(source),
        concrete_subject_id,
        family_index_bound_at_n0,
        native_index_bound,
        family_experiments,
        concrete_experiments,
        fs_correspondence_id(correspondence),
        source_selector_id,
        target_selector_id,
        role_map_ids,
        normalization_id,
        exact_subjects,
        family_manifests,
        concrete_manifests,
        family_supports,
        concrete_supports,
        hypothesis_nodes,
        hypotheses,
    )


def _coordinates_from_correspondence_judgment(
    judgment: FamilyInstanceCorrespondenceJudgment,
) -> _FamilyInstanceCorrespondenceCoordinates:
    return _FamilyInstanceCorrespondenceCoordinates(
        judgment.family_definition_id,
        judgment.logical_index,
        judgment.logical_index_id,
        judgment.native_statement_length,
        judgment.native_subject_projection_id,
        judgment.concrete_member_subject_id,
        judgment.family_index_bound_at_n0,
        judgment.native_index_bound,
        judgment.family_experiment_profile_ids,
        judgment.concrete_experiment_profile_ids,
        judgment.fs_correspondence_id,
        judgment.source_member_selector_id,
        judgment.target_member_selector_id,
        judgment.role_map_ids,
        judgment.normalization_id,
        judgment.exact_subjects,
        judgment.family_manifest_schema_ids,
        judgment.concrete_manifest_ids,
        judgment.family_support_schema_bindings,
        judgment.concrete_support_coordinates,
        judgment.hypothesis_nodes,
        judgment.retained_hypotheses,
    )


def _family_instance_correspondence_goal_id(
    coordinates: _FamilyInstanceCorrespondenceCoordinates,
) -> object:
    payload = _expand_probe_references(
        k1.DatumRecord(
            (
                (
                    0,
                    _id_datum(
                        coordinates.family_definition_id,
                        "analysis.asymptotic-protocol-family",
                    ),
                ),
                (
                    1,
                    _id_datum(
                        coordinates.logical_index_id,
                        "analysis.logical-nat-literal",
                    ),
                ),
                (2, k1.Nat(coordinates.native_statement_length)),
                (
                    3,
                    _id_datum(
                        coordinates.native_subject_projection_id,
                        "analysis.native-subject-projection",
                    ),
                ),
                (
                    4,
                    k1.DatumRecord(
                        (
                            (0, k1.Nat(coordinates.family_index_bound_at_n0)),
                            (1, k1.Nat(coordinates.native_index_bound)),
                        )
                    ),
                ),
                (
                    5,
                    _id_datum(
                        coordinates.fs_correspondence_id,
                        "analysis.fs-correspondence",
                    ),
                ),
                (
                    6,
                    k1.DatumSeq(
                        tuple(
                            _id_datum(item, "analysis.family-instance-role-map")
                            for item in coordinates.role_map_ids
                        )
                    ),
                ),
                (
                    7,
                    _id_datum(
                        coordinates.normalization_id,
                        "analysis.pointwise-quantitative-normalization",
                    ),
                ),
                (
                    8,
                    k1.DatumSeq(
                        (
                            _id_datum(
                                coordinates.source_member_selector_id,
                                "analysis.family-member-selector",
                            ),
                            _id_datum(
                                coordinates.target_member_selector_id,
                                "analysis.family-member-selector",
                            ),
                        )
                    ),
                ),
                (
                    9,
                    k1.DatumRecord(
                        (
                            (
                                0,
                                k1.DatumSeq(
                                    tuple(
                                        _id_datum(item, "analysis.experiment-profile")
                                        for item in (
                                            coordinates.family_experiment_profile_ids
                                        )
                                    )
                                ),
                            ),
                            (
                                1,
                                k1.DatumSeq(
                                    tuple(
                                        _id_datum(item, "analysis.experiment-profile")
                                        for item in (
                                            coordinates.concrete_experiment_profile_ids
                                        )
                                    )
                                ),
                            ),
                        )
                    ),
                ),
            )
        )
    )
    return _exact_premise_goal_id(
        "family-instance-correspondence",
        coordinates.exact_subjects,
        k1.DatumVariant(
            3,
            k1.DatumRecord(
                (
                    (
                        0,
                        k1.DatumSeq(
                            tuple(
                                _id_datum(item, "analysis.family-read-manifest-schema")
                                for item in coordinates.family_manifest_schema_ids
                            )
                        ),
                    ),
                    (
                        1,
                        k1.DatumSeq(
                            tuple(
                                _id_datum(item, "analysis.semantic-read-manifest")
                                for item in coordinates.concrete_manifest_ids
                            )
                        ),
                    ),
                )
            ),
        ),
        payload,
        selected_profile=ANALYSIS_TRANSPORT_PROFILE,
    )


def _family_instance_hypothesis_context_id(
    coordinates: _FamilyInstanceCorrespondenceCoordinates,
) -> object:
    if (
        len(coordinates.hypothesis_nodes) != 9
        or tuple(node.local_ordinal for node in coordinates.hypothesis_nodes)
        != tuple(range(9))
        or canonical_hypotheses(node.goal_id for node in coordinates.hypothesis_nodes)
        != coordinates.retained_hypotheses
    ):
        raise AuthorityError("family-instance hypothesis DAG is incomplete")
    return _analysis_transport_id(
        "analysis.hypothesis-context",
        AnalysisHypothesisContextBodyV0(coordinates.hypothesis_nodes, (7, 8)),
    )


def _family_instance_correspondence_components(
    coordinates: _FamilyInstanceCorrespondenceCoordinates,
) -> tuple[
    FamilyInstanceCorrespondenceJudgment,
    InertCheckedResult,
    AnalysisSourceAuthorityContract,
]:
    hypotheses = canonical_hypotheses(coordinates.retained_hypotheses)
    if hypotheses != coordinates.retained_hypotheses:
        raise AuthorityError("family-instance support is not canonical")
    context_id = _family_instance_hypothesis_context_id(coordinates)
    expected_family_supports = tuple(
        _family_support_schema_binding(
            manifest_id,
            experiment_id,
            context_id,
            coordinates.hypothesis_nodes,
        )
        for manifest_id, experiment_id in zip(
            coordinates.family_manifest_schema_ids,
            coordinates.family_experiment_profile_ids,
            strict=True,
        )
    )
    if coordinates.family_support_schema_bindings != expected_family_supports:
        raise AuthorityError("family manifest support schema was substituted")
    for support_id, manifest_id in zip(
        coordinates.concrete_support_coordinates,
        coordinates.concrete_manifest_ids,
        strict=True,
    ):
        support_body = _formed_analysis_body(support_id, "analysis.source-support")
        expected_support_id = _qualification_exact_concrete_source_support_id(
            manifest_id
        )
        if (
            type(support_body) is not AnalysisSourceSupportBodyV0
            or support_body.semantic_read_manifest_id != manifest_id
            or support_body.derived_owner_policy_dependency_closure != ()
            or support_id != expected_support_id
        ):
            raise AuthorityError("concrete manifest support was substituted")
    goal_id = _family_instance_correspondence_goal_id(coordinates)
    proposition_id = _analysis_transport_id(
        "analysis.proposition",
        AnalysisPropositionBodyV0(
            goal_id,
            context_id,
        ),
    )
    source_purposes = complete_read_purpose_requirements(
        concrete_manifest_ids=coordinates.concrete_manifest_ids,
        family_manifest_schema_ids=coordinates.family_manifest_schema_ids,
    )
    semantic_basis_id = _analysis_transport_id(
        "analysis.semantic-basis",
        AnalysisSemanticBasisBodyV0(
            _family_declaration_ref(
                ANALYSIS_TRANSPORT_PROFILE,
                "family-instance-correspondence",
                owner_profile=ANALYSIS_TRANSPORT_PROFILE,
            ),
            _formed_analysis_body(goal_id, "analysis.goal").question_id,
            _native_rule_source(
                ANALYSIS_TRANSPORT_PROFILE,
                ANALYSIS_PROPERTY_PROFILE,
                "conditional-family-instance-correspondence",
                k1.DatumRecord(
                    (
                        (
                            0,
                            _id_datum(
                                coordinates.family_definition_id,
                                "analysis.asymptotic-protocol-family",
                            ),
                        ),
                        (
                            1,
                            _id_datum(
                                coordinates.logical_index_id,
                                "analysis.logical-nat-literal",
                            ),
                        ),
                        (2, k1.Nat(coordinates.native_statement_length)),
                    )
                ),
            ),
            _exact_hypothesis_node_requirements(
                context_id,
                coordinates.hypothesis_nodes,
            ),
            source_purposes,
            _conclusion_schema_ref(
                ANALYSIS_TRANSPORT_PROFILE,
                ANALYSIS_TRANSPORT_PROFILE,
                "family-instance-correspondence-conclusion-v0",
            ),
            k1.DatumRecord(
                (
                    (
                        0,
                        k1.DatumSeq(
                            tuple(
                                _id_datum(item, "analysis.family-instance-role-map")
                                for item in coordinates.role_map_ids
                            )
                        ),
                    ),
                    (
                        1,
                        _id_datum(
                            coordinates.normalization_id,
                            "analysis.pointwise-quantitative-normalization",
                        ),
                    ),
                    (2, k1.Symbol("conditional-one-member-correspondence-only")),
                )
            ),
        ),
    )
    support_id = _analysis_support_instantiation_id(
        profile=ANALYSIS_TRANSPORT_PROFILE,
        semantic_basis_id=semantic_basis_id,
        proposition_id=proposition_id,
        assumed_goals=hypotheses,
        assumed_hypothesis_node_bindings=k1.DatumSeq(
            tuple(
                k1.DatumRecord(
                    (
                        (0, k1.Nat(node.local_ordinal)),
                        (
                            1,
                            k1.DatumRecord(
                                (
                                    (0, _id_datum(node.goal_id, "analysis.goal")),
                                    (1, k1.DatumVariant(0, k1.UNIT)),
                                    (2, k1.DatumVariant(0, k1.UNIT)),
                                )
                            ),
                        ),
                    )
                )
                for node in coordinates.hypothesis_nodes
            )
        ),
        source_support_bindings=_family_instance_source_support_bindings(coordinates),
    )
    validation_basis_id = analysis_validation_basis_id(
        (), profile=ANALYSIS_TRANSPORT_PROFILE
    )
    operation_policy_id = _analysis_operation_policy_id(
        proposition_id,
        (
            (
                "afk-member-specialization",
                ("afk-exact-family-member-specialization",),
            ),
        ),
        profile=ANALYSIS_TRANSPORT_PROFILE,
    )
    judgment_id = _analysis_judgment_record_id(
        profile=ANALYSIS_TRANSPORT_PROFILE,
        proposition_id=proposition_id,
        exact_family_conclusion=k1.DatumRecord(
            (
                (
                    0,
                    _id_datum(
                        coordinates.family_definition_id,
                        "analysis.asymptotic-protocol-family",
                    ),
                ),
                (
                    1,
                    _id_datum(
                        coordinates.logical_index_id,
                        "analysis.logical-nat-literal",
                    ),
                ),
                (
                    2,
                    _expand_probe_references(
                        _id_datum(
                            coordinates.native_subject_projection_id,
                            "analysis.native-subject-projection",
                        )
                    ),
                ),
                (
                    3,
                    _embedded_component_datum(
                        coordinates.concrete_member_subject_id,
                        "analysis.concrete-family-member-subject",
                    ),
                ),
                (4, k1.Nat(coordinates.native_statement_length)),
            )
        ),
        inherited_hypothesis_context_id=_family_instance_hypothesis_context_id(
            coordinates
        ),
        typed_quantitative_result=k1.DatumVariant(0, k1.UNIT),
        semantic_basis_id=semantic_basis_id,
        support_id=support_id,
        validation_basis_id=validation_basis_id,
        qualification=_MEMBER_CORRESPONDENCE_QUALIFICATION_ID,
        operation_policy_id=operation_policy_id,
    )
    judgment = FamilyInstanceCorrespondenceJudgment(
        judgment_id,
        coordinates.family_definition_id,
        coordinates.logical_index,
        coordinates.logical_index_id,
        coordinates.native_statement_length,
        coordinates.native_subject_projection_id,
        coordinates.concrete_member_subject_id,
        coordinates.family_index_bound_at_n0,
        coordinates.native_index_bound,
        coordinates.family_experiment_profile_ids,
        coordinates.concrete_experiment_profile_ids,
        coordinates.fs_correspondence_id,
        coordinates.source_member_selector_id,
        coordinates.target_member_selector_id,
        coordinates.role_map_ids,
        coordinates.normalization_id,
        coordinates.exact_subjects,
        coordinates.family_manifest_schema_ids,
        coordinates.concrete_manifest_ids,
        coordinates.family_support_schema_bindings,
        coordinates.concrete_support_coordinates,
        coordinates.hypothesis_nodes,
        hypotheses,
        proposition_id,
        semantic_basis_id,
        support_id,
        validation_basis_id,
        operation_policy_id,
        _MEMBER_CORRESPONDENCE_QUALIFICATION_ID,
    )
    checked_result = InertCheckedResult(
        judgment_id,
        proposition_id,
        semantic_basis_id,
        support_id,
        validation_basis_id,
        _MEMBER_CORRESPONDENCE_QUALIFICATION_ID,
        AttemptKind.AFFIRMATIVE,
        ANALYSIS_TRANSPORT_PROFILE,
    )
    authority_binding = _make_authority_binding(
        owner_id=_MEMBER_CORRESPONDENCE_OWNER_ID,
        checked_result=checked_result,
        consumer_label="afk-member-specialization",
        purpose_label="afk-exact-family-member-specialization",
        immediate_policy_ids=(operation_policy_id,),
    )
    return judgment, checked_result, authority_binding


@_with_family_derivation_scope
def require_family_instance_correspondence_judgment(
    judgment: FamilyInstanceCorrespondenceJudgment,
) -> None:
    if type(judgment) is not FamilyInstanceCorrespondenceJudgment:
        raise AuthorityError("family-instance correspondence judgment is malformed")
    expected, _, _ = _family_instance_correspondence_components(
        _coordinates_from_correspondence_judgment(judgment)
    )
    if expected != judgment:
        raise AuthorityError("family-instance correspondence judgment was substituted")


@_with_family_derivation_scope
def form_concrete_family_instance_correspondence(
    family: AFKAsymptoticFamily,
    source: FreshFsRelationSource,
    source_model: ExperimentModel,
    target_model: ExperimentModel,
    assumptions: Iterable[object],
    *,
    correspondence: FSCorrespondence | None = None,
    family_index_bound_at_n0: int | None = None,
    role_maps: tuple[FamilyInstanceRoleMap, ...] | None = None,
    formula_correspondences: tuple[PointwiseFormulaCorrespondence, ...] | None = None,
) -> AttemptOutcome:
    try:
        family_definition_id(family)
        require_fresh_fs_relation_source(source)
        _require_exact_special_soundness_model(source_model)
        _require_exact_adaptive_knowledge_model(target_model)
        profile = derive_schnorr_special_soundness_profile(source)
        native_statement_length = native_statement_octet_length(source)
        if (
            family.challenge_cardinality != 8
            or profile.challenge_count != 8
            or native_statement_length != 1
            or _model_parameters(source_model) != {"N": 8, "k": 2}
            or _model_parameters(target_model) != {"N": 8, "k": 2}
        ):
            return AttemptOutcome(
                AttemptKind.CANNOT_ANSWER,
                detail="the bounded n0 specialization requires the exact N=8 member",
            )
        native_index_bound = native_raw_query_index_bit_bound()
        derived_family_bound = family_ro_index_bound_at(family, 1)
        selected_family_bound = (
            derived_family_bound
            if family_index_bound_at_n0 is None
            else family_index_bound_at_n0
        )
        if (
            selected_family_bound != derived_family_bound
            or derived_family_bound != native_index_bound
        ):
            return AttemptOutcome(
                AttemptKind.CANNOT_ANSWER,
                detail=(
                    "supplied or evaluated u(n0) does not match the authenticated "
                    "family bound and Foundation bounded-byte member domain"
                ),
            )
        expected_correspondence = derive_fs_correspondence(
            source, source_model, target_model
        )
        selected_correspondence = (
            expected_correspondence if correspondence is None else correspondence
        )
        if selected_correspondence != expected_correspondence:
            return AttemptOutcome(
                AttemptKind.MALFORMED,
                detail="concrete Fresh/FS process correspondence was substituted",
            )
        fs_correspondence_id(selected_correspondence)
        if not selected_correspondence.sampler_map or not all(
            total_uniform
            and modulus == family.challenge_cardinality
            and width == 1
            and attempts == 1
            for _, modulus, width, attempts, total_uniform in selected_correspondence.sampler_map
        ):
            return AttemptOutcome(
                AttemptKind.CANNOT_ANSWER,
                detail="concrete sampler is not exact total uniform N=8",
            )
        expected_role_maps = family_instance_role_maps(
            family, source, selected_correspondence
        )
        selected_role_maps = expected_role_maps if role_maps is None else role_maps
        if selected_role_maps != expected_role_maps:
            return AttemptOutcome(
                AttemptKind.MALFORMED,
                detail="pointwise role map domain or coordinate was substituted",
            )
        for mapping in selected_role_maps:
            _family_instance_role_map_id(mapping)
        source_selector_id = fixed_family_member_selector_id(source, "fresh")
        target_selector_id = fixed_family_member_selector_id(source, "fiat-shamir")
        concrete_subject_id = concrete_member_subject_id(
            family,
            source,
            selected_correspondence,
            source_selector_id,
            target_selector_id,
        )
        expected_formulas = pointwise_formula_correspondences(
            family, concrete_subject_id
        )
        selected_formulas = (
            expected_formulas
            if formula_correspondences is None
            else formula_correspondences
        )
        for mapping in selected_formulas:
            _pointwise_formula_correspondence_id(
                mapping,
                family,
                concrete_subject_id,
                selected_correspondence.fixed_public_setup,
            )
        if selected_formulas != expected_formulas:
            return AttemptOutcome(
                AttemptKind.MALFORMED,
                detail="pointwise formula substitution is not exact AST equality",
            )
        hypotheses = canonical_hypotheses(assumptions)
        required = fixed_member_required_hypotheses(
            family,
            source,
            source_model,
            target_model,
            selected_correspondence,
            family_index_bound_at_n0=selected_family_bound,
        )
        if any(item not in hypotheses for item in required):
            return AttemptOutcome(
                AttemptKind.CANNOT_ANSWER,
                detail="one pointwise correspondence adequacy premise is unavailable",
            )
        if hypotheses != required:
            return AttemptOutcome(
                AttemptKind.REFUSED,
                detail="pointwise correspondence support has extra or wrong premises",
            )
        coordinates = _family_instance_correspondence_coordinates(
            family,
            source,
            source_model,
            target_model,
            selected_correspondence,
            concrete_subject_id,
            selected_family_bound,
            native_index_bound,
            source_selector_id,
            target_selector_id,
            selected_role_maps,
            hypotheses,
        )
        judgment, checked_result, authority_binding = (
            _family_instance_correspondence_components(coordinates)
        )
        live_capability = _issue_invocation_capability(
            authority_binding, _MEMBER_CORRESPONDENCE_TOKENS
        )
        return _affirmative(
            ConcreteFamilyInstanceCorrespondence(
                judgment,
                checked_result,
                authority_binding,
                live_capability,
                family,
                family_definition_id(family),
                1,
                native_statement_length,
                source,
                native_subject_projection_id(source),
                concrete_subject_id,
                selected_family_bound,
                native_index_bound,
                source_model,
                target_model,
                selected_correspondence,
                fs_correspondence_id(selected_correspondence),
                source_selector_id,
                target_selector_id,
                selected_role_maps,
                selected_formulas,
                hypotheses,
            )
        )
    except AuthorityError as error:
        return AttemptOutcome(AttemptKind.REFUSED, detail=str(error))
    except (AnalysisError, k2.ModelError, k3.K3Error) as error:
        return AttemptOutcome(AttemptKind.MALFORMED, detail=str(error))


def require_concrete_family_instance_correspondence(
    capability: ConcreteFamilyInstanceCorrespondence,
) -> None:
    if type(capability) is not ConcreteFamilyInstanceCorrespondence:
        raise AuthorityError(
            "pointwise family/member correspondence is forged or detached"
        )
    family_definition_id(capability.family)
    require_fresh_fs_relation_source(capability.source)
    _require_exact_special_soundness_model(capability.source_model)
    _require_exact_adaptive_knowledge_model(capability.target_model)
    profile = derive_schnorr_special_soundness_profile(capability.source)
    expected_native_length = native_statement_octet_length(capability.source)
    expected_native_bound = native_raw_query_index_bit_bound()
    expected_family_bound = family_ro_index_bound_at(capability.family, 1)
    expected_correspondence = derive_fs_correspondence(
        capability.source, capability.source_model, capability.target_model
    )
    if (
        capability.family.challenge_cardinality != 8
        or profile.challenge_count != 8
        or expected_native_length != 1
        or _model_parameters(capability.source_model) != {"N": 8, "k": 2}
        or _model_parameters(capability.target_model) != {"N": 8, "k": 2}
        or expected_family_bound != expected_native_bound
        or capability.family_index_bound_at_n0 != expected_family_bound
        or capability.native_index_bound != expected_native_bound
        or capability.fs_correspondence != expected_correspondence
        or not expected_correspondence.sampler_map
        or not all(
            total_uniform and modulus == 8 and width == 1 and attempts == 1
            for _, modulus, width, attempts, total_uniform in (
                expected_correspondence.sampler_map
            )
        )
    ):
        raise AuthorityError(
            "pointwise family/member correspondence does not satisfy its exact gate"
        )
    expected_source_selector = fixed_family_member_selector_id(
        capability.source, "fresh"
    )
    expected_target_selector = fixed_family_member_selector_id(
        capability.source, "fiat-shamir"
    )
    expected_subject = concrete_member_subject_id(
        capability.family,
        capability.source,
        expected_correspondence,
        expected_source_selector,
        expected_target_selector,
    )
    expected_role_maps = family_instance_role_maps(
        capability.family, capability.source, expected_correspondence
    )
    expected_formulas = pointwise_formula_correspondences(
        capability.family, expected_subject
    )
    expected_hypotheses = fixed_member_required_hypotheses(
        capability.family,
        capability.source,
        capability.source_model,
        capability.target_model,
        expected_correspondence,
        family_index_bound_at_n0=expected_family_bound,
    )
    coordinates = _family_instance_correspondence_coordinates(
        capability.family,
        capability.source,
        capability.source_model,
        capability.target_model,
        expected_correspondence,
        expected_subject,
        expected_family_bound,
        expected_native_bound,
        expected_source_selector,
        expected_target_selector,
        expected_role_maps,
        expected_hypotheses,
    )
    expected_judgment, expected_result, expected_binding = (
        _family_instance_correspondence_components(coordinates)
    )
    if (
        capability.judgment != expected_judgment
        or capability.checked_result != expected_result
        or capability.authority_binding != expected_binding
        or capability.family_definition_id != coordinates.family_definition_id
        or capability.logical_index != coordinates.logical_index
        or capability.native_statement_length != expected_native_length
        or capability.native_subject_projection_id
        != coordinates.native_subject_projection_id
        or capability.concrete_member_subject_id != expected_subject
        or capability.fs_correspondence_id != coordinates.fs_correspondence_id
        or capability.source_member_selector_id != expected_source_selector
        or capability.target_member_selector_id != expected_target_selector
        or capability.role_maps != expected_role_maps
        or capability.formula_correspondences != expected_formulas
        or capability.retained_hypotheses != expected_hypotheses
    ):
        raise AuthorityError(
            "pointwise family/member correspondence does not reproduce its minting gate"
        )
    require_family_instance_correspondence_judgment(capability.judgment)
    _require_invocation_capability(
        capability.live_capability,
        capability.authority_binding,
        _MEMBER_CORRESPONDENCE_TOKENS,
    )


@dataclass(frozen=True)
class ConcreteMemberKnowledgeJudgment:
    judgment_id: object
    family_judgment: AFKFamilyKnowledgeJudgment
    correspondence_judgment: FamilyInstanceCorrespondenceJudgment
    family_judgment_id: object
    correspondence_checked_result: InertCheckedResult
    correspondence_authority_binding: AnalysisSourceAuthorityContract
    correspondence_retained_hypotheses: tuple[object, ...]
    family_definition_id: object
    logical_index: int
    native_statement_length: int
    native_subject_projection_id: object
    concrete_member_subject_id: object
    quantitative_transform: AFKQuantitativeTransform
    quantitative_transform_id: object
    quantitative_formula_ids: tuple[object, ...]
    target_conclusion: AFKKnowledgeSoundnessConclusion
    target_conclusion_id: object
    retained_hypotheses: tuple[object, ...]
    family_checked_result: InertCheckedResult
    family_authority_binding: AnalysisSourceAuthorityContract
    proposition_id: object
    semantic_basis_id: object
    support_id: object
    validation_basis_id: object
    operation_policy_id: object
    qualification_id: object


_MEMBER_SPECIALIZATION_OWNER_ID = _k3c_evaluator_owner_id(
    "afk-fixed-member-specialization"
)
_MEMBER_SPECIALIZATION_QUALIFICATION_ID = analysis_profile_declaration_ref(
    ANALYSIS_THEOREM_SOURCE_VALIDATION_PROFILE,
    ANALYSIS_THEOREM_SOURCE_VALIDATION_PROFILE,
    "analysis.qualification",
    "afk-member-specialization-result",
)


def _fixed_member_hypothesis_context_body(
    retained: Iterable[object],
    correspondence: FamilyInstanceCorrespondenceJudgment,
) -> AnalysisHypothesisContextBodyV0:
    """Canonically union the family frontier with the exact instance DAG."""

    require_family_instance_correspondence_judgment(correspondence)
    retained_goals = canonical_hypotheses(retained)
    if (
        hypothesis_union(retained_goals, correspondence.retained_hypotheses)
        != retained_goals
    ):
        raise AuthorityError(
            "member context does not contain the correspondence frontier"
        )
    graph: dict[bytes, tuple[object, set[bytes]]] = {
        goal.internal_reference(): (goal, set()) for goal in retained_goals
    }
    instance_nodes = correspondence.hypothesis_nodes
    if tuple(node.local_ordinal for node in instance_nodes) != tuple(
        range(len(instance_nodes))
    ):
        raise AuthorityError("family-instance hypothesis ordinals are not exact")
    for node in instance_nodes:
        key = node.goal_id.internal_reference()
        if key not in graph:
            raise AuthorityError("family-instance node is absent from member context")
        dependencies: set[bytes] = set()
        for dependency_ordinal in node.dependency_ordinals:
            if dependency_ordinal >= node.local_ordinal:
                raise AuthorityError("family-instance hypothesis edge is not backward")
            dependency = instance_nodes[dependency_ordinal].goal_id
            dependency_key = dependency.internal_reference()
            if dependency_key == key:
                raise AuthorityError("family-instance hypothesis graph has a self edge")
            dependencies.add(dependency_key)
        graph[key][1].update(dependencies)

    ordered: list[tuple[object, tuple[int, ...]]] = []
    ordinal_by_key: dict[bytes, int] = {}
    remaining = dict(graph)
    while remaining:
        ready = sorted(
            (
                (key, goal, dependencies)
                for key, (goal, dependencies) in remaining.items()
                if dependencies <= ordinal_by_key.keys()
            ),
            key=lambda item: item[0],
        )
        if not ready:
            raise AuthorityError("canonical member hypothesis union contains a cycle")
        key, goal, dependencies = ready[0]
        dependency_ordinals = tuple(
            sorted(ordinal_by_key[dependency] for dependency in dependencies)
        )
        ordinal_by_key[key] = len(ordered)
        ordered.append((goal, dependency_ordinals))
        del remaining[key]
    dependency_keys = {
        dependency for _, dependencies in graph.values() for dependency in dependencies
    }
    root_ordinals = tuple(
        ordinal_by_key[key] for key in ordinal_by_key if key not in dependency_keys
    )
    return AnalysisHypothesisContextBodyV0(
        tuple(
            AnalysisHypothesisNodeV0(ordinal, goal, dependencies)
            for ordinal, (goal, dependencies) in enumerate(ordered)
        ),
        tuple(sorted(root_ordinals)),
    )


def _fixed_member_hypothesis_context_id(
    retained: Iterable[object],
    correspondence: FamilyInstanceCorrespondenceJudgment,
) -> object:
    return _analysis_transport_id(
        "analysis.hypothesis-context",
        _fixed_member_hypothesis_context_body(retained, correspondence),
    )


def _fixed_member_hypothesis_node_requirements(
    retained: Iterable[object],
    correspondence: FamilyInstanceCorrespondenceJudgment,
) -> object:
    body = _fixed_member_hypothesis_context_body(retained, correspondence)
    context_id = _analysis_transport_id("analysis.hypothesis-context", body)
    return k1.DatumSeq(
        tuple(
            k1.DatumVariant(
                0,
                k1.DatumRecord(
                    (
                        (0, _id_datum(context_id, "analysis.hypothesis-context")),
                        (1, k1.Nat(node.local_ordinal)),
                        (2, _id_datum(node.goal_id, "analysis.goal")),
                    )
                ),
            )
            for node in body.nodes
        )
    )


def _fixed_member_question_id(
    correspondence: FamilyInstanceCorrespondenceJudgment,
    conclusion_id: object,
) -> object:
    require_family_instance_correspondence_judgment(correspondence)
    return _analysis_transport_id(
        "analysis.question",
        AnalysisQuestionBodyV0(
            _family_declaration_ref(
                ANALYSIS_TRANSPORT_PROFILE,
                "adaptive-knowledge-extraction-at-fixed-length-q-lt-n",
                owner_profile=ANALYSIS_PROPERTY_PROFILE,
            ),
            correspondence.exact_subjects,
            k1.DatumVariant(
                3,
                k1.DatumRecord(
                    (
                        (
                            0,
                            _id_datum(
                                correspondence.family_definition_id,
                                "analysis.asymptotic-protocol-family",
                            ),
                        ),
                        (
                            1,
                            _id_datum(
                                correspondence.logical_index_id,
                                "analysis.logical-nat-literal",
                            ),
                        ),
                        (
                            2,
                            analysis_domain_body_v0(
                                "analysis.native-subject-projection",
                                _formed_analysis_body(
                                    correspondence.native_subject_projection_id,
                                    "analysis.native-subject-projection",
                                ),
                            ),
                        ),
                        (
                            3,
                            k1.DatumSeq(
                                tuple(
                                    _id_datum(
                                        item,
                                        "analysis.family-instance-role-map",
                                    )
                                    for item in correspondence.role_map_ids
                                )
                            ),
                        ),
                        (
                            4,
                            _id_datum(
                                correspondence.normalization_id,
                                "analysis.pointwise-quantitative-normalization",
                            ),
                        ),
                    )
                ),
            ),
            k1.DatumRecord(
                (
                    (
                        0,
                        _embedded_component_datum(
                            conclusion_id,
                            "analysis.property-conclusion",
                        ),
                    ),
                    (1, k1.Symbol("exact-fixed-member-specialization")),
                )
            ),
        ),
    )


def _fixed_member_goal_id(
    correspondence: FamilyInstanceCorrespondenceJudgment,
    conclusion_id: object,
) -> object:
    return _analysis_transport_id(
        "analysis.goal",
        AnalysisGoalBodyV0(_fixed_member_question_id(correspondence, conclusion_id)),
    )


def _fixed_member_proposition_id(
    correspondence: FamilyInstanceCorrespondenceJudgment,
    conclusion_id: object,
    retained: tuple[object, ...],
) -> object:
    return _analysis_transport_id(
        "analysis.proposition",
        AnalysisPropositionBodyV0(
            _fixed_member_goal_id(correspondence, conclusion_id),
            _fixed_member_hypothesis_context_id(retained, correspondence),
        ),
    )


def _fixed_member_semantic_basis_id(
    family_judgment: AFKFamilyKnowledgeJudgment,
    family_authority_binding: AnalysisSourceAuthorityContract,
    correspondence: FamilyInstanceCorrespondenceJudgment,
    correspondence_authority_binding: AnalysisSourceAuthorityContract,
    transform_id: object,
    conclusion_id: object,
) -> object:
    require_family_instance_correspondence_judgment(correspondence)
    retained = hypothesis_union(
        family_judgment.retained_hypotheses,
        correspondence.retained_hypotheses,
    )
    node_requirements = _fixed_member_hypothesis_node_requirements(
        retained, correspondence
    )
    capability_requirements = tuple(
        k1.DatumVariant(
            1,
            k1.DatumRecord(
                (
                    (
                        0,
                        _id_datum(
                            analysis_capability_requirement_payload_id(
                                binding.capability_requirement
                            ),
                            "analysis.capability-requirement-payload",
                        ),
                    ),
                    (
                        1,
                        _id_datum(
                            portable_source_authority_binding_id(binding),
                            "analysis.portable-source-authority-binding",
                        ),
                    ),
                )
            ),
        )
        for binding in (
            family_authority_binding,
            correspondence_authority_binding,
        )
    )
    return _analysis_transport_id(
        "analysis.semantic-basis",
        AnalysisSemanticBasisBodyV0(
            _family_declaration_ref(
                ANALYSIS_TRANSPORT_PROFILE,
                "adaptive-knowledge-extraction-at-fixed-length-q-lt-n",
                owner_profile=ANALYSIS_PROPERTY_PROFILE,
            ),
            _fixed_member_question_id(correspondence, conclusion_id),
            _native_rule_source(
                ANALYSIS_TRANSPORT_PROFILE,
                ANALYSIS_TRANSPORT_PROFILE,
                "dependent-family-member-specialization",
                k1.DatumRecord(
                    (
                        (
                            0,
                            _id_datum(
                                family_judgment.target_proposition_id,
                                "analysis.proposition",
                            ),
                        ),
                        (
                            1,
                            k1.DatumSeq(
                                tuple(
                                    _id_datum(
                                        item,
                                        "analysis.family-instance-role-map",
                                    )
                                    for item in correspondence.role_map_ids
                                )
                            ),
                        ),
                        (
                            2,
                            _id_datum(
                                correspondence.normalization_id,
                                "analysis.pointwise-quantitative-normalization",
                            ),
                        ),
                    )
                ),
            ),
            k1.DatumSeq((*node_requirements.values, *capability_requirements)),
            complete_read_purpose_requirements(
                concrete_manifest_ids=(correspondence.concrete_manifest_ids[1],),
            ),
            _conclusion_schema_ref(
                ANALYSIS_TRANSPORT_PROFILE,
                ANALYSIS_TRANSPORT_PROFILE,
                "fixed-member-knowledge-conclusion-v0",
            ),
            k1.DatumRecord(
                (
                    (
                        0,
                        _embedded_component_datum(
                            transform_id,
                            "analysis.quantitative-transform",
                        ),
                    ),
                    (
                        1,
                        _embedded_component_datum(
                            conclusion_id,
                            "analysis.property-conclusion",
                        ),
                    ),
                )
            ),
        ),
    )


def _fixed_member_support_id(
    family_checked_result: InertCheckedResult,
    family_authority_binding: AnalysisSourceAuthorityContract,
    correspondence_checked_result: InertCheckedResult,
    correspondence_authority_binding: AnalysisSourceAuthorityContract,
    correspondence: FamilyInstanceCorrespondenceJudgment,
    proposition_id: object,
    semantic_basis_id: object,
    retained: tuple[object, ...],
) -> object:
    result_bindings = (
        (family_checked_result, family_authority_binding),
        (correspondence_checked_result, correspondence_authority_binding),
    )
    context_body = _fixed_member_hypothesis_context_body(retained, correspondence)
    theorem_truth_goal = theorem_truth_goal_id(_AFK_GLOBAL_THEOREM_SCHEMA)
    assumed_node_bindings = k1.DatumSeq(
        tuple(
            k1.DatumRecord(
                (
                    (0, k1.Nat(node.local_ordinal)),
                    (
                        1,
                        k1.DatumRecord(
                            (
                                (0, _id_datum(node.goal_id, "analysis.goal")),
                                (1, k1.DatumVariant(0, k1.UNIT)),
                                (
                                    2,
                                    k1.DatumVariant(
                                        1,
                                        _id_datum(
                                            AFK_V2_THM4_SOURCE_VALIDATION,
                                            "analysis.theorem-source-validation",
                                        ),
                                    )
                                    if node.goal_id == theorem_truth_goal
                                    else k1.DatumVariant(0, k1.UNIT),
                                ),
                            )
                        ),
                    ),
                )
            )
            for node in context_body.nodes
        )
    )
    return _analysis_support_instantiation_id(
        profile=ANALYSIS_THEOREM_SOURCE_VALIDATION_PROFILE,
        semantic_basis_id=semantic_basis_id,
        proposition_id=proposition_id,
        assumed_goals=retained,
        theorem_validations={theorem_truth_goal: AFK_V2_THM4_SOURCE_VALIDATION},
        non_hypothesis_premise_bindings=k1.DatumSeq(
            tuple(
                k1.DatumRecord(
                    (
                        (0, k1.Nat(ordinal)),
                        (
                            1,
                            k1.DatumRecord(
                                (
                                    (
                                        0,
                                        _id_datum(
                                            checked_result_coordinate_id(result),
                                            "analysis.checked-result-coordinate",
                                        ),
                                    ),
                                    (
                                        1,
                                        _id_datum(
                                            portable_source_authority_binding_id(
                                                binding
                                            ),
                                            "analysis.portable-source-authority-binding",
                                        ),
                                    ),
                                )
                            ),
                        ),
                    )
                )
                for ordinal, (result, binding) in enumerate(result_bindings)
            )
        ),
        assumed_hypothesis_node_bindings=assumed_node_bindings,
        source_support_bindings=k1.DatumSeq(
            (
                _id_datum(
                    correspondence.concrete_support_coordinates[1],
                    "analysis.source-support",
                ),
            )
        ),
    )


def _fixed_member_judgment_id(
    correspondence: FamilyInstanceCorrespondenceJudgment,
    proposition_id: object,
    transform_id: object,
    formula_ids: tuple[object, ...],
    conclusion_id: object,
    semantic_basis_id: object,
    support_id: object,
    validation_basis_id: object,
    operation_policy_id: object,
    retained: tuple[object, ...],
    source_policy_closure: tuple[object, ...],
) -> object:
    return _analysis_judgment_record_id(
        profile=ANALYSIS_THEOREM_SOURCE_VALIDATION_PROFILE,
        proposition_id=proposition_id,
        exact_family_conclusion=k1.DatumRecord(
            (
                (
                    0,
                    _id_datum(
                        correspondence.family_definition_id,
                        "analysis.asymptotic-protocol-family",
                    ),
                ),
                (1, k1.Nat(correspondence.logical_index)),
                (
                    2,
                    _embedded_component_datum(
                        correspondence.concrete_member_subject_id,
                        "analysis.concrete-family-member-subject",
                    ),
                ),
                (
                    3,
                    _embedded_component_datum(
                        conclusion_id,
                        "analysis.property-conclusion",
                    ),
                ),
            )
        ),
        inherited_hypothesis_context_id=_fixed_member_hypothesis_context_id(
            retained, correspondence
        ),
        typed_quantitative_result=k1.DatumRecord(
            (
                (
                    0,
                    _embedded_component_datum(
                        transform_id,
                        "analysis.quantitative-transform",
                    ),
                ),
                (
                    1,
                    k1.DatumSeq(
                        tuple(
                            _id_datum(item, "analysis.quantitative-formula")
                            for item in formula_ids
                        )
                    ),
                ),
            )
        ),
        semantic_basis_id=semantic_basis_id,
        support_id=support_id,
        validation_basis_id=validation_basis_id,
        qualification=_MEMBER_SPECIALIZATION_QUALIFICATION_ID,
        operation_policy_id=operation_policy_id,
        source_policy_closure=source_policy_closure,
    )


@_with_family_derivation_scope
def specialize_afk_family_judgment(
    family_capability: AFKFamilyKnowledgeCapability,
    correspondence: ConcreteFamilyInstanceCorrespondence | None,
) -> AttemptOutcome:
    try:
        require_family_knowledge_capability(family_capability)
        family_judgment = family_capability.judgment
        if correspondence is None:
            return AttemptOutcome(
                AttemptKind.CANNOT_ANSWER,
                detail="exact family/member correspondence is unavailable",
            )
        require_concrete_family_instance_correspondence(correspondence)
        correspondence_judgment = correspondence.judgment
        if (
            correspondence_judgment.family_definition_id
            != family_judgment.family_definition_id
        ):
            return AttemptOutcome(
                AttemptKind.REFUSED,
                detail="pointwise correspondence belongs to another family",
            )
        transform = afk_quantitative_transform(
            k=2,
            challenge_count=family_judgment.family.challenge_cardinality,
            subject_id=correspondence_judgment.concrete_member_subject_id,
        )
        formula_map = afk_quantitative_formula_ids(transform)
        formula_ids = (
            formula_map["knowledge-error"],
            formula_map["knowledge-success-lower-bound"],
            formula_map["lemma4-transcript-extraction-lower-bound"],
            formula_map["expected-adversary-calls-upper-bound"],
        )
        conclusion = afk_knowledge_soundness_conclusion(transform)
        transform_id = afk_quantitative_transform_id(transform)
        conclusion_id = afk_target_conclusion_id(conclusion)
        retained = hypothesis_union(
            family_judgment.retained_hypotheses,
            correspondence_judgment.retained_hypotheses,
        )
        proposition_id = _fixed_member_proposition_id(
            correspondence_judgment, conclusion_id, retained
        )
        semantic_basis_id = _fixed_member_semantic_basis_id(
            family_judgment,
            family_capability.authority_binding,
            correspondence_judgment,
            correspondence.authority_binding,
            transform_id,
            conclusion_id,
        )
        support_id = _fixed_member_support_id(
            family_capability.checked_result,
            family_capability.authority_binding,
            correspondence.checked_result,
            correspondence.authority_binding,
            correspondence_judgment,
            proposition_id,
            semantic_basis_id,
            retained,
        )
        validation_basis_id = analysis_validation_basis_id(
            (), profile=ANALYSIS_THEOREM_SOURCE_VALIDATION_PROFILE
        )
        operation_policy_id = _analysis_operation_policy_id(
            proposition_id,
            (),
            profile=ANALYSIS_THEOREM_SOURCE_VALIDATION_PROFILE,
        )
        source_policy_closure = derive_source_policy_closure(
            (
                family_capability.authority_binding,
                correspondence.authority_binding,
            )
        )
        judgment_id = _fixed_member_judgment_id(
            correspondence_judgment,
            proposition_id,
            transform_id,
            formula_ids,
            conclusion_id,
            semantic_basis_id,
            support_id,
            validation_basis_id,
            operation_policy_id,
            retained,
            source_policy_closure,
        )
        return _affirmative(
            ConcreteMemberKnowledgeJudgment(
                judgment_id=judgment_id,
                family_judgment=family_judgment,
                correspondence_judgment=correspondence_judgment,
                family_judgment_id=family_judgment.judgment_id,
                correspondence_checked_result=correspondence.checked_result,
                correspondence_authority_binding=correspondence.authority_binding,
                correspondence_retained_hypotheses=(
                    correspondence_judgment.retained_hypotheses
                ),
                family_definition_id=correspondence_judgment.family_definition_id,
                logical_index=correspondence_judgment.logical_index,
                native_statement_length=(
                    correspondence_judgment.native_statement_length
                ),
                native_subject_projection_id=(
                    correspondence_judgment.native_subject_projection_id
                ),
                concrete_member_subject_id=(
                    correspondence_judgment.concrete_member_subject_id
                ),
                quantitative_transform=transform,
                quantitative_transform_id=transform_id,
                quantitative_formula_ids=formula_ids,
                target_conclusion=conclusion,
                target_conclusion_id=conclusion_id,
                retained_hypotheses=retained,
                family_checked_result=family_capability.checked_result,
                family_authority_binding=family_capability.authority_binding,
                proposition_id=proposition_id,
                semantic_basis_id=semantic_basis_id,
                support_id=support_id,
                validation_basis_id=validation_basis_id,
                operation_policy_id=operation_policy_id,
                qualification_id=_MEMBER_SPECIALIZATION_QUALIFICATION_ID,
            )
        )
    except AuthorityError as error:
        return AttemptOutcome(AttemptKind.REFUSED, detail=str(error))
    except (AnalysisError, k2.ModelError, k3.K3Error) as error:
        return AttemptOutcome(AttemptKind.MALFORMED, detail=str(error))


@_with_family_derivation_scope
def require_concrete_member_judgment(
    judgment: ConcreteMemberKnowledgeJudgment,
) -> None:
    if type(judgment) is not ConcreteMemberKnowledgeJudgment:
        raise AuthorityError("concrete member judgment is forged or detached")
    require_family_knowledge_judgment(judgment.family_judgment)
    require_family_instance_correspondence_judgment(judgment.correspondence_judgment)
    family = judgment.family_judgment
    source_bindings = (
        family.applicability_authority_binding,
        family.source_authority_binding,
        family.theorem_truth_authority_binding,
    )
    family_result_coordinates = (
        checked_result_coordinate_id(family.applicability_checked_result),
        checked_result_coordinate_id(family.source_checked_result),
        checked_result_coordinate_id(family.theorem_truth_checked_result),
    )
    expected_family_support = _family_transport_support_id(
        family_result_coordinates,
        family.retained_hypotheses,
        family.semantic_basis_id,
        family.target_proposition_id,
        source_bindings,
    )
    expected_family_result = InertCheckedResult(
        family.judgment_id,
        family.target_proposition_id,
        family.semantic_basis_id,
        expected_family_support,
        family.validation_basis_id,
        _FAMILY_TRANSPORT_QUALIFICATION_ID,
        AttemptKind.AFFIRMATIVE,
        ANALYSIS_THEOREM_SOURCE_VALIDATION_PROFILE,
    )
    expected_family_binding = _make_authority_binding(
        owner_id=_ANALYSIS_TRANSPORT_OWNER_ID,
        checked_result=expected_family_result,
        consumer_label="afk-member-specialization",
        purpose_label="afk-family-target-specialization",
        immediate_policy_ids=(
            _analysis_operation_policy_id(
                family.target_proposition_id,
                (
                    (
                        "afk-member-specialization",
                        ("afk-family-target-specialization",),
                    ),
                ),
                profile=ANALYSIS_THEOREM_SOURCE_VALIDATION_PROFILE,
            ),
        ),
        transitive_policy_ids=derive_source_policy_closure(source_bindings),
    )
    correspondence = judgment.correspondence_judgment
    (
        expected_correspondence_judgment,
        expected_correspondence_result,
        expected_correspondence_binding,
    ) = _family_instance_correspondence_components(
        _coordinates_from_correspondence_judgment(correspondence)
    )
    if (
        judgment.family_checked_result != expected_family_result
        or judgment.family_authority_binding != expected_family_binding
        or correspondence != expected_correspondence_judgment
        or judgment.correspondence_checked_result != expected_correspondence_result
        or judgment.correspondence_authority_binding != expected_correspondence_binding
        or judgment.correspondence_retained_hypotheses
        != correspondence.retained_hypotheses
        or judgment.family_definition_id != correspondence.family_definition_id
        or judgment.logical_index != correspondence.logical_index
        or judgment.native_statement_length != correspondence.native_statement_length
        or judgment.native_subject_projection_id
        != correspondence.native_subject_projection_id
        or judgment.concrete_member_subject_id
        != correspondence.concrete_member_subject_id
    ):
        raise AuthorityError("concrete member source authority was substituted")
    correspondence_hypotheses = canonical_hypotheses(
        judgment.correspondence_retained_hypotheses
    )
    if correspondence_hypotheses != judgment.correspondence_retained_hypotheses:
        raise AuthorityError("concrete member support is not canonical")
    expected_transform = afk_quantitative_transform(
        k=2,
        challenge_count=judgment.family_judgment.family.challenge_cardinality,
        subject_id=judgment.concrete_member_subject_id,
    )
    expected_formula_map = afk_quantitative_formula_ids(expected_transform)
    expected_formula_ids = (
        expected_formula_map["knowledge-error"],
        expected_formula_map["knowledge-success-lower-bound"],
        expected_formula_map["lemma4-transcript-extraction-lower-bound"],
        expected_formula_map["expected-adversary-calls-upper-bound"],
    )
    expected_conclusion = afk_knowledge_soundness_conclusion(expected_transform)
    retained = hypothesis_union(
        family.retained_hypotheses,
        correspondence_hypotheses,
    )
    expected_conclusion_id = afk_target_conclusion_id(expected_conclusion)
    expected_transform_id = afk_quantitative_transform_id(expected_transform)
    expected_proposition = _fixed_member_proposition_id(
        correspondence, expected_conclusion_id, retained
    )
    expected_basis = _fixed_member_semantic_basis_id(
        family,
        expected_family_binding,
        correspondence,
        expected_correspondence_binding,
        expected_transform_id,
        expected_conclusion_id,
    )
    expected_support = _fixed_member_support_id(
        expected_family_result,
        expected_family_binding,
        expected_correspondence_result,
        expected_correspondence_binding,
        correspondence,
        expected_proposition,
        expected_basis,
        retained,
    )
    expected_validation = analysis_validation_basis_id(
        (), profile=ANALYSIS_THEOREM_SOURCE_VALIDATION_PROFILE
    )
    expected_policy = _analysis_operation_policy_id(
        expected_proposition,
        (),
        profile=ANALYSIS_THEOREM_SOURCE_VALIDATION_PROFILE,
    )
    if (
        judgment.family_judgment_id != family.judgment_id
        or type(judgment.logical_index) is not int
        or judgment.logical_index < 1
        or type(judgment.native_statement_length) is not int
        or judgment.native_statement_length < 0
        or judgment.quantitative_transform != expected_transform
        or judgment.quantitative_transform_id != expected_transform_id
        or judgment.quantitative_formula_ids != expected_formula_ids
        or judgment.target_conclusion != expected_conclusion
        or judgment.target_conclusion_id != expected_conclusion_id
        or retained != judgment.retained_hypotheses
        or judgment.proposition_id != expected_proposition
        or judgment.semantic_basis_id != expected_basis
        or judgment.support_id != expected_support
        or judgment.validation_basis_id != expected_validation
        or judgment.operation_policy_id != expected_policy
        or judgment.qualification_id != _MEMBER_SPECIALIZATION_QUALIFICATION_ID
    ):
        raise AuthorityError("concrete member judgment is forged or detached")
    expected_judgment_id = _fixed_member_judgment_id(
        correspondence,
        expected_proposition,
        expected_transform_id,
        expected_formula_ids,
        expected_conclusion_id,
        expected_basis,
        expected_support,
        expected_validation,
        expected_policy,
        retained,
        derive_source_policy_closure(
            (expected_family_binding, expected_correspondence_binding)
        ),
    )
    if judgment.judgment_id != expected_judgment_id:
        raise AuthorityError("concrete member judgment identity was substituted")


def selected_fixed_member_fixture() -> tuple[
    FreshFsRelationSource, ExperimentModel, ExperimentModel
]:
    """Return the only executable member anchor; this is not a family proof."""

    source = _SCHNORR_PINNED_SOURCE
    source_model = fresh_special_soundness_model(k=2, challenge_count=8)
    target_model = adaptive_rom_knowledge_model(k=2, challenge_count=8)
    return source, source_model, target_model
