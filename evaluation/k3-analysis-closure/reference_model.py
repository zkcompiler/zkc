"""Bounded executable research model for K3-C Analysis closure.

This module imports the K3-B dependent-surface model, and through it the K2
Protocol/Fiat--Shamir and K1 executable-foundation models.  It adds only the
minimum Analysis-owned consumer structures needed to pressure source ingress,
strategy/experiment identity, relation-bound property formation, theorem
applicability, property transport, and explicit loss-export occurrence ingress.

The model is deliberately finite.  Fixture theorem rules remain explicit
hypotheses.  No semantic-reference label, run record, replay result, or
structural Fresh/Fiat--Shamir pair is treated as proof of a property.
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from enum import Enum
from fractions import Fraction
import hashlib
import importlib.util
from pathlib import Path
import re
import sys
from typing import Iterable


# ---------------------------------------------------------------------------
# Exact K3-B/K2/K1 imports
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
        raise ImportError(f"cannot load K3-B reference model from {_K3_PATH}")
    k3 = importlib.util.module_from_spec(_spec)
    sys.modules[_K3_NAME] = k3
    _spec.loader.exec_module(k3)

k2 = k3.k2
k1 = k3.k1


# ---------------------------------------------------------------------------
# Common finite helpers and refusal classes
# ---------------------------------------------------------------------------


MAX_SOURCE_READS = 128
MAX_QUANTIFIERS = 16
MAX_HYPOTHESES = 64
MAX_LOSS_USES = 128
MAX_EXPRESSION_NODES = 256


class AnalysisError(ValueError):
    """Base class for one malformed or forged K3-C input."""


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


def _ascii(text: str, what: str) -> str:
    if (
        type(text) is not str
        or not text
        or any(ord(ch) < 0x21 or ord(ch) > 0x7E for ch in text)
    ):
        raise AnalysisError(f"{what} must be nonempty printable ASCII without spaces")
    return text


def _id_datum(
    identifier: object,
    expected_subject_kind: str | tuple[str, ...] | None = None,
) -> object:
    if type(identifier) is not k1.TypedContentId:
        raise AnalysisError("semantic reference must be one exact K1 TypedContentId")
    identifier.__post_init__()
    if identifier.semantic_regime != k1.SEMANTIC_REGIME_ID:
        raise AnalysisError("semantic reference belongs to an unsupported regime")
    if expected_subject_kind is not None:
        expected = (
            (expected_subject_kind,)
            if type(expected_subject_kind) is str
            else expected_subject_kind
        )
        if identifier.subject_kind not in expected:
            raise AnalysisError(
                f"semantic reference has kind {identifier.subject_kind!r}; "
                f"expected one of {expected!r}"
            )
    return k1.BytesValue(identifier.internal_reference())


def _analysis_id(subject_kind: str, body: object) -> object:
    return k1.content_id(
        subject_kind,
        k1.encode_datum(body),
        semantic_regime=k1.SEMANTIC_REGIME_ID,
    )


def fixture_ref(subject_kind: str, label: str) -> object:
    """Create an inert K1 identity for a fixture meaning, never authority."""

    return _analysis_id(
        subject_kind,
        k1.DatumRecord(((0, k1.Symbol(_ascii(label, "fixture label"))),)),
    )


class AttemptKind(str, Enum):
    AFFIRMATIVE = "affirmative"
    UNSUPPORTED = "unsupported"
    CANNOT_ANSWER = "cannot-answer"
    MALFORMED = "malformed"
    REFUSED = "refused"


@dataclass(frozen=True)
class AttemptOutcome:
    kind: AttemptKind
    value: object | None = None
    detail: str = ""


def _affirmative(value: object) -> AttemptOutcome:
    return AttemptOutcome(AttemptKind.AFFIRMATIVE, value)


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
                        _id_datum(expression.resource_dimension_id)
                        if expression.resource_dimension_id is not None
                        else k1.DatumVariant(0, k1.DatumRecord(())),
                    ),
                    (
                        3,
                        _id_datum(expression.query_abi_id)
                        if expression.query_abi_id is not None
                        else k1.DatumVariant(0, k1.DatumRecord(())),
                    ),
                    (
                        4,
                        _id_datum(expression.subject_id)
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
                        _id_datum(expression.resource_dimension_id)
                        if expression.resource_dimension_id is not None
                        else k1.DatumVariant(0, k1.DatumRecord(())),
                    ),
                    (
                        3,
                        _id_datum(expression.query_abi_id)
                        if expression.query_abi_id is not None
                        else k1.DatumVariant(0, k1.DatumRecord(())),
                    ),
                    (
                        4,
                        _id_datum(expression.subject_id)
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
                        _id_datum(
                            expression.resource_dimension_id,
                            "analysis.resource-dimension",
                        ),
                    ),
                    (
                        5,
                        _id_datum(
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
                    _id_datum(
                        expression.experiment_body_id, "analysis.experiment-body"
                    ),
                ),
                (2, _id_datum(expression.event_id, "analysis.event-profile")),
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
                    _id_datum(
                        expression.query_resource_dimension_id,
                        "analysis.resource-dimension",
                    ),
                ),
                (7, _id_datum(expression.query_abi_id, "analysis.oracle-query-abi")),
                (8, _id_datum(expression.subject_id)),
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
            or n_domain[2] != "N-is-exactly-8-and-at-least-two"
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
        k1.DatumRecord(
            (
                (0, k1.Symbol(profile.result_sort.value)),
                (1, _id_datum(profile.exact_subject_id)),
                (
                    2,
                    k1.DatumSeq(
                        tuple(
                            k1.DatumRecord(
                                (
                                    (0, k1.Symbol(name)),
                                    (1, k1.Symbol(sort_name)),
                                )
                            )
                            for name, sort_name in profile.parameter_schema
                        )
                    ),
                ),
                (
                    3,
                    k1.DatumSeq(
                        tuple(
                            k1.DatumRecord(
                                (
                                    (0, k1.Symbol(name)),
                                    (
                                        1,
                                        _id_datum(
                                            domain_id,
                                            "analysis.formula-parameter-domain",
                                        ),
                                    ),
                                )
                            )
                            for name, domain_id in profile.parameter_domain_ids
                        )
                    ),
                ),
                (4, _symbol_seq(profile.implicit_dependencies)),
                (5, _symbol_seq(profile.declared_independence)),
                (6, quantitative_body(profile.expression)),
            )
        ),
    )
    key = identifier.internal_reference()
    prior_sort = _FORMULA_RESULT_SORT_REGISTRY.get(key)
    if prior_sort is not None and prior_sort is not profile.result_sort:
        raise QuantitativeError("formula identity was registered at two result sorts")
    _FORMULA_RESULT_SORT_REGISTRY[key] = profile.result_sort
    return identifier


def resource_dimension_id(dimension: "ResourceDimension") -> object:
    if type(dimension) is not ResourceDimension:
        raise QuantitativeError("resource dimension has the wrong shape")
    return _analysis_id(
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
    if (
        _FORMULA_RESULT_SORT_REGISTRY.get(rhs_key)
        is not QuantitativeSort.EXPECTED_COUNT_ADVERSARY_RUNNING_ALGORITHM
        or _FORMULA_ROLE_REGISTRY.get(rhs_key, (None, None))[0]
        != "expected-adversary-calls-upper-bound"
    ):
        raise QuantitativeError(
            "expected-invocation bound needs the registered expected-call formula role"
        )
    if bound.comparator != "less-than-or-equal":
        raise QuantitativeError("expected-invocation bound needs <= orientation")
    return _analysis_id(
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


def _source_read_body(read: SourceRead) -> object:
    if type(read) is not SourceRead or type(read.kind) is not SourceFactKind:
        raise SourceIngressError("source read has an unknown exact shape")
    _ascii(read.coordinate, "source-read coordinate")
    return k1.DatumRecord(
        (
            (0, k1.Symbol(read.kind.value)),
            (1, _id_datum(read.owner_id)),
            (2, k1.Symbol(read.coordinate)),
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


def source_manifest_id(manifest: SourceManifest) -> object:
    admit_source_manifest(manifest)
    return _analysis_id(
        "analysis.semantic-read-manifest",
        k1.DatumSeq(tuple(_source_read_body(read) for read in manifest.reads)),
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
            "Protocol Analysis source disagrees with K2/K3 derivation"
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
        raise SourceIngressError("relation property needs one exact K3-B FS case")
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
                    f"{edge.instance}:{edge.slot}:{edge.source.scope}:{edge.source.input_name}",
                )
            )
    for edge in binding.binding.claim_edges:
        reads.append(
            SourceRead(
                SourceFactKind.CLAIM_EDGE,
                binding.binding_id,
                f"{edge.instance}:{edge.claim.origin.value}:{edge.claim.claim}",
            )
        )
    for edge in plan_binding.binding.witness_edges:
        reads.append(
            SourceRead(
                SourceFactKind.WITNESS_EDGE,
                plan_binding.binding_id,
                f"{edge.slot}:{edge.witness_surface_key}",
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


def _quantifier_body(quantifier: Quantifier) -> object:
    if (
        type(quantifier) is not Quantifier
        or type(quantifier.kind) is not QuantifierKind
    ):
        raise ExperimentError("experiment quantifier has an unknown shape")
    _ascii(quantifier.binder, "quantifier binder")
    expected_subject = {
        QuantifierKind.EXISTS_DETERMINISTIC_TRANSCRIPT_EXTRACTOR: (
            "analysis.extractor-profile"
        ),
        QuantifierKind.FOR_ALL_VALUE: "analysis.value-domain-profile",
        QuantifierKind.FOR_ALL_QUANTITATIVE_VALUE: (
            "analysis.formula-parameter-domain"
        ),
        QuantifierKind.EXISTS_POSITIVE_POLYNOMIAL: (
            "analysis.positive-polynomial-domain"
        ),
        QuantifierKind.EXISTS_UNIFORM_BLACK_BOX_EXTRACTOR: (
            "analysis.extractor-profile"
        ),
        QuantifierKind.FOR_ALL_ADAPTIVE_PROVERS: "analysis.strategy-interface",
        QuantifierKind.OVER_RANDOM_ORACLE: "analysis.distribution-profile",
    }[quantifier.kind]
    return k1.DatumRecord(
        (
            (0, k1.Symbol(quantifier.kind.value)),
            (1, k1.Symbol(quantifier.binder)),
            (2, _id_datum(quantifier.domain_id, expected_subject)),
        )
    )


def admit_experiment_model(model: ExperimentModel) -> None:
    if type(model) is not ExperimentModel:
        raise ExperimentError("experiment model has the wrong exact shape")
    _id_datum(model.strategy_interface_id, "analysis.strategy-interface")
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
    for quantifier in model.quantifiers:
        _quantifier_body(quantifier)
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
    return _analysis_id(
        "analysis.model-instantiation",
        k1.DatumRecord(
            (
                (
                    0,
                    _id_datum(
                        model.strategy_interface_id, "analysis.strategy-interface"
                    ),
                ),
                (1, k1.Symbol(model.strategy_class.value)),
                (2, k1.Symbol(model.oracle_model.value)),
                (3, k1.Symbol(model.randomness_ownership.value)),
                (
                    4,
                    _id_datum(
                        model.randomness_law_id,
                        "analysis.distribution-profile",
                    ),
                ),
                (5, k1.Symbol(model.scheduling.value)),
                (6, k1.Symbol(model.statement_timing.value)),
                (7, _id_datum(model.setup_profile_id, "analysis.setup-profile")),
                (
                    8,
                    _id_datum(
                        model.execution_body_id,
                        "analysis.experiment-body-bundle",
                    ),
                ),
                (
                    9,
                    _id_datum(
                        model.output_distribution_profile_id,
                        "analysis.output-distribution-profile",
                    ),
                ),
                (10, _id_datum(model.oracle_query_abi_id, "analysis.oracle-query-abi")),
                (11, _id_datum(model.event_profile_id, "analysis.event-profile")),
                (12, _id_datum(model.failure_profile_id, "analysis.failure-profile")),
                (13, _id_datum(model.resource_basis_id, "analysis.resource-basis")),
                (
                    14,
                    k1.DatumSeq(
                        tuple(_quantifier_body(item) for item in model.quantifiers)
                    ),
                ),
                (
                    15,
                    k1.DatumSeq(
                        tuple(
                            k1.DatumRecord(((0, k1.Symbol(name)), (1, k1.Nat(value))))
                            for name, value in model.parameters
                        )
                    ),
                ),
                (16, quantitative_body(model.query_bound)),
            )
        ),
    )


def _symbol_seq(items: tuple[str, ...]) -> object:
    return k1.DatumSeq(
        tuple(k1.Symbol(_ascii(item, "profile coordinate")) for item in items)
    )


@dataclass(frozen=True)
class ValueDomainProfile:
    value_type: str
    domain_predicate: str
    parameters: tuple[tuple[str, int], ...]


def value_domain_profile_id(profile: ValueDomainProfile) -> object:
    if type(profile) is not ValueDomainProfile:
        raise ExperimentError("value-domain profile has the wrong shape")
    return _analysis_id(
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
        k1.DatumRecord(
            (
                (0, _symbol_seq(profile.inputs)),
                (1, _symbol_seq(profile.output)),
                (2, k1.Symbol(_ascii(profile.algorithm, "extractor algorithm"))),
                (3, k1.Symbol(_ascii(profile.resource_law, "extractor resource law"))),
                (4, profile.deterministic),
            )
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
    return _analysis_id(
        "analysis.strategy-interface",
        k1.DatumRecord(
            (
                (0, k1.Symbol(_ascii(profile.role, "strategy role"))),
                (1, _symbol_seq(profile.inputs)),
                (2, _symbol_seq(profile.allowed_views)),
                (3, _symbol_seq(profile.forbidden_views)),
                (4, _symbol_seq(profile.outputs)),
                (5, _symbol_seq(profile.output_constraints)),
                (6, _symbol_seq(profile.dependent_binders)),
                (7, k1.Symbol(_ascii(profile.query_limit, "strategy query limit"))),
                (
                    8,
                    k1.Symbol(
                        _ascii(
                            profile.efficiency_restriction,
                            "strategy efficiency restriction",
                        )
                    ),
                ),
                (9, profile.causal_generation_required),
                (10, profile.total_output_required),
            )
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
        k1.DatumRecord(
            (
                (0, k1.DatumSeq(tuple(k1.Nat(item) for item in profile.values))),
                (1, _fraction_body(profile.mass)),
                (2, k1.Symbol(profile.owner.value)),
                (3, _symbol_seq(profile.independent_from)),
                (4, k1.Symbol(_ascii(profile.access, "randomness access"))),
                (5, profile.hidden_table_from_adversary),
                (6, _symbol_seq(profile.failures)),
                (7, k1.Symbol(_ascii(profile.table_state, "randomness table state"))),
                (
                    8,
                    k1.Symbol(
                        _ascii(
                            profile.existing_index_transition,
                            "existing-index transition",
                        )
                    ),
                ),
                (
                    9,
                    k1.Symbol(
                        _ascii(profile.fresh_index_transition, "fresh-index transition")
                    ),
                ),
                (10, profile.repeat_query_consistent),
                (11, profile.fresh_index_conditionally_uniform),
                (12, profile.adaptive_indices),
            )
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
    return _analysis_id(
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
    return _analysis_id(
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
    return _analysis_id(
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


@dataclass(frozen=True)
class RandomOracleCapabilityContractProfile:
    actor_kind: str
    programming_right: str
    already_defined_point_rule: str
    programmed_value_rule: str
    query_accounting_rule: str
    rerun_right: str
    rerun_table_rule: str
    rerun_prover_state_rule: str
    authority: str
    executable_scope: str


def random_oracle_capability_contract_id(
    profile: RandomOracleCapabilityContractProfile,
) -> object:
    if type(profile) is not RandomOracleCapabilityContractProfile:
        raise ExperimentError("random-oracle capability contract has wrong shape")
    values = tuple(
        _ascii(value, "random-oracle capability contract field")
        for value in (
            profile.actor_kind,
            profile.programming_right,
            profile.already_defined_point_rule,
            profile.programmed_value_rule,
            profile.query_accounting_rule,
            profile.rerun_right,
            profile.rerun_table_rule,
            profile.rerun_prover_state_rule,
            profile.authority,
            profile.executable_scope,
        )
    )
    if values not in (
        (
            "adaptive-prover",
            "forbidden",
            "not-applicable",
            "not-applicable",
            "all-oracle-calls-count-toward-Q",
            "forbidden",
            "not-applicable",
            "not-applicable",
            "analysis-process-admission",
            "symbolic-contract-not-local-transition-execution",
        ),
        (
            "uniform-black-box-extractor",
            "theorem-granted",
            "AFK-v2-Lemma-4-and-Remark-6-govern-existing-points",
            "values-remain-in-exact-C8-random-function-codomain",
            "all-adversary-oracle-calls-count-toward-Q",
            "theorem-granted",
            "AFK-v2-Remark-6-governs-table-coupling-across-reruns",
            "AFK-v2-Remark-2-rewind-fixed-deterministic-prover-state-no-coin-resampling",
            "AssumedTheorem-AFK-v2-Theorem-4-plus-process-correspondence",
            "symbolic-contract-not-local-transition-execution",
        ),
    ):
        raise ExperimentError(
            "random-oracle programming/rerun contract was substituted"
        )
    return _analysis_id(
        "analysis.random-oracle-capability-contract", _symbol_seq(values)
    )


AFK_PROVER_RO_CAPABILITY_CONTRACT_ID = random_oracle_capability_contract_id(
    RandomOracleCapabilityContractProfile(
        "adaptive-prover",
        "forbidden",
        "not-applicable",
        "not-applicable",
        "all-oracle-calls-count-toward-Q",
        "forbidden",
        "not-applicable",
        "not-applicable",
        "analysis-process-admission",
        "symbolic-contract-not-local-transition-execution",
    )
)
AFK_EXTRACTOR_RO_CAPABILITY_CONTRACT_ID = random_oracle_capability_contract_id(
    RandomOracleCapabilityContractProfile(
        "uniform-black-box-extractor",
        "theorem-granted",
        "AFK-v2-Lemma-4-and-Remark-6-govern-existing-points",
        "values-remain-in-exact-C8-random-function-codomain",
        "all-adversary-oracle-calls-count-toward-Q",
        "theorem-granted",
        "AFK-v2-Remark-6-governs-table-coupling-across-reruns",
        "AFK-v2-Remark-2-rewind-fixed-deterministic-prover-state-no-coin-resampling",
        "AssumedTheorem-AFK-v2-Theorem-4-plus-process-correspondence",
        "symbolic-contract-not-local-transition-execution",
    )
)


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
    exact_common = (
        profile.initial_state,
        profile.index_equality,
        profile.repeat_transition,
        profile.fresh_transition,
        profile.query_count_transition,
        profile.bound_binder,
        profile.over_bound,
        profile.executable_scope,
    )
    if exact_common != (
        "empty-finite-map",
        "byte-equality",
        "lookup-return-no-fresh-draw",
        "uniform-sample-insert-return",
        "increment-on-every-call-including-repeat-and-off-image",
        "Q",
        "refuse-before-Q-plus-one-query",
        "symbolic-process-plus-finite-realized-trace-sanity-only",
    ) or profile.capability_contract_id not in (
        AFK_PROVER_RO_CAPABILITY_CONTRACT_ID,
        AFK_EXTRACTOR_RO_CAPABILITY_CONTRACT_ID,
    ):
        raise ExperimentError("lazy random-function process semantics were substituted")
    return _analysis_id(
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
        "analysis.strategy-interface"
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
            else AFK_EXTRACTOR_RO_CAPABILITY_CONTRACT_ID
        )
        if (
            profile.random_function_process.query_abi_id != profile.oracle_query_abi_id
            or profile.random_function_process.capability_contract_id
            != expected_capability_contract_id
        ):
            raise ExperimentError("AFK process capability detached from its actor")
    elif profile.random_function_process is not None:
        raise ExperimentError("non-ROM experiment cannot carry a lazy-RO process")
    return _analysis_id(
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
    _id_datum(profile.strategy_interface_id, "analysis.strategy-interface")
    _id_datum(profile.oracle_query_abi_id, "analysis.oracle-query-abi")
    _id_datum(
        profile.output_distribution_profile_id,
        "analysis.output-distribution-profile",
    )
    _id_datum(profile.extractor_profile_id, "analysis.extractor-profile")
    _id_datum(profile.distribution_law_id, "analysis.distribution-law")
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
                "permit-theorem-granted-lazy-sampling-programming-and-rerun",
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
    return _analysis_id(
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
                    _id_datum(
                        profile.strategy_interface_id, "analysis.strategy-interface"
                    ),
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
                    _id_datum(profile.distribution_law_id, "analysis.distribution-law"),
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
                        "analysis.distribution-law",
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
        "analysis.distribution-law",
        k1.DatumRecord(
            (
                (
                    0,
                    _id_datum(
                        profile.left_experiment_body_id,
                        "analysis.experiment-body",
                    ),
                ),
                (
                    1,
                    _id_datum(
                        profile.right_experiment_body_id,
                        "analysis.experiment-body",
                    ),
                ),
                (2, _symbol_seq(profile.projection)),
                (3, k1.Symbol(profile.equality)),
            )
        ),
    )


def outcome_profile_id(subject_kind: str, profile: OutcomeProfile) -> object:
    if type(profile) is not OutcomeProfile:
        raise ExperimentError("outcome profile has the wrong shape")
    return _analysis_id(
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
    return _analysis_id(
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
    return _analysis_id(
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
        k1.DatumRecord(
            (
                (0, k1.Symbol(_ascii(profile.input_sort, "polynomial input sort"))),
                (1, k1.DatumSeq((k1.Nat(1),))),
                (2, k1.Symbol(_ascii(profile.evaluation, "polynomial evaluation"))),
                (3, k1.Symbol(_ascii(profile.positivity, "polynomial positivity"))),
            )
        ),
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
        k1.DatumRecord(
            (
                (0, _symbol_seq(profile.inputs)),
                (1, _symbol_seq(profile.forbidden_inputs)),
                (2, _symbol_seq(profile.oracle_rights)),
                (3, _symbol_seq(profile.outputs)),
                (4, _symbol_seq(profile.preserves)),
                (5, k1.Symbol(_ascii(profile.success_event, "extractor success"))),
                (
                    6,
                    k1.Symbol(_ascii(profile.termination_law, "extractor termination")),
                ),
                (7, _symbol_seq(profile.resource_dimensions)),
                (
                    8,
                    k1.Symbol(
                        _ascii(profile.prover_rerun_coin_law, "prover rerun coin law")
                    ),
                ),
                (9, profile.uniform_across_provers),
            )
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
    "all-canonical-byte-strings-within-the-imported-K1-finite-term-bound",
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
FRESH_NO_ORACLE_QUERY_DIMENSION_ID = fixture_ref(
    "analysis.resource-dimension", "fresh-no-random-oracle-query-count"
)

AFK_Q_ONE_POLYNOMIAL_PROFILE = PositivePolynomialProfile(
    "logical-nat", (1,), "exact-checked-natural-horner", "constant-at-least-one"
)
AFK_POSITIVE_POLYNOMIAL_Q_ONE = positive_polynomial_profile_id(
    AFK_Q_ONE_POLYNOMIAL_PROFILE
)
AFK_POSITIVE_POLYNOMIAL_DOMAIN_ID = fixture_ref(
    "analysis.positive-polynomial-domain",
    "singleton-positive-polynomial-one-over-logical-nat",
)
AFK_Q_ONE_SUBSTITUTION = fixture_ref(
    "analysis.theorem-substitution", "afk-v2-thm4-q-of-n-equals-one"
)


def schnorr_protocol_family_id(axis: str) -> object:
    if axis not in ("fresh", "fiat-shamir"):
        raise PropertyError("Schnorr protocol-family axis is unsupported")
    return fixture_ref(
        "analysis.protocol-family",
        f"schnorr-prime-order-family:{axis}:parameterized-by-n",
    )


SCHNORR_FRESH_PROTOCOL_FAMILY_ID = schnorr_protocol_family_id("fresh")
SCHNORR_FIAT_SHAMIR_PROTOCOL_FAMILY_ID = schnorr_protocol_family_id("fiat-shamir")
SCHNORR_RELATION_FAMILY_ID = fixture_ref(
    "analysis.relation-family",
    "discrete-log-relation:Y-equals-g-to-x:parameterized-by-n",
)


def schnorr_family_member_relation_id(
    protocol_family_id: object,
    relation_family_id: object = SCHNORR_RELATION_FAMILY_ID,
) -> object:
    _id_datum(protocol_family_id, "analysis.protocol-family")
    _id_datum(relation_family_id, "analysis.relation-family")
    return _analysis_id(
        "analysis.family-member-relation",
        k1.DatumRecord(
            (
                (0, _id_datum(protocol_family_id, "analysis.protocol-family")),
                (1, _id_datum(relation_family_id, "analysis.relation-family")),
                (2, k1.Symbol("forall-n-Member(F,n)-equals-S_n")),
                (3, k1.Symbol("uniform-codecs-relations-verifiers-and-extractors")),
                (4, k1.Symbol("not-established-by-the-fixed-n0-anchor")),
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
    return _analysis_id(
        "analysis.family-member-subject",
        k1.DatumRecord(
            (
                (0, _id_datum(profile.protocol_family_id, "analysis.protocol-family")),
                (1, _id_datum(profile.relation_family_id, "analysis.relation-family")),
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
    """Form one diagnostic member term without claiming native K1/K2 admission."""

    _id_datum(subject_id, "analysis.family-member-subject")
    if type(statement_length) is not int or statement_length < 1:
        raise PropertyError("family-member term needs a positive statement length")
    return _analysis_id(
        "analysis.family-member-term",
        k1.DatumRecord(
            (
                (0, _id_datum(subject_id, "analysis.family-member-subject")),
                (1, k1.Nat(statement_length)),
                (2, k1.Symbol("symbolic-Analysis-member-not-native-K1-K2-artifact")),
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
    ("classical-query", "lazy-sampling", "programming", "rerun"),
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
    return _analysis_id(
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
FRESH_DETERMINISTIC_DISTRIBUTION_LAW = fixture_ref(
    "analysis.distribution-law", "fresh-deterministic-pair-domain-output-law"
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
            "symbolic-process-plus-finite-realized-trace-sanity-only",
        ),
    )


def afk_prover_experiment_body_id(challenge_count: int) -> object:
    return single_experiment_body_id(
        afk_prover_experiment_body_profile(challenge_count)
    )


def afk_adversary_running_algorithm_id(challenge_count: int) -> object:
    """AFK's running algorithm A, not merely the prover P^a interface."""

    return _analysis_id(
        "analysis.adversary-running-algorithm",
        k1.DatumRecord(
            (
                (
                    0,
                    _id_datum(
                        ADAPTIVE_KNOWLEDGE_INTERFACE,
                        "analysis.strategy-interface",
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
            "permit-theorem-granted-lazy-sampling-programming-and-rerun",
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
            AFK_EXTRACTOR_RO_CAPABILITY_CONTRACT_ID,
            "symbolic-process-plus-finite-realized-trace-sanity-only",
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
    return _analysis_id(
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
    return _analysis_id(
        "analysis.extractor-profile",
        k1.DatumRecord(
            (
                (0, k1.Symbol("subject-bound-afk-uniform-black-box-extractor")),
                (1, _id_datum(subject_id)),
                (
                    2,
                    _id_datum(
                        AFK_UNIFORM_BLACK_BOX_EXTRACTOR,
                        "analysis.extractor-profile",
                    ),
                ),
            )
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
    return _analysis_id(
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

    `query_indices` may contain any canonical byte strings, including indices
    outside the verifier image.  A fresh draw is consumed only for the first
    occurrence of each byte-equal index; repeats return the stored value.
    This executes the ideal finite law only and says nothing about SHA-256 or
    the K2 construction correspondence.
    """

    if type(challenge_count) is not int or challenge_count < 2:
        raise ExperimentError("lazy random function requires N >= 2")
    if any(type(index) is not bytes for index in query_indices):
        raise ExperimentError("random-oracle query indices must be exact bytes")
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
    """Retain the current K2 probe's missing owner-issued static views.

    K2 exposes rederivable raw bodies and execution operations, but not the
    durable design's owner-issued static view carriers.  This hypothesis is
    exact to the imported bodies; it does not manufacture that authority.
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
    return _analysis_id(
        "analysis.hypothesis",
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
                        "K2-ProverView-is-runtime-prefix-only-and-does-not-close-these-views"
                    ),
                ),
            )
        ),
    )


def fresh_uniformity_correspondence_hypothesis_id(
    source: FreshFsRelationSource, model: ExperimentModel
) -> object:
    """Exact unproved bridge from K2 Fresh resolution to the selected law."""

    require_fresh_fs_relation_source(source)
    _require_exact_special_soundness_model(model)
    challenge = next(
        item
        for item in source.case.core.schedule
        if item.kind is k2.OccurrenceKind.CHALLENGE
    )
    return _analysis_id(
        "analysis.hypothesis",
        k1.DatumRecord(
            (
                (0, k1.Symbol("assumed-k2-fresh-uniform-independent-law")),
                (
                    1,
                    _id_datum(source.protocol_source.fresh_protocol_id, "pir.protocol"),
                ),
                (2, k1.Symbol(challenge.name)),
                (3, k1.Nat(challenge.challenge_domain.modulus)),
                (
                    4,
                    _id_datum(
                        model.randomness_law_id,
                        "analysis.distribution-profile",
                    ),
                ),
                (
                    5,
                    _id_datum(
                        experiment_model_id(model),
                        "analysis.model-instantiation",
                    ),
                ),
            )
        ),
    )


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
    return fixture_ref("analysis.family-semantic-profile", family.value)


SCHNORR_FIXED_WIDTH_STATEMENT_CODEC_ID = fixture_ref(
    "analysis.codec-profile",
    "canonical-fixed-width-one-octet-schnorr-subgroup-element",
)


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
    return _analysis_id(
        "analysis.family-member-selector",
        k1.DatumRecord(
            (
                (
                    0,
                    _id_datum(
                        protocol_family_id,
                        "analysis.protocol-family",
                    ),
                ),
                (1, _id_datum(SCHNORR_RELATION_FAMILY_ID, "analysis.relation-family")),
                (2, k1.Symbol("fixed-member-n0-bounded-witness-only")),
                (3, k1.Nat(1)),
                (4, k1.Symbol("statement-length-unit-octet")),
                (
                    5,
                    _id_datum(
                        SCHNORR_FIXED_WIDTH_STATEMENT_CODEC_ID,
                        "analysis.codec-profile",
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
    _id_datum(identifier, "analysis.hypothesis")
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


def fixture_hypothesis(label: str) -> object:
    return fixture_ref("analysis.hypothesis", label)


def analysis_question_id(question: AnalysisQuestion) -> object:
    if (
        type(question) is not AnalysisQuestion
        or type(question.family) is not PropertyFamily
    ):
        raise PropertyError("Analysis question has the wrong exact shape")
    _id_datum(question.protocol_family_id, "analysis.protocol-family")
    _id_datum(question.relation_family_id, "analysis.relation-family")
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
    _id_datum(question.model_id, "analysis.model-instantiation")
    _id_datum(question.semantic_read_closure_id, "analysis.semantic-read-manifest")
    for quantifier in question.quantifiers:
        _quantifier_body(quantifier)
    return _analysis_id(
        "analysis.question",
        k1.DatumRecord(
            (
                (
                    0,
                    _id_datum(
                        family_profile_id(question.family),
                        "analysis.family-semantic-profile",
                    ),
                ),
                (1, _id_datum(question.subject_id)),
                (2, k1.Symbol(question.scope)),
                (
                    3,
                    _id_datum(question.protocol_family_id, "analysis.protocol-family"),
                ),
                (
                    4,
                    _id_datum(question.relation_family_id, "analysis.relation-family"),
                ),
                (
                    5,
                    _id_datum(
                        question.fixed_member_selector_id,
                        "analysis.family-member-selector",
                    ),
                ),
                (6, _id_datum(question.protocol_id, "pir.protocol")),
                (
                    7,
                    _id_datum(
                        question.relation_binding_id, "relations.protocol-binding"
                    ),
                ),
                (8, _id_datum(question.model_id, "analysis.model-instantiation")),
                (
                    9,
                    _id_datum(
                        question.semantic_read_closure_id,
                        "analysis.semantic-read-manifest",
                    ),
                ),
                (
                    10,
                    k1.DatumSeq(
                        tuple(_quantifier_body(item) for item in question.quantifiers)
                    ),
                ),
            )
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
                        _id_datum(
                            conclusion.profile_id, "analysis.bounded-property-profile"
                        ),
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
                            "analysis.extractor-algorithm",
                        ),
                    ),
                )
            ),
        )
    if type(conclusion) is AFKKnowledgeSoundnessConclusion:
        _id_datum(conclusion.extractor_profile_id, "analysis.extractor-profile")
        _id_datum(conclusion.distribution_law_id, "analysis.distribution-law")
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
        _id_datum(
            conclusion.expected_invocation_bound_id,
            "analysis.expected-invocation-bound",
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
                            "analysis.distribution-law",
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


def analysis_goal_id(goal: AnalysisGoal) -> object:
    if type(goal) is not AnalysisGoal:
        raise PropertyError("Analysis goal has the wrong exact shape")
    question_id = analysis_question_id(goal.question)
    if goal.question.family is PropertyFamily.K_OUT_OF_N_SPECIAL_SOUNDNESS:
        if type(goal.conclusion) is not SpecialSoundnessConclusion:
            raise PropertyError(
                "special soundness requires an extractor conclusion, not a bound"
            )
    elif (
        goal.question.family is PropertyFamily.ADAPTIVE_NIROP_KNOWLEDGE_SOUNDNESS_Q_LT_N
    ):
        if type(goal.conclusion) is not AFKKnowledgeSoundnessConclusion:
            raise PropertyError(
                "adaptive knowledge soundness requires the exact AFK success law"
            )
        _property_conclusion_body(goal.conclusion)
    return _analysis_id(
        "analysis.goal",
        k1.DatumRecord(
            (
                (0, _id_datum(question_id, "analysis.question")),
                (1, _property_conclusion_body(goal.conclusion)),
            )
        ),
    )


def analysis_proposition_id(proposition: AnalysisProposition) -> object:
    if type(proposition) is not AnalysisProposition:
        raise PropertyError("Analysis proposition has the wrong exact shape")
    goal_id = analysis_goal_id(proposition.goal)
    hypotheses = canonical_hypotheses(proposition.hypotheses)
    if hypotheses != proposition.hypotheses:
        raise PropertyError("Analysis proposition hypotheses are not canonical")
    return _analysis_id(
        "analysis.proposition",
        k1.DatumRecord(
            (
                (0, _id_datum(goal_id, "analysis.goal")),
                (
                    1,
                    k1.DatumSeq(
                        tuple(
                            _id_datum(item, "analysis.hypothesis")
                            for item in hypotheses
                        )
                    ),
                ),
            )
        ),
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
    )
    proposition = AnalysisProposition(
        AnalysisGoal(
            question,
            SpecialSoundnessConclusion(
                profile.profile_id,
                profile.extraction_arity,
                profile.challenge_count,
                profile.extractor_profile_id,
                profile.extractor_algorithm_id,
            ),
        ),
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
    _issuer: object


_JUDGMENT_ISSUER = object()


def schnorr_semantic_basis_id(
    proposition: AnalysisProposition,
) -> object:
    """Rederive the exact basis for the selected conditional Schnorr theorem."""

    proposition_id = analysis_proposition_id(proposition)
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
        k1.DatumRecord(
            (
                (0, k1.Symbol("schnorr-two-special-soundness-conditional-basis")),
                (1, _id_datum(proposition_id, "analysis.proposition")),
                (
                    2,
                    _id_datum(
                        SCHNORR_SPECIAL_SOUNDNESS_RULE_ID,
                        "analysis.semantic-rule",
                    ),
                ),
                (
                    3,
                    _id_datum(
                        SCHNORR_TRANSCRIPT_EXTRACTOR_PROFILE_ID,
                        "analysis.extractor-profile",
                    ),
                ),
                (
                    4,
                    _id_datum(
                        SCHNORR_EXTRACTOR_ALGORITHM,
                        "analysis.extractor-algorithm",
                    ),
                ),
            )
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
    _id_datum(rule.rule_id, "analysis.semantic-rule")
    _id_datum(rule.exact_proposition_id, "analysis.proposition")
    _id_datum(rule.required_hypothesis_id, "analysis.hypothesis")
    _id_datum(rule.semantic_basis_id, "analysis.semantic-basis")
    if rule.exact_proposition_id != proposition_id:
        raise PropertyError("conditional rule names another exact proposition")
    if rule.required_hypothesis_id not in proposition.hypotheses:
        raise PropertyError("conditional theorem assumption was not retained")
    return EstablishedJudgment(
        proposition,
        proposition_id,
        rule.rule_id,
        rule.semantic_basis_id,
        proposition.hypotheses,
        rule,
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
    _id_datum(judgment.rule_id, "analysis.semantic-rule")
    _id_datum(judgment.semantic_basis_id, "analysis.semantic-basis")
    if judgment.rule_id != SCHNORR_SPECIAL_SOUNDNESS_RULE_ID:
        raise PropertyError("property judgment uses no selected fixed-source rule")
    if judgment.semantic_basis_id != schnorr_semantic_basis_id(judgment.proposition):
        raise PropertyError("Schnorr judgment semantic basis was substituted")
    if judgment.conditional_hypotheses != judgment.proposition.hypotheses:
        raise PropertyError("property judgment dropped conditional hypotheses")
    expected_rule = schnorr_special_soundness_rule(judgment.proposition)
    if judgment.derivation_support != expected_rule:
        raise PropertyError("Schnorr judgment derivation support was substituted")


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
            _id_datum(rule.required_hypothesis_id, "analysis.hypothesis")
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
    except (k2.ModelError, k3.K3Error) as error:
        return AttemptOutcome(AttemptKind.MALFORMED, detail=str(error))
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

    The stock K2 Schnorr fixture samples into modulus 11 by bounded rejection.
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


SCHNORR_TWO_SPECIAL_SOUNDNESS = fixture_ref(
    "analysis.property-profile", "schnorr-two-special-soundness"
)
SCHNORR_RELATION_CORRESPONDENCE_ASSUMPTION_PROFILE = fixture_ref(
    "analysis.assumption-profile",
    "schnorr-relation-check-decl-and-grounding-equation-correspondence",
)
SCHNORR_EXTRACTOR_ALGORITHM = _analysis_id(
    "analysis.extractor-algorithm",
    k1.DatumRecord(
        (
            (0, k1.Symbol("schnorr-two-transcript-extractor")),
            (1, k1.Symbol("x=(z-z-prime)/(c-c-prime)-mod-q")),
            (2, k1.Symbol("deterministic")),
            (3, k1.Symbol("polynomial-time-field-arithmetic")),
            (4, k1.Nat(23)),
            (5, k1.Nat(11)),
            (6, k1.Nat(2)),
        )
    ),
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
    ):
        raise PropertyError("Schnorr source profile has invalid finite parameters")
    return k1.DatumRecord(
        (
            (0, _id_datum(SCHNORR_TWO_SPECIAL_SOUNDNESS, "analysis.property-profile")),
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
                    profile.extractor_algorithm_id, "analysis.extractor-algorithm"
                ),
            ),
        )
    )


def _schnorr_profile_id(profile: SchnorrSpecialSoundnessProfile) -> object:
    return _analysis_id(
        "analysis.bounded-property-profile", _schnorr_profile_body(profile)
    )


def schnorr_relation_correspondence_hypothesis_id(
    profile: SchnorrSpecialSoundnessProfile,
) -> object:
    if (
        type(profile) is not SchnorrSpecialSoundnessProfile
        or profile._issuer is not _SCHNORR_PROFILE_ISSUER
        or profile.profile_id != _schnorr_profile_id(profile)
    ):
        raise AuthorityError("Schnorr relation hypothesis lacks an issued profile")
    return _analysis_id(
        "analysis.hypothesis",
        k1.DatumRecord(
            (
                (
                    0,
                    _id_datum(
                        SCHNORR_RELATION_CORRESPONDENCE_ASSUMPTION_PROFILE,
                        "analysis.assumption-profile",
                    ),
                ),
                (
                    1,
                    _id_datum(profile.profile_id, "analysis.bounded-property-profile"),
                ),
            )
        ),
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
    profile = SchnorrSpecialSoundnessProfile(
        fixture_ref("analysis.bounded-property-profile", "pending"),
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


def schnorr_accepts(
    profile: SchnorrSpecialSoundnessProfile, transcript: SchnorrTranscript
) -> bool:
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
    if (
        not 1 <= transcript.statement < profile.group_modulus
        or not 1 <= transcript.commitment < profile.group_modulus
        or not 0 <= transcript.challenge < profile.challenge_count
        or not 0 <= transcript.response < profile.subgroup_order
        or pow(
            transcript.statement,
            profile.subgroup_order,
            profile.group_modulus,
        )
        != 1
        or pow(
            transcript.commitment,
            profile.subgroup_order,
            profile.group_modulus,
        )
        != 1
    ):
        return False
    return (
        pow(
            profile.generator,
            transcript.response % profile.subgroup_order,
            profile.group_modulus,
        )
        == (
            transcript.commitment
            * pow(
                transcript.statement,
                transcript.challenge % profile.subgroup_order,
                profile.group_modulus,
            )
        )
        % profile.group_modulus
    )


def extract_schnorr_witness(
    source: FreshFsRelationSource,
    profile: SchnorrSpecialSoundnessProfile,
    first: SchnorrTranscript,
    second: SchnorrTranscript,
) -> AttemptOutcome:
    """Execute the selected two-transcript algebra, not its universal theorem."""

    try:
        require_schnorr_special_soundness_profile(source, profile)
        if (
            type(first) is not SchnorrTranscript
            or type(second) is not SchnorrTranscript
        ):
            raise PropertyError("Schnorr extraction needs two exact transcripts")
        if first.statement != second.statement or first.commitment != second.commitment:
            return AttemptOutcome(
                AttemptKind.CANNOT_ANSWER,
                detail="transcripts do not share one statement and commitment",
            )
        if first.challenge == second.challenge:
            return AttemptOutcome(
                AttemptKind.CANNOT_ANSWER,
                detail="special-soundness challenges are not distinct",
            )
        if not schnorr_accepts(profile, first) or not schnorr_accepts(profile, second):
            return AttemptOutcome(
                AttemptKind.CANNOT_ANSWER,
                detail="one selected Schnorr transcript is not accepted",
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
        SCHNORR_SPECIAL_SOUNDNESS_RULE_ID,
        proposition_id,
        ASSUMED_SCHNORR_TWO_SPECIAL_SOUNDNESS,
        basis_id,
    )


# ---------------------------------------------------------------------------
# Fresh-to-FS theorem applicability and property transport
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class FixedPublicSetup:
    core_id: object
    construction_id: object
    group_generator: int
    subgroup_order: int
    group_modulus: int
    session: bytes
    application_domain: bytes
    challenge_ordinal: int
    challenge_name: str
    challenge_condition_refs: tuple[tuple[str, str], ...]
    challenge_namespace: bytes
    construction_body: bytes
    fixed_before_prover_and_oracle: bool
    adversary_selected: bool
    oracle_correlated: bool
    mutable_within_instance: bool


def fixed_public_setup_id(setup: FixedPublicSetup) -> object:
    if (
        type(setup) is not FixedPublicSetup
        or any(
            type(item) is not int
            for item in (
                setup.group_generator,
                setup.subgroup_order,
                setup.group_modulus,
                setup.challenge_ordinal,
            )
        )
        or type(setup.session) is not bytes
        or type(setup.application_domain) is not bytes
        or type(setup.challenge_namespace) is not bytes
        or type(setup.construction_body) is not bytes
        or not setup.fixed_before_prover_and_oracle
        or setup.adversary_selected
        or setup.oracle_correlated
        or setup.mutable_within_instance
    ):
        raise TheoremError(
            "AFK fixed public setup is mutable, correlated, or malformed"
        )
    return _analysis_id(
        "analysis.fixed-public-setup",
        k1.DatumRecord(
            (
                (0, _id_datum(setup.core_id, "pir.interactive-core")),
                (
                    1,
                    _id_datum(setup.construction_id, "pir.transcript-construction"),
                ),
                (2, k1.Nat(setup.group_generator)),
                (3, k1.Nat(setup.subgroup_order)),
                (4, k1.Nat(setup.group_modulus)),
                (5, k1.BytesValue(setup.session)),
                (6, k1.BytesValue(setup.application_domain)),
                (7, k1.Nat(setup.challenge_ordinal)),
                (8, k1.Symbol(_ascii(setup.challenge_name, "challenge name"))),
                (
                    9,
                    k1.DatumSeq(
                        tuple(
                            k1.DatumRecord(
                                (
                                    (0, k1.Symbol(_ascii(kind, "reference kind"))),
                                    (1, k1.Symbol(_ascii(name, "reference name"))),
                                )
                            )
                            for kind, name in setup.challenge_condition_refs
                        )
                    ),
                ),
                (10, k1.BytesValue(setup.challenge_namespace)),
                (11, k1.BytesValue(setup.construction_body)),
                (12, setup.fixed_before_prover_and_oracle),
                (13, setup.adversary_selected),
                (14, setup.oracle_correlated),
                (15, setup.mutable_within_instance),
            )
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
        raise TheoremError("bounded query table has a malformed K2 carrier")
    for carrier in carriers:
        if len(carrier) > k1.MAX_CANONICAL_BYTES:
            raise TheoremError("raw K2 query-index encoding exceeds the K1 byte bound")
        try:
            if k1.encode_datum(k1.decode_datum(carrier)) != carrier:
                raise TheoremError("K2 query index is not one canonical datum encoding")
        except k1.CanonicalError as error:
            raise TheoremError(
                "K2 query index is not one canonical datum encoding"
            ) from error
    if len(carriers) != len(set(carriers)):
        raise TheoremError(
            "bounded K2 query carrier is not injective on the selected valid domain"
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
                raise TheoremError("K2 could not generate one bounded query carrier")
            challenge_entry = result.record.entries[setup.challenge_ordinal]
            if (
                challenge_entry.prefix_state is None
                or len(challenge_entry.draw_namespaces) != 1
                or challenge_entry.draw_namespaces[0] != setup.challenge_namespace
            ):
                raise TheoremError(
                    "K2 challenge carrier lacks exact prefix or namespace"
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
    return _analysis_id(
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
    query_encoding_table: tuple[QueryEncodingEntry, ...]
    query_encoding_id: object
    sampler_map: tuple[tuple[str, int, int, int, bool], ...]
    query_index_map: tuple[str, str]
    extractor_algorithm_id: object
    auxiliary_distribution_map: tuple[str, ...]
    forking_semantics: str
    source_model_id: object
    target_model_id: object


def _derive_fixed_setup_provenance(
    source: FreshFsRelationSource,
    challenge_ordinal: int,
    transcript_prefix_map: tuple[tuple[str, tuple[str, ...]], ...],
) -> tuple[bool, bool, bool, bool]:
    """Derive the selected setup timing flags from immutable K2 source data."""

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
    immutable_inputs = all(
        getattr(type(item), "__dataclass_params__", None) is not None
        and type(item).__dataclass_params__.frozen
        for item in (
            source.case.core,
            source.case.construction,
            source.case.invocation,
        )
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
    challenge_occurrence = source.case.core.schedule[challenge_ordinal]
    setup_provenance = _derive_fixed_setup_provenance(
        source, challenge_ordinal, transcript_prefix_map
    )
    setup = FixedPublicSetup(
        source.protocol_source.core_id,
        source.protocol_source.construction_id,
        values["g"],
        values["q"],
        values["p"],
        session,
        source.case.construction.application_domain,
        challenge_ordinal,
        challenge_occurrence.name,
        tuple((ref.kind.value, ref.name) for ref in challenge_occurrence.dependencies),
        challenge_namespace_map[0][2],
        k2.construction_body(source.case.core, source.case.construction),
        *setup_provenance,
    )
    setup_id = fixed_public_setup_id(setup)
    encoding_table = _query_encoding_table(source, setup)
    encoding_id = query_encoding_id(setup, encoding_table)
    return FSCorrespondence(
        source.protocol_source.core_id,
        source.protocol_source.construction_id,
        source.protocol_source.fresh_protocol_id,
        source.protocol_source.fiat_shamir_protocol_id,
        source.fresh_binding.binding_id,
        source.fiat_shamir_binding.binding_id,
        occurrence_map,
        statement_map,
        claim_map,
        witness_map,
        profile.profile_id,
        source.case.construction.application_domain,
        k2.construction_body(source.case.core, source.case.construction),
        source.case.construction.version,
        challenge_namespace_map,
        transcript_prefix_map,
        tuple(
            coordinates[-1]
            for kind, coordinates in transcript_prefix_map
            if kind in {"public-parameter", "statement", "public-context"}
        ),
        setup,
        setup_id,
        encoding_table,
        encoding_id,
        sampler_map,
        ("statement", "commitment"),
        SCHNORR_EXTRACTOR_ALGORITHM,
        ("x", "pi", "aux", "v", "w"),
        "afk-lazy-sampling-reprogramming-not-k2-replay",
        experiment_model_id(source_model),
        experiment_model_id(target_model),
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
        (correspondence.source_model_id, "analysis.model-instantiation"),
        (correspondence.target_model_id, "analysis.model-instantiation"),
        (
            correspondence.source_property_profile_id,
            "analysis.bounded-property-profile",
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
        raise TheoremError("FS correspondence lacks the imported K2 construction body")
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
        raise TheoremError("AFK correspondence lacks the exact K2 prefix map")
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
        raise TheoremError("AFK correspondence has a substituted K2 prefix atom map")
    if correspondence.statement_extension_map != (
        "g",
        "q",
        "p",
        "statement",
        "session",
    ):
        raise TheoremError("AFK logical Statement extension map is incomplete")
    expected_setup_id = fixed_public_setup_id(correspondence.fixed_public_setup)
    if (
        correspondence.fixed_public_setup_id != expected_setup_id
        or correspondence.fixed_public_setup.core_id != correspondence.core_id
        or correspondence.fixed_public_setup.construction_id
        != correspondence.construction_id
        or correspondence.fixed_public_setup.application_domain
        != correspondence.application_domain
        or correspondence.fixed_public_setup.construction_body
        != correspondence.construction_body
    ):
        raise TheoremError("AFK fixed setup was substituted or detached")
    expected_encoding_id = query_encoding_id(
        correspondence.fixed_public_setup,
        correspondence.query_encoding_table,
    )
    if correspondence.query_encoding_id != expected_encoding_id:
        raise TheoremError("bounded K2 query encoding identity was substituted")
    if correspondence.query_index_map != ("statement", "commitment"):
        raise TheoremError("AFK query index must be exactly (statement, commitment)")
    _id_datum(correspondence.extractor_algorithm_id, "analysis.extractor-algorithm")
    if correspondence.auxiliary_distribution_map != ("x", "pi", "aux", "v", "w"):
        raise TheoremError("AFK auxiliary-output map is incomplete")
    if (
        correspondence.forking_semantics
        != "afk-lazy-sampling-reprogramming-not-k2-replay"
    ):
        raise TheoremError("AFK forking semantics was conflated with execution replay")
    return _analysis_id(
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
                        "analysis.bounded-property-profile",
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
                        "analysis.extractor-algorithm",
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
                        correspondence.source_model_id, "analysis.model-instantiation"
                    ),
                ),
                (
                    18,
                    _id_datum(
                        correspondence.target_model_id, "analysis.model-instantiation"
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
                    _id_datum(
                        correspondence.query_encoding_id,
                        "analysis.query-encoding",
                    ),
                ),
            )
        ),
    )


def _assumed_theorem_hypothesis(theorem_schema_id: object) -> object:
    """Form one explicit truth assumption outside theorem applicability."""

    _id_datum(theorem_schema_id, "analysis.theorem-schema")
    return _analysis_id(
        "analysis.hypothesis",
        k1.DatumRecord(
            (
                (0, _id_datum(theorem_schema_id, "analysis.theorem-schema")),
                (1, k1.Symbol("assumed-external-theorem-truth")),
            )
        ),
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
    identifier = _analysis_id(
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


def _afk_formula_parameter_domains(
    challenge_count: int,
    subject_id: object = AFK_THEOREM_SUBJECT_SCHEMA_ID,
) -> dict[str, object]:
    if type(challenge_count) is not int or challenge_count < 2:
        raise QuantitativeError("AFK formula domains require N >= 2")
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
        "N": formula_parameter_domain_id(
            "N",
            "challenge-count",
            f"N-is-exactly-{challenge_count}-and-at-least-two",
            fixture_ref("analysis.challenge-domain", f"selected-C{challenge_count}"),
        ),
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
        if prior_role is not None and prior_role != role_record:
            raise QuantitativeError(
                "one quantitative formula identity was assigned two semantic roles"
            )
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
                    "analysis.positive-polynomial-profile",
                ),
            ),
            (
                11,
                _id_datum(
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
    return _analysis_id(
        "analysis.quantitative-transform", _afk_transform_body(transform)
    )


def afk_target_conclusion_id(
    conclusion: AFKKnowledgeSoundnessConclusion,
) -> object:
    return _analysis_id(
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
SCHNORR_TWO_SPECIAL_SOUNDNESS_THEOREM_ID = _analysis_id(
    "analysis.theorem-schema",
    k1.DatumRecord(
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
                    "analysis.bounded-property-profile",
                ),
            ),
            (
                3,
                _id_datum(
                    experiment_model_id(_SCHNORR_PINNED_MODEL),
                    "analysis.model-instantiation",
                ),
            ),
            (
                4,
                _id_datum(
                    SCHNORR_EXTRACTOR_ALGORITHM,
                    "analysis.extractor-algorithm",
                ),
            ),
            (5, k1.Symbol("truth-is-an-explicit-assumption")),
        )
    ),
)
ASSUMED_SCHNORR_TWO_SPECIAL_SOUNDNESS = _assumed_theorem_hypothesis(
    SCHNORR_TWO_SPECIAL_SOUNDNESS_THEOREM_ID
)
SCHNORR_SPECIAL_SOUNDNESS_RULE_ID = _analysis_id(
    "analysis.semantic-rule",
    k1.DatumRecord(
        (
            (
                0,
                _id_datum(
                    SCHNORR_TWO_SPECIAL_SOUNDNESS_THEOREM_ID,
                    "analysis.theorem-schema",
                ),
            ),
            (1, k1.Symbol("conditional-exact-proposition-elimination")),
        )
    ),
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
    "Remark-2",
    "Remark-6",
    "Definition-4",
    "Definition-10",
    "Definition-11",
    "Lemma-4",
    "Section-6.3-adaptive-construction-immediately-before-Theorem-4",
    "Theorem-4",
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
    return k1.DatumRecord(
        (
            (0, k1.Symbol(_ascii(component.component_kind, "component kind"))),
            (
                1,
                k1.DatumSeq(
                    tuple(
                        k1.Symbol(_ascii(item, "component clause"))
                        for item in component.canonical_clauses
                    )
                ),
            ),
        )
    )


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
    return k1.DatumRecord(
        (
            (0, k1.Nat(operator.ordinal)),
            (
                1,
                k1.DatumSeq(
                    tuple(
                        k1.Symbol(_ascii(item, "local operand sort"))
                        for item in operator.operand_sorts
                    )
                ),
            ),
            (2, k1.Symbol(_ascii(operator.result_sort, "local result sort"))),
            (3, k1.Symbol(_ascii(operator.template_ast, "local operator AST"))),
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
            (0, _template_component_body(source_property)),
            (1, _template_component_body(target_property)),
            (2, _template_component_body(source_experiment)),
            (3, _template_component_body(target_experiment)),
            (
                4,
                k1.DatumSeq(
                    tuple(_template_component_body(item) for item in source_views)
                ),
            ),
            (
                5,
                k1.DatumSeq(tuple(_template_component_body(item) for item in maps)),
            ),
            (
                6,
                k1.DatumSeq(
                    tuple(_template_component_body(item) for item in side_conditions)
                ),
            ),
            (
                7,
                k1.DatumSeq(tuple(_local_operator_body(item) for item in operators)),
            ),
            (8, _template_component_body(transform_program)),
            (9, _template_component_body(conclusion_law)),
        )
    )


# Independent pin for the selected statement body.  Do not derive this constant
# from the body it authenticates: a statement edit must fail closed until a
# reviewer deliberately rotates the literal and the accompanying source record.
AFK_SELECTED_STATEMENT_CONTENT_SHA256 = (
    "f449dd9a41b8d4ef6f4ed7794d68398f81d562e31e828252fabd09ca551ae0bc"
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
        or authority.stable_source_id != "iacr-eprint:2021/1377"
        or authority.bibliographic_version != 2
        or authority.publication_date != "2022-02-16"
        or authority.artifact_media_type != "application/pdf"
        or authority.artifact_sha256 != AFK_PDF_SHA256
        or authority.exact_locators != AFK_PRIMARY_SOURCE_LOCATORS
        or authority.statement_content_sha256 != AFK_SELECTED_STATEMENT_CONTENT_SHA256
        or len(authority.artifact_sha256) != 64
        or len(authority.statement_content_sha256) != 64
    ):
        raise TheoremError(
            "AFK authority must pin the verified PDF and independent statement digest"
        )
    return k1.DatumRecord(
        (
            (0, k1.Symbol(authority.stable_source_id)),
            (1, k1.Nat(authority.bibliographic_version)),
            (2, k1.Symbol(authority.publication_date)),
            (3, k1.Symbol(authority.artifact_media_type)),
            (4, k1.Symbol(authority.artifact_sha256)),
            (
                5,
                k1.DatumSeq(
                    tuple(k1.Symbol(item) for item in authority.exact_locators)
                ),
            ),
            (6, k1.Symbol(authority.statement_content_sha256)),
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
    if (
        type(schema) is not FSTheoremSchema
        or schema._issuer is not _GLOBAL_SCHEMA_ISSUER
        or schema != _expected_global_schema()
    ):
        raise TheoremError(
            "global AFK schema is not the exact family-neutral selected template"
        )
    if tuple(item.ordinal for item in schema.local_operator_catalog) != (0, 1, 2, 3):
        raise TheoremError("AFK global operator catalog must be exactly 0..3")
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
    statement_digest = hashlib.sha256(k1.encode_datum(statement_body)).hexdigest()
    if (
        statement_digest != AFK_SELECTED_STATEMENT_CONTENT_SHA256
        or schema.authority.statement_content_sha256
        != AFK_SELECTED_STATEMENT_CONTENT_SHA256
    ):
        raise TheoremError(
            "AFK statement-content digest does not authenticate its body"
        )
    return k1.DatumRecord(
        (
            (0, _theorem_authority_body(schema.authority)),
            (1, _template_component_body(schema.proof_status)),
            (2, statement_body),
        )
    )


def fs_theorem_schema_id(schema: FSTheoremSchema) -> object:
    return _analysis_id("analysis.theorem-schema", _global_schema_body(schema))


def afk_v2_theorem_schema() -> FSTheoremSchema:
    return _AFK_GLOBAL_THEOREM_SCHEMA


_AFK_GLOBAL_THEOREM_SCHEMA = _expected_global_schema()
AFK_V2_THM4_CLASSICAL_ROM = fs_theorem_schema_id(_AFK_GLOBAL_THEOREM_SCHEMA)
ASSUMED_AFK_V2_THM4 = _assumed_theorem_hypothesis(AFK_V2_THM4_CLASSICAL_ROM)


def theorem_truth_goal_id(schema: FSTheoremSchema) -> object:
    schema_id = fs_theorem_schema_id(schema)
    return _analysis_id(
        "analysis.goal",
        k1.DatumRecord(
            (
                (0, k1.Symbol("external-theorem-truth")),
                (1, _id_datum(schema_id, "analysis.theorem-schema")),
            )
        ),
    )


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


def family_definition_id(family: AFKAsymptoticFamily) -> object:
    return _analysis_id("analysis.asymptotic-family-definition", _family_body(family))


SELECTED_AFK_FAMILY = form_afk_asymptotic_family(
    "selected-prime-order-schnorr-family-N8"
)


def family_ro_index_domain_id(family: AFKAsymptoticFamily) -> object:
    family_id = family_definition_id(family)
    return _analysis_id(
        "analysis.family-ro-index-domain",
        k1.DatumRecord(
            (
                (
                    0,
                    _id_datum(family_id, "analysis.asymptotic-family-definition"),
                ),
                (1, _family_ro_index_domain_body(family.ro_index_domain)),
            )
        ),
    )


def family_query_dimension_id(family: AFKAsymptoticFamily) -> object:
    return _analysis_id(
        "analysis.resource-dimension",
        k1.DatumRecord(
            (
                (
                    0,
                    _id_datum(
                        family_definition_id(family),
                        "analysis.asymptotic-family-definition",
                    ),
                ),
                (1, k1.Symbol("random-oracle-query")),
                (2, k1.Symbol("hard-count-every-call-including-repeat-and-off-image")),
            )
        ),
    )


def family_invocation_dimension_id(family: AFKAsymptoticFamily) -> object:
    return _analysis_id(
        "analysis.resource-dimension",
        k1.DatumRecord(
            (
                (
                    0,
                    _id_datum(
                        family_definition_id(family),
                        "analysis.asymptotic-family-definition",
                    ),
                ),
                (1, k1.Symbol("adversary-running-invocation")),
                (2, k1.Symbol("expected-count")),
            )
        ),
    )


def family_goal_id(family: AFKAsymptoticFamily, role: str) -> object:
    if role not in (
        "source-two-special-soundness",
        "target-adaptive-knowledge-q-lt-N",
    ):
        raise TheoremError("unsupported AFK family goal role")
    return _analysis_id(
        "analysis.goal",
        k1.DatumRecord(
            (
                (
                    0,
                    _id_datum(
                        family_definition_id(family),
                        "analysis.asymptotic-family-definition",
                    ),
                ),
                (1, k1.Symbol(role)),
                (2, k1.Symbol("forall-logical-n")),
                (3, k1.Nat(family.challenge_cardinality)),
                (4, k1.Symbol("relation-bound")),
            )
        ),
    )


def family_experiment_profile_id(family: AFKAsymptoticFamily, axis: str) -> object:
    if axis not in ("fresh-source", "adaptive-fs-target"):
        raise TheoremError("unsupported family experiment axis")
    return _analysis_id(
        "analysis.family-experiment-profile",
        k1.DatumRecord(
            (
                (
                    0,
                    _id_datum(
                        family_definition_id(family),
                        "analysis.asymptotic-family-definition",
                    ),
                ),
                (1, k1.Symbol(axis)),
                (2, k1.Nat(family.challenge_cardinality)),
                (
                    3,
                    _id_datum(
                        family_ro_index_domain_id(family),
                        "analysis.family-ro-index-domain",
                    ),
                ),
                (4, k1.Symbol("symbolic-family-profile-not-native-K1-K2-member")),
            )
        ),
    )


def family_manifest_schema_id(family: AFKAsymptoticFamily, axis: str) -> object:
    if axis not in ("fresh-source", "adaptive-fs-target"):
        raise TheoremError("unsupported family manifest axis")
    return _analysis_id(
        "analysis.family-read-manifest-schema",
        k1.DatumRecord(
            (
                (
                    0,
                    _id_datum(
                        family_definition_id(family),
                        "analysis.asymptotic-family-definition",
                    ),
                ),
                (1, k1.Symbol(axis)),
                (2, k1.Symbol("dependent-family-member-read-schema")),
            )
        ),
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
    operator: LocalOperatorTemplate, challenge_cardinality: int
) -> LocalOperatorAst:
    """Parse the authenticated, deliberately tiny AFK local-expression grammar."""

    text = operator.template_ast
    bounded = re.fullmatch(
        r"bounded-ratio\(\(([A-Za-z_][A-Za-z0-9_]*)\+(\d+)\),N\);"
        r"domain=0<=\1<N",
        text,
    )
    if bounded is not None:
        return (
            "bounded-ratio",
            bounded.group(1),
            int(bounded.group(2)),
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
                AFK_LOCAL_OPERATOR_CATALOG[referenced], challenge_cardinality
            ),
        )
    scaled = re.fullmatch(
        r"scale\(N/\(N-(\d+)\),\(epsilon-operator(\d+)\(Q,N\)\)\)", text
    )
    if scaled is not None:
        decrement = int(scaled.group(1))
        referenced = int(scaled.group(2))
        if decrement >= challenge_cardinality or referenced not in range(
            len(AFK_LOCAL_OPERATOR_CATALOG)
        ):
            raise TheoremError("AFK local scaling template is not total")
        return (
            "scale-difference",
            Fraction(
                challenge_cardinality,
                challenge_cardinality - decrement,
            ),
            _parse_local_operator_template(
                AFK_LOCAL_OPERATOR_CATALOG[referenced], challenge_cardinality
            ),
        )
    expected = re.fullmatch(r"expected-count\(([A-Za-z_][A-Za-z0-9_]*)\+(\d+)\)", text)
    if expected is not None:
        return ("expected-count", expected.group(1), int(expected.group(2)))
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
) -> object:
    family_id = family_definition_id(family)
    q_dimension = family_query_dimension_id(family)
    invocation_dimension = family_invocation_dimension_id(family)
    signatures = {
        0: (
            ("n:LogicalNat", "Q:QueryCount"),
            "Probability",
        ),
        1: (
            ("epsilon:Probability", "n:LogicalNat", "Q:QueryCount"),
            "SignedProbabilityLowerBound",
        ),
        2: (
            ("epsilon:Probability", "n:LogicalNat", "Q:QueryCount"),
            "SignedProbabilityLowerBound",
        ),
        3: (
            ("Q:QueryCount",),
            "ExpectedCount(AdversaryInvocations)",
        ),
    }
    if operator.ordinal not in signatures:
        raise TheoremError("family operator ordinal is outside the AFK catalog")
    parameters, result_sort = signatures[operator.ordinal]
    expression = _instantiate_local_operator_ast(operator, family.challenge_cardinality)
    return k1.DatumRecord(
        (
            (
                0,
                _id_datum(family_id, "analysis.asymptotic-family-definition"),
            ),
            (1, k1.Nat(operator.ordinal)),
            (2, _symbol_seq(parameters)),
            (3, k1.Symbol(result_sort)),
            (4, k1.Symbol(expression)),
            (
                5,
                _id_datum(q_dimension, "analysis.resource-dimension"),
            ),
            (
                6,
                _id_datum(invocation_dimension, "analysis.resource-dimension"),
            ),
            (7, k1.Nat(family.challenge_cardinality)),
            (8, _local_operator_body(operator)),
        )
    )


def family_operator_bindings(
    family: AFKAsymptoticFamily,
) -> tuple[AFKFamilyOperatorBinding, ...]:
    bindings = []
    for operator in AFK_LOCAL_OPERATOR_CATALOG:
        body = _family_formula_body(family, operator)
        formula_id = _analysis_id("analysis.quantitative-formula", body)
        parameters, result_sort = {
            0: (
                ("n:LogicalNat", "Q:QueryCount"),
                "Probability",
            ),
            1: (
                ("epsilon:Probability", "n:LogicalNat", "Q:QueryCount"),
                "SignedProbabilityLowerBound",
            ),
            2: (
                ("epsilon:Probability", "n:LogicalNat", "Q:QueryCount"),
                "SignedProbabilityLowerBound",
            ),
            3: (
                ("Q:QueryCount",),
                "ExpectedCount(AdversaryInvocations)",
            ),
        }[operator.ordinal]
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


def family_operator_binding_id(binding: AFKFamilyOperatorBinding) -> object:
    if (
        type(binding) is not AFKFamilyOperatorBinding
        or binding.local_ordinal not in range(4)
        or binding.source_operator != AFK_LOCAL_OPERATOR_CATALOG[binding.local_ordinal]
        or type(binding.challenge_cardinality) is not int
        or binding.challenge_cardinality < 2
        or binding.instantiated_ast
        != _instantiate_local_operator_ast(
            binding.source_operator,
            binding.challenge_cardinality,
        )
    ):
        raise TheoremError("family operator binding has the wrong exact shape")
    return _analysis_id(
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
                    "analysis.positive-polynomial-profile",
                ),
            ),
            (
                2,
                _id_datum(
                    substitution.positive_polynomial_domain_id,
                    "analysis.positive-polynomial-domain",
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


def family_applicability_premise_ids(
    family: AFKAsymptoticFamily,
) -> tuple[object, ...]:
    family_id = family_definition_id(family)
    roles = (
        "family-denotation",
        "fresh-fs-projection-coherence",
        "finite-constant-challenge-cardinality",
        "public-coin-uniformity-and-independence",
        "efficient-relation-and-verifier",
        "finite-bounded-bitstring-index-and-efficient-encoder",
        "adaptive-lazy-random-function-process-correspondence",
        "framing-sampling-programming-rerun-adequacy",
        "restricted-domain-0-le-Q-lt-N",
    )
    return canonical_hypotheses(
        _analysis_id(
            "analysis.hypothesis",
            k1.DatumRecord(
                (
                    (
                        0,
                        _id_datum(
                            family_id,
                            "analysis.asymptotic-family-definition",
                        ),
                    ),
                    (1, k1.Symbol(role)),
                )
            ),
        )
        for role in roles
    )


def family_source_property_proposition_id(
    family: AFKAsymptoticFamily,
) -> object:
    return _analysis_id(
        "analysis.proposition",
        k1.DatumRecord(
            (
                (
                    0,
                    _id_datum(
                        family_goal_id(family, "source-two-special-soundness"),
                        "analysis.goal",
                    ),
                ),
                (1, k1.Symbol("all-logical-n-source-property")),
                (2, k1.Symbol("not-derived-from-any-fixed-member")),
            )
        ),
    )


def family_target_property_proposition_id(
    family: AFKAsymptoticFamily,
) -> object:
    return _analysis_id(
        "analysis.proposition",
        k1.DatumRecord(
            (
                (
                    0,
                    _id_datum(
                        family_goal_id(family, "target-adaptive-knowledge-q-lt-N"),
                        "analysis.goal",
                    ),
                ),
                (
                    1,
                    k1.DatumSeq(
                        tuple(
                            _id_datum(
                                binding.formula_id,
                                "analysis.quantitative-formula",
                            )
                            for binding in family_operator_bindings(family)
                        )
                    ),
                ),
                (2, k1.Symbol("relation-bound-target-family")),
            )
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


def derive_family_applicability_input(
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
                    "analysis.asymptotic-family-definition",
                ),
            ),
            (2, _id_datum(candidate.source_property_goal_id, "analysis.goal")),
            (3, _id_datum(candidate.target_property_goal_id, "analysis.goal")),
            (
                4,
                _id_datum(
                    candidate.source_experiment_profile_id,
                    "analysis.family-experiment-profile",
                ),
            ),
            (
                5,
                _id_datum(
                    candidate.target_experiment_profile_id,
                    "analysis.family-experiment-profile",
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
            (
                7,
                k1.DatumSeq(
                    tuple(
                        _id_datum(item, "analysis.hypothesis")
                        for item in candidate.applicability_premise_ids
                    )
                ),
            ),
            (8, _parameter_substitution_body(candidate.parameter_substitution)),
            (
                9,
                k1.DatumSeq(
                    tuple(
                        _id_datum(
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
    return _analysis_id(
        "analysis.family-theorem-applicability-input",
        _family_applicability_input_body(candidate),
    )


@dataclass(frozen=True)
class AFKFamilyApplicabilityPort:
    port_id: object
    theorem_schema_id: object
    family: AFKAsymptoticFamily
    family_definition_id: object
    applicability_input: AFKFamilyApplicabilityInput
    applicability_input_id: object
    semantic_basis_id: object
    support_id: object
    retained_hypotheses: tuple[object, ...]
    purpose: str
    _issuer: object


_FAMILY_PORT_ISSUER = object()


def _family_applicability_semantic_basis_id(
    schema: FSTheoremSchema,
    family: AFKAsymptoticFamily,
    candidate: AFKFamilyApplicabilityInput,
) -> object:
    return _analysis_id(
        "analysis.semantic-basis",
        k1.DatumRecord(
            (
                (
                    0,
                    _id_datum(fs_theorem_schema_id(schema), "analysis.theorem-schema"),
                ),
                (
                    1,
                    _id_datum(
                        family_definition_id(family),
                        "analysis.asymptotic-family-definition",
                    ),
                ),
                (
                    2,
                    _id_datum(
                        family_applicability_input_id(candidate),
                        "analysis.family-theorem-applicability-input",
                    ),
                ),
                (
                    3,
                    k1.DatumSeq(
                        tuple(
                            _id_datum(
                                family_operator_binding_id(binding),
                                "analysis.theorem-operator-binding",
                            )
                            for binding in candidate.operator_bindings
                        )
                    ),
                ),
                (4, k1.Symbol("bind-global-local-roles-to-one-abstract-family")),
            )
        ),
    )


def _family_applicability_support_id(
    semantic_basis_id: object, hypotheses: tuple[object, ...]
) -> object:
    return _analysis_id(
        "analysis.support-instantiation",
        k1.DatumRecord(
            (
                (
                    0,
                    _id_datum(semantic_basis_id, "analysis.semantic-basis"),
                ),
                (
                    1,
                    k1.DatumSeq(
                        tuple(
                            _id_datum(item, "analysis.hypothesis")
                            for item in hypotheses
                        )
                    ),
                ),
            )
        ),
    )


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
        if schema != _AFK_GLOBAL_THEOREM_SCHEMA:
            return AttemptOutcome(
                AttemptKind.UNSUPPORTED,
                detail="only the exact verified AFK-v2 global schema is selected",
            )
        expected = derive_family_applicability_input(schema, family)
        selected = expected if candidate is None else candidate
        _family_applicability_input_body(selected)
        if selected != expected:
            return AttemptOutcome(
                AttemptKind.CANNOT_ANSWER,
                detail=(
                    "family, experiment, index-domain, premise, parameter, "
                    "or operator binding does not instantiate the global theorem"
                ),
            )
        hypotheses = canonical_hypotheses(support_hypotheses)
        theorem_truth = _assumed_theorem_hypothesis(schema_id)
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
        basis_id = _family_applicability_semantic_basis_id(schema, family, selected)
        support_id = _family_applicability_support_id(basis_id, hypotheses)
        candidate_id = family_applicability_input_id(selected)
        port_id = _analysis_id(
            "analysis.family-theorem-applicability-port",
            k1.DatumRecord(
                (
                    (
                        0,
                        _id_datum(schema_id, "analysis.theorem-schema"),
                    ),
                    (
                        1,
                        _id_datum(
                            family_definition_id(family),
                            "analysis.asymptotic-family-definition",
                        ),
                    ),
                    (
                        2,
                        _id_datum(
                            candidate_id,
                            "analysis.family-theorem-applicability-input",
                        ),
                    ),
                    (3, _id_datum(basis_id, "analysis.semantic-basis")),
                    (
                        4,
                        _id_datum(support_id, "analysis.support-instantiation"),
                    ),
                )
            ),
        )
        return _affirmative(
            AFKFamilyApplicabilityPort(
                port_id,
                schema_id,
                family,
                family_definition_id(family),
                selected,
                candidate_id,
                basis_id,
                support_id,
                hypotheses,
                "afk-family-property-transport-only",
                _FAMILY_PORT_ISSUER,
            )
        )
    except (AnalysisError, k2.ModelError, k3.K3Error) as error:
        return AttemptOutcome(AttemptKind.MALFORMED, detail=str(error))


def require_family_applicability_port(
    port: AFKFamilyApplicabilityPort,
) -> None:
    if (
        type(port) is not AFKFamilyApplicabilityPort
        or port._issuer is not _FAMILY_PORT_ISSUER
    ):
        raise AuthorityError("family applicability port lacks Analysis issuance")
    expected_outcome = check_afk_family_applicability(
        _AFK_GLOBAL_THEOREM_SCHEMA,
        port.family,
        port.retained_hypotheses,
        candidate=port.applicability_input,
    )
    if (
        expected_outcome.kind is not AttemptKind.AFFIRMATIVE
        or expected_outcome.value.port_id != port.port_id
        or expected_outcome.value != port
    ):
        raise TheoremError("family applicability port was substituted")


@dataclass(frozen=True)
class FamilySourcePropertyCapability:
    family_definition_id: object
    proposition_id: object
    semantic_basis_id: object
    support_id: object
    qualification_id: object
    external_authority_id: object
    retained_hypothesis_id: object
    named_consumer: str
    typed_purpose: str
    _issuer: object


_EXTERNAL_SOURCE_CAP_ISSUER = object()


def assume_external_family_source_capability_for_fixture(
    family: AFKAsymptoticFamily,
    *,
    authority_label: str,
) -> FamilySourcePropertyCapability:
    """Fixture-only external capability; never derived from the n0 extractor."""

    family_id = family_definition_id(family)
    proposition_id = family_source_property_proposition_id(family)
    authority_id = fixture_ref("analysis.external-proof-authority", authority_label)
    hypothesis_id = _analysis_id(
        "analysis.hypothesis",
        k1.DatumRecord(
            (
                (
                    0,
                    _id_datum(proposition_id, "analysis.proposition"),
                ),
                (
                    1,
                    _id_datum(authority_id, "analysis.external-proof-authority"),
                ),
                (2, k1.Symbol("assumed-external-all-n-source-capability")),
            )
        ),
    )
    basis_id = _analysis_id(
        "analysis.semantic-basis",
        k1.DatumRecord(
            (
                (
                    0,
                    _id_datum(family_id, "analysis.asymptotic-family-definition"),
                ),
                (
                    1,
                    _id_datum(authority_id, "analysis.external-proof-authority"),
                ),
                (2, k1.Symbol("external-family-source-proof-basis")),
            )
        ),
    )
    support_id = _analysis_id(
        "analysis.support-instantiation",
        k1.DatumRecord(
            (
                (0, _id_datum(basis_id, "analysis.semantic-basis")),
                (1, _id_datum(hypothesis_id, "analysis.hypothesis")),
            )
        ),
    )
    qualification_id = fixture_ref(
        "analysis.qualification", "conditional-assumed-external-all-n"
    )
    return FamilySourcePropertyCapability(
        family_id,
        proposition_id,
        basis_id,
        support_id,
        qualification_id,
        authority_id,
        hypothesis_id,
        "AFKFamilyTransportConsumer",
        "all-n-two-special-soundness-source",
        _EXTERNAL_SOURCE_CAP_ISSUER,
    )


def require_family_source_capability(
    family: AFKAsymptoticFamily,
    capability: FamilySourcePropertyCapability,
) -> None:
    if (
        type(capability) is not FamilySourcePropertyCapability
        or capability._issuer is not _EXTERNAL_SOURCE_CAP_ISSUER
        or capability.family_definition_id != family_definition_id(family)
        or capability.proposition_id != family_source_property_proposition_id(family)
        or capability.named_consumer != "AFKFamilyTransportConsumer"
        or capability.typed_purpose != "all-n-two-special-soundness-source"
    ):
        raise AuthorityError(
            "source capability is not an exact external all-n family result"
        )
    family_id = family_definition_id(family)
    _id_datum(capability.external_authority_id, "analysis.external-proof-authority")
    expected_hypothesis = _analysis_id(
        "analysis.hypothesis",
        k1.DatumRecord(
            (
                (
                    0,
                    _id_datum(capability.proposition_id, "analysis.proposition"),
                ),
                (
                    1,
                    _id_datum(
                        capability.external_authority_id,
                        "analysis.external-proof-authority",
                    ),
                ),
                (2, k1.Symbol("assumed-external-all-n-source-capability")),
            )
        ),
    )
    expected_basis = _analysis_id(
        "analysis.semantic-basis",
        k1.DatumRecord(
            (
                (
                    0,
                    _id_datum(family_id, "analysis.asymptotic-family-definition"),
                ),
                (
                    1,
                    _id_datum(
                        capability.external_authority_id,
                        "analysis.external-proof-authority",
                    ),
                ),
                (2, k1.Symbol("external-family-source-proof-basis")),
            )
        ),
    )
    expected_support = _analysis_id(
        "analysis.support-instantiation",
        k1.DatumRecord(
            (
                (0, _id_datum(expected_basis, "analysis.semantic-basis")),
                (1, _id_datum(expected_hypothesis, "analysis.hypothesis")),
            )
        ),
    )
    if (
        capability.retained_hypothesis_id != expected_hypothesis
        or capability.semantic_basis_id != expected_basis
        or capability.support_id != expected_support
        or capability.qualification_id
        != fixture_ref("analysis.qualification", "conditional-assumed-external-all-n")
    ):
        raise AuthorityError(
            "external family source capability identity or support was substituted"
        )


@dataclass(frozen=True)
class TheoremTruthTreatment:
    theorem_schema_id: object
    theorem_truth_goal_id: object
    treatment: str
    support_ref: object
    retained_hypothesis_id: object
    _issuer: object


_TRUTH_TREATMENT_ISSUER = object()


def assume_afk_theorem_truth(
    schema: FSTheoremSchema,
) -> TheoremTruthTreatment:
    schema_id = fs_theorem_schema_id(schema)
    goal_id = theorem_truth_goal_id(schema)
    hypothesis_id = _assumed_theorem_hypothesis(schema_id)
    support_ref = _analysis_id(
        "analysis.theorem-truth-support",
        k1.DatumRecord(
            (
                (0, _id_datum(schema_id, "analysis.theorem-schema")),
                (1, _id_datum(goal_id, "analysis.goal")),
                (2, _id_datum(hypothesis_id, "analysis.hypothesis")),
                (3, k1.Symbol("Assumed")),
            )
        ),
    )
    return TheoremTruthTreatment(
        schema_id,
        goal_id,
        "Assumed",
        support_ref,
        hypothesis_id,
        _TRUTH_TREATMENT_ISSUER,
    )


def require_theorem_truth_treatment(
    schema: FSTheoremSchema, treatment: TheoremTruthTreatment
) -> None:
    schema_id = fs_theorem_schema_id(schema)
    expected_goal = theorem_truth_goal_id(schema)
    expected_hypothesis = _assumed_theorem_hypothesis(schema_id)
    expected_support = _analysis_id(
        "analysis.theorem-truth-support",
        k1.DatumRecord(
            (
                (0, _id_datum(schema_id, "analysis.theorem-schema")),
                (1, _id_datum(expected_goal, "analysis.goal")),
                (2, _id_datum(expected_hypothesis, "analysis.hypothesis")),
                (3, k1.Symbol("Assumed")),
            )
        ),
    )
    if (
        type(treatment) is not TheoremTruthTreatment
        or treatment._issuer is not _TRUTH_TREATMENT_ISSUER
        or treatment.theorem_schema_id != schema_id
        or treatment.theorem_truth_goal_id != expected_goal
        or treatment.treatment != "Assumed"
        or treatment.support_ref != expected_support
        or treatment.retained_hypothesis_id != expected_hypothesis
    ):
        raise AuthorityError("theorem truth treatment is missing or belongs elsewhere")


@dataclass(frozen=True)
class AFKFamilyKnowledgeJudgment:
    judgment_id: object
    theorem_schema_id: object
    family: AFKAsymptoticFamily
    family_definition_id: object
    target_proposition_id: object
    operator_bindings: tuple[AFKFamilyOperatorBinding, ...]
    applicability_port: AFKFamilyApplicabilityPort
    applicability_port_id: object
    source_capability: FamilySourcePropertyCapability
    source_capability_id: object
    theorem_truth: TheoremTruthTreatment
    theorem_truth_support_ref: object
    semantic_basis_id: object
    retained_hypotheses: tuple[object, ...]
    _issuer: object


_FAMILY_JUDGMENT_ISSUER = object()


def _family_source_capability_id(
    capability: FamilySourcePropertyCapability,
) -> object:
    return _analysis_id(
        "analysis.family-source-property-capability",
        k1.DatumRecord(
            (
                (
                    0,
                    _id_datum(
                        capability.family_definition_id,
                        "analysis.asymptotic-family-definition",
                    ),
                ),
                (
                    1,
                    _id_datum(capability.proposition_id, "analysis.proposition"),
                ),
                (2, _id_datum(capability.semantic_basis_id, "analysis.semantic-basis")),
                (
                    3,
                    _id_datum(capability.support_id, "analysis.support-instantiation"),
                ),
                (
                    4,
                    _id_datum(
                        capability.external_authority_id,
                        "analysis.external-proof-authority",
                    ),
                ),
                (5, k1.Symbol(capability.typed_purpose)),
            )
        ),
    )


def _family_judgment_basis_id(
    applicability_basis_id: object,
    source_capability_id: object,
    theorem_truth_support_ref: object,
    target_proposition_id: object,
) -> object:
    return _analysis_id(
        "analysis.semantic-basis",
        k1.DatumRecord(
            (
                (
                    0,
                    _id_datum(applicability_basis_id, "analysis.semantic-basis"),
                ),
                (
                    1,
                    _id_datum(
                        source_capability_id,
                        "analysis.family-source-property-capability",
                    ),
                ),
                (
                    2,
                    _id_datum(
                        theorem_truth_support_ref,
                        "analysis.theorem-truth-support",
                    ),
                ),
                (
                    3,
                    _id_datum(target_proposition_id, "analysis.proposition"),
                ),
            )
        ),
    )


def _family_judgment_id(
    applicability_port_id: object,
    source_capability_id: object,
    theorem_truth_support_ref: object,
    target_proposition_id: object,
    semantic_basis_id: object,
    retained_hypotheses: tuple[object, ...],
) -> object:
    return _analysis_id(
        "analysis.family-knowledge-judgment",
        k1.DatumRecord(
            (
                (
                    0,
                    _id_datum(
                        applicability_port_id,
                        "analysis.family-theorem-applicability-port",
                    ),
                ),
                (
                    1,
                    _id_datum(
                        source_capability_id,
                        "analysis.family-source-property-capability",
                    ),
                ),
                (
                    2,
                    _id_datum(
                        theorem_truth_support_ref,
                        "analysis.theorem-truth-support",
                    ),
                ),
                (
                    3,
                    _id_datum(target_proposition_id, "analysis.proposition"),
                ),
                (4, _id_datum(semantic_basis_id, "analysis.semantic-basis")),
                (
                    5,
                    k1.DatumSeq(
                        tuple(
                            _id_datum(item, "analysis.hypothesis")
                            for item in retained_hypotheses
                        )
                    ),
                ),
            )
        ),
    )


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
                detail="a fixed n0 judgment cannot fill the all-n family source slot",
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
        source_capability_id = _family_source_capability_id(source_capability)
        target_proposition_id = family_target_property_proposition_id(family)
        retained = hypothesis_union(
            applicability_port.retained_hypotheses,
            (
                source_capability.retained_hypothesis_id,
                theorem_truth.retained_hypothesis_id,
            ),
        )
        basis_id = _family_judgment_basis_id(
            applicability_port.semantic_basis_id,
            source_capability_id,
            theorem_truth.support_ref,
            target_proposition_id,
        )
        judgment_id = _family_judgment_id(
            applicability_port.port_id,
            source_capability_id,
            theorem_truth.support_ref,
            target_proposition_id,
            basis_id,
            retained,
        )
        return _affirmative(
            AFKFamilyKnowledgeJudgment(
                judgment_id=judgment_id,
                theorem_schema_id=applicability_port.theorem_schema_id,
                family=family,
                family_definition_id=family_definition_id(family),
                target_proposition_id=target_proposition_id,
                operator_bindings=applicability_port.applicability_input.operator_bindings,
                applicability_port=applicability_port,
                applicability_port_id=applicability_port.port_id,
                source_capability=source_capability,
                source_capability_id=source_capability_id,
                theorem_truth=theorem_truth,
                theorem_truth_support_ref=theorem_truth.support_ref,
                semantic_basis_id=basis_id,
                retained_hypotheses=retained,
                _issuer=_FAMILY_JUDGMENT_ISSUER,
            )
        )
    except AuthorityError as error:
        return AttemptOutcome(AttemptKind.REFUSED, detail=str(error))
    except (AnalysisError, k2.ModelError, k3.K3Error) as error:
        return AttemptOutcome(AttemptKind.MALFORMED, detail=str(error))


def require_family_knowledge_judgment(
    judgment: AFKFamilyKnowledgeJudgment,
) -> None:
    if (
        type(judgment) is not AFKFamilyKnowledgeJudgment
        or judgment._issuer is not _FAMILY_JUDGMENT_ISSUER
        or judgment.family_definition_id != family_definition_id(judgment.family)
        or judgment.target_proposition_id
        != family_target_property_proposition_id(judgment.family)
        or judgment.operator_bindings != family_operator_bindings(judgment.family)
        or judgment.theorem_schema_id != AFK_V2_THM4_CLASSICAL_ROM
    ):
        raise AuthorityError("family knowledge judgment is forged or detached")
    require_family_applicability_port(judgment.applicability_port)
    require_family_source_capability(judgment.family, judgment.source_capability)
    require_theorem_truth_treatment(_AFK_GLOBAL_THEOREM_SCHEMA, judgment.theorem_truth)
    expected_source_capability_id = _family_source_capability_id(
        judgment.source_capability
    )
    expected_retained = hypothesis_union(
        judgment.applicability_port.retained_hypotheses,
        (
            judgment.source_capability.retained_hypothesis_id,
            judgment.theorem_truth.retained_hypothesis_id,
        ),
    )
    expected_basis = _family_judgment_basis_id(
        judgment.applicability_port.semantic_basis_id,
        expected_source_capability_id,
        judgment.theorem_truth.support_ref,
        judgment.target_proposition_id,
    )
    if (
        judgment.applicability_port.family_definition_id
        != judgment.family_definition_id
        or judgment.applicability_port_id != judgment.applicability_port.port_id
        or judgment.source_capability_id != expected_source_capability_id
        or judgment.theorem_truth_support_ref != judgment.theorem_truth.support_ref
        or judgment.semantic_basis_id != expected_basis
        or judgment.retained_hypotheses != expected_retained
    ):
        raise TheoremError(
            "family judgment authority or retained support was substituted"
        )
    expected_judgment_id = _family_judgment_id(
        judgment.applicability_port_id,
        judgment.source_capability_id,
        judgment.theorem_truth_support_ref,
        judgment.target_proposition_id,
        judgment.semantic_basis_id,
        expected_retained,
    )
    if judgment.judgment_id != expected_judgment_id:
        raise TheoremError("family knowledge judgment identity was substituted")


# ---------------------------------------------------------------------------
# Pointwise n0 specialization: all concrete K1/K2/K3 coordinates live here
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


def native_subject_projection_id(source: FreshFsRelationSource) -> object:
    require_fresh_fs_relation_source(source)
    return _analysis_id(
        "analysis.native-subject-projection",
        k1.DatumRecord(
            (
                (
                    0,
                    _id_datum(source.protocol_source.core_id, "pir.interactive-core"),
                ),
                (
                    1,
                    _id_datum(source.protocol_source.fresh_protocol_id, "pir.protocol"),
                ),
                (
                    2,
                    _id_datum(
                        source.protocol_source.fiat_shamir_protocol_id,
                        "pir.protocol",
                    ),
                ),
                (
                    3,
                    _id_datum(
                        source.fresh_binding.binding_id,
                        "relations.protocol-binding",
                    ),
                ),
                (
                    4,
                    _id_datum(
                        source.fiat_shamir_binding.binding_id,
                        "relations.protocol-binding",
                    ),
                ),
                (
                    5,
                    _id_datum(
                        source_manifest_id(source.fresh_manifest),
                        "analysis.semantic-read-manifest",
                    ),
                ),
                (
                    6,
                    _id_datum(
                        source_manifest_id(source.fiat_shamir_manifest),
                        "analysis.semantic-read-manifest",
                    ),
                ),
            )
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
    return _analysis_id(
        "analysis.concrete-family-member-subject",
        k1.DatumRecord(
            (
                (
                    0,
                    _id_datum(
                        family_definition_id(family),
                        "analysis.asymptotic-family-definition",
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
                    _id_datum(source_selector_id, "analysis.family-member-selector"),
                ),
                (
                    4,
                    _id_datum(target_selector_id, "analysis.family-member-selector"),
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
                (
                    10,
                    _id_datum(
                        correspondence.query_encoding_id,
                        "analysis.query-encoding",
                    ),
                ),
                (11, k1.Symbol("exact-raw-statement-relation-member-at-n0")),
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
    return _analysis_id(
        "analysis.family-instance-role-map",
        k1.DatumRecord(
            (
                (0, k1.Nat(mapping.ordinal)),
                (1, k1.Symbol(mapping.role)),
                (
                    2,
                    _id_datum(
                        mapping.family_definition_id,
                        "analysis.asymptotic-family-definition",
                    ),
                ),
                (3, k1.Nat(mapping.logical_index)),
                (
                    4,
                    _id_datum(
                        mapping.native_subject_projection_id,
                        "analysis.native-subject-projection",
                    ),
                ),
                (
                    5,
                    _id_datum(
                        mapping.abstract_coordinate_id,
                        "analysis.abstract-family-role-coordinate",
                    ),
                ),
                (
                    6,
                    _id_datum(
                        mapping.native_coordinate_id,
                        "analysis.native-role-coordinate",
                    ),
                ),
                (
                    7,
                    _id_datum(
                        mapping.abstract_resolved_id,
                        "analysis.abstract-resolved-role",
                    ),
                ),
                (
                    8,
                    _id_datum(
                        mapping.native_resolved_id,
                        "analysis.native-resolved-role",
                    ),
                ),
                (9, k1.Symbol(mapping.map_clause)),
                (10, k1.Symbol(mapping.information_loss)),
            )
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
    native_challenge_domain_id = _analysis_id(
        "analysis.challenge-domain",
        k1.DatumRecord(
            (
                (0, _id_datum(correspondence.core_id, "pir.interactive-core")),
                (1, k1.Nat(challenge_ordinal)),
                (2, k1.Symbol(challenge_occurrence.name)),
                (3, k1.Nat(challenge_occurrence.challenge_domain.modulus)),
            )
        ),
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
            AFK_POSITIVE_POLYNOMIAL_Q_ONE, "analysis.positive-polynomial-profile"
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
                        correspondence.source_model_id, "analysis.model-instantiation"
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
                        correspondence.target_model_id, "analysis.model-instantiation"
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
        k1.DatumRecord(
            (
                (
                    0,
                    _id_datum(
                        correspondence.fresh_binding_id, "relations.protocol-binding"
                    ),
                ),
                (
                    1,
                    _id_datum(
                        correspondence.fiat_shamir_binding_id,
                        "relations.protocol-binding",
                    ),
                ),
            )
        ),
        k1.DatumSeq(
            tuple(
                k1.DatumSeq(tuple(k1.Symbol(x) for x in item))
                for item in correspondence.claim_map
            )
        ),
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
                (0, k1.Nat(1)),
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
                        AFK_POSITIVE_POLYNOMIAL_Q_ONE,
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
        abstract_id = _analysis_id(
            "analysis.abstract-family-role-coordinate",
            k1.DatumRecord(
                (
                    (
                        0,
                        _id_datum(
                            family_id,
                            "analysis.asymptotic-family-definition",
                        ),
                    ),
                    (1, k1.Nat(logical_index)),
                    (2, k1.Nat(ordinal)),
                    (3, k1.Symbol(role)),
                )
            ),
        )
        native_id = _analysis_id(
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
        abstract_resolved_id = _analysis_id(
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
        native_resolved_id = _analysis_id(
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
    member_by_ordinal = (
        concrete["knowledge-error"],
        concrete["knowledge-success-lower-bound"],
        concrete["lemma4-transcript-extraction-lower-bound"],
        concrete["expected-adversary-calls-upper-bound"],
    )
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
) -> object:
    if (
        type(correspondence) is not PointwiseFormulaCorrespondence
        or correspondence.local_ordinal not in range(4)
        or correspondence.family_instantiated_ast
        != correspondence.member_normalized_ast
    ):
        raise TheoremError("pointwise formula correspondence lacks exact AST equality")
    return _analysis_id(
        "analysis.pointwise-formula-correspondence",
        k1.DatumRecord(
            (
                (0, k1.Nat(correspondence.local_ordinal)),
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
                (5, _symbol_seq(correspondence.exact_substitution)),
            )
        ),
    )


def fixed_member_process_hypothesis_id(
    family: AFKAsymptoticFamily, correspondence: FSCorrespondence
) -> object:
    return _analysis_id(
        "analysis.hypothesis",
        k1.DatumRecord(
            (
                (
                    0,
                    _id_datum(
                        family_definition_id(family),
                        "analysis.asymptotic-family-definition",
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
                        "assumed-full-adaptive-family-to-K2-process-correspondence-at-n0"
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
    return _analysis_id(
        "analysis.hypothesis",
        k1.DatumRecord(
            (
                (
                    0,
                    _id_datum(
                        family_definition_id(family),
                        "analysis.asymptotic-family-definition",
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
                                _family_instance_role_map_id(item),
                                "analysis.family-instance-role-map",
                            )
                            for item in family_instance_role_maps(
                                family, source, correspondence
                            )
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
    return _analysis_id(
        "analysis.hypothesis",
        k1.DatumRecord(
            (
                (
                    0,
                    _id_datum(
                        family_definition_id(family),
                        "analysis.asymptotic-family-definition",
                    ),
                ),
                (
                    1,
                    k1.DatumSeq(
                        tuple(
                            _id_datum(
                                _pointwise_formula_correspondence_id(item),
                                "analysis.pointwise-formula-correspondence",
                            )
                            for item in pointwise_formula_correspondences(
                                family, concrete_subject_id
                            )
                        )
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
class ConcreteFamilyInstanceCorrespondence:
    correspondence_capability_id: object
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
    _issuer: object


_MEMBER_CORRESPONDENCE_ISSUER = object()


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
    ):
        raise TheoremError("pointwise oracle-index bounds must be positive integers")
    return _analysis_id(
        "analysis.hypothesis",
        k1.DatumRecord(
            (
                (
                    0,
                    _id_datum(
                        family_definition_id(family),
                        "analysis.asymptotic-family-definition",
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
                (3, k1.Nat(family_index_bound_at_n0)),
                (4, k1.Nat(native_index_bound)),
                (
                    5,
                    k1.Symbol(
                        "checked-numeric-u-at-n0-equality-with-assumed-domain-correspondence"
                    ),
                ),
            )
        ),
    )


def fixed_member_required_hypotheses(
    family: AFKAsymptoticFamily,
    source: FreshFsRelationSource,
    source_model: ExperimentModel,
    target_model: ExperimentModel,
    correspondence: FSCorrespondence,
    *,
    family_index_bound_at_n0: int | None = None,
) -> tuple[object, ...]:
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
    return canonical_hypotheses(
        (
            k2_static_view_support_hypothesis_id(source),
            fresh_uniformity_correspondence_hypothesis_id(source, source_model),
            fixed_member_process_hypothesis_id(family, correspondence),
            fixed_member_role_adequacy_hypothesis_id(family, source, correspondence),
            fixed_member_formula_adequacy_hypothesis_id(family, concrete_subject_id),
            fixed_member_index_bound_hypothesis_id(
                family,
                concrete_subject_id,
                selected_family_bound,
                native_index_bound,
            ),
        )
    )


def _member_correspondence_id(
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
    formula_correspondences: tuple[PointwiseFormulaCorrespondence, ...],
    hypotheses: tuple[object, ...],
) -> object:
    return _analysis_id(
        "analysis.family-instance-correspondence-capability",
        k1.DatumRecord(
            (
                (
                    0,
                    _id_datum(
                        family_definition_id(family),
                        "analysis.asymptotic-family-definition",
                    ),
                ),
                (1, k1.Nat(1)),
                (2, k1.Nat(1)),
                (
                    3,
                    _id_datum(
                        native_subject_projection_id(source),
                        "analysis.native-subject-projection",
                    ),
                ),
                (
                    4,
                    _id_datum(
                        experiment_model_id(source_model),
                        "analysis.model-instantiation",
                    ),
                ),
                (
                    5,
                    _id_datum(
                        experiment_model_id(target_model),
                        "analysis.model-instantiation",
                    ),
                ),
                (
                    6,
                    _id_datum(
                        concrete_subject_id,
                        "analysis.concrete-family-member-subject",
                    ),
                ),
                (7, k1.Nat(family_index_bound_at_n0)),
                (8, k1.Nat(native_index_bound)),
                (
                    9,
                    _id_datum(
                        fs_correspondence_id(correspondence),
                        "analysis.fs-correspondence",
                    ),
                ),
                (
                    10,
                    _id_datum(source_selector_id, "analysis.family-member-selector"),
                ),
                (
                    11,
                    _id_datum(target_selector_id, "analysis.family-member-selector"),
                ),
                (
                    12,
                    k1.DatumSeq(
                        tuple(
                            _id_datum(
                                _family_instance_role_map_id(item),
                                "analysis.family-instance-role-map",
                            )
                            for item in role_maps
                        )
                    ),
                ),
                (
                    13,
                    k1.DatumSeq(
                        tuple(
                            _id_datum(
                                _pointwise_formula_correspondence_id(item),
                                "analysis.pointwise-formula-correspondence",
                            )
                            for item in formula_correspondences
                        )
                    ),
                ),
                (
                    14,
                    k1.DatumSeq(
                        tuple(
                            _id_datum(item, "analysis.hypothesis")
                            for item in hypotheses
                        )
                    ),
                ),
            )
        ),
    )


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
        if (
            family.challenge_cardinality != 8
            or profile.challenge_count != 8
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
                    "family bound and K1 bounded-byte member domain"
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
        if selected_formulas != expected_formulas:
            return AttemptOutcome(
                AttemptKind.MALFORMED,
                detail="pointwise formula substitution is not exact AST equality",
            )
        for mapping in selected_formulas:
            _pointwise_formula_correspondence_id(mapping)
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
        capability_id = _member_correspondence_id(
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
            selected_formulas,
            hypotheses,
        )
        return _affirmative(
            ConcreteFamilyInstanceCorrespondence(
                capability_id,
                family,
                family_definition_id(family),
                1,
                1,
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
                _MEMBER_CORRESPONDENCE_ISSUER,
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
    require_fresh_fs_relation_source(capability.source)
    _require_exact_special_soundness_model(capability.source_model)
    _require_exact_adaptive_knowledge_model(capability.target_model)
    expected_correspondence = derive_fs_correspondence(
        capability.source, capability.source_model, capability.target_model
    )
    expected_subject_id = concrete_member_subject_id(
        capability.family,
        capability.source,
        expected_correspondence,
        capability.source_member_selector_id,
        capability.target_member_selector_id,
    )
    if (
        capability._issuer is not _MEMBER_CORRESPONDENCE_ISSUER
        or capability.logical_index != 1
        or capability.native_statement_length != 1
        or capability.family.challenge_cardinality != 8
        or capability.family_index_bound_at_n0
        != family_ro_index_bound_at(capability.family, capability.logical_index)
        or capability.native_index_bound != native_raw_query_index_bit_bound()
        or capability.family_definition_id != family_definition_id(capability.family)
        or capability.native_subject_projection_id
        != native_subject_projection_id(capability.source)
        or capability.concrete_member_subject_id != expected_subject_id
        or capability.fs_correspondence != expected_correspondence
        or capability.fs_correspondence_id
        != fs_correspondence_id(capability.fs_correspondence)
        or capability.source_member_selector_id
        != fixed_family_member_selector_id(capability.source, "fresh")
        or capability.target_member_selector_id
        != fixed_family_member_selector_id(capability.source, "fiat-shamir")
        or capability.role_maps
        != family_instance_role_maps(
            capability.family, capability.source, capability.fs_correspondence
        )
        or capability.formula_correspondences
        != pointwise_formula_correspondences(capability.family, expected_subject_id)
    ):
        raise AuthorityError(
            "pointwise family/member correspondence is forged or detached"
        )
    required = fixed_member_required_hypotheses(
        capability.family,
        capability.source,
        capability.source_model,
        capability.target_model,
        capability.fs_correspondence,
        family_index_bound_at_n0=capability.family_index_bound_at_n0,
    )
    if capability.retained_hypotheses != required:
        raise TheoremError("pointwise correspondence premise support was substituted")
    expected_id = _member_correspondence_id(
        capability.family,
        capability.source,
        capability.source_model,
        capability.target_model,
        capability.fs_correspondence,
        capability.concrete_member_subject_id,
        capability.family_index_bound_at_n0,
        capability.native_index_bound,
        capability.source_member_selector_id,
        capability.target_member_selector_id,
        capability.role_maps,
        capability.formula_correspondences,
        capability.retained_hypotheses,
    )
    if capability.correspondence_capability_id != expected_id:
        raise TheoremError("pointwise correspondence identity was substituted")


@dataclass(frozen=True)
class ConcreteMemberKnowledgeJudgment:
    judgment_id: object
    family_judgment: AFKFamilyKnowledgeJudgment
    family_judgment_id: object
    correspondence: ConcreteFamilyInstanceCorrespondence
    correspondence_capability_id: object
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
    _issuer: object


_MEMBER_JUDGMENT_ISSUER = object()


def specialize_afk_family_judgment(
    family_judgment: AFKFamilyKnowledgeJudgment,
    correspondence: ConcreteFamilyInstanceCorrespondence | None,
) -> AttemptOutcome:
    try:
        require_family_knowledge_judgment(family_judgment)
        if correspondence is None:
            return AttemptOutcome(
                AttemptKind.CANNOT_ANSWER,
                detail="exact family/member correspondence is unavailable",
            )
        require_concrete_family_instance_correspondence(correspondence)
        if correspondence.family_definition_id != family_judgment.family_definition_id:
            return AttemptOutcome(
                AttemptKind.REFUSED,
                detail="pointwise correspondence belongs to another family",
            )
        transform = afk_quantitative_transform(
            k=2,
            challenge_count=correspondence.family.challenge_cardinality,
            subject_id=correspondence.concrete_member_subject_id,
        )
        formula_map = afk_quantitative_formula_ids(transform)
        formula_ids = (
            formula_map["knowledge-error"],
            formula_map["knowledge-success-lower-bound"],
            formula_map["lemma4-transcript-extraction-lower-bound"],
            formula_map["expected-adversary-calls-upper-bound"],
        )
        expected_from_correspondence = tuple(
            item.member_formula_id for item in correspondence.formula_correspondences
        )
        if formula_ids != expected_from_correspondence:
            return AttemptOutcome(
                AttemptKind.REFUSED,
                detail="family target formulas do not specialize pointwise",
            )
        conclusion = afk_knowledge_soundness_conclusion(transform)
        transform_id = afk_quantitative_transform_id(transform)
        conclusion_id = afk_target_conclusion_id(conclusion)
        retained = hypothesis_union(
            family_judgment.retained_hypotheses,
            correspondence.retained_hypotheses,
        )
        judgment_id = _analysis_id(
            "analysis.concrete-member-knowledge-judgment",
            k1.DatumRecord(
                (
                    (
                        0,
                        _id_datum(
                            family_judgment.judgment_id,
                            "analysis.family-knowledge-judgment",
                        ),
                    ),
                    (
                        1,
                        _id_datum(
                            correspondence.correspondence_capability_id,
                            "analysis.family-instance-correspondence-capability",
                        ),
                    ),
                    (2, k1.Nat(correspondence.logical_index)),
                    (3, k1.Nat(correspondence.native_statement_length)),
                    (
                        4,
                        _id_datum(
                            correspondence.native_subject_projection_id,
                            "analysis.native-subject-projection",
                        ),
                    ),
                    (
                        5,
                        _id_datum(
                            correspondence.concrete_member_subject_id,
                            "analysis.concrete-family-member-subject",
                        ),
                    ),
                    (
                        6,
                        _id_datum(transform_id, "analysis.quantitative-transform"),
                    ),
                    (
                        7,
                        k1.DatumSeq(
                            tuple(
                                _id_datum(item, "analysis.quantitative-formula")
                                for item in formula_ids
                            )
                        ),
                    ),
                    (
                        8,
                        _id_datum(conclusion_id, "analysis.property-conclusion"),
                    ),
                    (
                        9,
                        k1.DatumSeq(
                            tuple(
                                _id_datum(item, "analysis.hypothesis")
                                for item in retained
                            )
                        ),
                    ),
                )
            ),
        )
        return _affirmative(
            ConcreteMemberKnowledgeJudgment(
                judgment_id=judgment_id,
                family_judgment=family_judgment,
                family_judgment_id=family_judgment.judgment_id,
                correspondence=correspondence,
                correspondence_capability_id=correspondence.correspondence_capability_id,
                family_definition_id=correspondence.family_definition_id,
                logical_index=correspondence.logical_index,
                native_statement_length=correspondence.native_statement_length,
                native_subject_projection_id=correspondence.native_subject_projection_id,
                concrete_member_subject_id=correspondence.concrete_member_subject_id,
                quantitative_transform=transform,
                quantitative_transform_id=transform_id,
                quantitative_formula_ids=formula_ids,
                target_conclusion=conclusion,
                target_conclusion_id=conclusion_id,
                retained_hypotheses=retained,
                _issuer=_MEMBER_JUDGMENT_ISSUER,
            )
        )
    except AuthorityError as error:
        return AttemptOutcome(AttemptKind.REFUSED, detail=str(error))
    except (AnalysisError, k2.ModelError, k3.K3Error) as error:
        return AttemptOutcome(AttemptKind.MALFORMED, detail=str(error))


def require_concrete_member_judgment(
    judgment: ConcreteMemberKnowledgeJudgment,
) -> None:
    if type(judgment) is not ConcreteMemberKnowledgeJudgment:
        raise AuthorityError("concrete member judgment is forged or detached")
    require_family_knowledge_judgment(judgment.family_judgment)
    require_concrete_family_instance_correspondence(judgment.correspondence)
    correspondence = judgment.correspondence
    expected_transform = afk_quantitative_transform(
        k=2,
        challenge_count=correspondence.family.challenge_cardinality,
        subject_id=correspondence.concrete_member_subject_id,
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
        judgment.family_judgment.retained_hypotheses,
        correspondence.retained_hypotheses,
    )
    if (
        judgment._issuer is not _MEMBER_JUDGMENT_ISSUER
        or judgment.family_judgment_id != judgment.family_judgment.judgment_id
        or judgment.correspondence_capability_id
        != correspondence.correspondence_capability_id
        or judgment.family_definition_id != correspondence.family_definition_id
        or judgment.logical_index != correspondence.logical_index
        or judgment.native_statement_length != correspondence.native_statement_length
        or judgment.native_subject_projection_id
        != correspondence.native_subject_projection_id
        or judgment.concrete_member_subject_id
        != correspondence.concrete_member_subject_id
        or judgment.family_judgment.family_definition_id
        != correspondence.family_definition_id
        or judgment.quantitative_transform != expected_transform
        or judgment.quantitative_transform_id
        != afk_quantitative_transform_id(judgment.quantitative_transform)
        or judgment.quantitative_formula_ids != expected_formula_ids
        or judgment.target_conclusion != expected_conclusion
        or judgment.target_conclusion_id
        != afk_target_conclusion_id(judgment.target_conclusion)
        or retained != judgment.retained_hypotheses
    ):
        raise AuthorityError("concrete member judgment is forged or detached")
    expected_judgment_id = _analysis_id(
        "analysis.concrete-member-knowledge-judgment",
        k1.DatumRecord(
            (
                (
                    0,
                    _id_datum(
                        judgment.family_judgment_id,
                        "analysis.family-knowledge-judgment",
                    ),
                ),
                (
                    1,
                    _id_datum(
                        judgment.correspondence_capability_id,
                        "analysis.family-instance-correspondence-capability",
                    ),
                ),
                (2, k1.Nat(judgment.logical_index)),
                (3, k1.Nat(judgment.native_statement_length)),
                (
                    4,
                    _id_datum(
                        judgment.native_subject_projection_id,
                        "analysis.native-subject-projection",
                    ),
                ),
                (
                    5,
                    _id_datum(
                        judgment.concrete_member_subject_id,
                        "analysis.concrete-family-member-subject",
                    ),
                ),
                (
                    6,
                    _id_datum(
                        judgment.quantitative_transform_id,
                        "analysis.quantitative-transform",
                    ),
                ),
                (
                    7,
                    k1.DatumSeq(
                        tuple(
                            _id_datum(item, "analysis.quantitative-formula")
                            for item in judgment.quantitative_formula_ids
                        )
                    ),
                ),
                (
                    8,
                    _id_datum(
                        judgment.target_conclusion_id,
                        "analysis.property-conclusion",
                    ),
                ),
                (
                    9,
                    k1.DatumSeq(
                        tuple(
                            _id_datum(item, "analysis.hypothesis") for item in retained
                        )
                    ),
                ),
            )
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
