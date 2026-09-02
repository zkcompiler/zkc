"""Portable natural arithmetic and exact bounded-stream support.

This module is deliberately independent of the Analysis object model.  Its
caller supplies the authenticated Foundation model and receives one immutable
bundle containing:

* an ordinary semantic module (not a root-regime extension),
* four portable algorithms used by the bounded Schnorr cover, and
* a small evaluator that authenticates those exact module and algorithm
  preimages before interpreting their closed arithmetic laws.

The evaluator is operational support.  Algorithm identity, module identity,
declaration bodies, and the caller-owned Analysis laws remain the authorities.
"""

from __future__ import annotations

from dataclasses import dataclass
from hashlib import sha256
from math import gcd
from types import MappingProxyType
from typing import Mapping


UINT64_MAX = (1 << 64) - 1
GROUP_MODULUS = 23
SUBGROUP_ORDER = 11
GENERATOR = 2
STATEMENT = 8
CHALLENGE_COUNT = 8


@dataclass(frozen=True)
class PortableEvaluationLimits:
    maximum_steps: int = 20_000
    maximum_primitive_work: int = 20_000
    maximum_result_bytes: int = 1 << 20


@dataclass(frozen=True)
class PortableEvaluationCharge:
    steps: int = 0
    primitive_work: int = 0
    result_bytes: int = 0


@dataclass(frozen=True)
class PortableEvaluationResult:
    kind: str
    value: object | None = None
    failure_label: str | None = None
    charge: PortableEvaluationCharge = PortableEvaluationCharge()
    detail: str = ""


@dataclass(frozen=True)
class PortableArithmeticBundle:
    module: object
    module_id: object
    module_preimages: Mapping[object, object]
    primitive_refs: Mapping[str, object]
    raw_transcript_type: object
    raw_pair_type: object
    representative_transcript_type: object
    representative_pair_type: object
    stream_state_type: object
    stream_output_type: object
    witness_type: object
    normalization_algorithm: object
    embedding_algorithm: object
    candidate_algorithm: object
    representative_stream_algorithm: object
    representative_datums: tuple[object, ...]
    representative_stream_digest: bytes


@dataclass(frozen=True)
class QuotientFactorizationReceipt:
    module_id: object
    normalization_algorithm_id: object
    embedding_algorithm_id: object
    candidate_algorithm_id: object
    statement_period: int
    commitment_period: int
    challenge_bound: int
    response_period: int
    checked_algebraic_facts: tuple[str, ...]


class _Unsupported(Exception):
    pass


class _DomainFailure(Exception):
    def __init__(self, label: str) -> None:
        super().__init__(label)
        self.label = label


class _LimitExceeded(Exception):
    pass


def _natural_type(k1: object, maximum: int) -> object:
    return k1.ValueType(k1.NAT_DOMAIN, k1.NatSchema(maximum))


def _record_type(k1: object, fields: tuple[tuple[int, object], ...]) -> object:
    return k1.ValueType(k1.RECORD_DOMAIN, k1.RecordSchema(fields))


def _variant_type(k1: object, cases: tuple[tuple[int, object], ...]) -> object:
    return k1.ValueType(k1.VARIANT_DOMAIN, k1.VariantSchema(cases))


def _sequence_type(k1: object, element: object, maximum: int) -> object:
    return k1.ValueType(k1.SEQUENCE_DOMAIN, k1.SeqSchema(element, maximum))


def _literal(k1: object, value_type: object, datum: object) -> object:
    return k1.Literal(k1.admit_value(value_type, datum))


def _primitive_reference_body(k1: object, module_id: object, ordinal: int) -> object:
    return k1.DatumVariant(
        1,
        k1.DatumRecord(
            (
                (0, k1.BytesValue(module_id.internal_reference())),
                (1, k1.Symbol("semantic-primitive")),
                (2, k1.Nat(ordinal)),
            )
        ),
    )


def _local_failure_ref(k1: object, ordinal: int) -> object:
    return k1.DatumRecord(
        ((0, k1.Symbol("semantic-failure")), (1, k1.Nat(ordinal)))
    )


def _primitive_declaration(
    k1: object,
    name: str,
    type_rule: bytes,
    operation_law: bytes,
    failures: tuple[int, ...] = (),
) -> object:
    return k1.DatumRecord(
        (
            (0, k1.Symbol(name)),
            (1, k1.Nat(1)),
            (2, k1.BytesValue(type_rule)),
            (3, k1.BytesValue(operation_law)),
            (4, k1.DatumSeq(tuple(_local_failure_ref(k1, item) for item in failures))),
            (
                5,
                k1.Symbol(
                    "pure-total-with-typed-failure"
                    if failures
                    else "pure-total-deterministic"
                ),
            ),
        )
    )


def _module_candidate(k1: object) -> tuple[object, tuple[str, ...]]:
    unit_descriptor = k1.declaration_value_type_datum(k1.UNIT_VALUE)
    failures = k1.DatumSeq(
        (
            k1.DatumRecord(
                ((0, k1.Symbol("zero-modulus")), (1, unit_descriptor))
            ),
            k1.DatumRecord(
                ((0, k1.Symbol("non-invertible")), (1, unit_descriptor))
            ),
            k1.DatumRecord(
                ((0, k1.Symbol("stream-index-out-of-range")), (1, unit_descriptor))
            ),
        )
    )
    rows = (
        (
            "natural.equal",
            b"(Nat[a],Nat[b])->Bool",
            b"true-iff-input[0]-equals-input[1]",
            (),
        ),
        (
            "natural.less-than",
            b"(Nat[a],Nat[b])->Bool",
            b"true-iff-input[0]-is-strictly-less-than-input[1]",
            (),
        ),
        (
            "natural.modulo-positive",
            b"(Nat[a],LiteralPositiveNat[m])->Nat[m-1]!zero-modulus",
            b"euclidean-remainder-by-the-exact-positive-literal-modulus",
            (0,),
        ),
        (
            "natural.subtract-modulo-positive",
            b"(Nat[a],Nat[b],LiteralPositiveNat[m])->Nat[m-1]!zero-modulus",
            b"euclidean-input[0]-minus-input[1]-modulo-the-exact-positive-literal",
            (0,),
        ),
        (
            "natural.multiply-modulo-positive",
            b"(Nat[a],Nat[b],LiteralPositiveNat[m])->Nat[m-1]!zero-modulus",
            b"input[0]-times-input[1]-modulo-the-exact-positive-literal",
            (0,),
        ),
        (
            "natural.power-modulo-positive",
            b"(Nat[a],Nat[b],LiteralPositiveNat[m])->Nat[m-1]!zero-modulus",
            b"input[0]-to-input[1]-modulo-the-exact-positive-literal",
            (0,),
        ),
        (
            "natural.inverse-modulo-coprime",
            b"(Nat[a],LiteralPositiveNat[m])->Nat[m-1]!zero-modulus!non-invertible",
            b"unique-multiplicative-inverse-modulo-m-iff-gcd(input[0],m)=1",
            (0, 1),
        ),
        (
            "natural.widen-u64",
            b"(Nat[a<=2^64-1])->Nat[2^64-1]",
            b"identity-on-the-mathematical-natural-with-a-wider-static-carrier",
            (),
        ),
    )
    primitive_catalog = k1.DatumSeq(
        tuple(
            _primitive_declaration(k1, name, type_rule, law, failure_ordinals)
            for name, type_rule, law, failure_ordinals in rows
        )
    )
    declarations = k1.DatumSeq(
        (
            k1.DatumRecord(
                ((0, k1.Symbol("semantic-failure")), (1, failures))
            ),
            k1.DatumRecord(
                ((0, k1.Symbol("semantic-primitive")), (1, primitive_catalog))
            ),
        )
    )
    return (
        k1.SemanticModuleCandidate(
            k1.Symbol("zkc.foundation.natural-modular-arithmetic"),
            (),
            declarations,
        ),
        tuple(row[0] for row in rows),
    )


def _transcript_datum(k1: object, values: tuple[int, int, int, int]) -> object:
    return k1.DatumRecord(tuple((index, k1.Nat(value)) for index, value in enumerate(values)))


def _pair_datum(
    k1: object,
    first: tuple[int, int, int, int],
    second: tuple[int, int, int, int],
) -> object:
    return k1.DatumRecord(
        ((0, _transcript_datum(k1, first)), (1, _transcript_datum(k1, second)))
    )


def _canonical_representative_datums(k1: object) -> tuple[object, ...]:
    values = []
    for commitment in range(GROUP_MODULUS):
        for first_challenge in range(CHALLENGE_COUNT):
            for second_challenge in range(first_challenge + 1, CHALLENGE_COUNT):
                first_responses = tuple(
                    response
                    for response in range(SUBGROUP_ORDER)
                    if pow(GENERATOR, response, GROUP_MODULUS)
                    == (
                        commitment
                        * pow(STATEMENT, first_challenge, GROUP_MODULUS)
                    )
                    % GROUP_MODULUS
                )
                second_responses = tuple(
                    response
                    for response in range(SUBGROUP_ORDER)
                    if pow(GENERATOR, response, GROUP_MODULUS)
                    == (
                        commitment
                        * pow(STATEMENT, second_challenge, GROUP_MODULUS)
                    )
                    % GROUP_MODULUS
                )
                if not first_responses or not second_responses:
                    continue
                if len(first_responses) != 1 or len(second_responses) != 1:
                    raise AssertionError(
                        "an accepted quotient residue has non-unique responses"
                    )
                first = (
                    STATEMENT,
                    commitment,
                    first_challenge,
                    first_responses[0],
                )
                second = (
                    STATEMENT,
                    commitment,
                    second_challenge,
                    second_responses[0],
                )
                values.append(_pair_datum(k1, first, second))
    if len(values) != 308:
        raise AssertionError("the selected canonical cover must contain 308 members")
    return tuple(values)


def ordered_stream_digest(k1: object, datums: tuple[object, ...]) -> bytes:
    digest = sha256()
    for datum in datums:
        body = k1.encode_datum(datum)
        digest.update(len(body).to_bytes(8, "big"))
        digest.update(body)
    return digest.digest()


def _project_path(k1: object, root: object, *ordinals: int) -> object:
    result = root
    for ordinal in ordinals:
        result = k1.Project(result, ordinal)
    return result


def _mod_call(
    k1: object,
    refs: Mapping[str, object],
    value: object,
    modulus: int,
) -> object:
    return k1.PrimitiveCall(
        refs["natural.modulo-positive"],
        (
            value,
            _literal(k1, _natural_type(k1, modulus), k1.Nat(modulus)),
        ),
    )


def _normalized_transcript_term(
    k1: object,
    refs: Mapping[str, object],
    root: object,
    transcript_ordinal: int,
) -> object:
    return k1.RecordConstruct(
        (
            (0, _mod_call(k1, refs, _project_path(k1, root, transcript_ordinal, 0), 9)),
            (1, _mod_call(k1, refs, _project_path(k1, root, transcript_ordinal, 1), 23)),
            (2, _mod_call(k1, refs, _project_path(k1, root, transcript_ordinal, 2), 8)),
            (3, _mod_call(k1, refs, _project_path(k1, root, transcript_ordinal, 3), 11)),
        )
    )


def _widened_transcript_term(
    k1: object,
    refs: Mapping[str, object],
    root: object,
    transcript_ordinal: int,
) -> object:
    return k1.RecordConstruct(
        tuple(
            (
                field,
                k1.PrimitiveCall(
                    refs["natural.widen-u64"],
                    (_project_path(k1, root, transcript_ordinal, field),),
                ),
            )
            for field in range(4)
        )
    )


def build_bundle(k1: object) -> PortableArithmeticBundle:
    module, primitive_names = _module_candidate(k1)
    module_id = module.identity
    primitive_refs: dict[str, object] = {}
    for ordinal, name in enumerate(primitive_names):
        declaration_body = _primitive_reference_body(k1, module_id, ordinal)
        identifier = k1.content_id(
            k1.SEMANTIC_PRIMITIVE_KIND,
            k1.encode_datum(declaration_body),
            semantic_regime=k1.SEMANTIC_REGIME_ID,
        )
        primitive_refs[name] = k1.SemanticPrimitiveRef(
            identifier, module_id, ordinal
        )

    nat64 = _natural_type(k1, UINT64_MAX)
    raw_transcript = _record_type(
        k1, tuple((ordinal, nat64) for ordinal in range(4))
    )
    raw_pair = _record_type(k1, ((0, raw_transcript), (1, raw_transcript)))
    representative_transcript = _record_type(
        k1,
        (
            (0, _natural_type(k1, 8)),
            (1, _natural_type(k1, 22)),
            (2, _natural_type(k1, 7)),
            (3, _natural_type(k1, 10)),
        ),
    )
    representative_pair = _record_type(
        k1,
        ((0, representative_transcript), (1, representative_transcript)),
    )
    witness_type = _natural_type(k1, 10)
    stream_state = _natural_type(k1, 308)
    yield_payload = _record_type(
        k1, ((0, representative_pair), (1, stream_state))
    )
    terminal_payload = _record_type(
        k1,
        (
            (0, _natural_type(k1, 308)),
            (1, k1.ValueType(k1.BYTES_DOMAIN, k1.BytesSchema(32, 32))),
        ),
    )
    stream_output = _variant_type(k1, ((0, yield_payload), (1, terminal_payload)))

    raw_root = k1.Variable(0, raw_pair)
    normalization = k1.CanonicalAlgorithm(
        k1.Symbol("analysis.finite-cover.normalization"),
        (raw_pair,),
        k1.RecordConstruct(
            (
                (0, _normalized_transcript_term(k1, primitive_refs, raw_root, 0)),
                (1, _normalized_transcript_term(k1, primitive_refs, raw_root, 1)),
            )
        ),
        diagnostic_label=k1.Symbol("schnorr-pair-normalization"),
    )

    representative_root = k1.Variable(0, representative_pair)
    embedding = k1.CanonicalAlgorithm(
        k1.Symbol("analysis.finite-cover.representative-embedding"),
        (representative_pair,),
        k1.RecordConstruct(
            (
                (0, _widened_transcript_term(k1, primitive_refs, representative_root, 0)),
                (1, _widened_transcript_term(k1, primitive_refs, representative_root, 1)),
            )
        ),
        diagnostic_label=k1.Symbol("schnorr-pair-embedding"),
    )

    candidate_root = k1.Variable(0, raw_pair)
    response_difference = k1.PrimitiveCall(
        primitive_refs["natural.subtract-modulo-positive"],
        (
            _project_path(k1, candidate_root, 0, 3),
            _project_path(k1, candidate_root, 1, 3),
            _literal(k1, _natural_type(k1, 11), k1.Nat(11)),
        ),
    )
    challenge_difference = k1.PrimitiveCall(
        primitive_refs["natural.subtract-modulo-positive"],
        (
            _project_path(k1, candidate_root, 0, 2),
            _project_path(k1, candidate_root, 1, 2),
            _literal(k1, _natural_type(k1, 11), k1.Nat(11)),
        ),
    )
    inverse = k1.PrimitiveCall(
        primitive_refs["natural.inverse-modulo-coprime"],
        (
            challenge_difference,
            _literal(k1, _natural_type(k1, 11), k1.Nat(11)),
        ),
    )
    candidate = k1.CanonicalAlgorithm(
        k1.Symbol("analysis.fixed-extractor.response-difference"),
        (raw_pair,),
        k1.PrimitiveCall(
            primitive_refs["natural.multiply-modulo-positive"],
            (
                response_difference,
                inverse,
                _literal(k1, _natural_type(k1, 11), k1.Nat(11)),
            ),
        ),
        diagnostic_label=k1.Symbol("bounded-schnorr-fixed-extractor"),
    )

    representative_datums = _canonical_representative_datums(k1)
    stream_digest = ordered_stream_digest(k1, representative_datums)
    representatives_value = k1.admit_value(
        _sequence_type(k1, representative_pair, 308),
        k1.DatumSeq(representative_datums),
    )
    successors_value = k1.admit_value(
        _sequence_type(k1, stream_state, 308),
        k1.DatumSeq(tuple(k1.Nat(index + 1) for index in range(308))),
    )
    index_failure = k1.SemanticFailureType(module_id, 2, k1.UNIT_VALUE)
    state = k1.Variable(0, stream_state)
    at_terminal = k1.PrimitiveCall(
        primitive_refs["natural.equal"],
        (state, _literal(k1, stream_state, k1.Nat(308))),
    )
    yielded = k1.Inject(
        0,
        k1.RecordConstruct(
            (
                (0, k1.StrictIndex(k1.Literal(representatives_value), state, index_failure)),
                (1, k1.StrictIndex(k1.Literal(successors_value), state, index_failure)),
            )
        ),
        stream_output,
    )
    terminal = k1.Inject(
        1,
        k1.RecordConstruct(
            (
                (0, _literal(k1, _natural_type(k1, 308), k1.Nat(308))),
                (
                    1,
                    _literal(
                        k1,
                        k1.ValueType(k1.BYTES_DOMAIN, k1.BytesSchema(32, 32)),
                        k1.BytesValue(stream_digest),
                    ),
                ),
            )
        ),
        stream_output,
    )
    stream = k1.CanonicalAlgorithm(
        k1.Symbol("analysis.finite-cover.representative-stream"),
        (stream_state,),
        k1.Conditional(at_terminal, terminal, yielded),
        diagnostic_label=k1.Symbol("bounded-schnorr-representative-stream"),
    )

    for algorithm in (normalization, embedding, candidate, stream):
        k1.authenticate_algorithm_identity(algorithm)
        k1.validate_term_structure(algorithm.term)
        dependencies = k1.direct_module_dependencies(algorithm)
        k1.authenticate_module_closure(
            dependencies,
            {module_id: module},
            semantic_regime=k1.SEMANTIC_REGIME_ID,
        )
        k1.authenticate_algorithm_declaration_references(
            algorithm,
            {module_id: module},
        )

    return PortableArithmeticBundle(
        module,
        module_id,
        MappingProxyType({module_id: module}),
        MappingProxyType(dict(primitive_refs)),
        raw_transcript,
        raw_pair,
        representative_transcript,
        representative_pair,
        stream_state,
        stream_output,
        witness_type,
        normalization,
        embedding,
        candidate,
        stream,
        representative_datums,
        stream_digest,
    )


def check_quotient_factorization_basis(
    k1: object,
    bundle: PortableArithmeticBundle,
    *,
    group_modulus: int,
    subgroup_order: int,
    generator: int,
    statement: int,
    challenge_count: int,
) -> QuotientFactorizationReceipt:
    """Check the exact symbolic basis used for the raw-to-quotient lift.

    The check is target-specific but universal over the admitted Nat64 carrier:
    it authenticates the exact normalization, embedding, and candidate terms,
    then establishes the periodicity and invertibility facts that make the raw
    verifier predicate and candidate factor through those terms.  Boundary
    examples remain falsifiers only; they are not used as the universal premise.
    """

    if type(bundle) is not PortableArithmeticBundle:
        raise ValueError("factorization basis has another carrier")
    expected = build_bundle(k1)
    exact_fields = (
        "module_id",
        "raw_pair_type",
        "representative_pair_type",
        "normalization_algorithm",
        "embedding_algorithm",
        "candidate_algorithm",
    )
    if any(getattr(bundle, field) != getattr(expected, field) for field in exact_fields):
        raise ValueError("factorization basis changes an exact operation preimage")
    if (
        group_modulus,
        subgroup_order,
        generator,
        statement,
        challenge_count,
    ) != (
        GROUP_MODULUS,
        SUBGROUP_ORDER,
        GENERATOR,
        STATEMENT,
        CHALLENGE_COUNT,
    ):
        raise ValueError("factorization basis is detached from the selected source")
    if group_modulus <= 2 or subgroup_order <= 1 or challenge_count <= 1:
        raise ValueError("factorization basis has degenerate algebraic bounds")
    if challenge_count > subgroup_order:
        raise ValueError("distinct admitted challenges need not remain distinct modulo q")
    if pow(generator, subgroup_order, group_modulus) != 1:
        raise ValueError("response periodicity is not established")
    if any(
        pow(generator, exponent, group_modulus) == 1
        for exponent in range(1, subgroup_order)
    ):
        raise ValueError("the selected generator has smaller order")
    if pow(statement, subgroup_order, group_modulus) != 1:
        raise ValueError("the statement is outside the selected response subgroup")
    if any(
        gcd(first - second, subgroup_order) != 1
        for first in range(challenge_count)
        for second in range(first + 1, challenge_count)
    ):
        raise ValueError("one admitted challenge difference is not invertible modulo q")
    accepted_residues = 0
    for commitment in range(group_modulus):
        for challenge in range(challenge_count):
            responses = tuple(
                response
                for response in range(subgroup_order)
                if pow(generator, response, group_modulus)
                == (
                    commitment * pow(statement, challenge, group_modulus)
                )
                % group_modulus
            )
            if len(responses) > 1:
                raise ValueError("an accepted quotient residue has ambiguous response")
            accepted_residues += len(responses)
    if accepted_residues != subgroup_order * challenge_count:
        raise ValueError("accepted residue count disagrees with the selected quotient")
    return QuotientFactorizationReceipt(
        bundle.module_id,
        bundle.normalization_algorithm.identity,
        bundle.embedding_algorithm.identity,
        bundle.candidate_algorithm.identity,
        9,
        group_modulus,
        challenge_count,
        subgroup_order,
        (
            "raw-statements-are-exactly-anchored-before-modulo-nine",
            "equal-raw-commitments-factor-modulo-group-modulus",
            "verifier-acceptance-is-periodic-in-responses-modulo-subgroup-order",
            "candidate-output-is-periodic-in-responses-modulo-subgroup-order",
            "admitted-challenge-differences-are-invertible-modulo-subgroup-order",
        ),
    )


class CheckedPortableEvaluator:
    """Exact provider for ``PortableArithmeticBundle`` and no other module."""

    def __init__(self, k1: object, bundle: PortableArithmeticBundle) -> None:
        self.k1 = k1
        self.bundle = bundle
        self._primitive_names = {
            reference.identifier: name
            for name, reference in bundle.primitive_refs.items()
        }
        # Exact algorithms and their terms are immutable.  Retaining the object
        # itself makes this an identity cache, not an ID-only trust shortcut:
        # a different preimage that merely repeats an identifier is still
        # authenticated from scratch and rejected.
        self._authenticated_algorithms: dict[int, tuple[object, object]] = {}

    def _literal_positive_modulus(self, term: object) -> int:
        k1 = self.k1
        if (
            type(term) is not k1.Literal
            or type(term.value.datum) is not k1.Nat
            or term.value.datum.value <= 0
        ):
            raise _Unsupported("modulus must be one exact positive literal")
        return term.value.datum.value

    def _primitive_output_type(
        self,
        term: object,
        argument_types: tuple[object, ...],
    ) -> object:
        k1 = self.k1
        name = self._primitive_names.get(term.primitive.identifier)
        if name is None or term.primitive != self.bundle.primitive_refs.get(name):
            raise _Unsupported("primitive has no exact provider interpretation")
        if any(
            type(item) is not k1.ValueType
            or item.domain != k1.NAT_DOMAIN
            or type(item.schema) is not k1.NatSchema
            for item in argument_types
        ):
            raise _Unsupported("natural arithmetic received a non-natural argument")
        if name in ("natural.equal", "natural.less-than"):
            if len(argument_types) != 2:
                raise _Unsupported("comparison has another arity")
            return k1.BOOL
        if name == "natural.widen-u64":
            if len(argument_types) != 1 or argument_types[0].schema.maximum > UINT64_MAX:
                raise _Unsupported("widen-u64 received an unbounded natural")
            return k1.NAT_U64
        modulus_position = {
            "natural.modulo-positive": 1,
            "natural.subtract-modulo-positive": 2,
            "natural.multiply-modulo-positive": 2,
            "natural.power-modulo-positive": 2,
            "natural.inverse-modulo-coprime": 1,
        }.get(name)
        expected_arity = {
            "natural.modulo-positive": 2,
            "natural.subtract-modulo-positive": 3,
            "natural.multiply-modulo-positive": 3,
            "natural.power-modulo-positive": 3,
            "natural.inverse-modulo-coprime": 2,
        }.get(name)
        if modulus_position is None or len(argument_types) != expected_arity:
            raise _Unsupported("primitive has another exact ABI")
        modulus = self._literal_positive_modulus(term.arguments[modulus_position])
        return _natural_type(k1, modulus - 1)

    def _infer(self, term: object, inputs: tuple[object, ...]) -> object:
        k1 = self.k1
        if type(term) is k1.Literal:
            k1.admit_value(term.value.value_type, term.value.datum)
            return term.value.value_type
        if type(term) is k1.Variable:
            if not 0 <= term.index < len(inputs) or term.value_type != inputs[term.index]:
                raise _Unsupported("variable is detached from its exact input type")
            return term.value_type
        if type(term) is k1.RecordConstruct:
            if tuple(item[0] for item in term.fields) != tuple(sorted({item[0] for item in term.fields})):
                raise _Unsupported("record fields are not canonical")
            return _record_type(
                k1,
                tuple((ordinal, self._infer(child, inputs)) for ordinal, child in term.fields),
            )
        if type(term) is k1.Project:
            source = self._infer(term.record, inputs)
            if source.domain != k1.RECORD_DOMAIN or type(source.schema) is not k1.RecordSchema:
                raise _Unsupported("projection source is not a record")
            fields = dict(source.schema.fields)
            if term.ordinal not in fields:
                raise _Unsupported("projection ordinal is absent")
            return fields[term.ordinal]
        if type(term) is k1.Inject:
            payload = self._infer(term.payload, inputs)
            if (
                term.sum_type.domain != k1.VARIANT_DOMAIN
                or type(term.sum_type.schema) is not k1.VariantSchema
                or dict(term.sum_type.schema.cases).get(term.case) != payload
            ):
                raise _Unsupported("variant injection has another exact case type")
            return term.sum_type
        if type(term) is k1.Conditional:
            condition = self._infer(term.condition, inputs)
            when_true = self._infer(term.when_true, inputs)
            when_false = self._infer(term.when_false, inputs)
            if condition != k1.BOOL or when_true != when_false:
                raise _Unsupported("conditional branches have incompatible types")
            return when_true
        if type(term) is k1.StrictIndex:
            source = self._infer(term.source, inputs)
            index = self._infer(term.index, inputs)
            if (
                source.domain != k1.SEQUENCE_DOMAIN
                or type(source.schema) is not k1.SeqSchema
                or index.domain != k1.NAT_DOMAIN
                or type(index.schema) is not k1.NatSchema
                or term.failure_type
                != k1.SemanticFailureType(self.bundle.module_id, 2, k1.UNIT_VALUE)
            ):
                raise _Unsupported("strict-index has another exact ABI")
            return source.schema.element
        if type(term) is k1.PrimitiveCall:
            return self._primitive_output_type(
                term, tuple(self._infer(item, inputs) for item in term.arguments)
            )
        raise _Unsupported("term constructor is outside the focused evaluator")

    def _evaluate_primitive(self, term: object, arguments: tuple[object, ...]) -> object:
        k1 = self.k1
        name = self._primitive_names[term.primitive.identifier]
        values = tuple(item.datum.value for item in arguments)
        if name == "natural.equal":
            datum = values[0] == values[1]
            return k1.admit_value(k1.BOOL, datum)
        if name == "natural.less-than":
            datum = values[0] < values[1]
            return k1.admit_value(k1.BOOL, datum)
        if name == "natural.widen-u64":
            return k1.admit_value(k1.NAT_U64, k1.Nat(values[0]))
        modulus = values[-1]
        if modulus == 0:
            raise _DomainFailure("zero-modulus")
        output_type = _natural_type(k1, modulus - 1)
        if name == "natural.modulo-positive":
            result = values[0] % modulus
        elif name == "natural.subtract-modulo-positive":
            result = (values[0] - values[1]) % modulus
        elif name == "natural.multiply-modulo-positive":
            result = (values[0] * values[1]) % modulus
        elif name == "natural.power-modulo-positive":
            result = pow(values[0], values[1], modulus)
        elif name == "natural.inverse-modulo-coprime":
            if gcd(values[0], modulus) != 1:
                raise _DomainFailure("non-invertible")
            result = pow(values[0], -1, modulus)
        else:  # pragma: no cover - closed by the exact provider map
            raise _Unsupported("primitive provider is incomplete")
        return k1.admit_value(output_type, k1.Nat(result))

    def evaluate(
        self,
        algorithm: object,
        inputs: tuple[object, ...],
        *,
        limits: PortableEvaluationLimits = PortableEvaluationLimits(),
        module_preimages: Mapping[object, object] | None = None,
    ) -> PortableEvaluationResult:
        k1 = self.k1
        steps = 0
        primitive_work = 0

        def charge(*, primitive: bool = False) -> None:
            nonlocal steps, primitive_work
            next_steps = steps + 1
            next_primitive = primitive_work + (1 if primitive else 0)
            if (
                next_steps > limits.maximum_steps
                or next_primitive > limits.maximum_primitive_work
            ):
                raise _LimitExceeded
            steps = next_steps
            primitive_work = next_primitive

        def run(term: object, values: tuple[object, ...]) -> object:
            charge(primitive=type(term) is k1.PrimitiveCall)
            if type(term) is k1.Literal:
                # Full admission happened while deriving the authenticated
                # algorithm's output type.  CanonicalValue is immutable.
                return term.value
            if type(term) is k1.Variable:
                return values[term.index]
            if type(term) is k1.RecordConstruct:
                children = tuple((ordinal, run(child, values).datum) for ordinal, child in term.fields)
                result_type = self._infer(term, algorithm.inputs)
                return k1.admit_value(result_type, k1.DatumRecord(children))
            if type(term) is k1.Project:
                source = run(term.record, values)
                child = dict(source.datum.fields)[term.ordinal]
                return k1.admit_value(self._infer(term, algorithm.inputs), child)
            if type(term) is k1.Inject:
                payload = run(term.payload, values)
                return k1.admit_value(term.sum_type, k1.DatumVariant(term.case, payload.datum))
            if type(term) is k1.Conditional:
                condition = run(term.condition, values)
                branch = term.when_true if condition.datum is True else term.when_false
                return run(branch, values)
            if type(term) is k1.StrictIndex:
                source = run(term.source, values)
                index = run(term.index, values)
                if index.datum.value >= len(source.datum.values):
                    raise _DomainFailure("stream-index-out-of-range")
                return k1.admit_value(
                    source.value_type.schema.element,
                    source.datum.values[index.datum.value],
                )
            if type(term) is k1.PrimitiveCall:
                arguments = tuple(run(item, values) for item in term.arguments)
                return self._evaluate_primitive(term, arguments)
            raise _Unsupported("term constructor is outside the focused evaluator")

        try:
            if type(limits) is not PortableEvaluationLimits or any(
                type(item) is not int or item < 0
                for item in (
                    limits.maximum_steps,
                    limits.maximum_primitive_work,
                    limits.maximum_result_bytes,
                )
            ):
                return PortableEvaluationResult("malformed", detail="limits are malformed")
            supplied = (
                dict(self.bundle.module_preimages)
                if module_preimages is None
                else dict(module_preimages)
            )
            cache_entry = self._authenticated_algorithms.get(id(algorithm))
            if (
                module_preimages is None
                and cache_entry is not None
                and cache_entry[0] is algorithm
            ):
                output_type = cache_entry[1]
            else:
                k1.authenticate_algorithm_identity(algorithm)
                k1.validate_term_structure(algorithm.term)
                dependencies = k1.direct_module_dependencies(algorithm)
                missing = tuple(item for item in dependencies if item not in supplied)
                if missing:
                    return PortableEvaluationResult(
                        "missing-dependency",
                        detail="one exact module preimage is absent",
                    )
                k1.authenticate_module_closure(
                    dependencies,
                    supplied,
                    semantic_regime=k1.SEMANTIC_REGIME_ID,
                )
                k1.authenticate_algorithm_declaration_references(
                    algorithm, supplied
                )
                if supplied != dict(self.bundle.module_preimages):
                    return PortableEvaluationResult(
                        "refused",
                        detail=(
                            "module closure differs from the exact provider closure"
                        ),
                    )
                output_type = self._infer(algorithm.term, algorithm.inputs)
                if module_preimages is None:
                    self._authenticated_algorithms[id(algorithm)] = (
                        algorithm,
                        output_type,
                    )
            if type(inputs) is not tuple or len(inputs) != len(algorithm.inputs):
                return PortableEvaluationResult("kind-mismatch", detail="input arity differs")
            admitted = []
            for supplied_value, expected_type in zip(inputs, algorithm.inputs, strict=True):
                if type(supplied_value) is not k1.CanonicalValue:
                    return PortableEvaluationResult("malformed", detail="input carrier is malformed")
                if supplied_value.value_type != expected_type:
                    return PortableEvaluationResult("kind-mismatch", detail="input type differs")
                admitted.append(k1.admit_value(expected_type, supplied_value.datum))
            value = run(algorithm.term, tuple(admitted))
            if value.value_type != output_type:
                return PortableEvaluationResult(
                    "checker-failure", detail="provider output disagrees with derived type"
                )
            result_bytes = len(k1.encode_datum(value.datum))
            if result_bytes > limits.maximum_result_bytes:
                raise _LimitExceeded
            return PortableEvaluationResult(
                "success",
                value,
                charge=PortableEvaluationCharge(steps, primitive_work, result_bytes),
            )
        except _DomainFailure as failure:
            return PortableEvaluationResult(
                "domain-failure",
                failure_label=failure.label,
                charge=PortableEvaluationCharge(steps, primitive_work, 0),
            )
        except _LimitExceeded:
            return PortableEvaluationResult(
                "deterministic-limit-exceeded",
                charge=PortableEvaluationCharge(steps, primitive_work, 0),
            )
        except _Unsupported as error:
            return PortableEvaluationResult(
                "unsupported",
                charge=PortableEvaluationCharge(steps, primitive_work, 0),
                detail=str(error),
            )
        except getattr(k1, "_Control") as error:
            return PortableEvaluationResult(
                getattr(error.outcome, "value", str(error.outcome)),
                charge=PortableEvaluationCharge(steps, primitive_work, 0),
                detail=error.detail,
            )
        except (k1.CanonicalError, k1.ModelError, AttributeError, TypeError, ValueError) as error:
            return PortableEvaluationResult(
                "malformed",
                charge=PortableEvaluationCharge(steps, primitive_work, 0),
                detail=str(error),
            )
