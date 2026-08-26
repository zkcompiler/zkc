"""Bounded executable candidate for the K2 Protocol/Fiat--Shamir kernel.

This module is a research instrument, not repository authority.  It imports
K1's canonical ``Datum`` and typed content-identity machinery and adds only the
finite protocol surface needed by the K2 fixtures.  The model deliberately
separates three questions:

* ``admit_core`` checks one exact finite interaction schedule;
* ``generate`` asks a causal prover strategy for each current move through a
  restricted view; and
* ``replay`` checks a completed record without claiming that a causal strategy
  generated it.

The same literal ``Core`` is interpreted with fresh public coins or with an
admitted transcript construction.  Transcript influence is derived from the
Core; there is no per-message author-controlled "absorb" bit.
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from enum import Enum
import hashlib
import importlib.util
from pathlib import Path
import sys
from types import MappingProxyType
from typing import Callable, Mapping, Protocol, TypeAlias


# ---------------------------------------------------------------------------
# K1 foundation import
# ---------------------------------------------------------------------------


_K1_NAME = "_zkc_k1_executable_foundations"
_K1_PATH = (
    Path(__file__).resolve().parents[1]
    / "k1-executable-foundations"
    / "reference_model.py"
)
if _K1_NAME in sys.modules:
    k1 = sys.modules[_K1_NAME]
else:
    _spec = importlib.util.spec_from_file_location(_K1_NAME, _K1_PATH)
    if _spec is None or _spec.loader is None:  # pragma: no cover - host failure
        raise ImportError(f"cannot load K1 reference model from {_K1_PATH}")
    k1 = importlib.util.module_from_spec(_spec)
    sys.modules[_K1_NAME] = k1
    _spec.loader.exec_module(k1)


# ---------------------------------------------------------------------------
# Finite carriers and typed refusals
# ---------------------------------------------------------------------------


MAX_INPUTS = 128
MAX_SCOPES = 64
MAX_OCCURRENCES = 512
MAX_DEPENDENCIES = 64
MAX_CLAIMS = 256
MAX_ORACLE_CELLS = 4096
MAX_CELL_BYTES = 1 << 16


class ModelError(ValueError):
    """Base class for a K2 model refusal."""


class AdmissionError(ModelError):
    """The Core or construction is outside the selected K2 surface."""


class InvocationError(ModelError):
    """An invocation does not provide the Core's exact input surface."""


class ReplayError(ModelError):
    """A completed record is not an exact run of the selected interpretation."""


class ExecutionError(ModelError):
    """A deterministic protocol operation is undefined on this invocation."""


class FutureReadError(ModelError):
    """A strategy attempted to observe an occurrence not yet available."""


@dataclass(frozen=True)
class SamplingExhausted(ModelError):
    namespaces: tuple[bytes, ...]
    terminal_state: bytes
    attempts: int

    def __str__(self) -> str:
        return f"sampling exhausted after {self.attempts} attempts"


class InputRole(str, Enum):
    STATEMENT = "statement"
    PUBLIC_CONTEXT = "public-context"
    PUBLIC_PARAMETER = "public-parameter"
    VERIFIER_PRIVATE = "verifier-private"


class ValueSort(str, Enum):
    BYTES = "bytes"
    NAT = "nat"
    BOOL = "bool"
    ORACLE = "oracle"


class OccurrenceKind(str, Enum):
    PROVER_MESSAGE = "prover-message"
    VERIFIER_MESSAGE = "verifier-message"
    CHALLENGE = "challenge"
    CHECK = "check"
    TERMINAL = "terminal"
    ORACLE_PUBLISH = "oracle-publish"
    ORACLE_QUERY = "oracle-query"
    ORACLE_ANSWER = "oracle-answer"


class RefKind(str, Enum):
    INPUT = "input"
    OCCURRENCE = "occurrence"


@dataclass(frozen=True)
class ValueRef:
    kind: RefKind
    name: str

    @classmethod
    def input(cls, name: str) -> "ValueRef":
        return cls(RefKind.INPUT, name)

    @classmethod
    def occurrence(cls, name: str) -> "ValueRef":
        return cls(RefKind.OCCURRENCE, name)


@dataclass(frozen=True)
class InputDecl:
    name: str
    role: InputRole
    scope: str = "root"
    value_sort: ValueSort = ValueSort.BYTES


@dataclass(frozen=True)
class ScopeDecl:
    """One unconditional lexical scope activation.

    ``open_before=None`` means open during initialization.  Otherwise the
    scope opens immediately before the named occurrence, against the current
    transcript state.  Opening never resets the state.
    """

    name: str
    parent: str | None
    open_before: str | None


class PredicateKind(str, Enum):
    ALWAYS = "always"
    NEVER = "never"
    BOOL = "bool"
    BYTES_EQUAL = "bytes-equal"
    SCHNORR = "fixture-schnorr"
    LEADING_ZERO_BITS = "fixture-leading-zero-bits"


@dataclass(frozen=True)
class Predicate:
    """A bounded pure fixture predicate, the permitted non-K1 guard lane."""

    kind: PredicateKind = PredicateKind.ALWAYS
    refs: tuple[ValueRef, ...] = ()
    parameters: tuple[int, ...] = ()


class VerifierRuleKind(str, Enum):
    COPY = "copy"
    SHA256 = "sha2-256"
    CONSTANT_INT = "constant-int"


@dataclass(frozen=True)
class VerifierRule:
    kind: VerifierRuleKind
    parameters: tuple[int, ...] = ()


@dataclass(frozen=True)
class ChallengeDomain:
    modulus: int


@dataclass(frozen=True)
class Occurrence:
    name: str
    kind: OccurrenceKind
    scope: str = "root"
    dependencies: tuple[ValueRef, ...] = ()
    guard: Predicate = Predicate()
    verifier_rule: VerifierRule | None = None
    challenge_domain: ChallengeDomain | None = None
    oracle_name: str | None = None
    check_predicate: Predicate | None = None
    prover_value_sort: ValueSort = ValueSort.BYTES


@dataclass(frozen=True)
class RequiredPublication:
    publication: str
    next_challenge: str | None


@dataclass(frozen=True)
class ReductionDecl:
    name: str
    at_occurrence: str
    scope: str
    input_claims: tuple[str, ...]
    side_inputs: tuple[ValueRef, ...]
    required_challenges: tuple[str, ...]
    required_publications: tuple[RequiredPublication, ...]
    output_claims: tuple[str, ...]


@dataclass(frozen=True)
class ClaimConsumerUse:
    claim: str
    consumer: str


@dataclass(frozen=True)
class Core:
    inputs: tuple[InputDecl, ...]
    scopes: tuple[ScopeDecl, ...]
    schedule: tuple[Occurrence, ...]
    extensions: tuple[str, ...] = ()
    initial_claims: tuple[str, ...] = ()
    reductions: tuple[ReductionDecl, ...] = ()
    claim_uses: tuple[ClaimConsumerUse, ...] = ()


@dataclass(frozen=True)
class OracleObject:
    cells: tuple[bytes, ...]


Value: TypeAlias = bytes | int | bool | OracleObject


@dataclass(frozen=True)
class Invocation:
    values: Mapping[str, Value]
    public_coins: Mapping[str, int]


@dataclass(frozen=True)
class InfluenceAtom:
    """One finite, coordinate-bearing transcript-influence obligation."""

    kind: str
    coordinates: tuple[str, ...]


@dataclass(frozen=True)
class Frame:
    tag: str
    payload: bytes
    atom: InfluenceAtom


@dataclass(frozen=True)
class InfluenceComparison:
    required: tuple[InfluenceAtom, ...]
    observed: tuple[InfluenceAtom, ...]
    missing: tuple[InfluenceAtom, ...]


class EntryStatus(str, Enum):
    EXECUTED = "executed"
    SKIPPED = "skipped"


@dataclass(frozen=True)
class RunEntry:
    occurrence: str
    kind: OccurrenceKind
    status: EntryStatus
    value: Value | None
    prefix_state: bytes | None = None
    draw_namespaces: tuple[bytes, ...] = ()
    sampling_attempts: int | None = None
    influence: InfluenceComparison | None = None


@dataclass(frozen=True)
class RunRecord:
    core_id: object
    construction_id: object | None
    invocation_id: object
    interpretation: "ChallengeInterpretation"
    entries: tuple[RunEntry, ...]
    transcript_frames: tuple[Frame, ...]
    terminal_state: bytes | None


class ChallengeInterpretation(str, Enum):
    FRESH = "fresh-public-coins"
    FIAT_SHAMIR = "fiat-shamir"


class NoncompletionReason(str, Enum):
    STRATEGY_STOPPED = "strategy-stopped"
    FUTURE_READ = "future-read"
    INVALID_MOVE = "invalid-move"


@dataclass(frozen=True)
class Noncompletion:
    reason: NoncompletionReason
    at_occurrence: str
    detail: str


@dataclass(frozen=True)
class Completed:
    record: RunRecord


GenerationResult: TypeAlias = Completed | Noncompletion


class StrategyStopped(Exception):
    """A strategy may decline a move without creating a Core terminal."""


class ProverStrategy(Protocol):
    def move(self, occurrence: Occurrence, view: "ProverView") -> Value:
        ...


# ---------------------------------------------------------------------------
# Canonical K1-backed identity
# ---------------------------------------------------------------------------


def _symbol(text: str, what: str) -> object:
    if type(text) is not str or not text or any(ord(ch) < 0x21 or ord(ch) > 0x7E for ch in text):
        raise AdmissionError(f"{what} must be nonempty printable ASCII without spaces")
    return k1.Symbol(text)


def _datum(value: Value | None) -> object:
    if value is None:
        return k1.DatumVariant(0, k1.UNIT)
    if type(value) is bytes:
        return k1.DatumVariant(1, k1.BytesValue(value))
    if type(value) is int:
        if value < 0:
            raise ModelError("fixture values use nonnegative integers")
        return k1.DatumVariant(2, k1.Nat(value))
    if type(value) is bool:
        return k1.DatumVariant(3, value)
    if type(value) is OracleObject:
        return k1.DatumVariant(
            4,
            k1.DatumSeq(tuple(k1.BytesValue(cell) for cell in value.cells)),
        )
    raise ModelError(f"unsupported fixture value: {type(value)!r}")


def _appendix_ref(value: int, what: str) -> object:
    """Form one exact Appendix-A natural reference coordinate."""

    if type(value) is not int or not 0 <= value < 1 << 64:
        raise ModelError(f"{what} must be an unsigned 64-bit natural")
    return k1.Nat(value)


def appendix_guard_outcome_frame_body(
    occurrence_ref: int,
    active: bool,
) -> object:
    """Form the exact K2 Appendix-A GuardOutcome frame body.

    K1 Boolean values are MetaBooleanFalse/MetaBooleanTrue scalar datums.  In
    particular, this body deliberately does not wrap ``active`` in a generic
    MetaVariant.
    """

    if type(active) is not bool:
        raise ModelError("guard outcome must be one exact K1 Boolean")
    return k1.DatumVariant(
        5,
        k1.DatumRecord(
            (
                (0, _appendix_ref(occurrence_ref, "occurrence reference")),
                (1, active),
            )
        ),
    )


def appendix_oracle_lookup_result_type(element_type: object) -> object:
    """Form ``RootVariant<[(0, RootUnit), (1, element_type)]>`` exactly."""

    if type(element_type) is not k1.ValueType:
        raise ModelError("Oracle element type must be one exact K1 ValueType")
    if element_type.domain.semantic_regime != k1.SEMANTIC_REGIME_ID:
        raise ModelError("Oracle element type crosses the K2 fixture regime")
    unit_type = k1.ValueType(k1.UNIT_DOMAIN, k1.UNIT_SCHEMA)
    return k1.ValueType(
        k1.VARIANT_DOMAIN,
        k1.VariantSchema(((0, unit_type), (1, element_type))),
    )


def appendix_oracle_answer_frame_body(
    occurrence_ref: int,
    oracle_ref: int,
    element_type: object,
    answer: object,
) -> object:
    """Form one exact K2 Appendix-A OracleAnswer frame body.

    The type carried in field 2 is the derived lookup-result sum, never the
    element type.  Admission at that sum makes both absent and present answers
    formable before the frame is returned.
    """

    result_type = appendix_oracle_lookup_result_type(element_type)
    admitted = k1.admit_value(result_type, answer)
    return k1.DatumVariant(
        10,
        k1.DatumRecord(
            (
                (0, _appendix_ref(occurrence_ref, "occurrence reference")),
                (1, _appendix_ref(oracle_ref, "Oracle reference")),
                (2, k1.value_type_datum(result_type)),
                (3, admitted.datum),
            )
        ),
    )


def _ref_datum(ref: ValueRef) -> object:
    return k1.DatumRecord(
        ((0, k1.Symbol(ref.kind.value)), (1, _symbol(ref.name, "reference name")))
    )


def _validate_ref(ref: object) -> ValueRef:
    if type(ref) is not ValueRef or type(ref.kind) is not RefKind:
        raise AdmissionError("value reference has the wrong exact shape")
    _symbol(ref.name, "reference name")
    return ref


def _predicate_datum(predicate: Predicate) -> object:
    return k1.DatumRecord(
        (
            (0, k1.Symbol("fixture-bounded-pure-predicate-v0")),
            (1, k1.Symbol(predicate.kind.value)),
            (2, k1.DatumSeq(tuple(_ref_datum(ref) for ref in predicate.refs))),
            (3, k1.DatumSeq(tuple(k1.Nat(item) for item in predicate.parameters))),
        )
    )


def core_body(core: Core) -> bytes:
    """Return the exact K1 canonical body; schedule order is identity-bearing."""

    admit_core(core)
    datum = k1.DatumRecord(
        (
            (0, k1.Symbol("k2.protocol-core.v1")),
            (
                1,
                k1.DatumSeq(
                    tuple(
                        k1.DatumRecord(
                            (
                                (0, _symbol(item.name, "input name")),
                                (1, k1.Symbol(item.role.value)),
                                (2, _symbol(item.scope, "input scope")),
                                (3, k1.Symbol(item.value_sort.value)),
                            )
                        )
                        for item in core.inputs
                    )
                ),
            ),
            (
                2,
                k1.DatumSeq(
                    tuple(
                        k1.DatumRecord(
                            (
                                (0, _symbol(item.name, "scope name")),
                                (
                                    1,
                                    k1.DatumVariant(
                                        0 if item.parent is None else 1,
                                        k1.UNIT
                                        if item.parent is None
                                        else _symbol(item.parent, "parent scope"),
                                    ),
                                ),
                                (
                                    2,
                                    k1.DatumVariant(
                                        0 if item.open_before is None else 1,
                                        k1.UNIT
                                        if item.open_before is None
                                        else _symbol(item.open_before, "scope opening"),
                                    ),
                                ),
                            )
                        )
                        for item in core.scopes
                    )
                ),
            ),
            (
                3,
                k1.DatumSeq(
                    tuple(
                        k1.DatumRecord(
                            (
                                (0, _symbol(item.name, "occurrence name")),
                                (1, k1.Symbol(item.kind.value)),
                                (2, _symbol(item.scope, "occurrence scope")),
                                (
                                    3,
                                    k1.DatumSeq(
                                        tuple(_ref_datum(ref) for ref in item.dependencies)
                                    ),
                                ),
                                (4, _predicate_datum(item.guard)),
                                (
                                    5,
                                    k1.DatumVariant(
                                        0 if item.verifier_rule is None else 1,
                                        k1.UNIT
                                        if item.verifier_rule is None
                                        else k1.DatumRecord(
                                            (
                                                (
                                                    0,
                                                    k1.Symbol(item.verifier_rule.kind.value),
                                                ),
                                                (
                                                    1,
                                                    k1.DatumSeq(
                                                        tuple(
                                                            k1.Nat(value)
                                                            for value in item.verifier_rule.parameters
                                                        )
                                                    ),
                                                ),
                                            )
                                        ),
                                    ),
                                ),
                                (
                                    6,
                                    k1.DatumVariant(
                                        0 if item.challenge_domain is None else 1,
                                        k1.UNIT
                                        if item.challenge_domain is None
                                        else k1.Nat(item.challenge_domain.modulus),
                                    ),
                                ),
                                (
                                    7,
                                    k1.DatumVariant(
                                        0 if item.oracle_name is None else 1,
                                        k1.UNIT
                                        if item.oracle_name is None
                                        else _symbol(item.oracle_name, "oracle name"),
                                    ),
                                ),
                                (
                                    8,
                                    k1.DatumVariant(
                                        0 if item.check_predicate is None else 1,
                                        k1.UNIT
                                        if item.check_predicate is None
                                        else _predicate_datum(item.check_predicate),
                                    ),
                                ),
                                (9, k1.Symbol(item.prover_value_sort.value)),
                            )
                        )
                        for item in core.schedule
                    )
                ),
            ),
            (4, k1.DatumSeq(tuple(_symbol(item, "extension") for item in core.extensions))),
            (5, k1.DatumSeq(tuple(_symbol(item, "claim") for item in core.initial_claims))),
            (
                6,
                k1.DatumSeq(
                    tuple(
                        k1.DatumRecord(
                            (
                                (0, _symbol(step.name, "reduction name")),
                                (1, _symbol(step.at_occurrence, "reduction occurrence")),
                                (2, _symbol(step.scope, "reduction scope")),
                                (
                                    3,
                                    k1.DatumSeq(
                                        tuple(
                                            _symbol(claim, "input claim")
                                            for claim in step.input_claims
                                        )
                                    ),
                                ),
                                (
                                    4,
                                    k1.DatumSeq(
                                        tuple(_ref_datum(ref) for ref in step.side_inputs)
                                    ),
                                ),
                                (
                                    5,
                                    k1.DatumSeq(
                                        tuple(
                                            _symbol(challenge, "required challenge")
                                            for challenge in step.required_challenges
                                        )
                                    ),
                                ),
                                (
                                    6,
                                    k1.DatumSeq(
                                        tuple(
                                            k1.DatumRecord(
                                                (
                                                    (
                                                        0,
                                                        _symbol(
                                                            required.publication,
                                                            "required publication",
                                                        ),
                                                    ),
                                                    (
                                                        1,
                                                        k1.DatumVariant(
                                                            0,
                                                            k1.UNIT,
                                                        )
                                                        if required.next_challenge is None
                                                        else k1.DatumVariant(
                                                            1,
                                                            _symbol(
                                                                required.next_challenge,
                                                                "publication challenge",
                                                            ),
                                                        ),
                                                    ),
                                                )
                                            )
                                            for required in step.required_publications
                                        )
                                    ),
                                ),
                                (
                                    7,
                                    k1.DatumSeq(
                                        tuple(
                                            _symbol(claim, "output claim")
                                            for claim in step.output_claims
                                        )
                                    ),
                                ),
                            )
                        )
                        for step in core.reductions
                    )
                ),
            ),
            (
                7,
                k1.DatumSeq(
                    tuple(
                        k1.DatumRecord(
                            (
                                (0, _symbol(use.claim, "consumed claim")),
                                (1, _symbol(use.consumer, "claim consumer")),
                            )
                        )
                        for use in core.claim_uses
                    )
                ),
            ),
        )
    )
    return k1.encode_datum(datum)


def core_id(core: Core) -> object:
    return k1.content_id(
        "pir.interactive-core",
        core_body(core),
        semantic_regime=k1.SEMANTIC_REGIME_ID,
    )


def invocation_body(core: Core, invocation: Invocation) -> bytes:
    values = admit_invocation(core, invocation)
    datum = k1.DatumRecord(
        (
            (
                0,
                k1.DatumSeq(
                    tuple(
                        k1.DatumRecord(
                            ((0, _symbol(item.name, "input name")), (1, _datum(values[item.name])))
                        )
                        for item in core.inputs
                    )
                ),
            ),
            (
                1,
                k1.DatumSeq(
                    tuple(
                        k1.DatumRecord(
                            ((0, _symbol(name, "challenge name")), (1, k1.Nat(value)))
                        )
                        for name, value in sorted(
                            invocation.public_coins.items(), key=lambda item: item[0]
                        )
                    )
                ),
            ),
        )
    )
    return k1.encode_datum(datum)


def invocation_id(core: Core, invocation: Invocation) -> object:
    return k1.content_id(
        "pir.protocol-invocation",
        invocation_body(core, invocation),
        semantic_regime=k1.SEMANTIC_REGIME_ID,
    )


# ---------------------------------------------------------------------------
# Structural admission
# ---------------------------------------------------------------------------


KNOWN_EXTENSIONS = frozenset({"native-oracle-v0"})


def _bounded_unique(items: tuple[str, ...], limit: int, what: str) -> None:
    if len(items) > limit:
        raise AdmissionError(f"{what} exceeds the finite bound {limit}")
    if len(set(items)) != len(items):
        raise AdmissionError(f"{what} must be unique")
    for item in items:
        _symbol(item, what)


def _sort_accepts(value: Value, expected: ValueSort) -> bool:
    return {
        ValueSort.BYTES: type(value) is bytes,
        ValueSort.NAT: type(value) is int and value >= 0,
        ValueSort.BOOL: type(value) is bool,
        ValueSort.ORACLE: type(value) is OracleObject,
    }[expected]


def _validate_predicate(
    predicate: Predicate,
    available: set[ValueRef],
    sorts: Mapping[ValueRef, ValueSort],
) -> None:
    if type(predicate) is not Predicate or type(predicate.kind) is not PredicateKind:
        raise AdmissionError("guards/checks must use an exact bounded predicate")
    if len(predicate.refs) > MAX_DEPENDENCIES:
        raise AdmissionError("predicate dependency bound exceeded")
    if type(predicate.refs) is not tuple or type(predicate.parameters) is not tuple:
        raise AdmissionError("predicate aggregates must be immutable tuples")
    for ref in predicate.refs:
        _validate_ref(ref)
    if any(ref not in available for ref in predicate.refs):
        raise AdmissionError("predicate references a value outside its exact prefix")
    expected = {
        PredicateKind.ALWAYS: (0, 0),
        PredicateKind.NEVER: (0, 0),
        PredicateKind.BOOL: (1, 0),
        PredicateKind.BYTES_EQUAL: (2, 0),
        PredicateKind.SCHNORR: (6, 1),
        PredicateKind.LEADING_ZERO_BITS: (1, 1),
    }[predicate.kind]
    if len(predicate.refs) != expected[0] or len(predicate.parameters) != expected[1]:
        raise AdmissionError("predicate arity does not match its frozen fixture law")
    if any(type(item) is not int or item < 0 for item in predicate.parameters):
        raise AdmissionError("predicate parameters must be nonnegative exact integers")
    if predicate.kind is PredicateKind.SCHNORR and predicate.parameters[0] <= 1:
        raise AdmissionError("Schnorr fixture order must exceed one")
    if (
        predicate.kind is PredicateKind.LEADING_ZERO_BITS
        and predicate.parameters[0] > 256
    ):
        raise AdmissionError("grinding fixture work factor exceeds SHA-256 width")
    expected_sorts = {
        PredicateKind.ALWAYS: (),
        PredicateKind.NEVER: (),
        PredicateKind.BOOL: (ValueSort.BOOL,),
        PredicateKind.BYTES_EQUAL: (ValueSort.BYTES, ValueSort.BYTES),
        PredicateKind.SCHNORR: (ValueSort.NAT,) * 6,
        PredicateKind.LEADING_ZERO_BITS: (ValueSort.BYTES,),
    }[predicate.kind]
    if tuple(sorts[ref] for ref in predicate.refs) != expected_sorts:
        raise AdmissionError("predicate reference sorts do not match its frozen law")


def _occurrence_sort(
    occurrence: Occurrence,
    sorts: Mapping[ValueRef, ValueSort],
) -> ValueSort:
    if occurrence.kind is OccurrenceKind.PROVER_MESSAGE:
        return occurrence.prover_value_sort
    if occurrence.kind is OccurrenceKind.VERIFIER_MESSAGE:
        assert occurrence.verifier_rule is not None
        if occurrence.verifier_rule.kind is VerifierRuleKind.COPY:
            return sorts[occurrence.dependencies[0]]
        if occurrence.verifier_rule.kind is VerifierRuleKind.SHA256:
            if any(sorts[ref] is not ValueSort.BYTES for ref in occurrence.dependencies):
                raise AdmissionError("SHA-256 verifier inputs must be byte strings")
            return ValueSort.BYTES
        return ValueSort.NAT
    return {
        OccurrenceKind.CHALLENGE: ValueSort.NAT,
        OccurrenceKind.CHECK: ValueSort.BOOL,
        OccurrenceKind.TERMINAL: ValueSort.BOOL,
        OccurrenceKind.ORACLE_PUBLISH: ValueSort.ORACLE,
        OccurrenceKind.ORACLE_QUERY: ValueSort.NAT,
        OccurrenceKind.ORACLE_ANSWER: ValueSort.BYTES,
    }[occurrence.kind]


def admit_core(core: Core) -> None:
    if type(core) is not Core:
        raise AdmissionError("Core must have the exact immutable carrier")
    if (
        type(core.inputs) is not tuple
        or type(core.scopes) is not tuple
        or type(core.schedule) is not tuple
        or type(core.extensions) is not tuple
        or type(core.initial_claims) is not tuple
        or type(core.reductions) is not tuple
        or type(core.claim_uses) is not tuple
    ):
        raise AdmissionError("Core aggregates must be immutable tuples")

    input_names = tuple(item.name for item in core.inputs)
    _bounded_unique(input_names, MAX_INPUTS, "input names")
    if any(
        type(item) is not InputDecl
        or type(item.role) is not InputRole
        or type(item.value_sort) is not ValueSort
        or item.value_sort is ValueSort.ORACLE
        for item in core.inputs
    ):
        raise AdmissionError("input declarations have the wrong exact shape")

    scope_names = tuple(item.name for item in core.scopes)
    _bounded_unique(scope_names, MAX_SCOPES, "scope names")
    if not core.scopes or core.scopes[0] != ScopeDecl("root", None, None):
        raise AdmissionError("the first scope must be the initially open root scope")
    occurrence_names = tuple(item.name for item in core.schedule)
    _bounded_unique(occurrence_names, MAX_OCCURRENCES, "occurrence names")
    occurrence_index = {name: index for index, name in enumerate(occurrence_names)}
    scope_index = {name: index for index, name in enumerate(scope_names)}
    for index, scope in enumerate(core.scopes):
        if type(scope) is not ScopeDecl:
            raise AdmissionError("scope declarations have the wrong exact shape")
        if index == 0:
            continue
        if scope.parent not in scope_index or scope_index[scope.parent] >= index:
            raise AdmissionError("nested scope parent must precede the child")
        if scope.open_before not in occurrence_index:
            raise AdmissionError("nested scope must open before a named occurrence")
        parent = core.scopes[scope_index[scope.parent]]
        parent_open = -1 if parent.open_before is None else occurrence_index[parent.open_before]
        if occurrence_index[scope.open_before] < parent_open:
            raise AdmissionError("nested scope cannot open before its parent")
    if any(item.scope not in scope_index for item in core.inputs):
        raise AdmissionError("every input must belong to a declared scope")

    if not core.schedule:
        raise AdmissionError("a Core needs a nonempty exact total schedule")
    if sum(item.kind is OccurrenceKind.TERMINAL for item in core.schedule) != 1:
        raise AdmissionError("a Core needs exactly one terminal occurrence")
    if core.schedule[-1].kind is not OccurrenceKind.TERMINAL:
        raise AdmissionError("the unique terminal must close the total schedule")

    inputs_by_scope: dict[str, tuple[ValueRef, ...]] = {
        scope: tuple(
            ValueRef.input(item.name) for item in core.inputs if item.scope == scope
        )
        for scope in scope_names
    }
    available: set[ValueRef] = set(inputs_by_scope["root"])
    input_by_name = {item.name: item for item in core.inputs}
    sorts: dict[ValueRef, ValueSort] = {
        ref: input_by_name[ref.name].value_sort for ref in available
    }
    scopes_opening_at: dict[int, tuple[str, ...]] = {}
    for scope in core.scopes[1:]:
        assert scope.open_before is not None
        opening_index = occurrence_index[scope.open_before]
        scopes_opening_at[opening_index] = (
            *scopes_opening_at.get(opening_index, ()),
            scope.name,
        )
    published: dict[str, int] = {}
    queries: dict[str, tuple[str, int]] = {}
    answered_queries: set[str] = set()
    oracle_seen = False
    for index, occurrence in enumerate(core.schedule):
        for opening_scope in scopes_opening_at.get(index, ()):
            available.update(inputs_by_scope[opening_scope])
            sorts.update(
                {
                    ref: input_by_name[ref.name].value_sort
                    for ref in inputs_by_scope[opening_scope]
                }
            )
        if type(occurrence) is not Occurrence or type(occurrence.kind) is not OccurrenceKind:
            raise AdmissionError("occurrences have the wrong exact shape")
        _symbol(occurrence.name, "occurrence name")
        if occurrence.scope not in scope_index:
            raise AdmissionError("occurrence names an unknown scope")
        scope = core.scopes[scope_index[occurrence.scope]]
        open_index = -1 if scope.open_before is None else occurrence_index[scope.open_before]
        if index < open_index:
            raise AdmissionError("occurrence precedes activation of its scope")
        if type(occurrence.prover_value_sort) is not ValueSort:
            raise AdmissionError("prover value sort has the wrong exact shape")
        if (
            occurrence.kind is not OccurrenceKind.PROVER_MESSAGE
            and occurrence.prover_value_sort is not ValueSort.BYTES
        ):
            raise AdmissionError("only prover messages may select a prover value sort")
        if type(occurrence.dependencies) is not tuple or len(occurrence.dependencies) > MAX_DEPENDENCIES:
            raise AdmissionError("occurrence dependencies exceed their exact bound")
        for ref in occurrence.dependencies:
            _validate_ref(ref)
        if len(set(occurrence.dependencies)) != len(occurrence.dependencies):
            raise AdmissionError("occurrence dependencies must be unique")
        if any(ref not in available for ref in occurrence.dependencies):
            raise AdmissionError("occurrence dependency is not in the exact prior prefix")
        if (
            occurrence.kind is OccurrenceKind.PROVER_MESSAGE
            and occurrence.dependencies
        ):
            raise AdmissionError(
                "prover messages have no authored dependency field"
            )
        _validate_predicate(occurrence.guard, available, sorts)

        if occurrence.kind is OccurrenceKind.CHALLENGE:
            if type(occurrence.challenge_domain) is not ChallengeDomain:
                raise AdmissionError("challenge occurrence needs an exact domain")
            if type(occurrence.challenge_domain.modulus) is not int or occurrence.challenge_domain.modulus <= 1:
                raise AdmissionError("challenge modulus must be an exact integer above one")
        elif occurrence.challenge_domain is not None:
            raise AdmissionError("only a challenge may carry a challenge domain")

        if occurrence.kind is OccurrenceKind.VERIFIER_MESSAGE:
            if (
                type(occurrence.verifier_rule) is not VerifierRule
                or type(occurrence.verifier_rule.kind) is not VerifierRuleKind
                or type(occurrence.verifier_rule.parameters) is not tuple
                or any(
                    type(item) is not int or item < 0
                    for item in occurrence.verifier_rule.parameters
                )
            ):
                raise AdmissionError("verifier message needs one deterministic rule")
            if (
                occurrence.verifier_rule.kind is VerifierRuleKind.CONSTANT_INT
                and (
                    occurrence.dependencies
                    or len(occurrence.verifier_rule.parameters) != 1
                )
            ):
                raise AdmissionError("constant verifier rule has exact arity zero-to-one")
            if (
                occurrence.verifier_rule.kind is VerifierRuleKind.COPY
                and (
                    len(occurrence.dependencies) != 1
                    or occurrence.verifier_rule.parameters
                )
            ):
                raise AdmissionError("copy verifier rule has exact arity one-to-one")
            if (
                occurrence.verifier_rule.kind is VerifierRuleKind.SHA256
                and occurrence.verifier_rule.parameters
            ):
                raise AdmissionError("SHA-256 verifier rule carries no parameters")
        elif occurrence.verifier_rule is not None:
            raise AdmissionError("only verifier messages may carry a verifier rule")

        if occurrence.kind is OccurrenceKind.CHECK:
            if occurrence.guard.kind is not PredicateKind.ALWAYS:
                raise AdmissionError("checks use dependencies as their predicate, not a path guard")
            if len(occurrence.dependencies) == 0:
                raise AdmissionError("check needs dependencies")
            if occurrence.check_predicate is None:
                raise AdmissionError("check needs an identity-bearing Bool predicate")
            _validate_predicate(occurrence.check_predicate, available, sorts)
            if occurrence.check_predicate.refs != occurrence.dependencies:
                raise AdmissionError("check predicate must use the exact dependency tuple")
        elif occurrence.check_predicate is not None:
            raise AdmissionError("only a check may carry a check predicate")

        if occurrence.kind in {
            OccurrenceKind.ORACLE_PUBLISH,
            OccurrenceKind.ORACLE_QUERY,
            OccurrenceKind.ORACLE_ANSWER,
        }:
            oracle_seen = True
            if occurrence.oracle_name is None:
                raise AdmissionError("oracle occurrence must name its oracle")
            _symbol(occurrence.oracle_name, "oracle name")
        elif occurrence.oracle_name is not None:
            raise AdmissionError("non-oracle occurrence cannot name an oracle")

        if occurrence.kind is OccurrenceKind.ORACLE_PUBLISH:
            assert occurrence.oracle_name is not None
            if occurrence.oracle_name in published:
                raise AdmissionError("an immutable native oracle is published exactly once")
            published[occurrence.oracle_name] = index
        elif occurrence.kind is OccurrenceKind.ORACLE_QUERY:
            assert occurrence.oracle_name is not None
            if occurrence.oracle_name not in published or published[occurrence.oracle_name] >= index:
                raise AdmissionError("native oracle query must follow publication")
            if len(occurrence.dependencies) != 1:
                raise AdmissionError("native oracle query has exactly one index source")
            if sorts[occurrence.dependencies[0]] is not ValueSort.NAT:
                raise AdmissionError("native oracle query index source must have Nat sort")
            queries[occurrence.name] = (occurrence.oracle_name, index)
        elif occurrence.kind is OccurrenceKind.ORACLE_ANSWER:
            assert occurrence.oracle_name is not None
            if len(occurrence.dependencies) != 1:
                raise AdmissionError("native oracle answer names exactly one query")
            ref = occurrence.dependencies[0]
            if ref.kind is not RefKind.OCCURRENCE or ref.name not in queries:
                raise AdmissionError("native oracle answer must reference a prior query")
            query_oracle, _ = queries[ref.name]
            if query_oracle != occurrence.oracle_name or ref.name in answered_queries:
                raise AdmissionError("native oracle answer mismatches or repeats its query")
            answered_queries.add(ref.name)

        occurrence_ref = ValueRef.occurrence(occurrence.name)
        available.add(occurrence_ref)
        sorts[occurrence_ref] = _occurrence_sort(occurrence, sorts)

    if set(queries) != answered_queries:
        raise AdmissionError("every native oracle query needs exactly one answer")
    extension_names = tuple(core.extensions)
    _bounded_unique(extension_names, 16, "extensions")
    unknown = set(extension_names) - KNOWN_EXTENSIONS
    if unknown:
        raise AdmissionError(f"unsupported extension: {sorted(unknown)!r}")
    if oracle_seen != ("native-oracle-v0" in core.extensions):
        raise AdmissionError("native oracle events and extension declaration must agree")

    claim_names = tuple(core.initial_claims)
    _bounded_unique(claim_names, MAX_CLAIMS, "initial claims")
    live = set(claim_names)
    produced = set(claim_names)
    reduction_names = tuple(step.name for step in core.reductions)
    _bounded_unique(reduction_names, MAX_CLAIMS, "reduction names")
    if any(type(use) is not ClaimConsumerUse for use in core.claim_uses):
        raise AdmissionError("claim consumer uses have the wrong exact shape")
    uses_by_consumer: dict[str, list[str]] = {}
    for use in core.claim_uses:
        _symbol(use.claim, "consumed claim")
        _symbol(use.consumer, "claim consumer")
        uses_by_consumer.setdefault(use.consumer, []).append(use.claim)
    if len(core.claim_uses) != len({use.claim for use in core.claim_uses}):
        raise AdmissionError("claim use must be linear")
    if any(len(set(items)) != len(items) for items in uses_by_consumer.values()):
        raise AdmissionError("claim use must be linear")

    def ref_available_before(ref: ValueRef, step_index: int) -> bool:
        if ref.kind is RefKind.OCCURRENCE:
            return ref.name in occurrence_index and occurrence_index[ref.name] < step_index
        item = input_by_name.get(ref.name)
        if item is None:
            return False
        declared_scope = core.scopes[scope_index[item.scope]]
        opening = -1 if declared_scope.open_before is None else occurrence_index[declared_scope.open_before]
        return opening <= step_index

    previous_step_index = -1
    oracle_publication_by_name = {
        item.oracle_name: item.name
        for item in core.schedule
        if item.kind is OccurrenceKind.ORACLE_PUBLISH
    }

    def publication_dependencies(ref: ValueRef) -> set[str]:
        """Derive prover publications in one finite value-dependency closure."""

        pending = [ref]
        seen: set[ValueRef] = set()
        result: set[str] = set()
        while pending:
            current = pending.pop()
            if current in seen or current.kind is not RefKind.OCCURRENCE:
                continue
            seen.add(current)
            if current.name not in occurrence_index:
                continue
            source = core.schedule[occurrence_index[current.name]]
            if source.kind in {
                OccurrenceKind.PROVER_MESSAGE,
                OccurrenceKind.ORACLE_PUBLISH,
            }:
                result.add(source.name)
            if source.kind in {
                OccurrenceKind.ORACLE_QUERY,
                OccurrenceKind.ORACLE_ANSWER,
            }:
                publication = oracle_publication_by_name.get(source.oracle_name)
                if publication is not None:
                    result.add(publication)
            pending.extend(source.dependencies)
        return result

    for step in core.reductions:
        if type(step) is not ReductionDecl or step.at_occurrence not in occurrence_index:
            raise AdmissionError("reduction declaration names an unknown occurrence")
        step_index = occurrence_index[step.at_occurrence]
        if step_index < previous_step_index:
            raise AdmissionError("reduction declarations must follow schedule order")
        previous_step_index = step_index
        if step.scope not in scope_index or core.schedule[step_index].scope != step.scope:
            raise AdmissionError("reduction scope must equal its application scope")
        aggregates = (
            step.input_claims,
            step.side_inputs,
            step.required_challenges,
            step.required_publications,
            step.output_claims,
        )
        if any(type(items) is not tuple for items in aggregates):
            raise AdmissionError("reduction aggregates must be immutable tuples")
        if len(set(step.input_claims)) != len(step.input_claims) or len(set(step.output_claims)) != len(step.output_claims):
            raise AdmissionError("reduction claims cannot repeat")
        if tuple(uses_by_consumer.pop(step.name, ())) != step.input_claims:
            raise AdmissionError("reduction input claims need exact consumer uses")
        if any(name not in live for name in step.input_claims):
            raise AdmissionError("claim use must be linear and presently live")
        if any(name in produced for name in step.output_claims):
            raise AdmissionError("claim names are single-assignment")
        for ref in step.side_inputs:
            _validate_ref(ref)
            if not ref_available_before(ref, step_index):
                raise AdmissionError("reduction side input is not available at application")
        if len(set(step.required_challenges)) != len(step.required_challenges):
            raise AdmissionError("required challenges must be unique")
        for challenge in step.required_challenges:
            if challenge not in occurrence_index or core.schedule[occurrence_index[challenge]].kind is not OccurrenceKind.CHALLENGE:
                raise AdmissionError("reduction required challenge is not a challenge occurrence")
            if occurrence_index[challenge] >= step_index:
                raise AdmissionError("reduction required challenge must precede application")
        publication_names = tuple(
            required.publication for required in step.required_publications
        )
        if len(set(publication_names)) != len(publication_names):
            raise AdmissionError("required publication occurrences must be unique")
        if tuple(
            sorted(publication_names, key=occurrence_index.__getitem__)
        ) != publication_names:
            raise AdmissionError("required publications must follow occurrence order")
        for required in step.required_publications:
            if type(required) is not RequiredPublication:
                raise AdmissionError("required publication has the wrong exact shape")
            if required.publication not in occurrence_index:
                raise AdmissionError("required publication names an unknown occurrence")
            publication = core.schedule[occurrence_index[required.publication]]
            if publication.kind not in {OccurrenceKind.PROVER_MESSAGE, OccurrenceKind.ORACLE_PUBLISH}:
                raise AdmissionError("required publication must be prover-controlled")
            publication_index = occurrence_index[required.publication]
            if publication_index >= step_index:
                raise AdmissionError("required publication must precede reduction application")
            following = tuple(
                challenge
                for challenge in step.required_challenges
                if occurrence_index[challenge] > publication_index
            )
            expected_next = min(
                following,
                key=occurrence_index.__getitem__,
                default=None,
            )
            if required.next_challenge != expected_next:
                raise AdmissionError(
                    "required publication must name its least following challenge"
                )
        dependency_publications: set[str] = set()
        for ref in step.side_inputs:
            dependency_publications.update(publication_dependencies(ref))
        if not dependency_publications.issubset(set(publication_names)):
            raise AdmissionError(
                "reduction side-input publication closure is incomplete"
            )
        live.difference_update(step.input_claims)
        live.update(step.output_claims)
        produced.update(step.output_claims)

    terminal_name = core.schedule[-1].name
    terminal_uses = uses_by_consumer.pop(terminal_name, [])
    if uses_by_consumer:
        raise AdmissionError("claim use names an unknown consumer")
    if len(terminal_uses) != len(set(terminal_uses)) or set(terminal_uses) != live:
        raise AdmissionError("terminal closure must consume every live claim exactly once")


def is_public_coin_eligible(core: Core) -> bool:
    """Compute dependency-sensitive private influence to verifier consumers."""

    admit_core(core)
    tainted = {
        ValueRef.input(item.name)
        for item in core.inputs
        if item.role is InputRole.VERIFIER_PRIVATE
    }
    checks: list[ValueRef] = []
    reductions_at: dict[str, list[ReductionDecl]] = {}
    for reduction in core.reductions:
        reductions_at.setdefault(reduction.at_occurrence, []).append(reduction)
    for item in core.schedule:
        sources = set(item.dependencies) | set(item.guard.refs)
        if item.check_predicate is not None:
            sources.update(item.check_predicate.refs)
        if item.kind is OccurrenceKind.TERMINAL:
            sources.update(checks)
        consumer = item.kind in {
            OccurrenceKind.PROVER_MESSAGE,
            OccurrenceKind.VERIFIER_MESSAGE,
            OccurrenceKind.CHALLENGE,
            OccurrenceKind.ORACLE_PUBLISH,
            OccurrenceKind.ORACLE_QUERY,
            OccurrenceKind.ORACLE_ANSWER,
            OccurrenceKind.CHECK,
            OccurrenceKind.TERMINAL,
        }
        if consumer and sources & tainted:
            return False
        output = ValueRef.occurrence(item.name)
        if sources & tainted:
            tainted.add(output)
        if item.kind is OccurrenceKind.CHECK:
            checks.append(output)
        for reduction in reductions_at.get(item.name, ()):
            reduction_sources = set(reduction.side_inputs)
            reduction_sources.update(
                ValueRef.occurrence(name) for name in reduction.required_challenges
            )
            reduction_sources.update(
                ValueRef.occurrence(required.publication)
                for required in reduction.required_publications
            )
            reduction_sources.add(output)
            if reduction_sources & tainted:
                return False
    return True


def admit_invocation(core: Core, invocation: Invocation) -> Mapping[str, Value]:
    admit_core(core)
    if type(invocation) is not Invocation or not isinstance(invocation.values, Mapping) or not isinstance(invocation.public_coins, Mapping):
        raise InvocationError("invocation has the wrong finite mapping shape")
    expected = tuple(item.name for item in core.inputs)
    if set(invocation.values) != set(expected):
        raise InvocationError("invocation must provide exactly every declared input")
    copied: dict[str, Value] = {}
    declarations = {item.name: item for item in core.inputs}
    for name in expected:
        value = invocation.values[name]
        _datum(value)
        if type(value) is OracleObject:
            raise InvocationError("native oracles are published, not invocation inputs")
        if not _sort_accepts(value, declarations[name].value_sort):
            raise InvocationError("invocation value does not match its declared sort")
        copied[name] = value
    for name, coin in invocation.public_coins.items():
        if name not in {item.name for item in core.schedule if item.kind is OccurrenceKind.CHALLENGE}:
            raise InvocationError("public coin names an unknown challenge")
        if type(coin) is not int or coin < 0:
            raise InvocationError("fresh public coins are nonnegative exact integers")
    return MappingProxyType(copied)


# ---------------------------------------------------------------------------
# Exact transcript construction and derived influence
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class TranscriptConstruction:
    application_domain: bytes
    sample_bytes: int = 8
    max_attempts: int = 16
    state_bytes: int = 32
    version: str = "k2-sha256-duplex-fixture-v1"

    def admit(self) -> None:
        if type(self.application_domain) is not bytes or not self.application_domain:
            raise AdmissionError("transcript application domain must be nonempty bytes")
        if type(self.sample_bytes) is not int or not 1 <= self.sample_bytes <= 32:
            raise AdmissionError("sample width must be in 1..32 octets")
        if type(self.max_attempts) is not int or not 1 <= self.max_attempts <= 256:
            raise AdmissionError("sampling attempt bound must be in 1..256")
        if self.state_bytes != 32 or self.version != "k2-sha256-duplex-fixture-v1":
            raise AdmissionError("unsupported exact transcript transition suite")


@dataclass(frozen=True)
class ChallengeSample:
    value: int
    state: bytes
    attempts: int
    namespaces: tuple[bytes, ...]


INITIAL_TRANSCRIPT_STATE = hashlib.sha256(b"zkc/k2/initial-state/v1").digest()


def construction_body(core: Core, construction: TranscriptConstruction) -> bytes:
    admit_core(core)
    construction.admit()
    return k1.encode_datum(
        k1.DatumRecord(
            (
                (0, k1.Symbol("k2.transcript-construction.v1")),
                (1, k1.BytesValue(core_id(core).internal_reference())),
                (2, k1.BytesValue(INITIAL_TRANSCRIPT_STATE)),
                (3, k1.BytesValue(construction.application_domain)),
                (4, k1.Nat(construction.sample_bytes)),
                (5, k1.Nat(construction.max_attempts)),
                (6, k1.Nat(construction.state_bytes)),
                (7, k1.Symbol(construction.version)),
                (8, k1.Symbol("init=fixed-state-then-core-construction-domain-frames")),
                (9, k1.Symbol("absorb=SHA256(frame(absorb)||frame(state)||frame(atom)||frame(payload))")),
                (10, k1.Symbol("squeeze=SHA256(frame(squeeze)||frame(state)||frame(draw-namespace)||frame(requested-bytes))[:requested-bytes]")),
                (11, k1.Symbol("advance=SHA256(frame(advance)||frame(state)||frame(draw-namespace)||frame(requested-bytes)||frame(block))")),
                (12, k1.Symbol("decode=big-endian-rejection-into-[0,modulus)")),
            )
        )
    )


def construction_id(core: Core, construction: TranscriptConstruction) -> object:
    return k1.content_id(
        "pir.transcript-construction",
        construction_body(core, construction),
        semantic_regime=k1.SEMANTIC_REGIME_ID,
    )


def _frame_bytes(body: bytes) -> bytes:
    if type(body) is not bytes:
        raise ModelError("transcript framing accepts exact bytes")
    return len(body).to_bytes(8, "big") + body


def _initial_state() -> bytes:
    return INITIAL_TRANSCRIPT_STATE


def _atom(kind: str, *coordinates: str) -> InfluenceAtom:
    _symbol(kind, "influence kind")
    for coordinate in coordinates:
        _symbol(coordinate, "influence coordinate")
    return InfluenceAtom(kind, tuple(coordinates))


def _atom_bytes(atom: InfluenceAtom) -> bytes:
    if type(atom) is not InfluenceAtom or type(atom.coordinates) is not tuple:
        raise ModelError("influence atom has the wrong exact carrier")
    return k1.encode_datum(
        k1.DatumRecord(
            (
                (0, _symbol(atom.kind, "influence kind")),
                (
                    1,
                    k1.DatumSeq(
                        tuple(
                            _symbol(item, "influence coordinate")
                            for item in atom.coordinates
                        )
                    ),
                ),
            )
        )
    )


def _absorb(state: bytes, frame: Frame) -> bytes:
    if type(state) is not bytes or len(state) != 32:
        raise ModelError("transcript state must be 32 exact octets")
    return hashlib.sha256(
        _frame_bytes(b"k2/absorb/v1")
        + _frame_bytes(state)
        + _frame_bytes(_atom_bytes(frame.atom))
        + _frame_bytes(frame.payload)
    ).digest()


def derive_occurrence_namespace(
    core: Core,
    construction: TranscriptConstruction,
    ordinal: int,
    draw_ordinal: int = 0,
) -> bytes:
    """Derive a collision-free canonical occurrence namespace.

    The namespace is the exact framed tuple, not an author-supplied label and
    not merely a digest.  Its two typed references and schedule ordinal make
    equality equivalent to equality of the complete tuple.
    """

    admit_core(core)
    construction.admit()
    if type(ordinal) is not int or not 0 <= ordinal < len(core.schedule):
        raise AdmissionError("challenge ordinal is outside the exact schedule")
    if (
        type(draw_ordinal) is not int
        or not 0 <= draw_ordinal < construction.max_attempts
    ):
        raise AdmissionError("draw ordinal is outside the construction bound")
    occurrence = core.schedule[ordinal]
    if occurrence.kind is not OccurrenceKind.CHALLENGE:
        raise AdmissionError("only a challenge occurrence has a squeeze namespace")
    scope_index = {scope.name: index for index, scope in enumerate(core.scopes)}
    scope_by_name = {scope.name: scope for scope in core.scopes}
    path: list[int] = []
    current: str | None = occurrence.scope
    while current is not None:
        path.append(scope_index[current])
        current = scope_by_name[current].parent
    path.reverse()
    assert occurrence.challenge_domain is not None
    return k1.encode_datum(
        k1.DatumRecord(
            (
                (0, k1.BytesValue(core_id(core).internal_reference())),
                (
                    1,
                    k1.BytesValue(
                        construction_id(core, construction).internal_reference()
                    ),
                ),
                (2, k1.DatumSeq(tuple(k1.Nat(index) for index in path))),
                (3, k1.Nat(ordinal)),
                (4, k1.Nat(draw_ordinal)),
                (5, k1.Nat(occurrence.challenge_domain.modulus)),
            )
        )
    )


def _squeeze_block(state: bytes, namespace: bytes, requested_bytes: int) -> bytes:
    if type(requested_bytes) is not int or not 1 <= requested_bytes <= 32:
        raise AdmissionError("requested squeeze length is outside the fixture bound")
    return hashlib.sha256(
        _frame_bytes(b"k2/squeeze/v0")
        + _frame_bytes(state)
        + _frame_bytes(namespace)
        + _frame_bytes(requested_bytes.to_bytes(8, "big"))
    ).digest()[:requested_bytes]


def _advance_state(
    state: bytes,
    namespace: bytes,
    requested_bytes: int,
    block: bytes,
) -> bytes:
    return hashlib.sha256(
        _frame_bytes(b"k2/advance/v0")
        + _frame_bytes(state)
        + _frame_bytes(namespace)
        + _frame_bytes(requested_bytes.to_bytes(8, "big"))
        + _frame_bytes(block)
    ).digest()


def squeeze_and_sample(
    state: bytes,
    core: Core,
    occurrence_ordinal: int,
    domain: ChallengeDomain,
    construction: TranscriptConstruction,
) -> ChallengeSample:
    construction.admit()
    if type(state) is not bytes or len(state) != construction.state_bytes:
        raise AdmissionError("squeeze state has the wrong exact carrier")
    if (
        type(occurrence_ordinal) is not int
        or not 0 <= occurrence_ordinal < len(core.schedule)
        or core.schedule[occurrence_ordinal].kind is not OccurrenceKind.CHALLENGE
    ):
        raise AdmissionError("sampling must name one exact challenge occurrence")
    if domain != core.schedule[occurrence_ordinal].challenge_domain:
        raise AdmissionError("sampling domain must equal the Core challenge domain")
    if type(domain) is not ChallengeDomain or type(domain.modulus) is not int or domain.modulus <= 1:
        raise AdmissionError("invalid challenge sampling domain")
    width = construction.sample_bytes
    space = 1 << (8 * width)
    if domain.modulus > space:
        raise AdmissionError("challenge modulus exceeds the exact sample word")
    accept_below = space - (space % domain.modulus)
    current = state
    namespaces: list[bytes] = []
    for attempt in range(construction.max_attempts):
        namespace = derive_occurrence_namespace(
            core,
            construction,
            occurrence_ordinal,
            attempt,
        )
        namespaces.append(namespace)
        block = _squeeze_block(current, namespace, width)
        if len(block) != width:
            raise AdmissionError("squeeze output length differs from requested length")
        current = _advance_state(current, namespace, width, block)
        raw = int.from_bytes(block[:width], "big")
        if raw < accept_below:
            return ChallengeSample(
                raw % domain.modulus,
                current,
                attempt + 1,
                tuple(namespaces),
            )
    raise SamplingExhausted(tuple(namespaces), current, construction.max_attempts)


def _value_bytes(value: Value) -> bytes:
    return k1.encode_datum(_datum(value))


def _scope_openings(core: Core) -> Mapping[str | None, tuple[ScopeDecl, ...]]:
    result: dict[str | None, list[ScopeDecl]] = {}
    for scope in core.scopes:
        result.setdefault(scope.open_before, []).append(scope)
    return MappingProxyType({key: tuple(value) for key, value in result.items()})


def required_influence_kinds(occurrence: Occurrence) -> tuple[str, ...]:
    """Return derived value influence; callers cannot remove these classes."""

    if occurrence.kind in {
        OccurrenceKind.PROVER_MESSAGE,
        OccurrenceKind.ORACLE_PUBLISH,
        OccurrenceKind.ORACLE_QUERY,
        OccurrenceKind.ORACLE_ANSWER,
    }:
        return (occurrence.kind.value,)
    if occurrence.kind is OccurrenceKind.VERIFIER_MESSAGE:
        return (occurrence.kind.value,)
    return ()


def _occurrence_atom(occurrence: Occurrence) -> InfluenceAtom | None:
    kinds = required_influence_kinds(occurrence)
    return None if not kinds else _atom(kinds[0], occurrence.name)


def _draw_atom(entry: RunEntry, ordinal: int, namespace: bytes) -> InfluenceAtom:
    return _atom("challenge-draw", entry.occurrence, str(ordinal), namespace.hex())


def extract_influence_atoms(
    frames: tuple[Frame, ...],
    prior_entries: tuple[RunEntry, ...] = (),
    core: Core | None = None,
) -> tuple[InfluenceAtom, ...]:
    """Extract the finite observed influence trace from an exact run prefix."""

    frame_atoms: list[InfluenceAtom] = []
    for frame in frames:
        if type(frame) is not Frame or frame.tag != frame.atom.kind:
            raise ReplayError("transcript frame and influence atom disagree")
        _atom_bytes(frame.atom)
        frame_atoms.append(frame.atom)

    draw_atoms = tuple(
        (entry_index, _draw_atom(entry, ordinal, namespace))
        for entry_index, entry in enumerate(prior_entries)
        for ordinal, namespace in enumerate(entry.draw_namespaces)
    )
    if core is None or not draw_atoms:
        atoms = frame_atoms + [atom for _, atom in draw_atoms]
    else:
        occurrence_index = {
            occurrence.name: index for index, occurrence in enumerate(core.schedule)
        }
        scope_index = {
            scope.name: (
                -1
                if scope.open_before is None
                else occurrence_index[scope.open_before]
            )
            for scope in core.scopes
        }

        def frame_rank(atom: InfluenceAtom) -> int:
            if atom.kind in {
                "core-header",
                "construction-header",
                "application-domain",
            }:
                return -1
            if atom.kind in {
                "scope-open",
                InputRole.STATEMENT.value,
                InputRole.PUBLIC_CONTEXT.value,
                InputRole.PUBLIC_PARAMETER.value,
            }:
                return scope_index[atom.coordinates[0]]
            return occurrence_index[atom.coordinates[0]]

        atoms = []
        draw_index = 0
        for atom in frame_atoms:
            rank = frame_rank(atom)
            while (
                draw_index < len(draw_atoms)
                and draw_atoms[draw_index][0] < rank
            ):
                atoms.append(draw_atoms[draw_index][1])
                draw_index += 1
            atoms.append(atom)
        atoms.extend(atom for _, atom in draw_atoms[draw_index:])
    if len(atoms) != len(set(atoms)):
        raise ReplayError("duplicate transcript influence atom")
    return tuple(atoms)


def required_influence_atoms(
    core: Core,
    construction: TranscriptConstruction,
    challenge_ordinal: int,
    prior_entries: tuple[RunEntry, ...],
) -> tuple[InfluenceAtom, ...]:
    """Derive all finite obligations for one challenge from Core structure."""

    occurrence = core.schedule[challenge_ordinal]
    if occurrence.kind is not OccurrenceKind.CHALLENGE:
        raise AdmissionError("required influence is defined only for challenges")
    required: list[InfluenceAtom] = [
        _atom("core-header", core_id(core).internal_reference().hex()),
        _atom(
            "construction-header",
            construction_id(core, construction).internal_reference().hex(),
        ),
        _atom("application-domain", construction.application_domain.hex()),
    ]
    scopes_by_opening = _scope_openings(core)

    def append_scope_openings(open_before: str | None) -> None:
        for scope in scopes_by_opening.get(open_before, ()):
            required.append(_atom("scope-open", scope.name))
            required.extend(
                _atom(item.role.value, item.scope, item.name)
                for item in core.inputs
                if item.scope == scope.name
                and item.role
                in {
                    InputRole.STATEMENT,
                    InputRole.PUBLIC_CONTEXT,
                    InputRole.PUBLIC_PARAMETER,
                }
            )

    append_scope_openings(None)
    by_name = {item.name: item for item in core.schedule}
    for entry in prior_entries:
        prior = by_name[entry.occurrence]
        append_scope_openings(prior.name)
        if prior.guard.kind is not PredicateKind.ALWAYS:
            required.append(
                _atom(
                    "guard-outcome",
                    prior.name,
                    "executed" if entry.status is EntryStatus.EXECUTED else "skipped",
                )
            )
        if entry.status is EntryStatus.EXECUTED:
            atom = _occurrence_atom(prior)
            if atom is not None:
                required.append(atom)
            required.extend(
                _draw_atom(entry, ordinal, namespace)
                for ordinal, namespace in enumerate(entry.draw_namespaces)
            )
    append_scope_openings(occurrence.name)
    if occurrence.guard.kind is not PredicateKind.ALWAYS:
        required.append(_atom("guard-outcome", occurrence.name, "executed"))
    required.extend(
        _atom("challenge-condition", occurrence.name, ref.kind.value, ref.name)
        for ref in occurrence.dependencies
    )
    for reduction in core.reductions:
        for publication in reduction.required_publications:
            if publication.next_challenge == occurrence.name:
                atom = _occurrence_atom(by_name[publication.publication])
                assert atom is not None
                required.append(atom)
    return tuple(dict.fromkeys(required))


def compare_influence(
    required: tuple[InfluenceAtom, ...],
    observed: tuple[InfluenceAtom, ...],
) -> InfluenceComparison:
    if len(required) != len(set(required)):
        raise ReplayError("duplicate required transcript influence atom")
    if len(observed) != len(set(observed)):
        raise ReplayError("duplicate transcript influence atom")

    # Greedily match the required trace in its declared order.  Extra observed
    # atoms are allowed, but an atom seen only before its required predecessor
    # cannot be reused after that predecessor and is therefore reported
    # missing.  This is an ordered-subtrace check, not set containment.
    observed_index = 0
    missing: list[InfluenceAtom] = []
    for required_atom in required:
        while (
            observed_index < len(observed)
            and observed[observed_index] != required_atom
        ):
            observed_index += 1
        if observed_index == len(observed):
            missing.append(required_atom)
        else:
            observed_index += 1

    return InfluenceComparison(
        required,
        observed,
        tuple(missing),
    )


# ---------------------------------------------------------------------------
# Causal generation and noncausal replay
# ---------------------------------------------------------------------------


class ProverView:
    """The only protocol-owned strategy input: current, finite, prefix-only."""

    __slots__ = ("_ordinal", "_public", "_history", "_index")

    def __init__(
        self,
        ordinal: int,
        public_values: Mapping[str, Value],
        history: tuple[RunEntry, ...],
        occurrence_index: Mapping[str, int],
    ) -> None:
        self._ordinal = ordinal
        self._public = MappingProxyType(dict(public_values))
        self._history = history
        self._index = MappingProxyType(dict(occurrence_index))

    def public_input(self, name: str) -> Value:
        if name not in self._public:
            raise FutureReadError(f"input {name!r} is not public to the strategy")
        return self._public[name]

    def read_occurrence(self, name: str) -> Value:
        index = self._index.get(name)
        if index is None or index >= self._ordinal:
            raise FutureReadError(f"occurrence {name!r} is not in the current prefix")
        entry = self._history[index]
        if entry.status is EntryStatus.SKIPPED or entry.value is None:
            raise FutureReadError(f"occurrence {name!r} has no visible value")
        return entry.value

    @property
    def visible_prefix(self) -> tuple[RunEntry, ...]:
        return self._history


def _resolve(ref: ValueRef, values: Mapping[ValueRef, Value]) -> Value:
    try:
        return values[ref]
    except KeyError as error:
        raise ExecutionError(f"dependency {ref.kind.value}:{ref.name} has no value") from error


def _predicate(predicate: Predicate, values: Mapping[ValueRef, Value]) -> bool:
    resolved = tuple(_resolve(ref, values) for ref in predicate.refs)
    if predicate.kind is PredicateKind.ALWAYS:
        return True
    if predicate.kind is PredicateKind.NEVER:
        return False
    if predicate.kind is PredicateKind.BOOL:
        if type(resolved[0]) is not bool:
            raise ExecutionError("Bool fixture predicate received a nonboolean")
        return resolved[0]
    if predicate.kind is PredicateKind.BYTES_EQUAL:
        return type(resolved[0]) is bytes and type(resolved[1]) is bytes and resolved[0] == resolved[1]
    if predicate.kind is PredicateKind.SCHNORR:
        if any(type(value) is not int for value in resolved):
            raise ExecutionError("Schnorr fixture predicate expects six integers")
        g, statement, commitment, challenge, response, modulus = resolved
        (order,) = predicate.parameters
        if modulus <= 2 or order <= 1:
            raise ExecutionError("invalid Schnorr fixture parameters")
        return pow(g, response % order, modulus) == (
            commitment * pow(statement, challenge % order, modulus)
        ) % modulus
    if predicate.kind is PredicateKind.LEADING_ZERO_BITS:
        value = resolved[0]
        bits = predicate.parameters[0]
        if type(value) is not bytes or not 0 <= bits <= 256:
            raise ExecutionError("invalid grinding fixture input")
        digest = hashlib.sha256(value).digest()
        return int.from_bytes(digest, "big") < (1 << (256 - bits))
    raise ExecutionError("unsupported fixture predicate")


def _verifier_value(rule: VerifierRule, dependencies: tuple[Value, ...]) -> Value:
    if rule.kind is VerifierRuleKind.COPY:
        if len(dependencies) != 1:
            raise ExecutionError("copy rule needs one dependency")
        return dependencies[0]
    if rule.kind is VerifierRuleKind.SHA256:
        if any(type(item) is not bytes for item in dependencies):
            raise ExecutionError("SHA-256 verifier rule accepts byte strings")
        return hashlib.sha256(b"".join(dependencies)).digest()
    if rule.kind is VerifierRuleKind.CONSTANT_INT:
        if dependencies or len(rule.parameters) != 1:
            raise ExecutionError("constant-int rule has one parameter and no dependency")
        return rule.parameters[0]
    raise ExecutionError("unsupported verifier rule")


def _append_frame(
    state: bytes,
    frames: list[Frame],
    tag: str,
    payload: bytes,
    *coordinates: str,
) -> bytes:
    frame = Frame(tag, payload, _atom(tag, *coordinates))
    frames.append(frame)
    return _absorb(state, frame)


def _open_scopes(
    core: Core,
    scopes: tuple[ScopeDecl, ...],
    invocation_values: Mapping[str, Value],
    state: bytes,
    frames: list[Frame],
) -> bytes:
    for scope in scopes:
        state = _append_frame(
            state,
            frames,
            "scope-open",
            scope.name.encode("ascii"),
            scope.name,
        )
        for item in core.inputs:
            if item.scope == scope.name and item.role in {
                InputRole.STATEMENT,
                InputRole.PUBLIC_CONTEXT,
                InputRole.PUBLIC_PARAMETER,
            }:
                state = _append_frame(
                    state,
                    frames,
                    item.role.value,
                    k1.encode_datum(
                        k1.DatumRecord(
                            (
                                (0, _symbol(item.name, "public binding name")),
                                (1, _datum(invocation_values[item.name])),
                            )
                        )
                    ),
                    item.scope,
                    item.name,
                )
    return state


def _execute(
    core: Core,
    construction: TranscriptConstruction,
    interpretation: ChallengeInterpretation,
    invocation: Invocation,
    strategy: ProverStrategy | None,
    expected_record: RunRecord | None,
) -> GenerationResult:
    admit_core(core)
    is_fs = interpretation is ChallengeInterpretation.FIAT_SHAMIR
    if is_fs:
        construction.admit()
        if not is_public_coin_eligible(core):
            raise AdmissionError(
                "Fiat--Shamir requires a derived public-coin-eligible Core"
            )
    inputs = admit_invocation(core, invocation)
    expected_entries = None if expected_record is None else expected_record.entries
    if expected_entries is not None and len(expected_entries) != len(core.schedule):
        raise ReplayError("record does not have one entry per scheduled occurrence")
    if expected_record is not None:
        extract_influence_atoms(
            expected_record.transcript_frames,
            expected_record.entries,
            core,
        )

    cid = core_id(core)
    tid = construction_id(core, construction) if is_fs else None
    iid = invocation_id(core, invocation)
    if expected_record is not None:
        if (
            expected_record.core_id != cid
            or expected_record.construction_id != tid
            or expected_record.invocation_id != iid
            or expected_record.interpretation is not interpretation
        ):
            raise ReplayError("record identity axes do not match this run request")

    state: bytes | None = None
    frames: list[Frame] = []
    openings = _scope_openings(core)
    root_scopes = openings.get(None, ())
    public_values: dict[str, Value] = {
        item.name: inputs[item.name]
        for item in core.inputs
        if item.role is not InputRole.VERIFIER_PRIVATE
        and item.scope in {scope.name for scope in root_scopes}
    }
    if is_fs:
        assert tid is not None
        state = _initial_state()
        state = _append_frame(
            state,
            frames,
            "core-header",
            cid.internal_reference(),
            cid.internal_reference().hex(),
        )
        state = _append_frame(
            state,
            frames,
            "construction-header",
            tid.internal_reference(),
            tid.internal_reference().hex(),
        )
        state = _append_frame(
            state,
            frames,
            "application-domain",
            construction.application_domain,
            construction.application_domain.hex(),
        )
        state = _open_scopes(
            core,
            root_scopes,
            inputs,
            state,
            frames,
        )

    value_map: dict[ValueRef, Value] = {
        ValueRef.input(name): value for name, value in inputs.items()
    }
    entries: list[RunEntry] = []
    occurrence_index = {item.name: index for index, item in enumerate(core.schedule)}
    oracles: dict[str, OracleObject] = {}

    for ordinal, occurrence in enumerate(core.schedule):
        due_scopes = openings.get(occurrence.name, ())
        for opened_scope in due_scopes:
            for item in core.inputs:
                if (
                    item.scope == opened_scope.name
                    and item.role is not InputRole.VERIFIER_PRIVATE
                ):
                    public_values[item.name] = inputs[item.name]
        if is_fs:
            assert state is not None
            state = _open_scopes(
                core,
                due_scopes,
                inputs,
                state,
                frames,
            )
        executed = _predicate(occurrence.guard, value_map)
        if is_fs and occurrence.guard.kind is not PredicateKind.ALWAYS:
            assert state is not None
            state = _append_frame(
                state,
                frames,
                "guard-outcome",
                k1.encode_datum(
                    k1.DatumRecord(
                        (
                            (0, _symbol(occurrence.name, "occurrence name")),
                            (1, executed),
                        )
                    )
                ),
                occurrence.name,
                "executed" if executed else "skipped",
            )
        if not executed:
            entry = RunEntry(occurrence.name, occurrence.kind, EntryStatus.SKIPPED, None)
            entries.append(entry)
            continue

        dependencies = tuple(_resolve(ref, value_map) for ref in occurrence.dependencies)
        prefix: bytes | None = None
        draw_namespaces: tuple[bytes, ...] = ()
        attempts: int | None = None
        influence: InfluenceComparison | None = None

        if occurrence.kind in {OccurrenceKind.PROVER_MESSAGE, OccurrenceKind.ORACLE_PUBLISH}:
            if expected_entries is not None:
                value = expected_entries[ordinal].value
                if value is None:
                    raise ReplayError("executed prover occurrence has no recorded value")
            else:
                assert strategy is not None
                view = ProverView(ordinal, public_values, tuple(entries), occurrence_index)
                try:
                    value = strategy.move(occurrence, view)
                except FutureReadError as error:
                    return Noncompletion(NoncompletionReason.FUTURE_READ, occurrence.name, str(error))
                except StrategyStopped as error:
                    return Noncompletion(NoncompletionReason.STRATEGY_STOPPED, occurrence.name, str(error))
                try:
                    _datum(value)
                except ModelError as error:
                    return Noncompletion(NoncompletionReason.INVALID_MOVE, occurrence.name, str(error))
            expected_sort = (
                ValueSort.ORACLE
                if occurrence.kind is OccurrenceKind.ORACLE_PUBLISH
                else occurrence.prover_value_sort
            )
            if not _sort_accepts(value, expected_sort):
                if expected_entries is not None:
                    raise ReplayError("prover value does not match its declared sort")
                return Noncompletion(
                    NoncompletionReason.INVALID_MOVE,
                    occurrence.name,
                    "prover value does not match its declared sort",
                )
            if occurrence.kind is OccurrenceKind.ORACLE_PUBLISH:
                if type(value) is not OracleObject:
                    if expected_entries is not None:
                        raise ReplayError("oracle publication is not an immutable oracle object")
                    return Noncompletion(NoncompletionReason.INVALID_MOVE, occurrence.name, "oracle publication needs OracleObject")
                if type(value.cells) is not tuple or not 1 <= len(value.cells) <= MAX_ORACLE_CELLS or any(
                    type(cell) is not bytes or len(cell) > MAX_CELL_BYTES for cell in value.cells
                ):
                    if expected_entries is not None:
                        raise ReplayError("oracle object violates finite cell bounds")
                    return Noncompletion(NoncompletionReason.INVALID_MOVE, occurrence.name, "oracle object violates finite cell bounds")
                assert occurrence.oracle_name is not None
                oracles[occurrence.oracle_name] = value
        elif occurrence.kind is OccurrenceKind.VERIFIER_MESSAGE:
            assert occurrence.verifier_rule is not None
            value = _verifier_value(occurrence.verifier_rule, dependencies)
        elif occurrence.kind is OccurrenceKind.CHALLENGE:
            assert occurrence.challenge_domain is not None
            if interpretation is ChallengeInterpretation.FRESH:
                if occurrence.name not in invocation.public_coins:
                    raise InvocationError("fresh interpretation needs one public coin per challenge")
                value = invocation.public_coins[occurrence.name]
                if not 0 <= value < occurrence.challenge_domain.modulus:
                    raise InvocationError("fresh public coin is outside the challenge domain")
            else:
                assert state is not None
                for ref, dependency in zip(occurrence.dependencies, dependencies):
                    state = _append_frame(
                        state,
                        frames,
                        "challenge-condition",
                        k1.encode_datum(
                            k1.DatumRecord(
                                (
                                    (0, _ref_datum(ref)),
                                    (1, _datum(dependency)),
                                )
                            )
                        ),
                        occurrence.name,
                        ref.kind.value,
                        ref.name,
                    )
                observed = extract_influence_atoms(
                    tuple(frames),
                    tuple(entries),
                    core,
                )
                required = required_influence_atoms(
                    core,
                    construction,
                    ordinal,
                    tuple(entries),
                )
                influence = compare_influence(required, observed)
                if influence.missing:
                    raise ExecutionError(
                        "required transcript influence is missing before challenge"
                    )
                prefix = state
                sample = squeeze_and_sample(
                    state,
                    core,
                    ordinal,
                    occurrence.challenge_domain,
                    construction,
                )
                value = sample.value
                state = sample.state
                attempts = sample.attempts
                draw_namespaces = sample.namespaces
        elif occurrence.kind is OccurrenceKind.CHECK:
            assert occurrence.check_predicate is not None
            value = _predicate(occurrence.check_predicate, value_map)
        elif occurrence.kind is OccurrenceKind.TERMINAL:
            value = all(
                entry.value is True
                for entry in entries
                if entry.kind is OccurrenceKind.CHECK and entry.status is EntryStatus.EXECUTED
            )
        elif occurrence.kind is OccurrenceKind.ORACLE_QUERY:
            assert occurrence.oracle_name is not None
            oracle = oracles[occurrence.oracle_name]
            source = dependencies[0]
            if type(source) is not int:
                raise ExecutionError("native oracle query index source must be an integer")
            value = source % len(oracle.cells)
        elif occurrence.kind is OccurrenceKind.ORACLE_ANSWER:
            assert occurrence.oracle_name is not None
            oracle = oracles[occurrence.oracle_name]
            index = dependencies[0]
            if type(index) is not int or not 0 <= index < len(oracle.cells):
                raise ExecutionError("native oracle answer index is out of range")
            value = oracle.cells[index]
        else:  # pragma: no cover - exhaustive Enum guard
            raise ExecutionError("unknown occurrence kind")

        assert value is not None
        _datum(value)
        if is_fs:
            assert state is not None
            for influence_tag in required_influence_kinds(occurrence):
                state = _append_frame(
                    state,
                    frames,
                    influence_tag,
                    k1.encode_datum(
                        k1.DatumRecord(
                            (
                                (0, _symbol(occurrence.name, "occurrence name")),
                                (1, _datum(value)),
                            )
                        )
                    ),
                    occurrence.name,
                )
        entry = RunEntry(
            occurrence.name,
            occurrence.kind,
            EntryStatus.EXECUTED,
            value,
            prefix,
            draw_namespaces,
            attempts,
            influence,
        )
        entries.append(entry)
        value_map[ValueRef.occurrence(occurrence.name)] = value

    record = RunRecord(
        cid,
        tid,
        iid,
        interpretation,
        tuple(entries),
        tuple(frames),
        state,
    )
    if expected_record is not None and record != expected_record:
        raise ReplayError("record differs from the exact derived execution")
    return Completed(record)


def generate(
    core: Core,
    construction: TranscriptConstruction,
    interpretation: ChallengeInterpretation,
    invocation: Invocation,
    strategy: ProverStrategy,
) -> GenerationResult:
    if strategy is None:
        raise ModelError("generation requires a prover strategy")
    return _execute(core, construction, interpretation, invocation, strategy, None)


def replay(
    core: Core,
    construction: TranscriptConstruction,
    invocation: Invocation,
    record: RunRecord,
) -> RunRecord:
    result = _execute(
        core,
        construction,
        record.interpretation,
        invocation,
        None,
        record,
    )
    if type(result) is not Completed:  # pragma: no cover - replay has no strategy
        raise ReplayError("replay unexpectedly did not complete")
    return result.record


@dataclass(frozen=True)
class FreshFsPairEvidence:
    core_id: object
    fresh_terminal: bool
    fiat_shamir_terminal: bool
    occurrence_topology: tuple[tuple[str, OccurrenceKind, EntryStatus], ...]


def check_fresh_fs_pair(
    core: Core,
    construction: TranscriptConstruction,
    invocation: Invocation,
    fresh: RunRecord,
    fiat_shamir: RunRecord,
) -> FreshFsPairEvidence:
    """Check both runs and their exact same-Core structural relation."""

    expected_construction = construction_id(core, construction)
    if fresh.core_id != fiat_shamir.core_id:
        raise ReplayError("Fresh/FS relation requires the same literal Core")
    if fresh.construction_id is not None:
        raise ReplayError("Fresh run must not cite a transcript construction")
    if (
        fresh.transcript_frames
        or fresh.terminal_state is not None
        or any(
            entry.prefix_state is not None
            or entry.draw_namespaces
            or entry.sampling_attempts is not None
            or entry.influence is not None
            for entry in fresh.entries
        )
    ):
        raise ReplayError("Fresh run must not carry Fiat--Shamir transcript state")
    if fiat_shamir.construction_id != expected_construction:
        raise ReplayError("Fiat--Shamir run cites the wrong Core-scoped construction")
    if fresh.invocation_id != fiat_shamir.invocation_id:
        raise ReplayError("Fresh/FS relation requires the same invocation")
    if fresh.interpretation is not ChallengeInterpretation.FRESH or fiat_shamir.interpretation is not ChallengeInterpretation.FIAT_SHAMIR:
        raise ReplayError("Fresh/FS relation axes are reversed or missing")
    fresh_topology = tuple((item.occurrence, item.kind, item.status) for item in fresh.entries)
    fs_topology = tuple((item.occurrence, item.kind, item.status) for item in fiat_shamir.entries)
    if fresh_topology != fs_topology:
        raise ReplayError("Fresh/FS runs disagree on exact occurrence topology")
    namespaces = tuple(
        namespace
        for item in fiat_shamir.entries
        if item.kind is OccurrenceKind.CHALLENGE
        for namespace in item.draw_namespaces
    )
    if len(set(namespaces)) != len(namespaces):
        raise ReplayError("Fiat--Shamir challenge namespaces are not unique")
    replay(core, construction, invocation, fresh)
    replay(core, construction, invocation, fiat_shamir)
    fresh_terminal = fresh.entries[-1].value is True
    fs_terminal = fiat_shamir.entries[-1].value is True
    return FreshFsPairEvidence(fresh.core_id, fresh_terminal, fs_terminal, fresh_topology)


def mutate_record(record: RunRecord, *, entries: tuple[RunEntry, ...] | None = None, frames: tuple[Frame, ...] | None = None) -> RunRecord:
    """Small explicit mutation helper for negative fixtures."""

    return replace(
        record,
        entries=record.entries if entries is None else entries,
        transcript_frames=record.transcript_frames if frames is None else frames,
    )


# ---------------------------------------------------------------------------
# Reusable bounded fixtures
# ---------------------------------------------------------------------------


class ScriptedStrategy:
    def __init__(self, moves: Mapping[str, Value | Callable[[ProverView], Value]]) -> None:
        self._moves = dict(moves)

    def move(self, occurrence: Occurrence, view: ProverView) -> Value:
        if occurrence.name not in self._moves:
            raise StrategyStopped(f"no move for {occurrence.name}")
        value = self._moves[occurrence.name]
        return value(view) if callable(value) else value


def schnorr_fixture() -> tuple[Core, TranscriptConstruction, Invocation, ProverStrategy]:
    modulus = 23
    order = 11
    generator = 2
    secret = 3
    nonce = 4
    statement = pow(generator, secret, modulus)
    core = Core(
        inputs=(
            InputDecl("g", InputRole.PUBLIC_PARAMETER, value_sort=ValueSort.NAT),
            InputDecl("q", InputRole.PUBLIC_PARAMETER, value_sort=ValueSort.NAT),
            InputDecl("p", InputRole.PUBLIC_PARAMETER, value_sort=ValueSort.NAT),
            InputDecl("statement", InputRole.STATEMENT, value_sort=ValueSort.NAT),
            InputDecl("session", InputRole.PUBLIC_CONTEXT),
        ),
        scopes=(ScopeDecl("root", None, None),),
        schedule=(
            Occurrence(
                "commitment",
                OccurrenceKind.PROVER_MESSAGE,
                prover_value_sort=ValueSort.NAT,
            ),
            Occurrence(
                "challenge",
                OccurrenceKind.CHALLENGE,
                dependencies=(ValueRef.input("statement"),),
                challenge_domain=ChallengeDomain(order),
            ),
            Occurrence(
                "response",
                OccurrenceKind.PROVER_MESSAGE,
                prover_value_sort=ValueSort.NAT,
            ),
            Occurrence(
                "verify",
                OccurrenceKind.CHECK,
                dependencies=(
                    ValueRef.input("g"),
                    ValueRef.input("statement"),
                    ValueRef.occurrence("commitment"),
                    ValueRef.occurrence("challenge"),
                    ValueRef.occurrence("response"),
                    ValueRef.input("p"),
                ),
                check_predicate=Predicate(
                    PredicateKind.SCHNORR,
                    (
                        ValueRef.input("g"),
                        ValueRef.input("statement"),
                        ValueRef.occurrence("commitment"),
                        ValueRef.occurrence("challenge"),
                        ValueRef.occurrence("response"),
                        ValueRef.input("p"),
                    ),
                    (order,),
                ),
            ),
            Occurrence("terminal", OccurrenceKind.TERMINAL),
        ),
        initial_claims=("knowledge",),
        reductions=(
            ReductionDecl(
                "schnorr-reduction",
                "verify",
                "root",
                ("knowledge",),
                (
                    ValueRef.input("g"),
                    ValueRef.input("statement"),
                    ValueRef.occurrence("commitment"),
                    ValueRef.occurrence("challenge"),
                    ValueRef.occurrence("response"),
                    ValueRef.input("p"),
                ),
                ("challenge",),
                (
                    RequiredPublication("commitment", "challenge"),
                    RequiredPublication("response", None),
                ),
                ("checked",),
            ),
        ),
        claim_uses=(
            ClaimConsumerUse("knowledge", "schnorr-reduction"),
            ClaimConsumerUse("checked", "terminal"),
        ),
    )
    def response(view: ProverView) -> Value:
        challenge = view.read_occurrence("challenge")
        assert type(challenge) is int
        return (nonce + challenge * secret) % order

    strategy = ScriptedStrategy(
        {
            "commitment": pow(generator, nonce, modulus),
            "response": response,
        }
    )
    construction = TranscriptConstruction(b"zkc/k2/schnorr/v0")
    invocation = Invocation(
        MappingProxyType(
            {
                "g": generator,
                "q": order,
                "p": modulus,
                "statement": statement,
                "session": b"fixture-session",
            }
        ),
        MappingProxyType({"challenge": 7}),
    )
    return core, construction, invocation, strategy


def oracle_fixture() -> tuple[Core, TranscriptConstruction, Invocation, ProverStrategy]:
    core = Core(
        inputs=(
            InputDecl("statement", InputRole.STATEMENT),
            InputDecl("session", InputRole.PUBLIC_CONTEXT),
        ),
        scopes=(ScopeDecl("root", None, None),),
        schedule=(
            Occurrence("oracle", OccurrenceKind.ORACLE_PUBLISH, oracle_name="f"),
            Occurrence("query_coin", OccurrenceKind.CHALLENGE, challenge_domain=ChallengeDomain(17)),
            Occurrence(
                "query",
                OccurrenceKind.ORACLE_QUERY,
                dependencies=(ValueRef.occurrence("query_coin"),),
                oracle_name="f",
            ),
            Occurrence(
                "answer",
                OccurrenceKind.ORACLE_ANSWER,
                dependencies=(ValueRef.occurrence("query"),),
                oracle_name="f",
            ),
            Occurrence("fold_coin", OccurrenceKind.CHALLENGE, challenge_domain=ChallengeDomain(19)),
            Occurrence(
                "answer_nonempty",
                OccurrenceKind.CHECK,
                dependencies=(ValueRef.occurrence("answer"), ValueRef.input("statement")),
                check_predicate=Predicate(
                    PredicateKind.BYTES_EQUAL,
                    (ValueRef.occurrence("answer"), ValueRef.input("statement")),
                ),
            ),
            Occurrence("terminal", OccurrenceKind.TERMINAL),
        ),
        extensions=("native-oracle-v0",),
        initial_claims=("oracle-claim",),
        reductions=(
            ReductionDecl(
                "oracle-reduction",
                "answer_nonempty",
                "root",
                ("oracle-claim",),
                (
                    ValueRef.occurrence("answer"),
                    ValueRef.input("statement"),
                ),
                ("query_coin", "fold_coin"),
                (RequiredPublication("oracle", "query_coin"),),
                ("queried",),
            ),
        ),
        claim_uses=(
            ClaimConsumerUse("oracle-claim", "oracle-reduction"),
            ClaimConsumerUse("queried", "terminal"),
        ),
    )
    cells = (b"statement", b"statement", b"statement")
    strategy = ScriptedStrategy({"oracle": OracleObject(cells)})
    invocation = Invocation(
        MappingProxyType({"statement": b"statement", "session": b"oracle-session"}),
        MappingProxyType({"query_coin": 2, "fold_coin": 3}),
    )
    return core, TranscriptConstruction(b"zkc/k2/oracle/v0"), invocation, strategy
