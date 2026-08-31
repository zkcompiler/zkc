"""Executable K1 foundation candidate used by the bounded evaluation fixtures.

This module is deliberately self-contained and uses only the Python standard
library.  It is a reference *candidate*, not current zkc authority.  Its scope
is narrow:

* a fixed, prior ``FoundationMetaProfileV0`` canonical datum encoding;
* typed content identifiers whose semantic axes are hashed, while their text
  rendering is only a carrier;
* domain-indexed, schema-checked canonical values;
* a small first-order term language with only structurally bounded iteration;
* an exact, versioned primitive registry; and
* an evaluator that keeps semantic completion separate from deterministic
  abstract charging and operational refusal.

The syntax has no recursive bindings, general calls, effects, host callbacks,
I/O, clocks, randomness, or implicit ambient dependencies.  Term admission is
structural; evaluator support remains an explicit and fail-closed question.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
import hashlib
import re
from types import MappingProxyType
from typing import Callable, Iterable, Mapping, Sequence, TypeAlias


# ---------------------------------------------------------------------------
# FoundationMetaProfileV0: fixed prior encoding and typed content identity
# ---------------------------------------------------------------------------


FOUNDATION_PROFILE = "zkc.foundation.meta.v0"
IDENTITY_PROFILE_KIND = "foundation.identity-profile"
HASH_SUITE_KIND = "foundation.hash-suite"
SEMANTIC_MODULE_KIND = "foundation.semantic-module"
SEMANTIC_LANGUAGE_PROFILE_KIND = "foundation.semantic-language-profile"
SEMANTIC_REGIME_KIND = "foundation.semantic-regime"
CANONICAL_VALUE_KIND = "foundation.canonical-value"
SEMANTIC_PRIMITIVE_KIND = "foundation.semantic-primitive"
PORTABLE_ALGORITHM_KIND = "foundation.portable-algorithm"
EVALUATION_CONTRACT_KIND = "foundation.evaluation-contract"
EXTERNAL_OPERATION_CONTRACT_KIND = "foundation.external-operation-contract"
PRIOR_META_SUBJECT_KINDS = frozenset(
    {
        IDENTITY_PROFILE_KIND,
        HASH_SUITE_KIND,
        SEMANTIC_REGIME_KIND,
    }
)
FOUNDATION_STANDALONE_SEMANTIC_SUBJECT_KINDS = frozenset(
    {
        SEMANTIC_LANGUAGE_PROFILE_KIND,
        SEMANTIC_MODULE_KIND,
        CANONICAL_VALUE_KIND,
        SEMANTIC_PRIMITIVE_KIND,
        PORTABLE_ALGORITHM_KIND,
        EVALUATION_CONTRACT_KIND,
        EXTERNAL_OPERATION_CONTRACT_KIND,
    }
)
PROFILED_FORBIDDEN_SUBJECT_KINDS = (
    PRIOR_META_SUBJECT_KINDS | FOUNDATION_STANDALONE_SEMANTIC_SUBJECT_KINDS
)
META_ID_PREFIX = b"zkc/prior-meta-id/v0\x00"
CONTENT_ID_PREFIX = b"zkc/content-id/v0\x00"

MAX_CANONICAL_BYTES = 1 << 20
MAX_CANONICAL_NODES = 1 << 14
MAX_CANONICAL_EDGES = 1 << 14
MAX_CANONICAL_DEPTH = 384
MAX_SCHEMA_DEPTH = 48
MAX_MODULE_BUNDLE_ENTRIES = 1 << 14
MAX_MODULE_NODES = 1 << 14
MAX_MODULE_EDGES = 1 << 14
MAX_PROFILE_BUNDLE_ENTRIES = 1 << 14
MAX_PROFILE_NODES = 1 << 14
MAX_PROFILE_EDGES = 1 << 14
MAX_EVALUATOR_REGISTRY_ENTRIES = 1 << 14
# Three prior-meta descriptors, one contract, one algorithm, every bounded
# request module, the evaluator's primitive-support module, and at most one
# distinct primitive ID per bounded term node.
MAX_AUTHENTICATION_LEDGER_ENTRIES = (
    3 + 1 + 1 + MAX_PROFILE_NODES + MAX_MODULE_NODES + 1 + (1 << 12)
)


class CanonicalError(ValueError):
    """A datum or value is outside FoundationMetaProfileV0."""


class HashBindingConflictError(CanonicalError):
    """One validation scope authenticated distinct preimages for one typed ID."""


class UnsupportedValueDomainError(CanonicalError):
    """A valid nominal value domain has no exact implementation here."""


class ValueAdmissionRefusedError(ValueError):
    """A canonical datum failed a supported value owner's admission predicate."""


class ReferenceAxisMismatchError(CanonicalError):
    """A strictly framed identifier reference names incompatible typed axes."""


def _u64(value: int) -> bytes:
    if not _is_u64_natural(value):
        raise CanonicalError("value is outside the unsigned 64-bit range")
    return value.to_bytes(8, "big")


def _is_u64_natural(value: object) -> bool:
    return type(value) is int and 0 <= value < 1 << 64


def _frame(body: bytes) -> bytes:
    if type(body) is not bytes:
        raise CanonicalError("framed bodies must be exact bytes")
    return _u64(len(body)) + body


def _axis(text: str) -> bytes:
    if type(text) is not str:
        raise CanonicalError("identity axes must be text")
    if not text or len(text) > MAX_CANONICAL_BYTES:
        raise CanonicalError(
            "identity axes must fit the constitutional axis-length bound"
        )
    try:
        body = text.encode("ascii")
    except UnicodeEncodeError as error:
        raise CanonicalError("identity axes must be ASCII") from error
    if not body or any(byte < 0x21 or byte > 0x7E for byte in body):
        raise CanonicalError("identity axes must use nonempty printable ASCII")
    return body


def _read_reference_frame(
    data: bytes,
    offset: int,
    what: str,
) -> tuple[bytes, int]:
    """Read one exact u64-framed component from an internal ID reference."""

    if type(data) is not bytes or type(offset) is not int:
        raise CanonicalError(f"{what} reference has the wrong carrier")
    if offset < 0 or len(data) - offset < 8:
        raise CanonicalError(f"{what} reference has truncated framing")
    length = int.from_bytes(data[offset : offset + 8], "big")
    if length > MAX_CANONICAL_BYTES:
        raise CanonicalError(f"{what} reference component exceeds the axis bound")
    start = offset + 8
    end = start + length
    if end > len(data):
        raise CanonicalError(f"{what} reference has a truncated component")
    return data[start:end], end


def _decode_reference_axis(body: bytes, what: str) -> str:
    """Decode one exact printable-ASCII identity axis."""

    try:
        text = body.decode("ascii")
    except UnicodeDecodeError as error:
        raise CanonicalError(f"{what} reference axis is not ASCII") from error
    if _axis(text) != body:
        raise CanonicalError(f"{what} reference axis is not canonical")
    return text


def decode_prior_meta_reference(data: bytes) -> "PriorMetaId":
    """Strictly decode one PriorRefV0 internal reference."""

    foundation_body, offset = _read_reference_frame(data, 0, "prior-meta")
    kind_body, offset = _read_reference_frame(data, offset, "prior-meta")
    if len(data) - offset != 32:
        raise CanonicalError("prior-meta reference has a nonexact digest suffix")
    foundation = _decode_reference_axis(foundation_body, "prior-meta")
    subject_kind = _decode_reference_axis(kind_body, "prior-meta")
    if foundation != FOUNDATION_PROFILE:
        raise ReferenceAxisMismatchError(
            "prior-meta reference names another foundation profile"
        )
    if subject_kind not in PRIOR_META_SUBJECT_KINDS:
        raise ReferenceAxisMismatchError(
            "prior-meta reference has the wrong subject kind"
        )
    return PriorMetaId(foundation, subject_kind, data[offset:])


def decode_content_reference(data: bytes) -> "TypedContentId":
    """Strictly decode one ContentRefV0 internal reference."""

    foundation_body, offset = _read_reference_frame(data, 0, "content")
    identity_body, offset = _read_reference_frame(data, offset, "content")
    hash_body, offset = _read_reference_frame(data, offset, "content")
    kind_body, offset = _read_reference_frame(data, offset, "content")
    regime_body, offset = _read_reference_frame(data, offset, "content")
    if len(data) - offset != 32:
        raise CanonicalError("content reference has a nonexact digest suffix")
    foundation = _decode_reference_axis(foundation_body, "content")
    subject_kind = _decode_reference_axis(kind_body, "content")
    identity_profile = decode_prior_meta_reference(identity_body)
    hash_suite = decode_prior_meta_reference(hash_body)
    semantic_regime = decode_prior_meta_reference(regime_body)
    if foundation != FOUNDATION_PROFILE:
        raise ReferenceAxisMismatchError(
            "content reference names another foundation profile"
        )
    if subject_kind in PRIOR_META_SUBJECT_KINDS:
        raise ReferenceAxisMismatchError(
            "content reference has a prior-meta subject kind"
        )
    if identity_profile.subject_kind != IDENTITY_PROFILE_KIND:
        raise ReferenceAxisMismatchError(
            "content reference has the wrong identity-profile axis kind"
        )
    if identity_profile != IDENTITY_PROFILE_ID:
        raise ReferenceAxisMismatchError(
            "content reference names another identity profile"
        )
    if hash_suite.subject_kind != HASH_SUITE_KIND:
        raise ReferenceAxisMismatchError(
            "content reference has the wrong hash-suite axis kind"
        )
    if hash_suite != HASH_SUITE_ID:
        raise ReferenceAxisMismatchError("content reference names another hash suite")
    if semantic_regime.subject_kind != SEMANTIC_REGIME_KIND:
        raise ReferenceAxisMismatchError(
            "content reference has the wrong semantic-regime axis kind"
        )
    return TypedContentId(
        foundation,
        identity_profile,
        hash_suite,
        subject_kind,
        semantic_regime,
        data[offset:],
    )


@dataclass(frozen=True)
class Unit:
    """The unique unit datum."""


UNIT = Unit()


@dataclass(frozen=True)
class Nat:
    value: int


@dataclass(frozen=True)
class IntValue:
    value: int


@dataclass(frozen=True)
class BytesValue:
    value: bytes


@dataclass(frozen=True)
class Symbol:
    value: str


@dataclass(frozen=True)
class DatumSeq:
    values: tuple["Datum", ...]


@dataclass(frozen=True)
class DatumRecord:
    fields: tuple[tuple[int, "Datum"], ...]


@dataclass(frozen=True)
class DatumVariant:
    case: int
    payload: "Datum"


Datum: TypeAlias = (
    Unit
    | bool
    | Nat
    | IntValue
    | BytesValue
    | Symbol
    | DatumSeq
    | DatumRecord
    | DatumVariant
)


_SYMBOL_RE = re.compile(r"^[!-~]+$")


def _magnitude_size(value: int) -> int:
    if type(value) is not int or value < 0:
        raise CanonicalError("magnitude must be nonnegative")
    size = max(1, (value.bit_length() + 7) // 8)
    if size > MAX_CANONICAL_BYTES - 10:
        raise CanonicalError("integer magnitude exceeds canonical byte bound")
    return size


def _minimal_magnitude(value: int) -> bytes:
    size = _magnitude_size(value)
    return value.to_bytes(size, "big")


def _encoded_size(value: Datum) -> int:
    """Preflight exact encoded size without materializing child encodings."""

    nodes = 0
    edges = 0
    active: set[int] = set()

    def add(total: int, increment: int) -> int:
        result = total + increment
        if result > MAX_CANONICAL_BYTES:
            raise CanonicalError("canonical datum exceeds cumulative byte bound")
        return result

    def size(current: Datum, depth: int) -> int:
        nonlocal edges, nodes
        nodes += 1
        if nodes > MAX_CANONICAL_NODES:
            raise CanonicalError("canonical datum exceeds cumulative node bound")
        if depth > MAX_CANONICAL_DEPTH:
            raise CanonicalError("canonical datum exceeds depth bound")
        if type(current) is Unit or type(current) is bool:
            return 1
        if type(current) is Nat:
            if type(current.value) is not int or current.value < 0:
                raise CanonicalError("Nat cannot be negative")
            return 1 + 8 + _magnitude_size(current.value)
        if type(current) is IntValue:
            if type(current.value) is not int:
                raise CanonicalError("Int must contain an exact integer")
            return 1 + 1 + 8 + _magnitude_size(abs(current.value))
        if type(current) is BytesValue:
            if type(current.value) is not bytes:
                raise CanonicalError("Bytes must contain exact octets")
            return add(1 + 8, len(current.value))
        if type(current) is Symbol:
            if type(current.value) is not str:
                raise CanonicalError("Symbol must be text")
            if not current.value or len(current.value) > MAX_CANONICAL_BYTES - 9:
                raise CanonicalError("Symbol exceeds the canonical byte bound")
            try:
                body = current.value.encode("ascii")
            except UnicodeEncodeError as error:
                raise CanonicalError("Symbol must be ASCII") from error
            if not _SYMBOL_RE.fullmatch(current.value):
                raise CanonicalError(
                    "Symbol must be nonempty bytes in the range 0x21..0x7e"
                )
            return add(1 + 8, len(body))
        if type(current) is DatumSeq:
            if type(current.values) is not tuple:
                raise CanonicalError("Sequence children must use an immutable tuple")
            if len(current.values) > MAX_CANONICAL_NODES - nodes:
                raise CanonicalError("canonical datum exceeds cumulative node bound")
            marker = id(current)
            if marker in active:
                raise CanonicalError("canonical datum must be finite and acyclic")
            active.add(marker)
            edges += len(current.values)
            if edges > MAX_CANONICAL_EDGES:
                active.remove(marker)
                raise CanonicalError(
                    "canonical datum exceeds cumulative child-edge bound"
                )
            try:
                total = 1 + 8
                for child in current.values:
                    total = add(total, 8)
                    total = add(total, size(child, depth + 1))
                return total
            finally:
                active.remove(marker)
        if type(current) is DatumRecord:
            if type(current.fields) is not tuple:
                raise CanonicalError("Record fields must use an immutable tuple")
            if len(current.fields) > MAX_CANONICAL_NODES - nodes:
                raise CanonicalError("canonical datum exceeds cumulative node bound")
            marker = id(current)
            if marker in active:
                raise CanonicalError("canonical datum must be finite and acyclic")
            active.add(marker)
            edges += len(current.fields)
            if edges > MAX_CANONICAL_EDGES:
                active.remove(marker)
                raise CanonicalError(
                    "canonical datum exceeds cumulative child-edge bound"
                )
            try:
                total = 1 + 8
                previous = -1
                for field in current.fields:
                    if type(field) is not tuple or len(field) != 2:
                        raise CanonicalError(
                            "Record fields must use immutable ordinal-value pairs"
                        )
                    ordinal, child = field
                    if type(ordinal) is not int or not 0 <= ordinal < 1 << 64:
                        raise CanonicalError(
                            "Record field ordinal is outside the unsigned 64-bit range"
                        )
                    if ordinal <= previous:
                        raise CanonicalError(
                            "Record field ordinals must be strictly increasing"
                        )
                    previous = ordinal
                    total = add(total, 16)
                    total = add(total, size(child, depth + 1))
                return total
            finally:
                active.remove(marker)
        if type(current) is DatumVariant:
            if type(current.case) is not int or not 0 <= current.case < 1 << 64:
                raise CanonicalError(
                    "Variant case is outside the unsigned 64-bit range"
                )
            marker = id(current)
            if marker in active:
                raise CanonicalError("canonical datum must be finite and acyclic")
            active.add(marker)
            edges += 1
            if edges > MAX_CANONICAL_EDGES:
                active.remove(marker)
                raise CanonicalError(
                    "canonical datum exceeds cumulative child-edge bound"
                )
            try:
                return add(1 + 8 + 8, size(current.payload, depth + 1))
            finally:
                active.remove(marker)
        raise CanonicalError(f"unsupported canonical datum: {type(current)!r}")

    return size(value, 0)


def encode_datum(value: Datum) -> bytes:
    """Return the unique FoundationMetaProfileV0 encoding of ``value``."""

    expected_size = _encoded_size(value)
    nodes = 0

    def encode(current: Datum, depth: int) -> bytes:
        nonlocal nodes
        nodes += 1
        if nodes > MAX_CANONICAL_NODES:
            raise CanonicalError("canonical datum exceeds node bound")
        if depth > MAX_CANONICAL_DEPTH:
            raise CanonicalError("canonical datum exceeds depth bound")

        if type(current) is Unit:
            result = b"\x00"
        elif current is False:
            result = b"\x01"
        elif current is True:
            result = b"\x02"
        elif type(current) is Nat:
            if type(current.value) is not int or current.value < 0:
                raise CanonicalError("Nat cannot be negative")
            magnitude = _minimal_magnitude(current.value)
            result = b"\x03" + _frame(magnitude)
        elif type(current) is IntValue:
            if type(current.value) is not int:
                raise CanonicalError("Int must contain an exact integer")
            sign = 1 if current.value < 0 else 0
            magnitude = _minimal_magnitude(abs(current.value))
            result = b"\x04" + bytes((sign,)) + _frame(magnitude)
        elif type(current) is BytesValue:
            if type(current.value) is not bytes:
                raise CanonicalError("Bytes must contain exact octets")
            result = b"\x05" + _frame(current.value)
        elif type(current) is Symbol:
            if type(current.value) is not str:
                raise CanonicalError("Symbol must be text")
            try:
                body = current.value.encode("ascii")
            except UnicodeEncodeError as error:
                raise CanonicalError("Symbol must be ASCII") from error
            if not _SYMBOL_RE.fullmatch(current.value):
                raise CanonicalError(
                    "Symbol must be nonempty bytes in the range 0x21..0x7e"
                )
            result = b"\x06" + _frame(body)
        elif type(current) is DatumSeq:
            children = [encode(child, depth + 1) for child in current.values]
            result = (
                b"\x07"
                + _u64(len(children))
                + b"".join(_frame(child) for child in children)
            )
        elif type(current) is DatumRecord:
            previous = -1
            children: list[bytes] = []
            for ordinal, child in current.fields:
                if ordinal <= previous:
                    raise CanonicalError(
                        "Record field ordinals must be strictly increasing"
                    )
                previous = ordinal
                children.append(_u64(ordinal) + _frame(encode(child, depth + 1)))
            result = b"\x08" + _u64(len(children)) + b"".join(children)
        elif type(current) is DatumVariant:
            child = encode(current.payload, depth + 1)
            result = b"\x09" + _u64(current.case) + _frame(child)
        else:
            raise CanonicalError(f"unsupported canonical datum: {type(current)!r}")

        if len(result) > MAX_CANONICAL_BYTES:
            raise CanonicalError("canonical datum exceeds byte bound")
        return result

    result = encode(value, 0)
    if len(result) != expected_size:
        raise AssertionError("canonical preflight disagrees with encoder")
    return result


@dataclass
class _DecodeBudget:
    nodes: int = 0
    edges: int = 0


class _DatumReader:
    def __init__(self, data: bytes, budget: _DecodeBudget | None = None) -> None:
        if type(data) is not bytes:
            raise CanonicalError("canonical datum input must be exact bytes")
        if len(data) > MAX_CANONICAL_BYTES:
            raise CanonicalError("canonical datum exceeds byte bound")
        self.data = data
        self.offset = 0
        self.budget = budget if budget is not None else _DecodeBudget()

    def take(self, size: int) -> bytes:
        end = self.offset + size
        if size < 0 or end > len(self.data):
            raise CanonicalError("truncated canonical datum")
        result = self.data[self.offset : end]
        self.offset = end
        return result

    def u64(self) -> int:
        return int.from_bytes(self.take(8), "big")

    def framed_reader(self, child_depth: int) -> "_DatumReader":
        if child_depth > MAX_CANONICAL_DEPTH:
            raise CanonicalError("canonical datum exceeds depth bound")
        if self.budget.nodes >= MAX_CANONICAL_NODES:
            raise CanonicalError("canonical datum exceeds cumulative node bound")
        body = self.take(self.u64())
        return _DatumReader(body, self.budget)

    def datum(self, depth: int = 0) -> Datum:
        self.budget.nodes += 1
        if self.budget.nodes > MAX_CANONICAL_NODES:
            raise CanonicalError("canonical datum exceeds cumulative node bound")
        if depth > MAX_CANONICAL_DEPTH:
            raise CanonicalError("canonical datum exceeds depth bound")

        tag = self.take(1)
        if tag == b"\x00":
            return UNIT
        if tag == b"\x01":
            return False
        if tag == b"\x02":
            return True
        if tag in (b"\x03", b"\x04"):
            sign = 0
            if tag == b"\x04":
                sign = self.take(1)[0]
                if sign not in (0, 1):
                    raise CanonicalError("Int sign must be zero or one")
            magnitude = self.take(self.u64())
            if not magnitude or (len(magnitude) > 1 and magnitude[0] == 0):
                raise CanonicalError("integer magnitude is not minimal")
            number = int.from_bytes(magnitude, "big")
            if sign == 1 and number == 0:
                raise CanonicalError("negative zero is not canonical")
            return (
                Nat(number) if tag == b"\x03" else IntValue(-number if sign else number)
            )
        if tag in (b"\x05", b"\x06"):
            body = self.take(self.u64())
            if tag == b"\x05":
                return BytesValue(body)
            try:
                text = body.decode("ascii")
            except UnicodeDecodeError as error:
                raise CanonicalError("Symbol must be ASCII") from error
            if not _SYMBOL_RE.fullmatch(text):
                raise CanonicalError(
                    "Symbol must be nonempty bytes in the range 0x21..0x7e"
                )
            return Symbol(text)
        if tag == b"\x07":
            count = self.u64()
            self.budget.edges += count
            if self.budget.edges > MAX_CANONICAL_EDGES:
                raise CanonicalError(
                    "canonical datum exceeds cumulative child-edge bound"
                )
            if count > MAX_CANONICAL_NODES - self.budget.nodes:
                raise CanonicalError("canonical datum exceeds cumulative node bound")
            values: list[Datum] = []
            for _ in range(count):
                child = self.framed_reader(depth + 1)
                values.append(child.complete_datum(depth + 1))
            return DatumSeq(tuple(values))
        if tag == b"\x08":
            count = self.u64()
            self.budget.edges += count
            if self.budget.edges > MAX_CANONICAL_EDGES:
                raise CanonicalError(
                    "canonical datum exceeds cumulative child-edge bound"
                )
            if count > MAX_CANONICAL_NODES - self.budget.nodes:
                raise CanonicalError("canonical datum exceeds cumulative node bound")
            previous = -1
            fields: list[tuple[int, Datum]] = []
            for _ in range(count):
                ordinal = self.u64()
                if ordinal <= previous:
                    raise CanonicalError(
                        "Record field ordinals must be strictly increasing"
                    )
                previous = ordinal
                child = self.framed_reader(depth + 1)
                fields.append((ordinal, child.complete_datum(depth + 1)))
            return DatumRecord(tuple(fields))
        if tag == b"\x09":
            case = self.u64()
            self.budget.edges += 1
            if self.budget.edges > MAX_CANONICAL_EDGES:
                raise CanonicalError(
                    "canonical datum exceeds cumulative child-edge bound"
                )
            if self.budget.nodes >= MAX_CANONICAL_NODES:
                raise CanonicalError("canonical datum exceeds cumulative node bound")
            child = self.framed_reader(depth + 1)
            return DatumVariant(case, child.complete_datum(depth + 1))
        raise CanonicalError(f"unknown canonical datum tag 0x{tag.hex()}")

    def complete_datum(self, depth: int = 0) -> Datum:
        result = self.datum(depth)
        if self.offset != len(self.data):
            raise CanonicalError("trailing bytes in canonical datum")
        return result


def decode_datum(data: bytes) -> Datum:
    """Strictly decode one datum, rejecting every noncanonical spelling."""

    value = _DatumReader(data).complete_datum()
    if encode_datum(value) != data:
        raise CanonicalError("decoded datum does not re-encode identically")
    return value


@dataclass(frozen=True)
class PriorMetaId:
    """Identifier constructed only by the constitutional prior profile."""

    foundation_profile: str
    subject_kind: str
    digest: bytes

    def __post_init__(self) -> None:
        _axis(self.foundation_profile)
        _axis(self.subject_kind)
        if self.foundation_profile != FOUNDATION_PROFILE:
            raise CanonicalError("unsupported foundation profile")
        if self.subject_kind not in PRIOR_META_SUBJECT_KINDS:
            raise CanonicalError("subject kind is not a prior-meta kind")
        if type(self.digest) is not bytes or len(self.digest) != 32:
            raise CanonicalError("this prior profile requires one SHA-256 digest")

    def internal_reference(self) -> bytes:
        self.__post_init__()
        return (
            _frame(_axis(self.foundation_profile))
            + _frame(_axis(self.subject_kind))
            + self.digest
        )

    def carrier(self) -> str:
        return f"zkcmetaidv0:{self.subject_kind}:{self.digest.hex()}"


def meta_object_id(
    subject_kind: str,
    body: bytes,
    *,
    foundation_profile: str = FOUNDATION_PROFILE,
) -> PriorMetaId:
    """Identify one prior meta object without invoking ordinary identity."""

    _axis(foundation_profile)
    _axis(subject_kind)
    if foundation_profile != FOUNDATION_PROFILE:
        raise CanonicalError("unsupported foundation profile")
    if subject_kind not in PRIOR_META_SUBJECT_KINDS:
        raise CanonicalError("subject kind is not a prior-meta kind")
    if type(body) is not bytes:
        raise CanonicalError("prior-meta descriptor body must be bytes")
    decode_datum(body)
    preimage = (
        META_ID_PREFIX
        + _frame(_axis(foundation_profile))
        + _frame(_axis(subject_kind))
        + _frame(body)
    )
    return PriorMetaId(
        foundation_profile,
        subject_kind,
        hashlib.sha256(preimage).digest(),
    )


IDENTITY_PROFILE_DESCRIPTOR = DatumRecord(
    (
        (0, Symbol("zkc.identity.framed.v0")),
        (1, BytesValue(CONTENT_ID_PREFIX)),
        (2, Symbol("u64-be-octet-length")),
        (
            3,
            DatumSeq(
                tuple(
                    Symbol(axis)
                    for axis in (
                        "foundation-profile",
                        "identity-profile-id",
                        "hash-suite-id",
                        "subject-kind",
                        "semantic-regime-id",
                        "canonical-body",
                    )
                )
            ),
        ),
        (4, Symbol("digest-excluded")),
    )
)
IDENTITY_PROFILE_ID = meta_object_id(
    IDENTITY_PROFILE_KIND,
    encode_datum(IDENTITY_PROFILE_DESCRIPTOR),
)
HASH_SUITE_DESCRIPTOR = DatumRecord(
    (
        (0, Symbol("sha2-256")),
        (1, Nat(1)),
        (2, Symbol("fips-180-4-octets")),
        (3, Nat(32)),
    )
)
HASH_SUITE_ID = meta_object_id(
    HASH_SUITE_KIND,
    encode_datum(HASH_SUITE_DESCRIPTOR),
)


def _require_prior_meta_axis(
    value: object,
    *,
    expected_kind: str,
    axis_name: str,
) -> PriorMetaId:
    """Validate one typed prior-meta axis without leaking host exceptions."""

    if type(value) is not PriorMetaId:
        raise CanonicalError(f"{axis_name} axis must be a PriorMetaId")
    value.__post_init__()
    if value.subject_kind != expected_kind:
        raise CanonicalError(f"{axis_name} axis has the wrong kind")
    return value


@dataclass(frozen=True)
class TypedContentId:
    """A regime-qualified semantic-content identifier."""

    foundation_profile: str
    identity_profile: PriorMetaId
    hash_suite: PriorMetaId
    subject_kind: str
    semantic_regime: PriorMetaId
    digest: bytes

    def __post_init__(self) -> None:
        _axis(self.foundation_profile)
        _axis(self.subject_kind)
        if self.foundation_profile != FOUNDATION_PROFILE:
            raise CanonicalError("unsupported foundation profile")
        if self.subject_kind in PRIOR_META_SUBJECT_KINDS:
            raise CanonicalError(
                "prior-meta subjects cannot use the semantic-content constructor"
            )
        _require_prior_meta_axis(
            self.identity_profile,
            expected_kind=IDENTITY_PROFILE_KIND,
            axis_name="identity-profile",
        )
        _require_prior_meta_axis(
            self.hash_suite,
            expected_kind=HASH_SUITE_KIND,
            axis_name="hash-suite",
        )
        _require_prior_meta_axis(
            self.semantic_regime,
            expected_kind=SEMANTIC_REGIME_KIND,
            axis_name="semantic-regime",
        )
        if self.identity_profile != IDENTITY_PROFILE_ID:
            raise CanonicalError("unsupported identity profile")
        if self.hash_suite != HASH_SUITE_ID:
            raise CanonicalError("unsupported hash suite")
        if type(self.digest) is not bytes or len(self.digest) != 32:
            raise CanonicalError("this profile requires one SHA-256 digest")

    def internal_reference(self) -> bytes:
        self.__post_init__()
        return (
            _frame(_axis(self.foundation_profile))
            + _frame(self.identity_profile.internal_reference())
            + _frame(self.hash_suite.internal_reference())
            + _frame(_axis(self.subject_kind))
            + _frame(self.semantic_regime.internal_reference())
            + self.digest
        )

    def carrier(self) -> str:
        """Render a diagnostic carrier; this text is never hashed as identity."""

        return f"zkcidv0:{self.subject_kind}:{self.digest.hex()}"


def _require_typed_content_id(
    value: object,
    *,
    axis_name: str,
) -> TypedContentId:
    """Form one complete ContentRefV0 carrier without routing its semantics."""

    if type(value) is not TypedContentId:
        raise CanonicalError(f"{axis_name} must be a TypedContentId")
    value.__post_init__()
    return value


def content_id(
    subject_kind: str,
    body: bytes,
    *,
    semantic_regime: PriorMetaId,
    foundation_profile: str = FOUNDATION_PROFILE,
    identity_profile: PriorMetaId = IDENTITY_PROFILE_ID,
    hash_suite: PriorMetaId = HASH_SUITE_ID,
) -> TypedContentId:
    """Frame and hash typed axes plus a canonical body, without admitting it."""

    _axis(foundation_profile)
    _axis(subject_kind)
    if foundation_profile != FOUNDATION_PROFILE:
        raise CanonicalError("unsupported foundation profile")
    if subject_kind in PRIOR_META_SUBJECT_KINDS:
        raise CanonicalError(
            "prior-meta subjects cannot use the semantic-content constructor"
        )
    _require_prior_meta_axis(
        identity_profile,
        expected_kind=IDENTITY_PROFILE_KIND,
        axis_name="identity-profile",
    )
    _require_prior_meta_axis(
        hash_suite,
        expected_kind=HASH_SUITE_KIND,
        axis_name="hash-suite",
    )
    _require_prior_meta_axis(
        semantic_regime,
        expected_kind=SEMANTIC_REGIME_KIND,
        axis_name="semantic-regime",
    )
    if identity_profile != IDENTITY_PROFILE_ID:
        raise CanonicalError("unsupported identity profile")
    if hash_suite != HASH_SUITE_ID:
        raise CanonicalError("unsupported hash suite")
    if type(body) is not bytes:
        raise CanonicalError("identity preimage body must be bytes")
    decode_datum(body)
    preimage = (
        CONTENT_ID_PREFIX
        + _frame(_axis(foundation_profile))
        + _frame(identity_profile.internal_reference())
        + _frame(hash_suite.internal_reference())
        + _frame(_axis(subject_kind))
        + _frame(semantic_regime.internal_reference())
        + _frame(body)
    )
    return TypedContentId(
        foundation_profile,
        identity_profile,
        hash_suite,
        subject_kind,
        semantic_regime,
        hashlib.sha256(preimage).digest(),
    )


@dataclass(frozen=True)
class PriorMetaPreimageBundle:
    identity_profile: bytes
    hash_suite: bytes
    semantic_regime: bytes


class AuthenticationLedger:
    """Request-local grouping of successfully authenticated typed preimages."""

    __slots__ = ("_preimages",)

    def __init__(self) -> None:
        self._preimages: dict[PriorMetaId | TypedContentId, bytes] = {}

    @property
    def size(self) -> int:
        return len(self._preimages)

    def record_authenticated(
        self,
        identifier: PriorMetaId | TypedContentId,
        preimage: bytes,
    ) -> None:
        if type(identifier) not in (PriorMetaId, TypedContentId):
            raise CanonicalError("authentication ledger key has the wrong typed shape")
        identifier.__post_init__()
        if type(preimage) is not bytes:
            raise CanonicalError("authentication ledger preimage must be exact bytes")
        at_capacity = len(self._preimages) >= MAX_AUTHENTICATION_LEDGER_ENTRIES
        if identifier in self._preimages:
            if self._preimages[identifier] != preimage:
                raise HashBindingConflictError(
                    "one typed ID authenticated distinct preimages in one scope"
                )
            return
        if at_capacity:
            raise CanonicalError(
                "authentication ledger exceeds its derived request bound"
            )
        self._preimages[identifier] = preimage


def authenticate_prior_meta_id(
    identifier: PriorMetaId,
    descriptor_body: bytes,
    *,
    expected_kind: str,
    ledger: AuthenticationLedger | None = None,
) -> None:
    _require_prior_meta_axis(
        identifier,
        expected_kind=expected_kind,
        axis_name=expected_kind,
    )
    if meta_object_id(expected_kind, descriptor_body) != identifier:
        raise CanonicalError("prior-meta descriptor does not authenticate its ID")
    if ledger is not None:
        if type(ledger) is not AuthenticationLedger:
            raise CanonicalError("authentication ledger has the wrong exact shape")
        ledger.record_authenticated(identifier, descriptor_body)


def authenticate_content_id(
    identifier: TypedContentId,
    body: bytes,
    prior_meta_preimages: PriorMetaPreimageBundle,
    *,
    ledger: AuthenticationLedger | None = None,
) -> None:
    """Authenticate every ordinary axis before recomputing the subject ID."""

    _require_typed_content_id(identifier, axis_name="ordinary subject ID")
    if type(body) is not bytes:
        raise CanonicalError("ordinary subject body must be exact bytes")
    if type(prior_meta_preimages) is not PriorMetaPreimageBundle or any(
        type(item) is not bytes
        for item in (
            getattr(prior_meta_preimages, "identity_profile", None),
            getattr(prior_meta_preimages, "hash_suite", None),
            getattr(prior_meta_preimages, "semantic_regime", None),
        )
    ):
        raise CanonicalError("prior-meta basis has the wrong exact typed shape")
    authenticate_prior_meta_id(
        identifier.identity_profile,
        prior_meta_preimages.identity_profile,
        expected_kind=IDENTITY_PROFILE_KIND,
        ledger=ledger,
    )
    authenticate_prior_meta_id(
        identifier.hash_suite,
        prior_meta_preimages.hash_suite,
        expected_kind=HASH_SUITE_KIND,
        ledger=ledger,
    )
    authenticate_prior_meta_id(
        identifier.semantic_regime,
        prior_meta_preimages.semantic_regime,
        expected_kind=SEMANTIC_REGIME_KIND,
        ledger=ledger,
    )
    recomputed = content_id(
        identifier.subject_kind,
        body,
        semantic_regime=identifier.semantic_regime,
        foundation_profile=identifier.foundation_profile,
        identity_profile=identifier.identity_profile,
        hash_suite=identifier.hash_suite,
    )
    if recomputed != identifier:
        raise CanonicalError("semantic body does not authenticate its content ID")
    if ledger is not None:
        ledger.record_authenticated(identifier, body)


def authenticate_prior_meta_basis(
    prior_meta_preimages: PriorMetaPreimageBundle,
    *,
    ledger: AuthenticationLedger | None = None,
) -> None:
    """Authenticate the exact three constitutional descriptor preimages."""

    if type(prior_meta_preimages) is not PriorMetaPreimageBundle or any(
        type(body) is not bytes
        for body in (
            getattr(prior_meta_preimages, "identity_profile", None),
            getattr(prior_meta_preimages, "hash_suite", None),
            getattr(prior_meta_preimages, "semantic_regime", None),
        )
    ):
        raise CanonicalError("prior-meta basis has the wrong exact typed shape")

    authenticate_prior_meta_id(
        IDENTITY_PROFILE_ID,
        prior_meta_preimages.identity_profile,
        expected_kind=IDENTITY_PROFILE_KIND,
        ledger=ledger,
    )
    authenticate_prior_meta_id(
        HASH_SUITE_ID,
        prior_meta_preimages.hash_suite,
        expected_kind=HASH_SUITE_KIND,
        ledger=ledger,
    )
    authenticate_prior_meta_id(
        SEMANTIC_REGIME_ID,
        prior_meta_preimages.semantic_regime,
        expected_kind=SEMANTIC_REGIME_KIND,
        ledger=ledger,
    )


PrimitiveCatalogEntry: TypeAlias = tuple[
    int, str, int, bytes, bytes, tuple[int, ...], str
]


PRIMITIVE_SEMANTIC_CATALOG: tuple[PrimitiveCatalogEntry, ...] = (
    (
        0,
        "sha2-256",
        1,
        b"(Bytes[min,max])->Bytes[32,32]",
        b"FIPS-180-4-SHA-256(input[0])-as-32-octets",
        (),
        "pure-total-deterministic",
    ),
    (
        1,
        "bytes.concat",
        1,
        b"(Bytes[a,b],Bytes[c,d])->Bytes[a+c,b+d]",
        b"ordered-octet-concatenation(input[0],input[1])",
        (),
        "pure-total-deterministic",
    ),
    (
        2,
        "u64.to-be",
        1,
        b"(Nat[2^64-1])->Bytes[8,8]",
        b"fixed-width-eight-octet-big-endian(input[0])",
        (),
        "pure-total-deterministic",
    ),
    (
        3,
        "bytes.first-u64-be",
        1,
        b"(Bytes[min>=8,max])->Nat[2^64-1]",
        b"first-eight-octets-as-unsigned-big-endian-natural(input[0])",
        (),
        "pure-total-deterministic",
    ),
    (
        4,
        "nat.lt",
        1,
        b"(Nat[a],Nat[b])->Bool",
        b"input[0]-strictly-less-than-input[1]",
        (),
        "pure-total-deterministic",
    ),
    (
        5,
        "nat.mod-positive",
        1,
        b"(Nat[a],Nat[b])->Nat[a]!Failure[0:Unit]",
        b"if-input[1]=0-then-Failure[0,Unit]-else-euclidean-remainder",
        (0,),
        "pure-total-with-typed-failure",
    ),
    (
        6,
        "bytes.take",
        1,
        b"(Bytes[a,b],Nat[n])->Bytes[0,min(b,n)]",
        b"prefix-of-input[0]-of-length-min(length(input[0]),input[1])",
        (),
        "pure-total-deterministic",
    ),
    (
        7,
        "fixture.bytes.reverse",
        1,
        b"(Bytes[a,b])->Bytes[a,b]",
        b"reverse-octet-order(input[0])",
        (),
        "pure-total-deterministic",
    ),
    (
        8,
        "fixture.bytes.prefix-27",
        1,
        b"(Bytes[32,32])->Bytes[27,27]",
        b"first-exactly-27-octets-of-input[0]",
        (),
        "pure-total-deterministic",
    ),
)
PRIMITIVE_CATALOG_BY_KEY: Mapping[tuple[str, int], PrimitiveCatalogEntry] = (
    MappingProxyType(
        {(entry[1], entry[2]): entry for entry in PRIMITIVE_SEMANTIC_CATALOG}
    )
)


def primitive_catalog_datum(
    entries: Sequence[PrimitiveCatalogEntry] = PRIMITIVE_SEMANTIC_CATALOG,
) -> DatumSeq:
    if any(
        not _is_u64_natural(entry[0])
        or any(not _is_u64_natural(item) for item in entry[5])
        for entry in entries
    ):
        raise CanonicalError(
            "primitive and failure declaration ordinals must be u64 naturals"
        )
    if tuple(entry[0] for entry in entries) != tuple(range(len(entries))):
        raise CanonicalError(
            "primitive catalog ordinals must equal ordered body positions"
        )
    return DatumSeq(
        tuple(
            DatumRecord(
                (
                    (0, Symbol(name)),
                    (1, Nat(version)),
                    (2, BytesValue(type_rule_source)),
                    (3, BytesValue(operation_law_source)),
                    (
                        4,
                        DatumSeq(
                            tuple(
                                DatumRecord(
                                    (
                                        (0, Symbol("semantic-failure")),
                                        (1, Nat(item)),
                                    )
                                )
                                for item in failure_ordinals
                            )
                        ),
                    ),
                    (5, Symbol(discipline)),
                )
            )
            for (
                ordinal,
                name,
                version,
                type_rule_source,
                operation_law_source,
                failure_ordinals,
                discipline,
            ) in entries
        )
    )


SEMANTIC_CORE_NAMES = DatumSeq(
    tuple(
        Symbol(name)
        for name in (
            "unit",
            "bool",
            "nat",
            "int",
            "bytes",
            "symbol",
            "seq",
            "record",
            "variant",
            "literal",
            "variable",
            "let",
            "record-construct",
            "project",
            "inject",
            "case",
            "sequence-construct",
            "sequence-length",
            "fail",
            "strict-index",
            "bounded-append",
            "primitive-call",
            "bounded-iterate",
            "conditional",
        )
    )
)
SEMANTIC_CORE_LAW_SOURCE = b"""zkc.foundation.semantic-core-law.v0
source-encoding=ASCII-0x20..0x7e;LF-after-every-line-including-last;no-CR
notation=U:MetaUnit;MF:MetaBooleanFalse;MT:MetaBooleanTrue;N(n):MetaNatural(n);I(z):MetaInt(z);O(x):MetaBytes(x);Q(x):MetaSymbol(x);S[x...]:MetaSeq(x...);R{n:x,...}:MetaRecord((n,x)...);V(n,x):MetaVariant(n,x);M(x):FoundationMetaProfileV0-canonical-bytes
reference-notation=PR(id):PriorRefV0(id);CR(id):ContentRefV0(id);SR:SemanticRegimeId-derived-from-this-exact-descriptor
basis-notation=B:the-enclosing-authenticated-PriorMetaAuthenticationBasis-with-B.semantic-regime.id=SR
ordinary-id(K,b):=SemanticContentId<K>(B,b)
foundation-standalone-semantic-kinds=foundation.canonical-value,foundation.evaluation-contract,foundation.external-operation-contract,foundation.portable-algorithm,foundation.semantic-language-profile,foundation.semantic-module,foundation.semantic-primitive
identity-body-mode-law=every-foundation-standalone-semantic-kind-has-only-its-exact-dedicated-body-constructor;prior-meta-kinds-remain-a-separate-constructor-class;profiled-semantic-subjects-use-neither-class;raw-ordinary-id-is-structural-framing-and-never-semantic-admission
sequence-notation=S[...] preserves written order;R fields are written in increasing ordinal order;map preserves source order
selected-limits=axis-octets<=1048576;meta-bytes<=1048576;meta-nodes<=16384;meta-child-edges<=16384;meta-root-zero-depth<=384;schema-nodes<=16384;schema-root-zero-depth<=48;term-nodes<=4096;term-root-zero-depth<=48;profile-bundle-entries<=16384;profile-nodes<=16384;profile-import-edges<=16384;module-bundle-entries<=16384;module-nodes<=16384;module-import-edges<=16384;sequence-capacity<=16384;all-bounds-inclusive
axis-admission=A(s)-is-nonempty-printable-ASCII-and-length-at-most-1048576-checked-before-character-conversion-or-scanning
pair-authentication=exact-typed-constructor-kind-and-axes;strict-canonical-body-decode-and-reencode;recomputed-governing-digest-equals-asserted-ID
closed-validation-scope=one-top-level-admission-check-or-evaluation-transaction-from-prior-meta-basis-authentication-through-final-decision;includes-every-request-preimage-and-every-consulted-successfully-authenticated-registry-resolver-or-cache-preimage
hash-binding-conflict=same-exact-typed-ID-and-two-pair-authenticated-distinct-canonical-descriptor-or-body-byte-strings-in-one-closed-validation-scope
hash-binding-conflict-outcome=CheckerFailure-before-owner-admission-or-capability;equal-byte-reobservation-is-idempotent;retained-cross-transaction-authentication-state-requires-equivalent-cross-scope-grouping-and-quarantine-or-per-transaction-reauthentication
aggregate-bound-owners=MetaValue-sequence-or-record:remaining-cumulative-meta-child-edges-and-nodes;FiniteSchema-record-or-variant:per-aggregate-meta-child-edge-ceiling-plus-remaining-cumulative-schema-node-minimum-reservation;SemanticFunction-inputs-or-failures,PrimitiveDeclaration-failures,PrimitiveWork-indices,EvaluationContract-cost-rules,SemanticModule-declaration-catalogs-or-bodies,SemanticLanguageProfile-supported-kinds-or-declaration-catalogs,PortableAlgorithm-inputs:per-aggregate-meta-child-edge-ceiling;CanonicalTerm-multi-child:remaining-term-nodes;SemanticLanguageProfile-imports:per-profile-import-edge-ceiling-then-authenticated-closure-remaining-edge-reservation;ProfilePreimageBundle:profile-bundle-entries;SemanticModule-imports:per-module-import-edge-ceiling-then-authenticated-closure-remaining-edge-reservation;DirectModuleRoots:module-node-ceiling;ModulePreimageBundle:module-bundle-entries;EvaluationRequest-inputs:derived-function-input-count
aggregate-admission-preflight=every-aggregate-bearing-semantic-carrier-has-the-explicit-owner-above;check-its-declared-or-trusted-cardinality-against-that-bound-before-member-inspection-or-derived-aggregate-construction;the-serialized-carrier-separately-owns-aggregate-raw-byte-preflight
u64-range=0..18446744073709551615
core-names=unit,bool,nat,int,bytes,symbol,seq,record,variant,literal,variable,let,record-construct,project,inject,case,sequence-construct,sequence-length,fail,strict-index,bounded-append,primitive-call,bounded-iterate,conditional
root-domain-kind=foundation.root-value-domain
root-domain-bodies=0:Q(unit),1:Q(bool),2:Q(nat),3:Q(int),4:Q(bytes),5:Q(symbol),6:Q(seq),7:Q(record),8:Q(variant)
root-domain-catalog=kind:foundation.root-value-domain;ordinals:0..8-only;owner:SR
root-term-name-tags=literal:0,variable:1,let:2,record-construct:3,project:4,inject:5,case:6,sequence-construct:7,sequence-length:8,fail:9,strict-index:10,bounded-append:11,primitive-call:12,bounded-iterate:13,conditional:14
root-primitive-catalog=empty
module-kind=foundation.semantic-module
module-catalog-body=R{0:Q(kind),1:S[bodies...]}
module-body=R{0:S[O(CR(import))...],1:S[module-catalog-body...],2:domain-payload}
module-id(m)=ordinary-id(foundation.semantic-module,module-body(m))
module-self-id=absent-from-module-body
module-nonauthority=container-and-diagnostic-label-are-outside-module-body-and-cannot-change-portable-authentication-admission-declaration-resolution-evaluation-or-completion
module-import-admission=each-import-kind-foundation.semantic-module;each-import-regime-SR;ascending-full-CR-bytes;no-duplicates
module-catalog-admission=ascending-A(kind)-bytes;unique-kinds;body-position-is-zero-based-local-ordinal
module-value-domain-kind=value-domain
module-value-domain-body=ValueDomainDeclarationBody(name):=R{0:Q(name)}
module-value-domain-admission=catalog-kind-is-exactly-value-domain;body-is-exactly-one-field-0-containing-a-valid-MetaSymbol-name;declares-one-opaque-nominal-domain-only;does-not-establish-DomainSupport
local-decl-ref-body=LDRB(kind,ordinal):=R{0:Q(kind),1:N(ordinal)}
local-decl-ref-admission=ordinal-is-u64;target-is-a-declaration-in-the-same-authenticated-aggregate;cross-kind-local-refs-are-permitted;supported-kind-specific-admission-owns-finite-local-SCC-and-cycle-legality
module-closed-scc-law=mutually-recursive-declarations-are-one-finite-aggregate-module-and-use-LDRB;ordinary-module-imports-remain-acyclic
module-reference-grammar=within-supported-kind-specific-declaration-bodies,LDRB-same-aggregate,DRB-Root-SR,and-DRB-Module-authenticated-import-closure-refs-are-permitted;arbitrary-body-bytes-are-never-scanned-for-references
decl-ref-root-body=DRB(Root(r,k,n)):=V(0,R{0:O(PR(r)),1:Q(k),2:N(n)})
decl-ref-module-body=DRB(Module(m,k,n)):=V(1,R{0:O(CR(m)),1:Q(k),2:N(n)})
decl-ref-admission=Root-owner-is-exact-SR;Module-owner-kind-is-foundation.semantic-module-and-owner-regime-is-SR;ordinal-is-u64
decl-ref-resolution=Root-resolves-exact-kind-and-position-in-authenticated-SR-root;Module-resolves-exact-kind-and-position-in-authenticated-owner-module
decl-ref-no-inference=root-or-module-tag-owner-kind-and-ordinal-are-identity-bearing;names-registry-search-and-equal-digests-do-not-resolve
declaration-domain-ref-body=DDRB(Local(kind,n)):=V(0,LDRB(kind,n));DDRB(Durable(d)):=V(1,DRB(d))
declaration-value-type=DVT(domain,schema)
declaration-value-type-body=DVTB(DVT(d,s)):=R{0:DDRB(d),1:DSB(s)}
declaration-schema-body.Unit=DSB(Unit):=V(0,U)
declaration-schema-body.Bool=DSB(Bool):=V(1,U)
declaration-schema-body.Nat=DSB(Nat(max)):=V(2,N(max))
declaration-schema-body.Int=DSB(Int(min,max)):=V(3,R{0:I(min),1:I(max)})
declaration-schema-body.Bytes=DSB(Bytes(min,max)):=V(4,R{0:N(min),1:N(max)})
declaration-schema-body.Symbol=DSB(Symbol(max)):=V(5,N(max))
declaration-schema-body.Seq=DSB(Seq(element,max)):=V(6,R{0:DVTB(element),1:N(max)})
declaration-schema-body.Record=DSB(Record[(n,T)...]):=V(7,S[R{0:N(n),1:DVTB(T)}...])
declaration-schema-body.Variant=DSB(Variant[(n,T)...]):=V(8,S[R{0:N(n),1:DVTB(T)}...])
declaration-schema-admission=same-exact-scalar,ordinal,structure,worst-case,and-constitutional-body-bounds-as-FiniteSchema-with-every-recursive-child-a-DeclarationValueType
declaration-ref-lift.local=LiftRef_m(Local(kind,n)):=Module(m,kind,n)
declaration-ref-lift.root=LiftRef_m(Durable(Root(SR,kind,n))):=Root(SR,kind,n)
declaration-ref-lift.import=LiftRef_m(Durable(Module(target,kind,n))):=Module(target,kind,n)-iff-target!=m-and-target-is-in-the-authenticated-transitive-import-closure-of-m
declaration-ref-lift.self=LiftRef_m(Durable(Module(m,kind,n)))-refuses
declaration-schema-lift.scalar=LiftSchema_m(Unit):=Unit;LiftSchema_m(Bool):=Bool;LiftSchema_m(Nat(max)):=Nat(max);LiftSchema_m(Int(min,max)):=Int(min,max);LiftSchema_m(Bytes(min,max)):=Bytes(min,max);LiftSchema_m(Symbol(max)):=Symbol(max)
declaration-schema-lift.aggregate=LiftSchema_m(Seq(T,max)):=Seq(LiftType_m(T),max);LiftSchema_m(Record[(n,T)...]):=Record[(n,LiftType_m(T))...];LiftSchema_m(Variant[(n,T)...]):=Variant[(n,LiftType_m(T))...]
declaration-type-lift=LiftType_m(DVT(d,s)):=VT(LiftRef_m(d),LiftSchema_m(s))
declaration-lift-precondition=LiftRef_m,LiftSchema_m,and-LiftType_m-are-defined-only-after-m-and-its-exact-transitive-import-closure-authenticate;durable-same-module-spelling-refuses-even-when-a-caller-omits-the-declaring-module-context
declaration-lift-result-admission=for-every-D,LiftType_m(D)-and-every-recursively-lifted-nested-ValueType-must-have-an-exact-ValueDomainRef-and-VTB(LiftType_m(D))-must-satisfy-ordinary-same-regime-schema-and-type-body-admission-and-all-constitutional-bounds;DVTB-or-DSB-fit-alone-is-insufficient;failure-refuses-during-supported-kind-specific-declaration-admission
declaration-local-domain-admission=each-Local(value-domain,n)-used-as-a-domain-resolves-in-the-same-authenticated-module-aggregate-to-an-exact-admitted-ValueDomainDeclarationBody;Local(kind,n)-with-kind!=value-domain-cannot-be-a-domain
local-ref-nondurability=LDRB-has-no-owner-id,is-never-a-DRB,cannot-cross-an-import,cannot-escape-its-module,cannot-be-independently-content-addressed,and-cannot-use-a-durable-self-spelling
kind-specific-local-type-law=every-supported-kind-specific-body-that-stores-a-value-type-uses-DVTB-inside-the-module-and-compares-the-exact-LiftType_m-result-to-its-outward-ValueType-semantics;semantic-failure-payload-types-must-do-so
recognized-declaration-formation=for-every-recognized-kind-K,strict-decoding-into-K's-exact-typed-body-grammar-precedes-owner-context-interpretation;wrong-constructor,tag,record-field-set-or-order,or-field-carrier-is-Malformed;only-after-formation-can-closed-owner-admission-run
typed-coordinate-formation=before-coordinate-routing,every-PriorRefV0-and-ContentRefV0-carrier-must-have-its-exact-host-constructor,canonical-foundation-and-nested-prior-meta-axes,and-exact-32-byte-digest;failure-is-Malformed;only-a-fully-formed-carrier-can-be-compared-with-the-consuming-slot's-required-namespace,subject-kind,semantic-regime,owner-kind,or-other-semantic-axis,and-disagreement-is-KindMismatch
declaration-resolution-phases=at-each-hierarchical-recognized-body-boundary,strictly-form-the-complete-body-and-all-of-its-immediate-reference-carriers,then-classify-and-resolve-the-complete-explicit-coordinate-set-for-owner,kind,regime,scope,and-exact-local-position,before-interpreting-any-selected-target-body;repeat-the-same-sequence-for-each-selected-nested-body-before-contextual-lift-or-admission
direct-primitive-refs=all-distinct-exact-(primitive-id,declaration-ref)-pairs-structurally-present-in-PrimitiveCall-nodes;ascending-lexicographic-(CR(primitive-id),PrimitiveBody(ref))-bytes;only-exact-pair-duplicates-collapse
primitive-ref-pair-law=every-retained-pair-authenticates-before-primitive-support-lookup;failed-asserted-id-and-body-authentication-is-Malformed;same-typed-id-with-distinct-pair-authenticated-declaration-bodies-is-HashBindingConflict;equal-pair-reobservation-is-idempotent;same-declaration-body-cannot-authenticate-as-two-ids-under-one-fixed-deterministic-basis
direct-declaration-refs=all-declaration-references-in-ordered-input-types,literal-types,term-type-annotations,failure-constructors,and-declaration-halves-of-direct-primitive-refs;include-all-recursively-nested-value-types;never-scan-arbitrary-data
direct-module-roots=unique-module-owners-of-direct-declaration-refs;ascending-full-CR(module-id)-bytes
authenticated-imports-B(m,P)=imports-from-P[m]-only-after-strict-module-body-decode-and-recomputed-module-id-equals-m-under-basis-B
required-module-closure-B(alg,P)=least-X-containing-direct-module-roots-and-every-authenticated-import-of-every-m-in-X
module-preimage-bundle=finite-map-from-asserted-module-id-to-exact-module-body-bytes;entry-count<=16384-checked-before-key-iteration-or-copy;every-key-carrier-then-forms-and-routes-as-an-exact-same-regime-foundation.semantic-module-ID-before-map-copy-or-key-set-comparison;keys-ascending-full-CR-bytes;no-duplicate-key;aggregate-raw-carrier-byte-bound-is-owned-by-the-serialized-request-carrier
module-closure-order=depth-first;direct-roots-ascending;each-import-list-ascending;authenticate-reached-candidate-before-reading-its-imports-or-classifying-a-candidate-selected-cycle;reserve-the-whole-authenticated-import-list-against-the-remaining-closure-edge-budget-before-scheduling-or-inspecting-any-child-target
module-closure-admission=every-reached-key-recomputed-before-its-imports;keys(P)-equal-required-module-closure-after-traversal;unreferenced-extra-keys-refused-without-body-interpretation;no-missing-wrong-kind-cross-regime-id-mismatch-or-cycle
module-closure-measure=each-unique-module-node-once;each-authenticated-module-import-edge-once;shared-diamond-target-authenticated-and-expanded-once
module-closure-limits=unique-nodes<=16384;import-edges<=16384
semantic-language-profile-kind=foundation.semantic-language-profile
semantic-language-profile-body=SLPB(family,revision,imports,kinds,catalogs,law):=R{0:Q(family),1:N(revision),2:S[O(CR(profile-import_i))...],3:S[Q(kind_i)...],4:S[R{0:Q(declaration-kind),1:S[declaration-body...] }...],5:O(law)}
semantic-language-profile-id=SLPId(profile):=ordinary-id(foundation.semantic-language-profile,SLPB(profile));regime-axis-SR
semantic-language-profile-formation=family,each-supported-kind,and-each-declaration-kind-are-exact-Symbols;revision-is-u64;imports-are-ascending-full-CR-unique-same-SR-foundation.semantic-language-profile-IDs;kinds-is-nonempty-ascending-ASCII-and-unique;no-kind-is-prior-meta-or-any-foundation-standalone-semantic-kind;catalog-kinds-are-ascending-ASCII-and-unique;body-position-is-zero-based-local-ordinal;law-is-nonempty-exact-bytes;constitutional-body-bounds-apply
semantic-language-profile-preimages=finite-map-from-asserted-SLPId-to-exact-SLPB;entry-count<=16384-before-key-inspection-or-copy;every-key-forms-and-routes-before-map-copy-or-key-set-comparison
semantic-language-profile-closure=depth-first-from-the-selected-SLPId;authenticate-each-profile-before-reading-its-imports-or-classifying-a-selected-cycle;keys(bundle)-equal-the-reached-profile-DAG;no-missing,extra,wrong-kind,cross-regime,forged,or-cyclic-profile;unique-profile-nodes<=16384;profile-import-edges<=16384
profile-declaration-ref-body=PDRB(Local(kind,n)):=V(0,R{0:Q(kind),1:N(n)});PDRB(Imported(profile,kind,n)):=V(1,R{0:O(CR(profile)),1:Q(kind),2:N(n)})
profile-declaration-ref-admission=Local-resolves-only-in-the-selected-profile;Imported-owner-is-a-distinct-exact-profile-in-the-authenticated-import-closure;kind-and-ordinal-resolve-exactly;self-spelled-as-Imported-refuses;arbitrary-bytes-have-no-reference-semantics
profiled-semantic-body=PSB(profile-id,body):=R{0:O(CR(profile-id)),1:body}
profiled-semantic-id=ordinary-id(subject-kind,PSB(profile-id,domain-body));the-exact-standalone-profile-ID-is-in-the-subject-preimage;subject-kind-is-neither-prior-meta-nor-any-foundation-standalone-semantic-kind
effective-semantic-context=ESC(profile-id,profile-preimages):=(SR,profile-id,authenticated-selected-SLPB,canonical-authenticated-profile-DAG)
effective-semantic-context-admission=authenticate-the-exact-no-extra-profile-closure;subject-kind-is-in-the-selected-SLPB-kinds;evaluator-support-explicitly-contains-the-exact-selected-SLPId;family-or-revision-equality-alone-is-insufficient;subject-specific-module-closures-remain-separate-domain-inputs
profile-reference-exclusions=SLPB-has-no-structured-self,governed-subject,evidence,policy,capability,module,or-live-authority-reference;profile-imports-point-only-upstream;only-PDRB-has-profile-declaration-reference-semantics;fixpoint-construction-is-never-used
profile-support-law=unequal-effective-contexts-have-no-intrinsic-compatibility-and-require-a-separate-owner-checked-edge
profile-evolution=changing-a-selected-profile-or-imported-profile-rotates-dependent-subject-IDs;adding-or-changing-an-unreferenced-profile-does-not;subject-specific-module-evolution-is-owned-and-authenticated-separately
owner-capability-requirement-body=OCRB(owner,family,owner-requirement):=R{0:Q(owner),1:Q(family),2:O(CR(owner-requirement))}
owner-policy-disposition-body=OPDB(BoundTo(owner-policy-binding)):=V(0,O(CR(owner-policy-binding)));OPDB(NoPolicy(owner-no-policy-declaration)):=V(1,O(CR(owner-no-policy-declaration)))
portable-source-authority-binding-body=PSABB(owner,family,source-coordinate,binding-payload,policy,policy-closure,requirement):=R{0:Q(owner),1:Q(family),2:O(CR(source-coordinate)),3:O(CR(binding-payload)),4:OPDB(policy),5:O(CR(policy-closure)),6:OCRB(requirement)}
portable-source-authority-binding-formation=owner-and-family-are-Symbols-and-equal-the-enclosed-OCRB-owner-and-family;all-refs-share-the-source-coordinate-SR;the-owner-authenticates-and-interprets-the-exact-profiled-source-coordinate,binding-payload,policy-disposition,complete-derived-policy-closure,and-requirement
authority-envelope-inertness=OCRB,OPDB,and-PSABB-are-canonical-inert-bodies-only;their-owner-defined-ID-targets-carry-all-domain-specific-ABI,binding,freshness,lifetime,fact,qualification,assurance,trust,policy,and-completeness-semantics;the-envelope-never-mints-or-contains-a-live-capability,occurrence,mutable-handle,checker-cache,or-provider-object
owner-local-source-authority-binding=inert-process-local-metadata(owner,family,owner-local-coordinate,binding-payload,policy,policy-closure,requirement);fresh-live-capability-is-a-separate-checking-input;the-local-binding-has-no-canonical-body-or-content-ID;serialization,hashing,copying,FFI,caching,or-evidence-does-not-transport-the-local-coordinate-or-live-capability
module-declaration-reference-scope=after-module-authentication-each-supported-kind-interprets-only-its-exact-body-law;recognized-target-is-LDRB-in-the-same-aggregate,SR-root,or-a-module-in-the-declaring-module-import-closure;an-unrecognized-kind-in-a-generic-extension-capable-declaration-position-is-Unsupported;an-exact-typed-slot-carrying-a-kind-other-than-its-required-K-is-KindMismatch;unreferenced-unknown-catalogs-are-inert
primitive-candidates-not-module-nodes=primitive-id-is-a-direct-algorithm-dependency;primitive-declaration-resolves-through-its-owner-module;only-module-imports-form-the-transitive-preimage-DAG
value-domain-ref=Root(SR,foundation.root-value-domain,n)-with-n-in-0..8-or-Module(m,value-domain,n)-whose-resolved-body-passes-module-value-domain-admission;no-other-kind-or-body-is-a-value-domain-ref
value-domain-ref-body=VDRB(d):=DRB(d)
value-type=VT(d,s):=(domain:d,schema:s)
value-type-body=VTB(VT(d,s)):=R{0:VDRB(d),1:SB(s)}
value-type-regime=domain-and-every-recursively-nested-value-type-have-exact-regime-SR
domain-support=DomainSupport(E,d):=Supports(E,(d,Resolve(d)),PortableValueDomainAdmissionV0)
domain-support-contract=exact-total-deterministic-schema-admission+datum-membership+unique-canonical-decode-encode+mathematical-equality-for-the-exact-ref-and-body;support-does-not-transfer-between-owner-kind-ordinal-or-body
root-domain-support=intrinsic-only-for-root-domain-kind-ordinals-0..8-with-the-exact-matching-outer-schema-constructor
module-domain-support=module-owned-domain-is-opaque;FiniteSchema-is-only-a-carrier-shape-bound;resolution-or-shape-does-not-prove-membership;without-exact-DomainSupport-use-is-Unsupported-before-domain-interpretation-or-owner-admission
root-structural-boundary=generic-Boolean,record,variant,sequence,and-natural-operations-require-the-exact-corresponding-root-domain;schema-shape-equality-is-insufficient
module-value-entry=first-entry-only-as-owner-admitted-literal,owner-admitted-input,or-owner-admitted-result-of-an-exact-supported-primitive;root-aggregate-members-may-contain-already-admitted-same-regime-module-values
canonical-value=CV(T,v,d,M(d));d-is-the-unique-domain-admitted-MetaValueV0-representative-of-v;strict-decode-consumes-one-datum-reencodes-identically-and-owner-admits
canonical-and-root-value-equality=defined-only-for-values-with-the-same-exact-ValueType;then-use-the-exact-domain-owned-mathematical-equality;selected-root-domains-use-equality-of-their-unique-admitted-datums;same-domain-values-under-different-FiniteSchemas-are-not-equal-at-this-typed-value-layer
canonical-value-id-body(P,T,d):=R{0:Q(P),1:VDRB(T.domain),2:SB(T.schema),3:d}
canonical-value-id(P,T,d):=ordinary-id(foundation.canonical-value,canonical-value-id-body(P,T,d));P-is-the-caller-purpose-kind-and-is-identity-bearing-but-not-the-ID-subject-kind;defined-only-after-exact-domain-admission;private-or-unaddressed-values-need-no-id
schema-body.Unit=SB(Unit):=V(0,U)
schema-body.Bool=SB(Bool):=V(1,U)
schema-body.Nat=SB(Nat(max)):=V(2,N(max))
schema-body.Int=SB(Int(min,max)):=V(3,R{0:I(min),1:I(max)})
schema-body.Bytes=SB(Bytes(min,max)):=V(4,R{0:N(min),1:N(max)})
schema-body.Symbol=SB(Symbol(max)):=V(5,N(max))
schema-body.Seq=SB(Seq(element,max)):=V(6,R{0:VTB(element),1:N(max)})
schema-body.Record=SB(Record[(n,T)...]):=V(7,S[R{0:N(n),1:VTB(T)}...])
schema-body.Variant=SB(Variant[(n,T)...]):=V(8,S[R{0:N(n),1:VTB(T)}...])
schema-ordinal-law=record-fields-and-variant-cases-use-u64-ordinals-in-strictly-increasing-order;variant-case-list-is-nonempty
schema-scalar-bounds=Nat:0<=max<2^256;Int:min<=max-and-max(abs(min),abs(max))<2^255;Bytes:0<=min<=max<=1048576;Symbol:1<=max<=4096;Seq:0<=max<=16384
schema-structure=finite-acyclic-occurrence-tree;nodes<=16384;root-zero-depth<=48
schema-type-body-bound=M(VTB(T))-fits-meta-bytes-nodes-child-edges-and-root-zero-depth-selected-limits
canonical-value-type-formation=direct-VTB-is-a-refined-carrier-and-forms-only-after-schema-ordinal,scalar,finite-tree,Worst,and-type-body-bounds-all-hold;failure-in-a-presented-algorithm-or-value-header-is-Malformed;raw-DVTB-first-forms-its-complete-grammar-and-post-formation-contextual-lift-or-closed-schema-admission-failure-is-Refused;derived-maximum-completion-schema-bound-failure-is-Refused
mag(n)=max(1,ceil(bitlength(n)/8))
worst.Unit=Worst(Unit):=(1,1,0,0)
worst.Bool=Worst(Bool):=(1,1,0,0)
worst.Nat=Worst(Nat(max)):=(9+mag(max),1,0,0)
worst.Int=Worst(Int(min,max)):=(10+mag(max(abs(min),abs(max))),1,0,0)
worst.Bytes=Worst(Bytes(min,max)):=(9+max,1,0,0)
worst.Symbol=Worst(Symbol(max)):=(9+max,1,0,0)
worst.Seq=Worst(Seq(T,c)):=(9+c*(8+w.bytes),1+c*w.nodes,c*(1+w.edges),if-c=0-then-0-else-1+w.depth);w:=Worst(T.schema)
worst.Record=Worst(Record[(n,T_i)...]):=(9+sum_i(16+w_i.bytes),1+sum_i(w_i.nodes),count+sum_i(w_i.edges),if-count=0-then-0-else-1+max_i(w_i.depth));w_i:=Worst(T_i.schema)
worst.Variant=Worst(Variant[(n,T_i)...]):=(17+max_i(w_i.bytes),1+max_i(w_i.nodes),1+max_i(w_i.edges),1+max_i(w_i.depth));w_i:=Worst(T_i.schema)
schema-worst-admission=for-Worst(s)=(bytes,nodes,edges,depth):bytes<=1048576;nodes<=16384;edges<=16384;depth<=384
max-datum-bytes=MaxDatumBytes(T):=Worst(T.schema).bytes
actual-datum-admission=exactly-one-strict-MetaValueV0-datum;recursive-carrier-shape-match;actual-meta-bytes-nodes-child-edges-and-depth-within-selected-limits;then-exact-domain-owner-membership
root-membership.Unit=Unit-admits-only-U
root-membership.Bool=Bool-admits-only-MF-or-MT
root-membership.Nat=Nat(max)-admits-N(n)-iff-0<=n<=max
root-membership.Int=Int(min,max)-admits-I(z)-iff-min<=z<=max
root-membership.Bytes=Bytes(min,max)-admits-O(x)-iff-min<=length(x)<=max
root-membership.Symbol=Symbol(max)-admits-Q(x)-iff-1<=ASCII-length(x)<=max-and-each-octet-is-0x21..0x7e
root-membership.Seq=Seq(T,max)-admits-S[x_0...x_(k-1)]-iff-k<=max-and-each-x_i-is-owner-admitted-at-T
root-membership.Record=Record[(n_i,T_i)...]-admits-R{n_i:x_i,...}-iff-the-ordinal-sequence-is-exact-and-each-x_i-is-owner-admitted-at-T_i
root-membership.Variant=Variant[(n_i,T_i)...]-admits-V(n_j,x)-iff-n_j-is-a-declared-case-and-x-is-owner-admitted-at-T_j
root-type-aliases=RootUnit:=VT(Root(SR,foundation.root-value-domain,0),Unit);RootBool:=VT(Root(SR,foundation.root-value-domain,1),Bool);RootNat[m]:=VT(Root(SR,foundation.root-value-domain,2),Nat(m));RootInt[a,b]:=VT(Root(SR,foundation.root-value-domain,3),Int(a,b));RootBytes[a,b]:=VT(Root(SR,foundation.root-value-domain,4),Bytes(a,b));RootSymbol[m]:=VT(Root(SR,foundation.root-value-domain,5),Symbol(m));RootSeq[T,c]:=VT(Root(SR,foundation.root-value-domain,6),Seq(T,c));RootRecord[F]:=VT(Root(SR,foundation.root-value-domain,7),Record(F));RootVariant[C]:=VT(Root(SR,foundation.root-value-domain,8),Variant(C))
failure-type=Failure(module,ordinal,payload-type);module-kind-foundation.semantic-module;module-regime-SR;declaration-kind-semantic-failure
failure-type-body=FT(Failure(m,n,T)):=R{0:DRB(Module(m,semantic-failure,n)),1:VTB(T)}
failure-declaration-body=FailureDeclarationBody(name,D):=R{0:Q(name),1:DVTB(D)}
failure-declaration-admission=exact-owner-module-m-and-ordinal-resolve-to-one-strict-FailureDeclarationBody(name,D);name-is-a-valid-Symbol;D-is-an-admitted-localizable-declaration-value-type;LiftType_m(D)-equals-the-outward-payload-type-exactly;payload-regime-SR
primitive-ref=PrimitiveRef(id,module,ordinal);id-kind-foundation.semantic-primitive;module-kind-foundation.semantic-module;both-regime-SR;declaration-kind-semantic-primitive
primitive-semantic-body=PrimitiveBody(p):=DRB(Module(p.module,semantic-primitive,p.ordinal))
primitive-id-law=p.id=ordinary-id(foundation.semantic-primitive,PrimitiveBody(p))
primitive-ref-body=PRB(p):=R{0:O(CR(p.id)),1:DRB(Module(p.module,semantic-primitive,p.ordinal))}
primitive-declaration-body=PrimitiveDeclarationBody(name,version,type-source,operation-source,failures,discipline):=R{0:Q(name),1:N(version),2:O(type-source),3:O(operation-source),4:S[LDRB(semantic-failure,n_i)...],5:Q(discipline)}
primitive-declaration-formation=name-and-discipline-are-Symbols;version-and-each-failure-ordinal-are-u64;n_i-resolves-in-the-same-authenticated-module-to-one-strict-FailureDeclarationBody-whose-localizable-payload-type-forms-and-lifts;malformed-primitive,local-failure,or-DVT-or-DSB-structure-is-Malformed;formed-wrong-kind-or-regime-coordinate-is-KindMismatch;absent-local-failure-coordinate-or-post-formation-closed-lift-admission-failure-is-Refused
primitive-declaration-admission=exact-owner-module-and-ordinal-resolve-to-one-strict-PrimitiveDeclarationBody;the-supported-kind-law-interprets-the-immutable-type-and-operation-sources-and-fixes-exact-input-and-derived-output-rule,exact-failure-row,semantic-dependencies,state-and-effect-discipline,bounds,distribution,canonicality,and-side-conditions
primitive-denotation=total-deterministic-function-of-exact-owner-admitted-arguments;returns-exact-owner-admitted-derived-success-or-one-declared-typed-failure;semantic-state-is-explicit-input-and-output;ambient-state,freshness,I/O,and-supplier-behavior-are-forbidden
primitive-provider-law=provider-and-build-identity-are-nonsemantic-unless-explicitly-identified;lack-of-provider-is-operational-noncompletion;provider-disagreement-is-checker-or-conformance-failure
function-type=Fn(inputs,success,failures)
function-type-body=FnB(Fn(inputs,success,failures)):=R{0:S[VTB(input_i)...],1:VTB(success),2:S[FT(failure_i)...]}
failure-row-order=ascending-M(FT(f))-bytes;exact-duplicates-collapse;same-declaration-with-different-payload-type-refuses
failure-row-derivation=canonical-union-of-every-failure-in-every-structurally-present-subterm-including-unselected-case-and-conditional-branches,each-explicit-Fail,StrictIndex,and-BoundedAppend-failure,and-each-resolved-primitive-declaration-row
external-operation-contract-body=EOCB(kind,abi):=R{0:Q(kind),1:FnB(abi)}
external-operation-contract-id=ordinary-id(foundation.external-operation-contract,EOCB(kind,abi));kind-is-an-identity-bearing-operation-purpose-and-abi-is-an-exact-same-regime-SemanticFunctionType
external-operation-binding-nonauthority=provider-binding-is-outside-EOCB-and-cannot-rotate-the-contract-ID-or-inherit-portable-algorithm-denotation;execution-requires-a-separate-owner-capability-contract
semantic-completion=Success(CV(success,...))|DomainFailure(failure_i,CV(failure_i.payload-type,...));only-these-are-semantic-completions
term-body.Literal=TB(Literal(v)):=V(0,R{0:VTB(v.type),1:v.datum})
term-body.Variable=TB(Variable(n,T)):=V(1,R{0:N(n),1:VTB(T)})
term-body.Let=TB(Let(bound,body)):=V(2,R{0:TB(bound),1:TB(body)})
term-body.RecordConstruct=TB(RecordConstruct[(n,e)...]):=V(3,S[R{0:N(n),1:TB(e)}...])
term-body.Project=TB(Project(record,n)):=V(4,R{0:TB(record),1:N(n)})
term-body.Inject=TB(Inject(n,payload,sum-type)):=V(5,R{0:N(n),1:TB(payload),2:VTB(sum-type)})
term-body.Case=TB(Case(scrutinee,[(n,branch)...])):=V(6,R{0:TB(scrutinee),1:S[R{0:N(n),1:TB(branch)}...]})
term-body.SequenceConstruct=TB(SequenceConstruct(T,[e...],capacity)):=V(7,R{0:VTB(T),1:S[TB(e)...],2:N(capacity)})
term-body.SequenceLength=TB(SequenceLength(source)):=V(8,TB(source))
term-body.Fail=TB(Fail(f,payload,success-type)):=V(9,R{0:FT(f),1:TB(payload),2:VTB(success-type)})
term-body.StrictIndex=TB(StrictIndex(source,index,f)):=V(10,R{0:TB(source),1:TB(index),2:FT(f)})
term-body.BoundedAppend=TB(BoundedAppend(source,element,f)):=V(11,R{0:TB(source),1:TB(element),2:FT(f)})
term-body.PrimitiveCall=TB(PrimitiveCall(p,[argument...])):=V(12,R{0:PRB(p),1:S[TB(argument)...]})
iteration-source-body=IS(SequenceSource(e)):=V(0,TB(e));IS(RangeSource(e)):=V(1,TB(e))
term-body.BoundedIterate=TB(BoundedIterate(source,initial,body)):=V(13,R{0:IS(source),1:TB(initial),2:TB(body)})
term-body.Conditional=TB(Conditional(condition,when-true,when-false)):=V(14,R{0:TB(condition),1:TB(when-true),2:TB(when-false)})
term-ordinal-law=Variable-de-Bruijn-indices-and-record-field,case-branch,projection,and-injection-ordinals-are-u64;record-fields-and-case-branches-are-strictly-increasing
term-structure=finite-acyclic-occurrence-tree;nodes<=4096;root-zero-depth<=48;M(TB(term))-and-M(AlgorithmBody)-also-fit-all-selected-meta-limits
typing-context=Gamma-is-ordered-nearest-binder-first;de-Bruijn-index-zero-is-nearest;Variable(n,T)-requires-n<length(Gamma)-and-T=Gamma[n]
typing-literal=output-is-the-explicit-exact-type-without-schema-shape-or-owner-membership-inspection-of-the-datum;canonical-algorithm-structure-authentication-independently-requires-the-literal-datum-to-be-one-exact-canonical-MetaValueV0-within-constitutional-limits;after-DomainSupport-owner-admission-rechecks-constitutional-limits-and-checks-the-finite-carrier-shape-and-exact-domain-law
typing-let=type(bound,Gamma)=B;type(body,[B]+Gamma)=R;output=R
typing-record=field-ordinals-strictly-increasing;type(e_i,Gamma)=T_i;output=RootRecord[(n_i,T_i)...]
typing-project=type(record,Gamma)=RootRecord[(n_i,T_i)...];n=n_j-for-one-field;output=T_j
typing-inject=sum-type=RootVariant[(n_i,T_i)...];n=n_j;type(payload,Gamma)=T_j;output=sum-type
typing-case=type(scrutinee,Gamma)=RootVariant[(n_i,T_i)...];branch-ordinals-exactly-(n_i);type(branch_i,[T_i]+Gamma)=R-for-one-exact-R;output=R
typing-conditional=type(condition,Gamma)=RootBool;type(when-true,Gamma)=type(when-false,Gamma)=R;output=R
typing-sequence=type(e_i,Gamma)=T;count(e)<=capacity<=16384;admit-schema-RootSeq[T,capacity];output=RootSeq[T,capacity]
typing-sequence-length=type(source,Gamma)=RootSeq[T,capacity];output=RootNat[capacity]
typing-fail=f-resolved-and-admitted;type(payload,Gamma)=f.payload-type;success-type-S-is-explicit;output=S
typing-strict-index=type(source,Gamma)=RootSeq[T,capacity];type(index,Gamma)=RootNat[m]=f.payload-type;f-resolved-and-admitted;output=T
typing-bounded-append=type(source,Gamma)=RootSeq[T,capacity];type(element,Gamma)=T;f.payload-type=RootUnit;f-resolved-and-admitted;output-is-the-exact-source-type
typing-primitive-call=p-resolved-and-owner-typed;argument-types-ordered;resolved-exact-type-rule-derives-output-R;output=R
index-type=IndexType(N):=RootNat[max(0,N-1)];if-N=0-no-index-value-is-produced
continue-break-type=ContinueBreak(S,R):=RootVariant[(0,S),(1,R)]
typing-iterate-sequence=type(source.sequence,Gamma)=RootSeq[T,N];0<=N<=16384;type(initial,Gamma)=S;type(body,[IndexType(N),T,S]+Gamma)=ContinueBreak(S,R);output=ContinueBreak(S,R)
typing-iterate-range=type(source.exclusive-bound,Gamma)=RootNat[N];0<=N<=16384;type(initial,Gamma)=S;type(body,[IndexType(N),IndexType(N),S]+Gamma)=ContinueBreak(S,R);output=ContinueBreak(S,R)
reachable-value-types=every-input,explicit-annotation,literal,failure-payload,primitive-derived-output,subterm-derived-output,and-every-recursively-nested-member-type-in-the-complete-typed-term
typing-and-owner-admission-order=resolve-and-kind-support-all-declarations;derive-all-carrier-types-and-complete-ABI-without-owner-admitting-literals;require-DomainSupport-for-every-reachable-value-type;then-owner-admit-literals-in-canonical-syntax-order
evaluation=strict-deterministic-call-by-value;each-term-entry-is-charged-before-that-node;semantic-failure-immediately-propagates
evaluation-order=every-executed-strict-term-constructor-and-operand-list-is-evaluated-in-canonical-TB-field-order-and-each-S-field-in-source-order;Let-bound-before-body;record-fields-by-ordinal;sequence-elements-left-to-right;primitive-arguments-left-to-right;Project-source-first;Inject-payload-first;SequenceLength-source-first;Fail-payload-first;case-scrutinee-before-only-selected-branch;conditional-condition-before-only-selected-branch;StrictIndex-source-before-index;BoundedAppend-source-before-element;iterator-source-before-initial-before-items-in-source-order
eval.Literal=return-owner-admitted-literal
eval.Variable=return-Gamma[index]
eval.Let=evaluate-bound;prepend-result;evaluate-body
eval.RecordConstruct=evaluate-fields-by-ordinal;construct-R{n:datum...};owner-admit-at-inferred-RootRecord-type
eval.Project=evaluate-record;select-exact-field-datum;owner-admit-at-inferred-field-type
eval.Inject=evaluate-payload;construct-V(case,payload-datum);owner-admit-at-explicit-RootVariant-type
eval.Case=evaluate-scrutinee;owner-admit-selected-payload-at-its-case-type;prepend-payload;evaluate-only-corresponding-branch
eval.Conditional=evaluate-RootBool-condition;evaluate-only-true-branch-for-MT-or-false-branch-for-MF
eval.SequenceConstruct=evaluate-elements-left-to-right;construct-S[datum...];owner-admit-at-RootSeq[T,capacity]
eval.SequenceLength=evaluate-source;return-owner-admitted-N(actual-count)-at-RootNat[capacity]
eval.Fail=evaluate-payload;complete-DomainFailure(f,payload)
eval.StrictIndex=evaluate-source-then-index;if-index>=actual-count-complete-DomainFailure(f,index);otherwise-owner-admit-selected-element-at-T
eval.BoundedAppend=evaluate-source-then-element;if-actual-count>=capacity-complete-DomainFailure(f,RootUnit-value);otherwise-append-and-owner-admit-at-exact-source-type
eval.PrimitiveCall=evaluate-arguments-left-to-right;charge-exact-work-formula-before-denotation;enter-exact-total-denotation;owner-admit-returned-success-or-declared-failure-payload
eval.IterateSequence=evaluate-sequence-then-initial;items-are-(RootNat-index,owner-admitted-element)-in-sequence-order
eval.IterateRange=evaluate-exclusive-bound-n-then-initial;items-are-(RootNat(i),RootNat(i))-for-i=0..n-1
eval.IterateLoop=before-each-item-charge-iteration-item-units;evaluate-body-with-[index,item,state]+Gamma;case-0-owner-admits-next-state-and-continues;case-1-returns-the-exact-Break-value-immediately;exhaustion-returns-owner-admitted-V(0,final-state-datum)
totality=finite-acyclic-typed-syntax+finite-schemas+bounded-sequences+single-bounded-iterator+acyclic-module-closure+supported-total-domain-laws+supported-total-primitives
portable-language-exclusions=no-general-recursion;no-cyclic-calls;no-callbacks;no-dynamic-code;no-ambient-registry;no-I/O;no-clock;no-implicit-randomness;no-reflection;no-unordered-iteration;no-implementation-defined-arithmetic
algorithm-candidate=algorithm-kind:Symbol;ordered-inputs:S[ValueType...];term:CanonicalTerm
algorithm-body=AlgorithmBody(alg):=R{0:Q(alg.algorithm-kind),1:S[VTB(input_i)...],2:TB(alg.term),3:S[PRB(p_i)...]}
algorithm-direct-primitive-field=p_i-is-exactly-direct-primitive-refs-derived-from-term-in-canonical-order;omission,padding,or-reordering-refuses
algorithm-id=ordinary-id(foundation.portable-algorithm,AlgorithmBody(alg));regime-axis-SR
algorithm-derived-ABI=Fn(ordered-inputs,type(term,ordered-inputs),derived-canonical-failure-row)
algorithm-derived-module-roots=direct-module-roots-are-derived-only-and-not-an-authored-or-hashed-summary
algorithm-nonauthority=diagnostic-label,authored-output-manifest,authored-failure-manifest,trace,printer,normalization,and-extensional-equivalence-are-excluded-from-identity-and-cannot-change-portable-authentication-admission-evaluation-or-completion
work-formula-body.Fixed=WB(Fixed(c)):=V(0,N(c))
work-formula-body.SumByteLengths=WB(SumByteLengths(indices,c)):=V(1,R{0:S[N(index)...],1:N(c)})
work-formula.body.MinByteLengthNatural=WB(MinByteLengthNatural(byte-index,natural-index,c)):=V(2,R{0:N(byte-index),1:N(natural-index),2:N(c)})
work-formula-syntax-admission=all-constants-are-naturals;all-positional-indices-are-u64-naturals;SumByteLengths-indices-ascending-numeric-and-unique;fixed-has-no-indices;MinByteLengthNatural-has-exactly-two-indices;unknown-tag-fails-closed-variant-formation-and-is-Malformed;constitutional-body-bounds-apply
work-formula-admitted-for-ABI=FormulaSyntaxAdmissible-and-all-indices-in-the-exact-primitive-ABI-and-SumByteLengths-selected-argument-datums-are-O(x)-or-MinByteLengthNatural-selected-datums-are-O(x)-then-N(n);checked-only-for-rules-keyed-by-exact-direct-primitives;unused-syntax-admissible-rules-grant-no-ABI-applicability
work-formula-semantics=Fixed(c):c;SumByteLengths(indices,c):c+sum_index-in-indices(length(argument[index].datum.octets));MinByteLengthNatural(byte-index,natural-index,c):c+min(length(argument[byte-index].datum.octets),argument[natural-index].datum.natural)
evaluation-contract-version=0
evaluation-contract-body=ContractBody(C):=R{0:N(0),1:N(C.term-entry-units),2:N(C.iteration-item-units),3:Q(portable-evaluation-precedence-v0),4:Q(tagged-canonical-completion-v0),5:Q(maximum-completion-schema-v0),6:S[R{0:O(CR(primitive-id)),1:WB(formula)}...]}
evaluation-contract-rule-order=primitive-ids-have-kind-foundation.semantic-primitive-and-regime-SR;rules-ascending-full-CR-bytes;no-duplicate-key
evaluation-contract-id=ordinary-id(foundation.evaluation-contract,ContractBody(C));regime-axis-SR
evaluation-contract-closure=every-direct-primitive-has-exactly-one-ABI-compatible-rule-and-evaluator-support;unused-rules-are-allowed-and-do-not-enlarge-module-closure
evaluation-contract-boundary=contract-controls-only-charges,validation-precedence,completion-encoding,and-static-completion-preflight;it-does-not-change-term-typing,evaluation-order,primitive-denotation,semantic-failure,or-algorithm-identity
evaluation-request=finite-limits+complete-prior-meta-basis+asserted-contract-id-and-exact-contract-body+asserted-portable-algorithm-id-and-exact-algorithm-body+exact-module-preimage-bundle+ordered-input-headers-and-canonical-payload-bytes
evaluation-request-snapshot=evaluation-consumes-one-immutable-admitted-request-snapshot;module-and-input-material-is-captured-exactly-once-at-its-respective-validation-boundary;all-later-semantic-steps-use-only-the-captured-material-and-never-reread-a-mutable-producer-or-source;capture-preserves-validation-precedence-and-cannot-observe-a-later-boundary-early;concrete-host-carriers-are-not-portable-semantic-root-law
evaluation-limits=maximum-term-units,maximum-iteration-units,maximum-primitive-work,maximum-completion-bytes;each-is-a-finite-mathematical-natural;request-local-and-not-content-addressed
evaluation-charge=term-units,iteration-units,primitive-work,completion-bytes;each-is-a-mathematical-natural;completion-bytes-is-zero-until-one-complete-envelope-exists
charge-term=on-entry-to-each-term-node-add-C.term-entry-units-before-node-work
charge-iteration=before-each-executed-iterator-item-add-C.iteration-item-units-before-body-work
charge-primitive=after-arguments-and-before-denotation-add-the-exact-formula-result
charge-atomicity=precheck-combined-next-counter-values-against-request-limits;commit-all-or-none-before-associated-work;equal-to-limit-is-allowed
precedence.01=validate-all-request-limit-fields-as-finite-mathematical-naturals
precedence.02=authenticate-and-establish-support-for-the-complete-exact-prior-meta-basis
precedence.03=validate-contract-typed-header;strictly-decode-exact-body;authenticate-asserted-id;validate-version,closed-formula-syntax,canonical-rule-order,and-same-regime-refs;establish-support-for-that-exact-contract
precedence.04=validate-subject-outer-typed-header-and-require-foundation.portable-algorithm
precedence.05=strictly-decode-canonical-algorithm-structure,reject-every-over-u64-Variable-index-or-other-structural-ordinal,and-authenticate-asserted-id-without-declaration-resolution-or-owner-typing
precedence.06=derive-direct-references;authenticate-the-exact-required-module-closure;resolve-the-complete-explicit-declaration-coordinate-set-for-owner,kind,regime,and-exact-local-position;begin-no-kind-specific-body-interpretation-until-all-coordinates-resolve
precedence.07=establish-supported-kind-specific-interpretation-for-every-resolved-body;derive-carrier-types-and-complete-ABI-without-owner-admitting-literals;check-exact-direct-primitive-field;compute-all-reachable-value-types;require-DomainSupport-for-all;owner-admit-all-literals-in-canonical-syntax-order
precedence.08=validate-input-arity,carrier-shape,and-exact-ValueType-for-all-headers-in-argument-order-without-decoding-any-input-payload
precedence.09=strictly-decode-and-owner-admit-input-payloads-in-argument-order
precedence.10=establish-evaluator-support-for-every-exact-direct-primitive-and-require-one-exact-ABI-compatible-work-formula-per-direct-primitive
precedence.11=derive-and-preflight-the-full-maximum-tagged-completion-schema-and-byte-size-before-first-term-entry
precedence.12=enter-semantic-evaluation
precedence-barrier=failure-at-an-earlier-boundary-forbids-later-semantic-inspection;missing-or-invalid-owner-declaration-precedes-unsupported-domain;unsupported-reachable-domain-precedes-input-arity,header,and-payload-defects;all-input-headers-precede-any-input-payload-decode
completion-bytes.Success=CompletionBytes(Success(v)):=M(V(0,v.datum))
completion-bytes.Failure=CompletionBytes(DomainFailure(failures[i],p)):=M(V(i+1,p.datum))
completion-maximum=MaximumCompletionSize:=17+max({MaxDatumBytes(success)}-union-{MaxDatumBytes(f.payload-type)-for-f-in-failures})
completion-schema=RootVariant([(0,success)]-concatenated-with-[(i+1,failures[i].payload-type)-for-0<=i<length(failures)])-shape;its-schema-structure-and-Worst-measure-must-be-admitted-and-MaximumCompletionSize<=1048576
completion-envelope-nonauthority=the-derived-tagged-variant-is-only-the-exact-ABI-envelope-for-one-derived-function-type;it-is-not-a-universal-Foundation-result-type
completion-preflight=MaximumCompletionSize-is-checked-against-maximum-completion-bytes-before-first-term-entry;actual-complete-envelope-size-is-charged-on-completion;equal-to-limit-is-allowed
operational-noncompletion=unsupported,missing-dependency,cannot-answer,kind-mismatch,malformed,refused,deterministic-limit-exhaustion,and-checker-or-conformance-failure-are-distinct-from-Success-and-DomainFailure
operational-outcome-partition=Unsupported,MissingDependency,CannotAnswer,KindMismatch,Malformed,Refused,DeterministicLimitExceeded,and-CheckerFailure-are-pairwise-distinct;MissingDependency-means-a-required-exact-named-preimage-is-absent-after-typed-coordinate-formation;CannotAnswer-means-an-exact-supported-and-structurally-formed-operation-cannot-obtain-a-required-semantic-premise,live-read,or-authority-needed-to-answer-and-is-neither-a-missing-named-durable-preimage-nor-a-negative-semantic-conclusion;KindMismatch-means-an-exact-formed-typed-subject,reference,or-header-names-the-wrong-namespace,kind,regime,arity,or-exact-ABI-coordinate-under-the-authenticated-basis;Unsupported-means-an-exact-same-kind-and-same-regime-authenticated-basis,subject,or-request-pair-lacks-evaluator-selected-interpretation-or-coverage,including-an-absent-primitive-provider-or-cost-rule;Malformed-means-an-invalid-carrier,forbidden-subclass,noncanonical-bytes,failed-asserted-ID-and-body-authentication,or-failed-structural-formation-before-a-closed-semantic-predicate-is-defined;Refused-means-an-authenticated-structurally-formed-candidate-reached-and-failed-a-supported-closed-resolution,typing,owner-admission,or-compatibility-predicate,including-a-present-work-rule-incompatible-with-the-exact-call-ABI;DeterministicLimitExceeded-means-a-declared-finite-request,closure,or-evaluation-bound-is-exhausted-before-the-associated-work-and-produces-no-semantic-completion;CheckerFailure-means-an-evaluator-advertised-or-selected-support-entry,derived-ABI,provider-postcondition,or-request-local-typed-ID-binding-is-internally-inconsistent;strict-input-decode-failure-is-Malformed-and-post-decode-owner-admission-failure-is-Refused
host-failure=process-death,unrecordable-allocation-failure,or-unavailable-device-may-produce-no-record-and-is-never-a-semantic-completion
nonclaims=no-universal-result-type-or-resource-or-judgment;no-security-property;no-distribution-property;no-constant-time-property;no-provider-conformance;no-unconditional-hash-binding-or-collision-resistance;no-protocol-relation-analysis-compiler-or-endpoint-admission
"""
SEMANTIC_ROOT_PRIMITIVE_EXTENSIONS = DatumSeq(())
SEMANTIC_REGIME_DESCRIPTOR = DatumRecord(
    (
        (0, Symbol("zkc.foundation.portable-semantics.v0")),
        (1, Nat(0)),
        (
            2,
            DatumRecord(
                (
                    (0, SEMANTIC_CORE_NAMES),
                    (1, BytesValue(SEMANTIC_CORE_LAW_SOURCE)),
                )
            ),
        ),
        (3, SEMANTIC_ROOT_PRIMITIVE_EXTENSIONS),
        (4, Symbol("local-ordinals-and-closed-scc-v0")),
        (5, Symbol("language-profiles-and-extension-modules-same-root-dag-v0")),
    )
)
SEMANTIC_REGIME_ID = meta_object_id(
    SEMANTIC_REGIME_KIND,
    encode_datum(SEMANTIC_REGIME_DESCRIPTOR),
)
FOUNDATION_PRIOR_META_PREIMAGES = PriorMetaPreimageBundle(
    encode_datum(IDENTITY_PROFILE_DESCRIPTOR),
    encode_datum(HASH_SUITE_DESCRIPTOR),
    encode_datum(SEMANTIC_REGIME_DESCRIPTOR),
)


def _root_value_type_descriptor(root_ordinal: int, schema: Datum) -> DatumRecord:
    return DatumRecord(
        (
            (
                0,
                DatumVariant(
                    1,
                    DatumVariant(
                        0,
                        DatumRecord(
                            (
                                (
                                    0,
                                    BytesValue(SEMANTIC_REGIME_ID.internal_reference()),
                                ),
                                (1, Symbol("foundation.root-value-domain")),
                                (2, Nat(root_ordinal)),
                            )
                        ),
                    ),
                ),
            ),
            (1, schema),
        )
    )


FIXTURE_FAILURE_CATALOG = DatumSeq(
    (
        DatumRecord(
            (
                (0, Symbol("zero-divisor")),
                (1, _root_value_type_descriptor(0, DatumVariant(0, UNIT))),
            )
        ),
        DatumRecord(
            (
                (0, Symbol("index-out-of-range")),
                (
                    1,
                    _root_value_type_descriptor(
                        2,
                        DatumVariant(2, Nat((1 << 64) - 1)),
                    ),
                ),
            )
        ),
        DatumRecord(
            (
                (0, Symbol("sequence-capacity")),
                (1, _root_value_type_descriptor(0, DatumVariant(0, UNIT))),
            )
        ),
        DatumRecord(
            (
                (0, Symbol("sampling-exhausted")),
                (1, _root_value_type_descriptor(2, DatumVariant(2, Nat(15)))),
            )
        ),
    )
)
FIXTURE_EXTENSION_LOCAL_DECLARATIONS = DatumSeq(
    (
        DatumRecord(
            (
                (0, Symbol("semantic-failure")),
                (1, FIXTURE_FAILURE_CATALOG),
            )
        ),
        DatumRecord(
            (
                (0, Symbol("semantic-primitive")),
                (1, primitive_catalog_datum()),
            )
        ),
    )
)
# This descriptor is exactly SemanticModuleCandidate.body() for the fixture
# module.  Keeping a second, version-shaped descriptor here would create an ID
# that no candidate could authenticate.
FIXTURE_EXTENSION_MODULE_DESCRIPTOR = DatumRecord(
    (
        (0, DatumSeq(())),
        (1, FIXTURE_EXTENSION_LOCAL_DECLARATIONS),
        (2, UNIT),
    )
)
FIXTURE_EXTENSION_MODULE_ID = content_id(
    SEMANTIC_MODULE_KIND,
    encode_datum(FIXTURE_EXTENSION_MODULE_DESCRIPTOR),
    semantic_regime=SEMANTIC_REGIME_ID,
)


def primitive_reference_datum(entry: PrimitiveCatalogEntry) -> DatumVariant:
    ordinal, _, _, _, _, _, _ = entry
    return DatumVariant(
        1,
        DatumRecord(
            (
                (0, BytesValue(FIXTURE_EXTENSION_MODULE_ID.internal_reference())),
                (1, Symbol("semantic-primitive")),
                (2, Nat(ordinal)),
            )
        ),
    )


PRIMITIVE_IDS_BY_KEY: Mapping[tuple[str, int], TypedContentId] = MappingProxyType(
    {
        (entry[1], entry[2]): content_id(
            SEMANTIC_PRIMITIVE_KIND,
            encode_datum(primitive_reference_datum(entry)),
            semantic_regime=SEMANTIC_REGIME_ID,
        )
        for entry in PRIMITIVE_SEMANTIC_CATALOG
    }
)


@dataclass(frozen=True)
class SemanticPrimitiveRef:
    """Exact primitive ID paired with its structurally visible declaration."""

    identifier: TypedContentId
    declaration_module: TypedContentId
    local_ordinal: int

    def __post_init__(self) -> None:
        _require_typed_content_id(
            self.identifier,
            axis_name="primitive identifier",
        )
        _require_typed_content_id(
            self.declaration_module,
            axis_name="primitive declaration owner",
        )
        if not _is_u64_natural(self.local_ordinal):
            raise CanonicalError("primitive declaration ordinal must be a u64 natural")

    def declaration_body(self) -> DatumVariant:
        if type(self) is not SemanticPrimitiveRef:
            raise ModelError("primitive reference has the wrong exact typed shape")
        self.__post_init__()
        return DatumVariant(
            1,
            DatumRecord(
                (
                    (0, BytesValue(self.declaration_module.internal_reference())),
                    (1, Symbol("semantic-primitive")),
                    (2, Nat(self.local_ordinal)),
                )
            ),
        )

    def datum(self) -> DatumRecord:
        if type(self) is not SemanticPrimitiveRef:
            raise ModelError("primitive reference has the wrong exact typed shape")
        self.__post_init__()
        return DatumRecord(
            (
                (0, BytesValue(self.identifier.internal_reference())),
                (1, self.declaration_body()),
            )
        )


def authenticate_primitive_reference(
    reference: SemanticPrimitiveRef,
    *,
    ledger: AuthenticationLedger | None = None,
) -> None:
    if type(reference) is not SemanticPrimitiveRef:
        raise ModelError("primitive reference has the wrong exact typed shape")
    reference.__post_init__()
    if reference.identifier.subject_kind != SEMANTIC_PRIMITIVE_KIND:
        raise DeclarationKindMismatchError(
            "primitive reference has the wrong identifier kind"
        )
    if reference.declaration_module.subject_kind != SEMANTIC_MODULE_KIND:
        raise DeclarationKindMismatchError(
            "primitive declaration owner is not a semantic module"
        )
    if (
        reference.identifier.semantic_regime
        != reference.declaration_module.semantic_regime
    ):
        raise DeclarationKindMismatchError(
            "primitive reference identifier and owner cross semantic regimes"
        )
    authenticate_content_id(
        reference.identifier,
        encode_datum(reference.declaration_body()),
        FOUNDATION_PRIOR_META_PREIMAGES,
        ledger=ledger,
    )


PRIMITIVE_REFS_BY_KEY: Mapping[tuple[str, int], SemanticPrimitiveRef] = (
    MappingProxyType(
        {
            (entry[1], entry[2]): SemanticPrimitiveRef(
                PRIMITIVE_IDS_BY_KEY[(entry[1], entry[2])],
                FIXTURE_EXTENSION_MODULE_ID,
                entry[0],
            )
            for entry in PRIMITIVE_SEMANTIC_CATALOG
        }
    )
)


# ---------------------------------------------------------------------------
# Domain-indexed schemas and canonical semantic values
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class UnitSchema:
    pass


@dataclass(frozen=True)
class BoolSchema:
    pass


@dataclass(frozen=True)
class NatSchema:
    maximum: int


@dataclass(frozen=True)
class IntSchema:
    minimum: int
    maximum: int


@dataclass(frozen=True)
class BytesSchema:
    minimum_length: int
    maximum_length: int


@dataclass(frozen=True)
class SymbolSchema:
    maximum_length: int


@dataclass(frozen=True)
class SeqSchema:
    element: "ValueType"
    maximum_length: int


@dataclass(frozen=True)
class RecordSchema:
    fields: tuple[tuple[int, "ValueType"], ...]


@dataclass(frozen=True)
class VariantSchema:
    cases: tuple[tuple[int, "ValueType"], ...]


Schema: TypeAlias = (
    UnitSchema
    | BoolSchema
    | NatSchema
    | IntSchema
    | BytesSchema
    | SymbolSchema
    | SeqSchema
    | RecordSchema
    | VariantSchema
)


UNIT_SCHEMA = UnitSchema()
BOOL_SCHEMA = BoolSchema()


def maximum_encoded_size(schema: Schema) -> int:
    """Validate a finite schema and its worst canonical-value envelope."""

    schema_nodes = 0
    active: set[int] = set()

    def bounded(
        measure: tuple[int, int, int, int],
    ) -> tuple[int, int, int, int]:
        size, value_nodes, value_edges, value_depth = measure
        if size > MAX_CANONICAL_BYTES:
            raise CanonicalError(
                "schema admits a value beyond the canonical byte bound"
            )
        if value_nodes > MAX_CANONICAL_NODES:
            raise CanonicalError(
                "schema admits a value beyond the canonical node bound"
            )
        if value_edges > MAX_CANONICAL_EDGES:
            raise CanonicalError(
                "schema admits a value beyond the canonical child-edge bound"
            )
        if value_depth > MAX_CANONICAL_DEPTH:
            raise CanonicalError(
                "schema admits a value beyond the canonical depth bound"
            )
        return measure

    def entries(
        values: tuple[tuple[int, "ValueType"], ...], what: str, depth: int
    ) -> tuple[tuple[int, int, int, int], ...]:
        if type(values) is not tuple:
            raise CanonicalError(f"{what} entries must use an immutable tuple")
        if len(values) > MAX_CANONICAL_EDGES:
            raise CanonicalError(f"{what} exceeds the child-edge bound")
        if len(values) > MAX_CANONICAL_NODES - schema_nodes:
            raise CanonicalError(f"{what} exceeds the cumulative schema-node bound")
        previous = -1
        measures: list[tuple[int, int, int, int]] = []
        for entry in values:
            if type(entry) is not tuple or len(entry) != 2:
                raise CanonicalError(
                    f"{what} entries must use immutable ordinal-type pairs"
                )
            ordinal, child = entry
            if type(ordinal) is not int or not 0 <= ordinal < 1 << 64:
                raise CanonicalError(
                    f"{what} ordinals must be unsigned 64-bit naturals"
                )
            if ordinal <= previous:
                raise CanonicalError(f"{what} ordinals must be strictly increasing")
            previous = ordinal
            if type(child) is not ValueType:
                raise CanonicalError(f"{what} children must be exact value types")
            measures.append(visit(child.schema, depth + 1))
        return tuple(measures)

    def visit(current: Schema, depth: int) -> tuple[int, int, int, int]:
        nonlocal schema_nodes
        schema_nodes += 1
        if schema_nodes > MAX_CANONICAL_NODES:
            raise CanonicalError("schema exceeds cumulative node bound")
        if depth > MAX_SCHEMA_DEPTH:
            raise CanonicalError("schema exceeds depth bound")
        marker = id(current)
        if marker in active:
            raise CanonicalError("recursive schema is not finite")
        active.add(marker)
        try:
            if type(current) in (UnitSchema, BoolSchema):
                return 1, 1, 0, 0
            if type(current) is NatSchema:
                if (
                    type(current.maximum) is not int
                    or current.maximum < 0
                    or current.maximum >= 1 << 256
                ):
                    raise CanonicalError("Nat schema bound is outside the profile")
                magnitude = max(1, (current.maximum.bit_length() + 7) // 8)
                return 1 + 8 + magnitude, 1, 0, 0
            if type(current) is IntSchema:
                if type(current.minimum) is not int or type(current.maximum) is not int:
                    raise CanonicalError("Int schema bounds must be integers")
                if current.minimum > current.maximum:
                    raise CanonicalError("Int schema bounds are inverted")
                magnitude_bound = max(abs(current.minimum), abs(current.maximum))
                if magnitude_bound >= 1 << 255:
                    raise CanonicalError("Int schema bound is outside the profile")
                magnitude = max(1, (magnitude_bound.bit_length() + 7) // 8)
                return 1 + 1 + 8 + magnitude, 1, 0, 0
            if type(current) is BytesSchema:
                if (
                    type(current.minimum_length) is not int
                    or type(current.maximum_length) is not int
                    or not 0
                    <= current.minimum_length
                    <= current.maximum_length
                    <= MAX_CANONICAL_BYTES
                ):
                    raise CanonicalError("Bytes schema bounds are invalid")
                return bounded((1 + 8 + current.maximum_length, 1, 0, 0))
            if type(current) is SymbolSchema:
                if (
                    type(current.maximum_length) is not int
                    or not 1 <= current.maximum_length <= 4096
                ):
                    raise CanonicalError("Symbol schema bound is invalid")
                return 1 + 8 + current.maximum_length, 1, 0, 0
            if type(current) is SeqSchema:
                if (
                    type(current.maximum_length) is not int
                    or not 0 <= current.maximum_length <= MAX_CANONICAL_NODES
                ):
                    raise CanonicalError("sequence schema bound is invalid")
                if type(current.element) is not ValueType:
                    raise CanonicalError(
                        "sequence schema element must be an exact value type"
                    )
                child_size, child_nodes, child_edges, child_depth = visit(
                    current.element.schema, depth + 1
                )
                maximum = current.maximum_length
                return bounded(
                    (
                        1 + 8 + maximum * (8 + child_size),
                        1 + maximum * child_nodes,
                        maximum * (1 + child_edges),
                        0 if maximum == 0 else 1 + child_depth,
                    )
                )
            if type(current) is RecordSchema:
                children = entries(current.fields, "record schema", depth)
                return bounded(
                    (
                        1 + 8 + sum(16 + item[0] for item in children),
                        1 + sum(item[1] for item in children),
                        len(children) + sum(item[2] for item in children),
                        0 if not children else 1 + max(item[3] for item in children),
                    )
                )
            if type(current) is VariantSchema:
                children = entries(current.cases, "variant schema", depth)
                if not children:
                    raise CanonicalError("variant schema must have at least one case")
                return bounded(
                    (
                        1 + 8 + 8 + max(item[0] for item in children),
                        1 + max(item[1] for item in children),
                        1 + max(item[2] for item in children),
                        1 + max(item[3] for item in children),
                    )
                )
            raise CanonicalError(f"unsupported schema: {type(current)!r}")
        finally:
            active.remove(marker)

    return visit(schema, 0)[0]


def validate_schema(schema: Schema) -> None:
    maximum_encoded_size(schema)


def schema_datum(schema: Schema) -> Datum:
    validate_schema(schema)
    if type(schema) is UnitSchema:
        return DatumVariant(0, UNIT)
    if type(schema) is BoolSchema:
        return DatumVariant(1, UNIT)
    if type(schema) is NatSchema:
        return DatumVariant(2, Nat(schema.maximum))
    if type(schema) is IntSchema:
        return DatumVariant(
            3,
            DatumRecord(((0, IntValue(schema.minimum)), (1, IntValue(schema.maximum)))),
        )
    if type(schema) is BytesSchema:
        return DatumVariant(
            4,
            DatumRecord(
                (
                    (0, Nat(schema.minimum_length)),
                    (1, Nat(schema.maximum_length)),
                )
            ),
        )
    if type(schema) is SymbolSchema:
        return DatumVariant(5, Nat(schema.maximum_length))
    if type(schema) is SeqSchema:
        return DatumVariant(
            6,
            DatumRecord(
                (
                    (0, value_type_datum(schema.element)),
                    (1, Nat(schema.maximum_length)),
                )
            ),
        )
    if type(schema) is RecordSchema:
        return DatumVariant(
            7,
            DatumSeq(
                tuple(
                    DatumRecord(((0, Nat(ordinal)), (1, value_type_datum(child))))
                    for ordinal, child in schema.fields
                )
            ),
        )
    if type(schema) is VariantSchema:
        return DatumVariant(
            8,
            DatumSeq(
                tuple(
                    DatumRecord(((0, Nat(ordinal)), (1, value_type_datum(child))))
                    for ordinal, child in schema.cases
                )
            ),
        )
    raise AssertionError("unreachable schema")


@dataclass(frozen=True)
class ValueDomain:
    """Exact root- or module-qualified value-domain declaration reference."""

    owner: PriorMetaId | TypedContentId
    declaration_kind: Symbol
    local_ordinal: int

    def __post_init__(self) -> None:
        if type(self.declaration_kind) is not Symbol:
            raise CanonicalError(
                "value-domain declaration kind must be an exact symbol"
            )
        encode_datum(self.declaration_kind)
        if not _is_u64_natural(self.local_ordinal):
            raise CanonicalError(
                "value-domain declaration ordinal must be a u64 natural"
            )
        if type(self.owner) is PriorMetaId:
            self.owner.__post_init__()
        elif type(self.owner) is TypedContentId:
            self.owner.__post_init__()
        else:
            raise CanonicalError(
                "value domain owner must be a regime root or semantic module"
            )

    @property
    def semantic_regime(self) -> PriorMetaId:
        if type(self.owner) is PriorMetaId:
            return self.owner
        return self.owner.semantic_regime

    def datum(self) -> DatumVariant:
        if type(self) is not ValueDomain:
            raise CanonicalError("value domain has the wrong exact typed shape")
        self.__post_init__()
        owner_case = 0 if type(self.owner) is PriorMetaId else 1
        return DatumVariant(
            owner_case,
            DatumRecord(
                (
                    (0, BytesValue(self.owner.internal_reference())),
                    (1, self.declaration_kind),
                    (2, Nat(self.local_ordinal)),
                )
            ),
        )


def value_type_datum(value_type: "ValueType") -> Datum:
    if type(value_type) is not ValueType:
        raise CanonicalError("value type has the wrong exact typed shape")
    if type(value_type.domain) is not ValueDomain:
        raise CanonicalError("value type domain has the wrong exact typed shape")
    return DatumRecord(
        (
            (0, value_type.domain.datum()),
            (1, schema_datum(value_type.schema)),
        )
    )


@dataclass(frozen=True)
class ValueType:
    domain: ValueDomain
    schema: Schema

    def __post_init__(self) -> None:
        if type(self.domain) is not ValueDomain:
            raise CanonicalError("value type must carry an exact value domain")
        self.domain.__post_init__()
        validate_schema(self.schema)
        encode_datum(value_type_datum(self))


def declaration_schema_datum(
    schema: Schema,
    declaring_module: TypedContentId | None,
) -> Datum:
    """Encode a schema inside one module's declaration-local type grammar."""

    validate_schema(schema)
    if type(schema) in (
        UnitSchema,
        BoolSchema,
        NatSchema,
        IntSchema,
        BytesSchema,
        SymbolSchema,
    ):
        return schema_datum(schema)
    if type(schema) is SeqSchema:
        return DatumVariant(
            6,
            DatumRecord(
                (
                    (
                        0,
                        declaration_value_type_datum(
                            schema.element,
                            declaring_module,
                        ),
                    ),
                    (1, Nat(schema.maximum_length)),
                )
            ),
        )
    if type(schema) is RecordSchema:
        return DatumVariant(
            7,
            DatumSeq(
                tuple(
                    DatumRecord(
                        (
                            (0, Nat(ordinal)),
                            (
                                1,
                                declaration_value_type_datum(
                                    child,
                                    declaring_module,
                                ),
                            ),
                        )
                    )
                    for ordinal, child in schema.fields
                )
            ),
        )
    if type(schema) is VariantSchema:
        return DatumVariant(
            8,
            DatumSeq(
                tuple(
                    DatumRecord(
                        (
                            (0, Nat(ordinal)),
                            (
                                1,
                                declaration_value_type_datum(
                                    child,
                                    declaring_module,
                                ),
                            ),
                        )
                    )
                    for ordinal, child in schema.cases
                )
            ),
        )
    raise CanonicalError("unsupported declaration-local schema")


def declaration_value_type_datum(
    value_type: ValueType,
    declaring_module: TypedContentId | None = None,
) -> DatumRecord:
    """Encode one localizable ValueType inside a declaration body.

    Same-aggregate module references use a context-local ordinal. Root and
    imported-module references remain exact durable declaration references.
    """

    if type(value_type) is not ValueType:
        raise CanonicalError("declaration-local type must be an exact value type")
    domain = value_type.domain
    if type(domain.owner) is TypedContentId and domain.owner == declaring_module:
        domain_body: Datum = DatumVariant(
            0,
            DatumRecord(
                (
                    (0, domain.declaration_kind),
                    (1, Nat(domain.local_ordinal)),
                )
            ),
        )
    else:
        domain_body = DatumVariant(1, domain.datum())
    return DatumRecord(
        (
            (0, domain_body),
            (1, declaration_schema_datum(value_type.schema, declaring_module)),
        )
    )


@dataclass(frozen=True)
class CanonicalValue:
    value_type: ValueType
    datum: Datum

    def bytes(self) -> bytes:
        return encode_datum(self.datum)


ROOT_VALUE_DOMAIN_KIND = Symbol("foundation.root-value-domain")
UNIT_DOMAIN = ValueDomain(SEMANTIC_REGIME_ID, ROOT_VALUE_DOMAIN_KIND, 0)
BOOL_DOMAIN = ValueDomain(SEMANTIC_REGIME_ID, ROOT_VALUE_DOMAIN_KIND, 1)
NAT_DOMAIN = ValueDomain(SEMANTIC_REGIME_ID, ROOT_VALUE_DOMAIN_KIND, 2)
INT_DOMAIN = ValueDomain(SEMANTIC_REGIME_ID, ROOT_VALUE_DOMAIN_KIND, 3)
BYTES_DOMAIN = ValueDomain(SEMANTIC_REGIME_ID, ROOT_VALUE_DOMAIN_KIND, 4)
SYMBOL_DOMAIN = ValueDomain(SEMANTIC_REGIME_ID, ROOT_VALUE_DOMAIN_KIND, 5)
SEQUENCE_DOMAIN = ValueDomain(SEMANTIC_REGIME_ID, ROOT_VALUE_DOMAIN_KIND, 6)
RECORD_DOMAIN = ValueDomain(SEMANTIC_REGIME_ID, ROOT_VALUE_DOMAIN_KIND, 7)
VARIANT_DOMAIN = ValueDomain(SEMANTIC_REGIME_ID, ROOT_VALUE_DOMAIN_KIND, 8)

ROOT_VALUE_SCHEMA_CLASSES: Mapping[int, type[Schema]] = MappingProxyType(
    {
        0: UnitSchema,
        1: BoolSchema,
        2: NatSchema,
        3: IntSchema,
        4: BytesSchema,
        5: SymbolSchema,
        6: SeqSchema,
        7: RecordSchema,
        8: VariantSchema,
    }
)

MODULE_VALUE_DOMAIN_KIND = Symbol("value-domain")


def authenticate_module_value_domain_declaration(
    candidate: SemanticModuleCandidate,
    declaration_kind: Symbol,
    local_ordinal: int,
) -> DatumRecord:
    """Admit the exact selected opaque module value-domain declaration."""

    if declaration_kind != MODULE_VALUE_DOMAIN_KIND:
        raise DeclarationKindMismatchError(
            "extension value domain has the wrong declaration kind"
        )
    body = resolve_module_declaration(
        candidate,
        declaration_kind.value,
        local_ordinal,
    )
    if type(body) is not DatumRecord or tuple(
        ordinal for ordinal, _ in body.fields
    ) != (0,):
        raise ModelError("module value-domain declaration has the wrong shape")
    name = body.fields[0][1]
    if type(name) is not Symbol:
        raise ModelError("module value-domain declaration name is not a symbol")
    return body


def authenticate_module_primitive_declaration_body(
    candidate: SemanticModuleCandidate,
    local_ordinal: int,
    modules: Mapping[TypedContentId, SemanticModuleCandidate],
    *,
    semantic_regime: PriorMetaId,
) -> DatumRecord:
    """Form one recognized semantic-primitive body before support lookup."""

    body = resolve_module_declaration(
        candidate,
        "semantic-primitive",
        local_ordinal,
    )
    fields = _declaration_record_fields(
        body,
        (0, 1, 2, 3, 4, 5),
        "semantic primitive declaration",
    )
    if (
        type(fields[0]) is not Symbol
        or type(fields[1]) is not Nat
        or not _is_u64_natural(fields[1].value)
        or type(fields[2]) is not BytesValue
        or type(fields[3]) is not BytesValue
        or type(fields[4]) is not DatumSeq
        or type(fields[5]) is not Symbol
    ):
        raise ModelError("semantic primitive declaration has wrong field types")
    failure_coordinates: list[tuple[Symbol, int]] = []
    for failure_ref in fields[4].values:
        failure_fields = _declaration_record_fields(
            failure_ref,
            (0, 1),
            "semantic primitive failure reference",
        )
        if type(failure_fields[0]) is not Symbol:
            raise ModelError(
                "semantic primitive failure reference kind is not a symbol"
            )
        if type(failure_fields[1]) is not Nat or not _is_u64_natural(
            failure_fields[1].value
        ):
            raise ModelError(
                "semantic primitive failure reference ordinal is malformed"
            )
        failure_coordinates.append((failure_fields[0], failure_fields[1].value))

    if any(kind != Symbol("semantic-failure") for kind, _ in failure_coordinates):
        raise DeclarationKindMismatchError(
            "semantic primitive failure reference has the wrong declaration kind"
        )

    failure_bodies = tuple(
        resolve_module_declaration(
            candidate,
            "semantic-failure",
            ordinal,
        )
        for _, ordinal in failure_coordinates
    )
    formed_payload_types: list[_DeclarationValueTypePlan] = []
    for failure_body in failure_bodies:
        declared_failure_fields = _declaration_record_fields(
            failure_body,
            (0, 1),
            "semantic failure declaration",
        )
        if type(declared_failure_fields[0]) is not Symbol:
            raise ModelError("semantic failure declaration name is not a symbol")
        formed_payload_types.append(
            _form_declaration_value_type_datum(declared_failure_fields[1])
        )
    _lift_declaration_value_type_plans(
        tuple(formed_payload_types),
        candidate.identity,
        modules,
        semantic_regime=semantic_regime,
    )
    return body


def _declaration_record_fields(
    datum: Datum,
    ordinals: tuple[int, ...],
    what: str,
) -> Mapping[int, Datum]:
    if (
        type(datum) is not DatumRecord
        or tuple(ordinal for ordinal, _ in datum.fields) != ordinals
    ):
        raise ModelError(f"{what} has the wrong exact record shape")
    return dict(datum.fields)


@dataclass(frozen=True)
class _DeclarationDomainPlan:
    """A structurally formed, but not yet context-resolved, domain coordinate."""

    case: int
    kind: Symbol
    ordinal: int
    owner_bytes: bytes | None = None


@dataclass(frozen=True)
class _DeclarationSchemaPlan:
    """One structurally formed node in a declaration-local schema tree."""

    case: int
    payload: object = None


@dataclass(frozen=True)
class _DeclarationValueTypePlan:
    """The context-free formation result for one declaration-local type."""

    domain: _DeclarationDomainPlan
    schema: _DeclarationSchemaPlan


def _form_prior_meta_reference_carrier(data: bytes, what: str) -> None:
    """Form one exact PriorMetaId carrier without selecting its slot kind."""

    try:
        decode_prior_meta_reference(data)
    except CanonicalError as error:
        raise ModelError(f"{what} reference is malformed: {error}") from error


def _form_content_reference_carrier(data: bytes, what: str) -> None:
    """Form one exact TypedContentId carrier before slot-specific routing."""

    try:
        decode_content_reference(data)
    except CanonicalError as error:
        raise ModelError(f"{what} reference is malformed: {error}") from error


def _form_declaration_value_type_datum(
    body: Datum,
) -> _DeclarationValueTypePlan:
    """Strictly form a complete DVTB tree without consulting owner context."""

    try:
        encode_datum(body)
    except CanonicalError as error:
        raise ModelError(
            f"declaration-local value type body is not canonical: {error}"
        ) from error

    formed_nodes = 0
    formed_edges = 0
    active: set[int] = set()

    def reserve_node(current: Datum, depth: int) -> int:
        nonlocal formed_nodes
        if depth > MAX_CANONICAL_DEPTH:
            raise ModelError(
                "declaration-local type exceeds the structural depth bound"
            )
        formed_nodes += 1
        if formed_nodes > MAX_CANONICAL_NODES:
            raise ModelError("declaration-local type exceeds the structural node bound")
        marker = id(current)
        if marker in active:
            raise ModelError("declaration-local type is recursively cyclic")
        active.add(marker)
        return marker

    def reserve_edges(count: int) -> None:
        nonlocal formed_edges
        formed_edges += count
        if formed_edges > MAX_CANONICAL_EDGES:
            raise ModelError("declaration-local type exceeds the structural edge bound")

    def form_type(current: Datum, depth: int) -> _DeclarationValueTypePlan:
        marker = reserve_node(current, depth)
        try:
            fields = _declaration_record_fields(
                current,
                (0, 1),
                "declaration-local value type",
            )
            reference = fields[0]
            if type(reference) is not DatumVariant:
                raise ModelError("declaration-local domain reference is not tagged")
            if reference.case == 0:
                local = _declaration_record_fields(
                    reference.payload,
                    (0, 1),
                    "local declaration reference",
                )
                kind = local[0]
                ordinal = local[1]
                if type(kind) is not Symbol or type(ordinal) is not Nat:
                    raise ModelError(
                        "local declaration reference has wrong field types"
                    )
                if not _is_u64_natural(ordinal.value):
                    raise ModelError("local declaration ordinal is not a u64 natural")
                domain = _DeclarationDomainPlan(0, kind, ordinal.value)
            elif reference.case == 1:
                durable = reference.payload
                if type(durable) is not DatumVariant:
                    raise ModelError("durable declaration reference is not tagged")
                if durable.case not in (0, 1):
                    raise ModelError("durable declaration reference has an unknown tag")
                durable_fields = _declaration_record_fields(
                    durable.payload,
                    (0, 1, 2),
                    "durable declaration reference",
                )
                owner_bytes = durable_fields[0]
                kind = durable_fields[1]
                ordinal = durable_fields[2]
                if (
                    type(owner_bytes) is not BytesValue
                    or type(kind) is not Symbol
                    or type(ordinal) is not Nat
                    or not _is_u64_natural(ordinal.value)
                ):
                    raise ModelError(
                        "durable declaration reference has wrong field types"
                    )
                if durable.case == 0:
                    _form_prior_meta_reference_carrier(
                        owner_bytes.value,
                        "durable root declaration",
                    )
                    domain_case = 1
                else:
                    _form_content_reference_carrier(
                        owner_bytes.value,
                        "durable module declaration",
                    )
                    domain_case = 2
                domain = _DeclarationDomainPlan(
                    domain_case,
                    kind,
                    ordinal.value,
                    owner_bytes.value,
                )
            else:
                raise ModelError(
                    "declaration-local domain reference has an unknown tag"
                )
            return _DeclarationValueTypePlan(
                domain,
                form_schema(fields[1], depth + 1),
            )
        finally:
            active.remove(marker)

    def form_entries(
        payload: Datum,
        what: str,
        depth: int,
    ) -> tuple[tuple[int, _DeclarationValueTypePlan], ...]:
        if type(payload) is not DatumSeq:
            raise ModelError(f"{what} entries are not a sequence")
        reserve_edges(len(payload.values))
        entries: list[tuple[int, _DeclarationValueTypePlan]] = []
        previous = -1
        for entry in payload.values:
            fields = _declaration_record_fields(entry, (0, 1), what)
            ordinal = fields[0]
            if type(ordinal) is not Nat or not _is_u64_natural(ordinal.value):
                raise ModelError(f"{what} ordinal is not a u64 natural")
            if ordinal.value <= previous:
                raise ModelError(f"{what} ordinals are not strictly increasing")
            previous = ordinal.value
            entries.append((ordinal.value, form_type(fields[1], depth + 1)))
        return tuple(entries)

    def form_schema(current: Datum, depth: int) -> _DeclarationSchemaPlan:
        if type(current) is not DatumVariant:
            raise ModelError("declaration-local schema is not tagged")
        if current.case == 0:
            if type(current.payload) is not Unit:
                raise ModelError("Unit schema has the wrong payload")
            return _DeclarationSchemaPlan(0)
        if current.case == 1:
            if type(current.payload) is not Unit:
                raise ModelError("Boolean schema has the wrong payload")
            return _DeclarationSchemaPlan(1)
        if current.case == 2:
            if type(current.payload) is not Nat:
                raise ModelError("Nat schema has the wrong payload")
            return _DeclarationSchemaPlan(2, current.payload.value)
        if current.case == 3:
            fields = _declaration_record_fields(current.payload, (0, 1), "Int schema")
            if type(fields[0]) is not IntValue or type(fields[1]) is not IntValue:
                raise ModelError("Int schema bounds have the wrong types")
            return _DeclarationSchemaPlan(
                3,
                (fields[0].value, fields[1].value),
            )
        if current.case == 4:
            fields = _declaration_record_fields(
                current.payload,
                (0, 1),
                "Bytes schema",
            )
            if type(fields[0]) is not Nat or type(fields[1]) is not Nat:
                raise ModelError("Bytes schema bounds have the wrong types")
            return _DeclarationSchemaPlan(
                4,
                (fields[0].value, fields[1].value),
            )
        if current.case == 5:
            if type(current.payload) is not Nat:
                raise ModelError("Symbol schema has the wrong payload")
            return _DeclarationSchemaPlan(5, current.payload.value)
        if current.case == 6:
            fields = _declaration_record_fields(current.payload, (0, 1), "Seq schema")
            if type(fields[1]) is not Nat:
                raise ModelError("Seq schema bound has the wrong type")
            reserve_edges(1)
            return _DeclarationSchemaPlan(
                6,
                (form_type(fields[0], depth + 1), fields[1].value),
            )
        if current.case == 7:
            return _DeclarationSchemaPlan(
                7,
                form_entries(current.payload, "Record schema", depth),
            )
        if current.case == 8:
            return _DeclarationSchemaPlan(
                8,
                form_entries(current.payload, "Variant schema", depth),
            )
        raise ModelError("declaration-local schema has an unknown tag")

    return form_type(body, 0)


def _lift_declaration_value_type_plans(
    plans: tuple[_DeclarationValueTypePlan, ...],
    declaring_module: TypedContentId,
    modules: Mapping[TypedContentId, SemanticModuleCandidate],
    *,
    semantic_regime: PriorMetaId,
) -> tuple[ValueType, ...]:
    """Resolve all coordinates before interpreting any referenced owner body."""

    domains: list[_DeclarationDomainPlan] = []

    def collect(plan: _DeclarationValueTypePlan) -> None:
        domains.append(plan.domain)
        payload = plan.schema.payload
        if plan.schema.case == 6:
            child, _ = payload
            collect(child)
        elif plan.schema.case in (7, 8):
            for _, child in payload:
                collect(child)

    for plan in plans:
        collect(plan)

    decoded_owners: dict[int, PriorMetaId | TypedContentId] = {}

    # First classify every formed coordinate's typed axes.  No owner lookup or
    # body interpretation may make a later KindMismatch unobservable.
    for domain in domains:
        if domain.kind != (
            ROOT_VALUE_DOMAIN_KIND if domain.case == 1 else MODULE_VALUE_DOMAIN_KIND
        ):
            raise DeclarationKindMismatchError(
                "declaration-local domain reference has the wrong declaration kind"
            )
        if domain.case == 0:
            continue
        assert domain.owner_bytes is not None
        try:
            if domain.case == 1:
                owner: PriorMetaId | TypedContentId = decode_prior_meta_reference(
                    domain.owner_bytes
                )
                if owner.subject_kind != SEMANTIC_REGIME_KIND:
                    raise DeclarationKindMismatchError(
                        "root declaration reference has the wrong prior-meta kind"
                    )
                if owner != semantic_regime:
                    raise DeclarationKindMismatchError(
                        "root declaration reference names another regime"
                    )
            else:
                owner = decode_content_reference(domain.owner_bytes)
                if owner.subject_kind != SEMANTIC_MODULE_KIND:
                    raise DeclarationKindMismatchError(
                        "durable declaration reference owner is not a semantic module"
                    )
                if owner.semantic_regime != semantic_regime:
                    raise DeclarationKindMismatchError(
                        "durable declaration reference owner crosses semantic regimes"
                    )
        except CanonicalError as error:
            # The same immutable bytes already formed as an exact ID carrier.
            # A later decode failure is therefore malformed model state, never
            # a slot-specific semantic mismatch.
            raise ModelError(
                f"formed declaration owner failed deterministic re-decode: {error}"
            ) from error
        decoded_owners[id(domain)] = owner

    imported_modules = authenticated_module_import_scope(
        declaring_module,
        modules,
    )

    # Then establish scope for every module coordinate before resolving any
    # exact declaration position.
    for domain in domains:
        if domain.case != 2:
            continue
        target = decoded_owners[id(domain)]
        assert type(target) is TypedContentId
        if target not in modules:
            raise DeclarationAdmissionRefusedError(
                "durable declaration reference owner was not authenticated"
            )
        if target == declaring_module:
            raise DeclarationAdmissionRefusedError(
                "same-module declaration references must use local ordinals"
            )
        if target not in imported_modules:
            raise DeclarationAdmissionRefusedError(
                "durable declaration reference is outside the declaring module's import closure"
            )

    resolved_domains: dict[int, ValueDomain] = {}
    module_coordinates: list[tuple[TypedContentId, SemanticModuleCandidate, int]] = []

    # Resolve the complete finite coordinate set without interpreting any
    # selected value-domain declaration body.
    for domain in domains:
        if domain.case == 1:
            if domain.ordinal not in ROOT_VALUE_SCHEMA_CLASSES:
                raise DeclarationAdmissionRefusedError(
                    "root value-domain ordinal is absent from the selected catalog"
                )
            owner = decoded_owners[id(domain)]
            assert type(owner) is PriorMetaId
            resolved_domains[id(domain)] = ValueDomain(
                owner,
                domain.kind,
                domain.ordinal,
            )
            continue
        if domain.case == 0:
            owner = declaring_module
        else:
            owner = decoded_owners[id(domain)]
            assert type(owner) is TypedContentId
        candidate = modules.get(owner)
        if candidate is None:
            raise ModelError("declaration value-domain owner was not authenticated")
        resolve_module_declaration(
            candidate,
            MODULE_VALUE_DOMAIN_KIND.value,
            domain.ordinal,
        )
        module_coordinates.append((owner, candidate, domain.ordinal))
        resolved_domains[id(domain)] = ValueDomain(
            owner,
            domain.kind,
            domain.ordinal,
        )

    # Only after every coordinate resolves may an owner-specific target body
    # be interpreted.
    seen_module_coordinates: set[tuple[TypedContentId, int]] = set()
    for owner, candidate, ordinal in module_coordinates:
        key = (owner, ordinal)
        if key in seen_module_coordinates:
            continue
        seen_module_coordinates.add(key)
        authenticate_module_value_domain_declaration(
            candidate,
            MODULE_VALUE_DOMAIN_KIND,
            ordinal,
        )

    def build(plan: _DeclarationValueTypePlan) -> ValueType:
        try:
            schema_plan = plan.schema
            if schema_plan.case == 0:
                schema: Schema = UnitSchema()
            elif schema_plan.case == 1:
                schema = BoolSchema()
            elif schema_plan.case == 2:
                schema = NatSchema(schema_plan.payload)
            elif schema_plan.case == 3:
                minimum, maximum = schema_plan.payload
                schema = IntSchema(minimum, maximum)
            elif schema_plan.case == 4:
                minimum, maximum = schema_plan.payload
                schema = BytesSchema(minimum, maximum)
            elif schema_plan.case == 5:
                schema = SymbolSchema(schema_plan.payload)
            elif schema_plan.case == 6:
                child, maximum = schema_plan.payload
                schema = SeqSchema(build(child), maximum)
            elif schema_plan.case == 7:
                schema = RecordSchema(
                    tuple(
                        (ordinal, build(child))
                        for ordinal, child in schema_plan.payload
                    )
                )
            elif schema_plan.case == 8:
                schema = VariantSchema(
                    tuple(
                        (ordinal, build(child))
                        for ordinal, child in schema_plan.payload
                    )
                )
            else:
                raise AssertionError("unreachable declaration schema plan")
            validate_schema(schema)
            return ValueType(resolved_domains[id(plan.domain)], schema)
        except CanonicalError as error:
            if str(error).startswith("canonical datum exceeds "):
                raise DeclarationAdmissionRefusedError(
                    "lifted declaration value type exceeds a constitutional body bound"
                ) from error
            raise DeclarationAdmissionRefusedError(
                f"declaration schema or lifted value type failed admission: {error}"
            ) from error

    lifted = tuple(build(plan) for plan in plans)

    def authenticate_lifted_shape(value_type: ValueType) -> None:
        domain = value_type.domain
        if domain.semantic_regime != semantic_regime:
            raise DeclarationKindMismatchError(
                "lifted declaration value type crosses semantic regimes"
            )
        if type(domain.owner) is PriorMetaId:
            schema_class = ROOT_VALUE_SCHEMA_CLASSES[domain.local_ordinal]
            if type(value_type.schema) is not schema_class:
                raise DeclarationKindMismatchError(
                    "root value-domain ordinal disagrees with the structural schema"
                )
        for child in nested_value_types(value_type):
            authenticate_lifted_shape(child)

    for value_type in lifted:
        authenticate_lifted_shape(value_type)
    return lifted


def lift_declaration_value_type_datum(
    body: Datum,
    declaring_module: TypedContentId,
    modules: Mapping[TypedContentId, SemanticModuleCandidate],
    *,
    semantic_regime: PriorMetaId,
) -> ValueType:
    """Resolve a declaration-local type into its outward durable ValueType."""
    formed = _form_declaration_value_type_datum(body)
    return _lift_declaration_value_type_plans(
        (formed,),
        declaring_module,
        modules,
        semantic_regime=semantic_regime,
    )[0]


def nested_value_types(value_type: ValueType) -> tuple[ValueType, ...]:
    schema = value_type.schema
    if type(schema) is SeqSchema:
        return (schema.element,)
    if type(schema) is RecordSchema:
        return tuple(child for _, child in schema.fields)
    if type(schema) is VariantSchema:
        return tuple(child for _, child in schema.cases)
    return ()


def require_supported_value_type(value_type: ValueType) -> None:
    """Require the K1 evaluator's exact value-domain admission support.

    The bounded reference implements only the nine structural domains owned by
    the regime root.  A module-owned domain is an opaque nominal domain: its
    schema bounds a carrier but cannot establish domain membership.  Such a
    domain therefore remains identity-bearing but unsupported until an exact
    domain implementation is added and authenticated.
    """

    if type(value_type) is not ValueType or type(value_type.domain) is not ValueDomain:
        raise CanonicalError("value type has the wrong exact typed shape")
    domain = value_type.domain
    schema_class = ROOT_VALUE_SCHEMA_CLASSES.get(domain.local_ordinal)
    if (
        domain.owner != SEMANTIC_REGIME_ID
        or domain.declaration_kind != ROOT_VALUE_DOMAIN_KIND
        or schema_class is None
        or type(value_type.schema) is not schema_class
    ):
        raise UnsupportedValueDomainError(
            "value domain has no exact admission implementation in this evaluator"
        )
    for child in nested_value_types(value_type):
        require_supported_value_type(child)


def _matches_schema(schema: Schema, datum: Datum) -> bool:
    if type(schema) is UnitSchema:
        return type(datum) is Unit
    if type(schema) is BoolSchema:
        return type(datum) is bool
    if type(schema) is NatSchema:
        return type(datum) is Nat and 0 <= datum.value <= schema.maximum
    if type(schema) is IntSchema:
        return (
            type(datum) is IntValue and schema.minimum <= datum.value <= schema.maximum
        )
    if type(schema) is BytesSchema:
        return (
            type(datum) is BytesValue
            and schema.minimum_length <= len(datum.value) <= schema.maximum_length
        )
    if type(schema) is SymbolSchema:
        if type(datum) is not Symbol:
            return False
        try:
            size = len(datum.value.encode("ascii"))
        except UnicodeEncodeError:
            return False
        return bool(_SYMBOL_RE.fullmatch(datum.value)) and size <= schema.maximum_length
    if type(schema) is SeqSchema:
        return (
            type(datum) is DatumSeq
            and len(datum.values) <= schema.maximum_length
            and all(
                _matches_schema(schema.element.schema, child) for child in datum.values
            )
        )
    if type(schema) is RecordSchema:
        return (
            type(datum) is DatumRecord
            and tuple(ordinal for ordinal, _ in datum.fields)
            == tuple(ordinal for ordinal, _ in schema.fields)
            and all(
                _matches_schema(child_type.schema, child)
                for (_, child_type), (_, child) in zip(schema.fields, datum.fields)
            )
        )
    if type(schema) is VariantSchema:
        if type(datum) is not DatumVariant:
            return False
        cases = dict(schema.cases)
        return datum.case in cases and _matches_schema(
            cases[datum.case].schema, datum.payload
        )
    return False


def _admit_shaped_value(value_type: ValueType, datum: Datum) -> CanonicalValue:
    if type(value_type) is not ValueType:
        raise CanonicalError("value type has the wrong exact typed shape")
    # Validate the full canonical measure without materializing aggregate
    # bytes.  Actual encoding is reserved for an explicitly metered boundary.
    _encoded_size(datum)
    if not _matches_schema(value_type.schema, datum):
        raise ValueAdmissionRefusedError(
            "datum does not match its declared carrier schema"
        )
    return CanonicalValue(value_type, datum)


def admit_value(value_type: ValueType, datum: Datum) -> CanonicalValue:
    if type(value_type) is not ValueType:
        raise CanonicalError("value type has the wrong exact typed shape")
    require_supported_value_type(value_type)
    return _admit_shaped_value(value_type, datum)


def decode_value(value_type: ValueType, body: bytes) -> CanonicalValue:
    return admit_value(value_type, decode_datum(body))


def canonical_value_equal(left: CanonicalValue, right: CanonicalValue) -> bool:
    """Apply the selected root-domain equality at one exact ValueType."""

    if type(left) is not CanonicalValue or type(right) is not CanonicalValue:
        raise CanonicalError("value equality requires exact canonical-value carriers")
    if (
        type(left.value_type) is not ValueType
        or type(right.value_type) is not ValueType
    ):
        raise CanonicalError("value equality requires exact value-type carriers")
    if left.value_type != right.value_type:
        raise CanonicalError("value equality is defined only at one exact value type")
    admitted_left = admit_value(left.value_type, left.datum)
    admitted_right = admit_value(right.value_type, right.datum)
    return admitted_left.datum == admitted_right.datum


def value_preimage(purpose_kind: str, value: CanonicalValue) -> bytes:
    _axis(purpose_kind)
    if type(value) is not CanonicalValue:
        raise CanonicalError("value identity requires an exact canonical-value carrier")
    admitted = admit_value(value.value_type, value.datum)
    return encode_datum(
        DatumRecord(
            (
                (0, Symbol(purpose_kind)),
                (1, admitted.value_type.domain.datum()),
                (2, schema_datum(admitted.value_type.schema)),
                (3, admitted.datum),
            )
        )
    )


def value_id(purpose_kind: str, value: CanonicalValue) -> TypedContentId:
    return content_id(
        CANONICAL_VALUE_KIND,
        value_preimage(purpose_kind, value),
        semantic_regime=value.value_type.domain.semantic_regime,
    )


# ---------------------------------------------------------------------------
# Closed first-order bounded term calculus
# ---------------------------------------------------------------------------


MAX_TERM_NODES = 4096
MAX_TERM_DEPTH = 48


@dataclass(frozen=True)
class Literal:
    value: CanonicalValue


@dataclass(frozen=True)
class Variable:
    index: int
    value_type: ValueType


@dataclass(frozen=True)
class Let:
    bound: "Term"
    body: "Term"


@dataclass(frozen=True)
class RecordConstruct:
    fields: tuple[tuple[int, "Term"], ...]


@dataclass(frozen=True)
class Project:
    record: "Term"
    ordinal: int


@dataclass(frozen=True)
class Inject:
    case: int
    payload: "Term"
    sum_type: ValueType


@dataclass(frozen=True)
class Case:
    scrutinee: "Term"
    branches: tuple[tuple[int, "Term"], ...]


@dataclass(frozen=True)
class Conditional:
    condition: "Term"
    when_true: "Term"
    when_false: "Term"


@dataclass(frozen=True)
class SequenceConstruct:
    element_type: ValueType
    elements: tuple["Term", ...]
    maximum_length: int


@dataclass(frozen=True)
class SequenceLength:
    source: "Term"


@dataclass(frozen=True)
class SemanticFailureType:
    """One completed, typed failure alternative in a semantic function ABI."""

    declaration_module: TypedContentId
    local_ordinal: int
    payload_type: ValueType

    def __post_init__(self) -> None:
        _require_typed_content_id(
            self.declaration_module,
            axis_name="semantic failure declaration owner",
        )
        if type(self.payload_type) is not ValueType:
            raise ModelError("semantic failure must carry an exact payload type")
        self.payload_type.__post_init__()
        if not _is_u64_natural(self.local_ordinal):
            raise ModelError("failure declaration ordinal must be a u64 natural")


def validate_semantic_failure_type_shape(
    failure_type: SemanticFailureType,
) -> None:
    """Validate typed failure structure without selecting an owner registry."""

    if type(failure_type) is not SemanticFailureType:
        raise ModelError("semantic failure has the wrong typed shape")
    failure_type.__post_init__()
    if type(failure_type.payload_type) is not ValueType:
        raise ModelError("semantic failure must carry an exact payload type")


@dataclass(frozen=True)
class Fail:
    failure_type: SemanticFailureType
    payload: "Term"
    success_type: ValueType


@dataclass(frozen=True)
class StrictIndex:
    source: "Term"
    index: "Term"
    failure_type: SemanticFailureType


@dataclass(frozen=True)
class BoundedAppend:
    source: "Term"
    element: "Term"
    failure_type: SemanticFailureType


@dataclass(frozen=True)
class PrimitiveCall:
    primitive: SemanticPrimitiveRef
    arguments: tuple["Term", ...]


@dataclass(frozen=True)
class SequenceIterationSource:
    sequence: "Term"


@dataclass(frozen=True)
class RangeIterationSource:
    exclusive_bound: "Term"


IterationSource: TypeAlias = SequenceIterationSource | RangeIterationSource


@dataclass(frozen=True)
class BoundedIterate:
    """Indexed state iteration returning Continue(state) or Break(result)."""

    source: IterationSource
    initial_state: "Term"
    body: "Term"


Term: TypeAlias = (
    Literal
    | Variable
    | Let
    | RecordConstruct
    | Project
    | Inject
    | Case
    | Conditional
    | SequenceConstruct
    | SequenceLength
    | Fail
    | StrictIndex
    | BoundedAppend
    | PrimitiveCall
    | BoundedIterate
)


def option_schema(payload: ValueType) -> VariantSchema:
    return VariantSchema(
        (
            (0, ValueType(UNIT_DOMAIN, UNIT_SCHEMA)),
            (1, payload),
        )
    )


class ModelError(ValueError):
    """A term, ABI, or algorithm is not well formed."""


class DeclarationAdmissionRefusedError(ModelError):
    """An authenticated declaration failed a closed owner-resolution predicate."""


class DeclarationKindMismatchError(ModelError):
    """An authenticated declaration coordinate has the wrong kind or type."""


class UnsupportedInterpretationError(ModelError):
    """No exact supported interpretation exists for an authenticated subject."""


class SemanticRegimeMismatchError(ModelError):
    """A formed typed subject names a regime other than the selected basis."""


PrimitiveTypeRule: TypeAlias = Callable[[tuple[ValueType, ...]], ValueType]


@dataclass(frozen=True)
class PrimitiveDeclaration:
    identifier: TypedContentId
    owning_module: TypedContentId
    local_ordinal: int
    name: str
    version: int
    type_rule_source: bytes
    operation_law_source: bytes
    discipline: str
    failures: tuple[SemanticFailureType, ...] = ()

    @property
    def key(self) -> tuple[str, int]:
        return self.name, self.version


def authenticate_primitive_declaration(
    declaration: PrimitiveDeclaration,
    *,
    ledger: AuthenticationLedger | None = None,
) -> None:
    if type(declaration) is not PrimitiveDeclaration:
        raise ModelError("primitive declaration has the wrong exact typed shape")
    if type(declaration.failures) is not tuple:
        raise ModelError("primitive declaration failures must be an immutable tuple")
    if len(declaration.failures) > MAX_CANONICAL_EDGES:
        raise ModelError("primitive declaration failures exceed the edge bound")
    if (
        type(declaration.identifier) is not TypedContentId
        or type(declaration.owning_module) is not TypedContentId
        or not _is_u64_natural(declaration.local_ordinal)
        or type(declaration.name) is not str
        or not _is_u64_natural(declaration.version)
        or type(declaration.type_rule_source) is not bytes
        or type(declaration.operation_law_source) is not bytes
        or type(declaration.discipline) is not str
        or any(type(item) is not SemanticFailureType for item in declaration.failures)
    ):
        raise ModelError("primitive declaration fields have the wrong exact shapes")
    if declaration.identifier.subject_kind != SEMANTIC_PRIMITIVE_KIND:
        raise ModelError("primitive declaration identifier has the wrong subject kind")
    if (
        declaration.identifier.semantic_regime
        != declaration.owning_module.semantic_regime
    ):
        raise ModelError("primitive declaration identifier crosses semantic regimes")
    entry = PRIMITIVE_CATALOG_BY_KEY.get(declaration.key)
    if entry is None:
        raise ModelError("primitive declaration key is absent from its module")
    (
        ordinal,
        _,
        _,
        type_rule_source,
        operation_law_source,
        failure_ordinals,
        discipline,
    ) = entry
    if (
        declaration.owning_module != FIXTURE_EXTENSION_MODULE_ID
        or declaration.local_ordinal != ordinal
        or declaration.type_rule_source != type_rule_source
        or declaration.operation_law_source != operation_law_source
        or declaration.discipline != discipline
        or tuple(item.local_ordinal for item in declaration.failures)
        != failure_ordinals
        or any(
            item.declaration_module != declaration.owning_module
            for item in declaration.failures
        )
    ):
        raise ModelError(
            "runtime primitive declaration disagrees with its authenticated module entry"
        )
    for failure in declaration.failures:
        authenticate_semantic_failure_type(failure)
    authenticate_content_id(
        declaration.identifier,
        encode_datum(primitive_reference_datum(entry)),
        FOUNDATION_PRIOR_META_PREIMAGES,
        ledger=ledger,
    )


def _same_domain(types: Iterable[ValueType]) -> bool:
    values = tuple(types)
    return bool(values) and all(item.domain == values[0].domain for item in values)


def _same_regime(types: Iterable[ValueType]) -> bool:
    values = tuple(types)
    return bool(values) and all(
        item.domain.semantic_regime == values[0].domain.semantic_regime
        for item in values
    )


def _require(condition: bool, detail: str) -> None:
    if not condition:
        raise ModelError(detail)


def _type_sha(inputs: tuple[ValueType, ...]) -> ValueType:
    _require(
        len(inputs) == 1
        and inputs[0].domain == BYTES_DOMAIN
        and isinstance(inputs[0].schema, BytesSchema),
        "sha2-256 expects one root byte value",
    )
    return ValueType(BYTES_DOMAIN, BytesSchema(32, 32))


def _type_concat(inputs: tuple[ValueType, ...]) -> ValueType:
    _require(
        len(inputs) == 2
        and all(item.domain == BYTES_DOMAIN for item in inputs)
        and all(isinstance(item.schema, BytesSchema) for item in inputs)
        and _same_domain(inputs),
        "bytes.concat expects two root byte values",
    )
    left = inputs[0].schema
    right = inputs[1].schema
    assert isinstance(left, BytesSchema) and isinstance(right, BytesSchema)
    return ValueType(
        BYTES_DOMAIN,
        BytesSchema(
            left.minimum_length + right.minimum_length,
            left.maximum_length + right.maximum_length,
        ),
    )


def _type_u64_to_be(inputs: tuple[ValueType, ...]) -> ValueType:
    _require(
        len(inputs) == 1
        and inputs[0].domain == NAT_DOMAIN
        and isinstance(inputs[0].schema, NatSchema)
        and inputs[0].schema.maximum <= (1 << 64) - 1,
        "u64.to-be expects one bounded u64 natural",
    )
    return ValueType(BYTES_DOMAIN, BytesSchema(8, 8))


def _type_first_u64(inputs: tuple[ValueType, ...]) -> ValueType:
    _require(
        len(inputs) == 1
        and inputs[0].domain == BYTES_DOMAIN
        and isinstance(inputs[0].schema, BytesSchema)
        and inputs[0].schema.minimum_length >= 8,
        "bytes.first-u64-be expects at least eight octets",
    )
    return ValueType(NAT_DOMAIN, NatSchema((1 << 64) - 1))


def _type_nat_lt(inputs: tuple[ValueType, ...]) -> ValueType:
    _require(
        len(inputs) == 2
        and all(item.domain == NAT_DOMAIN for item in inputs)
        and all(isinstance(item.schema, NatSchema) for item in inputs)
        and _same_domain(inputs),
        "nat.lt expects two naturals from one domain",
    )
    return ValueType(BOOL_DOMAIN, BOOL_SCHEMA)


def _type_nat_mod(inputs: tuple[ValueType, ...]) -> ValueType:
    _require(
        len(inputs) == 2
        and all(item.domain == NAT_DOMAIN for item in inputs)
        and all(isinstance(item.schema, NatSchema) for item in inputs)
        and _same_domain(inputs),
        "nat.mod-positive expects two naturals from one domain",
    )
    return inputs[0]


def _type_take(inputs: tuple[ValueType, ...]) -> ValueType:
    _require(
        len(inputs) == 2
        and inputs[0].domain == BYTES_DOMAIN
        and inputs[1].domain == NAT_DOMAIN
        and isinstance(inputs[0].schema, BytesSchema)
        and isinstance(inputs[1].schema, NatSchema)
        and _same_regime(inputs),
        "bytes.take expects bytes and a natural from one semantic regime",
    )
    maximum = min(inputs[0].schema.maximum_length, inputs[1].schema.maximum)
    return ValueType(BYTES_DOMAIN, BytesSchema(0, maximum))


def _type_reverse(inputs: tuple[ValueType, ...]) -> ValueType:
    _require(
        len(inputs) == 1
        and inputs[0].domain == BYTES_DOMAIN
        and isinstance(inputs[0].schema, BytesSchema),
        "bytes.reverse expects one root byte value",
    )
    return inputs[0]


def _type_prefix_27(inputs: tuple[ValueType, ...]) -> ValueType:
    _require(
        len(inputs) == 1
        and inputs[0].domain == BYTES_DOMAIN
        and isinstance(inputs[0].schema, BytesSchema)
        and inputs[0].schema.minimum_length == 32
        and inputs[0].schema.maximum_length == 32,
        "fixture.bytes.prefix-27 expects exactly 32 octets",
    )
    return ValueType(BYTES_DOMAIN, BytesSchema(27, 27))


_PRIMITIVE_TYPE_RULE_SUPPORT: Mapping[TypedContentId, PrimitiveTypeRule] = (
    MappingProxyType(
        {
            PRIMITIVE_IDS_BY_KEY[key]: rule
            for key, rule in (
                (("sha2-256", 1), _type_sha),
                (("bytes.concat", 1), _type_concat),
                (("u64.to-be", 1), _type_u64_to_be),
                (("bytes.first-u64-be", 1), _type_first_u64),
                (("nat.lt", 1), _type_nat_lt),
                (("nat.mod-positive", 1), _type_nat_mod),
                (("bytes.take", 1), _type_take),
                (("fixture.bytes.reverse", 1), _type_reverse),
                (("fixture.bytes.prefix-27", 1), _type_prefix_27),
            )
        }
    )
)


def resolve_primitive_type_rule(
    identifier: TypedContentId,
    support: Mapping[TypedContentId, PrimitiveTypeRule] = _PRIMITIVE_TYPE_RULE_SUPPORT,
) -> PrimitiveTypeRule:
    """Resolve evaluator support without treating a host callback as semantics."""

    rule = support.get(identifier)
    if rule is None:
        raise UnsupportedInterpretationError(
            "primitive type-rule implementation is unsupported"
        )
    return rule


ZERO_DIVISOR_FAILURE = SemanticFailureType(
    FIXTURE_EXTENSION_MODULE_ID,
    0,
    ValueType(UNIT_DOMAIN, UNIT_SCHEMA),
)
INDEX_OUT_OF_RANGE_FAILURE = SemanticFailureType(
    FIXTURE_EXTENSION_MODULE_ID,
    1,
    ValueType(NAT_DOMAIN, NatSchema((1 << 64) - 1)),
)
SEQUENCE_CAPACITY_FAILURE = SemanticFailureType(
    FIXTURE_EXTENSION_MODULE_ID,
    2,
    ValueType(UNIT_DOMAIN, UNIT_SCHEMA),
)
SAMPLING_EXHAUSTED_FAILURE = SemanticFailureType(
    FIXTURE_EXTENSION_MODULE_ID,
    3,
    ValueType(NAT_DOMAIN, NatSchema(15)),
)

_FIXTURE_FAILURE_TYPES = (
    ZERO_DIVISOR_FAILURE,
    INDEX_OUT_OF_RANGE_FAILURE,
    SEQUENCE_CAPACITY_FAILURE,
    SAMPLING_EXHAUSTED_FAILURE,
)
FIXTURE_FAILURE_TYPES_BY_ORDINAL: Mapping[int, SemanticFailureType] = MappingProxyType(
    {item.local_ordinal: item for item in _FIXTURE_FAILURE_TYPES}
)


def authenticate_semantic_failure_type(
    failure_type: SemanticFailureType,
    failure_types: tuple[SemanticFailureType, ...] = _FIXTURE_FAILURE_TYPES,
) -> None:
    validate_semantic_failure_type_shape(failure_type)
    if type(failure_types) is not tuple:
        raise ModelError("failure declaration registry has the wrong exact shape")
    if len(failure_types) > MAX_CANONICAL_EDGES:
        raise ModelError("failure declaration registry exceeds the edge bound")
    if any(type(item) is not SemanticFailureType for item in failure_types):
        raise ModelError("failure declaration registry has the wrong item shape")
    if failure_type.declaration_module != FIXTURE_EXTENSION_MODULE_ID:
        raise ModelError("semantic failure declaration module is unresolved")
    expected = next(
        (
            item
            for item in failure_types
            if item.local_ordinal == failure_type.local_ordinal
        ),
        None,
    )
    if expected is None:
        raise ModelError("semantic failure ordinal is absent from its module")
    if failure_type.payload_type != expected.payload_type:
        raise ModelError(
            "semantic failure payload disagrees with its authenticated declaration"
        )


def _primitive_declaration(
    key: tuple[str, int],
    failures: tuple[SemanticFailureType, ...] = (),
) -> PrimitiveDeclaration:
    entry = PRIMITIVE_CATALOG_BY_KEY[key]
    (
        local_ordinal,
        name,
        version,
        type_rule_source,
        operation_law_source,
        _,
        discipline,
    ) = entry
    declaration = PrimitiveDeclaration(
        PRIMITIVE_IDS_BY_KEY[key],
        FIXTURE_EXTENSION_MODULE_ID,
        local_ordinal,
        name,
        version,
        type_rule_source,
        operation_law_source,
        discipline,
        failures,
    )
    authenticate_primitive_declaration(declaration)
    return declaration


_PRIMITIVE_DECLARATION_SET = (
    _primitive_declaration(("sha2-256", 1)),
    _primitive_declaration(("bytes.concat", 1)),
    _primitive_declaration(("u64.to-be", 1)),
    _primitive_declaration(("bytes.first-u64-be", 1)),
    _primitive_declaration(("nat.lt", 1)),
    _primitive_declaration(("nat.mod-positive", 1), (ZERO_DIVISOR_FAILURE,)),
    _primitive_declaration(("bytes.take", 1)),
    # This exact declaration exists only to exercise Supports independently
    # of well-formedness.  The default evaluator intentionally omits it.
    _primitive_declaration(("fixture.bytes.reverse", 1)),
    _primitive_declaration(("fixture.bytes.prefix-27", 1)),
)
PRIMITIVE_DECLARATIONS: Mapping[TypedContentId, PrimitiveDeclaration] = (
    MappingProxyType(
        {
            declaration.identifier: declaration
            for declaration in _PRIMITIVE_DECLARATION_SET
        }
    )
)

PRIMITIVE_DECLARATIONS_BY_KEY: Mapping[tuple[str, int], PrimitiveDeclaration] = (
    MappingProxyType(
        {declaration.key: declaration for declaration in _PRIMITIVE_DECLARATION_SET}
    )
)


def resolve_primitive_declaration(
    reference: SemanticPrimitiveRef,
    declarations: tuple[PrimitiveDeclaration, ...] = _PRIMITIVE_DECLARATION_SET,
    *,
    ledger: AuthenticationLedger | None = None,
) -> PrimitiveDeclaration:
    """Resolve only an exact, authenticated module-local primitive reference."""

    authenticate_primitive_reference(reference, ledger=ledger)
    if ledger is not None:
        supported_module_body = FIXTURE_EXTENSION_MODULE_CANDIDATE.body()
        authenticate_content_id(
            FIXTURE_EXTENSION_MODULE_ID,
            supported_module_body,
            FOUNDATION_PRIOR_META_PREIMAGES,
            ledger=ledger,
        )
    declaration = next(
        (item for item in declarations if item.identifier == reference.identifier),
        None,
    )
    if declaration is None:
        raise ModelError("primitive is not in the semantic registry")
    authenticate_primitive_declaration(declaration, ledger=ledger)
    if (
        declaration.owning_module != reference.declaration_module
        or declaration.local_ordinal != reference.local_ordinal
    ):
        raise ModelError("primitive reference disagrees with the resolved declaration")
    return declaration


@dataclass(frozen=True)
class SemanticFunctionType:
    """Derived portable success and semantic-failure ABI."""

    inputs: tuple[ValueType, ...]
    output: ValueType
    failures: tuple[SemanticFailureType, ...] = ()

    def __post_init__(self) -> None:
        validate_semantic_function_type(self)


@dataclass(frozen=True)
class CanonicalAlgorithm:
    algorithm_kind: Symbol
    inputs: tuple[ValueType, ...]
    term: Term
    semantic_regime: PriorMetaId = SEMANTIC_REGIME_ID
    diagnostic_label: Symbol = Symbol("unlabeled")

    @property
    def function_type(self) -> SemanticFunctionType:
        validate_algorithm_header(self)
        validate_term_structure(self.term)
        inferred = infer_term_type(self.term, self.inputs)
        return SemanticFunctionType(self.inputs, inferred.output, inferred.failures)

    @property
    def identity(self) -> TypedContentId:
        return content_id(
            PORTABLE_ALGORITHM_KIND,
            algorithm_preimage(self),
            semantic_regime=self.semantic_regime,
        )

    @property
    def module_dependencies(self) -> tuple[TypedContentId, ...]:
        validate_algorithm_header(self)
        validate_term_structure(self.term)
        return direct_module_dependencies(self)


@dataclass(frozen=True)
class ExternalOperationContract:
    operation_kind: Symbol
    function_type: SemanticFunctionType
    semantic_regime: PriorMetaId = SEMANTIC_REGIME_ID

    def __post_init__(self) -> None:
        validate_external_operation_contract(self)

    def body(self) -> bytes:
        if type(self) is not ExternalOperationContract:
            raise ModelError("external operation contract has the wrong exact shape")
        validate_external_operation_contract(self)
        return encode_datum(
            DatumRecord(
                (
                    (0, self.operation_kind),
                    (1, function_type_datum(self.function_type)),
                )
            )
        )

    @property
    def identity(self) -> TypedContentId:
        return content_id(
            EXTERNAL_OPERATION_CONTRACT_KIND,
            self.body(),
            semantic_regime=self.semantic_regime,
        )


@dataclass(frozen=True)
class ExternalOperationBinding:
    """A realization choice outside portable operation-contract identity."""

    contract: ExternalOperationContract
    provider: Symbol


def validate_external_operation_binding(binding: ExternalOperationBinding) -> None:
    """Validate the exact nonportable realization carrier without executing it."""

    if type(binding) is not ExternalOperationBinding:
        raise ModelError("external operation binding has the wrong exact shape")
    if type(binding.contract) is not ExternalOperationContract:
        raise ModelError("external operation binding has no exact contract")
    if type(binding.provider) is not Symbol:
        raise ModelError("external operation binding provider is not a symbol")
    binding.contract.__post_init__()
    encode_datum(binding.provider)


Subject: TypeAlias = (
    CanonicalAlgorithm | ExternalOperationContract | ExternalOperationBinding
)


for _failure_ordinal, _failure_type in FIXTURE_FAILURE_TYPES_BY_ORDINAL.items():
    _failure_body = FIXTURE_FAILURE_CATALOG.values[_failure_ordinal]
    if not isinstance(_failure_body, DatumRecord) or dict(_failure_body.fields)[
        1
    ] != declaration_value_type_datum(
        _failure_type.payload_type,
        FIXTURE_EXTENSION_MODULE_ID,
    ):
        raise AssertionError(
            "fixture failure catalog and ValueType serialization disagree"
        )


def semantic_failure_type_datum(failure_type: SemanticFailureType) -> Datum:
    validate_semantic_failure_type_shape(failure_type)
    return DatumRecord(
        (
            (
                0,
                DatumVariant(
                    1,
                    DatumRecord(
                        (
                            (
                                0,
                                BytesValue(
                                    failure_type.declaration_module.internal_reference()
                                ),
                            ),
                            (1, Symbol("semantic-failure")),
                            (2, Nat(failure_type.local_ordinal)),
                        )
                    ),
                ),
            ),
            (1, value_type_datum(failure_type.payload_type)),
        )
    )


def function_type_datum(function_type: SemanticFunctionType) -> Datum:
    validate_semantic_function_type(function_type)
    return DatumRecord(
        (
            (
                0,
                DatumSeq(
                    tuple(value_type_datum(item) for item in function_type.inputs)
                ),
            ),
            (1, value_type_datum(function_type.output)),
            (
                2,
                DatumSeq(
                    tuple(
                        semantic_failure_type_datum(item)
                        for item in function_type.failures
                    )
                ),
            ),
        )
    )


def validate_semantic_function_type(function_type: SemanticFunctionType) -> None:
    if type(function_type) is not SemanticFunctionType:
        raise ModelError("semantic function type has the wrong exact shape")
    if type(function_type.inputs) is not tuple:
        raise ModelError("semantic function inputs must use an immutable tuple")
    if len(function_type.inputs) > MAX_CANONICAL_EDGES:
        raise ModelError("semantic function inputs exceed the edge bound")
    if any(type(item) is not ValueType for item in function_type.inputs):
        raise ModelError("semantic function inputs must be exact value types")
    if type(function_type.output) is not ValueType:
        raise ModelError("semantic function output must be an exact value type")
    if type(function_type.failures) is not tuple:
        raise ModelError("semantic function failures must use an immutable tuple")
    if len(function_type.failures) > MAX_CANONICAL_EDGES:
        raise ModelError("semantic function failures exceed the edge bound")
    if any(type(item) is not SemanticFailureType for item in function_type.failures):
        raise ModelError("semantic function failures must be exact typed entries")

    value_types = (*function_type.inputs, function_type.output)
    for value_type in value_types:
        value_type.__post_init__()
    for failure in function_type.failures:
        validate_semantic_failure_type_shape(failure)
    semantic_regime = function_type.output.domain.semantic_regime
    if any(
        value_type.domain.semantic_regime != semantic_regime
        for value_type in function_type.inputs
    ) or any(
        failure.declaration_module.semantic_regime != semantic_regime
        for failure in function_type.failures
    ):
        raise ModelError("semantic function type crosses semantic regimes")

    encodings = tuple(
        encode_datum(semantic_failure_type_datum(item))
        for item in function_type.failures
    )
    if encodings != tuple(sorted(set(encodings))):
        raise ModelError("semantic function failures are not canonical sorted-unique")


def validate_external_operation_contract(contract: ExternalOperationContract) -> None:
    if type(contract) is not ExternalOperationContract:
        raise ModelError("external operation contract has the wrong exact shape")
    if type(contract.operation_kind) is not Symbol:
        raise ModelError("external operation kind must be an exact symbol")
    encode_datum(contract.operation_kind)
    validate_semantic_function_type(contract.function_type)
    _require_prior_meta_axis(
        contract.semantic_regime,
        expected_kind=SEMANTIC_REGIME_KIND,
        axis_name="external-operation semantic-regime",
    )
    if contract.function_type.output.domain.semantic_regime != contract.semantic_regime:
        raise ModelError("external operation contract crosses semantic regimes")


def validate_term_structure(term: Term) -> None:
    """Preflight the finite syntax tree before recursive serialization."""

    nodes = 0
    active: set[int] = set()

    def visit(current: Term, depth: int) -> None:
        nonlocal nodes
        nodes += 1
        if nodes > MAX_TERM_NODES:
            raise ModelError("term exceeds the structural node bound")
        if depth > MAX_TERM_DEPTH:
            raise ModelError("term exceeds the structural depth bound")
        marker = id(current)
        if marker in active:
            raise ModelError("cyclic host object is not a term")
        active.add(marker)
        try:
            children: tuple[Term, ...]
            if type(current) is Literal:
                if type(current.value) is not CanonicalValue:
                    raise ModelError(
                        "literal must carry a typed canonical-value candidate"
                    )
                if type(current.value.value_type) is not ValueType:
                    raise ModelError("literal must carry an exact value type")
                children = ()
            elif type(current) is Variable:
                if type(current.index) is not int or not 0 <= current.index < 1 << 64:
                    raise ModelError(
                        "variable index must be an unsigned 64-bit natural"
                    )
                if type(current.value_type) is not ValueType:
                    raise ModelError("variable annotation must be an exact value type")
                children = ()
            elif type(current) is Let:
                children = (current.bound, current.body)
            elif type(current) is RecordConstruct:
                if type(current.fields) is not tuple:
                    raise ModelError(
                        "record constructor fields must use an immutable tuple"
                    )
                if len(current.fields) > MAX_TERM_NODES - nodes:
                    raise ModelError("term exceeds the structural node bound")
                previous = -1
                child_list: list[Term] = []
                for field in current.fields:
                    if type(field) is not tuple or len(field) != 2:
                        raise ModelError(
                            "record constructor fields must be immutable ordinal-term pairs"
                        )
                    ordinal, child = field
                    if type(ordinal) is not int or not 0 <= ordinal < 1 << 64:
                        raise ModelError(
                            "record constructor ordinals must be unsigned 64-bit naturals"
                        )
                    if ordinal <= previous:
                        raise ModelError(
                            "record constructor ordinals must be strictly increasing"
                        )
                    previous = ordinal
                    child_list.append(child)
                children = tuple(child_list)
            elif type(current) is Project:
                if (
                    type(current.ordinal) is not int
                    or not 0 <= current.ordinal < 1 << 64
                ):
                    raise ModelError(
                        "projection ordinal must be an unsigned 64-bit natural"
                    )
                children = (current.record,)
            elif type(current) is Inject:
                if type(current.case) is not int or not 0 <= current.case < 1 << 64:
                    raise ModelError(
                        "injection case must be an unsigned 64-bit natural"
                    )
                if type(current.sum_type) is not ValueType:
                    raise ModelError("injection annotation must be an exact value type")
                children = (current.payload,)
            elif type(current) is Case:
                if type(current.branches) is not tuple:
                    raise ModelError("case branches must use an immutable tuple")
                if len(current.branches) + 1 > MAX_TERM_NODES - nodes:
                    raise ModelError("term exceeds the structural node bound")
                previous = -1
                branch_list: list[Term] = [current.scrutinee]
                for entry in current.branches:
                    if type(entry) is not tuple or len(entry) != 2:
                        raise ModelError(
                            "case branches must be immutable ordinal-term pairs"
                        )
                    case, branch = entry
                    if type(case) is not int or not 0 <= case < 1 << 64:
                        raise ModelError(
                            "case ordinals must be unsigned 64-bit naturals"
                        )
                    if case <= previous:
                        raise ModelError("case ordinals must be strictly increasing")
                    previous = case
                    branch_list.append(branch)
                children = tuple(branch_list)
            elif type(current) is Conditional:
                children = (
                    current.condition,
                    current.when_true,
                    current.when_false,
                )
            elif type(current) is SequenceConstruct:
                if type(current.element_type) is not ValueType:
                    raise ModelError(
                        "sequence constructor element annotation must be an exact value type"
                    )
                if type(current.elements) is not tuple:
                    raise ModelError(
                        "sequence elements must be an immutable term sequence"
                    )
                if len(current.elements) > MAX_TERM_NODES - nodes:
                    raise ModelError("term exceeds the structural node bound")
                children = current.elements
            elif type(current) is SequenceLength:
                children = (current.source,)
            elif type(current) is Fail:
                validate_semantic_failure_type_shape(current.failure_type)
                if type(current.success_type) is not ValueType:
                    raise ModelError("Fail must carry an exact success type")
                children = (current.payload,)
            elif type(current) is StrictIndex:
                validate_semantic_failure_type_shape(current.failure_type)
                children = (current.source, current.index)
            elif type(current) is BoundedAppend:
                validate_semantic_failure_type_shape(current.failure_type)
                children = (current.source, current.element)
            elif type(current) is PrimitiveCall:
                if type(current.primitive) is not SemanticPrimitiveRef:
                    raise ModelError(
                        "primitive call must carry an exact primitive reference"
                    )
                if type(current.arguments) is not tuple:
                    raise ModelError(
                        "primitive arguments must be an immutable term sequence"
                    )
                if len(current.arguments) > MAX_TERM_NODES - nodes:
                    raise ModelError("term exceeds the structural node bound")
                children = current.arguments
            elif type(current) is BoundedIterate:
                if type(current.source) is SequenceIterationSource:
                    source_term = current.source.sequence
                elif type(current.source) is RangeIterationSource:
                    source_term = current.source.exclusive_bound
                else:
                    raise ModelError("unknown bounded-iteration source")
                children = (source_term, current.initial_state, current.body)
            else:
                raise ModelError(f"unknown term constructor: {type(current)!r}")
            # Reserve every immediate child against the remaining cumulative
            # node budget before inspecting any child.  Variable-arity
            # carriers additionally preflight their raw cardinality above,
            # before inspecting member shapes or ordinals.
            if len(children) > MAX_TERM_NODES - nodes:
                raise ModelError("term exceeds the structural node bound")
            for child in children:
                visit(child, depth + 1)
        finally:
            active.remove(marker)

    visit(term, 0)


def term_datum(term: Term) -> Datum:
    if isinstance(term, Literal):
        return DatumVariant(
            0,
            DatumRecord(
                (
                    (0, value_type_datum(term.value.value_type)),
                    (1, term.value.datum),
                )
            ),
        )
    if isinstance(term, Variable):
        return DatumVariant(
            1,
            DatumRecord(((0, Nat(term.index)), (1, value_type_datum(term.value_type)))),
        )
    if isinstance(term, Let):
        return DatumVariant(
            2,
            DatumRecord(((0, term_datum(term.bound)), (1, term_datum(term.body)))),
        )
    if isinstance(term, RecordConstruct):
        return DatumVariant(
            3,
            DatumSeq(
                tuple(
                    DatumRecord(((0, Nat(ordinal)), (1, term_datum(child))))
                    for ordinal, child in term.fields
                )
            ),
        )
    if isinstance(term, Project):
        return DatumVariant(
            4,
            DatumRecord(((0, term_datum(term.record)), (1, Nat(term.ordinal)))),
        )
    if isinstance(term, Inject):
        return DatumVariant(
            5,
            DatumRecord(
                (
                    (0, Nat(term.case)),
                    (1, term_datum(term.payload)),
                    (2, value_type_datum(term.sum_type)),
                )
            ),
        )
    if isinstance(term, Case):
        return DatumVariant(
            6,
            DatumRecord(
                (
                    (0, term_datum(term.scrutinee)),
                    (
                        1,
                        DatumSeq(
                            tuple(
                                DatumRecord(((0, Nat(case)), (1, term_datum(branch))))
                                for case, branch in term.branches
                            )
                        ),
                    ),
                )
            ),
        )
    if isinstance(term, Conditional):
        return DatumVariant(
            14,
            DatumRecord(
                (
                    (0, term_datum(term.condition)),
                    (1, term_datum(term.when_true)),
                    (2, term_datum(term.when_false)),
                )
            ),
        )
    if isinstance(term, SequenceConstruct):
        return DatumVariant(
            7,
            DatumRecord(
                (
                    (0, value_type_datum(term.element_type)),
                    (1, DatumSeq(tuple(term_datum(item) for item in term.elements))),
                    (2, Nat(term.maximum_length)),
                )
            ),
        )
    if isinstance(term, SequenceLength):
        return DatumVariant(8, term_datum(term.source))
    if isinstance(term, Fail):
        return DatumVariant(
            9,
            DatumRecord(
                (
                    (0, semantic_failure_type_datum(term.failure_type)),
                    (1, term_datum(term.payload)),
                    (2, value_type_datum(term.success_type)),
                )
            ),
        )
    if isinstance(term, StrictIndex):
        return DatumVariant(
            10,
            DatumRecord(
                (
                    (0, term_datum(term.source)),
                    (1, term_datum(term.index)),
                    (2, semantic_failure_type_datum(term.failure_type)),
                )
            ),
        )
    if isinstance(term, BoundedAppend):
        return DatumVariant(
            11,
            DatumRecord(
                (
                    (0, term_datum(term.source)),
                    (1, term_datum(term.element)),
                    (2, semantic_failure_type_datum(term.failure_type)),
                )
            ),
        )
    if isinstance(term, PrimitiveCall):
        return DatumVariant(
            12,
            DatumRecord(
                (
                    (0, term.primitive.datum()),
                    (1, DatumSeq(tuple(term_datum(item) for item in term.arguments))),
                )
            ),
        )
    if isinstance(term, BoundedIterate):
        if isinstance(term.source, SequenceIterationSource):
            source = DatumVariant(0, term_datum(term.source.sequence))
        elif isinstance(term.source, RangeIterationSource):
            source = DatumVariant(1, term_datum(term.source.exclusive_bound))
        else:
            raise ModelError("unknown bounded-iteration source")
        return DatumVariant(
            13,
            DatumRecord(
                (
                    (0, source),
                    (1, term_datum(term.initial_state)),
                    (2, term_datum(term.body)),
                )
            ),
        )
    raise ModelError(f"unknown term constructor: {type(term)!r}")


def validate_algorithm_header(algorithm: CanonicalAlgorithm) -> None:
    if type(algorithm) is not CanonicalAlgorithm:
        raise ModelError("algorithm candidate has the wrong exact typed shape")
    if type(algorithm.algorithm_kind) is not Symbol:
        raise ModelError("algorithm kind must be an exact symbol")
    encode_datum(algorithm.algorithm_kind)
    if type(algorithm.inputs) is not tuple:
        raise ModelError("algorithm inputs must be an immutable value-type sequence")
    if len(algorithm.inputs) > MAX_CANONICAL_EDGES:
        raise ModelError("algorithm inputs exceed the structural edge bound")
    if any(type(item) is not ValueType for item in algorithm.inputs):
        raise ModelError("algorithm inputs must contain exact value types")
    _require_prior_meta_axis(
        algorithm.semantic_regime,
        expected_kind=SEMANTIC_REGIME_KIND,
        axis_name="algorithm semantic-regime",
    )
    for value_type in algorithm.inputs:
        value_type.__post_init__()


def algorithm_preimage(
    algorithm: CanonicalAlgorithm,
    *,
    ledger: AuthenticationLedger | None = None,
) -> bytes:
    validate_algorithm_header(algorithm)
    validate_term_structure(algorithm.term)
    primitive_dependencies = direct_primitive_dependencies(
        algorithm.term,
        ledger=ledger,
        authenticate_references=False,
    )
    return encode_datum(
        DatumRecord(
            (
                (0, algorithm.algorithm_kind),
                (
                    1,
                    DatumSeq(
                        tuple(value_type_datum(item) for item in algorithm.inputs)
                    ),
                ),
                (2, term_datum(algorithm.term)),
                (
                    3,
                    DatumSeq(tuple(item.datum() for item in primitive_dependencies)),
                ),
            )
        )
    )


@dataclass(frozen=True)
class InferredTermType:
    output: ValueType
    failures: tuple[SemanticFailureType, ...]


def _canonical_failures(
    failures: Iterable[SemanticFailureType],
) -> tuple[SemanticFailureType, ...]:
    by_encoding: dict[bytes, SemanticFailureType] = {}
    payload_by_declaration: dict[tuple[bytes, int], bytes] = {}
    for failure in failures:
        if type(failure) is not SemanticFailureType:
            raise ModelError("failure rows must contain exact semantic-failure types")
        declaration_key = (
            failure.declaration_module.internal_reference(),
            failure.local_ordinal,
        )
        payload_type = encode_datum(value_type_datum(failure.payload_type))
        previous_payload = payload_by_declaration.setdefault(
            declaration_key,
            payload_type,
        )
        if previous_payload != payload_type:
            raise ModelError(
                "one semantic-failure declaration has conflicting payload types"
            )
        encoded = encode_datum(semantic_failure_type_datum(failure))
        previous = by_encoding.setdefault(encoded, failure)
        if previous != failure:
            raise ModelError("semantic failure encoding is not injective")
    return tuple(by_encoding[key] for key in sorted(by_encoding))


def infer_term_type(
    term: Term,
    environment: tuple[ValueType, ...],
) -> InferredTermType:
    nodes = 0
    active: set[int] = set()

    def inferred(
        output: ValueType, *parts: InferredTermType | SemanticFailureType
    ) -> InferredTermType:
        failures: list[SemanticFailureType] = []
        for part in parts:
            if isinstance(part, SemanticFailureType):
                failures.append(part)
            else:
                failures.extend(part.failures)
        return InferredTermType(output, _canonical_failures(failures))

    def infer(
        current: Term, env: tuple[ValueType, ...], depth: int
    ) -> InferredTermType:
        nonlocal nodes
        nodes += 1
        if nodes > MAX_TERM_NODES or depth > MAX_TERM_DEPTH:
            raise ModelError("term exceeds structural bound")
        marker = id(current)
        if marker in active:
            raise ModelError("cyclic host object is not a term")
        active.add(marker)
        try:
            if isinstance(current, Literal):
                return inferred(current.value.value_type)
            if isinstance(current, Variable):
                if current.index < 0 or current.index >= len(env):
                    raise ModelError("variable index is outside its environment")
                if current.value_type != env[current.index]:
                    raise ModelError("variable carries the wrong declared type")
                return inferred(current.value_type)
            if isinstance(current, Let):
                bound = infer(current.bound, env, depth + 1)
                body = infer(current.body, (bound.output, *env), depth + 1)
                return inferred(body.output, bound, body)
            if isinstance(current, RecordConstruct):
                previous = -1
                fields: list[tuple[int, ValueType]] = []
                parts: list[InferredTermType] = []
                for ordinal, child in current.fields:
                    if ordinal <= previous:
                        raise ModelError(
                            "record constructor ordinals must be strictly increasing"
                        )
                    previous = ordinal
                    child_type = infer(child, env, depth + 1)
                    fields.append((ordinal, child_type.output))
                    parts.append(child_type)
                return inferred(
                    ValueType(RECORD_DOMAIN, RecordSchema(tuple(fields))), *parts
                )
            if isinstance(current, Project):
                record = infer(current.record, env, depth + 1)
                if record.output.domain != RECORD_DOMAIN or not isinstance(
                    record.output.schema, RecordSchema
                ):
                    raise ModelError("projection source is not a root record")
                fields = dict(record.output.schema.fields)
                if current.ordinal not in fields:
                    raise ModelError("projection ordinal is absent")
                return inferred(fields[current.ordinal], record)
            if isinstance(current, Inject):
                payload = infer(current.payload, env, depth + 1)
                if current.sum_type.domain != VARIANT_DOMAIN or not isinstance(
                    current.sum_type.schema, VariantSchema
                ):
                    raise ModelError("injection target is not a root tagged sum")
                cases = dict(current.sum_type.schema.cases)
                if current.case not in cases:
                    raise ModelError("injection case is absent from the tagged sum")
                if payload.output != cases[current.case]:
                    raise ModelError("injection payload has the wrong type")
                return inferred(current.sum_type, payload)
            if isinstance(current, Case):
                scrutinee = infer(current.scrutinee, env, depth + 1)
                if scrutinee.output.domain != VARIANT_DOMAIN or not isinstance(
                    scrutinee.output.schema, VariantSchema
                ):
                    raise ModelError("case scrutinee is not a root tagged sum")
                expected_cases = tuple(
                    ordinal for ordinal, _ in scrutinee.output.schema.cases
                )
                if tuple(ordinal for ordinal, _ in current.branches) != expected_cases:
                    raise ModelError("case branches are not exact and exhaustive")
                branch_parts: list[InferredTermType] = []
                branch_output: ValueType | None = None
                schemas = dict(scrutinee.output.schema.cases)
                for case, branch in current.branches:
                    payload_type = schemas[case]
                    branch_type = infer(branch, (payload_type, *env), depth + 1)
                    if branch_output is None:
                        branch_output = branch_type.output
                    elif branch_type.output != branch_output:
                        raise ModelError("case branches have different result types")
                    branch_parts.append(branch_type)
                assert branch_output is not None
                return inferred(branch_output, scrutinee, *branch_parts)
            if isinstance(current, Conditional):
                condition = infer(current.condition, env, depth + 1)
                if condition.output.domain != BOOL_DOMAIN or not isinstance(
                    condition.output.schema, BoolSchema
                ):
                    raise ModelError("conditional discriminator is not root Boolean")
                when_true = infer(current.when_true, env, depth + 1)
                when_false = infer(current.when_false, env, depth + 1)
                if when_true.output != when_false.output:
                    raise ModelError("conditional branches have different types")
                return inferred(when_true.output, condition, when_true, when_false)
            if isinstance(current, SequenceConstruct):
                parts = tuple(infer(item, env, depth + 1) for item in current.elements)
                if any(item.output != current.element_type for item in parts):
                    raise ModelError("sequence element has the wrong type")
                capacity = current.maximum_length
                if (
                    type(capacity) is not int
                    or capacity < len(parts)
                    or capacity > MAX_CANONICAL_NODES
                ):
                    raise ModelError(
                        "sequence capacity must be a bounded natural at least its length"
                    )
                return inferred(
                    ValueType(
                        SEQUENCE_DOMAIN,
                        SeqSchema(current.element_type, capacity),
                    ),
                    *parts,
                )
            if isinstance(current, SequenceLength):
                source = infer(current.source, env, depth + 1)
                if source.output.domain != SEQUENCE_DOMAIN or not isinstance(
                    source.output.schema, SeqSchema
                ):
                    raise ModelError("sequence length source is not a root sequence")
                return inferred(
                    ValueType(
                        NAT_DOMAIN,
                        NatSchema(source.output.schema.maximum_length),
                    ),
                    source,
                )
            if isinstance(current, Fail):
                validate_semantic_failure_type_shape(current.failure_type)
                payload = infer(current.payload, env, depth + 1)
                if payload.output != current.failure_type.payload_type:
                    raise ModelError("semantic failure payload has the wrong type")
                return inferred(current.success_type, payload, current.failure_type)
            if isinstance(current, StrictIndex):
                validate_semantic_failure_type_shape(current.failure_type)
                source = infer(current.source, env, depth + 1)
                index = infer(current.index, env, depth + 1)
                if source.output.domain != SEQUENCE_DOMAIN or not isinstance(
                    source.output.schema, SeqSchema
                ):
                    raise ModelError("strict index source is not a root sequence")
                if index.output.domain != NAT_DOMAIN or not isinstance(
                    index.output.schema, NatSchema
                ):
                    raise ModelError("strict index is not a root natural")
                if index.output != current.failure_type.payload_type:
                    raise ModelError("index failure payload must carry the exact index")
                return inferred(
                    source.output.schema.element,
                    source,
                    index,
                    current.failure_type,
                )
            if isinstance(current, BoundedAppend):
                validate_semantic_failure_type_shape(current.failure_type)
                source = infer(current.source, env, depth + 1)
                element = infer(current.element, env, depth + 1)
                if source.output.domain != SEQUENCE_DOMAIN or not isinstance(
                    source.output.schema, SeqSchema
                ):
                    raise ModelError("bounded append source is not a root sequence")
                if element.output != source.output.schema.element:
                    raise ModelError("bounded append element has the wrong type")
                if current.failure_type.payload_type != ValueType(
                    UNIT_DOMAIN, UNIT_SCHEMA
                ):
                    raise ModelError(
                        "bounded append capacity failure must carry exact Unit"
                    )
                return inferred(
                    source.output,
                    source,
                    element,
                    current.failure_type,
                )
            if isinstance(current, PrimitiveCall):
                declaration = resolve_primitive_declaration(current.primitive)
                arguments = tuple(
                    infer(item, env, depth + 1) for item in current.arguments
                )
                output = resolve_primitive_type_rule(declaration.identifier)(
                    tuple(item.output for item in arguments)
                )
                return inferred(output, *arguments, *declaration.failures)
            if isinstance(current, BoundedIterate):
                source_parts: list[InferredTermType] = []
                if isinstance(current.source, SequenceIterationSource):
                    source = infer(current.source.sequence, env, depth + 1)
                    if source.output.domain != SEQUENCE_DOMAIN or not isinstance(
                        source.output.schema, SeqSchema
                    ):
                        raise ModelError(
                            "bounded-iteration source is not a root sequence"
                        )
                    source_parts.append(source)
                    maximum_items = source.output.schema.maximum_length
                    element_type = source.output.schema.element
                    index_type = ValueType(
                        NAT_DOMAIN, NatSchema(max(0, maximum_items - 1))
                    )
                elif isinstance(current.source, RangeIterationSource):
                    bound = infer(current.source.exclusive_bound, env, depth + 1)
                    if bound.output.domain != NAT_DOMAIN or not isinstance(
                        bound.output.schema, NatSchema
                    ):
                        raise ModelError("range bound is not a root natural")
                    source_parts.append(bound)
                    maximum_items = bound.output.schema.maximum
                    index_type = ValueType(
                        NAT_DOMAIN,
                        NatSchema(max(0, maximum_items - 1)),
                    )
                    element_type = index_type
                else:
                    raise ModelError("unknown bounded-iteration source")
                if maximum_items > MAX_CANONICAL_NODES:
                    raise ModelError("bounded iteration exceeds the structural profile")
                initial = infer(current.initial_state, env, depth + 1)
                body = infer(
                    current.body,
                    (index_type, element_type, initial.output, *env),
                    depth + 1,
                )
                if body.output.domain != VARIANT_DOMAIN or not isinstance(
                    body.output.schema, VariantSchema
                ):
                    raise ModelError(
                        "bounded-iteration body must return Continue or Break"
                    )
                cases = dict(body.output.schema.cases)
                if tuple(cases) != (0, 1):
                    raise ModelError(
                        "bounded-iteration result must have exact cases 0 and 1"
                    )
                if cases[0] != initial.output:
                    raise ModelError(
                        "Continue payload does not preserve the state type"
                    )
                return inferred(
                    body.output,
                    *source_parts,
                    initial,
                    body,
                )
            raise ModelError(f"unknown term constructor: {type(current)!r}")
        finally:
            active.remove(marker)

    return infer(term, environment, 0)


def direct_primitive_dependencies(
    term: Term,
    *,
    ledger: AuthenticationLedger | None = None,
    authenticate_references: bool = True,
) -> tuple[SemanticPrimitiveRef, ...]:
    used: dict[tuple[bytes, bytes], SemanticPrimitiveRef] = {}
    active: set[int] = set()

    def visit(current: Term) -> None:
        marker = id(current)
        if marker in active:
            raise ModelError("cyclic host object is not a term")
        active.add(marker)
        try:
            if isinstance(current, PrimitiveCall):
                if type(current.primitive) is not SemanticPrimitiveRef:
                    raise ModelError(
                        "primitive reference has the wrong exact typed shape"
                    )
                current.primitive.__post_init__()
                current.primitive.identifier.__post_init__()
                current.primitive.declaration_module.__post_init__()
                if authenticate_references:
                    authenticate_primitive_reference(
                        current.primitive,
                        ledger=ledger,
                    )
                key = (
                    current.primitive.identifier.internal_reference(),
                    encode_datum(current.primitive.declaration_body()),
                )
                used.setdefault(key, current.primitive)
                for child in current.arguments:
                    visit(child)
            elif isinstance(current, Let):
                visit(current.bound)
                visit(current.body)
            elif isinstance(current, RecordConstruct):
                for _, child in current.fields:
                    visit(child)
            elif isinstance(current, Project):
                visit(current.record)
            elif isinstance(current, Inject):
                visit(current.payload)
            elif isinstance(current, Case):
                visit(current.scrutinee)
                for _, branch in current.branches:
                    visit(branch)
            elif isinstance(current, Conditional):
                visit(current.condition)
                visit(current.when_true)
                visit(current.when_false)
            elif isinstance(current, SequenceConstruct):
                for child in current.elements:
                    visit(child)
            elif isinstance(current, SequenceLength):
                visit(current.source)
            elif isinstance(current, Fail):
                visit(current.payload)
            elif isinstance(current, StrictIndex):
                visit(current.source)
                visit(current.index)
            elif isinstance(current, BoundedAppend):
                visit(current.source)
                visit(current.element)
            elif isinstance(current, BoundedIterate):
                if isinstance(current.source, SequenceIterationSource):
                    visit(current.source.sequence)
                else:
                    assert isinstance(current.source, RangeIterationSource)
                    visit(current.source.exclusive_bound)
                visit(current.initial_state)
                visit(current.body)
        finally:
            active.remove(marker)

    visit(term)
    return tuple(used[key] for key in sorted(used))


def direct_module_dependencies(
    algorithm: CanonicalAlgorithm,
    *,
    ledger: AuthenticationLedger | None = None,
) -> tuple[TypedContentId, ...]:
    """Derive exact direct module roots from typed semantic references."""

    validate_algorithm_header(algorithm)
    validate_term_structure(algorithm.term)

    used: dict[bytes, TypedContentId] = {}

    def add_module(identifier: TypedContentId) -> None:
        _require_typed_content_id(
            identifier,
            axis_name="semantic declaration owner",
        )
        if identifier.subject_kind != SEMANTIC_MODULE_KIND:
            raise DeclarationKindMismatchError(
                "semantic declaration owner is not a module"
            )
        if identifier.semantic_regime != algorithm.semantic_regime:
            raise SemanticRegimeMismatchError(
                "semantic declaration owner crosses the authenticated regime"
            )
        used[identifier.internal_reference()] = identifier

    def add_value_type(value_type: ValueType) -> None:
        value_type.__post_init__()
        if value_type.domain.semantic_regime != algorithm.semantic_regime:
            raise SemanticRegimeMismatchError(
                "algorithm value type crosses the authenticated semantic regime"
            )
        owner = value_type.domain.owner
        if isinstance(owner, TypedContentId):
            add_module(owner)
        schema = value_type.schema
        if isinstance(schema, SeqSchema):
            add_value_type(schema.element)
        elif isinstance(schema, RecordSchema):
            for _, field_type in schema.fields:
                add_value_type(field_type)
        elif isinstance(schema, VariantSchema):
            for _, case_type in schema.cases:
                add_value_type(case_type)

    def add_failure(failure: SemanticFailureType) -> None:
        validate_semantic_failure_type_shape(failure)
        add_module(failure.declaration_module)
        add_value_type(failure.payload_type)

    def visit(term: Term) -> None:
        if isinstance(term, Literal):
            add_value_type(term.value.value_type)
        elif isinstance(term, Variable):
            add_value_type(term.value_type)
        elif isinstance(term, Let):
            visit(term.bound)
            visit(term.body)
        elif isinstance(term, RecordConstruct):
            for _, child in term.fields:
                visit(child)
        elif isinstance(term, Project):
            visit(term.record)
        elif isinstance(term, Inject):
            add_value_type(term.sum_type)
            visit(term.payload)
        elif isinstance(term, Case):
            visit(term.scrutinee)
            for _, branch in term.branches:
                visit(branch)
        elif isinstance(term, Conditional):
            visit(term.condition)
            visit(term.when_true)
            visit(term.when_false)
        elif isinstance(term, SequenceConstruct):
            add_value_type(term.element_type)
            for child in term.elements:
                visit(child)
        elif isinstance(term, SequenceLength):
            visit(term.source)
        elif isinstance(term, Fail):
            add_failure(term.failure_type)
            add_value_type(term.success_type)
            visit(term.payload)
        elif isinstance(term, StrictIndex):
            add_failure(term.failure_type)
            visit(term.source)
            visit(term.index)
        elif isinstance(term, BoundedAppend):
            add_failure(term.failure_type)
            visit(term.source)
            visit(term.element)
        elif isinstance(term, PrimitiveCall):
            if (
                term.primitive.identifier.semantic_regime != algorithm.semantic_regime
                or term.primitive.declaration_module.semantic_regime
                != algorithm.semantic_regime
            ):
                raise SemanticRegimeMismatchError(
                    "primitive coordinate crosses the authenticated regime"
                )
            authenticate_primitive_reference(term.primitive, ledger=ledger)
            add_module(term.primitive.declaration_module)
            for argument in term.arguments:
                visit(argument)
        elif isinstance(term, BoundedIterate):
            if isinstance(term.source, SequenceIterationSource):
                visit(term.source.sequence)
            else:
                assert isinstance(term.source, RangeIterationSource)
                visit(term.source.exclusive_bound)
            visit(term.initial_state)
            visit(term.body)
        else:
            raise ModelError(f"unknown term constructor: {type(term)!r}")

    for input_type in algorithm.inputs:
        add_value_type(input_type)
    visit(algorithm.term)
    return tuple(used[key] for key in sorted(used))


def algorithm_value_types(algorithm: CanonicalAlgorithm) -> tuple[ValueType, ...]:
    """Return every value type reachable through the exact typed term.

    This is intentionally syntax-directed rather than a scan of the final ABI:
    an intermediate primitive result or bound value may require domain support
    even when the final success type does not.
    """

    used: dict[bytes, ValueType] = {}

    def add(value_type: ValueType) -> None:
        body = encode_datum(value_type_datum(value_type))
        previous = used.setdefault(body, value_type)
        if previous != value_type:
            raise ModelError("value-type encoding is not injective")
        for child in nested_value_types(value_type):
            add(child)

    def visit(current: Term, env: tuple[ValueType, ...]) -> None:
        current_type = infer_term_type(current, env)
        add(current_type.output)
        for failure in current_type.failures:
            add(failure.payload_type)

        if isinstance(current, (Literal, Variable)):
            return
        if isinstance(current, Let):
            visit(current.bound, env)
            bound_type = infer_term_type(current.bound, env).output
            visit(current.body, (bound_type, *env))
            return
        if isinstance(current, RecordConstruct):
            for _, child in current.fields:
                visit(child, env)
            return
        if isinstance(current, Project):
            visit(current.record, env)
            return
        if isinstance(current, Inject):
            add(current.sum_type)
            visit(current.payload, env)
            return
        if isinstance(current, Case):
            visit(current.scrutinee, env)
            scrutinee_type = infer_term_type(current.scrutinee, env).output
            assert isinstance(scrutinee_type.schema, VariantSchema)
            case_types = dict(scrutinee_type.schema.cases)
            for case, branch in current.branches:
                visit(branch, (case_types[case], *env))
            return
        if isinstance(current, Conditional):
            visit(current.condition, env)
            visit(current.when_true, env)
            visit(current.when_false, env)
            return
        if isinstance(current, SequenceConstruct):
            add(current.element_type)
            for child in current.elements:
                visit(child, env)
            return
        if isinstance(current, SequenceLength):
            visit(current.source, env)
            return
        if isinstance(current, Fail):
            add(current.failure_type.payload_type)
            add(current.success_type)
            visit(current.payload, env)
            return
        if isinstance(current, StrictIndex):
            add(current.failure_type.payload_type)
            visit(current.source, env)
            visit(current.index, env)
            return
        if isinstance(current, BoundedAppend):
            add(current.failure_type.payload_type)
            visit(current.source, env)
            visit(current.element, env)
            return
        if isinstance(current, PrimitiveCall):
            for argument in current.arguments:
                visit(argument, env)
            return
        if isinstance(current, BoundedIterate):
            if isinstance(current.source, SequenceIterationSource):
                visit(current.source.sequence, env)
                source_type = infer_term_type(current.source.sequence, env).output
                assert isinstance(source_type.schema, SeqSchema)
                maximum_items = source_type.schema.maximum_length
                element_type = source_type.schema.element
            else:
                assert isinstance(current.source, RangeIterationSource)
                visit(current.source.exclusive_bound, env)
                bound_type = infer_term_type(current.source.exclusive_bound, env).output
                assert isinstance(bound_type.schema, NatSchema)
                maximum_items = bound_type.schema.maximum
                element_type = ValueType(
                    NAT_DOMAIN, NatSchema(max(0, maximum_items - 1))
                )
            index_type = ValueType(NAT_DOMAIN, NatSchema(max(0, maximum_items - 1)))
            visit(current.initial_state, env)
            initial_type = infer_term_type(current.initial_state, env).output
            visit(current.body, (index_type, element_type, initial_type, *env))
            return
        raise ModelError(f"unknown term constructor: {type(current)!r}")

    for input_type in algorithm.inputs:
        add(input_type)
    visit(algorithm.term, algorithm.inputs)
    return tuple(used[key] for key in sorted(used))


def admit_algorithm_literals(algorithm: CanonicalAlgorithm) -> None:
    """Domain-admit every literal in canonical syntax order before execution."""

    def visit(current: Term) -> None:
        if isinstance(current, Literal):
            admit_value(current.value.value_type, current.value.datum)
            return
        if isinstance(current, Variable):
            return
        if isinstance(current, Let):
            visit(current.bound)
            visit(current.body)
            return
        if isinstance(current, RecordConstruct):
            for _, child in current.fields:
                visit(child)
            return
        if isinstance(current, Project):
            visit(current.record)
            return
        if isinstance(current, Inject):
            visit(current.payload)
            return
        if isinstance(current, Case):
            visit(current.scrutinee)
            for _, branch in current.branches:
                visit(branch)
            return
        if isinstance(current, Conditional):
            visit(current.condition)
            visit(current.when_true)
            visit(current.when_false)
            return
        if isinstance(current, SequenceConstruct):
            for child in current.elements:
                visit(child)
            return
        if isinstance(current, SequenceLength):
            visit(current.source)
            return
        if isinstance(current, Fail):
            visit(current.payload)
            return
        if isinstance(current, StrictIndex):
            visit(current.source)
            visit(current.index)
            return
        if isinstance(current, BoundedAppend):
            visit(current.source)
            visit(current.element)
            return
        if isinstance(current, PrimitiveCall):
            for argument in current.arguments:
                visit(argument)
            return
        if isinstance(current, BoundedIterate):
            if isinstance(current.source, SequenceIterationSource):
                visit(current.source.sequence)
            else:
                assert isinstance(current.source, RangeIterationSource)
                visit(current.source.exclusive_bound)
            visit(current.initial_state)
            visit(current.body)
            return
        raise ModelError(f"unknown term constructor: {type(current)!r}")

    visit(algorithm.term)


def authenticate_algorithm_identity(
    algorithm: CanonicalAlgorithm,
    *,
    ledger: AuthenticationLedger | None = None,
) -> TypedContentId:
    """Authenticate syntax identity without consulting module denotations."""

    if type(algorithm) is not CanonicalAlgorithm:
        raise ModelError("algorithm candidate has the wrong typed shape")
    if type(algorithm.semantic_regime) is not PriorMetaId:
        raise CanonicalError("algorithm semantic-regime must be a PriorMetaId")
    algorithm.semantic_regime.__post_init__()
    if (
        algorithm.semantic_regime.subject_kind != SEMANTIC_REGIME_KIND
        or algorithm.semantic_regime != SEMANTIC_REGIME_ID
    ):
        raise SemanticRegimeMismatchError(
            "algorithm semantic-regime kind or identity differs from the authenticated basis"
        )
    if type(algorithm.inputs) is not tuple:
        raise ModelError("algorithm inputs must be an immutable value-type sequence")
    if len(algorithm.inputs) > MAX_CANONICAL_EDGES:
        raise ModelError("algorithm inputs exceed the structural edge bound")
    if any(type(item) is not ValueType for item in algorithm.inputs):
        raise ModelError("algorithm inputs must contain exact value types")
    if type(algorithm.algorithm_kind) is not Symbol:
        raise ModelError("algorithm kind must be an exact symbol")
    body = algorithm_preimage(algorithm, ledger=ledger)
    identifier = content_id(
        PORTABLE_ALGORITHM_KIND,
        body,
        semantic_regime=algorithm.semantic_regime,
    )
    authenticate_content_id(
        identifier,
        body,
        FOUNDATION_PRIOR_META_PREIMAGES,
        ledger=ledger,
    )
    return identifier


def check_algorithm_syntax_and_types(
    algorithm: CanonicalAlgorithm,
) -> TypedContentId:
    """Authenticate syntax identity and check fixture primitive typing.

    This capability-free helper does not authenticate RequiredModuleClosure or
    resolve module-owned value and failure declarations.  Full evaluation
    admission is the evaluator boundary, which requires explicit module
    preimages before consulting declaration denotations.
    """

    ledger = AuthenticationLedger()
    identifier = authenticate_algorithm_identity(algorithm, ledger=ledger)
    module_dependencies = direct_module_dependencies(algorithm, ledger=ledger)
    module_keys = tuple(item.internal_reference() for item in module_dependencies)
    if module_keys != tuple(sorted(set(module_keys))):
        raise ModelError("module dependencies must be canonical sorted-unique")
    for reference in direct_primitive_dependencies(algorithm.term, ledger=ledger):
        resolve_primitive_declaration(reference, ledger=ledger)
    infer_term_type(algorithm.term, algorithm.inputs)
    return identifier


# ---------------------------------------------------------------------------
# Evaluation, semantic completion, and separate deterministic charging
# ---------------------------------------------------------------------------


class Outcome(str, Enum):
    COMPLETED = "Completed"
    UNSUPPORTED = "Unsupported"
    MISSING_DEPENDENCY = "MissingDependency"
    CANNOT_ANSWER = "CannotAnswer"
    KIND_MISMATCH = "KindMismatch"
    MALFORMED = "Malformed"
    REFUSED = "Refused"
    DETERMINISTIC_LIMIT_EXCEEDED = "DeterministicLimitExceeded"
    CHECKER_FAILURE = "CheckerFailure"


@dataclass(frozen=True)
class Success:
    value: CanonicalValue


@dataclass(frozen=True)
class DomainFailure:
    failure_type: SemanticFailureType
    payload: CanonicalValue


Completion: TypeAlias = Success | DomainFailure


@dataclass(frozen=True)
class AbstractCharge:
    steps: int = 0
    iteration_items: int = 0
    primitive_work: int = 0
    result_bytes: int = 0


@dataclass(frozen=True)
class DeterministicLimits:
    maximum_steps: int
    maximum_iteration_items: int
    maximum_primitive_work: int
    maximum_result_bytes: int


@dataclass(frozen=True)
class PrimitiveWorkFormulaV0:
    kind: Symbol
    argument_indices: tuple[int, ...] = ()
    constant: int = 0

    def __post_init__(self) -> None:
        if type(self.kind) is not Symbol:
            raise ModelError("primitive cost kind must be an exact symbol")
        if type(self.argument_indices) is not tuple:
            raise ModelError("primitive cost indices must be an immutable tuple")
        if len(self.argument_indices) > MAX_CANONICAL_EDGES:
            raise ModelError("primitive cost indices exceed the edge bound")
        encode_datum(self.kind)
        if type(self.constant) is not int or self.constant < 0:
            raise ModelError("primitive cost constant must be a natural")
        if any(not _is_u64_natural(item) for item in self.argument_indices):
            raise ModelError("primitive cost indices must be u64 naturals")
        if self.kind.value == "fixed":
            if self.argument_indices:
                raise ModelError("fixed cost cannot carry argument indices")
        elif self.kind.value == "sum-byte-lengths":
            if self.argument_indices != tuple(sorted(set(self.argument_indices))):
                raise ModelError(
                    "sum-byte-length cost indices must be canonical sorted-unique"
                )
        elif self.kind.value == "min-byte-length-natural":
            if len(self.argument_indices) != 2:
                raise ModelError("min cost rule requires two argument indices")
        else:
            raise ModelError("unknown primitive work formula")

    def measure(self, values: tuple[CanonicalValue, ...]) -> int:
        if type(self) is not PrimitiveWorkFormulaV0:
            raise ModelError("primitive work formula has the wrong exact shape")
        if self.kind.value == "fixed":
            if self.argument_indices:
                raise ModelError("fixed cost cannot carry argument indices")
            return self.constant
        if self.kind.value == "sum-byte-lengths":
            total = self.constant
            for index in self.argument_indices:
                if index >= len(values) or type(values[index].datum) is not BytesValue:
                    raise ModelError("byte-length cost rule has the wrong argument")
                total += len(values[index].datum.value)
            return total
        if self.kind.value == "min-byte-length-natural":
            if len(self.argument_indices) != 2:
                raise ModelError("min cost rule requires two argument indices")
            byte_index, natural_index = self.argument_indices
            if byte_index >= len(values) or natural_index >= len(values):
                raise ModelError("min cost rule index is outside the primitive ABI")
            byte_value = values[byte_index].datum
            natural = values[natural_index].datum
            if type(byte_value) is not BytesValue or type(natural) is not Nat:
                raise ModelError("min cost rule has the wrong argument types")
            return self.constant + min(len(byte_value.value), natural.value)
        raise ModelError("unknown primitive work formula")


@dataclass(frozen=True)
class PrimitiveCostRuleV0:
    primitive: TypedContentId
    formula: PrimitiveWorkFormulaV0

    def __post_init__(self) -> None:
        if type(self.primitive) is not TypedContentId:
            raise ModelError("primitive cost key must be an exact typed ID")
        self.primitive.__post_init__()
        if type(self.formula) is not PrimitiveWorkFormulaV0:
            raise ModelError("primitive cost formula has the wrong exact shape")
        self.formula.__post_init__()


def primitive_work_formula_datum(formula: PrimitiveWorkFormulaV0) -> Datum:
    if type(formula) is not PrimitiveWorkFormulaV0:
        raise ModelError("primitive work formula has the wrong exact shape")
    formula.__post_init__()
    if formula.kind.value == "fixed":
        return DatumVariant(0, Nat(formula.constant))
    if formula.kind.value == "sum-byte-lengths":
        return DatumVariant(
            1,
            DatumRecord(
                (
                    (
                        0,
                        DatumSeq(tuple(Nat(item) for item in formula.argument_indices)),
                    ),
                    (1, Nat(formula.constant)),
                )
            ),
        )
    if formula.kind.value == "min-byte-length-natural":
        byte_index, natural_index = formula.argument_indices
        return DatumVariant(
            2,
            DatumRecord(
                (
                    (0, Nat(byte_index)),
                    (1, Nat(natural_index)),
                    (2, Nat(formula.constant)),
                )
            ),
        )
    raise ModelError("unknown primitive work formula")


@dataclass(frozen=True)
class EvaluationContractV0:
    """Identified charging and preflight rules, not semantic evaluation order."""

    term_step_units: int
    iteration_item_units: int
    validation_precedence: Symbol
    completion_measure: Symbol
    static_bound_rule: Symbol
    primitive_cost_rules: tuple[PrimitiveCostRuleV0, ...]
    semantic_regime: PriorMetaId = SEMANTIC_REGIME_ID

    def _formed_body(self) -> bytes:
        """Form the complete closed body before typed-coordinate routing."""

        if type(self.term_step_units) is not int or self.term_step_units < 0:
            raise ModelError("term-step charge must be a natural")
        if type(self.iteration_item_units) is not int or self.iteration_item_units < 0:
            raise ModelError("iteration-item charge must be a natural")
        if type(self.semantic_regime) is not PriorMetaId:
            raise ModelError("evaluation contract has the wrong regime-ID shape")
        self.semantic_regime.__post_init__()
        if any(
            type(item) is not Symbol
            for item in (
                self.validation_precedence,
                self.completion_measure,
                self.static_bound_rule,
            )
        ):
            raise ModelError("evaluation contract tags must be exact symbols")
        for tag in (
            self.validation_precedence,
            self.completion_measure,
            self.static_bound_rule,
        ):
            encode_datum(tag)
        if self.validation_precedence != Symbol("portable-evaluation-precedence-v0"):
            raise ModelError("evaluation contract has an unknown precedence tag")
        if self.completion_measure != Symbol("tagged-canonical-completion-v0"):
            raise ModelError("evaluation contract has an unknown completion tag")
        if self.static_bound_rule != Symbol("maximum-completion-schema-v0"):
            raise ModelError("evaluation contract has an unknown static-bound tag")
        if type(self.primitive_cost_rules) is not tuple:
            raise ModelError("primitive cost rules must be an immutable tuple")
        if len(self.primitive_cost_rules) > MAX_CANONICAL_EDGES:
            raise ModelError("primitive cost rules exceed the edge bound")
        for rule in self.primitive_cost_rules:
            if type(rule) is not PrimitiveCostRuleV0:
                raise ModelError("primitive cost rule has the wrong typed shape")
            rule.__post_init__()
        keys = tuple(
            rule.primitive.internal_reference() for rule in self.primitive_cost_rules
        )
        if keys != tuple(sorted(set(keys))):
            raise ModelError("primitive cost rules must be canonical sorted-unique")
        rules = DatumSeq(
            tuple(
                DatumRecord(
                    (
                        (0, BytesValue(rule.primitive.internal_reference())),
                        (1, primitive_work_formula_datum(rule.formula)),
                    )
                )
                for rule in self.primitive_cost_rules
            )
        )
        return encode_datum(
            DatumRecord(
                (
                    (0, Nat(0)),
                    (1, Nat(self.term_step_units)),
                    (2, Nat(self.iteration_item_units)),
                    (3, self.validation_precedence),
                    (4, self.completion_measure),
                    (5, self.static_bound_rule),
                    (6, rules),
                )
            )
        )

    def _validate_coordinates(self) -> None:
        if self.semantic_regime != SEMANTIC_REGIME_ID:
            raise ModelError("evaluation contract crosses semantic regimes")
        for rule in self.primitive_cost_rules:
            if rule.primitive.subject_kind != SEMANTIC_PRIMITIVE_KIND:
                raise ModelError("primitive cost rule key has the wrong kind")
            if rule.primitive.semantic_regime != self.semantic_regime:
                raise ModelError("primitive cost rule crosses semantic regimes")

    def __post_init__(self) -> None:
        self._formed_body()
        self._validate_coordinates()

    def body(self) -> bytes:
        if type(self) is not EvaluationContractV0:
            raise ModelError("evaluation contract has the wrong exact typed shape")
        body = self._formed_body()
        self._validate_coordinates()
        return body

    @property
    def identity(self) -> TypedContentId:
        return content_id(
            EVALUATION_CONTRACT_KIND,
            self.body(),
            semantic_regime=self.semantic_regime,
        )

    def cost_rule(self, primitive: TypedContentId) -> PrimitiveWorkFormulaV0 | None:
        if type(self) is not EvaluationContractV0:
            raise ModelError("evaluation contract has the wrong exact typed shape")
        for rule in self.primitive_cost_rules:
            if rule.primitive == primitive:
                return rule.formula
        return None


def _cost_rule(
    key: tuple[str, int], formula: PrimitiveWorkFormulaV0
) -> PrimitiveCostRuleV0:
    return PrimitiveCostRuleV0(PRIMITIVE_IDS_BY_KEY[key], formula)


DEFAULT_EVALUATION_CONTRACT = EvaluationContractV0(
    term_step_units=1,
    iteration_item_units=1,
    validation_precedence=Symbol("portable-evaluation-precedence-v0"),
    completion_measure=Symbol("tagged-canonical-completion-v0"),
    static_bound_rule=Symbol("maximum-completion-schema-v0"),
    primitive_cost_rules=tuple(
        sorted(
            (
                _cost_rule(
                    ("sha2-256", 1),
                    PrimitiveWorkFormulaV0(Symbol("sum-byte-lengths"), (0,), 64),
                ),
                _cost_rule(
                    ("bytes.concat", 1),
                    PrimitiveWorkFormulaV0(Symbol("sum-byte-lengths"), (0, 1)),
                ),
                _cost_rule(
                    ("u64.to-be", 1), PrimitiveWorkFormulaV0(Symbol("fixed"), (), 8)
                ),
                _cost_rule(
                    ("bytes.first-u64-be", 1),
                    PrimitiveWorkFormulaV0(Symbol("fixed"), (), 8),
                ),
                _cost_rule(
                    ("nat.lt", 1), PrimitiveWorkFormulaV0(Symbol("fixed"), (), 1)
                ),
                _cost_rule(
                    ("nat.mod-positive", 1),
                    PrimitiveWorkFormulaV0(Symbol("fixed"), (), 1),
                ),
                _cost_rule(
                    ("bytes.take", 1),
                    PrimitiveWorkFormulaV0(Symbol("min-byte-length-natural"), (0, 1)),
                ),
                _cost_rule(
                    ("fixture.bytes.reverse", 1),
                    PrimitiveWorkFormulaV0(Symbol("sum-byte-lengths"), (0,)),
                ),
                _cost_rule(
                    ("fixture.bytes.prefix-27", 1),
                    PrimitiveWorkFormulaV0(Symbol("sum-byte-lengths"), (0,)),
                ),
            ),
            key=lambda rule: rule.primitive.internal_reference(),
        )
    ),
)


DEFAULT_LIMITS = DeterministicLimits(100_000, 100_000, 1 << 22, 1 << 20)


@dataclass(frozen=True)
class EvaluationResult:
    outcome: Outcome
    charge: AbstractCharge
    completion: Completion | None = None
    code: str = ""
    detail: str = ""


@dataclass(frozen=True)
class SemanticModuleCandidate:
    diagnostic_label: Symbol
    imports: tuple[TypedContentId, ...]
    local_declarations: Datum
    domain_payload: Datum = UNIT

    def body(self) -> bytes:
        if type(self) is not SemanticModuleCandidate:
            raise ModelError("module candidate has the wrong exact typed shape")
        if type(self.imports) is not tuple:
            raise ModelError("module imports must be an immutable typed-ID sequence")
        if len(self.imports) > MAX_MODULE_EDGES:
            raise ModelError("module imports exceed the semantic edge bound")
        if any(type(item) is not TypedContentId for item in self.imports):
            raise ModelError("module imports must contain exact typed IDs")
        return encode_datum(
            DatumRecord(
                (
                    (
                        0,
                        DatumSeq(
                            tuple(
                                BytesValue(item.internal_reference())
                                for item in self.imports
                            )
                        ),
                    ),
                    (1, self.local_declarations),
                    (2, self.domain_payload),
                )
            )
        )

    @property
    def identity(self) -> TypedContentId:
        """Identify this fixture candidate under the selected K1 regime."""

        return self.identity_for(SEMANTIC_REGIME_ID)

    def identity_for(self, semantic_regime: PriorMetaId) -> TypedContentId:
        """Identify the body under an explicit, authenticated regime axis."""

        return content_id(
            SEMANTIC_MODULE_KIND,
            self.body(),
            semantic_regime=semantic_regime,
        )


@dataclass(frozen=True)
class SemanticLanguageProfile:
    """One standalone, exact, domain-owned language-profile preimage."""

    profile_family: Symbol
    revision: int
    profile_imports: tuple[TypedContentId, ...]
    supported_subject_kinds: tuple[Symbol, ...]
    declaration_catalogs: DatumSeq
    semantic_law_source: bytes

    def body(self) -> DatumRecord:
        if type(self) is not SemanticLanguageProfile:
            raise ModelError(
                "semantic-language profile has the wrong exact typed shape"
            )
        if type(self.profile_family) is not Symbol:
            raise ModelError("profile family must be an exact MetaSymbol")
        if not _is_u64_natural(self.revision):
            raise ModelError("profile revision must be a u64 natural")
        profile_imports = _profile_reference_sequence(
            self.profile_imports,
            label="semantic-language profile imports",
        )
        if type(self.supported_subject_kinds) is not tuple:
            raise ModelError(
                "supported subject kinds must use an immutable tuple"
            )
        if not self.supported_subject_kinds:
            raise ModelError("a semantic-language profile must support a subject")
        if len(self.supported_subject_kinds) > MAX_CANONICAL_EDGES:
            raise ModelError("supported subject kinds exceed the edge bound")
        if any(type(item) is not Symbol for item in self.supported_subject_kinds):
            raise ModelError("supported subject kinds must be exact MetaSymbols")
        keys = tuple(
            item.value.encode("ascii") for item in self.supported_subject_kinds
        )
        if keys != tuple(sorted(set(keys))):
            raise ModelError(
                "supported subject kinds must be canonical sorted-unique"
            )
        if any(
            item.value in PROFILED_FORBIDDEN_SUBJECT_KINDS
            for item in self.supported_subject_kinds
        ):
            raise ModelError(
                "a profile cannot govern prior-meta or standalone Foundation "
                "subject kinds"
            )
        if type(self.declaration_catalogs) is not DatumSeq:
            raise ModelError("profile declaration catalogs must be an exact MetaSeq")
        profile_declaration_catalogs(self)
        if type(self.semantic_law_source) is not bytes:
            raise ModelError("semantic law source must be exact bytes")
        if not self.semantic_law_source:
            raise ModelError("semantic law source must be nonempty")
        body = DatumRecord(
            (
                (0, self.profile_family),
                (1, Nat(self.revision)),
                (
                    2,
                    DatumSeq(
                        tuple(
                            BytesValue(item.internal_reference())
                            for item in profile_imports
                        )
                    ),
                ),
                (
                    3,
                    DatumSeq(self.supported_subject_kinds),
                ),
                (4, self.declaration_catalogs),
                (5, BytesValue(self.semantic_law_source)),
            )
        )
        encode_datum(body)
        return body

    def identity_for(self, semantic_regime: PriorMetaId) -> TypedContentId:
        _require_prior_meta_axis(
            semantic_regime,
            expected_kind=SEMANTIC_REGIME_KIND,
            axis_name="semantic-language profile regime",
        )
        if any(
            item.semantic_regime != semantic_regime
            for item in self.profile_imports
        ):
            raise DeclarationKindMismatchError(
                "semantic-language profile dependencies cross regimes"
            )
        return content_id(
            SEMANTIC_LANGUAGE_PROFILE_KIND,
            encode_datum(self.body()),
            semantic_regime=semantic_regime,
        )

    @property
    def identity(self) -> TypedContentId:
        return self.identity_for(SEMANTIC_REGIME_ID)


SemanticLanguageProfileId: TypeAlias = TypedContentId
SemanticLanguageProfileBody: TypeAlias = SemanticLanguageProfile
ProfilePreimageBundle: TypeAlias = dict[
    SemanticLanguageProfileId, SemanticLanguageProfileBody
]


def _sorted_unique_reference_sequence(
    values: tuple[TypedContentId, ...],
    *,
    label: str,
    expected_kind: str,
) -> tuple[TypedContentId, ...]:
    if type(values) is not tuple:
        raise ModelError(f"{label} must use an immutable tuple")
    if len(values) > MAX_CANONICAL_EDGES:
        raise ModelError(f"{label} exceed the canonical edge bound")
    for value in values:
        if type(value) is not TypedContentId:
            raise ModelError(f"{label} must contain exact typed IDs")
        value.__post_init__()
        if value.subject_kind != expected_kind:
            raise DeclarationKindMismatchError(f"{label} have the wrong subject kind")
    keys = tuple(value.internal_reference() for value in values)
    if keys != tuple(sorted(set(keys))):
        raise ModelError(f"{label} must be canonical sorted-unique")
    return values


def _profile_reference_sequence(
    values: tuple[TypedContentId, ...],
    *,
    label: str,
) -> tuple[TypedContentId, ...]:
    return _sorted_unique_reference_sequence(
        values,
        label=label,
        expected_kind=SEMANTIC_LANGUAGE_PROFILE_KIND,
    )


def semantic_language_profile_body(
    profile: SemanticLanguageProfile,
) -> DatumRecord:
    if type(profile) is not SemanticLanguageProfile:
        raise ModelError(
            "semantic-language profile has the wrong exact typed shape"
        )
    return profile.body()


def semantic_language_profile_id(
    profile: SemanticLanguageProfile,
    *,
    semantic_regime: PriorMetaId,
) -> SemanticLanguageProfileId:
    if type(profile) is not SemanticLanguageProfile:
        raise ModelError(
            "semantic-language profile has the wrong exact typed shape"
        )
    return profile.identity_for(semantic_regime)


def profiled_semantic_body(
    profile_id: SemanticLanguageProfileId,
    domain_body: Datum,
) -> DatumRecord:
    """Place the exact used language-profile ID in a subject preimage."""

    _require_typed_content_id(profile_id, axis_name="semantic-language profile ID")
    if profile_id.subject_kind != SEMANTIC_LANGUAGE_PROFILE_KIND:
        raise DeclarationKindMismatchError(
            "profiled semantic body names the wrong profile subject kind"
        )
    body = DatumRecord(
        ((0, BytesValue(profile_id.internal_reference())), (1, domain_body))
    )
    encode_datum(body)
    return body


def profiled_content_id(
    subject_kind: str,
    profile_id: SemanticLanguageProfileId,
    domain_body: Datum,
    *,
    semantic_regime: PriorMetaId,
) -> TypedContentId:
    if (
        type(subject_kind) is str
        and subject_kind in PROFILED_FORBIDDEN_SUBJECT_KINDS
    ):
        raise DeclarationKindMismatchError(
            "profiled semantic subjects cannot use a prior-meta or standalone "
            "Foundation subject kind"
        )
    if profile_id.semantic_regime != semantic_regime:
        raise DeclarationKindMismatchError(
            "profiled subject and language profile cross semantic regimes"
        )
    return content_id(
        subject_kind,
        encode_datum(profiled_semantic_body(profile_id, domain_body)),
        semantic_regime=semantic_regime,
    )


def module_declaration_catalogs(
    candidate: SemanticModuleCandidate,
) -> Mapping[str, DatumSeq]:
    """Validate and expose the exact sorted per-kind declaration catalogs."""

    if type(candidate) is not SemanticModuleCandidate:
        raise ModelError("module candidate has the wrong exact typed shape")
    declarations = candidate.local_declarations
    if type(declarations) is not DatumSeq:
        raise ModelError("module local declarations must be a catalog sequence")
    if type(declarations.values) is not tuple:
        raise ModelError("module declaration catalogs must be an immutable sequence")
    if len(declarations.values) > MAX_CANONICAL_EDGES:
        raise ModelError("module declaration catalogs exceed the edge bound")
    result: dict[str, DatumSeq] = {}
    previous: bytes | None = None
    for catalog in declarations.values:
        if type(catalog) is not DatumRecord or type(catalog.fields) is not tuple:
            raise ModelError("module declaration catalog has the wrong shape")
        if len(catalog.fields) != 2:
            raise ModelError("module declaration catalog has the wrong shape")
        if any(type(entry) is not tuple or len(entry) != 2 for entry in catalog.fields):
            raise ModelError("module declaration catalog has the wrong shape")
        if tuple(entry[0] for entry in catalog.fields) != (0, 1) or any(
            type(entry[0]) is not int for entry in catalog.fields
        ):
            raise ModelError("module declaration catalog has the wrong shape")
        fields = dict(catalog.fields)
        kind = fields[0]
        bodies = fields[1]
        if type(kind) is not Symbol or type(bodies) is not DatumSeq:
            raise ModelError("module declaration catalog has the wrong field types")
        if type(bodies.values) is not tuple:
            raise ModelError("module declaration bodies must be an immutable sequence")
        if len(bodies.values) > MAX_CANONICAL_EDGES:
            raise ModelError("module declaration bodies exceed the edge bound")
        encode_datum(kind)
        encode_datum(bodies)
        key = kind.value.encode("ascii")
        if previous is not None and key <= previous:
            raise ModelError(
                "module declaration catalog kinds must be sorted and unique"
            )
        previous = key
        result[kind.value] = bodies
    return result


def profile_declaration_catalogs(
    profile: SemanticLanguageProfile,
) -> Mapping[str, DatumSeq]:
    """Validate profile-local catalogs using the shared exact catalog grammar."""

    if type(profile) is not SemanticLanguageProfile:
        raise ModelError("semantic-language profile has the wrong exact shape")
    probe = SemanticModuleCandidate(
        Symbol("foundation.profile-catalog-grammar"),
        (),
        profile.declaration_catalogs,
    )
    return module_declaration_catalogs(probe)


@dataclass(frozen=True)
class ProfileLocalDeclarationRef:
    declaration_kind: str
    local_ordinal: int


@dataclass(frozen=True)
class ImportedProfileDeclarationRef:
    profile_id: SemanticLanguageProfileId
    declaration_kind: str
    local_ordinal: int


ProfileDeclarationRef: TypeAlias = (
    ProfileLocalDeclarationRef | ImportedProfileDeclarationRef
)


def profile_declaration_ref_datum(reference: ProfileDeclarationRef) -> DatumVariant:
    if type(reference) is ProfileLocalDeclarationRef:
        _axis(reference.declaration_kind)
        if not _is_u64_natural(reference.local_ordinal):
            raise ModelError("profile-local declaration ordinal must be a u64")
        return DatumVariant(
            0,
            DatumRecord(
                (
                    (0, Symbol(reference.declaration_kind)),
                    (1, Nat(reference.local_ordinal)),
                )
            ),
        )
    if type(reference) is ImportedProfileDeclarationRef:
        _require_typed_content_id(
            reference.profile_id,
            axis_name="imported semantic-language profile",
        )
        if reference.profile_id.subject_kind != SEMANTIC_LANGUAGE_PROFILE_KIND:
            raise DeclarationKindMismatchError(
                "imported declaration owner has the wrong profile kind"
            )
        _axis(reference.declaration_kind)
        if not _is_u64_natural(reference.local_ordinal):
            raise ModelError("imported profile declaration ordinal must be a u64")
        return DatumVariant(
            1,
            DatumRecord(
                (
                    (0, BytesValue(reference.profile_id.internal_reference())),
                    (1, Symbol(reference.declaration_kind)),
                    (2, Nat(reference.local_ordinal)),
                )
            ),
        )
    raise ModelError("unknown profile declaration-reference branch")


def resolve_profile_declaration(
    context: EffectiveSemanticContext,
    reference: ProfileDeclarationRef,
) -> Datum:
    """Resolve only local or exact imported coordinates in a closed profile DAG."""

    if type(context) is not EffectiveSemanticContext:
        raise ModelError("effective semantic context has the wrong exact shape")
    authenticated_profiles = dict(context.authenticated_profiles)
    selected = authenticated_profiles.get(context.selected_profile)
    if selected is None or selected != context.selected_profile_body:
        raise ModelError("selected profile is absent from its authenticated closure")
    if type(reference) is ProfileLocalDeclarationRef:
        target = selected
        kind = reference.declaration_kind
        ordinal = reference.local_ordinal
    elif type(reference) is ImportedProfileDeclarationRef:
        if reference.profile_id == context.selected_profile:
            raise DeclarationAdmissionRefusedError(
                "self declarations must use a profile-local reference"
            )
        target = authenticated_profiles.get(reference.profile_id)
        if target is None:
            raise DeclarationAdmissionRefusedError(
                "imported declaration owner is outside the profile closure"
            )
        kind = reference.declaration_kind
        ordinal = reference.local_ordinal
    else:
        raise ModelError("unknown profile declaration-reference branch")
    catalogs = profile_declaration_catalogs(target)
    catalog = catalogs.get(kind)
    if catalog is None or not _is_u64_natural(ordinal) or ordinal >= len(catalog.values):
        raise DeclarationAdmissionRefusedError(
            "profile declaration coordinate is absent"
        )
    return catalog.values[ordinal]


def resolve_module_declaration(
    candidate: SemanticModuleCandidate,
    declaration_kind: str,
    local_ordinal: int,
) -> Datum:
    catalogs = module_declaration_catalogs(candidate)
    catalog = catalogs.get(declaration_kind)
    if catalog is None:
        raise DeclarationAdmissionRefusedError("module declaration kind is absent")
    if not _is_u64_natural(local_ordinal) or local_ordinal >= len(catalog.values):
        raise DeclarationAdmissionRefusedError("module declaration ordinal is absent")
    return catalog.values[local_ordinal]


def authenticate_value_type_reference(
    value_type: ValueType,
    modules: Mapping[TypedContentId, SemanticModuleCandidate],
    *,
    semantic_regime: PriorMetaId,
) -> None:
    """Resolve the exact domain declaration for a finite structural type."""

    if value_type.domain.semantic_regime != semantic_regime:
        raise DeclarationKindMismatchError(
            "value type crosses the algorithm semantic regime"
        )
    owner = value_type.domain.owner
    if isinstance(owner, PriorMetaId):
        if owner.subject_kind != SEMANTIC_REGIME_KIND:
            raise DeclarationKindMismatchError(
                "root value domain owner has the wrong prior-meta kind"
            )
        if owner != semantic_regime:
            raise DeclarationKindMismatchError(
                "root value domain names another semantic regime"
            )
        if value_type.domain.declaration_kind != ROOT_VALUE_DOMAIN_KIND:
            raise DeclarationKindMismatchError(
                "root value domain has the wrong declaration kind"
            )
        schema_class = ROOT_VALUE_SCHEMA_CLASSES.get(value_type.domain.local_ordinal)
        if schema_class is None:
            raise DeclarationAdmissionRefusedError(
                "root value-domain ordinal is absent from the selected catalog"
            )
        if type(value_type.schema) is not schema_class:
            raise DeclarationKindMismatchError(
                "root value-domain ordinal disagrees with the structural schema"
            )
    else:
        if owner.subject_kind != SEMANTIC_MODULE_KIND:
            raise DeclarationKindMismatchError(
                "extension value-domain owner is not a semantic module"
            )
        candidate = modules.get(owner)
        if candidate is None:
            raise ModelError("extension value-domain owner was not authenticated")
        authenticate_module_value_domain_declaration(
            candidate,
            value_type.domain.declaration_kind,
            value_type.domain.local_ordinal,
        )

    nested: tuple[ValueType, ...] = ()
    if isinstance(value_type.schema, SeqSchema):
        nested = (value_type.schema.element,)
    elif isinstance(value_type.schema, RecordSchema):
        nested = tuple(child for _, child in value_type.schema.fields)
    elif isinstance(value_type.schema, VariantSchema):
        nested = tuple(child for _, child in value_type.schema.cases)
    for child in nested:
        authenticate_value_type_reference(
            child,
            modules,
            semantic_regime=semantic_regime,
        )


def authenticated_module_import_scope(
    owner: TypedContentId,
    modules: Mapping[TypedContentId, SemanticModuleCandidate],
) -> frozenset[TypedContentId]:
    """Return only the declaring module's authenticated transitive imports."""

    owner_candidate = modules.get(owner)
    if owner_candidate is None:
        raise ModelError("declaring module was not authenticated")
    scope: set[TypedContentId] = set()
    pending = list(owner_candidate.imports)
    while pending:
        current = pending.pop()
        if current in scope:
            continue
        candidate = modules.get(current)
        if candidate is None:
            raise ModelError("declaring module import closure is incomplete")
        scope.add(current)
        pending.extend(candidate.imports)
    return frozenset(scope)


def authenticate_failure_reference(
    failure_type: SemanticFailureType,
    modules: Mapping[TypedContentId, SemanticModuleCandidate],
    *,
    semantic_regime: PriorMetaId,
) -> None:
    validate_semantic_failure_type_shape(failure_type)
    if failure_type.declaration_module.subject_kind != SEMANTIC_MODULE_KIND:
        raise DeclarationKindMismatchError(
            "semantic failure owner is not a semantic module"
        )
    if failure_type.declaration_module.semantic_regime != semantic_regime:
        raise DeclarationKindMismatchError(
            "semantic failure declaration crosses the selected regime"
        )
    candidate = modules.get(failure_type.declaration_module)
    if candidate is None:
        raise ModelError("semantic failure owner was not authenticated")
    body = resolve_module_declaration(
        candidate,
        "semantic-failure",
        failure_type.local_ordinal,
    )
    if not isinstance(body, DatumRecord) or tuple(
        ordinal for ordinal, _ in body.fields
    ) != (0, 1):
        raise ModelError("semantic failure declaration has the wrong shape")
    fields = dict(body.fields)
    if not isinstance(fields[0], Symbol):
        raise ModelError("semantic failure declaration name is not a symbol")
    lifted_payload_type = lift_declaration_value_type_datum(
        fields[1],
        failure_type.declaration_module,
        modules,
        semantic_regime=semantic_regime,
    )
    if lifted_payload_type != failure_type.payload_type:
        raise DeclarationAdmissionRefusedError(
            "semantic failure payload disagrees with its module declaration"
        )


def resolve_value_type_declaration_coordinates(
    value_type: ValueType,
    modules: Mapping[TypedContentId, SemanticModuleCandidate],
    *,
    semantic_regime: PriorMetaId,
) -> None:
    """Resolve declaration coordinates without interpreting selected bodies."""

    if type(value_type) is not ValueType or type(value_type.domain) is not ValueDomain:
        raise ModelError("value type has the wrong exact typed shape")
    domain = value_type.domain
    if domain.semantic_regime != semantic_regime:
        raise DeclarationKindMismatchError(
            "value type crosses the algorithm semantic regime"
        )
    owner = domain.owner
    if type(owner) is PriorMetaId:
        if owner.subject_kind != SEMANTIC_REGIME_KIND:
            raise DeclarationKindMismatchError(
                "root value domain owner has the wrong prior-meta kind"
            )
        if owner != semantic_regime:
            raise DeclarationKindMismatchError(
                "root value domain names another semantic regime"
            )
        if domain.declaration_kind != ROOT_VALUE_DOMAIN_KIND:
            raise DeclarationKindMismatchError(
                "root value domain has the wrong declaration kind"
            )
        if domain.local_ordinal not in ROOT_VALUE_SCHEMA_CLASSES:
            raise DeclarationAdmissionRefusedError(
                "root value-domain ordinal is absent from the selected catalog"
            )
    else:
        if owner.subject_kind != SEMANTIC_MODULE_KIND:
            raise DeclarationKindMismatchError(
                "extension value-domain owner is not a semantic module"
            )
        if domain.declaration_kind != MODULE_VALUE_DOMAIN_KIND:
            raise DeclarationKindMismatchError(
                "extension value domain has the wrong declaration kind"
            )
        candidate = modules.get(owner)
        if candidate is None:
            raise ModelError("extension value-domain owner was not authenticated")
        resolve_module_declaration(
            candidate,
            domain.declaration_kind.value,
            domain.local_ordinal,
        )
    for child in nested_value_types(value_type):
        resolve_value_type_declaration_coordinates(
            child,
            modules,
            semantic_regime=semantic_regime,
        )


def resolve_failure_declaration_coordinates(
    failure_type: SemanticFailureType,
    modules: Mapping[TypedContentId, SemanticModuleCandidate],
    *,
    semantic_regime: PriorMetaId,
) -> None:
    """Resolve a failure coordinate and its payload coordinates only."""

    validate_semantic_failure_type_shape(failure_type)
    if failure_type.declaration_module.subject_kind != SEMANTIC_MODULE_KIND:
        raise DeclarationKindMismatchError(
            "semantic failure owner is not a semantic module"
        )
    if failure_type.declaration_module.semantic_regime != semantic_regime:
        raise DeclarationKindMismatchError(
            "semantic failure declaration crosses the algorithm semantic regime"
        )
    if failure_type.payload_type.domain.semantic_regime != semantic_regime:
        raise DeclarationKindMismatchError(
            "semantic failure payload crosses the algorithm semantic regime"
        )
    candidate = modules.get(failure_type.declaration_module)
    if candidate is None:
        raise ModelError("semantic failure owner was not authenticated")
    resolve_module_declaration(
        candidate,
        "semantic-failure",
        failure_type.local_ordinal,
    )
    resolve_value_type_declaration_coordinates(
        failure_type.payload_type,
        modules,
        semantic_regime=semantic_regime,
    )


def _walk_algorithm_declaration_references(
    algorithm: CanonicalAlgorithm,
    modules: Mapping[TypedContentId, SemanticModuleCandidate],
    *,
    ledger: AuthenticationLedger | None = None,
    resolve_only: bool,
) -> None:
    """Walk explicit declaration material at one selected boundary."""

    active: set[int] = set()

    def value_type(item: ValueType) -> None:
        if resolve_only:
            resolve_value_type_declaration_coordinates(
                item,
                modules,
                semantic_regime=algorithm.semantic_regime,
            )
        else:
            authenticate_value_type_reference(
                item,
                modules,
                semantic_regime=algorithm.semantic_regime,
            )

    def failure(item: SemanticFailureType) -> None:
        if resolve_only:
            resolve_failure_declaration_coordinates(
                item,
                modules,
                semantic_regime=algorithm.semantic_regime,
            )
        else:
            authenticate_failure_reference(
                item,
                modules,
                semantic_regime=algorithm.semantic_regime,
            )

    def visit(term: Term) -> None:
        marker = id(term)
        if marker in active:
            raise ModelError("cyclic host object is not a term")
        active.add(marker)
        try:
            if isinstance(term, Literal):
                value_type(term.value.value_type)
            elif isinstance(term, Variable):
                value_type(term.value_type)
            elif isinstance(term, Let):
                visit(term.bound)
                visit(term.body)
            elif isinstance(term, RecordConstruct):
                for _, child in term.fields:
                    visit(child)
            elif isinstance(term, Project):
                visit(term.record)
            elif isinstance(term, Inject):
                value_type(term.sum_type)
                visit(term.payload)
            elif isinstance(term, Case):
                visit(term.scrutinee)
                for _, branch in term.branches:
                    visit(branch)
            elif isinstance(term, Conditional):
                visit(term.condition)
                visit(term.when_true)
                visit(term.when_false)
            elif isinstance(term, SequenceConstruct):
                value_type(term.element_type)
                for child in term.elements:
                    visit(child)
            elif isinstance(term, SequenceLength):
                visit(term.source)
            elif isinstance(term, Fail):
                failure(term.failure_type)
                value_type(term.success_type)
                visit(term.payload)
            elif isinstance(term, StrictIndex):
                failure(term.failure_type)
                visit(term.source)
                visit(term.index)
            elif isinstance(term, BoundedAppend):
                failure(term.failure_type)
                visit(term.source)
                visit(term.element)
            elif isinstance(term, PrimitiveCall):
                if resolve_only:
                    if type(term.primitive) is not SemanticPrimitiveRef:
                        raise ModelError(
                            "primitive reference has the wrong exact typed shape"
                        )
                    term.primitive.__post_init__()
                    if (
                        term.primitive.identifier.semantic_regime
                        != algorithm.semantic_regime
                        or term.primitive.declaration_module.semantic_regime
                        != algorithm.semantic_regime
                    ):
                        raise DeclarationKindMismatchError(
                            "primitive coordinate crosses the algorithm semantic regime"
                        )
                    authenticate_primitive_reference(term.primitive, ledger=ledger)
                    candidate = modules.get(term.primitive.declaration_module)
                    if candidate is None:
                        raise ModelError(
                            "primitive declaration owner was not authenticated"
                        )
                    resolve_module_declaration(
                        candidate,
                        "semantic-primitive",
                        term.primitive.local_ordinal,
                    )
                else:
                    candidate = modules.get(term.primitive.declaration_module)
                    if candidate is None:
                        raise ModelError(
                            "primitive declaration owner was not authenticated"
                        )
                    authenticate_module_primitive_declaration_body(
                        candidate,
                        term.primitive.local_ordinal,
                        modules,
                        semantic_regime=algorithm.semantic_regime,
                    )
                for child in term.arguments:
                    visit(child)
            elif isinstance(term, BoundedIterate):
                if isinstance(term.source, SequenceIterationSource):
                    visit(term.source.sequence)
                elif isinstance(term.source, RangeIterationSource):
                    visit(term.source.exclusive_bound)
                else:
                    raise ModelError("unknown bounded-iteration source")
                visit(term.initial_state)
                visit(term.body)
            else:
                raise ModelError(f"unknown term constructor: {type(term)!r}")
        finally:
            active.remove(marker)

    for input_type in algorithm.inputs:
        value_type(input_type)
    visit(algorithm.term)


def resolve_algorithm_declaration_coordinates(
    algorithm: CanonicalAlgorithm,
    modules: Mapping[TypedContentId, SemanticModuleCandidate],
    *,
    ledger: AuthenticationLedger | None = None,
) -> None:
    """Complete precedence boundary 6 without kind-specific interpretation."""

    _walk_algorithm_declaration_references(
        algorithm,
        modules,
        ledger=ledger,
        resolve_only=True,
    )


def _interpret_algorithm_declaration_references(
    algorithm: CanonicalAlgorithm,
    modules: Mapping[TypedContentId, SemanticModuleCandidate],
    *,
    ledger: AuthenticationLedger | None = None,
) -> None:
    """Interpret value/failure bodies after all coordinates have resolved.

    Primitive coordinates are resolved by boundary 6.  Boundary 7 first forms
    each recognized module body in its exact declaration grammar; evaluator
    support and denotation lookup remain a later part of that boundary.
    """

    _walk_algorithm_declaration_references(
        algorithm,
        modules,
        ledger=ledger,
        resolve_only=False,
    )


def authenticate_algorithm_declaration_references(
    algorithm: CanonicalAlgorithm,
    modules: Mapping[TypedContentId, SemanticModuleCandidate],
    *,
    ledger: AuthenticationLedger | None = None,
) -> None:
    """Resolve all coordinates, then interpret every supported body kind."""

    resolve_algorithm_declaration_coordinates(
        algorithm,
        modules,
        ledger=ledger,
    )
    _interpret_algorithm_declaration_references(
        algorithm,
        modules,
        ledger=ledger,
    )


FIXTURE_EXTENSION_MODULE_CANDIDATE = SemanticModuleCandidate(
    Symbol("zkc.k1.fixture-primitives"),
    (),
    FIXTURE_EXTENSION_LOCAL_DECLARATIONS,
)
if FIXTURE_EXTENSION_MODULE_CANDIDATE.identity != FIXTURE_EXTENSION_MODULE_ID:
    raise AssertionError("fixture module descriptor and candidate disagree")
FIXTURE_MODULE_PREIMAGES: Mapping[TypedContentId, SemanticModuleCandidate] = (
    MappingProxyType({FIXTURE_EXTENSION_MODULE_ID: FIXTURE_EXTENSION_MODULE_CANDIDATE})
)


@dataclass(frozen=True)
class AuthenticatedModuleClosure:
    nodes: int
    edges: int


@dataclass(frozen=True)
class EncodedValue:
    value_type: ValueType
    body: bytes


class _Control(Exception):
    outcome: Outcome

    def __init__(self, outcome: Outcome, code: str, detail: str) -> None:
        super().__init__(detail)
        self.outcome = outcome
        self.code = code
        self.detail = detail


def authenticate_module_closure(
    direct_dependencies: tuple[TypedContentId, ...],
    supplied: dict[TypedContentId, SemanticModuleCandidate],
    *,
    semantic_regime: PriorMetaId,
    ledger: AuthenticationLedger | None = None,
) -> AuthenticatedModuleClosure:
    if type(direct_dependencies) is not tuple:
        raise _Control(
            Outcome.MALFORMED,
            "K1-MALFORMED-MODULE-ROOTS",
            "direct module dependencies have the wrong exact typed shape",
        )
    if len(direct_dependencies) > MAX_MODULE_NODES:
        raise _Control(
            Outcome.DETERMINISTIC_LIMIT_EXCEEDED,
            "K1-LIMIT-MODULE-ROOTS",
            "direct module dependencies exceed the fixed node bound",
        )
    if any(type(item) is not TypedContentId for item in direct_dependencies):
        raise _Control(
            Outcome.MALFORMED,
            "K1-MALFORMED-MODULE-ROOTS",
            "direct module dependencies must contain exact typed IDs",
        )
    if type(semantic_regime) is not PriorMetaId:
        raise _Control(
            Outcome.MALFORMED,
            "K1-MALFORMED-MODULE-REGIME",
            "module-closure semantic-regime must be an exact PriorMetaId",
        )
    try:
        semantic_regime.__post_init__()
    except CanonicalError as error:
        raise _Control(
            Outcome.MALFORMED,
            "K1-MALFORMED-MODULE-REGIME",
            str(error),
        ) from error
    if semantic_regime.subject_kind != SEMANTIC_REGIME_KIND:
        raise _Control(
            Outcome.KIND_MISMATCH,
            "K1-KIND-MODULE-REGIME",
            "module closure regime coordinate has the wrong prior-meta kind",
        )
    if semantic_regime != SEMANTIC_REGIME_ID:
        raise _Control(
            Outcome.UNSUPPORTED,
            "K1-UNSUPPORTED-MODULE-REGIME",
            "module closure uses an unsupported semantic regime",
        )
    if type(supplied) is not dict:
        raise _Control(
            Outcome.MALFORMED,
            "K1-MALFORMED-MODULE-BUNDLE",
            "module preimages must use an exact built-in dict carrier",
        )
    if len(supplied) > MAX_MODULE_BUNDLE_ENTRIES:
        raise _Control(
            Outcome.DETERMINISTIC_LIMIT_EXCEEDED,
            "K1-LIMIT-MODULE-BUNDLE-ENTRIES",
            "module-preimage bundle exceeds the fixed entry bound",
        )
    if any(type(identifier) is not TypedContentId for identifier in supplied):
        raise _Control(
            Outcome.MALFORMED,
            "K1-MALFORMED-MODULE-BUNDLE",
            "module-preimage map keys must be exact TypedContentId values",
        )
    try:
        for identifier in supplied:
            identifier.__post_init__()
    except CanonicalError as error:
        raise _Control(
            Outcome.MALFORMED,
            "K1-MALFORMED-MODULE-BUNDLE",
            f"module-preimage map key is malformed: {error}",
        ) from error
    for identifier in supplied:
        if identifier.subject_kind != SEMANTIC_MODULE_KIND:
            raise _Control(
                Outcome.KIND_MISMATCH,
                "K1-KIND-MODULE",
                "module-preimage map key has the wrong subject kind",
            )
        if identifier.semantic_regime != semantic_regime:
            raise _Control(
                Outcome.KIND_MISMATCH,
                "K1-KIND-MODULE-REGIME",
                "module-preimage map key crosses semantic regimes",
            )
    supplied = dict(supplied)
    supplied_size = len(supplied)
    try:
        direct_keys = tuple(item.internal_reference() for item in direct_dependencies)
    except CanonicalError as error:
        raise _Control(
            Outcome.MALFORMED,
            "K1-MALFORMED-MODULE-ROOTS",
            f"direct module dependency is malformed: {error}",
        ) from error
    if direct_keys != tuple(sorted(set(direct_keys))):
        raise _Control(
            Outcome.MALFORMED,
            "K1-MALFORMED-MODULE-ROOTS",
            "direct module dependencies are not canonical sorted-unique",
        )

    active: set[TypedContentId] = set()
    discovered: set[TypedContentId] = set()
    visited: set[TypedContentId] = set()
    edges = 0

    def authenticate_candidate(
        identifier: TypedContentId,
    ) -> SemanticModuleCandidate:
        if identifier.subject_kind != SEMANTIC_MODULE_KIND:
            raise _Control(
                Outcome.KIND_MISMATCH,
                "K1-KIND-MODULE",
                "module dependency has the wrong subject kind",
            )
        if identifier.semantic_regime != semantic_regime:
            raise _Control(
                Outcome.KIND_MISMATCH,
                "K1-KIND-MODULE-REGIME",
                "semantic-module import crosses regime roots",
            )
        candidate = supplied.get(identifier)
        if candidate is None:
            raise _Control(
                Outcome.MISSING_DEPENDENCY,
                "K1-MISSING-MODULE",
                "required semantic-module preimage was not supplied",
            )
        if type(candidate) is not SemanticModuleCandidate:
            raise _Control(
                Outcome.MALFORMED,
                "K1-MALFORMED-MODULE-PREIMAGE",
                "module candidate has the wrong typed shape",
            )
        try:
            candidate_body = candidate.body()
            authenticate_content_id(
                identifier,
                candidate_body,
                FOUNDATION_PRIOR_META_PREIMAGES,
                ledger=ledger,
            )
        except HashBindingConflictError as error:
            raise _Control(
                Outcome.CHECKER_FAILURE,
                "FOUNDATION-HASH-BINDING-CONFLICT",
                str(error),
            ) from error
        except (CanonicalError, ModelError, AttributeError, TypeError) as error:
            raise _Control(
                Outcome.MALFORMED,
                "K1-MALFORMED-MODULE-PREIMAGE",
                f"module candidate is not canonical: {error}",
            ) from error
        try:
            module_declaration_catalogs(candidate)
        except (CanonicalError, ModelError, AttributeError, TypeError) as error:
            raise _Control(
                Outcome.MALFORMED,
                "K1-MALFORMED-MODULE-PREIMAGE",
                f"authenticated module has malformed kind-specific structure: {error}",
            ) from error
        try:
            import_keys = tuple(item.internal_reference() for item in candidate.imports)
        except (CanonicalError, AttributeError, TypeError) as error:
            raise _Control(
                Outcome.MALFORMED,
                "K1-MALFORMED-MODULE-IMPORTS",
                f"module imports are not typed references: {error}",
            ) from error
        if import_keys != tuple(sorted(set(import_keys))):
            raise _Control(
                Outcome.MALFORMED,
                "K1-MALFORMED-MODULE-IMPORTS",
                "module imports are not canonical sorted-unique",
            )
        return candidate

    for root in direct_dependencies:
        events: list[tuple[str, TypedContentId]] = [("enter", root)]
        while events:
            event, identifier = events.pop()
            if event == "exit":
                active.remove(identifier)
                visited.add(identifier)
                continue
            if identifier in active:
                # A cyclic target still authenticates before the cycle is
                # classified.  Otherwise a forged candidate could select the
                # observed refusal without first proving its own preimage.
                authenticate_candidate(identifier)
                raise _Control(
                    Outcome.REFUSED,
                    "K1-REFUSED-MODULE-CYCLE",
                    "semantic-module imports contain a cycle",
                )
            if identifier in visited:
                continue
            if identifier not in discovered:
                discovered.add(identifier)
                if len(discovered) > MAX_MODULE_NODES:
                    raise _Control(
                        Outcome.DETERMINISTIC_LIMIT_EXCEEDED,
                        "K1-LIMIT-MODULE-NODES",
                        "module closure exceeds the fixed node bound",
                    )
            candidate = authenticate_candidate(identifier)
            # Import edges are authoritative only after the candidate itself
            # has authenticated. Otherwise a forged preimage could select
            # which missing-dependency or cycle outcome is observed.
            next_edges = edges + len(candidate.imports)
            if next_edges > MAX_MODULE_EDGES:
                raise _Control(
                    Outcome.DETERMINISTIC_LIMIT_EXCEEDED,
                    "K1-LIMIT-MODULE-EDGES",
                    "module closure exceeds the fixed edge bound",
                )
            edges = next_edges
            active.add(identifier)
            events.append(("exit", identifier))
            for imported in reversed(candidate.imports):
                events.append(("enter", imported))
    if supplied_size != len(visited):
        raise _Control(
            Outcome.REFUSED,
            "K1-REFUSED-EXTRA-MODULE",
            "an unreferenced semantic-module preimage was supplied",
        )
    return AuthenticatedModuleClosure(len(visited), edges)


@dataclass(frozen=True)
class EffectiveSemanticContext:
    """The exact profile-qualified context authenticated for one subject."""

    semantic_regime: PriorMetaId
    selected_profile: SemanticLanguageProfileId
    selected_profile_body: SemanticLanguageProfile
    authenticated_profiles: tuple[
        tuple[SemanticLanguageProfileId, SemanticLanguageProfile], ...
    ]


def effective_semantic_context(
    selected_profile: SemanticLanguageProfileId,
    supplied_profiles: ProfilePreimageBundle,
    *,
    semantic_regime: PriorMetaId,
    ledger: AuthenticationLedger | None = None,
) -> EffectiveSemanticContext:
    """Authenticate and snapshot one exact no-extra profile-import closure."""

    if type(semantic_regime) is not PriorMetaId:
        raise _Control(
            Outcome.MALFORMED,
            "K1-MALFORMED-PROFILE-REGIME",
            "profile closure regime must be an exact PriorMetaId",
        )
    try:
        semantic_regime.__post_init__()
    except CanonicalError as error:
        raise _Control(
            Outcome.MALFORMED,
            "K1-MALFORMED-PROFILE-REGIME",
            str(error),
        ) from error
    if semantic_regime.subject_kind != SEMANTIC_REGIME_KIND:
        raise _Control(
            Outcome.KIND_MISMATCH,
            "K1-KIND-PROFILE-REGIME",
            "profile closure regime coordinate has the wrong prior-meta kind",
        )
    if semantic_regime != SEMANTIC_REGIME_ID:
        raise _Control(
            Outcome.UNSUPPORTED,
            "K1-UNSUPPORTED-PROFILE-REGIME",
            "profile closure uses an unsupported semantic regime",
        )

    if type(selected_profile) is not TypedContentId:
        raise _Control(
            Outcome.MALFORMED,
            "K1-MALFORMED-PROFILE-ROOT",
            "selected profile must be an exact typed ID",
        )
    try:
        selected_profile.__post_init__()
    except CanonicalError as error:
        raise _Control(
            Outcome.MALFORMED,
            "K1-MALFORMED-PROFILE-ROOT",
            str(error),
        ) from error
    if selected_profile.subject_kind != SEMANTIC_LANGUAGE_PROFILE_KIND:
        raise _Control(
            Outcome.KIND_MISMATCH,
            "K1-KIND-PROFILE",
            "selected language profile has the wrong subject kind",
        )
    if selected_profile.semantic_regime != semantic_regime:
        raise _Control(
            Outcome.KIND_MISMATCH,
            "K1-KIND-PROFILE-REGIME",
            "selected language profile crosses semantic regimes",
        )
    if type(supplied_profiles) is not dict:
        raise _Control(
            Outcome.MALFORMED,
            "K1-MALFORMED-PROFILE-BUNDLE",
            "profile preimages must use an exact built-in dict",
        )
    if len(supplied_profiles) > MAX_PROFILE_BUNDLE_ENTRIES:
        raise _Control(
            Outcome.DETERMINISTIC_LIMIT_EXCEEDED,
            "K1-LIMIT-PROFILE-BUNDLE",
            "profile preimages exceed the bundle-entry bound",
        )
    if any(type(profile_id) is not TypedContentId for profile_id in supplied_profiles):
        raise _Control(
            Outcome.MALFORMED,
            "K1-MALFORMED-PROFILE-BUNDLE",
            "profile-preimage keys must be exact typed IDs",
        )
    try:
        for profile_id in supplied_profiles:
            profile_id.__post_init__()
    except CanonicalError as error:
        raise _Control(
            Outcome.MALFORMED,
            "K1-MALFORMED-PROFILE-BUNDLE",
            str(error),
        ) from error
    for profile_id in supplied_profiles:
        if profile_id.subject_kind != SEMANTIC_LANGUAGE_PROFILE_KIND:
            raise _Control(
                Outcome.KIND_MISMATCH,
                "K1-KIND-PROFILE",
                "profile-preimage key has the wrong subject kind",
            )
        if profile_id.semantic_regime != semantic_regime:
            raise _Control(
                Outcome.KIND_MISMATCH,
                "K1-KIND-PROFILE-REGIME",
                "profile-preimage key crosses semantic regimes",
            )
    supplied_profiles = dict(supplied_profiles)

    active: set[SemanticLanguageProfileId] = set()
    discovered: set[SemanticLanguageProfileId] = set()
    visited: set[SemanticLanguageProfileId] = set()
    profile_edges = 0

    def authenticate_profile(profile_id: SemanticLanguageProfileId) -> None:
        try:
            _require_typed_content_id(
                profile_id,
                axis_name="semantic-language profile dependency",
            )
        except CanonicalError as error:
            raise _Control(
                Outcome.MALFORMED,
                "K1-MALFORMED-PROFILE-REF",
                str(error),
            ) from error
        if profile_id.subject_kind != SEMANTIC_LANGUAGE_PROFILE_KIND:
            raise _Control(
                Outcome.KIND_MISMATCH,
                "K1-KIND-PROFILE",
                "profile dependency has the wrong subject kind",
            )
        if profile_id.semantic_regime != semantic_regime:
            raise _Control(
                Outcome.KIND_MISMATCH,
                "K1-KIND-PROFILE-REGIME",
                "profile dependency crosses semantic regimes",
            )
        profile = supplied_profiles.get(profile_id)
        if profile is None:
            raise _Control(
                Outcome.MISSING_DEPENDENCY,
                "K1-MISSING-PROFILE",
                "required semantic-language profile is missing",
            )
        if type(profile) is not SemanticLanguageProfile:
            raise _Control(
                Outcome.MALFORMED,
                "K1-MALFORMED-PROFILE-PREIMAGE",
                "profile preimage has the wrong exact typed shape",
            )
        try:
            body = encode_datum(profile.body())
            authenticate_content_id(
                profile_id,
                body,
                FOUNDATION_PRIOR_META_PREIMAGES,
                ledger=ledger,
            )
        except HashBindingConflictError as error:
            raise _Control(
                Outcome.CHECKER_FAILURE,
                "FOUNDATION-HASH-BINDING-CONFLICT",
                str(error),
            ) from error
        except DeclarationKindMismatchError as error:
            raise _Control(
                Outcome.KIND_MISMATCH,
                "K1-KIND-PROFILE-DEPENDENCY",
                str(error),
            ) from error
        except (CanonicalError, ModelError, AttributeError, TypeError) as error:
            raise _Control(
                Outcome.MALFORMED,
                "K1-MALFORMED-PROFILE-PREIMAGE",
                str(error),
            ) from error
        for imported in profile.profile_imports:
            if imported.semantic_regime != semantic_regime:
                raise _Control(
                    Outcome.KIND_MISMATCH,
                    "K1-KIND-PROFILE-REGIME",
                    "profile import crosses semantic regimes",
                )

    events: list[tuple[str, SemanticLanguageProfileId]] = [
        ("enter", selected_profile)
    ]
    while events:
        event, profile_id = events.pop()
        if event == "exit":
            active.remove(profile_id)
            visited.add(profile_id)
            continue
        if profile_id in active:
            authenticate_profile(profile_id)
            raise _Control(
                Outcome.REFUSED,
                "K1-REFUSED-PROFILE-CYCLE",
                "semantic-language profile imports contain a cycle",
            )
        if profile_id in visited:
            continue
        if profile_id not in discovered:
            discovered.add(profile_id)
            if len(discovered) > MAX_PROFILE_NODES:
                raise _Control(
                    Outcome.DETERMINISTIC_LIMIT_EXCEEDED,
                    "K1-LIMIT-PROFILE-NODES",
                    "profile closure exceeds the node bound",
                )
        authenticate_profile(profile_id)
        profile = supplied_profiles[profile_id]
        next_profile_edges = profile_edges + len(profile.profile_imports)
        if next_profile_edges > MAX_PROFILE_EDGES:
            raise _Control(
                Outcome.DETERMINISTIC_LIMIT_EXCEEDED,
                "K1-LIMIT-PROFILE-EDGES",
                "profile closure exceeds the edge bound",
            )
        profile_edges = next_profile_edges
        active.add(profile_id)
        events.append(("exit", profile_id))
        for imported in reversed(profile.profile_imports):
            events.append(("enter", imported))

    if set(supplied_profiles) != visited:
        raise _Control(
            Outcome.REFUSED,
            "K1-REFUSED-EXTRA-PROFILE",
            "an unreferenced semantic-language profile preimage was supplied",
        )
    selected_profile_body = supplied_profiles[selected_profile]
    return EffectiveSemanticContext(
        semantic_regime,
        selected_profile,
        selected_profile_body,
        tuple(
            (profile_id, supplied_profiles[profile_id])
            for profile_id in sorted(
                visited,
                key=lambda item: item.internal_reference(),
            )
        ),
    )


def authenticate_profiled_semantic_content(
    identifier: TypedContentId,
    selected_profile: SemanticLanguageProfileId,
    domain_body: Datum,
    supplied_profiles: dict[SemanticLanguageProfileId, SemanticLanguageProfile],
    *,
    supported_profiles: tuple[SemanticLanguageProfileId, ...],
    ledger: AuthenticationLedger | None = None,
) -> EffectiveSemanticContext:
    """Authenticate profile closure, exact support, then the subject ID."""

    try:
        _require_typed_content_id(identifier, axis_name="profiled semantic subject")
    except CanonicalError as error:
        raise _Control(
            Outcome.MALFORMED,
            "K1-MALFORMED-PROFILED-SUBJECT",
            str(error),
        ) from error
    if identifier.subject_kind in PROFILED_FORBIDDEN_SUBJECT_KINDS:
        raise _Control(
            Outcome.KIND_MISMATCH,
            "K1-KIND-PROFILED-SUBJECT",
            "profiled semantic subjects cannot use a prior-meta or standalone "
            "Foundation subject kind",
        )
    context = effective_semantic_context(
        selected_profile,
        supplied_profiles,
        semantic_regime=identifier.semantic_regime,
        ledger=ledger,
    )
    try:
        supported = _profile_reference_sequence(
            supported_profiles,
            label="evaluator-supported semantic-language profiles",
        )
    except DeclarationKindMismatchError as error:
        raise _Control(
            Outcome.KIND_MISMATCH,
            "K1-KIND-PROFILE-SUPPORT",
            str(error),
        ) from error
    except (CanonicalError, ModelError, AttributeError, TypeError) as error:
        raise _Control(
            Outcome.MALFORMED,
            "K1-MALFORMED-PROFILE-SUPPORT",
            str(error),
        ) from error
    if any(
        profile.semantic_regime != identifier.semantic_regime
        for profile in supported
    ):
        raise _Control(
            Outcome.KIND_MISMATCH,
            "K1-KIND-PROFILE-SUPPORT-REGIME",
            "evaluator profile support crosses semantic regimes",
        )
    if selected_profile not in supported:
        raise _Control(
            Outcome.UNSUPPORTED,
            "K1-UNSUPPORTED-PROFILE",
            "evaluator does not support the exact semantic-language profile",
        )
    supported_subject_kinds = tuple(
        item.value for item in context.selected_profile_body.supported_subject_kinds
    )
    if identifier.subject_kind not in supported_subject_kinds:
        raise _Control(
            Outcome.REFUSED,
            "K1-REFUSED-PROFILE-SUBJECT-KIND",
            "selected language profile does not support the subject kind",
        )
    try:
        body = encode_datum(profiled_semantic_body(selected_profile, domain_body))
        authenticate_content_id(
            identifier,
            body,
            FOUNDATION_PRIOR_META_PREIMAGES,
            ledger=ledger,
        )
    except HashBindingConflictError as error:
        raise _Control(
            Outcome.CHECKER_FAILURE,
            "FOUNDATION-HASH-BINDING-CONFLICT",
            str(error),
        ) from error
    except (CanonicalError, ModelError, AttributeError, TypeError) as error:
        raise _Control(
            Outcome.MALFORMED,
            "K1-MALFORMED-PROFILED-SUBJECT",
            str(error),
        ) from error
    return context


def semantic_contexts_are_identical(
    left: EffectiveSemanticContext,
    right: EffectiveSemanticContext,
) -> bool:
    """The only intrinsic v0 compatibility relation is exact equality."""

    if (
        type(left) is not EffectiveSemanticContext
        or type(right) is not EffectiveSemanticContext
    ):
        raise ModelError("effective semantic context has the wrong exact shape")
    return left == right


def _content_ref_datum(identifier: TypedContentId) -> BytesValue:
    _require_typed_content_id(identifier, axis_name="authority-envelope reference")
    return BytesValue(identifier.internal_reference())


@dataclass(frozen=True)
class OwnerCapabilityRequirement:
    """One inert reference to the owner's complete profiled requirement."""

    owner_domain: Symbol
    capability_family: Symbol
    owner_requirement: TypedContentId

    def body(self) -> DatumRecord:
        if type(self) is not OwnerCapabilityRequirement:
            raise ModelError("owner capability requirement has the wrong shape")
        if (
            type(self.owner_domain) is not Symbol
            or type(self.capability_family) is not Symbol
        ):
            raise ModelError("capability requirement owner and family must be symbols")
        _require_typed_content_id(
            self.owner_requirement,
            axis_name="owner capability-requirement identity",
        )
        return DatumRecord(
            (
                (0, self.owner_domain),
                (1, self.capability_family),
                (2, _content_ref_datum(self.owner_requirement)),
            )
        )


@dataclass(frozen=True)
class BoundOwnerOperationPolicy:
    """Reference carrier for the durable ``BoundTo`` disposition."""

    owner_policy_binding: TypedContentId


@dataclass(frozen=True)
class OwnerDefinesNoOperationPolicy:
    """Reference carrier for durable ``OwnerDefinesNoPolicy``."""

    owner_no_policy_declaration: TypedContentId


OwnerOperationPolicyDisposition: TypeAlias = (
    BoundOwnerOperationPolicy | OwnerDefinesNoOperationPolicy
)


def owner_operation_policy_disposition_body(
    disposition: OwnerOperationPolicyDisposition,
) -> DatumVariant:
    if type(disposition) is BoundOwnerOperationPolicy:
        _require_typed_content_id(
            disposition.owner_policy_binding,
            axis_name="owner operation-policy binding",
        )
        return DatumVariant(
            0,
            _content_ref_datum(disposition.owner_policy_binding),
        )
    if type(disposition) is OwnerDefinesNoOperationPolicy:
        _require_typed_content_id(
            disposition.owner_no_policy_declaration,
            axis_name="owner no-policy declaration",
        )
        return DatumVariant(
            1,
            _content_ref_datum(disposition.owner_no_policy_declaration),
        )
    raise ModelError("unknown owner operation-policy disposition")


@dataclass(frozen=True)
class PortableSourceAuthorityBinding:
    """Exact portable metadata that carries no owner capability."""

    owner_domain: Symbol
    capability_family: Symbol
    owner_source_coordinate: TypedContentId
    owner_binding_payload: TypedContentId
    operation_policy: OwnerOperationPolicyDisposition
    owner_policy_closure: TypedContentId
    capability_requirement: OwnerCapabilityRequirement

    def body(self) -> DatumRecord:
        if type(self) is not PortableSourceAuthorityBinding:
            raise ModelError("portable source authority binding has the wrong shape")
        if (
            type(self.owner_domain) is not Symbol
            or type(self.capability_family) is not Symbol
        ):
            raise ModelError("authority owner and capability family must be symbols")
        if type(self.capability_requirement) is not OwnerCapabilityRequirement:
            raise ModelError("authority binding lacks an exact capability requirement")
        requirement_body = self.capability_requirement.body()
        if (
            self.capability_requirement.owner_domain != self.owner_domain
            or self.capability_requirement.capability_family
            != self.capability_family
        ):
            raise ModelError(
                "authority binding and capability requirement disagree on owner or family"
            )
        identifiers = (
            self.owner_source_coordinate,
            self.owner_binding_payload,
            self.owner_policy_closure,
            self.capability_requirement.owner_requirement,
        )
        for identifier in identifiers:
            _require_typed_content_id(
                identifier,
                axis_name="portable source-authority binding reference",
            )
        policy_body = owner_operation_policy_disposition_body(self.operation_policy)
        policy_id = (
            self.operation_policy.owner_policy_binding
            if type(self.operation_policy) is BoundOwnerOperationPolicy
            else self.operation_policy.owner_no_policy_declaration
        )
        regime = self.owner_source_coordinate.semantic_regime
        if any(
            identifier.semantic_regime != regime
            for identifier in (*identifiers, policy_id)
        ):
            raise DeclarationKindMismatchError(
                "portable source-authority binding crosses semantic regimes"
            )
        return DatumRecord(
            (
                (0, self.owner_domain),
                (1, self.capability_family),
                (2, _content_ref_datum(self.owner_source_coordinate)),
                (3, _content_ref_datum(self.owner_binding_payload)),
                (4, policy_body),
                (5, _content_ref_datum(self.owner_policy_closure)),
                (6, requirement_body),
            )
        )


@dataclass(frozen=True, eq=False, repr=False, slots=True)
class OwnerLocalSourceAuthorityBinding:
    """Inert owner-local metadata with deliberately no canonical body."""

    owner_domain: Symbol
    capability_family: Symbol
    owner_local_coordinate: object
    owner_binding_payload: TypedContentId
    operation_policy: OwnerOperationPolicyDisposition
    owner_policy_closure: TypedContentId
    capability_requirement: OwnerCapabilityRequirement

    __hash__ = None

    def __repr__(self) -> str:
        return "OwnerLocalSourceAuthorityBinding(<process-local>)"

    def __copy__(self) -> "OwnerLocalSourceAuthorityBinding":
        raise ModelError("owner-local authority bindings cannot be copied")

    def __deepcopy__(self, _memo: object) -> "OwnerLocalSourceAuthorityBinding":
        raise ModelError("owner-local authority bindings cannot be deep-copied")

    def __reduce_ex__(self, _protocol: int) -> object:
        raise ModelError("owner-local authority bindings cannot be serialized")


def owner_capability_requirement_body(
    requirement: OwnerCapabilityRequirement,
) -> DatumRecord:
    if type(requirement) is not OwnerCapabilityRequirement:
        raise ModelError("owner capability requirement has the wrong exact shape")
    return requirement.body()


def portable_source_authority_binding_body(
    binding: PortableSourceAuthorityBinding,
) -> DatumRecord:
    if type(binding) is not PortableSourceAuthorityBinding:
        raise ModelError(
            "only a portable source authority binding has a canonical body"
        )
    return binding.body()


def validate_owner_local_source_authority_binding(
    binding: OwnerLocalSourceAuthorityBinding,
) -> None:
    """Validate inert local metadata without creating bytes, an ID, or authority."""

    if type(binding) is not OwnerLocalSourceAuthorityBinding:
        raise ModelError("owner-local source authority binding has the wrong shape")
    if (
        type(binding.owner_domain) is not Symbol
        or type(binding.capability_family) is not Symbol
    ):
        raise ModelError("owner-local authority owner and family must be symbols")
    if binding.owner_local_coordinate is None:
        raise ModelError("owner-local authority binding lacks its local coordinate")
    if type(binding.capability_requirement) is not OwnerCapabilityRequirement:
        raise ModelError("owner-local authority binding lacks its requirement")
    binding.capability_requirement.body()
    if (
        binding.capability_requirement.owner_domain != binding.owner_domain
        or binding.capability_requirement.capability_family
        != binding.capability_family
    ):
        raise ModelError(
            "owner-local binding and capability requirement disagree on owner or family"
        )
    for identifier in (
        binding.owner_binding_payload,
        binding.owner_policy_closure,
        binding.capability_requirement.owner_requirement,
    ):
        _require_typed_content_id(
            identifier,
            axis_name="owner-local source-authority reference",
        )
    owner_operation_policy_disposition_body(binding.operation_policy)
    policy_id = (
        binding.operation_policy.owner_policy_binding
        if type(binding.operation_policy) is BoundOwnerOperationPolicy
        else binding.operation_policy.owner_no_policy_declaration
    )
    regime = binding.owner_binding_payload.semantic_regime
    if any(
        identifier.semantic_regime != regime
        for identifier in (
            binding.owner_policy_closure,
            binding.capability_requirement.owner_requirement,
            policy_id,
        )
    ):
        raise DeclarationKindMismatchError(
            "owner-local source-authority binding crosses semantic regimes"
        )


class _SemanticFailure(Exception):
    def __init__(self, failure: DomainFailure) -> None:
        super().__init__(failure.failure_type.local_ordinal)
        self.failure = failure


class _Meter:
    def __init__(
        self, limits: DeterministicLimits, contract: EvaluationContractV0
    ) -> None:
        self.limits = limits
        self.contract = contract
        self.steps = 0
        self.iteration_items = 0
        self.primitive_work = 0
        self.result_bytes = 0

    def charge(
        self,
        *,
        term_entries: int = 0,
        iteration_items: int = 0,
        primitive_work: int = 0,
    ) -> None:
        if any(
            type(item) is not int or item < 0
            for item in (term_entries, iteration_items, primitive_work)
        ):
            raise ModelError("charge deltas must be mathematical naturals")
        steps = term_entries * self.contract.term_step_units
        charged_iterations = iteration_items * self.contract.iteration_item_units
        next_steps = self.steps + steps
        next_iteration_items = self.iteration_items + charged_iterations
        next_primitive_work = self.primitive_work + primitive_work
        if (
            next_steps > self.limits.maximum_steps
            or next_iteration_items > self.limits.maximum_iteration_items
            or next_primitive_work > self.limits.maximum_primitive_work
        ):
            raise _Control(
                Outcome.DETERMINISTIC_LIMIT_EXCEEDED,
                "K1-LIMIT-EVALUATION",
                "deterministic abstract evaluation limit exceeded",
            )
        self.steps = next_steps
        self.iteration_items = next_iteration_items
        self.primitive_work = next_primitive_work

    def preflight_result_capacity(self, maximum_result_bytes: int) -> None:
        if maximum_result_bytes > self.limits.maximum_result_bytes:
            raise _Control(
                Outcome.DETERMINISTIC_LIMIT_EXCEEDED,
                "K1-LIMIT-RESULT-CAPACITY",
                "result schema exceeds deterministic result-size capacity",
            )

    def finish(self, result_bytes: int) -> None:
        if result_bytes > self.limits.maximum_result_bytes:
            raise _Control(
                Outcome.DETERMINISTIC_LIMIT_EXCEEDED,
                "K1-LIMIT-RESULT",
                "deterministic result-size limit exceeded",
            )
        self.result_bytes = result_bytes

    def snapshot(self) -> AbstractCharge:
        return AbstractCharge(
            self.steps,
            self.iteration_items,
            self.primitive_work,
            self.result_bytes,
        )


DEFAULT_SUPPORTED_PRIMITIVES = tuple(
    sorted(
        (
            identifier
            for identifier, declaration in PRIMITIVE_DECLARATIONS.items()
            if declaration.key != ("fixture.bytes.reverse", 1)
        ),
        key=lambda identifier: identifier.internal_reference(),
    )
)


def completion_datum(
    function_type: SemanticFunctionType, completion: Completion
) -> DatumVariant:
    if type(completion) is Success:
        if type(completion.value) is not CanonicalValue:
            raise ModelError("success completion has the wrong exact carrier")
        if type(completion.value.value_type) is not ValueType:
            raise ModelError("success value type has the wrong exact carrier")
        if completion.value.value_type != function_type.output:
            raise ModelError("success value has the wrong derived output type")
        value = admit_value(function_type.output, completion.value.datum)
        return DatumVariant(0, value.datum)
    if type(completion) is not DomainFailure:
        raise ModelError("completion has the wrong exact carrier")
    if type(completion.failure_type) is not SemanticFailureType:
        raise ModelError("semantic failure type has the wrong exact carrier")
    if type(completion.payload) is not CanonicalValue:
        raise ModelError("semantic failure payload has the wrong exact carrier")
    if type(completion.payload.value_type) is not ValueType:
        raise ModelError("semantic failure payload type has the wrong exact carrier")
    try:
        failure_index = function_type.failures.index(completion.failure_type)
    except ValueError as error:
        raise ModelError("evaluator emitted an undeclared semantic failure") from error
    payload = admit_value(
        completion.failure_type.payload_type, completion.payload.datum
    )
    if payload.value_type != completion.payload.value_type:
        raise ModelError("semantic failure payload has the wrong value type")
    return DatumVariant(1 + failure_index, payload.datum)


def maximum_completion_size(function_type: SemanticFunctionType) -> int:
    cases: list[tuple[int, ValueType]] = [(0, function_type.output)]
    cases.extend(
        (index + 1, failure.payload_type)
        for index, failure in enumerate(function_type.failures)
    )
    return maximum_encoded_size(VariantSchema(tuple(cases)))


class Evaluator:
    """Deterministic evaluator for admitted canonical algorithms."""

    __slots__ = ("_supported_contracts", "_supported_primitives")

    def __init__(
        self,
        supported_primitives: tuple[TypedContentId, ...] = DEFAULT_SUPPORTED_PRIMITIVES,
        supported_contracts: tuple[EvaluationContractV0, ...] = (
            DEFAULT_EVALUATION_CONTRACT,
        ),
    ) -> None:
        if type(supported_primitives) is not tuple:
            raise ModelError("supported primitive IDs must use an exact tuple")
        if len(supported_primitives) > MAX_EVALUATOR_REGISTRY_ENTRIES:
            raise ModelError("supported primitive registry exceeds its host bound")
        if type(supported_contracts) is not tuple:
            raise ModelError("supported evaluation contracts must use an exact tuple")
        if len(supported_contracts) > MAX_EVALUATOR_REGISTRY_ENTRIES:
            raise ModelError("supported contract registry exceeds its host bound")
        primitives = supported_primitives
        if any(type(identifier) is not TypedContentId for identifier in primitives):
            raise ModelError("supported primitive IDs must have exact typed shape")
        for identifier in primitives:
            identifier.__post_init__()
            if identifier.subject_kind != SEMANTIC_PRIMITIVE_KIND:
                raise ModelError("supported primitive ID has the wrong subject kind")
            if identifier.semantic_regime != SEMANTIC_REGIME_ID:
                raise ModelError("supported primitive ID crosses semantic regimes")
        primitive_keys = tuple(
            identifier.internal_reference() for identifier in primitives
        )
        if len(set(primitive_keys)) != len(primitive_keys):
            raise ModelError("supported primitive IDs must not repeat")
        contracts = supported_contracts
        if any(type(contract) is not EvaluationContractV0 for contract in contracts):
            raise ModelError(
                "supported evaluation contracts must have exact typed shape"
            )
        for contract in contracts:
            contract.__post_init__()
        contract_keys = tuple(
            contract.identity.internal_reference() for contract in contracts
        )
        if len(set(contract_keys)) != len(contract_keys):
            raise ModelError("supported evaluation contracts must not repeat")
        self._supported_primitives = frozenset(primitives)
        self._supported_contracts = MappingProxyType(
            {contract.identity: contract for contract in contracts}
        )

    @property
    def supported_primitives(self) -> frozenset[TypedContentId]:
        return self._supported_primitives

    @property
    def supported_contracts(
        self,
    ) -> Mapping[TypedContentId, EvaluationContractV0]:
        return self._supported_contracts

    @staticmethod
    def _validate_limits(limits: DeterministicLimits) -> None:
        if type(limits) is not DeterministicLimits or any(
            type(item) is not int or item < 0
            for item in (
                getattr(limits, "maximum_steps", None),
                getattr(limits, "maximum_iteration_items", None),
                getattr(limits, "maximum_primitive_work", None),
                getattr(limits, "maximum_result_bytes", None),
            )
        ):
            raise _Control(
                Outcome.MALFORMED,
                "K1-MALFORMED-LIMITS",
                "deterministic limits must be mathematical naturals",
            )

    def _resolve_contract(
        self,
        contract: EvaluationContractV0 | TypedContentId,
        ledger: AuthenticationLedger,
    ) -> EvaluationContractV0:
        try:
            if type(contract) is EvaluationContractV0:
                body = contract._formed_body()
                if (
                    contract.semantic_regime.subject_kind != SEMANTIC_REGIME_KIND
                    or contract.semantic_regime != SEMANTIC_REGIME_ID
                ):
                    raise _Control(
                        Outcome.KIND_MISMATCH,
                        "K1-KIND-EVALUATION-CONTRACT",
                        "evaluation contract crosses the authenticated regime",
                    )
                for rule in contract.primitive_cost_rules:
                    if (
                        rule.primitive.subject_kind != SEMANTIC_PRIMITIVE_KIND
                        or rule.primitive.semantic_regime != SEMANTIC_REGIME_ID
                    ):
                        raise _Control(
                            Outcome.KIND_MISMATCH,
                            "K1-KIND-EVALUATION-CONTRACT",
                            "evaluation contract rule names an incompatible primitive coordinate",
                        )
                identifier = content_id(
                    EVALUATION_CONTRACT_KIND,
                    body,
                    semantic_regime=contract.semantic_regime,
                )
                authenticate_content_id(
                    identifier,
                    body,
                    FOUNDATION_PRIOR_META_PREIMAGES,
                    ledger=ledger,
                )
            elif type(contract) is TypedContentId:
                contract.__post_init__()
                if contract.subject_kind != EVALUATION_CONTRACT_KIND:
                    raise _Control(
                        Outcome.KIND_MISMATCH,
                        "K1-KIND-EVALUATION-CONTRACT",
                        "evaluation contract reference has the wrong kind",
                    )
                if contract.semantic_regime != SEMANTIC_REGIME_ID:
                    raise _Control(
                        Outcome.KIND_MISMATCH,
                        "K1-KIND-EVALUATION-CONTRACT",
                        "evaluation contract reference crosses the authenticated regime",
                    )
                identifier = contract
            else:
                raise ModelError("evaluation contract has no exact supported carrier")
        except _Control:
            raise
        except HashBindingConflictError as error:
            raise _Control(
                Outcome.CHECKER_FAILURE,
                "FOUNDATION-HASH-BINDING-CONFLICT",
                str(error),
            ) from error
        except (CanonicalError, ModelError, AttributeError, TypeError) as error:
            raise _Control(
                Outcome.MALFORMED,
                "K1-MALFORMED-EVALUATION-CONTRACT",
                f"evaluation contract is not canonical: {error}",
            ) from error
        if identifier not in self._supported_contracts:
            raise _Control(
                Outcome.UNSUPPORTED,
                "K1-UNSUPPORTED-EVALUATION-CONTRACT",
                "evaluator does not support the exact evaluation contract",
            )
        resolved = self._supported_contracts[identifier]
        try:
            if type(resolved) is not EvaluationContractV0:
                raise ModelError(
                    "supported evaluation contract has the wrong exact typed shape"
                )
            resolved.__post_init__()
            authenticate_content_id(
                identifier,
                resolved.body(),
                FOUNDATION_PRIOR_META_PREIMAGES,
                ledger=ledger,
            )
        except HashBindingConflictError as error:
            raise _Control(
                Outcome.CHECKER_FAILURE,
                "FOUNDATION-HASH-BINDING-CONFLICT",
                str(error),
            ) from error
        except (CanonicalError, ModelError, AttributeError, TypeError) as error:
            raise _Control(
                Outcome.CHECKER_FAILURE,
                "K1-CHECKER-EVALUATION-CONTRACT-REGISTRY",
                f"supported evaluation-contract registry is inconsistent: {error}",
            ) from error
        return resolved

    @staticmethod
    def _control_result(signal: _Control) -> EvaluationResult:
        return EvaluationResult(
            signal.outcome,
            AbstractCharge(),
            code=signal.code,
            detail=signal.detail,
        )

    def _prepare(
        self,
        subject: Subject,
        limits: DeterministicLimits,
        evaluation_contract: EvaluationContractV0 | TypedContentId,
        prior_meta_preimages: PriorMetaPreimageBundle,
    ) -> tuple[CanonicalAlgorithm, EvaluationContractV0, AuthenticationLedger]:
        self._validate_limits(limits)
        ledger = AuthenticationLedger()
        try:
            authenticate_prior_meta_basis(prior_meta_preimages, ledger=ledger)
        except HashBindingConflictError as error:
            raise _Control(
                Outcome.CHECKER_FAILURE,
                "FOUNDATION-HASH-BINDING-CONFLICT",
                str(error),
            ) from error
        except (CanonicalError, ModelError, AttributeError, TypeError) as error:
            raise _Control(
                Outcome.MALFORMED,
                "K1-MALFORMED-PRIOR-META-BASIS",
                f"prior-meta authentication basis is invalid: {error}",
            ) from error
        try:
            # Support is a contract over exact descriptor bodies, not an
            # ID-only registry hit. Co-observe the evaluator-owned support
            # basis before routing any later request field.
            authenticate_prior_meta_basis(
                FOUNDATION_PRIOR_META_PREIMAGES,
                ledger=ledger,
            )
        except HashBindingConflictError as error:
            raise _Control(
                Outcome.CHECKER_FAILURE,
                "FOUNDATION-HASH-BINDING-CONFLICT",
                str(error),
            ) from error
        except (CanonicalError, ModelError, AttributeError, TypeError) as error:
            raise _Control(
                Outcome.CHECKER_FAILURE,
                "K1-CHECKER-PRIOR-META-SUPPORT",
                f"evaluator prior-meta support is inconsistent: {error}",
            ) from error
        contract = self._resolve_contract(evaluation_contract, ledger)
        if type(subject) in (ExternalOperationContract, ExternalOperationBinding):
            try:
                if type(subject) is ExternalOperationContract:
                    subject.__post_init__()
                else:
                    validate_external_operation_binding(subject)
            except (CanonicalError, ModelError, AttributeError, TypeError) as error:
                raise _Control(
                    Outcome.MALFORMED,
                    "K1-MALFORMED-SUBJECT-CARRIER",
                    f"subject has malformed typed structure: {error}",
                ) from error
            raise _Control(
                Outcome.KIND_MISMATCH,
                "K1-KIND-SUBJECT",
                "subject kind is not foundation.portable-algorithm",
            )
        if type(subject) is not CanonicalAlgorithm:
            raise _Control(
                Outcome.MALFORMED,
                "K1-MALFORMED-SUBJECT-CARRIER",
                "subject has no exact supported typed carrier",
            )
        return subject, contract, ledger

    @staticmethod
    def _authenticate_algorithm_and_dependencies(
        algorithm: CanonicalAlgorithm,
        modules: Mapping[TypedContentId, SemanticModuleCandidate],
        ledger: AuthenticationLedger,
    ) -> SemanticFunctionType:
        try:
            authenticate_algorithm_identity(algorithm, ledger=ledger)
        except SemanticRegimeMismatchError as error:
            raise _Control(
                Outcome.KIND_MISMATCH,
                "K1-KIND-ALGORITHM-REGIME",
                str(error),
            ) from error
        except (AttributeError, TypeError) as error:
            raise _Control(
                Outcome.MALFORMED,
                "K1-MALFORMED-ALGORITHM-CARRIER",
                f"algorithm carrier is incomplete or ill-typed: {error}",
            ) from error
        try:
            module_dependencies = direct_module_dependencies(
                algorithm,
                ledger=ledger,
            )
        except DeclarationKindMismatchError as error:
            raise _Control(
                Outcome.KIND_MISMATCH,
                "K1-KIND-DECLARATION",
                str(error),
            ) from error
        except SemanticRegimeMismatchError as error:
            raise _Control(
                Outcome.KIND_MISMATCH,
                "K1-KIND-ALGORITHM-REGIME",
                str(error),
            ) from error
        is_fixture_bundle = modules is FIXTURE_MODULE_PREIMAGES
        if not is_fixture_bundle and type(modules) is not dict:
            raise _Control(
                Outcome.MALFORMED,
                "K1-MALFORMED-MODULE-BUNDLE",
                "module preimages must use an exact built-in dict carrier",
            )
        if len(modules) > MAX_MODULE_BUNDLE_ENTRIES:
            raise _Control(
                Outcome.DETERMINISTIC_LIMIT_EXCEEDED,
                "K1-LIMIT-MODULE-BUNDLE-ENTRIES",
                "module-preimage bundle exceeds the fixed entry bound",
            )
        if is_fixture_bundle:
            modules = dict(FIXTURE_MODULE_PREIMAGES)
        # Inspect exact key shapes before any hash/equality lookup.  Otherwise
        # an object stored under a colliding hash could execute host-defined
        # equality or impersonate the required TypedContentId.
        if any(type(identifier) is not TypedContentId for identifier in modules):
            raise _Control(
                Outcome.MALFORMED,
                "K1-MALFORMED-MODULE-BUNDLE",
                "module-preimage map keys must be exact TypedContentId values",
            )
        try:
            for identifier in modules:
                identifier.__post_init__()
        except CanonicalError as error:
            raise _Control(
                Outcome.MALFORMED,
                "K1-MALFORMED-MODULE-BUNDLE",
                f"module-preimage map key is malformed: {error}",
            ) from error
        if not is_fixture_bundle:
            modules = dict(modules)
        authenticate_module_closure(
            module_dependencies,
            modules,
            semantic_regime=algorithm.semantic_regime,
            ledger=ledger,
        )
        try:
            # Boundary 6 is deliberately complete before boundary 7 starts.
            authenticate_algorithm_declaration_references(
                algorithm,
                modules,
                ledger=ledger,
            )
        except HashBindingConflictError:
            raise
        except DeclarationKindMismatchError as error:
            raise _Control(
                Outcome.KIND_MISMATCH,
                "K1-KIND-DECLARATION",
                f"declaration coordinate has the wrong kind or type: {error}",
            ) from error
        except DeclarationAdmissionRefusedError as error:
            raise _Control(
                Outcome.REFUSED,
                "K1-REFUSED-DECLARATION-ADMISSION",
                f"authenticated declarations failed owner admission: {error}",
            ) from error
        except (CanonicalError, ModelError) as error:
            raise _Control(
                Outcome.MALFORMED,
                "K1-MALFORMED-DECLARATION",
                f"declaration material has malformed kind-specific structure: {error}",
            ) from error
        for reference in direct_primitive_dependencies(
            algorithm.term,
            ledger=ledger,
        ):
            try:
                resolve_primitive_declaration(reference, ledger=ledger)
            except ModelError as error:
                if reference.identifier not in PRIMITIVE_DECLARATIONS:
                    raise _Control(
                        Outcome.UNSUPPORTED,
                        "K1-UNSUPPORTED-PRIMITIVE-DECLARATION",
                        "evaluator cannot owner-type an exact primitive declaration",
                    ) from error
                raise _Control(
                    Outcome.CHECKER_FAILURE,
                    "K1-CHECKER-PRIMITIVE-REGISTRY",
                    f"supported primitive registry is inconsistent: {error}",
                ) from error
        try:
            function_type = algorithm.function_type
        except UnsupportedInterpretationError as error:
            raise _Control(
                Outcome.UNSUPPORTED,
                "K1-UNSUPPORTED-PRIMITIVE-TYPE-RULE",
                str(error),
            ) from error
        except (CanonicalError, ModelError) as error:
            raise _Control(
                Outcome.REFUSED,
                "K1-REFUSED-ALGORITHM-TYPING",
                f"authenticated algorithm has no valid typing derivation: {error}",
            ) from error
        try:
            authenticate_value_type_reference(
                function_type.output,
                modules,
                semantic_regime=algorithm.semantic_regime,
            )
            for failure in function_type.failures:
                authenticate_failure_reference(
                    failure,
                    modules,
                    semantic_regime=algorithm.semantic_regime,
                )
        except (CanonicalError, ModelError) as error:
            raise _Control(
                Outcome.CHECKER_FAILURE,
                "K1-CHECKER-DERIVED-ABI",
                f"registry-derived ABI escaped the authenticated closure: {error}",
            ) from error
        return function_type

    @staticmethod
    def _check_input_headers(
        function_type: SemanticFunctionType,
        inputs: Sequence[EncodedValue] | Sequence[CanonicalValue],
        *,
        encoded: bool,
    ) -> None:
        if type(inputs) is not tuple:
            raise _Control(
                Outcome.MALFORMED,
                "K1-MALFORMED-INPUT-BUNDLE",
                "inputs must be supplied as one exact immutable tuple",
            )
        if len(inputs) != len(function_type.inputs):
            raise _Control(
                Outcome.KIND_MISMATCH,
                "K1-KIND-ARITY",
                "input arity differs from the derived algorithm ABI",
            )
        expected_class = EncodedValue if encoded else CanonicalValue
        for expected, supplied in zip(function_type.inputs, inputs):
            if type(supplied) is not expected_class:
                raise _Control(
                    Outcome.MALFORMED,
                    "K1-MALFORMED-INPUT-CARRIER",
                    "input has no exact carrier for this evaluation mode",
                )
            try:
                supplied_value_type = supplied.value_type
            except (AttributeError, TypeError) as error:
                raise _Control(
                    Outcome.MALFORMED,
                    "K1-MALFORMED-INPUT-CARRIER",
                    f"input carrier is incomplete: {error}",
                ) from error
            if type(supplied_value_type) is not ValueType:
                raise _Control(
                    Outcome.MALFORMED,
                    "K1-MALFORMED-INPUT-CARRIER",
                    "input value-type header has malformed typed structure",
                )
            try:
                supplied_value_type.__post_init__()
            except (CanonicalError, ModelError, AttributeError, TypeError) as error:
                raise _Control(
                    Outcome.MALFORMED,
                    "K1-MALFORMED-INPUT-CARRIER",
                    f"input value-type header is not canonical: {error}",
                ) from error
            if supplied_value_type != expected:
                raise _Control(
                    Outcome.KIND_MISMATCH,
                    "K1-KIND-INPUT",
                    "input domain or schema differs from the algorithm ABI",
                )

    @staticmethod
    def _validate_value_domain_support(algorithm: CanonicalAlgorithm) -> None:
        for value_type in algorithm_value_types(algorithm):
            try:
                require_supported_value_type(value_type)
            except UnsupportedValueDomainError as error:
                raise _Control(
                    Outcome.UNSUPPORTED,
                    "K1-UNSUPPORTED-VALUE-DOMAIN",
                    "evaluator lacks the exact value-domain admission implementation",
                ) from error

    def _validate_primitive_cost_closure(
        self,
        algorithm: CanonicalAlgorithm,
        contract: EvaluationContractV0,
        ledger: AuthenticationLedger,
    ) -> None:
        dependencies = direct_primitive_dependencies(
            algorithm.term,
            ledger=ledger,
        )
        if any(
            reference.identifier not in self._supported_primitives
            for reference in dependencies
        ):
            raise _Control(
                Outcome.UNSUPPORTED,
                "K1-UNSUPPORTED-PRIMITIVE",
                "evaluator does not support an exact primitive dependency",
            )
        if any(
            contract.cost_rule(reference.identifier) is None
            for reference in dependencies
        ):
            raise _Control(
                Outcome.UNSUPPORTED,
                "K1-UNSUPPORTED-PRIMITIVE-COST",
                "evaluation contract lacks an exact primitive cost rule",
            )

        def validate_formula(
            formula: PrimitiveWorkFormulaV0,
            argument_types: tuple[ValueType, ...],
        ) -> None:
            indices = formula.argument_indices
            if any(index >= len(argument_types) for index in indices):
                raise _Control(
                    Outcome.REFUSED,
                    "K1-REFUSED-PRIMITIVE-COST-ABI",
                    "primitive cost formula index is outside the exact ABI",
                )
            if formula.kind.value == "sum-byte-lengths":
                valid = all(
                    isinstance(argument_types[index].schema, BytesSchema)
                    for index in indices
                )
            elif formula.kind.value == "min-byte-length-natural":
                byte_index, natural_index = indices
                valid = isinstance(
                    argument_types[byte_index].schema, BytesSchema
                ) and isinstance(argument_types[natural_index].schema, NatSchema)
            else:
                valid = formula.kind.value == "fixed"
            if not valid:
                raise _Control(
                    Outcome.REFUSED,
                    "K1-REFUSED-PRIMITIVE-COST-ABI",
                    "primitive cost formula is incompatible with the exact ABI",
                )

        def visit(term: Term, env: tuple[ValueType, ...]) -> None:
            if isinstance(term, (Literal, Variable)):
                return
            if isinstance(term, Let):
                visit(term.bound, env)
                bound_type = infer_term_type(term.bound, env).output
                visit(term.body, (bound_type, *env))
                return
            if isinstance(term, RecordConstruct):
                for _, child in term.fields:
                    visit(child, env)
                return
            if isinstance(term, Project):
                visit(term.record, env)
                return
            if isinstance(term, Inject):
                visit(term.payload, env)
                return
            if isinstance(term, Case):
                visit(term.scrutinee, env)
                scrutinee_type = infer_term_type(term.scrutinee, env).output
                assert isinstance(scrutinee_type.schema, VariantSchema)
                cases = dict(scrutinee_type.schema.cases)
                for case, branch in term.branches:
                    visit(branch, (cases[case], *env))
                return
            if isinstance(term, Conditional):
                visit(term.condition, env)
                visit(term.when_true, env)
                visit(term.when_false, env)
                return
            if isinstance(term, SequenceConstruct):
                for child in term.elements:
                    visit(child, env)
                return
            if isinstance(term, SequenceLength):
                visit(term.source, env)
                return
            if isinstance(term, Fail):
                visit(term.payload, env)
                return
            if isinstance(term, StrictIndex):
                visit(term.source, env)
                visit(term.index, env)
                return
            if isinstance(term, BoundedAppend):
                visit(term.source, env)
                visit(term.element, env)
                return
            if isinstance(term, PrimitiveCall):
                argument_types = tuple(
                    infer_term_type(argument, env).output for argument in term.arguments
                )
                formula = contract.cost_rule(term.primitive.identifier)
                assert formula is not None
                validate_formula(formula, argument_types)
                for argument in term.arguments:
                    visit(argument, env)
                return
            if isinstance(term, BoundedIterate):
                if isinstance(term.source, SequenceIterationSource):
                    visit(term.source.sequence, env)
                    source_type = infer_term_type(term.source.sequence, env).output
                    assert isinstance(source_type.schema, SeqSchema)
                    maximum_items = source_type.schema.maximum_length
                    element_type = source_type.schema.element
                else:
                    assert isinstance(term.source, RangeIterationSource)
                    visit(term.source.exclusive_bound, env)
                    bound_type = infer_term_type(
                        term.source.exclusive_bound, env
                    ).output
                    assert isinstance(bound_type.schema, NatSchema)
                    maximum_items = bound_type.schema.maximum
                    element_type = ValueType(
                        NAT_DOMAIN,
                        NatSchema(max(0, maximum_items - 1)),
                    )
                index_type = ValueType(
                    NAT_DOMAIN,
                    NatSchema(max(0, maximum_items - 1)),
                )
                visit(term.initial_state, env)
                initial_type = infer_term_type(term.initial_state, env).output
                visit(term.body, (index_type, element_type, initial_type, *env))
                return
            raise ModelError(f"unknown term constructor: {type(term)!r}")

        visit(algorithm.term, algorithm.inputs)

    @staticmethod
    def _model_error_result(
        error: CanonicalError | ValueAdmissionRefusedError | ModelError,
    ) -> EvaluationResult:
        if isinstance(error, HashBindingConflictError):
            return EvaluationResult(
                Outcome.CHECKER_FAILURE,
                AbstractCharge(),
                code="FOUNDATION-HASH-BINDING-CONFLICT",
                detail=str(error),
            )
        if isinstance(error, ValueAdmissionRefusedError):
            return EvaluationResult(
                Outcome.REFUSED,
                AbstractCharge(),
                code="K1-REFUSED-VALUE-ADMISSION",
                detail=str(error),
            )
        return EvaluationResult(
            Outcome.MALFORMED,
            AbstractCharge(),
            code="K1-MALFORMED-MODEL",
            detail=str(error),
        )

    def evaluate_encoded(
        self,
        subject: Subject,
        inputs: Sequence[EncodedValue],
        *,
        modules: Mapping[TypedContentId, SemanticModuleCandidate] | None = None,
        limits: DeterministicLimits = DEFAULT_LIMITS,
        evaluation_contract: EvaluationContractV0
        | TypedContentId = DEFAULT_EVALUATION_CONTRACT,
        prior_meta_preimages: PriorMetaPreimageBundle = FOUNDATION_PRIOR_META_PREIMAGES,
    ) -> EvaluationResult:
        supplied_modules = {} if modules is None else modules
        try:
            algorithm, contract, ledger = self._prepare(
                subject,
                limits,
                evaluation_contract,
                prior_meta_preimages,
            )
        except _Control as signal:
            return self._control_result(signal)
        try:
            function_type = self._authenticate_algorithm_and_dependencies(
                algorithm, supplied_modules, ledger
            )
            self._validate_value_domain_support(algorithm)
            try:
                admit_algorithm_literals(algorithm)
            except ValueAdmissionRefusedError as error:
                raise _Control(
                    Outcome.REFUSED,
                    "K1-REFUSED-LITERAL-ADMISSION",
                    f"algorithm literal failed owner admission: {error}",
                ) from error
            self._check_input_headers(function_type, inputs, encoded=True)
        except _Control as signal:
            return self._control_result(signal)
        except (CanonicalError, ModelError) as error:
            return self._model_error_result(error)
        decoded_values: list[CanonicalValue] = []
        for expected, item in zip(function_type.inputs, inputs):
            try:
                datum = decode_datum(item.body)
            except (CanonicalError, TypeError, AttributeError) as error:
                return EvaluationResult(
                    Outcome.MALFORMED,
                    AbstractCharge(),
                    code="K1-MALFORMED-CANONICAL-INPUT",
                    detail=str(error),
                )
            try:
                decoded_values.append(admit_value(expected, datum))
            except ValueAdmissionRefusedError as error:
                return EvaluationResult(
                    Outcome.REFUSED,
                    AbstractCharge(),
                    code="K1-REFUSED-INPUT-ADMISSION",
                    detail=str(error),
                )
            except (CanonicalError, TypeError, AttributeError) as error:
                return EvaluationResult(
                    Outcome.MALFORMED,
                    AbstractCharge(),
                    code="K1-MALFORMED-CANONICAL-INPUT",
                    detail=str(error),
                )
        decoded = tuple(decoded_values)
        return self._evaluate_prepared(
            algorithm,
            decoded,
            limits,
            contract,
            function_type,
            ledger,
        )

    def evaluate(
        self,
        subject: Subject,
        inputs: Sequence[CanonicalValue],
        *,
        modules: Mapping[TypedContentId, SemanticModuleCandidate] | None = None,
        limits: DeterministicLimits = DEFAULT_LIMITS,
        evaluation_contract: EvaluationContractV0
        | TypedContentId = DEFAULT_EVALUATION_CONTRACT,
        prior_meta_preimages: PriorMetaPreimageBundle = FOUNDATION_PRIOR_META_PREIMAGES,
    ) -> EvaluationResult:
        supplied_modules = {} if modules is None else modules
        try:
            algorithm, contract, ledger = self._prepare(
                subject,
                limits,
                evaluation_contract,
                prior_meta_preimages,
            )
        except _Control as signal:
            return self._control_result(signal)
        try:
            function_type = self._authenticate_algorithm_and_dependencies(
                algorithm, supplied_modules, ledger
            )
            self._validate_value_domain_support(algorithm)
            try:
                admit_algorithm_literals(algorithm)
            except ValueAdmissionRefusedError as error:
                raise _Control(
                    Outcome.REFUSED,
                    "K1-REFUSED-LITERAL-ADMISSION",
                    f"algorithm literal failed owner admission: {error}",
                ) from error
            self._check_input_headers(function_type, inputs, encoded=False)
        except _Control as signal:
            return self._control_result(signal)
        except (CanonicalError, ModelError) as error:
            return self._model_error_result(error)
        return self._evaluate_prepared(
            algorithm,
            inputs,
            limits,
            contract,
            function_type,
            ledger,
        )

    def _evaluate_prepared(
        self,
        algorithm: CanonicalAlgorithm,
        inputs: Sequence[CanonicalValue],
        limits: DeterministicLimits,
        contract: EvaluationContractV0,
        function_type: SemanticFunctionType,
        ledger: AuthenticationLedger,
    ) -> EvaluationResult:
        meter = _Meter(limits, contract)
        try:
            checked_inputs: list[CanonicalValue] = []
            for expected, supplied in zip(function_type.inputs, inputs):
                checked_inputs.append(admit_value(expected, supplied.datum))
            self._validate_primitive_cost_closure(algorithm, contract, ledger)
            try:
                maximum_result_size = maximum_completion_size(function_type)
            except CanonicalError as error:
                raise _Control(
                    Outcome.REFUSED,
                    "K1-REFUSED-COMPLETION-SCHEMA-ADMISSION",
                    f"derived completion schema failed closed admission: {error}",
                ) from error
            meter.preflight_result_capacity(maximum_result_size)
        except _Control as signal:
            return EvaluationResult(
                signal.outcome,
                meter.snapshot(),
                code=signal.code,
                detail=signal.detail,
            )
        except ValueAdmissionRefusedError as error:
            return EvaluationResult(
                Outcome.REFUSED,
                meter.snapshot(),
                code="K1-REFUSED-INPUT-ADMISSION",
                detail=str(error),
            )
        except (AttributeError, TypeError) as error:
            return EvaluationResult(
                Outcome.MALFORMED,
                meter.snapshot(),
                code="K1-MALFORMED-INPUT-CARRIER",
                detail=f"canonical input carrier is incomplete: {error}",
            )
        except (CanonicalError, ModelError) as error:
            return EvaluationResult(
                Outcome.MALFORMED,
                meter.snapshot(),
                code="K1-MALFORMED-MODEL",
                detail=str(error),
            )

        try:
            value = self._eval(algorithm.term, tuple(checked_inputs), meter)
            completion: Completion = Success(value)
            meter.finish(_encoded_size(completion_datum(function_type, completion)))
            return EvaluationResult(
                Outcome.COMPLETED,
                meter.snapshot(),
                completion=completion,
            )
        except _SemanticFailure as signal:
            try:
                completion = signal.failure
                meter.finish(_encoded_size(completion_datum(function_type, completion)))
            except _Control as limit_signal:
                return EvaluationResult(
                    limit_signal.outcome,
                    meter.snapshot(),
                    code=limit_signal.code,
                    detail=limit_signal.detail,
                )
            except (
                CanonicalError,
                ValueAdmissionRefusedError,
                ModelError,
                AttributeError,
                TypeError,
            ) as error:
                return EvaluationResult(
                    Outcome.CHECKER_FAILURE,
                    meter.snapshot(),
                    code="K1-CHECKER-FAILURE-SEMANTIC-FAILURE",
                    detail=str(error),
                )
            return EvaluationResult(
                Outcome.COMPLETED,
                meter.snapshot(),
                completion=completion,
            )
        except _Control as signal:
            return EvaluationResult(
                signal.outcome,
                meter.snapshot(),
                code=signal.code,
                detail=signal.detail,
            )
        except MemoryError:
            # Host exhaustion may prevent any trustworthy result record.  It is
            # neither a semantic answer nor a safely classified checker defect.
            raise
        except Exception as error:  # pragma: no cover - exercised by fault injection
            return EvaluationResult(
                Outcome.CHECKER_FAILURE,
                meter.snapshot(),
                code="K1-CHECKER-FAILURE",
                detail=f"{type(error).__name__}: {error}",
            )

    def _eval(
        self,
        term: Term,
        env: tuple[CanonicalValue, ...],
        meter: _Meter,
    ) -> CanonicalValue:
        meter.charge(term_entries=1)
        if isinstance(term, Literal):
            return admit_value(term.value.value_type, term.value.datum)
        if isinstance(term, Variable):
            return env[term.index]
        if isinstance(term, Let):
            bound = self._eval(term.bound, env, meter)
            return self._eval(term.body, (bound, *env), meter)
        if isinstance(term, RecordConstruct):
            values = tuple(
                (ordinal, self._eval(child, env, meter))
                for ordinal, child in term.fields
            )
            output_type = infer_term_type(
                term, tuple(item.value_type for item in env)
            ).output
            return admit_value(
                output_type,
                DatumRecord(tuple((ordinal, item.datum) for ordinal, item in values)),
            )
        if isinstance(term, Project):
            record = self._eval(term.record, env, meter)
            assert isinstance(record.datum, DatumRecord)
            output_type = infer_term_type(
                term, tuple(item.value_type for item in env)
            ).output
            return admit_value(output_type, dict(record.datum.fields)[term.ordinal])
        if isinstance(term, Inject):
            payload = self._eval(term.payload, env, meter)
            return admit_value(term.sum_type, DatumVariant(term.case, payload.datum))
        if isinstance(term, Case):
            scrutinee = self._eval(term.scrutinee, env, meter)
            assert isinstance(scrutinee.datum, DatumVariant)
            schema = scrutinee.value_type.schema
            assert isinstance(schema, VariantSchema)
            payload_type = dict(schema.cases)[scrutinee.datum.case]
            payload = admit_value(payload_type, scrutinee.datum.payload)
            branch = dict(term.branches)[scrutinee.datum.case]
            return self._eval(branch, (payload, *env), meter)
        if isinstance(term, Conditional):
            condition = self._eval(term.condition, env, meter)
            assert type(condition.datum) is bool
            branch = term.when_true if condition.datum else term.when_false
            return self._eval(branch, env, meter)
        if isinstance(term, SequenceConstruct):
            elements = tuple(self._eval(item, env, meter) for item in term.elements)
            output_type = ValueType(
                SEQUENCE_DOMAIN,
                SeqSchema(term.element_type, term.maximum_length),
            )
            return admit_value(
                output_type, DatumSeq(tuple(item.datum for item in elements))
            )
        if isinstance(term, SequenceLength):
            source = self._eval(term.source, env, meter)
            assert isinstance(source.datum, DatumSeq)
            output_type = infer_term_type(
                term, tuple(item.value_type for item in env)
            ).output
            return admit_value(output_type, Nat(len(source.datum.values)))
        if isinstance(term, Fail):
            payload = self._eval(term.payload, env, meter)
            raise _SemanticFailure(DomainFailure(term.failure_type, payload))
        if isinstance(term, StrictIndex):
            source = self._eval(term.source, env, meter)
            index = self._eval(term.index, env, meter)
            assert isinstance(source.datum, DatumSeq) and isinstance(index.datum, Nat)
            if index.datum.value >= len(source.datum.values):
                raise _SemanticFailure(DomainFailure(term.failure_type, index))
            output_type = infer_term_type(
                term, tuple(item.value_type for item in env)
            ).output
            return admit_value(output_type, source.datum.values[index.datum.value])
        if isinstance(term, BoundedAppend):
            source = self._eval(term.source, env, meter)
            element = self._eval(term.element, env, meter)
            assert isinstance(source.datum, DatumSeq)
            schema = source.value_type.schema
            assert isinstance(schema, SeqSchema)
            if len(source.datum.values) >= schema.maximum_length:
                payload = admit_value(term.failure_type.payload_type, UNIT)
                raise _SemanticFailure(DomainFailure(term.failure_type, payload))
            return admit_value(
                source.value_type,
                DatumSeq((*source.datum.values, element.datum)),
            )
        if isinstance(term, PrimitiveCall):
            values = tuple(self._eval(item, env, meter) for item in term.arguments)
            return self._primitive(term, values, meter)
        if isinstance(term, BoundedIterate):
            if isinstance(term.source, SequenceIterationSource):
                source = self._eval(term.source.sequence, env, meter)
                assert isinstance(source.datum, DatumSeq)
                source_schema = source.value_type.schema
                assert isinstance(source_schema, SeqSchema)
                element_type = source_schema.element
                index_type = ValueType(
                    NAT_DOMAIN,
                    NatSchema(max(0, source_schema.maximum_length - 1)),
                )
                raw_items: Iterable[tuple[int, Datum | None]] = enumerate(
                    source.datum.values
                )
            else:
                assert isinstance(term.source, RangeIterationSource)
                bound = self._eval(term.source.exclusive_bound, env, meter)
                assert isinstance(bound.datum, Nat)
                assert isinstance(bound.value_type.schema, NatSchema)
                index_type = ValueType(
                    NAT_DOMAIN,
                    NatSchema(max(0, bound.value_type.schema.maximum - 1)),
                )
                element_type = index_type
                raw_items = ((index, None) for index in range(bound.datum.value))
            initial = self._eval(term.initial_state, env, meter)
            state = initial
            result_type = infer_term_type(
                term, tuple(item.value_type for item in env)
            ).output
            assert isinstance(result_type.schema, VariantSchema)
            cases = dict(result_type.schema.cases)
            for index, raw_element in raw_items:
                meter.charge(iteration_items=1)
                index_value = admit_value(index_type, Nat(index))
                element = (
                    index_value
                    if raw_element is None
                    else admit_value(element_type, raw_element)
                )
                decision = self._eval(
                    term.body, (index_value, element, state, *env), meter
                )
                assert isinstance(decision.datum, DatumVariant)
                if decision.datum.case == 0:
                    state = admit_value(
                        cases[0],
                        decision.datum.payload,
                    )
                else:
                    return decision
            return admit_value(result_type, DatumVariant(0, state.datum))
        raise ModelError("unknown term during evaluation")

    def _primitive(
        self,
        call: PrimitiveCall,
        values: tuple[CanonicalValue, ...],
        meter: _Meter,
    ) -> CanonicalValue:
        declaration = resolve_primitive_declaration(call.primitive)
        formula = meter.contract.cost_rule(call.primitive.identifier)
        if formula is None:
            raise RuntimeError("supported primitive lacks a cost rule")
        meter.charge(primitive_work=formula.measure(values))
        key = declaration.key
        data = tuple(value.datum for value in values)
        output_type = resolve_primitive_type_rule(declaration.identifier)(
            tuple(value.value_type for value in values)
        )
        if key == ("sha2-256", 1):
            source = data[0]
            assert isinstance(source, BytesValue)
            result: Datum = BytesValue(hashlib.sha256(source.value).digest())
        elif key == ("bytes.concat", 1):
            left, right = data
            assert isinstance(left, BytesValue) and isinstance(right, BytesValue)
            result = BytesValue(left.value + right.value)
        elif key == ("u64.to-be", 1):
            source = data[0]
            assert isinstance(source, Nat)
            result = BytesValue(source.value.to_bytes(8, "big"))
        elif key == ("bytes.first-u64-be", 1):
            source = data[0]
            assert isinstance(source, BytesValue)
            result = Nat(int.from_bytes(source.value[:8], "big"))
        elif key == ("nat.lt", 1):
            left, right = data
            assert isinstance(left, Nat) and isinstance(right, Nat)
            result = left.value < right.value
        elif key == ("nat.mod-positive", 1):
            left, right = data
            assert isinstance(left, Nat) and isinstance(right, Nat)
            if right.value == 0:
                raise _SemanticFailure(
                    DomainFailure(
                        ZERO_DIVISOR_FAILURE,
                        admit_value(ZERO_DIVISOR_FAILURE.payload_type, UNIT),
                    )
                )
            result = Nat(left.value % right.value)
        elif key == ("bytes.take", 1):
            source, count = data
            assert isinstance(source, BytesValue) and isinstance(count, Nat)
            result = BytesValue(source.value[: min(len(source.value), count.value)])
        elif key == ("fixture.bytes.prefix-27", 1):
            source = data[0]
            assert isinstance(source, BytesValue)
            result = BytesValue(source.value[:27])
        else:
            # A key can reach this point only if a caller explicitly advertises
            # support without providing semantics.  That is a checker defect,
            # not a domain-level answer.
            raise RuntimeError("supported primitive has no implementation")
        return admit_value(output_type, result)


# ---------------------------------------------------------------------------
# Exact fixture builders: composition pressure, not general conformance
# ---------------------------------------------------------------------------


BYTES_32 = ValueType(BYTES_DOMAIN, BytesSchema(32, 32))
BYTES_27 = ValueType(BYTES_DOMAIN, BytesSchema(27, 27))
BYTES_8 = ValueType(BYTES_DOMAIN, BytesSchema(8, 8))
BYTES_0_32 = ValueType(BYTES_DOMAIN, BytesSchema(0, 32))
BYTES_0_64 = ValueType(BYTES_DOMAIN, BytesSchema(0, 64))
BYTES_32_96 = ValueType(BYTES_DOMAIN, BytesSchema(32, 96))
NAT_U64 = ValueType(NAT_DOMAIN, NatSchema((1 << 64) - 1))
NAT_16 = ValueType(NAT_DOMAIN, NatSchema(16))
NAT_INDEX_16 = ValueType(NAT_DOMAIN, NatSchema(15))
BOOL = ValueType(BOOL_DOMAIN, BOOL_SCHEMA)
UNIT_VALUE = ValueType(UNIT_DOMAIN, UNIT_SCHEMA)


def _call(
    name: str,
    arguments: Sequence[Term],
    *,
    version: int = 1,
) -> PrimitiveCall:
    return PrimitiveCall(PRIMITIVE_REFS_BY_KEY[(name, version)], tuple(arguments))


def iteration_result_type(state: ValueType, broken: ValueType) -> ValueType:
    return ValueType(
        VARIANT_DOMAIN,
        VariantSchema(((0, state), (1, broken))),
    )


def build_transcript_algorithm() -> CanonicalAlgorithm:
    messages = ValueType(SEQUENCE_DOMAIN, SeqSchema(BYTES_0_64, 8))
    concatenated = _call(
        "bytes.concat",
        # Iterator binds index, element, and state at slots 0, 1, and 2.
        (Variable(2, BYTES_32), Variable(1, BYTES_0_64)),
    )
    step = _call("sha2-256", (concatenated,))
    result_type = iteration_result_type(BYTES_32, BYTES_32)
    iteration = BoundedIterate(
        SequenceIterationSource(Variable(1, messages)),
        Variable(0, BYTES_32),
        Inject(0, step, result_type),
    )
    term = Case(
        iteration,
        (
            (0, Variable(0, BYTES_32)),
            (1, Variable(0, BYTES_32)),
        ),
    )
    return CanonicalAlgorithm(
        Symbol("TranscriptStateFold"),
        (BYTES_32, messages),
        term,
    )


def build_rejection_find_algorithm() -> CanonicalAlgorithm:
    encoded_counter = _call("u64.to-be", (Variable(0, NAT_INDEX_16),))
    seed_and_counter = _call(
        "bytes.concat",
        # Iterator binds index, element, state, then outer inputs.
        (Variable(3, BYTES_32), encoded_counter),
    )
    candidate = _call("sha2-256", (seed_and_counter,))
    first_u64 = _call("bytes.first-u64-be", (Variable(0, BYTES_32),))
    # Let binds the candidate at slot 0, shifting the outer limit to slot 6.
    accepted = _call("nat.lt", (first_u64, Variable(6, NAT_U64)))
    iteration_type = iteration_result_type(UNIT_VALUE, BYTES_32)
    body = Let(
        candidate,
        Conditional(
            accepted,
            Inject(1, Variable(0, BYTES_32), iteration_type),
            Inject(0, Literal(admit_value(UNIT_VALUE, UNIT)), iteration_type),
        ),
    )
    iteration = BoundedIterate(
        RangeIterationSource(Variable(1, NAT_16)),
        Literal(admit_value(UNIT_VALUE, UNIT)),
        body,
    )
    output = ValueType(VARIANT_DOMAIN, option_schema(BYTES_32))
    term = Case(
        iteration,
        (
            (0, Inject(0, Literal(admit_value(UNIT_VALUE, UNIT)), output)),
            (1, Inject(1, Variable(0, BYTES_32), output)),
        ),
    )
    return CanonicalAlgorithm(
        Symbol("BoundedRejectionFind"),
        (BYTES_32, NAT_16, NAT_U64),
        term,
    )


def build_nested_sampler_algorithm() -> CanonicalAlgorithm:
    """Count-by-retry sampler shape with typed semantic exhaustion."""

    samples = ValueType(SEQUENCE_DOMAIN, SeqSchema(BYTES_32, 16))
    inner_result = iteration_result_type(UNIT_VALUE, BYTES_32)
    outer_result = iteration_result_type(samples, samples)

    # Inner binders are retry index/item/state, followed by the outer
    # draw-index/item/samples binders and then the four algorithm inputs.
    draw_bytes = _call("u64.to-be", (Variable(3, NAT_INDEX_16),))
    retry_bytes = _call("u64.to-be", (Variable(0, NAT_INDEX_16),))
    draw_seed = _call(
        "bytes.concat",
        (Variable(6, BYTES_32), draw_bytes),
    )
    candidate_preimage = _call("bytes.concat", (draw_seed, retry_bytes))
    candidate = _call("sha2-256", (candidate_preimage,))
    first_u64 = _call("bytes.first-u64-be", (Variable(0, BYTES_32),))
    accepted = _call("nat.lt", (first_u64, Variable(10, NAT_U64)))
    inner_body = Let(
        candidate,
        Conditional(
            accepted,
            Inject(1, Variable(0, BYTES_32), inner_result),
            Inject(
                0,
                Literal(admit_value(UNIT_VALUE, UNIT)),
                inner_result,
            ),
        ),
    )
    inner = BoundedIterate(
        # Outer binder slots are draw index/item/samples, then inputs.  The
        # retry count is therefore slot 5.
        RangeIterationSource(Variable(5, NAT_16)),
        Literal(admit_value(UNIT_VALUE, UNIT)),
        inner_body,
    )
    outer_body = Case(
        inner,
        (
            (
                0,
                Fail(
                    SAMPLING_EXHAUSTED_FAILURE,
                    Variable(1, NAT_INDEX_16),
                    outer_result,
                ),
            ),
            (
                1,
                Inject(
                    0,
                    BoundedAppend(
                        Variable(3, samples),
                        Variable(0, BYTES_32),
                        SEQUENCE_CAPACITY_FAILURE,
                    ),
                    outer_result,
                ),
            ),
        ),
    )
    outer = BoundedIterate(
        RangeIterationSource(Variable(1, NAT_16)),
        SequenceConstruct(BYTES_32, (), 16),
        outer_body,
    )
    term = Case(
        outer,
        (
            (0, Variable(0, samples)),
            (1, Variable(0, samples)),
        ),
    )
    return CanonicalAlgorithm(
        Symbol("NestedCountByRetrySampler"),
        (BYTES_32, NAT_16, NAT_16, NAT_U64),
        term,
    )


def build_lossy_projection_algorithm() -> CanonicalAlgorithm:
    term = _call("fixture.bytes.prefix-27", (Variable(0, BYTES_32),))
    return CanonicalAlgorithm(
        Symbol("LossyByteProjection"),
        (BYTES_32,),
        term,
    )


def build_pairwise_hash_algorithm() -> CanonicalAlgorithm:
    """Fixture Merkle-path-shaped state fold; no universal tree policy."""

    siblings = ValueType(SEQUENCE_DOMAIN, SeqSchema(BYTES_32, 8))
    pair = _call(
        "bytes.concat",
        (Variable(2, BYTES_32), Variable(1, BYTES_32)),
    )
    combine = _call("sha2-256", (pair,))
    result_type = iteration_result_type(BYTES_32, BYTES_32)
    iteration = BoundedIterate(
        SequenceIterationSource(Variable(1, siblings)),
        Variable(0, BYTES_32),
        Inject(0, combine, result_type),
    )
    term = Case(
        iteration,
        ((0, Variable(0, BYTES_32)), (1, Variable(0, BYTES_32))),
    )
    return CanonicalAlgorithm(
        Symbol("MerklePathStateFold"),
        (BYTES_32, siblings),
        term,
    )


def build_strict_paired_fold_algorithm() -> CanonicalAlgorithm:
    """Exact monomorphic zip that refuses either length mismatch."""

    left = ValueType(SEQUENCE_DOMAIN, SeqSchema(BYTES_32, 4))
    right = ValueType(SEQUENCE_DOMAIN, SeqSchema(BYTES_8, 4))
    pair = ValueType(
        RECORD_DOMAIN,
        RecordSchema(((0, BYTES_32), (1, BYTES_8))),
    )
    pairs = ValueType(SEQUENCE_DOMAIN, SeqSchema(pair, 4))
    fold_result = iteration_result_type(pairs, pairs)

    # Sequence iteration produces Nat[3]; widen through the exact u64 codec
    # because the declared strict-index failure carries NAT_U64.
    wide_index = _call(
        "bytes.first-u64-be",
        (_call("u64.to-be", (Variable(0, ValueType(NAT_DOMAIN, NatSchema(3))),)),),
    )
    right_item = StrictIndex(
        Variable(4, right),
        wide_index,
        INDEX_OUT_OF_RANGE_FAILURE,
    )
    paired = RecordConstruct(
        (
            (0, Variable(1, BYTES_32)),
            (1, right_item),
        )
    )
    body = Inject(
        0,
        BoundedAppend(
            Variable(2, pairs),
            paired,
            SEQUENCE_CAPACITY_FAILURE,
        ),
        fold_result,
    )
    fold = BoundedIterate(
        SequenceIterationSource(Variable(0, left)),
        SequenceConstruct(pair, (), 4),
        body,
    )

    # In a successful fold branch, slots are pairs, left, right.  A shorter
    # right sequence has already failed at StrictIndex; this final comparison
    # detects a longer right sequence.
    left_length = SequenceLength(Variable(1, left))
    right_length = SequenceLength(Variable(2, right))
    right_is_longer = _call("nat.lt", (left_length, right_length))
    wide_left_length = _call(
        "bytes.first-u64-be",
        (_call("u64.to-be", (left_length,)),),
    )
    normal_branch = Conditional(
        right_is_longer,
        Fail(
            INDEX_OUT_OF_RANGE_FAILURE,
            wide_left_length,
            pairs,
        ),
        Variable(0, pairs),
    )
    term = Case(
        fold,
        (
            (0, normal_branch),
            (1, Variable(0, pairs)),
        ),
    )
    return CanonicalAlgorithm(
        Symbol("StrictPairedFold"),
        (left, right),
        term,
    )


def build_oriented_path_algorithm(
    *,
    reverse_orientation_law: bool = False,
    domain_prefix: bytes = b"\x01",
) -> CanonicalAlgorithm:
    """Oriented path-shaped fold; membership remains a Relations judgment."""

    prefix_type = ValueType(BYTES_DOMAIN, BytesSchema(1, 1))
    prefix = Literal(admit_value(prefix_type, BytesValue(domain_prefix)))
    step = ValueType(
        RECORD_DOMAIN,
        RecordSchema(((0, BYTES_32), (1, BOOL))),
    )
    path = ValueType(SEQUENCE_DOMAIN, SeqSchema(step, 8))
    sibling = Project(Variable(1, step), 0)
    sibling_left = Project(Variable(1, step), 1)
    current = Variable(2, BYTES_32)

    def hash_pair(left_term: Term, right_term: Term) -> Term:
        prefixed = _call("bytes.concat", (prefix, left_term))
        return _call(
            "sha2-256",
            (_call("bytes.concat", (prefixed, right_term)),),
        )

    left_first = hash_pair(sibling, current)
    current_first = hash_pair(current, sibling)
    if reverse_orientation_law:
        left_first, current_first = current_first, left_first
    next_state = Conditional(sibling_left, left_first, current_first)
    result_type = iteration_result_type(BYTES_32, BYTES_32)
    iteration = BoundedIterate(
        SequenceIterationSource(Variable(1, path)),
        Variable(0, BYTES_32),
        Inject(0, next_state, result_type),
    )
    term = Case(
        iteration,
        ((0, Variable(0, BYTES_32)), (1, Variable(0, BYTES_32))),
    )
    return CanonicalAlgorithm(
        Symbol("OrientedPathStateFold"),
        (BYTES_32, path),
        term,
    )


def build_mod_algorithm() -> CanonicalAlgorithm:
    term = _call(
        "nat.mod-positive",
        (Variable(0, NAT_U64), Variable(1, NAT_U64)),
    )
    return CanonicalAlgorithm(
        Symbol("PartialModulusSurface"),
        (NAT_U64, NAT_U64),
        term,
    )


def build_unsupported_algorithm() -> CanonicalAlgorithm:
    term = _call(
        "fixture.bytes.reverse",
        (Variable(0, BYTES_0_32),),
    )
    return CanonicalAlgorithm(
        Symbol("UnsupportedFixturePrimitive"),
        (BYTES_0_32,),
        term,
    )


def build_module_dependent_algorithm(
    module_id: TypedContentId,
) -> CanonicalAlgorithm:
    dependent_domain = ValueDomain(
        module_id,
        Symbol("value-domain"),
        0,
    )
    dependent_type = ValueType(dependent_domain, BytesSchema(32, 32))
    # The literal carries a structurally checked opaque-domain candidate so
    # identity and module-closure locality can be exercised.  It does not mint
    # a domain-admitted value: evaluation must refuse it as Unsupported unless
    # an exact domain implementation is added.
    constant = _admit_shaped_value(dependent_type, BytesValue(b"m" * 32))
    return CanonicalAlgorithm(
        Symbol("ModuleDependentConstant"),
        (),
        Literal(constant),
    )
