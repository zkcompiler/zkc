#!/usr/bin/env python3
"""Independent FoundationMetaProfileV0 canonical-value and identity oracle.

The JSON-lines interface and canonical bytes are frozen in CONTRACT.md.  This
module intentionally imports nothing from the K1 reference evaluator.
"""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
import re
import sys
from typing import Any, BinaryIO, Iterable


FOUNDATION_PROFILE = "zkc.foundation.meta.v0"
PRIOR_META_DOMAIN = b"zkc/prior-meta-id/v0\x00"
IDENTITY_DOMAIN = b"zkc/content-id/v0\x00"
IDENTITY_PROFILE_KIND = "foundation.identity-profile"
HASH_SUITE_KIND = "foundation.hash-suite"
SEMANTIC_MODULE_KIND = "foundation.semantic-module"
SEMANTIC_REGIME_KIND = "foundation.semantic-regime"
PRIOR_META_KINDS = frozenset(
    {
        IDENTITY_PROFILE_KIND,
        HASH_SUITE_KIND,
        SEMANTIC_REGIME_KIND,
    }
)

# These digests identify the exact descriptor bodies frozen in cases/requests.jsonl.
# FoundationMetaProfileV0 itself is the constitutional encoder and hash prior, so
# neither profile identifier participates in its own construction.
SUPPORTED_IDENTITY_PROFILE_DIGEST = (
    "0764186d53048eb619e79783581331dd7ef7c3939215b8000239c94768237ac1"
)
SUPPORTED_HASH_SUITE_DIGEST = (
    "c24b580c31bf26bf314e746c87a93cb7ff61d3c33880fbd0ad8e31b307110805"
)
MAX_SOURCE_LINE_BYTES = 2 << 20

_DECIMAL_NAT = re.compile(r"(?:0|[1-9][0-9]*)\Z")
_DECIMAL_INT = re.compile(r"(?:0|-?[1-9][0-9]*)\Z")
_LOWER_HEX = re.compile(r"(?:[0-9a-f][0-9a-f])*\Z")
_DIGEST = re.compile(r"[0-9a-f]{64}\Z")
_U64_MAX = (1 << 64) - 1


class OracleError(Exception):
    """One classified oracle refusal."""

    def __init__(self, outcome: str, code: str, detail: str) -> None:
        super().__init__(detail)
        self.outcome = outcome
        self.code = code
        self.detail = detail


def _malformed(code: str, detail: str) -> OracleError:
    return OracleError("Malformed", code, detail)


def _noncanonical(detail: str) -> OracleError:
    return OracleError("Malformed", "NonCanonical", detail)


def _unsupported(detail: str) -> OracleError:
    return OracleError("Unsupported", "UnsupportedProfile", detail)


def _resource(counter: str, actual: int, limit: int) -> OracleError:
    return OracleError(
        "ResourceExceeded",
        "ResourceExceeded",
        f"{counter} {actual} exceeds limit {limit}",
    )


def _mismatch(code: str, detail: str) -> OracleError:
    return OracleError("Mismatch", code, detail)


@dataclass(frozen=True)
class Limits:
    max_input_bytes: int = 262_144
    max_output_bytes: int = 262_144
    max_nodes: int = 4_096
    max_depth: int = 64
    max_work: int = 1_048_576


HARD_LIMITS = Limits()
_LIMIT_FIELDS = frozenset(Limits.__dataclass_fields__)


@dataclass
class Counters:
    nodes: int = 0
    max_depth: int = 0
    edges: int = 0
    decimal_work: int = 0

    def add_node(self, depth: int, limits: Limits) -> None:
        self.nodes += 1
        if self.nodes > limits.max_nodes:
            raise _resource("nodes", self.nodes, limits.max_nodes)
        if depth > limits.max_depth:
            raise _resource("depth", depth, limits.max_depth)
        self.max_depth = max(self.max_depth, depth)

    def add_edges(self, count: int, limits: Limits) -> None:
        total = self.edges + count
        if total > limits.max_work:
            raise _resource("work", total, limits.max_work)
        self.edges = total

    def add_decimal_work(self, digits: int, limits: Limits) -> None:
        charge = digits * digits
        total = self.decimal_work + charge
        if total > limits.max_work:
            raise _resource("work", total, limits.max_work)
        self.decimal_work = total


@dataclass(frozen=True)
class Node:
    kind: str
    size: int
    scalar: Any = None
    children: tuple[Node, ...] = ()
    ordinals: tuple[int, ...] = ()


@dataclass(frozen=True)
class PriorMetaId:
    foundation_profile: str
    subject_kind: str
    digest: str

    def as_object(self) -> dict[str, Any]:
        return {
            "id_type": "prior-meta",
            "foundation_profile": self.foundation_profile,
            "subject_kind": self.subject_kind,
            "digest": self.digest,
        }


@dataclass(frozen=True)
class SemanticContentId:
    foundation_profile: str
    identity_profile: PriorMetaId
    hash_suite: PriorMetaId
    subject_kind: str
    semantic_regime: PriorMetaId
    digest: str

    def as_object(self) -> dict[str, Any]:
        return {
            "id_type": "semantic-content",
            "foundation_profile": self.foundation_profile,
            "identity_profile": self.identity_profile.as_object(),
            "hash_suite": self.hash_suite.as_object(),
            "subject_kind": self.subject_kind,
            "semantic_regime": self.semantic_regime.as_object(),
            "digest": self.digest,
        }


def _u64(value: int) -> bytes:
    if value < 0 or value > _U64_MAX:
        raise _malformed("IntegerRange", "value does not fit u64")
    return value.to_bytes(8, "big")


def _frame(value: bytes) -> bytes:
    return _u64(len(value)) + value


def _expect_object(value: Any, label: str) -> dict[str, Any]:
    if not isinstance(value, dict):
        raise _malformed("WrongShape", f"{label} must be a JSON object")
    return value


def _expect_fields(
    value: dict[str, Any], required: set[str], optional: set[str], label: str
) -> None:
    keys = set(value)
    missing = required - keys
    extra = keys - required - optional
    if missing:
        raise _malformed("MissingField", f"{label} is missing {sorted(missing)!r}")
    if extra:
        raise _malformed(
            "UnknownField", f"{label} has unknown fields {sorted(extra)!r}"
        )


def _parse_limits(raw: Any) -> Limits:
    if raw is None:
        return Limits()
    obj = _expect_object(raw, "limits")
    extra = set(obj) - _LIMIT_FIELDS
    if extra:
        raise _malformed("UnknownField", f"limits has unknown fields {sorted(extra)!r}")
    values: dict[str, int] = {}
    for name in _LIMIT_FIELDS:
        value = obj.get(name, getattr(HARD_LIMITS, name))
        if type(value) is not int or value <= 0:
            raise _malformed(
                "InvalidLimit", f"limits.{name} must be a positive JSON integer"
            )
        hard = getattr(HARD_LIMITS, name)
        if value > hard:
            raise _unsupported(f"limits.{name} exceeds this evaluator profile")
        values[name] = value
    return Limits(**values)


def _check_supported_profile(value: Any, expected: str, label: str) -> str:
    if not isinstance(value, str):
        raise _malformed("WrongShape", f"{label} must be text")
    if value != expected:
        raise _unsupported(f"unsupported {label} {value!r}")
    return value


def _symbol_bytes(value: Any, label: str) -> bytes:
    if not isinstance(value, str):
        raise _malformed("WrongShape", f"{label} must be text")
    try:
        encoded = value.encode("ascii")
    except UnicodeEncodeError as error:
        raise _malformed("InvalidSymbol", f"{label} is not ASCII") from error
    if not encoded or any(byte < 0x21 or byte > 0x7E for byte in encoded):
        raise _malformed("InvalidSymbol", f"{label} must use nonempty ASCII 0x21..0x7e")
    return encoded


def _parse_decimal(
    raw: Any,
    *,
    signed: bool,
    u64_only: bool,
    label: str,
    counters: Counters,
    limits: Limits,
) -> tuple[int, str]:
    if not isinstance(raw, str):
        raise _malformed("WrongShape", f"{label} must be a decimal string")
    pattern = _DECIMAL_INT if signed else _DECIMAL_NAT
    if pattern.fullmatch(raw) is None:
        raise _noncanonical(f"{label} is not canonical decimal")
    digits = len(raw) - (1 if raw.startswith("-") else 0)
    counters.add_decimal_work(digits, limits)
    value = int(raw, 10)
    if not signed and value < 0:
        raise _malformed("IntegerRange", f"{label} must be nonnegative")
    if u64_only and (value < 0 or value > _U64_MAX):
        raise _malformed("IntegerRange", f"{label} does not fit u64")
    return value, raw


def _minimal_magnitude(value: int) -> bytes:
    magnitude = abs(value)
    if magnitude == 0:
        return b"\x00"
    return magnitude.to_bytes((magnitude.bit_length() + 7) // 8, "big")


def _bounded_size(size: int, limits: Limits) -> int:
    if size > limits.max_input_bytes:
        raise _resource("input_bytes", size, limits.max_input_bytes)
    if size > _U64_MAX:
        raise _malformed("IntegerRange", "canonical value size does not fit u64")
    return size


def _normalize_value(raw: Any, limits: Limits) -> tuple[Node, Counters]:
    """Validate a JSON value and compute exact binary size without recursion."""

    counters = Counters()
    tasks: list[tuple[str, Any, int, Any]] = [("visit", raw, 1, None)]
    values: list[Node] = []

    while tasks:
        action, current, depth, metadata = tasks.pop()
        if action == "finish":
            kind, count, ordinals = metadata
            if count:
                children = tuple(values[-count:])
                del values[-count:]
            else:
                children = ()

            if kind == "seq":
                size = 1 + 8 + sum(8 + child.size for child in children)
            elif kind == "record":
                size = 1 + 8 + sum(16 + child.size for child in children)
            else:
                size = 1 + 8 + 8 + children[0].size
            values.append(
                Node(
                    kind,
                    _bounded_size(size, limits),
                    children=children,
                    ordinals=ordinals,
                )
            )
            continue

        obj = _expect_object(current, "value")
        tag = obj.get("tag")
        if not isinstance(tag, str):
            raise _malformed("MissingTag", "value.tag must be text")
        counters.add_node(depth, limits)

        if tag == "unit":
            _expect_fields(obj, {"tag"}, set(), "unit")
            values.append(Node("unit", 1))
        elif tag == "bool":
            _expect_fields(obj, {"tag", "value"}, set(), "bool")
            if type(obj["value"]) is not bool:
                raise _malformed("WrongShape", "bool.value must be a JSON boolean")
            values.append(Node("bool", 1, scalar=obj["value"]))
        elif tag in {"nat", "int"}:
            _expect_fields(obj, {"tag", "value"}, set(), tag)
            number, decimal = _parse_decimal(
                obj["value"],
                signed=tag == "int",
                u64_only=False,
                label=f"{tag}.value",
                counters=counters,
                limits=limits,
            )
            magnitude = _minimal_magnitude(number)
            size = 1 + 8 + len(magnitude) + (1 if tag == "int" else 0)
            values.append(
                Node(
                    tag,
                    _bounded_size(size, limits),
                    scalar=(number < 0, magnitude, decimal),
                )
            )
        elif tag == "bytes":
            _expect_fields(obj, {"tag", "value"}, set(), "bytes")
            text = obj["value"]
            if not isinstance(text, str):
                raise _malformed("WrongShape", "bytes.value must be hexadecimal text")
            if text != text.lower() or _LOWER_HEX.fullmatch(text) is None:
                raise _noncanonical("bytes.value must be lowercase even-length hex")
            byte_count = len(text) // 2
            _bounded_size(1 + 8 + byte_count, limits)
            payload = bytes.fromhex(text)
            values.append(Node("bytes", 1 + 8 + byte_count, scalar=payload))
        elif tag == "symbol":
            _expect_fields(obj, {"tag", "value"}, set(), "symbol")
            payload = _symbol_bytes(obj["value"], "symbol.value")
            values.append(
                Node(
                    "symbol",
                    _bounded_size(1 + 8 + len(payload), limits),
                    scalar=payload,
                )
            )
        elif tag == "seq":
            _expect_fields(obj, {"tag", "items"}, set(), "seq")
            items = obj["items"]
            if not isinstance(items, list):
                raise _malformed("WrongShape", "seq.items must be an array")
            counters.add_edges(len(items), limits)
            tasks.append(("finish", None, depth, ("seq", len(items), ())))
            for child in reversed(items):
                tasks.append(("visit", child, depth + 1, None))
        elif tag == "record":
            _expect_fields(obj, {"tag", "fields"}, set(), "record")
            fields = obj["fields"]
            if not isinstance(fields, list):
                raise _malformed("WrongShape", "record.fields must be an array")
            counters.add_edges(len(fields), limits)
            ordinals: list[int] = []
            children: list[Any] = []
            previous = -1
            for field in fields:
                field_obj = _expect_object(field, "record field")
                _expect_fields(field_obj, {"ordinal", "value"}, set(), "record field")
                ordinal, _ = _parse_decimal(
                    field_obj["ordinal"],
                    signed=False,
                    u64_only=True,
                    label="record ordinal",
                    counters=counters,
                    limits=limits,
                )
                if ordinal <= previous:
                    raise _noncanonical("record ordinals are not strictly increasing")
                previous = ordinal
                ordinals.append(ordinal)
                children.append(field_obj["value"])
            tasks.append(
                ("finish", None, depth, ("record", len(children), tuple(ordinals)))
            )
            for child in reversed(children):
                tasks.append(("visit", child, depth + 1, None))
        elif tag == "variant":
            _expect_fields(obj, {"tag", "case", "value"}, set(), "variant")
            case, _ = _parse_decimal(
                obj["case"],
                signed=False,
                u64_only=True,
                label="variant case",
                counters=counters,
                limits=limits,
            )
            counters.add_edges(1, limits)
            tasks.append(("finish", None, depth, ("variant", 1, (case,))))
            tasks.append(("visit", obj["value"], depth + 1, None))
        else:
            raise OracleError(
                "Unsupported", "UnsupportedValueTag", f"unsupported value tag {tag!r}"
            )

    if len(values) != 1:
        raise _malformed("WrongShape", "value did not produce one root")
    return values[0], counters


def _emit_node(root: Node) -> bytes:
    output = bytearray(root.size)
    cursor = 0
    tasks: list[tuple[str, Any]] = [("node", root)]

    def append(chunk: bytes) -> None:
        nonlocal cursor
        end = cursor + len(chunk)
        output[cursor:end] = chunk
        cursor = end

    while tasks:
        action, current = tasks.pop()
        if action == "bytes":
            append(current)
            continue

        node: Node = current
        if node.kind == "unit":
            append(b"\x00")
        elif node.kind == "bool":
            append(b"\x02" if node.scalar else b"\x01")
        elif node.kind == "nat":
            magnitude = node.scalar[1]
            append(b"\x03" + _u64(len(magnitude)) + magnitude)
        elif node.kind == "int":
            negative, magnitude, _ = node.scalar
            append(
                b"\x04"
                + (b"\x01" if negative else b"\x00")
                + _u64(len(magnitude))
                + magnitude
            )
        elif node.kind == "bytes":
            append(b"\x05" + _u64(len(node.scalar)) + node.scalar)
        elif node.kind == "symbol":
            append(b"\x06" + _u64(len(node.scalar)) + node.scalar)
        elif node.kind == "seq":
            append(b"\x07" + _u64(len(node.children)))
            for child in reversed(node.children):
                tasks.append(("node", child))
                tasks.append(("bytes", _u64(child.size)))
        elif node.kind == "record":
            append(b"\x08" + _u64(len(node.children)))
            entries = tuple(zip(node.ordinals, node.children, strict=True))
            for ordinal, child in reversed(entries):
                tasks.append(("node", child))
                tasks.append(("bytes", _u64(child.size)))
                tasks.append(("bytes", _u64(ordinal)))
        elif node.kind == "variant":
            append(b"\x09" + _u64(node.ordinals[0]) + _u64(node.children[0].size))
            tasks.append(("node", node.children[0]))
        else:  # pragma: no cover - Node is private and closed above.
            raise AssertionError(f"unknown normalized node {node.kind!r}")

    if cursor != root.size:  # pragma: no cover - internal consistency assertion.
        raise AssertionError(f"emitted {cursor} bytes for declared size {root.size}")
    return bytes(output)


def _read_u64(data: bytes, cursor: int, end: int, label: str) -> tuple[int, int]:
    next_cursor = cursor + 8
    if next_cursor > end:
        raise _malformed("TruncatedEncoding", f"truncated {label}")
    return int.from_bytes(data[cursor:next_cursor], "big"), next_cursor


def _scan_frame(data: bytes, cursor: int, end: int, label: str) -> tuple[int, int, int]:
    length, cursor = _read_u64(data, cursor, end, f"{label} length")
    child_end = cursor + length
    if child_end > end:
        raise _malformed("TruncatedEncoding", f"truncated {label}")
    if length == 0:
        raise _malformed("InvalidEncoding", f"{label} cannot be empty")
    return cursor, child_end, child_end


def _decoded_decimal(
    magnitude: bytes, negative: bool, counters: Counters, limits: Limits
) -> str:
    bit_length = int.from_bytes(magnitude, "big").bit_length()
    estimated_digits = max(1, (bit_length * 30_103) // 100_000 + 1)
    if counters.decimal_work + estimated_digits * estimated_digits > limits.max_work:
        raise _resource(
            "work",
            counters.decimal_work + estimated_digits * estimated_digits,
            limits.max_work,
        )
    number = int.from_bytes(magnitude, "big")
    decimal = str(-number if negative else number)
    digits = len(decimal) - (1 if negative else 0)
    counters.add_decimal_work(digits, limits)
    return decimal


def _decode_node(data: bytes, limits: Limits) -> tuple[Node, Counters]:
    """Decode exactly one canonical value using an explicit work stack."""

    if not data:
        raise _malformed("InvalidEncoding", "canonical value is empty")
    counters = Counters()
    tasks: list[tuple[str, Any, Any, Any]] = [("parse", 0, len(data), 1)]
    values: list[Node] = []

    while tasks:
        action, first, second, third = tasks.pop()
        if action == "finish":
            kind = first
            count = second
            ordinals = third
            if count:
                children = tuple(values[-count:])
                del values[-count:]
            else:
                children = ()
            if kind == "seq":
                size = 1 + 8 + sum(8 + child.size for child in children)
            elif kind == "record":
                size = 1 + 8 + sum(16 + child.size for child in children)
            else:
                size = 1 + 8 + 8 + children[0].size
            values.append(Node(kind, size, children=children, ordinals=ordinals))
            continue

        start = first
        end = second
        depth = third
        counters.add_node(depth, limits)
        if start >= end:
            raise _malformed("InvalidEncoding", "empty framed value")
        tag = data[start]
        cursor = start + 1

        if tag == 0x00:
            if cursor != end:
                raise _malformed("TrailingBytes", "Unit has trailing bytes")
            values.append(Node("unit", 1))
        elif tag in {0x01, 0x02}:
            if cursor != end:
                raise _malformed("TrailingBytes", "Bool has trailing bytes")
            values.append(Node("bool", 1, scalar=tag == 0x02))
        elif tag in {0x03, 0x04}:
            negative = False
            if tag == 0x04:
                if cursor >= end:
                    raise _malformed("TruncatedEncoding", "Integer sign is missing")
                sign = data[cursor]
                cursor += 1
                if sign not in {0, 1}:
                    raise _malformed("InvalidEncoding", "Integer sign is not 0 or 1")
                negative = sign == 1
            length, cursor = _read_u64(data, cursor, end, "magnitude length")
            if length == 0 or cursor + length != end:
                raise _malformed("InvalidEncoding", "invalid magnitude length")
            magnitude = data[cursor:end]
            if len(magnitude) > 1 and magnitude[0] == 0:
                raise _noncanonical("integer magnitude has a leading zero")
            if negative and magnitude == b"\x00":
                raise _noncanonical("negative zero is not canonical")
            decimal = _decoded_decimal(magnitude, negative, counters, limits)
            kind = "nat" if tag == 0x03 else "int"
            values.append(
                Node(kind, end - start, scalar=(negative, magnitude, decimal))
            )
        elif tag in {0x05, 0x06}:
            length, cursor = _read_u64(data, cursor, end, "payload length")
            if cursor + length != end:
                raise _malformed("InvalidEncoding", "invalid scalar payload length")
            payload = data[cursor:end]
            if tag == 0x05:
                values.append(Node("bytes", end - start, scalar=payload))
            else:
                if not payload or any(byte < 0x21 or byte > 0x7E for byte in payload):
                    raise _malformed(
                        "InvalidSymbol", "Symbol must use nonempty ASCII 0x21..0x7e"
                    )
                values.append(Node("symbol", end - start, scalar=payload))
        elif tag == 0x07:
            count, cursor = _read_u64(data, cursor, end, "Sequence count")
            projected_nodes = counters.nodes + count
            if projected_nodes > limits.max_nodes:
                raise _resource("nodes", projected_nodes, limits.max_nodes)
            counters.add_edges(count, limits)
            bounds: list[tuple[int, int]] = []
            for index in range(count):
                child_start, child_end, cursor = _scan_frame(
                    data, cursor, end, f"Sequence child {index}"
                )
                bounds.append((child_start, child_end))
            if cursor != end:
                raise _malformed("TrailingBytes", "Sequence has trailing bytes")
            tasks.append(("finish", "seq", count, ()))
            for child_start, child_end in reversed(bounds):
                tasks.append(("parse", child_start, child_end, depth + 1))
        elif tag == 0x08:
            count, cursor = _read_u64(data, cursor, end, "Record count")
            projected_nodes = counters.nodes + count
            if projected_nodes > limits.max_nodes:
                raise _resource("nodes", projected_nodes, limits.max_nodes)
            counters.add_edges(count, limits)
            ordinals: list[int] = []
            bounds = []
            previous = -1
            for index in range(count):
                ordinal, cursor = _read_u64(
                    data, cursor, end, f"Record ordinal {index}"
                )
                if ordinal <= previous:
                    raise _noncanonical("record ordinals are not strictly increasing")
                previous = ordinal
                child_start, child_end, cursor = _scan_frame(
                    data, cursor, end, f"Record value {index}"
                )
                ordinals.append(ordinal)
                bounds.append((child_start, child_end))
            if cursor != end:
                raise _malformed("TrailingBytes", "Record has trailing bytes")
            tasks.append(("finish", "record", count, tuple(ordinals)))
            for child_start, child_end in reversed(bounds):
                tasks.append(("parse", child_start, child_end, depth + 1))
        elif tag == 0x09:
            case, cursor = _read_u64(data, cursor, end, "Variant case")
            child_start, child_end, cursor = _scan_frame(
                data, cursor, end, "Variant payload"
            )
            if cursor != end:
                raise _malformed("TrailingBytes", "Variant has trailing bytes")
            counters.add_edges(1, limits)
            tasks.append(("finish", "variant", 1, (case,)))
            tasks.append(("parse", child_start, child_end, depth + 1))
        else:
            raise _malformed("UnknownTag", f"unknown binary tag 0x{tag:02x}")

    if len(values) != 1:
        raise _malformed("InvalidEncoding", "encoding did not produce one root")
    return values[0], counters


def _node_as_transport(root: Node) -> dict[str, Any]:
    tasks: list[tuple[str, Node | tuple[Any, ...], Any]] = [("visit", root, None)]
    values: list[dict[str, Any]] = []
    while tasks:
        action, current, metadata = tasks.pop()
        if action == "finish":
            kind, count, ordinals = metadata
            if count:
                children = values[-count:]
                del values[-count:]
            else:
                children = []
            if kind == "seq":
                values.append({"tag": "seq", "items": children})
            elif kind == "record":
                values.append(
                    {
                        "tag": "record",
                        "fields": [
                            {"ordinal": str(ordinal), "value": child}
                            for ordinal, child in zip(ordinals, children, strict=True)
                        ],
                    }
                )
            else:
                values.append(
                    {
                        "tag": "variant",
                        "case": str(ordinals[0]),
                        "value": children[0],
                    }
                )
            continue

        node = current
        if not isinstance(node, Node):  # pragma: no cover - private task stack.
            raise AssertionError("invalid node task")
        if node.kind == "unit":
            values.append({"tag": "unit"})
        elif node.kind == "bool":
            values.append({"tag": "bool", "value": node.scalar})
        elif node.kind in {"nat", "int"}:
            values.append({"tag": node.kind, "value": node.scalar[2]})
        elif node.kind == "bytes":
            values.append({"tag": "bytes", "value": node.scalar.hex()})
        elif node.kind == "symbol":
            values.append({"tag": "symbol", "value": node.scalar.decode("ascii")})
        else:
            tasks.append(
                (
                    "finish",
                    (),
                    (node.kind, len(node.children), node.ordinals),
                )
            )
            for child in reversed(node.children):
                tasks.append(("visit", child, None))
    if len(values) != 1:  # pragma: no cover - normalized Node is a tree.
        raise AssertionError("transport conversion did not produce one root")
    return values[0]


def _parse_canonical_hex(raw: Any, limits: Limits) -> bytes:
    if not isinstance(raw, str):
        raise _malformed("WrongShape", "canonical_hex must be text")
    if raw != raw.lower() or _LOWER_HEX.fullmatch(raw) is None:
        raise _noncanonical("canonical_hex must be lowercase even-length hex")
    byte_count = len(raw) // 2
    if byte_count > limits.max_input_bytes:
        raise _resource("input_bytes", byte_count, limits.max_input_bytes)
    if byte_count > limits.max_output_bytes:
        raise _resource("output_bytes", byte_count, limits.max_output_bytes)
    return bytes.fromhex(raw)


def _digest_text(raw: Any, label: str) -> str:
    if not isinstance(raw, str):
        raise _malformed("WrongShape", f"{label} must be text")
    if _DIGEST.fullmatch(raw) is None:
        if re.fullmatch(r"[0-9A-Fa-f]{64}", raw):
            raise _noncanonical(f"{label} must be lowercase hex")
        raise _malformed("InvalidDigest", f"{label} is not a SHA-256 digest")
    return raw


def _prior_meta_id_from_object(
    raw: Any, *, expected_kind: str | None = None
) -> PriorMetaId:
    obj = _expect_object(raw, "prior meta ID")
    _expect_fields(
        obj,
        {"id_type", "foundation_profile", "subject_kind", "digest"},
        set(),
        "prior meta ID",
    )
    if obj["id_type"] != "prior-meta":
        raise _malformed("WrongIdType", "expected a prior-meta identifier")
    foundation = _check_supported_profile(
        obj["foundation_profile"], FOUNDATION_PROFILE, "foundation_profile"
    )
    subject_kind = obj["subject_kind"]
    _symbol_bytes(subject_kind, "prior meta ID subject_kind")
    if subject_kind not in PRIOR_META_KINDS:
        raise _malformed(
            "WrongIdConstructor",
            f"{subject_kind!r} is not a closed prior-meta subject kind",
        )
    if expected_kind is not None and subject_kind != expected_kind:
        raise _malformed(
            "WrongReferenceKind",
            f"expected prior-meta kind {expected_kind!r}, got {subject_kind!r}",
        )
    digest = _digest_text(obj["digest"], "prior meta ID digest")
    return PriorMetaId(foundation, subject_kind, digest)


def _prior_meta_reference(identifier: PriorMetaId) -> bytes:
    return (
        _frame(identifier.foundation_profile.encode("ascii"))
        + _frame(identifier.subject_kind.encode("ascii"))
        + bytes.fromhex(identifier.digest)
    )


def _supported_identity_axes(
    identity_profile: PriorMetaId, hash_suite: PriorMetaId
) -> None:
    if identity_profile != PriorMetaId(
        FOUNDATION_PROFILE,
        IDENTITY_PROFILE_KIND,
        SUPPORTED_IDENTITY_PROFILE_DIGEST,
    ):
        raise _unsupported("unsupported identity-profile ID")
    if hash_suite != PriorMetaId(
        FOUNDATION_PROFILE,
        HASH_SUITE_KIND,
        SUPPORTED_HASH_SUITE_DIGEST,
    ):
        raise _unsupported("unsupported hash-suite ID")


def _semantic_id_from_object(raw: Any) -> SemanticContentId:
    obj = _expect_object(raw, "semantic content ID")
    _expect_fields(
        obj,
        {
            "id_type",
            "foundation_profile",
            "identity_profile",
            "hash_suite",
            "subject_kind",
            "semantic_regime",
            "digest",
        },
        set(),
        "semantic content ID",
    )
    if obj["id_type"] != "semantic-content":
        raise _malformed("WrongIdType", "expected a semantic-content identifier")
    foundation = _check_supported_profile(
        obj["foundation_profile"], FOUNDATION_PROFILE, "foundation_profile"
    )
    identity_profile = _prior_meta_id_from_object(
        obj["identity_profile"], expected_kind=IDENTITY_PROFILE_KIND
    )
    hash_suite = _prior_meta_id_from_object(
        obj["hash_suite"], expected_kind=HASH_SUITE_KIND
    )
    subject_kind = obj["subject_kind"]
    _symbol_bytes(subject_kind, "semantic content ID subject_kind")
    if subject_kind in PRIOR_META_KINDS:
        raise _malformed(
            "WrongIdConstructor",
            "prior-meta subjects cannot use the semantic-content constructor",
        )
    semantic_regime = _prior_meta_id_from_object(
        obj["semantic_regime"], expected_kind=SEMANTIC_REGIME_KIND
    )
    digest = _digest_text(obj["digest"], "semantic content ID digest")
    _supported_identity_axes(identity_profile, hash_suite)
    return SemanticContentId(
        foundation,
        identity_profile,
        hash_suite,
        subject_kind,
        semantic_regime,
        digest,
    )


def _prior_meta_preimage(subject_kind: bytes, body: bytes) -> bytes:
    return (
        PRIOR_META_DOMAIN
        + _frame(FOUNDATION_PROFILE.encode("ascii"))
        + _frame(subject_kind)
        + _frame(body)
    )


def _prior_meta_preimage_size(subject_kind: bytes, body_size: int) -> int:
    return (
        len(PRIOR_META_DOMAIN)
        + 8
        + len(FOUNDATION_PROFILE)
        + 8
        + len(subject_kind)
        + 8
        + body_size
    )


def _semantic_preimage(
    identity_profile: PriorMetaId,
    hash_suite: PriorMetaId,
    subject_kind: bytes,
    semantic_regime: PriorMetaId,
    body: bytes,
) -> bytes:
    return (
        IDENTITY_DOMAIN
        + _frame(FOUNDATION_PROFILE.encode("ascii"))
        + _frame(_prior_meta_reference(identity_profile))
        + _frame(_prior_meta_reference(hash_suite))
        + _frame(subject_kind)
        + _frame(_prior_meta_reference(semantic_regime))
        + _frame(body)
    )


def _semantic_preimage_size(
    identity_profile: PriorMetaId,
    hash_suite: PriorMetaId,
    subject_kind: bytes,
    semantic_regime: PriorMetaId,
    body_size: int,
) -> int:
    axes = (
        FOUNDATION_PROFILE.encode("ascii"),
        _prior_meta_reference(identity_profile),
        _prior_meta_reference(hash_suite),
        subject_kind,
        _prior_meta_reference(semantic_regime),
    )
    return len(IDENTITY_DOMAIN) + sum(8 + len(axis) for axis in axes) + 8 + body_size


def _semantic_id_input_size(identifier: SemanticContentId) -> int:
    axes = (
        identifier.foundation_profile.encode("ascii"),
        _prior_meta_reference(identifier.identity_profile),
        _prior_meta_reference(identifier.hash_suite),
        identifier.subject_kind.encode("ascii"),
        _prior_meta_reference(identifier.semantic_regime),
    )
    return sum(8 + len(axis) for axis in axes) + len(bytes.fromhex(identifier.digest))


def _prior_meta_id_input_size(identifier: PriorMetaId) -> int:
    return len(_prior_meta_reference(identifier))


def _usage(
    counters: Counters,
    limits: Limits,
    *,
    input_bytes: int,
    output_bytes: int,
) -> dict[str, int]:
    if input_bytes > limits.max_input_bytes:
        raise _resource("input_bytes", input_bytes, limits.max_input_bytes)
    if output_bytes > limits.max_output_bytes:
        raise _resource("output_bytes", output_bytes, limits.max_output_bytes)
    work = input_bytes + counters.nodes + counters.edges + counters.decimal_work
    if work > limits.max_work:
        raise _resource("work", work, limits.max_work)
    return {
        "input_bytes": input_bytes,
        "output_bytes": output_bytes,
        "nodes": counters.nodes,
        "max_depth": counters.max_depth,
        "work": work,
    }


def _base_request(request: Any) -> tuple[dict[str, Any], str, str, Limits]:
    obj = _expect_object(request, "request")
    case = obj.get("case")
    if not isinstance(case, str) or not case:
        raise _malformed("InvalidCase", "case must be nonempty text")
    operation = obj.get("op")
    if operation not in {
        "encode",
        "decode",
        "prior_meta_id",
        "verify_prior_meta_id",
        "content_id",
        "verify_id",
    }:
        if isinstance(operation, str):
            raise OracleError(
                "Unsupported",
                "UnsupportedOperation",
                f"unsupported operation {operation!r}",
            )
        raise _malformed("InvalidOperation", "op must be text")

    required_by_operation = {
        "encode": {"case", "op", "foundation_profile", "value"},
        "decode": {"case", "op", "foundation_profile", "canonical_hex"},
        "prior_meta_id": {
            "case",
            "op",
            "foundation_profile",
            "subject_kind",
            "value",
        },
        "verify_prior_meta_id": {
            "case",
            "op",
            "foundation_profile",
            "expected_subject_kind",
            "value",
            "content_id",
        },
        "content_id": {
            "case",
            "op",
            "foundation_profile",
            "identity_profile",
            "hash_suite",
            "subject_kind",
            "semantic_regime",
            "value",
        },
        "verify_id": {
            "case",
            "op",
            "foundation_profile",
            "expected_subject_kind",
            "identity_profile",
            "hash_suite",
            "semantic_regime",
            "value",
            "content_id",
        },
    }
    _expect_fields(
        obj,
        required_by_operation[operation],
        {"limits"},
        f"{operation} request",
    )
    foundation = _check_supported_profile(
        obj.get("foundation_profile"), FOUNDATION_PROFILE, "foundation_profile"
    )
    limits = _parse_limits(obj.get("limits"))
    return obj, case, foundation, limits


def process_request(request: Any) -> dict[str, Any]:
    """Process one already parsed request and return a deterministic result."""

    case = request.get("case", "unknown") if isinstance(request, dict) else "unknown"
    try:
        obj, case, foundation, limits = _base_request(request)
        operation = obj["op"]
        optional = {"limits"}

        if operation == "encode":
            _expect_fields(
                obj,
                {"case", "op", "foundation_profile", "value"},
                optional,
                "encode request",
            )
            node, counters = _normalize_value(obj["value"], limits)
            usage = _usage(
                counters,
                limits,
                input_bytes=node.size,
                output_bytes=node.size,
            )
            body = _emit_node(node)
            return {
                "case": case,
                "outcome": "Completed",
                "code": "OK",
                "canonical_hex": body.hex(),
                "value": _node_as_transport(node),
                "usage": usage,
            }

        if operation == "decode":
            _expect_fields(
                obj,
                {"case", "op", "foundation_profile", "canonical_hex"},
                optional,
                "decode request",
            )
            body = _parse_canonical_hex(obj["canonical_hex"], limits)
            node, counters = _decode_node(body, limits)
            usage = _usage(
                counters,
                limits,
                input_bytes=len(body),
                output_bytes=len(body),
            )
            if _emit_node(node) != body:
                raise _noncanonical("decoded value does not re-encode byte-for-byte")
            return {
                "case": case,
                "outcome": "Completed",
                "code": "OK",
                "canonical_hex": body.hex(),
                "value": _node_as_transport(node),
                "usage": usage,
            }

        if operation == "prior_meta_id":
            _expect_fields(
                obj,
                {
                    "case",
                    "op",
                    "foundation_profile",
                    "subject_kind",
                    "value",
                },
                optional,
                "prior_meta_id request",
            )
            subject_kind = _symbol_bytes(obj["subject_kind"], "subject_kind")
            if obj["subject_kind"] not in PRIOR_META_KINDS:
                raise _malformed(
                    "WrongIdConstructor",
                    "ordinary semantic subjects cannot use the prior-meta constructor",
                )
            node, counters = _normalize_value(obj["value"], limits)
            preimage_size = _prior_meta_preimage_size(subject_kind, node.size)
            usage = _usage(
                counters,
                limits,
                input_bytes=preimage_size,
                output_bytes=32,
            )
            body = _emit_node(node)
            preimage = _prior_meta_preimage(subject_kind, body)
            digest = hashlib.sha256(preimage).hexdigest()
            identifier = PriorMetaId(foundation, obj["subject_kind"], digest)
            return {
                "case": case,
                "outcome": "Completed",
                "code": "OK",
                "canonical_hex": body.hex(),
                "content_id": identifier.as_object(),
                "preimage_hex": preimage.hex(),
                "usage": usage,
            }

        if operation == "verify_prior_meta_id":
            _expect_fields(
                obj,
                {
                    "case",
                    "op",
                    "foundation_profile",
                    "expected_subject_kind",
                    "value",
                    "content_id",
                },
                optional,
                "verify_prior_meta_id request",
            )
            claimed_meta = _prior_meta_id_from_object(obj["content_id"])
            expected_kind = _symbol_bytes(
                obj["expected_subject_kind"], "expected_subject_kind"
            ).decode("ascii")
            if claimed_meta.subject_kind != expected_kind:
                raise _mismatch(
                    "WrongKind",
                    f"content kind {claimed_meta.subject_kind!r} does not match "
                    f"{expected_kind!r}",
                )
            node, counters = _normalize_value(obj["value"], limits)
            subject_kind = claimed_meta.subject_kind.encode("ascii")
            preimage_size = _prior_meta_preimage_size(subject_kind, node.size)
            usage = _usage(
                counters,
                limits,
                input_bytes=(preimage_size + _prior_meta_id_input_size(claimed_meta)),
                output_bytes=32,
            )
            body = _emit_node(node)
            digest = hashlib.sha256(
                _prior_meta_preimage(subject_kind, body)
            ).hexdigest()
            if digest != claimed_meta.digest:
                raise _mismatch(
                    "DigestMismatch",
                    "prior-meta digest does not match body and axes",
                )
            return {
                "case": case,
                "outcome": "Completed",
                "code": "OK",
                "content_id": claimed_meta.as_object(),
                "usage": usage,
            }

        if operation == "content_id":
            _expect_fields(
                obj,
                {
                    "case",
                    "op",
                    "foundation_profile",
                    "identity_profile",
                    "hash_suite",
                    "subject_kind",
                    "semantic_regime",
                    "value",
                },
                optional,
                "content_id request",
            )
            identity_profile = _prior_meta_id_from_object(
                obj["identity_profile"], expected_kind=IDENTITY_PROFILE_KIND
            )
            hash_suite = _prior_meta_id_from_object(
                obj["hash_suite"], expected_kind=HASH_SUITE_KIND
            )
            semantic_regime = _prior_meta_id_from_object(
                obj["semantic_regime"], expected_kind=SEMANTIC_REGIME_KIND
            )
            subject_kind = _symbol_bytes(obj["subject_kind"], "subject_kind")
            if obj["subject_kind"] in PRIOR_META_KINDS:
                raise _malformed(
                    "WrongIdConstructor",
                    "prior-meta subjects cannot use the semantic-content constructor",
                )
            _supported_identity_axes(identity_profile, hash_suite)
            node, counters = _normalize_value(obj["value"], limits)
            preimage_size = _semantic_preimage_size(
                identity_profile,
                hash_suite,
                subject_kind,
                semantic_regime,
                node.size,
            )
            usage = _usage(
                counters,
                limits,
                input_bytes=preimage_size,
                output_bytes=32,
            )
            body = _emit_node(node)
            preimage = _semantic_preimage(
                identity_profile,
                hash_suite,
                subject_kind,
                semantic_regime,
                body,
            )
            digest = hashlib.sha256(preimage).hexdigest()
            identifier = SemanticContentId(
                foundation,
                identity_profile,
                hash_suite,
                obj["subject_kind"],
                semantic_regime,
                digest,
            )
            return {
                "case": case,
                "outcome": "Completed",
                "code": "OK",
                "canonical_hex": body.hex(),
                "content_id": identifier.as_object(),
                "preimage_hex": preimage.hex(),
                "usage": usage,
            }

        _expect_fields(
            obj,
            {
                "case",
                "op",
                "foundation_profile",
                "expected_subject_kind",
                "identity_profile",
                "hash_suite",
                "semantic_regime",
                "value",
                "content_id",
            },
            optional,
            "verify_id request",
        )
        claimed = _semantic_id_from_object(obj["content_id"])
        expected_kind = _symbol_bytes(
            obj["expected_subject_kind"], "expected_subject_kind"
        ).decode("ascii")
        if claimed.subject_kind != expected_kind:
            raise _mismatch(
                "WrongKind",
                f"content kind {claimed.subject_kind!r} does not match {expected_kind!r}",
            )
        identity_profile = _prior_meta_id_from_object(
            obj["identity_profile"], expected_kind=IDENTITY_PROFILE_KIND
        )
        hash_suite = _prior_meta_id_from_object(
            obj["hash_suite"], expected_kind=HASH_SUITE_KIND
        )
        semantic_regime = _prior_meta_id_from_object(
            obj["semantic_regime"], expected_kind=SEMANTIC_REGIME_KIND
        )
        _supported_identity_axes(identity_profile, hash_suite)
        if claimed.identity_profile != identity_profile:
            raise _mismatch(
                "IdentityProfileMismatch",
                "content ID identity profile does not match the expected profile",
            )
        if claimed.hash_suite != hash_suite:
            raise _mismatch(
                "HashSuiteMismatch",
                "content ID hash suite does not match the expected suite",
            )
        if claimed.semantic_regime != semantic_regime:
            raise _mismatch(
                "SemanticRegimeMismatch",
                "content ID semantic regime does not match the expected regime",
            )
        node, counters = _normalize_value(obj["value"], limits)
        subject_kind = claimed.subject_kind.encode("ascii")
        preimage_size = _semantic_preimage_size(
            identity_profile,
            hash_suite,
            subject_kind,
            semantic_regime,
            node.size,
        )
        usage = _usage(
            counters,
            limits,
            input_bytes=preimage_size + _semantic_id_input_size(claimed),
            output_bytes=32,
        )
        body = _emit_node(node)
        digest = hashlib.sha256(
            _semantic_preimage(
                identity_profile,
                hash_suite,
                subject_kind,
                semantic_regime,
                body,
            )
        ).hexdigest()
        if digest != claimed.digest:
            raise _mismatch(
                "DigestMismatch", "content digest does not match body and axes"
            )
        return {
            "case": case,
            "outcome": "Completed",
            "code": "OK",
            "content_id": claimed.as_object(),
            "usage": usage,
        }
    except OracleError as error:
        return {
            "case": case if isinstance(case, str) and case else "unknown",
            "outcome": error.outcome,
            "code": error.code,
            "detail": error.detail,
        }


class _DuplicateKey(ValueError):
    pass


def _object_without_duplicates(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise _DuplicateKey(f"duplicate JSON key {key!r}")
        result[key] = value
    return result


def _reject_constant(value: str) -> None:
    raise ValueError(f"non-finite JSON number {value}")


def _line_result(raw_line: bytes, line_number: int) -> dict[str, Any]:
    if len(raw_line) > MAX_SOURCE_LINE_BYTES:
        error = _resource("source_line_bytes", len(raw_line), MAX_SOURCE_LINE_BYTES)
        return {
            "case": f"line-{line_number}",
            "outcome": error.outcome,
            "code": error.code,
            "detail": error.detail,
        }
    try:
        text = raw_line.decode("utf-8")
    except UnicodeDecodeError:
        return {
            "case": f"line-{line_number}",
            "outcome": "Malformed",
            "code": "InvalidUtf8",
            "detail": "fixture line is not UTF-8",
        }
    try:
        request = json.loads(
            text,
            object_pairs_hook=_object_without_duplicates,
            parse_constant=_reject_constant,
        )
    except (json.JSONDecodeError, _DuplicateKey, ValueError) as error:
        return {
            "case": f"line-{line_number}",
            "outcome": "Malformed",
            "code": "InvalidJson",
            "detail": str(error),
        }
    return process_request(request)


def run_json_lines(stream: BinaryIO) -> Iterable[dict[str, Any]]:
    for line_number, raw_line in enumerate(stream, 1):
        if raw_line.endswith(b"\n"):
            raw_line = raw_line[:-1]
            if raw_line.endswith(b"\r"):
                raw_line = raw_line[:-1]
        yield _line_result(raw_line, line_number)


def main(argv: list[str]) -> int:
    if len(argv) > 2:
        print(f"usage: {argv[0]} [REQUESTS.jsonl|-]", file=sys.stderr)
        return 2
    path = argv[1] if len(argv) == 2 else "-"
    if path == "-":
        stream = sys.stdin.buffer
        close = False
    else:
        stream = Path(path).open("rb")
        close = True
    try:
        for result in run_json_lines(stream):
            print(json.dumps(result, sort_keys=True, separators=(",", ":")))
    finally:
        if close:
            stream.close()
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
