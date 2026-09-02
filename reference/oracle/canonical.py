"""Canonical values, identity digests, and fail-closed JSON loading.

This module is the dependency-free bottom of the durable reference twin.  It
owns no PIR, OIR, registry, execution, or proof-system semantics.  Keeping the
canonical domain here lets those higher layers share one exact encoding while
remaining independently reviewable.
"""

from __future__ import annotations

import hashlib
import json
from typing import Any


class Refusal(ValueError):
    """A failed static judgment."""


def canon_json(value: Any) -> str:
    """The single canonical JSON spelling used by every digest."""

    return json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=True
    )


def tagged_digest(tag: str, value: Any, *, reference: bool = True) -> str:
    digest = hashlib.sha256(tag.encode("ascii") + canon_json(value).encode("ascii"))
    encoded = digest.hexdigest()
    return "sha256:" + encoded if reference else encoded


def material_construct(tag: str, typed_arguments: list[list[Any]]) -> str:
    """Evaluate the sole MaterialExpr reference constructor."""

    if not isinstance(tag, str) or not tag or not all(
        0x20 <= ord(char) <= 0x7E for char in tag
    ):
        raise Refusal("material constructor tag is not printable ASCII")
    valid_sorts = {"ref", "refs", "claim", "claims", "atom"}
    if any(
        not isinstance(argument, list)
        or len(argument) != 2
        or argument[0] not in valid_sorts
        for argument in typed_arguments
    ):
        raise Refusal("material constructor has malformed typed arguments")
    return tagged_digest(
        "zkc/material-expr\n",
        ["construct", tag, typed_arguments],
    )


def is_sha256_ref(value: Any) -> bool:
    return (
        isinstance(value, str)
        and len(value) == 71
        and value.startswith("sha256:")
        and all(char in "0123456789abcdef" for char in value[7:])
    )


MAX_ATTR_DEPTH = 64


def check_domain(value: Any, depth: int = 0) -> None:
    """Admit exactly the identity-bearing MLIR attribute domain."""

    if depth > MAX_ATTR_DEPTH:
        raise ValueError("[zkc-E228] canonical attribute nesting exceeds 64")
    if value is None:
        return
    if type(value) is bool:
        raise ValueError("[zkc-E228] booleans are outside the canonical domain")
    if type(value) is int:
        if not -(1 << 63) <= value < 1 << 63:
            raise ValueError("[zkc-E228] integer is outside signed 64-bit range")
        return
    if isinstance(value, str):
        if not all(0x20 <= ord(char) <= 0x7E for char in value):
            raise ValueError("[zkc-E228] strings must be printable ASCII")
        return
    if isinstance(value, (list, tuple)):
        for member in value:
            check_domain(member, depth + 1)
        return
    if isinstance(value, dict):
        for key, member in value.items():
            if not isinstance(key, str):
                raise ValueError("[zkc-E228] canonical dictionary keys are strings")
            check_domain(key, depth + 1)
            check_domain(member, depth + 1)
        return
    raise ValueError(f"[zkc-E228] unsupported canonical value {type(value).__name__}")


def check_atom_domain(value: Any, depth: int = 0) -> None:
    """Admit the non-null kernel attribute subset used by registry atoms."""

    if depth > MAX_ATTR_DEPTH:
        raise Refusal("canonical atom nesting exceeds 64")
    if value is None or type(value) is bool:
        raise Refusal("null and booleans are outside the canonical atom domain")
    if type(value) is int:
        if not -(1 << 63) <= value < 1 << 63:
            raise Refusal("canonical atom integer is outside signed 64-bit range")
        return
    if isinstance(value, str):
        if not all(0x20 <= ord(char) <= 0x7E for char in value):
            raise Refusal("canonical atom string is not printable ASCII")
        return
    if isinstance(value, (list, tuple)):
        for member in value:
            check_atom_domain(member, depth + 1)
        return
    if isinstance(value, dict):
        for key, member in value.items():
            if not isinstance(key, str) or not key:
                raise Refusal("canonical atom object keys must be nonempty strings")
            check_atom_domain(key, depth + 1)
            check_atom_domain(member, depth + 1)
        return
    raise Refusal(f"unsupported canonical atom {type(value).__name__}")


def _unique_keys(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    """Refuse a duplicate decoded object key at any depth."""

    seen: dict[str, Any] = {}
    for key, value in pairs:
        if key in seen:
            raise Refusal(f"duplicate JSON object key {key!r}")
        seen[key] = value
    return seen


def _reject_non_integer_number(literal: str) -> Any:
    raise Refusal(
        "a numeric value leaves the encoding domain: exact values are "
        "decimal integers or decimal strings"
    )


def load_json(text: str) -> Any:
    """Parse one authority input under the canonical JSON domain.

    Duplicate decoded keys have no last-wins reading. Floating-point syntax
    and Python's non-standard NaN/Infinity constants have no representation in
    the integer-only encoding domain.
    """

    try:
        return json.loads(
            text,
            object_pairs_hook=_unique_keys,
            parse_float=_reject_non_integer_number,
            parse_constant=_reject_non_integer_number,
        )
    except json.JSONDecodeError as error:
        raise Refusal(f"invalid JSON: {error.msg}") from None


def _message_count_is_dynamic(multiplicity: dict[str, Any]) -> bool:
    return multiplicity == {"same_as": "consumed_claims"}


def _resolve_message_count(
    multiplicity: dict[str, Any], consumed_claims: int
) -> int:
    if _message_count_is_dynamic(multiplicity):
        return consumed_claims
    return multiplicity["exact"]


def _closed(body: dict[str, Any], fields: set[str], where: str) -> None:
    unknown = set(body) - fields
    missing = fields - set(body)
    if unknown or missing:
        raise Refusal(
            f"{where} has missing={sorted(missing)} unknown={sorted(unknown)}"
        )
