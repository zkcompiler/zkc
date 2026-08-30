"""Canonical finite terms and content identities for the evaluator."""

from __future__ import annotations

import hashlib
import json
from typing import Any

from .diagnostics import MalformedInput


MAX_JSON_BYTES = 1 << 20


def _unique_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise MalformedInput(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def load_json_bytes(raw: bytes) -> Any:
    if type(raw) is not bytes or len(raw) > MAX_JSON_BYTES:
        raise MalformedInput("JSON input exceeds the exact byte bound")
    try:
        text = raw.decode("utf-8")
        return json.loads(text, object_pairs_hook=_unique_object)
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise MalformedInput(f"invalid JSON: {error}") from error


def canonical_json_bytes(value: Any) -> bytes:
    try:
        return json.dumps(
            value,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=True,
            allow_nan=False,
        ).encode("ascii")
    except (TypeError, ValueError) as error:
        raise MalformedInput(f"value is not canonical JSON: {error}") from error


def canonical_json_text(value: Any, *, pretty: bool = False) -> str:
    if pretty:
        try:
            return (
                json.dumps(
                    value,
                    sort_keys=True,
                    indent=2,
                    ensure_ascii=True,
                    allow_nan=False,
                )
                + "\n"
            )
        except (TypeError, ValueError) as error:
            raise MalformedInput(f"value is not canonical JSON: {error}") from error
    return canonical_json_bytes(value).decode("ascii")


def framed_hash(domain: str, parts: tuple[bytes, ...]) -> str:
    if type(domain) is not str or not domain:
        raise MalformedInput("identity domain must be a nonempty string")
    digest = hashlib.sha256()
    encoded_domain = domain.encode("ascii")
    digest.update(len(encoded_domain).to_bytes(8, "big"))
    digest.update(encoded_domain)
    for part in parts:
        if type(part) is not bytes:
            raise MalformedInput("identity preimage parts must be bytes")
        digest.update(len(part).to_bytes(8, "big"))
        digest.update(part)
    return f"sha256:{digest.hexdigest()}"


def semantic_id(kind: str, body: Any) -> str:
    return framed_hash(
        f"zkc.semantic.{kind}",
        (b"semantic-regime:duplex-sponge-evaluation", canonical_json_bytes(body)),
    )


def artifact_id(raw: bytes) -> str:
    return framed_hash("zkc.artifact.bytes", (raw,))


def evidence_id(subject: str, basis: str, payload: Any) -> str:
    return framed_hash(
        "zkc.evidence.record",
        (subject.encode("ascii"), basis.encode("ascii"), canonical_json_bytes(payload)),
    )


def exact_keys(value: Any, expected: set[str], *, where: str) -> dict[str, Any]:
    if type(value) is not dict:
        raise MalformedInput(f"{where} must be an object")
    if set(value) != expected:
        raise MalformedInput(f"{where} keys differ")
    return value

def exact_nat(value: Any, *, maximum: int, where: str) -> int:
    if type(value) is not int or not 0 <= value <= maximum:
        raise MalformedInput(f"{where} is outside 0..{maximum}")
    return value
