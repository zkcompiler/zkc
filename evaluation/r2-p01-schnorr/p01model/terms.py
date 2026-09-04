"""Bounded identity terms and result classes for the independent P01 probe.

This module is intentionally local.  The closed FRI-Grind witness binds its
own evaluator sources into validation identities, so P01 does not import or
refactor that package.  Cross-witness extraction is deferred until both probes
have survived independently.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum
import hashlib
from typing import Any, Mapping


MAX_TERM_BYTES = 1 << 18
MAX_TERM_NODES = 2048
MAX_TERM_DEPTH = 24


class TermEncodingError(ValueError):
    """A value is outside the P01 closed finite-term language."""


def _u64(value: int) -> bytes:
    if value < 0 or value >= 1 << 64:
        raise TermEncodingError("length is outside unsigned 64-bit range")
    return value.to_bytes(8, "big")


def encode_term(value: Any) -> bytes:
    """Encode a bounded canonical term with explicit tags and lengths."""

    nodes = 0

    def encode(current: Any, depth: int) -> bytes:
        nonlocal nodes
        nodes += 1
        if nodes > MAX_TERM_NODES:
            raise TermEncodingError("identity term exceeds node bound")
        if depth > MAX_TERM_DEPTH:
            raise TermEncodingError("identity term exceeds depth bound")

        if current is None:
            result = b"N"
        elif current is False:
            result = b"F"
        elif current is True:
            result = b"T"
        elif isinstance(current, int):
            sign = b"+" if current >= 0 else b"-"
            magnitude = abs(current)
            body = b"\x00" if magnitude == 0 else magnitude.to_bytes(
                (magnitude.bit_length() + 7) // 8, "big"
            )
            result = b"I" + sign + _u64(len(body)) + body
        elif isinstance(current, str):
            body = current.encode("utf-8")
            result = b"S" + _u64(len(body)) + body
        elif isinstance(current, bytes):
            result = b"B" + _u64(len(current)) + current
        elif isinstance(current, (tuple, list)):
            children = [encode(child, depth + 1) for child in current]
            result = b"L" + _u64(len(children)) + b"".join(
                _u64(len(child)) + child for child in children
            )
        elif isinstance(current, Mapping):
            if not all(isinstance(key, str) for key in current):
                raise TermEncodingError("identity maps require string keys")
            entries = []
            for key in sorted(current):
                key_body = encode(key, depth + 1)
                value_body = encode(current[key], depth + 1)
                entries.append(
                    _u64(len(key_body))
                    + key_body
                    + _u64(len(value_body))
                    + value_body
                )
            result = b"M" + _u64(len(entries)) + b"".join(entries)
        else:
            raise TermEncodingError(
                f"unsupported identity term type: {type(current)!r}"
            )

        if len(result) > MAX_TERM_BYTES:
            raise TermEncodingError("identity term exceeds byte bound")
        return result

    return encode(value, 0)


SEMANTIC_REGIME_TERM = {
    "name": "zkc.r2.p01.closed-finite-term",
    "version": 1,
    "hash": "sha256",
    "term_abi": "tagged-length-delimited-sorted-string-map.v1",
    "sequence_normalization": "tuple-and-list-as-canonical-sequence",
    "max_bytes": MAX_TERM_BYTES,
    "max_nodes": MAX_TERM_NODES,
    "max_depth": MAX_TERM_DEPTH,
}
SEMANTIC_REGIME_ID = "sha256:" + hashlib.sha256(
    b"zkc-p01-semantic-regime\x00" + encode_term(SEMANTIC_REGIME_TERM)
).hexdigest()


def semantic_id(domain: str, preimage: Any) -> str:
    """Hash one P01 semantic preimage under the explicit local regime."""

    if not isinstance(domain, str):
        raise TermEncodingError("identity domain must be text")
    try:
        domain_bytes = domain.encode("ascii")
    except UnicodeEncodeError as error:
        raise TermEncodingError("identity domain must be ASCII") from error
    if not domain_bytes or len(domain_bytes) > 192:
        raise TermEncodingError("identity domain length is outside the profile")
    regime = SEMANTIC_REGIME_ID.encode("ascii")
    body = encode_term(preimage)
    digest = hashlib.sha256(
        b"zkc-p01-id\x00"
        + _u64(len(regime))
        + regime
        + _u64(len(domain_bytes))
        + domain_bytes
        + body
    ).hexdigest()
    return f"sha256:{digest}"


class Outcome(str, Enum):
    AFFIRMATIVE = "Affirmative"
    SEMANTIC_NEGATIVE = "SemanticNegative"
    MISMATCH = "Mismatch"
    MALFORMED = "Malformed"
    UNSUPPORTED = "Unsupported"
    CANNOT_ANSWER = "CannotAnswer"
    MISSING_DEPENDENCY = "MissingDependency"
    REFUSED = "Refused"
    RESOURCE_EXCEEDED = "ResourceExceeded"
    CHECKER_FAILURE = "CheckerFailure"
    NOT_EXERCISED = "NotExercised"


@dataclass(frozen=True)
class Result:
    outcome: Outcome
    boundary: str
    code: str
    detail: str
    subject: str = ""
    evidence: Mapping[str, Any] = field(default_factory=dict)

    def term(self) -> dict[str, Any]:
        return {
            "outcome": self.outcome.value,
            "boundary": self.boundary,
            "code": self.code,
            "detail": self.detail,
            "subject": self.subject,
            "evidence": dict(self.evidence),
        }


def result(
    outcome: Outcome,
    boundary: str,
    code: str,
    detail: str,
    subject: str = "",
    **evidence: Any,
) -> Result:
    return Result(outcome, boundary, code, detail, subject, evidence)


def affirmative(
    boundary: str,
    code: str,
    detail: str,
    subject: str = "",
    **evidence: Any,
) -> Result:
    return result(
        Outcome.AFFIRMATIVE,
        boundary,
        code,
        detail,
        subject,
        **evidence,
    )
