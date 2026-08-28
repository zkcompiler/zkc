"""Strict, network-free provenance for the native FRI/IOR witness.

The source ledger is a bounded public input.  It authenticates exact bytes and
selected Git-source bytes; it does not authenticate a theorem, an
interpretation, a remote server, or an implementation-conformance claim.

This module deliberately keeps four identity lanes apart.  ``SemanticId`` is
owned by :mod:`friiormodel.terms` and is never constructed here.
``ArtifactContentId`` identifies exact bytes, ``CanonicalContentId`` identifies
one normalized JSON value, and ``ValidationBasisId`` identifies an evaluator
source basis under a separate domain.  Similar digest shapes do not permit a
cast between those carriers.

Normal loading performs no network operation.  Comparing cached or freshly
retrieved upstream bytes with the ledger is a separate optional audit and is
intentionally outside this module.
"""

from __future__ import annotations

from copy import deepcopy
from dataclasses import dataclass, field
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat
from typing import Any, Mapping, TypeAlias
from urllib.parse import urlsplit

from .terms import (
    CheckResult,
    ModelFailure,
    OutcomeClass,
    affirmative,
    checker_failure,
)


SOURCE_LEDGER_SCHEMA = "zkc.native-fri-ior.source-ledger.v1"
SOURCE_LEDGER_SCOPE = "constructive-execution-basis"

MAX_LEDGER_BYTES = 1 << 16
MAX_CANONICAL_JSON_BYTES = 1 << 16
MAX_JSON_NODES = 4096
MAX_JSON_DEPTH = 20
MAX_STRING_BYTES = 4096
MAX_PAPER_BYTES = 1 << 26
MAX_IMPLEMENTATION_FILE_BYTES = 1 << 20

PAPER_IDS = (
    "bcs-iop-2016-116-r2",
    "eccc-fri-tr17-134-r2",
    "ethstark-2021-582-r3",
    "fri-fs-2023-1071-r7",
    "icalp-fri-2018-14",
)
IMPLEMENTATION_SNAPSHOT_FILE_COUNTS = {
    "plonky3-3da3467-fri-profile": 12,
    "winterfell-2f78ee9-fri-profile": 17,
}

_TOP_LEVEL_KEYS = (
    "schema",
    "scope",
    "frozen_on",
    "papers",
    "implementation_snapshots",
    "claim_boundary",
)
_PAPER_KEYS = (
    "id",
    "kind",
    "title",
    "landing_url",
    "artifact_url",
    "revision",
    "content",
    "usage",
)
_PAPER_REVISION_KEYS = ("label", "archive_date")
_PAPER_CONTENT_KEYS = ("artifact_content_id", "byte_length")
_SNAPSHOT_KEYS = (
    "id",
    "kind",
    "repository_url",
    "revision",
    "selected_files",
    "profile_boundary",
    "interpretation_constraints",
)
_SNAPSHOT_REVISION_KEYS = (
    "object_format",
    "commit",
    "tree",
    "committer_date",
    "subject",
)
_FILE_KEYS = ("path", "artifact_content_id", "byte_length")
_CLAIM_KEYS = (
    "establishes",
    "excluded_from_this_ledger",
    "does_not_establish",
)

_REQUIRED_ESTABLISHES = (
    "exact-byte provenance for the five paper artifacts used by the executable "
    "construction",
    "exact Git revisions and selected implementation-source bytes used as "
    "comparison inputs",
)
_REQUIRED_EXCLUSIONS = (
    "AFK multi-round Fiat-Shamir and other analysis-only theorem sources",
    "Concrete FRI parameter studies",
    "DEEP-FRI, STIR, Circle FRI, BaseFold, WHIR, and other design-pressure "
    "variants",
    "the complete documentation and theorem corpus",
)
_REQUIRED_NONCLAIMS = (
    "correct interpretation of a source",
    "theorem truth or applicability",
    "implementation conformance",
    "cryptographic security",
)

_HEX_64 = re.compile(r"[0-9a-f]{64}\Z")
_HEX_40 = re.compile(r"[0-9a-f]{40}\Z")
_IDENTIFIER = re.compile(r"[a-z][a-z0-9.-]{0,127}\Z")
_TOKEN = re.compile(r"[a-z][a-z0-9-]{0,127}\Z")
_DATE = re.compile(r"[0-9]{4}-[0-9]{2}-[0-9]{2}\Z")
_COMMITTER_DATE = re.compile(
    r"[0-9]{4}-[0-9]{2}-[0-9]{2}T[0-9]{2}:[0-9]{2}:[0-9]{2}[+-]"
    r"[0-9]{2}:[0-9]{2}\Z"
)
_PATH_PART = re.compile(r"[A-Za-z0-9._-]+\Z")

JsonScalar: TypeAlias = None | bool | int | str
JsonValue: TypeAlias = JsonScalar | list["JsonValue"] | dict[str, "JsonValue"]


def _failure(
    outcome: OutcomeClass,
    boundary: str,
    code: str,
    detail: str,
) -> ModelFailure:
    return ModelFailure(outcome, boundary, code, detail)


def _malformed(code: str, detail: str, *, boundary: str = "provenance:formation") -> ModelFailure:
    return _failure(OutcomeClass.MALFORMED, boundary, code, detail)


def _digest_text(value: object, *, code: str) -> str:
    if not isinstance(value, str) or _HEX_64.fullmatch(value) is None:
        raise _malformed(code, "a SHA-256 digest must be 64 lowercase hexadecimal digits")
    return value


@dataclass(frozen=True, order=True, slots=True)
class ArtifactContentId:
    """Identity of exact artifact bytes: ``SHA256(exact bytes)``."""

    digest: str

    def __post_init__(self) -> None:
        _digest_text(self.digest, code="FRI-IOR-PROVENANCE-001")

    def to_text(self) -> str:
        return f"sha256:{self.digest}"

    def __str__(self) -> str:
        return self.to_text()

    @classmethod
    def parse(cls, value: object) -> "ArtifactContentId":
        prefix = "sha256:"
        if not isinstance(value, str) or not value.startswith(prefix):
            raise _malformed(
                "FRI-IOR-PROVENANCE-002",
                "an ArtifactContentId must use the sha256: prefix",
            )
        return cls(value[len(prefix) :])


@dataclass(frozen=True, order=True, slots=True)
class CanonicalContentId:
    """Identity of the compact canonical JSON encoding of one value."""

    digest: str

    def __post_init__(self) -> None:
        _digest_text(self.digest, code="FRI-IOR-PROVENANCE-003")

    def to_text(self) -> str:
        return f"canonical-sha256:{self.digest}"

    def __str__(self) -> str:
        return self.to_text()

    @classmethod
    def parse(cls, value: object) -> "CanonicalContentId":
        prefix = "canonical-sha256:"
        if not isinstance(value, str) or not value.startswith(prefix):
            raise _malformed(
                "FRI-IOR-PROVENANCE-004",
                "a CanonicalContentId must use the canonical-sha256: prefix",
            )
        return cls(value[len(prefix) :])


@dataclass(frozen=True, order=True, slots=True)
class ValidationBasisId:
    """Domain-separated identity of evaluator/report implementation sources."""

    digest: str

    def __post_init__(self) -> None:
        _digest_text(self.digest, code="FRI-IOR-PROVENANCE-005")

    def to_text(self) -> str:
        return f"validation-sha256:{self.digest}"

    def __str__(self) -> str:
        return self.to_text()

    @classmethod
    def parse(cls, value: object) -> "ValidationBasisId":
        prefix = "validation-sha256:"
        if not isinstance(value, str) or not value.startswith(prefix):
            raise _malformed(
                "FRI-IOR-PROVENANCE-006",
                "a ValidationBasisId must use the validation-sha256: prefix",
            )
        return cls(value[len(prefix) :])


def artifact_content_id(raw: bytes) -> ArtifactContentId:
    """Identify exact bytes without interpreting their content."""

    if not isinstance(raw, bytes):
        raise _malformed(
            "FRI-IOR-PROVENANCE-007",
            "exact artifact identity requires a bytes value",
        )
    return ArtifactContentId(hashlib.sha256(raw).hexdigest())


def _reject_float(value: str) -> Any:
    raise _malformed(
        "FRI-IOR-PROVENANCE-008",
        f"JSON floating-point values are unsupported: {value}",
        boundary="provenance:json-parse",
    )


def _reject_constant(value: str) -> Any:
    raise _malformed(
        "FRI-IOR-PROVENANCE-009",
        f"non-finite JSON constants are unsupported: {value}",
        boundary="provenance:json-parse",
    )


def _bounded_integer(value: str) -> int:
    parsed = int(value, 10)
    if not -(1 << 63) <= parsed < 1 << 64:
        raise _failure(
            OutcomeClass.DETERMINISTIC_LIMIT_EXCEEDED,
            "provenance:json-parse",
            "FRI-IOR-PROVENANCE-010",
            "a JSON integer exceeds the evaluator's bounded integer carrier",
        )
    return parsed


def _unique_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise _malformed(
                "FRI-IOR-PROVENANCE-011",
                f"duplicate JSON key: {key}",
                boundary="provenance:json-parse",
            )
        result[key] = value
    return result


def _bounded_json_tree(value: Any) -> JsonValue:
    nodes = 0

    def visit(current: Any, depth: int) -> JsonValue:
        nonlocal nodes
        nodes += 1
        if nodes > MAX_JSON_NODES or depth > MAX_JSON_DEPTH:
            raise _failure(
                OutcomeClass.DETERMINISTIC_LIMIT_EXCEEDED,
                "provenance:json-parse",
                "FRI-IOR-PROVENANCE-012",
                "the JSON value exceeds its node or depth bound",
            )
        if current is None or isinstance(current, bool):
            return current
        if isinstance(current, int):
            return current
        if isinstance(current, str):
            if len(current.encode("utf-8")) > MAX_STRING_BYTES:
                raise _failure(
                    OutcomeClass.DETERMINISTIC_LIMIT_EXCEEDED,
                    "provenance:json-parse",
                    "FRI-IOR-PROVENANCE-013",
                    "a JSON string exceeds its byte bound",
                )
            return current
        if isinstance(current, list):
            return [visit(item, depth + 1) for item in current]
        if isinstance(current, Mapping):
            if any(type(key) is not str for key in current):
                raise _malformed(
                    "FRI-IOR-PROVENANCE-014",
                    "JSON object keys must be text",
                    boundary="provenance:json-parse",
                )
            return {
                key: visit(item, depth + 1)
                for key, item in current.items()
            }
        raise _malformed(
            "FRI-IOR-PROVENANCE-015",
            f"unsupported JSON value type: {type(current).__name__}",
            boundary="provenance:json-parse",
        )

    return visit(value, 0)


def load_bounded_json_bytes(
    raw: bytes,
    *,
    maximum: int = MAX_LEDGER_BYTES,
) -> JsonValue:
    """Parse bounded UTF-8 JSON while refusing duplicates, floats, and NaN."""

    if not isinstance(raw, bytes):
        raise _malformed(
            "FRI-IOR-PROVENANCE-016",
            "JSON input must be exact bytes",
            boundary="provenance:json-parse",
        )
    if type(maximum) is not int or maximum <= 0:
        raise _malformed(
            "FRI-IOR-PROVENANCE-017",
            "the JSON input byte bound must be a positive integer",
            boundary="provenance:json-parse",
        )
    if len(raw) > maximum:
        raise _failure(
            OutcomeClass.DETERMINISTIC_LIMIT_EXCEEDED,
            "provenance:json-parse",
            "FRI-IOR-PROVENANCE-018",
            "the JSON input exceeds its byte bound",
        )
    try:
        text = raw.decode("utf-8", errors="strict")
    except UnicodeDecodeError as error:
        raise _malformed(
            "FRI-IOR-PROVENANCE-019",
            "JSON input is not valid UTF-8",
            boundary="provenance:json-parse",
        ) from error
    try:
        value = json.loads(
            text,
            object_pairs_hook=_unique_object,
            parse_float=_reject_float,
            parse_int=_bounded_integer,
            parse_constant=_reject_constant,
        )
    except ModelFailure:
        raise
    except (json.JSONDecodeError, RecursionError, ValueError) as error:
        raise _malformed(
            "FRI-IOR-PROVENANCE-020",
            "JSON input is malformed",
            boundary="provenance:json-parse",
        ) from error
    return _bounded_json_tree(value)


def _canonical_json_value(value: Any) -> JsonValue:
    bounded = _bounded_json_tree(value)
    if isinstance(bounded, dict):
        return {
            key: _canonical_json_value(bounded[key])
            for key in sorted(bounded)
        }
    if isinstance(bounded, list):
        return [_canonical_json_value(item) for item in bounded]
    return bounded


def canonical_json_bytes(value: Any) -> bytes:
    """Return the compact, sorted-key JSON encoding of the bounded value."""

    canonical = _canonical_json_value(value)
    encoded = json.dumps(
        canonical,
        ensure_ascii=True,
        allow_nan=False,
        sort_keys=True,
        separators=(",", ":"),
    ).encode("ascii")
    if len(encoded) > MAX_CANONICAL_JSON_BYTES:
        raise _failure(
            OutcomeClass.DETERMINISTIC_LIMIT_EXCEEDED,
            "provenance:canonicalization",
            "FRI-IOR-PROVENANCE-021",
            "canonical JSON exceeds its byte bound",
        )
    return encoded


def canonical_content_id(value: Any) -> CanonicalContentId:
    """Identify one JSON value independently of insignificant whitespace."""

    return CanonicalContentId(hashlib.sha256(canonical_json_bytes(value)).hexdigest())


def canonical_json_content_id(value: Any) -> CanonicalContentId:
    """Spell out the JSON carrier for callers composing public reports."""

    return canonical_content_id(value)


def validation_basis_id(component: str, preimage: Any) -> ValidationBasisId:
    """Identify evaluator sources under a lane distinct from all content IDs."""

    if not isinstance(component, str) or _IDENTIFIER.fullmatch(component) is None:
        raise _malformed(
            "FRI-IOR-PROVENANCE-022",
            "a validation-basis component must be a lowercase ASCII identifier",
        )
    label = component.encode("ascii")
    body = canonical_json_bytes(preimage)
    framed = (
        b"zkc.native-fri-ior.validation-basis.v1\x00"
        + len(label).to_bytes(4, "big")
        + label
        + len(body).to_bytes(8, "big")
        + body
    )
    return ValidationBasisId(hashlib.sha256(framed).hexdigest())


def _object(value: Any, *, where: str, keys: tuple[str, ...]) -> dict[str, Any]:
    if not isinstance(value, dict):
        raise _malformed(
            "FRI-IOR-PROVENANCE-023",
            f"{where} must be a JSON object",
            boundary="provenance:ledger-formation",
        )
    if tuple(value) != keys:
        raise _malformed(
            "FRI-IOR-PROVENANCE-024",
            f"{where} must have exactly the declared keys in canonical order",
            boundary="provenance:ledger-formation",
        )
    return value


def _array(value: Any, *, where: str) -> list[Any]:
    if not isinstance(value, list):
        raise _malformed(
            "FRI-IOR-PROVENANCE-025",
            f"{where} must be a JSON array",
            boundary="provenance:ledger-formation",
        )
    return value


def _text(value: Any, *, where: str, maximum: int = 512) -> str:
    if not isinstance(value, str) or not value:
        raise _malformed(
            "FRI-IOR-PROVENANCE-026",
            f"{where} must be nonempty text",
            boundary="provenance:ledger-formation",
        )
    if len(value.encode("utf-8")) > maximum:
        raise _failure(
            OutcomeClass.DETERMINISTIC_LIMIT_EXCEEDED,
            "provenance:ledger-formation",
            "FRI-IOR-PROVENANCE-027",
            f"{where} exceeds its byte bound",
        )
    return value


def _identifier(value: Any, *, where: str) -> str:
    text = _text(value, where=where, maximum=128)
    if _IDENTIFIER.fullmatch(text) is None:
        raise _malformed(
            "FRI-IOR-PROVENANCE-028",
            f"{where} is not a canonical lowercase ASCII identifier",
            boundary="provenance:ledger-formation",
        )
    return text


def _token(value: Any, *, where: str) -> str:
    text = _text(value, where=where, maximum=128)
    if _TOKEN.fullmatch(text) is None:
        raise _malformed(
            "FRI-IOR-PROVENANCE-029",
            f"{where} is not a canonical lowercase ASCII token",
            boundary="provenance:ledger-formation",
        )
    return text


def _https_url(value: Any, *, where: str) -> str:
    text = _text(value, where=where, maximum=1024)
    try:
        parsed = urlsplit(text)
        port = parsed.port
    except ValueError as error:
        raise _malformed(
            "FRI-IOR-PROVENANCE-030",
            f"{where} is not a formed URL",
            boundary="provenance:ledger-formation",
        ) from error
    if (
        parsed.scheme != "https"
        or not parsed.hostname
        or parsed.username is not None
        or parsed.password is not None
        or parsed.fragment
        or port is not None
        or "\\" in text
    ):
        raise _malformed(
            "FRI-IOR-PROVENANCE-031",
            f"{where} must be an HTTPS locator without credentials or fragments",
            boundary="provenance:ledger-formation",
        )
    return text


def _positive_length(value: Any, *, where: str, maximum: int) -> int:
    if type(value) is not int or not 0 < value <= maximum:
        raise _malformed(
            "FRI-IOR-PROVENANCE-032",
            f"{where} is outside its positive byte-length bound",
            boundary="provenance:ledger-formation",
        )
    return value


def _ordered_unique_text(
    value: Any,
    *,
    where: str,
    token_values: bool,
) -> tuple[str, ...]:
    raw = _array(value, where=where)
    if not raw:
        raise _malformed(
            "FRI-IOR-PROVENANCE-033",
            f"{where} must not be empty",
            boundary="provenance:ledger-formation",
        )
    values = tuple(
        _token(item, where=f"{where} item")
        if token_values
        else _text(item, where=f"{where} item")
        for item in raw
    )
    if len(set(values)) != len(values):
        raise _malformed(
            "FRI-IOR-PROVENANCE-034",
            f"{where} contains a duplicate item",
            boundary="provenance:ledger-formation",
        )
    if token_values and values != tuple(sorted(values)):
        raise _malformed(
            "FRI-IOR-PROVENANCE-035",
            f"{where} token items are not canonically ordered",
            boundary="provenance:ledger-formation",
        )
    return values


def _source_path(value: Any) -> str:
    path = _text(value, where="selected source path", maximum=512)
    if "\\" in path or "\x00" in path:
        raise _malformed(
            "FRI-IOR-PROVENANCE-036",
            "selected source paths must use canonical POSIX separators",
            boundary="provenance:ledger-formation",
        )
    pure = PurePosixPath(path)
    if (
        pure.is_absolute()
        or str(pure) != path
        or not pure.parts
        or any(
            part in {"", ".", ".."} or _PATH_PART.fullmatch(part) is None
            for part in pure.parts
        )
    ):
        raise _malformed(
            "FRI-IOR-PROVENANCE-037",
            "selected source paths must be canonical repository-relative paths",
            boundary="provenance:ledger-formation",
        )
    return path


def _reject_local_locators(value: JsonValue) -> None:
    forbidden = ("file://", "/tmp/", "/home/", "~/")

    def walk(current: JsonValue) -> None:
        if isinstance(current, str):
            if current.startswith(("/", "~")) or any(
                marker in current for marker in forbidden
            ):
                raise _malformed(
                    "FRI-IOR-PROVENANCE-038",
                    "the public ledger must not contain a local filesystem locator",
                    boundary="provenance:ledger-formation",
                )
        elif isinstance(current, list):
            for item in current:
                walk(item)
        elif isinstance(current, dict):
            for item in current.values():
                walk(item)

    walk(value)


@dataclass(frozen=True, slots=True)
class PaperArtifact:
    """Typed content binding for one selected primary paper artifact."""

    identifier: str
    artifact_content_id: ArtifactContentId
    byte_length: int


@dataclass(frozen=True, slots=True)
class ImplementationSource:
    """Typed content binding for one repository-relative source file."""

    path: str
    artifact_content_id: ArtifactContentId
    byte_length: int


@dataclass(frozen=True, slots=True)
class ImplementationSnapshot:
    """One exact Git revision and its bounded selected-source manifest."""

    identifier: str
    repository_url: str
    commit: str
    tree: str
    selected_files: tuple[ImplementationSource, ...]


@dataclass(frozen=True, slots=True)
class SourceLedger:
    """Validated exact bytes, normalized value, and typed selected entries."""

    artifact_id: ArtifactContentId
    canonical_id: CanonicalContentId
    exact_bytes: bytes = field(repr=False)
    canonical_bytes: bytes = field(repr=False)
    papers: tuple[PaperArtifact, ...]
    implementation_snapshots: tuple[ImplementationSnapshot, ...]
    _normalized_value: dict[str, Any] = field(repr=False, compare=False)

    @property
    def normalized_value(self) -> dict[str, Any]:
        """Return a defensive copy of the validated public JSON value."""

        return deepcopy(self._normalized_value)

    def binding_term(self) -> dict[str, Any]:
        """Return the complete public report binding for this ledger."""

        return {
            "scope": SOURCE_LEDGER_SCOPE,
            "artifact_content_id": str(self.artifact_id),
            "canonical_content_id": str(self.canonical_id),
            "value": self.normalized_value,
        }


def _validate_paper(value: Any, *, index: int) -> PaperArtifact:
    entry = _object(value, where=f"papers[{index}]", keys=_PAPER_KEYS)
    identifier = _identifier(entry["id"], where=f"papers[{index}].id")
    if entry["kind"] != "paper-pdf":
        raise _malformed(
            "FRI-IOR-PROVENANCE-039",
            "paper entries must have kind paper-pdf",
            boundary="provenance:ledger-formation",
        )
    _text(entry["title"], where=f"papers[{index}].title")
    _https_url(entry["landing_url"], where=f"papers[{index}].landing_url")
    _https_url(entry["artifact_url"], where=f"papers[{index}].artifact_url")
    revision = _object(
        entry["revision"],
        where=f"papers[{index}].revision",
        keys=_PAPER_REVISION_KEYS,
    )
    _text(revision["label"], where=f"papers[{index}].revision.label")
    date = _text(
        revision["archive_date"],
        where=f"papers[{index}].revision.archive_date",
        maximum=10,
    )
    if _DATE.fullmatch(date) is None:
        raise _malformed(
            "FRI-IOR-PROVENANCE-040",
            "paper archive dates must use YYYY-MM-DD",
            boundary="provenance:ledger-formation",
        )
    content = _object(
        entry["content"],
        where=f"papers[{index}].content",
        keys=_PAPER_CONTENT_KEYS,
    )
    content_id = ArtifactContentId.parse(content["artifact_content_id"])
    byte_length = _positive_length(
        content["byte_length"],
        where=f"papers[{index}].content.byte_length",
        maximum=MAX_PAPER_BYTES,
    )
    _ordered_unique_text(
        entry["usage"],
        where=f"papers[{index}].usage",
        token_values=True,
    )
    return PaperArtifact(identifier, content_id, byte_length)


def _validate_snapshot(value: Any, *, index: int) -> ImplementationSnapshot:
    entry = _object(
        value,
        where=f"implementation_snapshots[{index}]",
        keys=_SNAPSHOT_KEYS,
    )
    identifier = _identifier(
        entry["id"],
        where=f"implementation_snapshots[{index}].id",
    )
    if entry["kind"] != "git-source-profile":
        raise _malformed(
            "FRI-IOR-PROVENANCE-041",
            "implementation entries must have kind git-source-profile",
            boundary="provenance:ledger-formation",
        )
    repository_url = _https_url(
        entry["repository_url"],
        where=f"implementation_snapshots[{index}].repository_url",
    )
    revision = _object(
        entry["revision"],
        where=f"implementation_snapshots[{index}].revision",
        keys=_SNAPSHOT_REVISION_KEYS,
    )
    if revision["object_format"] != "sha1":
        raise _failure(
            OutcomeClass.UNSUPPORTED,
            "provenance:ledger-formation",
            "FRI-IOR-PROVENANCE-042",
            "the implementation snapshot uses an unsupported Git object format",
        )
    commit = _text(
        revision["commit"],
        where=f"implementation_snapshots[{index}].revision.commit",
        maximum=40,
    )
    tree = _text(
        revision["tree"],
        where=f"implementation_snapshots[{index}].revision.tree",
        maximum=40,
    )
    if _HEX_40.fullmatch(commit) is None or _HEX_40.fullmatch(tree) is None:
        raise _malformed(
            "FRI-IOR-PROVENANCE-043",
            "Git commit and tree IDs must be 40 lowercase hexadecimal digits",
            boundary="provenance:ledger-formation",
        )
    committer_date = _text(
        revision["committer_date"],
        where=f"implementation_snapshots[{index}].revision.committer_date",
        maximum=25,
    )
    if _COMMITTER_DATE.fullmatch(committer_date) is None:
        raise _malformed(
            "FRI-IOR-PROVENANCE-044",
            "Git committer dates must use the declared offset timestamp form",
            boundary="provenance:ledger-formation",
        )
    _text(
        revision["subject"],
        where=f"implementation_snapshots[{index}].revision.subject",
    )

    selected: list[ImplementationSource] = []
    for file_index, file_value in enumerate(
        _array(
            entry["selected_files"],
            where=f"implementation_snapshots[{index}].selected_files",
        )
    ):
        source = _object(
            file_value,
            where=f"implementation_snapshots[{index}].selected_files[{file_index}]",
            keys=_FILE_KEYS,
        )
        selected.append(
            ImplementationSource(
                path=_source_path(source["path"]),
                artifact_content_id=ArtifactContentId.parse(
                    source["artifact_content_id"]
                ),
                byte_length=_positive_length(
                    source["byte_length"],
                    where=(
                        "implementation_snapshots"
                        f"[{index}].selected_files[{file_index}].byte_length"
                    ),
                    maximum=MAX_IMPLEMENTATION_FILE_BYTES,
                ),
            )
        )
    paths = tuple(item.path for item in selected)
    if paths != tuple(sorted(paths)) or len(set(paths)) != len(paths):
        raise _malformed(
            "FRI-IOR-PROVENANCE-045",
            "selected implementation paths must be unique and sorted",
            boundary="provenance:ledger-formation",
        )
    if entry["profile_boundary"] != "comparison-input-not-conformance-target":
        raise _malformed(
            "FRI-IOR-PROVENANCE-046",
            "implementation snapshots must retain the comparison-only boundary",
            boundary="provenance:ledger-formation",
        )
    _ordered_unique_text(
        entry["interpretation_constraints"],
        where=f"implementation_snapshots[{index}].interpretation_constraints",
        token_values=False,
    )
    return ImplementationSnapshot(
        identifier,
        repository_url,
        commit,
        tree,
        tuple(selected),
    )


def _validate_ledger_value(value: JsonValue) -> tuple[
    dict[str, Any],
    tuple[PaperArtifact, ...],
    tuple[ImplementationSnapshot, ...],
]:
    _reject_local_locators(value)
    ledger = _object(value, where="source ledger", keys=_TOP_LEVEL_KEYS)
    schema = _text(ledger["schema"], where="source ledger schema")
    if schema != SOURCE_LEDGER_SCHEMA:
        raise _failure(
            OutcomeClass.UNSUPPORTED,
            "provenance:ledger-formation",
            "FRI-IOR-PROVENANCE-047",
            "the source-ledger schema is unsupported",
        )
    scope = _text(ledger["scope"], where="source ledger scope")
    if scope != SOURCE_LEDGER_SCOPE:
        raise _failure(
            OutcomeClass.UNSUPPORTED,
            "provenance:ledger-formation",
            "FRI-IOR-PROVENANCE-048",
            "the source-ledger scope is unsupported",
        )
    frozen_on = _text(
        ledger["frozen_on"],
        where="source ledger frozen_on",
        maximum=10,
    )
    if _DATE.fullmatch(frozen_on) is None:
        raise _malformed(
            "FRI-IOR-PROVENANCE-049",
            "source-ledger frozen_on must use YYYY-MM-DD",
            boundary="provenance:ledger-formation",
        )

    papers = tuple(
        _validate_paper(item, index=index)
        for index, item in enumerate(_array(ledger["papers"], where="papers"))
    )
    paper_ids = tuple(paper.identifier for paper in papers)
    if paper_ids != PAPER_IDS:
        raise _malformed(
            "FRI-IOR-PROVENANCE-050",
            "the constructive basis must contain exactly the five ordered paper IDs",
            boundary="provenance:ledger-formation",
        )

    snapshots = tuple(
        _validate_snapshot(item, index=index)
        for index, item in enumerate(
            _array(
                ledger["implementation_snapshots"],
                where="implementation_snapshots",
            )
        )
    )
    snapshot_ids = tuple(snapshot.identifier for snapshot in snapshots)
    expected_snapshot_ids = tuple(sorted(IMPLEMENTATION_SNAPSHOT_FILE_COUNTS))
    if snapshot_ids != expected_snapshot_ids:
        raise _malformed(
            "FRI-IOR-PROVENANCE-051",
            "implementation snapshots must have unique canonical ordered IDs",
            boundary="provenance:ledger-formation",
        )
    for snapshot in snapshots:
        expected_count = IMPLEMENTATION_SNAPSHOT_FILE_COUNTS[snapshot.identifier]
        if len(snapshot.selected_files) != expected_count:
            raise _malformed(
                "FRI-IOR-PROVENANCE-052",
                "an implementation selected-source manifest has the wrong size",
                boundary="provenance:ledger-formation",
            )

    claim = _object(
        ledger["claim_boundary"],
        where="claim_boundary",
        keys=_CLAIM_KEYS,
    )
    establishes = _ordered_unique_text(
        claim["establishes"],
        where="claim_boundary.establishes",
        token_values=False,
    )
    exclusions = _ordered_unique_text(
        claim["excluded_from_this_ledger"],
        where="claim_boundary.excluded_from_this_ledger",
        token_values=False,
    )
    nonclaims = _ordered_unique_text(
        claim["does_not_establish"],
        where="claim_boundary.does_not_establish",
        token_values=False,
    )
    if (
        establishes != _REQUIRED_ESTABLISHES
        or exclusions != _REQUIRED_EXCLUSIONS
        or nonclaims != _REQUIRED_NONCLAIMS
    ):
        raise _malformed(
            "FRI-IOR-PROVENANCE-053",
            "the constructive ledger must retain its exact claim and exclusion boundary",
            boundary="provenance:ledger-formation",
        )
    return ledger, papers, snapshots


def load_source_ledger_bytes(
    raw: bytes,
    *,
    expected_artifact_id: ArtifactContentId | None = None,
) -> SourceLedger:
    """Validate one exact source-ledger artifact without any network access."""

    if expected_artifact_id is not None and not isinstance(
        expected_artifact_id, ArtifactContentId
    ):
        raise _failure(
            OutcomeClass.KIND_MISMATCH,
            "provenance:artifact-binding",
            "FRI-IOR-PROVENANCE-054",
            "the expected ledger identity is not an ArtifactContentId",
        )
    exact_id = artifact_content_id(raw)
    if expected_artifact_id is not None and exact_id != expected_artifact_id:
        raise _failure(
            OutcomeClass.REFUSED,
            "provenance:artifact-binding",
            "FRI-IOR-PROVENANCE-055",
            "the exact source-ledger bytes differ from the frozen artifact ID",
        )
    parsed = load_bounded_json_bytes(raw)
    ledger, papers, snapshots = _validate_ledger_value(parsed)
    canonical = canonical_json_bytes(ledger)
    return SourceLedger(
        artifact_id=exact_id,
        canonical_id=CanonicalContentId(hashlib.sha256(canonical).hexdigest()),
        exact_bytes=raw,
        canonical_bytes=canonical,
        papers=papers,
        implementation_snapshots=snapshots,
        _normalized_value=deepcopy(ledger),
    )


def _read_regular_file(path: Path, *, maximum: int) -> bytes:
    try:
        metadata = path.lstat()
    except FileNotFoundError as error:
        raise _failure(
            OutcomeClass.MISSING_DEPENDENCY,
            "provenance:artifact-load",
            "FRI-IOR-PROVENANCE-056",
            "the source-ledger artifact is missing",
        ) from error
    except OSError as error:
        raise _failure(
            OutcomeClass.MISSING_DEPENDENCY,
            "provenance:artifact-load",
            "FRI-IOR-PROVENANCE-057",
            "the source-ledger artifact is unavailable",
        ) from error
    if not stat.S_ISREG(metadata.st_mode):
        raise _failure(
            OutcomeClass.REFUSED,
            "provenance:artifact-load",
            "FRI-IOR-PROVENANCE-058",
            "the source-ledger path is not a regular non-symlink file",
        )
    if metadata.st_size < 0 or metadata.st_size > maximum:
        raise _failure(
            OutcomeClass.DETERMINISTIC_LIMIT_EXCEEDED,
            "provenance:artifact-load",
            "FRI-IOR-PROVENANCE-059",
            "the source-ledger artifact exceeds its byte bound",
        )
    flags = os.O_RDONLY | getattr(os, "O_CLOEXEC", 0) | getattr(os, "O_NOFOLLOW", 0)
    try:
        descriptor = os.open(path, flags)
    except OSError as error:
        raise _failure(
            OutcomeClass.MISSING_DEPENDENCY,
            "provenance:artifact-load",
            "FRI-IOR-PROVENANCE-060",
            "the source-ledger artifact cannot be opened safely",
        ) from error
    try:
        before = os.fstat(descriptor)
        if not stat.S_ISREG(before.st_mode):
            raise _failure(
                OutcomeClass.REFUSED,
                "provenance:artifact-load",
                "FRI-IOR-PROVENANCE-061",
                "the opened source-ledger artifact is not a regular file",
            )
        if before.st_size < 0 or before.st_size > maximum:
            raise _failure(
                OutcomeClass.DETERMINISTIC_LIMIT_EXCEEDED,
                "provenance:artifact-load",
                "FRI-IOR-PROVENANCE-059",
                "the opened source-ledger artifact exceeds its byte bound",
            )
        chunks: list[bytes] = []
        remaining = before.st_size
        while remaining:
            chunk = os.read(descriptor, min(remaining, 1 << 14))
            if not chunk:
                raise _failure(
                    OutcomeClass.REFUSED,
                    "provenance:artifact-load",
                    "FRI-IOR-PROVENANCE-062",
                    "the source-ledger artifact changed while being read",
                )
            chunks.append(chunk)
            remaining -= len(chunk)
        if os.read(descriptor, 1):
            raise _failure(
                OutcomeClass.REFUSED,
                "provenance:artifact-load",
                "FRI-IOR-PROVENANCE-063",
                "the source-ledger artifact grew while being read",
            )
        after = os.fstat(descriptor)
    finally:
        os.close(descriptor)
    stable = ("st_dev", "st_ino", "st_mode", "st_size", "st_mtime_ns")
    if any(getattr(before, name) != getattr(after, name) for name in stable):
        raise _failure(
            OutcomeClass.REFUSED,
            "provenance:artifact-load",
            "FRI-IOR-PROVENANCE-064",
            "the source-ledger artifact changed while being read",
        )
    return b"".join(chunks)


def load_source_ledger(
    path: Path | str,
    *,
    expected_artifact_id: ArtifactContentId | None = None,
) -> SourceLedger:
    """Load one local ledger; remote retrieval is deliberately not supported."""

    if not isinstance(path, (Path, str)):
        raise _malformed(
            "FRI-IOR-PROVENANCE-065",
            "a source-ledger path must be Path or text",
            boundary="provenance:artifact-load",
        )
    raw = _read_regular_file(Path(path), maximum=MAX_LEDGER_BYTES)
    return load_source_ledger_bytes(raw, expected_artifact_id=expected_artifact_id)


def check_source_ledger(
    path: Path | str,
    *,
    expected_artifact_id: ArtifactContentId | None = None,
) -> CheckResult:
    """Return the stable package outcome partition for one ledger admission."""

    try:
        ledger = load_source_ledger(
            path,
            expected_artifact_id=expected_artifact_id,
        )
        return affirmative(
            "provenance:ledger-admission",
            "FRI-IOR-PROVENANCE-100",
            "the constructive source ledger is formed and exactly bound",
            artifact_content_id=str(ledger.artifact_id),
            canonical_content_id=str(ledger.canonical_id),
            paper_count=len(ledger.papers),
            implementation_snapshot_count=len(ledger.implementation_snapshots),
        )
    except ModelFailure as error:
        return error.to_result()
    except Exception:
        return checker_failure(
            "provenance:ledger-admission",
            "an unexpected source-ledger evaluator failure occurred",
        )


__all__ = [
    "ArtifactContentId",
    "CanonicalContentId",
    "IMPLEMENTATION_SNAPSHOT_FILE_COUNTS",
    "ImplementationSnapshot",
    "ImplementationSource",
    "MAX_CANONICAL_JSON_BYTES",
    "MAX_LEDGER_BYTES",
    "PAPER_IDS",
    "PaperArtifact",
    "SOURCE_LEDGER_SCHEMA",
    "SOURCE_LEDGER_SCOPE",
    "SourceLedger",
    "ValidationBasisId",
    "artifact_content_id",
    "canonical_content_id",
    "canonical_json_content_id",
    "canonical_json_bytes",
    "check_source_ledger",
    "load_bounded_json_bytes",
    "load_source_ledger",
    "load_source_ledger_bytes",
    "validation_basis_id",
]
