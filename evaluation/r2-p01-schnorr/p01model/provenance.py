"""Strict provenance and replay primitives for the finite P01 witness.

This module intentionally does not import :mod:`p01model.terms` and never uses
``semantic_id``.  Semantic subject identity, evaluator/source validation
identity, and evidence-record identity are different lanes.  The latter two
are domain-separated here, while raw artifact identity is exactly the SHA-256
of the artifact bytes.

Only public replay material belongs in ``SourceManifest`` and
``PublicFixtureBinding``.  In particular, callers must not place an owner-local
private sidecar, its digest, or a secret-derived handle in a public validation
basis.  Confidential local authority requires a separate non-portable API.
"""

from __future__ import annotations

from dataclasses import dataclass, field
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat
from types import ModuleType
from typing import Any, Iterable, Mapping, TypeAlias


MAX_JSON_INPUT_BYTES = 1 << 20
MAX_CANONICAL_JSON_BYTES = 1 << 20
MAX_JSON_NODES = 8192
MAX_JSON_DEPTH = 32
MAX_SOURCE_BYTES = 4 << 20
MAX_SOURCE_ENTRIES = 32
MAX_COMPONENT_BYTES = 192
MAX_ROLE_BYTES = 96

SOURCE_MANIFEST_LAW = "p01.exact-current-public-source-manifest.v1"
PUBLIC_FIXTURE_LAW = "p01.exact-public-fixture-content.v1"

_HEX_DIGEST = re.compile(r"[0-9a-f]{64}\Z")
_TOKEN = re.compile(r"[A-Za-z0-9][A-Za-z0-9._:/-]*\Z")
_PATH_SEGMENT = re.compile(r"[A-Za-z0-9._-]+\Z")

_LOADED_REPO_ROOT = Path(__file__).resolve().parents[3]

JsonScalar: TypeAlias = None | bool | int | str
JsonValue: TypeAlias = JsonScalar | list["JsonValue"] | dict[str, "JsonValue"]


class ProvenanceError(ValueError):
    """Base class for deterministic provenance/replay input failures."""


class RootBindingError(ProvenanceError):
    """The requested root is not the checkout that loaded this evaluator."""


class PathPolicyError(ProvenanceError):
    """A repository-relative path violates the replay path policy."""


class ContentMismatchError(ProvenanceError):
    """Current artifact bytes differ from their frozen content binding."""


class JsonInputError(ProvenanceError):
    """A bounded public JSON artifact is malformed or non-canonical in type."""


def _check_digest(digest: str) -> str:
    if not isinstance(digest, str) or _HEX_DIGEST.fullmatch(digest) is None:
        raise ProvenanceError("SHA-256 digest must be 64 lowercase hexadecimal bytes")
    return digest


@dataclass(frozen=True, order=True)
class ArtifactContentId:
    """Identity of exact public artifact bytes: ``SHA256(bytes)``."""

    digest: str

    def __post_init__(self) -> None:
        _check_digest(self.digest)

    def __str__(self) -> str:
        return f"sha256:{self.digest}"

    @classmethod
    def parse(cls, value: str) -> "ArtifactContentId":
        prefix = "sha256:"
        if not isinstance(value, str) or not value.startswith(prefix):
            raise ProvenanceError("ArtifactContentId must use the sha256: prefix")
        return cls(value[len(prefix) :])


@dataclass(frozen=True, order=True)
class ValidationBasisId:
    """Domain-separated identity of one component's public validation basis."""

    digest: str

    def __post_init__(self) -> None:
        _check_digest(self.digest)

    def __str__(self) -> str:
        return f"validation-sha256:{self.digest}"

    @classmethod
    def parse(cls, value: str) -> "ValidationBasisId":
        prefix = "validation-sha256:"
        if not isinstance(value, str) or not value.startswith(prefix):
            raise ProvenanceError(
                "ValidationBasisId must use the validation-sha256: prefix"
            )
        return cls(value[len(prefix) :])


@dataclass(frozen=True, order=True)
class EvidenceRecordId:
    """Domain-separated identity of a public evidence-record preimage."""

    digest: str

    def __post_init__(self) -> None:
        _check_digest(self.digest)

    def __str__(self) -> str:
        return f"evidence-sha256:{self.digest}"

    @classmethod
    def parse(cls, value: str) -> "EvidenceRecordId":
        prefix = "evidence-sha256:"
        if not isinstance(value, str) or not value.startswith(prefix):
            raise ProvenanceError(
                "EvidenceRecordId must use the evidence-sha256: prefix"
            )
        return cls(value[len(prefix) :])


def _bounded_ascii_token(value: str, *, where: str, maximum: int) -> str:
    if not isinstance(value, str) or _TOKEN.fullmatch(value) is None:
        raise ProvenanceError(f"{where} must be a nonempty canonical ASCII token")
    if len(value.encode("ascii")) > maximum:
        raise ProvenanceError(f"{where} exceeds its byte bound")
    return value


def safe_relative_path(value: str) -> str:
    """Return one canonical POSIX repository path or raise ``PathPolicyError``."""

    if not isinstance(value, str) or not value or "\x00" in value or "\\" in value:
        raise PathPolicyError("source path must be nonempty canonical POSIX text")
    try:
        value.encode("ascii")
    except UnicodeEncodeError as error:
        raise PathPolicyError("source path must be ASCII") from error
    pure = PurePosixPath(value)
    if pure.is_absolute() or not pure.parts or str(pure) != value:
        raise PathPolicyError("source path must be canonical and repository-relative")
    if any(
        part in {"", ".", ".."} or _PATH_SEGMENT.fullmatch(part) is None
        for part in pure.parts
    ):
        raise PathPolicyError("source path contains a forbidden segment")
    return value


def bind_loaded_root(repo_root: Path | str) -> Path:
    """Bind replay to the checkout whose ``provenance.py`` is executing.

    Python imports are resolved before a runner interprets ``--repo-root``.
    Accepting another data root would therefore misidentify the loaded
    evaluator.  A copied checkout must execute its own copied runner.
    """

    try:
        root = Path(repo_root).resolve(strict=True)
    except (OSError, RuntimeError, TypeError) as error:
        raise RootBindingError("repository root is unavailable or malformed") from error
    if root != _LOADED_REPO_ROOT:
        raise RootBindingError(
            "repository root differs from the checkout that loaded the evaluator"
        )
    if not root.is_dir():
        raise RootBindingError("loaded repository root is not a directory")
    return root


def loaded_repo_root() -> Path:
    """Return the resolved root that loaded this provenance implementation."""

    return _LOADED_REPO_ROOT


def _resolved_regular_path(root: Path, relative_path: str) -> Path:
    relative = safe_relative_path(relative_path)
    candidate = root.joinpath(*PurePosixPath(relative).parts)
    try:
        resolved = candidate.resolve(strict=True)
        metadata = candidate.lstat()
    except OSError as error:
        raise PathPolicyError(f"source is unavailable: {relative}") from error
    if resolved != candidate:
        raise PathPolicyError(f"source path traverses a symbolic link: {relative}")
    if not resolved.is_relative_to(root):
        raise PathPolicyError(f"source escapes the loaded repository: {relative}")
    if not stat.S_ISREG(metadata.st_mode):
        raise PathPolicyError(f"source is not a regular file: {relative}")
    return candidate


def _read_current_bytes(
    root: Path,
    relative_path: str,
    *,
    maximum: int,
) -> bytes:
    candidate = _resolved_regular_path(root, relative_path)
    flags = os.O_RDONLY | getattr(os, "O_CLOEXEC", 0) | getattr(os, "O_NOFOLLOW", 0)
    try:
        descriptor = os.open(candidate, flags)
    except OSError as error:
        raise PathPolicyError(f"source cannot be opened safely: {relative_path}") from error
    try:
        before = os.fstat(descriptor)
        if not stat.S_ISREG(before.st_mode):
            raise PathPolicyError(f"source is not a regular file: {relative_path}")
        if before.st_size < 0 or before.st_size > maximum:
            raise ProvenanceError(f"source exceeds its byte bound: {relative_path}")
        chunks: list[bytes] = []
        remaining = before.st_size
        while remaining:
            chunk = os.read(descriptor, min(remaining, 1 << 16))
            if not chunk:
                raise ContentMismatchError(
                    f"source changed while it was read: {relative_path}"
                )
            chunks.append(chunk)
            remaining -= len(chunk)
        if os.read(descriptor, 1):
            raise ContentMismatchError(
                f"source grew while it was read: {relative_path}"
            )
        after = os.fstat(descriptor)
    finally:
        os.close(descriptor)
    stable_fields = ("st_dev", "st_ino", "st_mode", "st_size", "st_mtime_ns")
    if any(getattr(before, name) != getattr(after, name) for name in stable_fields):
        raise ContentMismatchError(f"source changed while it was read: {relative_path}")
    raw = b"".join(chunks)
    if len(raw) != before.st_size:
        raise ContentMismatchError(f"source length changed while read: {relative_path}")
    return raw


def artifact_content_id(raw: bytes) -> ArtifactContentId:
    """Return the exact-byte SHA-256 content identity of a public artifact."""

    if not isinstance(raw, bytes):
        raise ProvenanceError("artifact content hashing requires bytes")
    return ArtifactContentId(hashlib.sha256(raw).hexdigest())


def _normalize_json_term(value: Any) -> JsonValue:
    nodes = 0

    def normalize(current: Any, depth: int) -> JsonValue:
        nonlocal nodes
        nodes += 1
        if nodes > MAX_JSON_NODES:
            raise JsonInputError("JSON term exceeds its node bound")
        if depth > MAX_JSON_DEPTH:
            raise JsonInputError("JSON term exceeds its depth bound")
        if current is None or isinstance(current, (bool, str)):
            return current
        if isinstance(current, int) and not isinstance(current, bool):
            return current
        if isinstance(current, (list, tuple)):
            return [normalize(item, depth + 1) for item in current]
        if isinstance(current, Mapping):
            if not all(type(key) is str for key in current):
                raise JsonInputError("canonical JSON maps require text keys")
            return {
                key: normalize(current[key], depth + 1)
                for key in sorted(current)
            }
        raise JsonInputError(
            f"unsupported canonical JSON value type: {type(current).__name__}"
        )

    return normalize(value, 0)


def canonical_json_bytes(
    value: Any,
    *,
    maximum: int = MAX_CANONICAL_JSON_BYTES,
) -> bytes:
    """Encode the closed JSON subset deterministically for hashing/comparison."""

    if not isinstance(maximum, int) or isinstance(maximum, bool) or maximum <= 0:
        raise ProvenanceError("canonical JSON byte bound must be positive")
    normalized = _normalize_json_term(value)
    encoded = json.dumps(
        normalized,
        ensure_ascii=True,
        allow_nan=False,
        sort_keys=True,
        separators=(",", ":"),
    ).encode("ascii")
    if len(encoded) > maximum:
        raise JsonInputError("canonical JSON encoding exceeds its byte bound")
    return encoded


def canonical_json_text(value: Any, *, pretty: bool = False) -> str:
    """Render stable JSON, with one trailing newline, for report artifacts."""

    normalized = _normalize_json_term(value)
    rendered = json.dumps(
        normalized,
        ensure_ascii=True,
        allow_nan=False,
        sort_keys=True,
        indent=2 if pretty else None,
        separators=None if pretty else (",", ":"),
    )
    if len(rendered.encode("ascii")) > MAX_CANONICAL_JSON_BYTES:
        raise JsonInputError("rendered JSON document exceeds its byte bound")
    return rendered + "\n"


def canonical_json_content_id(value: Any) -> ArtifactContentId:
    """Identify the compact canonical JSON bytes of a public value."""

    return artifact_content_id(canonical_json_bytes(value))


def _domain_digest(domain: bytes, label: str, preimage: Any) -> str:
    checked = _bounded_ascii_token(
        label,
        where="identity component",
        maximum=MAX_COMPONENT_BYTES,
    ).encode("ascii")
    body = canonical_json_bytes(preimage)
    framed = (
        domain
        + len(checked).to_bytes(4, "big")
        + checked
        + len(body).to_bytes(8, "big")
        + body
    )
    return hashlib.sha256(framed).hexdigest()


def validation_basis_id(component: str, preimage: Any) -> ValidationBasisId:
    """Identify one component's public validation basis, never a semantic subject."""

    return ValidationBasisId(
        _domain_digest(b"zkc-p01-validation-basis\x00", component, preimage)
    )


def evidence_record_id(record_kind: str, preimage: Any) -> EvidenceRecordId:
    """Identify one bounded public evidence record, never a semantic subject."""

    return EvidenceRecordId(
        _domain_digest(b"zkc-p01-evidence-record\x00", record_kind, preimage)
    )


@dataclass(frozen=True, order=True)
class SourceEntry:
    """Canonical binding for one current public evaluator/report source file."""

    role: str
    path: str
    sha256: ArtifactContentId
    byte_length: int

    def __post_init__(self) -> None:
        _bounded_ascii_token(self.role, where="source role", maximum=MAX_ROLE_BYTES)
        safe_relative_path(self.path)
        if not isinstance(self.sha256, ArtifactContentId):
            raise ProvenanceError("source SHA-256 must be an ArtifactContentId")
        if (
            not isinstance(self.byte_length, int)
            or isinstance(self.byte_length, bool)
            or self.byte_length < 0
            or self.byte_length > MAX_SOURCE_BYTES
        ):
            raise ProvenanceError("source byte length is outside the source bound")

    @classmethod
    def from_current_file(
        cls,
        repo_root: Path | str,
        *,
        role: str,
        path: str,
    ) -> "SourceEntry":
        root = bind_loaded_root(repo_root)
        raw = _read_current_bytes(root, path, maximum=MAX_SOURCE_BYTES)
        return cls(role, safe_relative_path(path), artifact_content_id(raw), len(raw))

    def term(self) -> dict[str, Any]:
        return {
            "role": self.role,
            "path": self.path,
            "sha256": str(self.sha256),
            "byte_length": self.byte_length,
        }


@dataclass(frozen=True)
class SourceDeclaration:
    """A manifest source and, optionally, the module expected at that path."""

    role: str
    path: str
    module: ModuleType | None = field(default=None, compare=False, repr=False)

    def __post_init__(self) -> None:
        _bounded_ascii_token(self.role, where="source role", maximum=MAX_ROLE_BYTES)
        safe_relative_path(self.path)
        if self.module is not None and not isinstance(self.module, ModuleType):
            raise ProvenanceError("loaded source module has the wrong type")


def validate_loaded_module(
    repo_root: Path | str,
    *,
    path: str,
    module: ModuleType,
) -> None:
    """Require ``module.__file__`` to be the declared current source file."""

    root = bind_loaded_root(repo_root)
    expected = _resolved_regular_path(root, path)
    if not isinstance(module, ModuleType):
        raise ProvenanceError("loaded source module has the wrong type")
    loaded_name = getattr(module, "__file__", None)
    if not isinstance(loaded_name, str):
        raise ContentMismatchError(f"loaded module has no source path: {path}")
    try:
        loaded = Path(loaded_name).resolve(strict=True)
    except (OSError, RuntimeError) as error:
        raise ContentMismatchError(f"loaded module path is unavailable: {path}") from error
    if loaded != expected:
        raise ContentMismatchError(
            f"loaded module differs from its declared source path: {path}"
        )
    specification = getattr(module, "__spec__", None)
    origin = getattr(specification, "origin", None) if specification is not None else None
    if origin not in (None, "built-in", "frozen"):
        try:
            resolved_origin = Path(origin).resolve(strict=True)
        except (OSError, RuntimeError) as error:
            raise ContentMismatchError(
                f"loaded module origin is unavailable: {path}"
            ) from error
        if resolved_origin != expected:
            raise ContentMismatchError(
                f"loaded module origin differs from its declared source path: {path}"
            )


@dataclass(frozen=True)
class SourceManifest:
    """Canonical, component-specific public validation source manifest."""

    component: str
    entries: tuple[SourceEntry, ...]
    law: str = SOURCE_MANIFEST_LAW

    def __post_init__(self) -> None:
        _bounded_ascii_token(
            self.component,
            where="source-manifest component",
            maximum=MAX_COMPONENT_BYTES,
        )
        if self.law != SOURCE_MANIFEST_LAW:
            raise ProvenanceError("source-manifest law is unsupported")
        if not isinstance(self.entries, tuple) or not (
            1 <= len(self.entries) <= MAX_SOURCE_ENTRIES
        ):
            raise ProvenanceError("source-manifest entry count is outside its bound")
        if any(not isinstance(entry, SourceEntry) for entry in self.entries):
            raise ProvenanceError("source manifest contains a non-SourceEntry value")
        if self.entries != tuple(sorted(self.entries, key=lambda item: (item.role, item.path))):
            raise ProvenanceError("source-manifest entries are not canonically ordered")
        roles = tuple(entry.role for entry in self.entries)
        paths = tuple(entry.path for entry in self.entries)
        if len(set(roles)) != len(roles):
            raise ProvenanceError("source manifest contains a duplicate role")
        if len(set(paths)) != len(paths):
            raise ProvenanceError("source manifest contains a duplicate path")

    def identity_preimage(self) -> dict[str, Any]:
        return {
            "law": self.law,
            "component": self.component,
            "sources": [entry.term() for entry in self.entries],
        }

    @property
    def identity(self) -> ValidationBasisId:
        return validation_basis_id(self.component, self.identity_preimage())

    def term(self) -> dict[str, Any]:
        return {
            "id": str(self.identity),
            **self.identity_preimage(),
        }


def build_source_manifest(
    repo_root: Path | str,
    *,
    component: str,
    declarations: Iterable[SourceDeclaration],
) -> SourceManifest:
    """Build a component manifest from exact bytes and loaded-module checks."""

    root = bind_loaded_root(repo_root)
    declared = tuple(declarations)
    if not declared:
        raise ProvenanceError("source manifest requires at least one declaration")
    entries: list[SourceEntry] = []
    for declaration in declared:
        if not isinstance(declaration, SourceDeclaration):
            raise ProvenanceError("source declaration has the wrong type")
        if declaration.module is not None:
            validate_loaded_module(
                root,
                path=declaration.path,
                module=declaration.module,
            )
        entries.append(
            SourceEntry.from_current_file(
                root,
                role=declaration.role,
                path=declaration.path,
            )
        )
    return SourceManifest(
        component=component,
        entries=tuple(sorted(entries, key=lambda item: (item.role, item.path))),
    )


def validate_source_manifest(
    manifest: SourceManifest,
    repo_root: Path | str,
    *,
    loaded_modules: Mapping[str, ModuleType] | None = None,
) -> None:
    """Validate source set shape, loaded paths, and every current source byte."""

    if not isinstance(manifest, SourceManifest):
        raise ProvenanceError("source manifest has the wrong type")
    root = bind_loaded_root(repo_root)
    paths = {entry.path for entry in manifest.entries}
    modules = dict(loaded_modules or {})
    if not set(modules).issubset(paths):
        raise ProvenanceError("loaded-module map names a source outside the manifest")
    for path, module in modules.items():
        validate_loaded_module(root, path=path, module=module)
    for expected in manifest.entries:
        actual = SourceEntry.from_current_file(
            root,
            role=expected.role,
            path=expected.path,
        )
        if actual != expected:
            raise ContentMismatchError(
                f"current source bytes differ from the manifest: {expected.path}"
            )


def _unique_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise JsonInputError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def _reject_float(value: str) -> Any:
    raise JsonInputError(f"JSON floating-point values are unsupported: {value}")


def _reject_constant(value: str) -> Any:
    raise JsonInputError(f"non-finite JSON constant is unsupported: {value}")


def load_bounded_json_bytes(
    raw: bytes,
    *,
    maximum: int = MAX_JSON_INPUT_BYTES,
) -> JsonValue:
    """Parse one bounded UTF-8 JSON value with duplicate keys and floats refused."""

    if not isinstance(raw, bytes):
        raise JsonInputError("JSON input must be bytes")
    if not isinstance(maximum, int) or isinstance(maximum, bool) or maximum <= 0:
        raise JsonInputError("JSON input byte bound must be positive")
    if len(raw) > maximum:
        raise JsonInputError("JSON input exceeds its byte bound")
    try:
        text = raw.decode("utf-8", errors="strict")
    except UnicodeDecodeError as error:
        raise JsonInputError("JSON input is not valid UTF-8") from error
    try:
        value = json.loads(
            text,
            object_pairs_hook=_unique_object,
            parse_float=_reject_float,
            parse_constant=_reject_constant,
        )
    except JsonInputError:
        raise
    except (json.JSONDecodeError, RecursionError, ValueError) as error:
        raise JsonInputError(f"JSON input is malformed: {error}") from error
    normalized = _normalize_json_term(value)
    canonical_json_bytes(normalized)
    return normalized


@dataclass(frozen=True)
class PublicFixtureBinding:
    """Exact-byte and normalized-value binding for one disclosed JSON fixture."""

    source: SourceEntry
    canonical_json_id: ArtifactContentId
    value: JsonValue = field(compare=False, repr=False)
    law: str = PUBLIC_FIXTURE_LAW

    def __post_init__(self) -> None:
        if not isinstance(self.source, SourceEntry):
            raise ProvenanceError("public fixture source has the wrong type")
        if not isinstance(self.canonical_json_id, ArtifactContentId):
            raise ProvenanceError("public fixture canonical ID has the wrong type")
        if self.law != PUBLIC_FIXTURE_LAW:
            raise ProvenanceError("public fixture binding law is unsupported")
        normalized = _normalize_json_term(self.value)
        if normalized != self.value:
            raise JsonInputError("public fixture value is not normalized JSON")
        if canonical_json_content_id(normalized) != self.canonical_json_id:
            raise ContentMismatchError("public fixture canonical JSON identity differs")

    @property
    def artifact_id(self) -> ArtifactContentId:
        return self.source.sha256

    def term(self) -> dict[str, Any]:
        return {
            "law": self.law,
            "source": self.source.term(),
            "artifact_content_id": str(self.artifact_id),
            "canonical_json_content_id": str(self.canonical_json_id),
            "disclosure": "PublicReplayInput",
            "confidentiality_claim": False,
        }


def load_public_fixture(
    repo_root: Path | str,
    *,
    path: str,
    role: str = "public-fixture",
    expected_artifact_id: ArtifactContentId | None = None,
) -> PublicFixtureBinding:
    """Read, bind, and parse one public fixture from the loaded checkout.

    ``expected_artifact_id`` is optional while initially freezing a fixture and
    should be supplied by replay consumers after the artifact has been frozen.
    This API is deliberately public-only and must not be used for a confidential
    owner-local witness sidecar.
    """

    root = bind_loaded_root(repo_root)
    relative = safe_relative_path(path)
    raw = _read_current_bytes(root, relative, maximum=MAX_JSON_INPUT_BYTES)
    content_id = artifact_content_id(raw)
    if expected_artifact_id is not None:
        if not isinstance(expected_artifact_id, ArtifactContentId):
            raise ProvenanceError("expected fixture ID has the wrong type")
        if content_id != expected_artifact_id:
            raise ContentMismatchError("public fixture bytes differ from the frozen ID")
    value = load_bounded_json_bytes(raw)
    source = SourceEntry(role, relative, content_id, len(raw))
    return PublicFixtureBinding(source, canonical_json_content_id(value), value)


__all__ = [
    "ArtifactContentId",
    "ContentMismatchError",
    "EvidenceRecordId",
    "JsonInputError",
    "JsonValue",
    "MAX_CANONICAL_JSON_BYTES",
    "MAX_JSON_INPUT_BYTES",
    "MAX_SOURCE_BYTES",
    "MAX_SOURCE_ENTRIES",
    "PUBLIC_FIXTURE_LAW",
    "PathPolicyError",
    "ProvenanceError",
    "PublicFixtureBinding",
    "RootBindingError",
    "SOURCE_MANIFEST_LAW",
    "SourceDeclaration",
    "SourceEntry",
    "SourceManifest",
    "ValidationBasisId",
    "artifact_content_id",
    "bind_loaded_root",
    "build_source_manifest",
    "canonical_json_bytes",
    "canonical_json_content_id",
    "canonical_json_text",
    "evidence_record_id",
    "load_bounded_json_bytes",
    "load_public_fixture",
    "loaded_repo_root",
    "safe_relative_path",
    "validate_loaded_module",
    "validate_source_manifest",
    "validation_basis_id",
]
