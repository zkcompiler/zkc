"""Foundation-backed compiler for published semantic profiles.

This is a bounded research and conformance instrument.  The durable source
formats are specified by ``docs-next/foundation/semantic-profile-publication.md``;
this module uses the selected Foundation reference model to compile exact
owner source into ``SemanticLanguageProfile`` bodies.
"""

from __future__ import annotations

from collections import defaultdict
from dataclasses import dataclass
import copy
import hashlib
import importlib.util
import json
from pathlib import Path, PurePosixPath
import sys
from typing import Any, Iterable, Mapping
import unicodedata
import re


ROOT = Path(__file__).resolve().parents[2]
PROFILE_INDEX = (
    ROOT / "docs-next" / "foundation" / "semantic-profile-manifests.json"
)
FOUNDATION_PAGE = ROOT / "docs-next" / "foundation" / "executable-foundations.md"
LEGACY_SOURCE_FORMAT = "zkc.pir.semantic-profile-source.v0"
OWNER_QUALIFIED_SOURCE_FORMAT = "zkc.semantic-profile-source.v1"
LEGACY_PROFILE_KEYS = (
    "interaction",
    "canonical-framed-fiat-shamir",
    "duplex-sponge-fiat-shamir",
    "public-setup",
    "commitment-opening",
    "oracle-commitment",
)
PROFILE_KEYS = LEGACY_PROFILE_KEYS
MANIFEST_FILES: dict[str, Path] = {}


_K1_NAME = "_zkc_k1_executable_foundations"
_K1_PATH = ROOT / "evaluation" / "k1-executable-foundations" / "reference_model.py"
if _K1_NAME in sys.modules:
    k1 = sys.modules[_K1_NAME]
else:
    _spec = importlib.util.spec_from_file_location(_K1_NAME, _K1_PATH)
    if _spec is None or _spec.loader is None:  # pragma: no cover - host failure
        raise ImportError(f"cannot load Foundation reference model from {_K1_PATH}")
    k1 = importlib.util.module_from_spec(_spec)
    sys.modules[_K1_NAME] = k1
    _spec.loader.exec_module(k1)


class PublicationError(ValueError):
    """A source artifact cannot form the selected publication."""


@dataclass(frozen=True)
class CompiledProfile:
    key: str
    manifest: Mapping[str, Any]
    profile: Any
    body_bytes: bytes
    profile_id: Any
    declaration_index: Mapping[tuple[str, str], int]
    direct_import_keys: tuple[str, ...]
    direct_import_uses: Mapping[str, tuple[bytes, ...]]
    source_fragments: Mapping[str, bytes]


@dataclass(frozen=True)
class Publication:
    profiles: Mapping[str, CompiledProfile]
    topological_order: tuple[str, ...]

    def exact_closure(self, root_key: str) -> tuple[str, ...]:
        if root_key not in self.profiles:
            raise PublicationError(f"unknown profile root {root_key!r}")
        seen: set[str] = set()

        def visit(key: str) -> None:
            if key in seen:
                return
            seen.add(key)
            for dependency in self.profiles[key].direct_import_keys:
                visit(dependency)

        visit(root_key)
        return tuple(
            sorted(
                seen,
                key=lambda key: self.profiles[key].profile_id.internal_reference(),
            )
        )


def _strict_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise PublicationError(f"duplicate JSON field {key!r}")
        result[key] = value
    return result


def _read_manifest(path: Path) -> dict[str, Any]:
    try:
        raw = path.read_bytes()
    except OSError as error:
        raise PublicationError(f"cannot read profile source {path}") from error
    if b"\r" in raw:
        raise PublicationError(f"profile source {path} contains CR octets")
    try:
        text = raw.decode("utf-8")
    except UnicodeDecodeError as error:
        raise PublicationError(f"profile source {path} is not UTF-8") from error
    try:
        value = json.loads(text, object_pairs_hook=_strict_object)
    except (json.JSONDecodeError, PublicationError) as error:
        raise PublicationError(f"profile source {path} is not strict JSON") from error
    if type(value) is not dict:
        raise PublicationError(f"profile source {path} must be a JSON object")
    return value


def _load_manifest_index() -> tuple[tuple[str, ...], dict[str, Path]]:
    index = _read_manifest(PROFILE_INDEX)
    _require_exact_fields(
        index,
        ("format", "manifests"),
        "semantic-profile manifest index",
    )
    if index["format"] != "zkc.semantic-profile-manifest-index.v0":
        raise PublicationError("unsupported semantic-profile manifest index")
    rows = _sequence(index["manifests"], "manifest index rows")
    if not rows:
        raise PublicationError("semantic-profile manifest index is empty")
    keys: list[str] = []
    files: dict[str, Path] = {}
    source_paths: set[str] = set()
    for ordinal, raw_row in enumerate(rows):
        row = _require_exact_fields(
            raw_row,
            ("key", "source"),
            f"manifest index row {ordinal}",
        )
        key = _ascii_symbol(row["key"], f"manifest index row {ordinal} key")
        source = _repository_relative_path(
            row["source"], f"manifest index row {ordinal} source"
        )
        path = (ROOT / source).resolve()
        try:
            path.relative_to(ROOT)
        except ValueError as error:
            raise PublicationError("manifest index source escapes repository") from error
        if key in files or source in source_paths:
            raise PublicationError("manifest index repeats a key or source path")
        keys.append(key)
        files[key] = path
        source_paths.add(source)
    return tuple(keys), files


def load_repository_manifests() -> dict[str, dict[str, Any]]:
    return {key: _read_manifest(MANIFEST_FILES[key]) for key in PROFILE_KEYS}


def _catalog_namespace(manifest: Mapping[str, Any]) -> str:
    if manifest["format"] == LEGACY_SOURCE_FORMAT:
        return "pir"
    return manifest["catalog_namespace"]


def _common_definition_kinds(namespace: str) -> frozenset[str]:
    return frozenset(
        f"{namespace}.{suffix}"
        for suffix in (
            "body-compiler",
            "evaluator-signature",
            "failure-schema",
            "semantic-law",
        )
    )


def _generated_catalog_kinds(namespace: str) -> frozenset[str]:
    return frozenset(
        f"{namespace}.{suffix}"
        for suffix in ("source-fragment", "subject-language")
    )


def _common_kind(manifest: Mapping[str, Any], suffix: str) -> str:
    return f"{_catalog_namespace(manifest)}.{suffix}"


def _require_exact_fields(value: object, fields: Iterable[str], label: str) -> dict[str, Any]:
    if type(value) is not dict:
        raise PublicationError(f"{label} must be an exact object")
    expected = frozenset(fields)
    actual = frozenset(value)
    if actual != expected:
        missing = sorted(expected - actual)
        extra = sorted(actual - expected)
        raise PublicationError(
            f"{label} has wrong fields; missing={missing}, extra={extra}"
        )
    return value


def _ascii_symbol(value: object, label: str) -> str:
    if type(value) is not str or not value:
        raise PublicationError(f"{label} must be nonempty text")
    try:
        raw = value.encode("ascii")
    except UnicodeEncodeError as error:
        raise PublicationError(f"{label} must be ASCII") from error
    if any(byte < 0x21 or byte > 0x7E for byte in raw):
        raise PublicationError(f"{label} must use printable non-space ASCII")
    return value


def _u64(value: object, label: str) -> int:
    if type(value) is not int or not 0 <= value < 1 << 64:
        raise PublicationError(f"{label} must be a u64 natural")
    return value


def _sequence(value: object, label: str) -> list[Any]:
    if type(value) is not list:
        raise PublicationError(f"{label} must be a JSON array")
    return value


def _sorted_unique_ascii(values: object, label: str, *, nonempty: bool) -> tuple[str, ...]:
    items = tuple(
        _ascii_symbol(item, f"{label} item") for item in _sequence(values, label)
    )
    if nonempty and not items:
        raise PublicationError(f"{label} must be nonempty")
    if items != tuple(sorted(set(items), key=lambda item: item.encode("ascii"))):
        raise PublicationError(f"{label} must be ASCII sorted-unique")
    return items


def _repository_relative_path(value: object, label: str) -> str:
    text = _ascii_symbol(value, label)
    path = PurePosixPath(text)
    if (
        path.is_absolute()
        or not path.parts
        or text != path.as_posix()
        or "\\" in text
        or any(part in ("", ".", "..") for part in path.parts)
    ):
        raise PublicationError(f"{label} must be a canonical repository-relative path")
    return text


PROFILE_KEYS, MANIFEST_FILES = _load_manifest_index()


def _validate_manifest_shape(key: str, raw: object) -> dict[str, Any]:
    if type(raw) is not dict:
        raise PublicationError(f"manifest {key} must be an exact object")
    source_format = raw.get("format")
    if source_format == LEGACY_SOURCE_FORMAT:
        fields = (
            "format",
            "key",
            "profile_family",
            "revision",
            "owner_page",
            "expected_imports",
            "supported_subject_kinds",
            "fragments",
            "definitions",
            "subjects",
        )
    elif source_format == OWNER_QUALIFIED_SOURCE_FORMAT:
        fields = (
            "format",
            "key",
            "catalog_namespace",
            "profile_family",
            "revision",
            "expected_imports",
            "supported_subject_kinds",
            "fragments",
            "definitions",
            "subjects",
        )
    else:
        raise PublicationError(f"manifest {key} has an unsupported format")
    manifest = _require_exact_fields(
        raw,
        fields,
        f"manifest {key}",
    )
    if source_format == OWNER_QUALIFIED_SOURCE_FORMAT:
        namespace = _ascii_symbol(
            manifest["catalog_namespace"],
            f"manifest {key} catalog namespace",
        )
        if re.fullmatch(r"[a-z][a-z0-9]*(?:\.[a-z][a-z0-9-]*)*", namespace) is None:
            raise PublicationError(
                f"manifest {key} has an invalid catalog namespace"
            )
    else:
        namespace = "pir"
    common_definition_kinds = _common_definition_kinds(namespace)
    generated_catalog_kinds = _generated_catalog_kinds(namespace)
    if _ascii_symbol(manifest["key"], f"manifest {key} key") != key:
        raise PublicationError(f"manifest key mismatch for {key}")
    _ascii_symbol(manifest["profile_family"], f"manifest {key} profile family")
    _u64(manifest["revision"], f"manifest {key} revision")
    if source_format == LEGACY_SOURCE_FORMAT:
        _repository_relative_path(
            manifest["owner_page"], f"manifest {key} owner page"
        )
    expected_imports = _sorted_unique_ascii(
        manifest["expected_imports"],
        f"manifest {key} expected imports",
        nonempty=False,
    )
    if key in expected_imports:
        raise PublicationError(f"manifest {key} cannot import itself")
    _sorted_unique_ascii(
        manifest["supported_subject_kinds"],
        f"manifest {key} supported kinds",
        nonempty=True,
    )
    fragments = _sequence(manifest["fragments"], f"manifest {key} fragments")
    if not fragments:
        raise PublicationError(f"manifest {key} must select source fragments")
    fragment_names: list[str] = []
    marker_names: set[str] = set()
    for ordinal, raw_fragment in enumerate(fragments):
        fragment_fields = (
            ("name", "start", "end")
            if source_format == LEGACY_SOURCE_FORMAT
            else ("name", "owner_page", "start", "end")
        )
        fragment = _require_exact_fields(
            raw_fragment,
            fragment_fields,
            f"manifest {key} fragment {ordinal}",
        )
        name = _ascii_symbol(fragment["name"], f"manifest {key} fragment name")
        if source_format == OWNER_QUALIFIED_SOURCE_FORMAT:
            _repository_relative_path(
                fragment["owner_page"],
                f"manifest {key} fragment owner page",
            )
        start = _ascii_symbol(fragment["start"], f"manifest {key} start marker")
        end = _ascii_symbol(fragment["end"], f"manifest {key} end marker")
        if start == end or start in marker_names or end in marker_names:
            raise PublicationError(f"manifest {key} repeats a source marker")
        marker_names.update((start, end))
        fragment_names.append(name)
    if len(fragment_names) != len(set(fragment_names)):
        raise PublicationError(f"manifest {key} repeats a fragment name")

    definitions = _sequence(
        manifest["definitions"], f"manifest {key} definitions"
    )
    if not definitions:
        raise PublicationError(f"manifest {key} must publish definitions")
    names_by_kind: dict[str, set[str]] = defaultdict(set)
    common_seen: set[str] = set()
    for ordinal, raw_definition in enumerate(definitions):
        definition = _require_exact_fields(
            raw_definition,
            ("kind", "name", "revision", "fragment", "selector", "dependencies"),
            f"manifest {key} definition {ordinal}",
        )
        kind = _ascii_symbol(definition["kind"], f"manifest {key} definition kind")
        if not kind.startswith(f"{namespace}.") or kind in generated_catalog_kinds:
            raise PublicationError(f"manifest {key} uses a reserved definition kind")
        name = _ascii_symbol(definition["name"], f"manifest {key} definition name")
        if name in names_by_kind[kind]:
            raise PublicationError(f"manifest {key} repeats {kind}/{name}")
        names_by_kind[kind].add(name)
        if kind in common_definition_kinds:
            common_seen.add(kind)
        _u64(definition["revision"], f"manifest {key} definition revision")
        if definition["fragment"] not in fragment_names:
            raise PublicationError(f"manifest {key} definition names no local fragment")
        if type(definition["selector"]) is not str or not definition["selector"]:
            raise PublicationError(f"manifest {key} definition selector is empty")
        if unicodedata.normalize("NFC", definition["selector"]) != definition["selector"]:
            raise PublicationError(f"manifest {key} definition selector is not NFC")
        for dependency_ordinal, dependency in enumerate(
            _sequence(
                definition["dependencies"],
                f"manifest {key} definition dependencies",
            )
        ):
            _validate_reference_shape(
                dependency,
                f"manifest {key} definition dependency {dependency_ordinal}",
            )
    if common_seen != common_definition_kinds:
        raise PublicationError(
            f"manifest {key} omits common definition kinds "
            f"{sorted(common_definition_kinds - common_seen)}"
        )

    subjects = _sequence(manifest["subjects"], f"manifest {key} subjects")
    subject_kinds: list[str] = []
    for ordinal, raw_subject in enumerate(subjects):
        subject = _require_exact_fields(
            raw_subject,
            ("kind", "body_compiler", "laws", "evaluator", "failure_schema"),
            f"manifest {key} subject {ordinal}",
        )
        subject_kinds.append(
            _ascii_symbol(subject["kind"], f"manifest {key} subject kind")
        )
        _validate_reference_shape(
            subject["body_compiler"], f"manifest {key} subject compiler"
        )
        _sorted_unique_ascii(
            subject["laws"], f"manifest {key} subject laws", nonempty=True
        )
        _ascii_symbol(subject["evaluator"], f"manifest {key} subject evaluator")
        _ascii_symbol(
            subject["failure_schema"], f"manifest {key} subject failure schema"
        )
    if tuple(subject_kinds) != tuple(manifest["supported_subject_kinds"]):
        raise PublicationError(
            f"manifest {key} subject rows do not equal its supported-kind set"
        )
    return manifest


def _validate_reference_shape(raw: object, label: str) -> dict[str, Any]:
    reference = _require_exact_fields(raw, ("profile", "kind", "name"), label)
    _ascii_symbol(reference["profile"], f"{label} profile")
    _ascii_symbol(reference["kind"], f"{label} kind")
    _ascii_symbol(reference["name"], f"{label} name")
    return reference


def _topological_order(manifests: Mapping[str, dict[str, Any]]) -> tuple[str, ...]:
    if frozenset(manifests) != frozenset(PROFILE_KEYS):
        raise PublicationError("publication source set is incomplete or contains extras")
    state: dict[str, int] = {}
    order: list[str] = []

    def visit(key: str) -> None:
        marker = state.get(key, 0)
        if marker == 1:
            raise PublicationError("profile import graph contains a cycle")
        if marker == 2:
            return
        state[key] = 1
        for dependency in manifests[key]["expected_imports"]:
            if dependency not in manifests:
                raise PublicationError(
                    f"manifest {key} names unknown expected import {dependency}"
                )
            visit(dependency)
        state[key] = 2
        order.append(key)

    for key in PROFILE_KEYS:
        visit(key)
    return tuple(order)


def _read_page(path_text: str, page_overrides: Mapping[str, bytes] | None) -> bytes:
    _repository_relative_path(path_text, "owner page")
    path = (ROOT / path_text).resolve()
    try:
        path.relative_to(ROOT)
    except ValueError as error:
        raise PublicationError("owner page escapes the repository") from error
    if page_overrides is not None and path_text in page_overrides:
        raw = page_overrides[path_text]
        if type(raw) is not bytes:
            raise PublicationError("owner-page override must be exact bytes")
        return raw
    try:
        return path.read_bytes()
    except OSError as error:
        raise PublicationError(f"cannot read owner page {path_text}") from error


def extract_marked_fragment(page: bytes, start_name: str, end_name: str) -> bytes:
    if type(page) is not bytes:
        raise PublicationError("owner page must be exact bytes")
    if b"\r" in page:
        raise PublicationError("owner page contains CR octets")
    start_line = f"<!-- {start_name} -->\n".encode("ascii")
    end_line = f"<!-- {end_name} -->\n".encode("ascii")
    if page.count(start_line) != 1 or page.count(end_line) != 1:
        raise PublicationError("source markers must each occur exactly once")
    start = page.index(start_line) + len(start_line)
    end = page.index(end_line)
    if start >= end:
        raise PublicationError("source markers are reversed or empty")
    region = page[start:end]
    if not region.startswith(b"\n") or not region.endswith(b"\n\n"):
        raise PublicationError("source markers lack exact structural blank lines")
    fragment = region[1:-1]
    if not fragment or not fragment.endswith(b"\n") or fragment.endswith(b"\n\n"):
        raise PublicationError("source fragment must end in exactly one LF")
    try:
        text = fragment.decode("utf-8")
    except UnicodeDecodeError as error:
        raise PublicationError("source fragment is not UTF-8") from error
    if unicodedata.normalize("NFC", text) != text:
        raise PublicationError("source fragment is not NFC")
    for line in text.splitlines():
        if line.endswith((" ", "\t")):
            raise PublicationError("source fragment has trailing horizontal whitespace")
    return fragment


def _extract_fragments(
    manifest: Mapping[str, Any],
    page_overrides: Mapping[str, bytes] | None,
) -> dict[str, bytes]:
    fragments: dict[str, bytes] = {}
    occupied_by_page: dict[str, list[tuple[int, int]]] = defaultdict(list)
    for source in manifest["fragments"]:
        page_name = (
            manifest["owner_page"]
            if manifest["format"] == LEGACY_SOURCE_FORMAT
            else source["owner_page"]
        )
        page = _read_page(page_name, page_overrides)
        start_line = f"<!-- {source['start']} -->\n".encode("ascii")
        end_line = f"<!-- {source['end']} -->\n".encode("ascii")
        if page.count(start_line) != 1 or page.count(end_line) != 1:
            raise PublicationError("source markers must each occur exactly once")
        start = page.index(start_line)
        end = page.index(end_line) + len(end_line)
        if start >= end:
            raise PublicationError("source marker interval is reversed")
        if any(
            not (end <= left or right <= start)
            for left, right in occupied_by_page[page_name]
        ):
            raise PublicationError("source marker intervals overlap")
        occupied_by_page[page_name].append((start, end))
        fragments[source["name"]] = extract_marked_fragment(
            page, source["start"], source["end"]
        )
    return fragments


def _catalog_record(kind: str, bodies: tuple[Any, ...]) -> Any:
    return k1.DatumRecord(
        ((0, k1.Symbol(kind)), (1, k1.DatumSeq(bodies)))
    )


def _sorted_ref_datums(datums: Iterable[Any]) -> tuple[Any, ...]:
    keyed = sorted((k1.encode_datum(item), item) for item in datums)
    if any(keyed[index - 1][0] == keyed[index][0] for index in range(1, len(keyed))):
        raise PublicationError("declaration reference sequence contains a duplicate")
    return tuple(item for _, item in keyed)


def _balanced_record_block(fragment: bytes, selector: bytes) -> bytes:
    start = fragment.find(selector)
    if start < 0:
        raise PublicationError("dependent-template selector is absent")
    opening = fragment.find(b"{", start + len(selector))
    if opening < 0:
        raise PublicationError("dependent-template declaration has no record body")
    depth = 0
    for offset in range(opening, len(fragment)):
        byte = fragment[offset]
        if byte == ord("{"):
            depth += 1
        elif byte == ord("}"):
            depth -= 1
            if depth == 0:
                return fragment[start : offset + 1]
    raise PublicationError("dependent-template record body is unclosed")


def _validate_dependent_receipt_template(
    profile_key: str,
    definition_kind: str,
    fragment: bytes,
    selector: bytes,
) -> None:
    if not (
        definition_kind.startswith("pir.fs-")
        and definition_kind.endswith("-receipt")
    ):
        return
    block = _balanced_record_block(fragment, selector)
    if definition_kind == "pir.fs-challenge-receipt":
        required = {
            "canonical-framed-fiat-shamir": (
                b"CanonicalValue<TranscriptStateType>",
                b"CanonicalValue<declared challenge type>",
            ),
            "duplex-sponge-fiat-shamir": (
                b"CanonicalValue<DuplexStateCarrier_T>",
                b"CanonicalValue<Core challenge type>",
            ),
        }.get(profile_key)
        if required is None or any(token not in block for token in required):
            raise PublicationError(
                "FS challenge receipt does not use the selected dependent parameters"
            )
    if any(token in block for token in (b"core_id", b"CoreId", b"ContentRefV0")):
        raise PublicationError(
            "FS receipt embeds a concrete Core coordinate"
        )


def _validate_global_fragment_disjointness(
    manifests: Mapping[str, Mapping[str, Any]],
    page_overrides: Mapping[str, bytes] | None,
) -> None:
    occupied_by_page: dict[str, list[tuple[int, int, str, str]]] = defaultdict(list)
    for key in PROFILE_KEYS:
        manifest = manifests[key]
        for source in manifest["fragments"]:
            page_name = (
                manifest["owner_page"]
                if manifest["format"] == LEGACY_SOURCE_FORMAT
                else source["owner_page"]
            )
            page = _read_page(page_name, page_overrides)
            start_line = f"<!-- {source['start']} -->\n".encode("ascii")
            end_line = f"<!-- {source['end']} -->\n".encode("ascii")
            if page.count(start_line) != 1 or page.count(end_line) != 1:
                raise PublicationError("source markers must each occur exactly once")
            start = page.index(start_line)
            end = page.index(end_line) + len(end_line)
            if start >= end:
                raise PublicationError("source marker interval is reversed")
            for left, right, other_key, other_name in occupied_by_page[page_name]:
                if not (end <= left or right <= start):
                    raise PublicationError(
                        "source marker interval overlaps across manifests: "
                        f"{other_key}/{other_name} and {key}/{source['name']}"
                    )
            occupied_by_page[page_name].append(
                (start, end, key, source["name"])
            )


def _compile_one(
    key: str,
    manifest: Mapping[str, Any],
    compiled: Mapping[str, CompiledProfile],
    page_overrides: Mapping[str, bytes] | None,
) -> CompiledProfile:
    fragments = _extract_fragments(manifest, page_overrides)
    definitions = manifest["definitions"]
    source_fragment_kind = _common_kind(manifest, "source-fragment")
    subject_language_kind = _common_kind(manifest, "subject-language")
    semantic_law_kind = _common_kind(manifest, "semantic-law")
    evaluator_kind = _common_kind(manifest, "evaluator-signature")
    failure_kind = _common_kind(manifest, "failure-schema")

    names_by_kind: dict[str, list[str]] = defaultdict(list)
    names_by_kind[source_fragment_kind] = [
        source["name"] for source in manifest["fragments"]
    ]
    for definition in definitions:
        names_by_kind[definition["kind"]].append(definition["name"])
    names_by_kind[subject_language_kind] = list(
        manifest["supported_subject_kinds"]
    )
    declaration_index = {
        (kind, name): ordinal
        for kind, names in names_by_kind.items()
        for ordinal, name in enumerate(names)
    }

    def resolve(raw: Mapping[str, str]) -> tuple[Any, str | None]:
        target_key = raw["profile"]
        coordinate = (raw["kind"], raw["name"])
        if target_key == "self":
            if coordinate not in declaration_index:
                raise PublicationError(
                    f"manifest {key} has unresolved local declaration {coordinate}"
                )
            return (
                k1.ProfileLocalDeclarationRef(
                    coordinate[0], declaration_index[coordinate]
                ),
                None,
            )
        if target_key == key:
            raise PublicationError(f"manifest {key} spells itself as an import")
        if target_key not in compiled:
            raise PublicationError(
                f"manifest {key} has unresolved imported profile {target_key}"
            )
        target = compiled[target_key]
        if coordinate not in target.declaration_index:
            raise PublicationError(
                f"manifest {key} has unresolved imported declaration "
                f"{target_key}/{coordinate}"
            )
        return (
            k1.ImportedProfileDeclarationRef(
                target.profile_id,
                coordinate[0],
                target.declaration_index[coordinate],
            ),
            target_key,
        )

    definition_by_coordinate = {
        (definition["kind"], definition["name"]): definition
        for definition in definitions
    }
    used_definitions: set[tuple[str, str]] = set()
    used_fragments: set[str] = set()

    def mark_local(coordinate: tuple[str, str]) -> None:
        if coordinate in used_definitions:
            return
        definition = definition_by_coordinate.get(coordinate)
        if definition is None:
            return
        used_definitions.add(coordinate)
        used_fragments.add(definition["fragment"])
        for raw_dependency in definition["dependencies"]:
            if raw_dependency["profile"] == "self":
                mark_local((raw_dependency["kind"], raw_dependency["name"]))

    for subject in manifest["subjects"]:
        body_compiler = subject["body_compiler"]
        if body_compiler["profile"] == "self":
            mark_local((body_compiler["kind"], body_compiler["name"]))
        for law in subject["laws"]:
            mark_local((semantic_law_kind, law))
        mark_local((evaluator_kind, subject["evaluator"]))
        mark_local((failure_kind, subject["failure_schema"]))
    if used_definitions != frozenset(definition_by_coordinate):
        unused = sorted(frozenset(definition_by_coordinate) - used_definitions)
        raise PublicationError(f"manifest {key} contains unreachable definitions {unused}")
    if used_fragments != frozenset(fragments):
        unused = sorted(frozenset(fragments) - used_fragments)
        raise PublicationError(f"manifest {key} contains unreachable fragments {unused}")

    catalog_bodies: dict[str, list[Any]] = defaultdict(list)
    for source in manifest["fragments"]:
        catalog_bodies[source_fragment_kind].append(
            k1.DatumRecord(
                (
                    (0, k1.Symbol(source["name"])),
                    (1, k1.Nat(0)),
                    (2, k1.BytesValue(fragments[source["name"]])),
                )
            )
        )

    uses_by_import: dict[str, list[Any]] = defaultdict(list)
    for definition in definitions:
        fragment_ref = k1.ProfileLocalDeclarationRef(
            source_fragment_kind,
            declaration_index[(source_fragment_kind, definition["fragment"])],
        )
        dependency_datums: list[Any] = []
        for raw_dependency in definition["dependencies"]:
            dependency, imported_key = resolve(raw_dependency)
            dependency_datum = k1.profile_declaration_ref_datum(dependency)
            dependency_datums.append(dependency_datum)
            if imported_key is not None:
                uses_by_import[imported_key].append(
                    k1.DatumVariant(0, dependency_datum)
                )
        body = k1.DatumRecord(
            (
                (0, k1.Symbol(definition["name"])),
                (1, k1.Nat(definition["revision"])),
                (2, k1.profile_declaration_ref_datum(fragment_ref)),
                (3, k1.BytesValue(definition["selector"].encode("utf-8"))),
                (4, k1.DatumSeq(_sorted_ref_datums(dependency_datums))),
            )
        )
        selector_bytes = definition["selector"].encode("utf-8")
        if selector_bytes not in fragments[definition["fragment"]]:
            raise PublicationError(
                f"manifest {key} selector {definition['selector']!r} is absent"
            )
        _validate_dependent_receipt_template(
            key,
            definition["kind"],
            fragments[definition["fragment"]],
            selector_bytes,
        )
        catalog_bodies[definition["kind"]].append(body)

    subject_rows: list[Any] = []
    for subject in manifest["subjects"]:
        body_compiler, imported_key = resolve(subject["body_compiler"])
        body_compiler_datum = k1.profile_declaration_ref_datum(body_compiler)
        if imported_key is not None:
            uses_by_import[imported_key].append(
                k1.DatumVariant(
                    1,
                    k1.DatumRecord(
                        (
                            (0, k1.Symbol(subject["kind"])),
                            (1, body_compiler_datum),
                        )
                    ),
                )
            )
        law_refs = tuple(
            k1.ProfileLocalDeclarationRef(
                semantic_law_kind,
                declaration_index[(semantic_law_kind, law)],
            )
            for law in subject["laws"]
        )
        evaluator_coordinate = (evaluator_kind, subject["evaluator"])
        failure_coordinate = (failure_kind, subject["failure_schema"])
        if evaluator_coordinate not in declaration_index:
            raise PublicationError(f"manifest {key} names an unknown evaluator")
        if failure_coordinate not in declaration_index:
            raise PublicationError(f"manifest {key} names an unknown failure schema")
        body = k1.DatumRecord(
            (
                (0, k1.Symbol(subject["kind"])),
                (1, body_compiler_datum),
                (
                    2,
                    k1.DatumSeq(
                        tuple(k1.profile_declaration_ref_datum(ref) for ref in law_refs)
                    ),
                ),
                (
                    3,
                    k1.profile_declaration_ref_datum(
                        k1.ProfileLocalDeclarationRef(
                            evaluator_coordinate[0],
                            declaration_index[evaluator_coordinate],
                        )
                    ),
                ),
                (
                    4,
                    k1.profile_declaration_ref_datum(
                        k1.ProfileLocalDeclarationRef(
                            failure_coordinate[0],
                            declaration_index[failure_coordinate],
                        )
                    ),
                ),
            )
        )
        catalog_bodies[subject_language_kind].append(body)
        subject_rows.append(
            k1.DatumRecord(
                (
                    (0, k1.Symbol(subject["kind"])),
                    (
                        1,
                        k1.profile_declaration_ref_datum(
                            k1.ProfileLocalDeclarationRef(
                                subject_language_kind,
                                declaration_index[
                                    (subject_language_kind, subject["kind"])
                                ],
                            )
                        ),
                    ),
                )
            )
        )

    derived_import_keys = tuple(
        sorted(uses_by_import, key=lambda item: item.encode("ascii"))
    )
    if derived_import_keys != tuple(manifest["expected_imports"]):
        raise PublicationError(
            f"manifest {key} expected imports {manifest['expected_imports']} "
            f"but derived {list(derived_import_keys)}"
        )
    import_profiles = tuple(
        sorted(
            (compiled[dependency].profile_id for dependency in derived_import_keys),
            key=lambda identifier: identifier.internal_reference(),
        )
    )
    import_use_rows: list[Any] = []
    direct_use_bytes: dict[str, tuple[bytes, ...]] = {}
    for imported_key in sorted(
        derived_import_keys,
        key=lambda item: compiled[item].profile_id.internal_reference(),
    ):
        sorted_uses = sorted(
            (k1.encode_datum(use), use) for use in uses_by_import[imported_key]
        )
        unique: list[Any] = []
        previous: bytes | None = None
        encoded_uses: list[bytes] = []
        for encoded, use in sorted_uses:
            if encoded == previous:
                continue
            previous = encoded
            unique.append(use)
            encoded_uses.append(encoded)
        if not unique:
            raise PublicationError(f"manifest {key} has an unused direct import")
        direct_use_bytes[imported_key] = tuple(encoded_uses)
        import_use_rows.append(
            k1.DatumRecord(
                (
                    (
                        0,
                        k1.BytesValue(
                            compiled[imported_key].profile_id.internal_reference()
                        ),
                    ),
                    (1, k1.DatumSeq(tuple(unique))),
                )
            )
        )

    evaluator_refs = tuple(
        k1.profile_declaration_ref_datum(
            k1.ProfileLocalDeclarationRef(evaluator_kind, ordinal)
        )
        for ordinal in range(len(names_by_kind[evaluator_kind]))
    )
    failure_refs = tuple(
        k1.profile_declaration_ref_datum(
            k1.ProfileLocalDeclarationRef(failure_kind, ordinal)
        )
        for ordinal in range(len(names_by_kind[failure_kind]))
    )
    law_source = k1.DatumRecord(
        (
            (
                0,
                k1.Nat(
                    0
                    if manifest["format"] == LEGACY_SOURCE_FORMAT
                    else 1
                ),
            ),
            (1, k1.DatumSeq(tuple(import_use_rows))),
            (2, k1.DatumSeq(tuple(subject_rows))),
            (3, k1.DatumSeq(evaluator_refs)),
            (4, k1.DatumSeq(failure_refs)),
            (5, k1.DatumSeq(())),
        )
    )
    declaration_catalogs = k1.DatumSeq(
        tuple(
            _catalog_record(kind, tuple(catalog_bodies[kind]))
            for kind in sorted(catalog_bodies, key=lambda item: item.encode("ascii"))
        )
    )
    profile = k1.SemanticLanguageProfile(
        k1.Symbol(manifest["profile_family"]),
        manifest["revision"],
        import_profiles,
        tuple(k1.Symbol(item) for item in manifest["supported_subject_kinds"]),
        declaration_catalogs,
        k1.encode_datum(law_source),
    )
    body_bytes = k1.encode_datum(profile.body())
    profile_id = profile.identity
    return CompiledProfile(
        key,
        copy.deepcopy(manifest),
        profile,
        body_bytes,
        profile_id,
        dict(declaration_index),
        derived_import_keys,
        direct_use_bytes,
        dict(fragments),
    )


def compile_repository(
    *,
    manifest_overrides: Mapping[str, dict[str, Any]] | None = None,
    page_overrides: Mapping[str, bytes] | None = None,
) -> Publication:
    manifests = load_repository_manifests()
    if manifest_overrides is not None:
        for key, value in manifest_overrides.items():
            if key not in manifests:
                raise PublicationError(f"unknown manifest override {key}")
            manifests[key] = copy.deepcopy(value)
    validated = {
        key: _validate_manifest_shape(key, manifests[key]) for key in PROFILE_KEYS
    }
    _validate_global_fragment_disjointness(validated, page_overrides)
    order = _topological_order(validated)
    compiled: dict[str, CompiledProfile] = {}
    for key in order:
        compiled[key] = _compile_one(
            key,
            validated[key],
            compiled,
            page_overrides,
        )
    return Publication(compiled, order)


def _foundation_law_source(page: bytes) -> bytes:
    region = extract_marked_fragment(
        page,
        "zkc-foundation-source:semantic-core-law:start",
        "zkc-foundation-source:semantic-core-law:end",
    )
    prefix = b"```text\n"
    suffix = b"```\n"
    if not region.startswith(prefix) or not region.endswith(suffix):
        raise PublicationError("Foundation law source must be one exact text fence")
    law = region[len(prefix) : -len(suffix)]
    if not law or not law.endswith(b"\n") or law.endswith(b"\n\n"):
        raise PublicationError("Foundation law source has wrong final framing")
    try:
        law.decode("ascii")
    except UnicodeDecodeError as error:
        raise PublicationError("Foundation law source is not ASCII") from error
    return law


def verify_foundation_source() -> dict[str, str | int]:
    page = FOUNDATION_PAGE.read_bytes()
    law = _foundation_law_source(page)
    if law != k1.SEMANTIC_CORE_LAW_SOURCE:
        raise PublicationError(
            "durable Foundation law source differs from the selected evaluator"
        )
    return {
        "identity_profile_digest": k1.IDENTITY_PROFILE_ID.digest.hex(),
        "hash_suite_digest": k1.HASH_SUITE_ID.digest.hex(),
        "semantic_regime_digest": k1.SEMANTIC_REGIME_ID.digest.hex(),
        "semantic_core_law_length": len(law),
        "semantic_core_law_sha256": hashlib.sha256(law).hexdigest(),
    }


def identity_table(publication: Publication) -> dict[str, Any]:
    foundation = verify_foundation_source()
    profiles: dict[str, Any] = {}
    for key in PROFILE_KEYS:
        artifact = publication.profiles[key]
        profiles[key] = {
            "profile_family": artifact.manifest["profile_family"],
            "revision": artifact.manifest["revision"],
            "direct_imports": list(artifact.direct_import_keys),
            "exact_closure": list(publication.exact_closure(key)),
            "body_length": len(artifact.body_bytes),
            "body_sha256": hashlib.sha256(artifact.body_bytes).hexdigest(),
            "profile_digest": artifact.profile_id.digest.hex(),
            "content_ref_hex": artifact.profile_id.internal_reference().hex(),
        }
    return {
        "format": "zkc.semantic-profile-identities.v1",
        "foundation": foundation,
        "profiles": profiles,
    }


def legacy_identity_table(publication: Publication) -> dict[str, Any]:
    foundation = verify_foundation_source()
    profiles: dict[str, Any] = {}
    for key in LEGACY_PROFILE_KEYS:
        artifact = publication.profiles[key]
        profiles[key] = {
            "profile_family": artifact.manifest["profile_family"],
            "revision": artifact.manifest["revision"],
            "direct_imports": list(artifact.direct_import_keys),
            "exact_closure": list(publication.exact_closure(key)),
            "body_length": len(artifact.body_bytes),
            "body_sha256": hashlib.sha256(artifact.body_bytes).hexdigest(),
            "profile_digest": artifact.profile_id.digest.hex(),
            "content_ref_hex": artifact.profile_id.internal_reference().hex(),
        }
    return {
        "format": "zkc.pir.semantic-profile-identities.v0",
        "foundation": foundation,
        "profiles": profiles,
    }
