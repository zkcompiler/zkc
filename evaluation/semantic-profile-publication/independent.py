"""Cold reconstruction of published PIR semantic-profile identities.

This module intentionally imports neither the Foundation reference model nor
the publication reference compiler.  It independently implements the selected
datum encoding, prior-meta and ordinary identity framing, strict source
extraction, declaration-reference encoding, graph compilation, and closure
derivation.
"""

from __future__ import annotations

from collections import defaultdict
from dataclasses import dataclass
import copy
import hashlib
import json
from pathlib import Path
from typing import Any, Iterable, Mapping
import unicodedata


ROOT = Path(__file__).resolve().parents[2]
PROFILE_DIR = ROOT / "docs-next" / "pir" / "profiles"
FOUNDATION_DOCUMENT = (
    ROOT / "docs-next" / "foundation" / "executable-foundations.md"
)
KEYS = (
    "interaction",
    "canonical-framed-fiat-shamir",
    "duplex-sponge-fiat-shamir",
    "public-setup",
    "commitment-opening",
    "oracle-commitment",
)
FORMAT = "zkc.pir.semantic-profile-source.v0"
COMMON_KINDS = {
    "pir.body-compiler",
    "pir.evaluator-signature",
    "pir.failure-schema",
    "pir.semantic-law",
}
RESERVED_KINDS = {"pir.source-fragment", "pir.subject-language"}

FOUNDATION = "zkc.foundation.meta.v0"
IDENTITY_KIND = "foundation.identity-profile"
HASH_KIND = "foundation.hash-suite"
REGIME_KIND = "foundation.semantic-regime"
PROFILE_KIND = "foundation.semantic-language-profile"
META_PREFIX = b"zkc/prior-meta-id/v0\x00"
CONTENT_PREFIX = b"zkc/content-id/v0\x00"
MAX_BYTES = 1 << 20
MAX_NODES = 1 << 14
MAX_EDGES = 1 << 14
MAX_DEPTH = 384


class ColdError(ValueError):
    """Cold publication reconstruction refused its input."""


# Datum constructors deliberately use a different representation from K1.
def n(value: int) -> tuple[str, int]:
    return ("n", value)


def y(value: bytes) -> tuple[str, bytes]:
    return ("y", value)


def q(value: str) -> tuple[str, str]:
    return ("q", value)


def s(*values: object) -> tuple[str, tuple[object, ...]]:
    return ("s", tuple(values))


def r(*fields: tuple[int, object]) -> tuple[str, tuple[tuple[int, object], ...]]:
    return ("r", tuple(fields))


def v(case: int, payload: object) -> tuple[str, int, object]:
    return ("v", case, payload)


def _u64(value: int) -> bytes:
    if type(value) is not int or not 0 <= value < 1 << 64:
        raise ColdError("value is not a u64 natural")
    return value.to_bytes(8, "big")


def _frame(value: bytes) -> bytes:
    if type(value) is not bytes:
        raise ColdError("frame payload is not exact bytes")
    return _u64(len(value)) + value


def _axis(value: str) -> bytes:
    if type(value) is not str or not value:
        raise ColdError("axis is not nonempty text")
    try:
        raw = value.encode("ascii")
    except UnicodeEncodeError as error:
        raise ColdError("axis is not ASCII") from error
    if len(raw) > MAX_BYTES or any(byte < 0x21 or byte > 0x7E for byte in raw):
        raise ColdError("axis is outside printable ASCII")
    return raw


def _magnitude(value: int) -> bytes:
    if type(value) is not int or value < 0:
        raise ColdError("natural magnitude is invalid")
    if value == 0:
        return b"\x00"
    return value.to_bytes((value.bit_length() + 7) // 8, "big")


def encode(value: object) -> bytes:
    nodes = 0
    edges = 0
    active: set[int] = set()

    def visit(current: object, depth: int) -> bytes:
        nonlocal nodes, edges
        nodes += 1
        if nodes > MAX_NODES or depth > MAX_DEPTH:
            raise ColdError("datum exceeds its structural bound")
        if type(current) is not tuple or not current:
            raise ColdError("unknown cold datum")
        marker = id(current)
        if marker in active:
            raise ColdError("cyclic cold datum")
        active.add(marker)
        try:
            tag = current[0]
            if tag == "n" and len(current) == 2:
                result = b"\x03" + _frame(_magnitude(current[1]))
            elif tag == "y" and len(current) == 2 and type(current[1]) is bytes:
                result = b"\x05" + _frame(current[1])
            elif tag == "q" and len(current) == 2:
                result = b"\x06" + _frame(_axis(current[1]))
            elif tag == "s" and len(current) == 2 and type(current[1]) is tuple:
                edges += len(current[1])
                children = tuple(visit(child, depth + 1) for child in current[1])
                result = b"\x07" + _u64(len(children)) + b"".join(
                    _frame(child) for child in children
                )
            elif tag == "r" and len(current) == 2 and type(current[1]) is tuple:
                fields = current[1]
                edges += len(fields)
                ordinals = tuple(field[0] for field in fields)
                if (
                    any(type(field) is not tuple or len(field) != 2 for field in fields)
                    or any(type(ordinal) is not int for ordinal in ordinals)
                    or ordinals != tuple(sorted(set(ordinals)))
                ):
                    raise ColdError("record fields are not strictly ordered")
                result = b"\x08" + _u64(len(fields)) + b"".join(
                    _u64(ordinal) + _frame(visit(child, depth + 1))
                    for ordinal, child in fields
                )
            elif tag == "v" and len(current) == 3:
                edges += 1
                result = (
                    b"\x09"
                    + _u64(current[1])
                    + _frame(visit(current[2], depth + 1))
                )
            else:
                raise ColdError("unknown cold datum tag")
        finally:
            active.remove(marker)
        if edges > MAX_EDGES or len(result) > MAX_BYTES:
            raise ColdError("datum exceeds its canonical bound")
        return result

    return visit(value, 0)


@dataclass(frozen=True)
class PriorId:
    kind: str
    digest: bytes

    def ref(self) -> bytes:
        if type(self.digest) is not bytes or len(self.digest) != 32:
            raise ColdError("prior ID digest has wrong shape")
        return _frame(_axis(FOUNDATION)) + _frame(_axis(self.kind)) + self.digest


@dataclass(frozen=True)
class ContentId:
    kind: str
    regime: PriorId
    digest: bytes

    def ref(self) -> bytes:
        if type(self.digest) is not bytes or len(self.digest) != 32:
            raise ColdError("content ID digest has wrong shape")
        return (
            _frame(_axis(FOUNDATION))
            + _frame(IDENTITY_PROFILE_ID.ref())
            + _frame(HASH_SUITE_ID.ref())
            + _frame(_axis(self.kind))
            + _frame(self.regime.ref())
            + self.digest
        )


def _prior_id(kind: str, descriptor: object) -> PriorId:
    body = encode(descriptor)
    preimage = META_PREFIX + _frame(_axis(FOUNDATION)) + _frame(_axis(kind)) + _frame(body)
    return PriorId(kind, hashlib.sha256(preimage).digest())


IDENTITY_DESCRIPTOR = r(
    (0, q("zkc.identity.framed.v0")),
    (1, y(CONTENT_PREFIX)),
    (2, q("u64-be-octet-length")),
    (
        3,
        s(
            q("foundation-profile"),
            q("identity-profile-id"),
            q("hash-suite-id"),
            q("subject-kind"),
            q("semantic-regime-id"),
            q("canonical-body"),
        ),
    ),
    (4, q("digest-excluded")),
)
HASH_DESCRIPTOR = r(
    (0, q("sha2-256")),
    (1, n(1)),
    (2, q("fips-180-4-octets")),
    (3, n(32)),
)
IDENTITY_PROFILE_ID = _prior_id(IDENTITY_KIND, IDENTITY_DESCRIPTOR)
HASH_SUITE_ID = _prior_id(HASH_KIND, HASH_DESCRIPTOR)


CORE_NAMES = (
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


def _extract_foundation_law(raw: bytes) -> bytes:
    try:
        text = raw.decode("utf-8")
    except UnicodeDecodeError as error:
        raise ColdError("Foundation page is not UTF-8") from error
    if "\r" in text:
        raise ColdError("Foundation page contains CR")
    start = "<!-- zkc-foundation-source:semantic-core-law:start -->\n\n"
    end = "\n<!-- zkc-foundation-source:semantic-core-law:end -->\n"
    if text.count(start) != 1 or text.count(end) != 1:
        raise ColdError("Foundation source markers are not unique")
    enclosed = text.split(start, 1)[1].split(end, 1)[0]
    if not enclosed.startswith("```text\n") or not enclosed.endswith("```\n"):
        raise ColdError("Foundation source is not one exact text fence")
    law = enclosed[len("```text\n") : -len("```\n")].encode("ascii")
    if not law.endswith(b"\n") or law.endswith(b"\n\n"):
        raise ColdError("Foundation law has wrong final LF")
    return law


def foundation_basis(page_override: bytes | None = None) -> tuple[PriorId, bytes]:
    raw = FOUNDATION_DOCUMENT.read_bytes() if page_override is None else page_override
    law = _extract_foundation_law(raw)
    descriptor = r(
        (0, q("zkc.foundation.portable-semantics.v0")),
        (1, n(0)),
        (2, r((0, s(*(q(name) for name in CORE_NAMES))), (1, y(law)))),
        (3, s()),
        (4, q("local-ordinals-and-closed-scc-v0")),
        (5, q("language-profiles-and-extension-modules-same-root-dag-v0")),
    )
    return _prior_id(REGIME_KIND, descriptor), law


SEMANTIC_REGIME_ID, SEMANTIC_CORE_LAW = foundation_basis()


def _content_id(kind: str, body: bytes) -> ContentId:
    preimage = (
        CONTENT_PREFIX
        + _frame(_axis(FOUNDATION))
        + _frame(IDENTITY_PROFILE_ID.ref())
        + _frame(HASH_SUITE_ID.ref())
        + _frame(_axis(kind))
        + _frame(SEMANTIC_REGIME_ID.ref())
        + _frame(body)
    )
    return ContentId(kind, SEMANTIC_REGIME_ID, hashlib.sha256(preimage).digest())


@dataclass(frozen=True)
class ColdProfile:
    key: str
    manifest: Mapping[str, Any]
    body_bytes: bytes
    identifier: ContentId
    declaration_index: Mapping[tuple[str, str], int]
    direct_import_keys: tuple[str, ...]
    direct_import_uses: Mapping[str, tuple[bytes, ...]]
    source_fragments: Mapping[str, bytes]


@dataclass(frozen=True)
class ColdPublication:
    profiles: Mapping[str, ColdProfile]
    topological_order: tuple[str, ...]

    def exact_closure(self, root: str) -> tuple[str, ...]:
        if root not in self.profiles:
            raise ColdError("unknown closure root")
        pending = [root]
        reached: set[str] = set()
        while pending:
            current = pending.pop()
            if current in reached:
                continue
            reached.add(current)
            pending.extend(self.profiles[current].direct_import_keys)
        return tuple(sorted(reached, key=lambda key: self.profiles[key].identifier.ref()))


def _pairs(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise ColdError("JSON object repeats a field")
        result[key] = value
    return result


def _read_json(path: Path) -> dict[str, Any]:
    raw = path.read_bytes()
    if b"\r" in raw:
        raise ColdError("manifest contains CR")
    try:
        result = json.loads(raw.decode("utf-8"), object_pairs_hook=_pairs)
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise ColdError("manifest is not strict UTF-8 JSON") from error
    if type(result) is not dict:
        raise ColdError("manifest root is not an object")
    return result


def load_manifests() -> dict[str, dict[str, Any]]:
    return {key: _read_json(PROFILE_DIR / f"{key}.json") for key in KEYS}


def _fields(value: object, expected: set[str], label: str) -> dict[str, Any]:
    if type(value) is not dict or set(value) != expected:
        raise ColdError(f"{label} has a nonexact shape")
    return value


def _symbol(value: object, label: str) -> str:
    if type(value) is not str:
        raise ColdError(f"{label} is not text")
    _axis(value)
    return value


def _array(value: object, label: str) -> list[Any]:
    if type(value) is not list:
        raise ColdError(f"{label} is not an array")
    return value


def _sorted_symbols(value: object, label: str, require_nonempty: bool) -> tuple[str, ...]:
    items = tuple(_symbol(item, label) for item in _array(value, label))
    if require_nonempty and not items:
        raise ColdError(f"{label} is empty")
    if items != tuple(sorted(set(items), key=lambda item: item.encode("ascii"))):
        raise ColdError(f"{label} is not sorted-unique")
    return items


def _ref_shape(raw: object) -> dict[str, Any]:
    value = _fields(raw, {"profile", "kind", "name"}, "reference")
    for field in ("profile", "kind", "name"):
        _symbol(value[field], f"reference {field}")
    return value


def _validate(key: str, raw: object) -> dict[str, Any]:
    manifest = _fields(
        raw,
        {
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
        },
        f"manifest {key}",
    )
    if manifest["format"] != FORMAT or manifest["key"] != key:
        raise ColdError("manifest format or key is wrong")
    _symbol(manifest["profile_family"], "profile family")
    if type(manifest["revision"]) is not int or not 0 <= manifest["revision"] < 1 << 64:
        raise ColdError("profile revision is not a u64")
    if type(manifest["owner_page"]) is not str or not manifest["owner_page"]:
        raise ColdError("owner page is absent")
    imports = _sorted_symbols(manifest["expected_imports"], "expected imports", False)
    if key in imports:
        raise ColdError("profile imports itself")
    supported = _sorted_symbols(
        manifest["supported_subject_kinds"], "supported kinds", True
    )

    fragment_names: list[str] = []
    marker_names: set[str] = set()
    for source in _array(manifest["fragments"], "fragments"):
        fragment = _fields(source, {"name", "start", "end"}, "fragment")
        name = _symbol(fragment["name"], "fragment name")
        start = _symbol(fragment["start"], "fragment start")
        end = _symbol(fragment["end"], "fragment end")
        if start == end or start in marker_names or end in marker_names:
            raise ColdError("fragment markers are repeated")
        marker_names.update((start, end))
        fragment_names.append(name)
    if not fragment_names or len(fragment_names) != len(set(fragment_names)):
        raise ColdError("fragment names are empty or repeated")

    names: dict[str, set[str]] = defaultdict(set)
    common: set[str] = set()
    definitions = _array(manifest["definitions"], "definitions")
    for source in definitions:
        definition = _fields(
            source,
            {"kind", "name", "revision", "fragment", "selector", "dependencies"},
            "definition",
        )
        kind = _symbol(definition["kind"], "definition kind")
        name = _symbol(definition["name"], "definition name")
        if not kind.startswith("pir.") or kind in RESERVED_KINDS or name in names[kind]:
            raise ColdError("definition kind or name is invalid")
        names[kind].add(name)
        common.add(kind) if kind in COMMON_KINDS else None
        if type(definition["revision"]) is not int or not 0 <= definition["revision"] < 1 << 64:
            raise ColdError("definition revision is invalid")
        if definition["fragment"] not in fragment_names:
            raise ColdError("definition fragment is unresolved")
        selector = definition["selector"]
        if (
            type(selector) is not str
            or not selector
            or unicodedata.normalize("NFC", selector) != selector
        ):
            raise ColdError("definition selector is invalid")
        for dependency in _array(definition["dependencies"], "dependencies"):
            _ref_shape(dependency)
    if common != COMMON_KINDS:
        raise ColdError("manifest omits a common definition catalog")

    subject_kinds: list[str] = []
    for source in _array(manifest["subjects"], "subjects"):
        subject = _fields(
            source,
            {"kind", "body_compiler", "laws", "evaluator", "failure_schema"},
            "subject",
        )
        subject_kinds.append(_symbol(subject["kind"], "subject kind"))
        _ref_shape(subject["body_compiler"])
        _sorted_symbols(subject["laws"], "subject laws", True)
        _symbol(subject["evaluator"], "subject evaluator")
        _symbol(subject["failure_schema"], "subject failure")
    if tuple(subject_kinds) != supported:
        raise ColdError("subject rows differ from supported kinds")
    return manifest


def _order(manifests: Mapping[str, dict[str, Any]]) -> tuple[str, ...]:
    if set(manifests) != set(KEYS):
        raise ColdError("manifest set is not exact")
    visiting: set[str] = set()
    done: set[str] = set()
    result: list[str] = []

    def walk(key: str) -> None:
        if key in done:
            return
        if key in visiting:
            raise ColdError("profile import cycle")
        visiting.add(key)
        for imported in manifests[key]["expected_imports"]:
            if imported not in manifests:
                raise ColdError("unknown profile import")
            walk(imported)
        visiting.remove(key)
        done.add(key)
        result.append(key)

    for key in KEYS:
        walk(key)
    return tuple(result)


def _page_bytes(path_text: str, overrides: Mapping[str, bytes] | None) -> bytes:
    if overrides is not None and path_text in overrides:
        raw = overrides[path_text]
    else:
        path = (ROOT / path_text).resolve()
        try:
            path.relative_to(ROOT)
        except ValueError as error:
            raise ColdError("owner page escapes repository") from error
        raw = path.read_bytes()
    if type(raw) is not bytes:
        raise ColdError("owner page has wrong carrier")
    return raw


def _fragments(manifest: Mapping[str, Any], overrides: Mapping[str, bytes] | None) -> dict[str, bytes]:
    raw = _page_bytes(manifest["owner_page"], overrides)
    try:
        text = raw.decode("utf-8")
    except UnicodeDecodeError as error:
        raise ColdError("owner page is not UTF-8") from error
    if "\r" in text:
        raise ColdError("owner page contains CR")
    intervals: list[tuple[int, int]] = []
    result: dict[str, bytes] = {}
    for source in manifest["fragments"]:
        raw_opening = f"<!-- {source['start']} -->\n"
        raw_closing = f"<!-- {source['end']} -->\n"
        opening = f"<!-- {source['start']} -->\n\n"
        closing = f"\n<!-- {source['end']} -->\n"
        if (
            text.count(raw_opening) != 1
            or text.count(raw_closing) != 1
            or text.count(opening) != 1
            or text.count(closing) != 1
        ):
            raise ColdError("source marker framing is not unique")
        left = text.index(opening)
        body_start = left + len(opening)
        body_end = text.index(closing)
        right = body_end + len(closing)
        if body_start >= body_end or any(
            not (right <= old_left or old_right <= left)
            for old_left, old_right in intervals
        ):
            raise ColdError("source fragments overlap or are empty")
        intervals.append((left, right))
        fragment_text = text[body_start:body_end]
        if (
            not fragment_text
            or not fragment_text.endswith("\n")
            or fragment_text.endswith("\n\n")
            or unicodedata.normalize("NFC", fragment_text) != fragment_text
            or any(line.endswith((" ", "\t")) for line in fragment_text.splitlines())
        ):
            raise ColdError("source fragment is not canonical")
        result[source["name"]] = fragment_text.encode("utf-8")
    return result


def _local_ref(kind: str, ordinal: int) -> object:
    return v(0, r((0, q(kind)), (1, n(ordinal))))


def _import_ref(identifier: ContentId, kind: str, ordinal: int) -> object:
    return v(
        1,
        r((0, y(identifier.ref())), (1, q(kind)), (2, n(ordinal))),
    )


def _sorted_datums(values: Iterable[object]) -> tuple[object, ...]:
    keyed = sorted((encode(value), value) for value in values)
    if any(keyed[index - 1][0] == keyed[index][0] for index in range(1, len(keyed))):
        raise ColdError("datum sequence contains a duplicate")
    return tuple(value for _, value in keyed)


def _receipt_block(fragment: bytes, selector: bytes) -> bytes:
    start = fragment.find(selector)
    opening = fragment.find(b"{", start + len(selector)) if start >= 0 else -1
    if start < 0 or opening < 0:
        raise ColdError("dependent receipt declaration is absent")
    level = 1
    cursor = opening + 1
    while cursor < len(fragment) and level:
        if fragment[cursor : cursor + 1] == b"{":
            level += 1
        elif fragment[cursor : cursor + 1] == b"}":
            level -= 1
        cursor += 1
    if level:
        raise ColdError("dependent receipt declaration is unclosed")
    return fragment[start:cursor]


def _check_receipt_parameterization(
    key: str, kind: str, fragment: bytes, selector: bytes
) -> None:
    if not (kind.startswith("pir.fs-") and kind.endswith("-receipt")):
        return
    block = _receipt_block(fragment, selector)
    if kind == "pir.fs-challenge-receipt":
        expected_by_family = {
            "canonical-framed-fiat-shamir": {
                b"CanonicalValue<TranscriptStateType>",
                b"CanonicalValue<declared challenge type>",
            },
            "duplex-sponge-fiat-shamir": {
                b"CanonicalValue<DuplexStateCarrier_T>",
                b"CanonicalValue<Core challenge type>",
            },
        }
        expected = expected_by_family.get(key)
        if expected is None or any(token not in block for token in expected):
            raise ColdError("FS receipt is not parameterized by the selected family types")
    for forbidden in (b"core_id", b"CoreId", b"ContentRefV0"):
        if forbidden in block:
            raise ColdError("FS receipt embeds a concrete Core coordinate")


def _check_global_fragment_disjointness(
    manifests: Mapping[str, Mapping[str, Any]],
    overrides: Mapping[str, bytes] | None,
) -> None:
    occupied_by_page: dict[str, list[tuple[int, int, str, str]]] = defaultdict(list)
    for key in KEYS:
        manifest = manifests[key]
        page_name = manifest["owner_page"]
        page = _page_bytes(page_name, overrides)
        for source in manifest["fragments"]:
            opening = f"<!-- {source['start']} -->\n".encode("ascii")
            closing = f"<!-- {source['end']} -->\n".encode("ascii")
            if page.count(opening) != 1 or page.count(closing) != 1:
                raise ColdError("source marker framing is not unique")
            left = page.index(opening)
            right = page.index(closing) + len(closing)
            if left >= right:
                raise ColdError("source marker interval is reversed")
            for old_left, old_right, other_key, other_name in occupied_by_page[page_name]:
                if not (right <= old_left or old_right <= left):
                    raise ColdError(
                        "source fragments overlap across manifests: "
                        f"{other_key}/{other_name} and {key}/{source['name']}"
                    )
            occupied_by_page[page_name].append(
                (left, right, key, source["name"])
            )


def _compile(
    key: str,
    manifest: Mapping[str, Any],
    completed: Mapping[str, ColdProfile],
    overrides: Mapping[str, bytes] | None,
) -> ColdProfile:
    fragments = _fragments(manifest, overrides)
    by_kind: dict[str, list[str]] = defaultdict(list)
    by_kind["pir.source-fragment"] = [item["name"] for item in manifest["fragments"]]
    for definition in manifest["definitions"]:
        by_kind[definition["kind"]].append(definition["name"])
    by_kind["pir.subject-language"] = list(manifest["supported_subject_kinds"])
    index = {
        (kind, name): ordinal
        for kind, names in by_kind.items()
        for ordinal, name in enumerate(names)
    }

    def resolve(raw: Mapping[str, str]) -> tuple[object, str | None]:
        coordinate = (raw["kind"], raw["name"])
        owner = raw["profile"]
        if owner == "self":
            if coordinate not in index:
                raise ColdError("local declaration is unresolved")
            return _local_ref(coordinate[0], index[coordinate]), None
        if owner == key:
            raise ColdError("self reference uses imported spelling")
        target = completed.get(owner)
        if target is None or coordinate not in target.declaration_index:
            raise ColdError("imported declaration is unresolved")
        return (
            _import_ref(
                target.identifier,
                coordinate[0],
                target.declaration_index[coordinate],
            ),
            owner,
        )

    definitions = {
        (item["kind"], item["name"]): item for item in manifest["definitions"]
    }
    reached: set[tuple[str, str]] = set()
    reached_fragments: set[str] = set()

    def reach(coordinate: tuple[str, str]) -> None:
        if coordinate in reached:
            return
        definition = definitions.get(coordinate)
        if definition is None:
            return
        reached.add(coordinate)
        reached_fragments.add(definition["fragment"])
        for dependency in definition["dependencies"]:
            if dependency["profile"] == "self":
                reach((dependency["kind"], dependency["name"]))

    for subject in manifest["subjects"]:
        compiler = subject["body_compiler"]
        if compiler["profile"] == "self":
            reach((compiler["kind"], compiler["name"]))
        for law in subject["laws"]:
            reach(("pir.semantic-law", law))
        reach(("pir.evaluator-signature", subject["evaluator"]))
        reach(("pir.failure-schema", subject["failure_schema"]))
    if reached != set(definitions) or reached_fragments != set(fragments):
        raise ColdError("publication source contains unreachable material")

    catalogs: dict[str, list[object]] = defaultdict(list)
    for source in manifest["fragments"]:
        catalogs["pir.source-fragment"].append(
            r((0, q(source["name"])), (1, n(0)), (2, y(fragments[source["name"]])))
        )

    uses: dict[str, list[object]] = defaultdict(list)
    for definition in manifest["definitions"]:
        dependencies: list[object] = []
        for dependency_source in definition["dependencies"]:
            dependency, imported = resolve(dependency_source)
            dependencies.append(dependency)
            if imported is not None:
                uses[imported].append(v(0, dependency))
        selector = definition["selector"].encode("utf-8")
        if selector not in fragments[definition["fragment"]]:
            raise ColdError("definition selector is absent from its fragment")
        _check_receipt_parameterization(
            key,
            definition["kind"],
            fragments[definition["fragment"]],
            selector,
        )
        catalogs[definition["kind"]].append(
            r(
                (0, q(definition["name"])),
                (1, n(definition["revision"])),
                (
                    2,
                    _local_ref(
                        "pir.source-fragment",
                        index[("pir.source-fragment", definition["fragment"])],
                    ),
                ),
                (3, y(selector)),
                (4, s(*_sorted_datums(dependencies))),
            )
        )

    law_subject_rows: list[object] = []
    for subject in manifest["subjects"]:
        compiler, imported = resolve(subject["body_compiler"])
        if imported is not None:
            uses[imported].append(
                v(1, r((0, q(subject["kind"])), (1, compiler)))
            )
        laws = tuple(
            _local_ref("pir.semantic-law", index[("pir.semantic-law", law)])
            for law in subject["laws"]
        )
        evaluator_key = ("pir.evaluator-signature", subject["evaluator"])
        failure_key = ("pir.failure-schema", subject["failure_schema"])
        if evaluator_key not in index or failure_key not in index:
            raise ColdError("subject evaluator or failure schema is unresolved")
        catalogs["pir.subject-language"].append(
            r(
                (0, q(subject["kind"])),
                (1, compiler),
                (2, s(*laws)),
                (3, _local_ref(evaluator_key[0], index[evaluator_key])),
                (4, _local_ref(failure_key[0], index[failure_key])),
            )
        )
        law_subject_rows.append(
            r(
                (0, q(subject["kind"])),
                (
                    1,
                    _local_ref(
                        "pir.subject-language",
                        index[("pir.subject-language", subject["kind"])],
                    ),
                ),
            )
        )

    derived = tuple(sorted(uses, key=lambda item: item.encode("ascii")))
    if derived != tuple(manifest["expected_imports"]):
        raise ColdError("expected and derived direct imports differ")
    import_ids = tuple(
        sorted(
            (completed[item].identifier for item in derived),
            key=lambda identifier: identifier.ref(),
        )
    )
    direct_use_bytes: dict[str, tuple[bytes, ...]] = {}
    import_rows: list[object] = []
    for imported in sorted(derived, key=lambda item: completed[item].identifier.ref()):
        keyed = sorted((encode(use), use) for use in uses[imported])
        unique: list[object] = []
        encoded_unique: list[bytes] = []
        for encoded_value, use in keyed:
            if encoded_unique and encoded_unique[-1] == encoded_value:
                continue
            encoded_unique.append(encoded_value)
            unique.append(use)
        if not unique:
            raise ColdError("direct import has no use")
        direct_use_bytes[imported] = tuple(encoded_unique)
        import_rows.append(
            r((0, y(completed[imported].identifier.ref())), (1, s(*unique)))
        )

    evaluator_refs = tuple(
        _local_ref("pir.evaluator-signature", ordinal)
        for ordinal in range(len(by_kind["pir.evaluator-signature"]))
    )
    failure_refs = tuple(
        _local_ref("pir.failure-schema", ordinal)
        for ordinal in range(len(by_kind["pir.failure-schema"]))
    )
    law_source = encode(
        r(
            (0, n(0)),
            (1, s(*import_rows)),
            (2, s(*law_subject_rows)),
            (3, s(*evaluator_refs)),
            (4, s(*failure_refs)),
            (5, s()),
        )
    )
    catalog_values = tuple(
        r((0, q(kind)), (1, s(*catalogs[kind])))
        for kind in sorted(catalogs, key=lambda item: item.encode("ascii"))
    )
    profile_body = r(
        (0, q(manifest["profile_family"])),
        (1, n(manifest["revision"])),
        (2, s(*(y(identifier.ref()) for identifier in import_ids))),
        (3, s(*(q(kind) for kind in manifest["supported_subject_kinds"]))),
        (4, s(*catalog_values)),
        (5, y(law_source)),
    )
    body_bytes = encode(profile_body)
    identifier = _content_id(PROFILE_KIND, body_bytes)
    return ColdProfile(
        key,
        copy.deepcopy(manifest),
        body_bytes,
        identifier,
        dict(index),
        derived,
        direct_use_bytes,
        dict(fragments),
    )


def compile_repository(
    *,
    manifest_overrides: Mapping[str, dict[str, Any]] | None = None,
    page_overrides: Mapping[str, bytes] | None = None,
) -> ColdPublication:
    manifests = load_manifests()
    if manifest_overrides is not None:
        for key, value in manifest_overrides.items():
            if key not in manifests:
                raise ColdError("unknown manifest override")
            manifests[key] = copy.deepcopy(value)
    checked = {key: _validate(key, manifests[key]) for key in KEYS}
    _check_global_fragment_disjointness(checked, page_overrides)
    order = _order(checked)
    completed: dict[str, ColdProfile] = {}
    for key in order:
        completed[key] = _compile(key, checked[key], completed, page_overrides)
    return ColdPublication(completed, order)


def foundation_record() -> dict[str, str | int]:
    regime, law = foundation_basis()
    return {
        "identity_profile_digest": IDENTITY_PROFILE_ID.digest.hex(),
        "hash_suite_digest": HASH_SUITE_ID.digest.hex(),
        "semantic_regime_digest": regime.digest.hex(),
        "semantic_core_law_length": len(law),
        "semantic_core_law_sha256": hashlib.sha256(law).hexdigest(),
    }


def identity_table(publication: ColdPublication) -> dict[str, Any]:
    profiles: dict[str, Any] = {}
    for key in KEYS:
        artifact = publication.profiles[key]
        profiles[key] = {
            "profile_family": artifact.manifest["profile_family"],
            "revision": artifact.manifest["revision"],
            "direct_imports": list(artifact.direct_import_keys),
            "exact_closure": list(publication.exact_closure(key)),
            "body_length": len(artifact.body_bytes),
            "body_sha256": hashlib.sha256(artifact.body_bytes).hexdigest(),
            "profile_digest": artifact.identifier.digest.hex(),
            "content_ref_hex": artifact.identifier.ref().hex(),
        }
    return {
        "format": "zkc.pir.semantic-profile-identities.v0",
        "foundation": foundation_record(),
        "profiles": profiles,
    }
