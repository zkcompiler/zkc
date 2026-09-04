"""Recursive compiler for the current FS-family view grammar."""

from __future__ import annotations

import copy
import hashlib
import json
from pathlib import Path
from typing import Any


HERE = Path(__file__).resolve().parent
SOURCE = HERE / "schema-source.json"
FORMAT = "zkc.formal-source-fs-view-determinacy-f0v3.source.v1"
SCOPE = "fs-family-current-eight-view-grammar"
OUTER_KEYS = {
    "format",
    "scope",
    "owner_profiles",
    "maximum_sequence_length",
    "maximum_schema_nodes",
    "maximum_schema_depth",
    "body_compilers",
    "laws",
    "view_order",
    "definitions",
    "views",
}
EXPECTED_OWNERS = {
    "CanonicalTranscriptDeclarationView": "pir.transcript-construction",
    "CanonicalRequiredInfluenceView": "pir.transcript-construction",
    "CanonicalChallengeTransitionView": "pir.transcript-construction",
    "CanonicalFSConstructionView": "pir.checked-fs-construction",
    "DuplexTranscriptDeclarationView": "pir.transcript-construction",
    "DuplexEncodedInputCoverageView": "pir.transcript-construction",
    "DuplexChallengeTransitionView": "pir.transcript-construction",
    "DuplexFSConstructionView": "pir.checked-duplex-fs-construction",
}
VIEW_FAMILIES = {
    name: ("canonical-framed" if name.startswith("Canonical") else "duplex-sponge")
    for name in EXPECTED_OWNERS
}


class SchemaError(ValueError):
    """The candidate source, schema, or value is malformed."""


def _strict_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    value: dict[str, Any] = {}
    for key, child in pairs:
        if key in value:
            raise SchemaError(f"duplicate JSON key {key!r}")
        value[key] = child
    return value


def wire(value: Any) -> bytes:
    try:
        return json.dumps(
            value, sort_keys=True, separators=(",", ":"), ensure_ascii=True
        ).encode("ascii")
    except (TypeError, ValueError) as error:
        raise SchemaError("value has no canonical diagnostic encoding") from error


def digest(value: Any) -> str:
    return hashlib.sha256(wire(value)).hexdigest()


def load_source(path: Path = SOURCE) -> dict[str, Any]:
    try:
        source = json.loads(
            path.read_text(encoding="utf-8"), object_pairs_hook=_strict_object
        )
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        raise SchemaError("cannot read the F0-V3 schema source") from error
    return source


def _catalog(value: Any, label: str) -> list[str]:
    if (
        type(value) is not list
        or not value
        or any(type(item) is not str or not item for item in value)
        or value != sorted(set(value))
    ):
        raise SchemaError(f"{label} catalog is not canonical sorted-unique")
    return value


def _preamble(source: dict[str, Any]) -> tuple[dict[str, Any], set[str], set[str]]:
    if type(source) is not dict or set(source) != OUTER_KEYS:
        raise SchemaError("schema source has another outer shape")
    if source["format"] != FORMAT or source["scope"] != SCOPE:
        raise SchemaError("schema source format or scope drifted")
    profiles = source["owner_profiles"]
    if (
        type(profiles) is not dict
        or list(profiles) != sorted(profiles)
        or set(profiles) != {"canonical-framed", "duplex-sponge"}
    ):
        raise SchemaError("owner profile catalog is malformed")
    expected_revisions = {"canonical-framed": 4, "duplex-sponge": 3}
    for key, profile in profiles.items():
        if (
            type(profile) is not dict
            or set(profile) != {
                "key",
                "revision",
                "profile_digest",
                "profile_body_sha256",
            }
            or profile["key"] != key
            or profile["revision"] != expected_revisions[key]
            or any(
                type(profile[name]) is not str or len(profile[name]) != 64
                for name in ("profile_digest", "profile_body_sha256")
            )
        ):
            raise SchemaError("owner profile pin is malformed")
    return (
        profiles,
        set(_catalog(source["body_compilers"], "body compiler")),
        set(_catalog(source["laws"], "law")),
    )


def compile_source(
    source: dict[str, Any],
) -> tuple[dict[str, Any], dict[str, str], dict[str, int]]:
    profiles, compilers, laws = _preamble(source)
    sequence_limit = source["maximum_sequence_length"]
    node_limit = source["maximum_schema_nodes"]
    depth_limit = source["maximum_schema_depth"]
    for value, cap in (
        (sequence_limit, 1 << 20),
        (node_limit, 1 << 24),
        (depth_limit, 1 << 12),
    ):
        if type(value) is not int or not 1 <= value <= cap:
            raise SchemaError("schema constitutional bound is invalid")
    definitions = source["definitions"]
    order = source["view_order"]
    views = source["views"]
    if (
        type(definitions) is not dict
        or not definitions
        or list(definitions) != sorted(definitions)
        or type(order) is not list
        or len(order) != 8
        or len(set(order)) != 8
        or type(views) is not dict
        or tuple(views) != tuple(order)
    ):
        raise SchemaError("view or definition catalog is malformed")

    visiting: set[str] = set()
    compiled: dict[str, dict[str, Any]] = {}
    used_definitions: set[str] = set()
    used_compilers: set[str] = set()
    used_laws: set[str] = set()
    source_nodes = 0
    maximum_depth = 0

    def compile_node(node: Any, depth: int) -> dict[str, Any]:
        nonlocal source_nodes, maximum_depth
        source_nodes += 1
        maximum_depth = max(maximum_depth, depth)
        if source_nodes > node_limit or depth > depth_limit:
            raise SchemaError("schema expansion crossed a constitutional bound")
        if type(node) is not dict or len(node) != 1:
            raise SchemaError("schema node has another shape")
        if "ref" in node:
            name = node["ref"]
            if type(name) is not str or name not in definitions:
                raise SchemaError("unknown definition reference")
            used_definitions.add(name)
            return copy.deepcopy(compile_definition(name, depth + 1))
        if "atom" in node:
            atom = node["atom"]
            if type(atom) is not dict or type(atom.get("kind")) is not str:
                raise SchemaError("schema atom is malformed")
            kind = atom["kind"]
            if kind in {"unit", "meta-boolean"}:
                if set(atom) != {"kind"}:
                    raise SchemaError("primitive atom has surplus fields")
            elif kind == "natural":
                if (
                    set(atom) != {"kind", "max"}
                    or type(atom["max"]) is not int
                    or not 0 <= atom["max"] < 1 << 256
                ):
                    raise SchemaError("natural atom has an invalid bound")
            elif kind == "canonical-body":
                if (
                    set(atom) != {"kind", "compiler"}
                    or atom["compiler"] not in compilers
                ):
                    raise SchemaError("canonical-body atom has an unknown compiler")
                used_compilers.add(atom["compiler"])
            elif kind == "exact-profile-law":
                if (
                    set(atom) != {"kind", "profile", "law"}
                    or atom["profile"] not in profiles
                    or atom["law"] not in laws
                    or not atom["law"].startswith(atom["profile"] + ":")
                ):
                    raise SchemaError("exact law atom has an unknown owner law")
                used_laws.add(atom["law"])
            else:
                raise SchemaError("schema source uses an unknown atom kind")
            return {"node": "atom", "atom": copy.deepcopy(atom)}
        if "record" in node or "variant" in node:
            kind = "record" if "record" in node else "variant"
            entries = node[kind]
            if type(entries) is not list or not entries:
                raise SchemaError(f"{kind} source must be nonempty")
            previous = -1
            result: list[list[Any]] = []
            for entry in entries:
                if type(entry) is not list or len(entry) != 2:
                    raise SchemaError(f"{kind} entry is malformed")
                ordinal, child = entry
                if type(ordinal) is not int or not 0 <= ordinal < 1 << 64:
                    raise SchemaError(f"{kind} ordinal is not a u64")
                if ordinal <= previous:
                    raise SchemaError(f"{kind} ordinals are not strict")
                previous = ordinal
                result.append([ordinal, compile_node(child, depth + 1)])
            return {
                "node": kind,
                "fields" if kind == "record" else "cases": result,
            }
        if "sequence" in node:
            sequence = node["sequence"]
            if type(sequence) is not dict or set(sequence) != {
                "min",
                "max",
                "discipline",
                "element",
            }:
                raise SchemaError("sequence source is malformed")
            minimum = sequence["min"]
            maximum = sequence["max"]
            discipline = sequence["discipline"]
            if (
                type(minimum) is not int
                or type(maximum) is not int
                or not 0 <= minimum <= maximum <= sequence_limit
                or discipline not in {"ordered", "sorted-unique"}
            ):
                raise SchemaError("sequence bounds or discipline are invalid")
            return {
                "node": "sequence",
                "min": minimum,
                "max": maximum,
                "discipline": discipline,
                "element": compile_node(sequence["element"], depth + 1),
            }
        raise SchemaError("schema source uses an unknown constructor")

    def compile_definition(name: str, depth: int) -> dict[str, Any]:
        if name in compiled:
            return compiled[name]
        if name in visiting:
            raise SchemaError("schema definition graph is cyclic")
        visiting.add(name)
        result = compile_node(definitions[name], depth + 1)
        visiting.remove(name)
        compiled[name] = result
        return result

    schemas: dict[str, Any] = {}
    owners: dict[str, str] = {}
    for view in order:
        entry = views[view]
        if type(entry) is not dict or set(entry) != {"owner_subject_kind", "schema"}:
            raise SchemaError("view source entry is malformed")
        owner = entry["owner_subject_kind"]
        if owner != EXPECTED_OWNERS[view]:
            raise SchemaError("view owner subject kind was substituted")
        schemas[view] = compile_node(entry["schema"], 0)
        owners[view] = owner
    if set(definitions) != used_definitions:
        raise SchemaError("schema source contains an unused definition")
    if compilers != used_compilers or laws != used_laws:
        raise SchemaError("schema source contains an unused compiler or law")
    return schemas, owners, {
        "definition_count": len(definitions),
        "source_node_count": source_nodes,
        "maximum_source_depth": maximum_depth,
    }


def _canonical_hex(value: Any) -> None:
    if type(value) is not str or not value or len(value) % 2:
        raise SchemaError("canonical body is not nonempty even-length hexadecimal")
    try:
        decoded = bytes.fromhex(value)
    except ValueError as error:
        raise SchemaError("canonical body is not hexadecimal") from error
    if decoded.hex() != value:
        raise SchemaError("canonical body is not canonical lowercase hexadecimal")


def _validate_atom(atom: dict[str, Any], value: Any, profiles: dict[str, Any]) -> None:
    kind = atom["kind"]
    if kind == "unit":
        if value is not None:
            raise SchemaError("unit atom has a non-unit value")
    elif kind == "natural":
        if type(value) is not int or not 0 <= value <= atom["max"]:
            raise SchemaError("natural atom is outside its exact bound")
    elif kind == "meta-boolean":
        if type(value) is not bool:
            raise SchemaError("MetaBoolean atom has another type")
    elif kind == "canonical-body":
        if type(value) is not dict or set(value) != {"compiler", "body"}:
            raise SchemaError("canonical body has another shape")
        if value["compiler"] != atom["compiler"]:
            raise SchemaError("canonical body compiler was substituted")
        _canonical_hex(value["body"])
    elif kind == "exact-profile-law":
        expected = {
            "profile": profiles[atom["profile"]]["profile_digest"],
            "kind": "pir.semantic-law",
            "name": atom["law"].split(":", 1)[1],
        }
        if type(value) is not dict or value != expected:
            raise SchemaError("exact owner-profile law was substituted")
    else:  # pragma: no cover - compilation excludes this path
        raise SchemaError("validator reached an unknown atom")


def validate(schema: dict[str, Any], value: Any, profiles: dict[str, Any]) -> None:
    kind = schema.get("node")
    if kind == "atom":
        _validate_atom(schema["atom"], value, profiles)
    elif kind == "record":
        expected = [ordinal for ordinal, _child in schema["fields"]]
        if type(value) is not dict or list(value) != expected:
            raise SchemaError("record value has another exact field set or order")
        for ordinal, child in schema["fields"]:
            validate(child, value[ordinal], profiles)
    elif kind == "variant":
        if type(value) is not dict or set(value) != {"case", "value"}:
            raise SchemaError("variant value has another shape")
        selected = [
            child for ordinal, child in schema["cases"] if ordinal == value["case"]
        ]
        if len(selected) != 1:
            raise SchemaError("variant selected an absent case")
        validate(selected[0], value["value"], profiles)
    elif kind == "sequence":
        if type(value) is not list or not schema["min"] <= len(value) <= schema["max"]:
            raise SchemaError("sequence value is outside its exact interval")
        if schema["discipline"] == "sorted-unique":
            encodings = [wire(item) for item in value]
            if any(left >= right for left, right in zip(encodings, encodings[1:])):
                raise SchemaError("sorted-unique sequence is not strict")
        for item in value:
            validate(schema["element"], item, profiles)
    else:
        raise SchemaError("validator reached an unknown compiled node")


def validate_view(
    family: str,
    view: str,
    schemas: dict[str, Any],
    value: Any,
    profiles: dict[str, Any],
) -> None:
    """Validate one value only under its exact family-local view kind."""

    if family not in {"canonical-framed", "duplex-sponge"}:
        raise SchemaError("unknown FS view family")
    if view not in schemas or VIEW_FAMILIES.get(view) != family:
        raise SchemaError("view kind belongs to another FS family")
    validate(schemas[view], value, profiles)


def schema_counts(schema: dict[str, Any]) -> tuple[int, int]:
    """Return expanded node and atomic-leaf counts."""

    kind = schema["node"]
    if kind == "atom":
        return 1, 1
    if kind in {"record", "variant"}:
        children = schema["fields" if kind == "record" else "cases"]
        counts = [schema_counts(child) for _ordinal, child in children]
    elif kind == "sequence":
        counts = [schema_counts(schema["element"])]
    else:  # pragma: no cover - compiler excludes this path
        raise SchemaError("counter reached an unknown node")
    return 1 + sum(item[0] for item in counts), sum(item[1] for item in counts)


def value_leaf_count(schema: dict[str, Any], value: Any) -> int:
    kind = schema["node"]
    if kind == "atom":
        return 1
    if kind == "record":
        return sum(
            value_leaf_count(child, value[ordinal])
            for ordinal, child in schema["fields"]
        )
    if kind == "variant":
        child = next(
            child for ordinal, child in schema["cases"] if ordinal == value["case"]
        )
        return value_leaf_count(child, value["value"])
    if kind == "sequence":
        return sum(value_leaf_count(schema["element"], item) for item in value)
    raise SchemaError("value counter reached an unknown node")


def compile_current() -> tuple[dict[str, Any], dict[str, str], dict[str, int]]:
    return compile_source(load_source())
