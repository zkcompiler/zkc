"""Recursive B2B schema compiler, validator, and inhabitance generator."""

from __future__ import annotations

import copy
import hashlib
import json
from pathlib import Path
from typing import Any


HERE = Path(__file__).resolve().parent
SOURCE = HERE / "schema-source.json"

FORMAT = "zkc.formal-source-view-schema-f0v2b2b.source.v0"
SCOPE = "interaction-r0-normalized-six-view-constructor-grammar"
PROFILE = {
    "key": "interaction",
    "revision": 0,
    "profile_digest": "f21774d19ebf5e045b1d5c70f9bd0ee1c7eb1202dc11f948900eb067e102ce87",
    "profile_body_sha256": "46a4b92b28962ace15009ca2a05ee26e92b0729fb6d7231fd46f3aa6735d1365",
}
PREDECESSOR = {
    "census_format": "zkc.formal-source-constructor-closure-f0v2b2a.inventory.v0",
    "census_sha256": "f258ac5527211f0fc2995fc0a6c2b179646b85d098c6498476e9b7e41ca114d8",
    "bounded_source_sha256": "a143a23c60350d258a9255ebf294111ae4e6ab4ce83c31b25d8162d95b8fd686",
}
OUTER_KEYS = {
    "format",
    "scope",
    "owner_profile",
    "predecessor",
    "maximum_sequence_length",
    "maximum_schema_nodes",
    "maximum_schema_depth",
    "body_compilers",
    "laws",
    "view_order",
    "definitions",
    "views",
}


class SchemaError(ValueError):
    """The B2B source, compiled schema, or candidate value does not form."""


def _strict_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise SchemaError(f"duplicate JSON key {key!r}")
        result[key] = value
    return result


def wire(value: Any) -> bytes:
    try:
        return json.dumps(
            value, sort_keys=True, separators=(",", ":"), ensure_ascii=True
        ).encode("ascii")
    except (TypeError, ValueError) as error:
        raise SchemaError("value has no canonical JSON diagnostic encoding") from error


def digest(value: Any) -> str:
    return hashlib.sha256(wire(value)).hexdigest()


def load_source(path: Path = SOURCE) -> dict[str, Any]:
    try:
        source = json.loads(
            path.read_text(encoding="utf-8"), object_pairs_hook=_strict_object
        )
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        raise SchemaError("cannot read the B2B schema source") from error
    if type(source) is not dict or set(source) != OUTER_KEYS:
        raise SchemaError("schema source has another outer shape")
    if source["format"] != FORMAT or source["scope"] != SCOPE:
        raise SchemaError("schema source format or scope drifted")
    if source["owner_profile"] != PROFILE:
        raise SchemaError("schema source cites another owner profile")
    if source["predecessor"] != PREDECESSOR:
        raise SchemaError("schema source cites another predecessor package")
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


def compile_source(
    source: dict[str, Any],
) -> tuple[dict[str, Any], dict[str, str], dict[str, int]]:
    if type(source) is not dict or set(source) != OUTER_KEYS:
        raise SchemaError("schema source has another outer shape")
    if source["format"] != FORMAT or source["scope"] != SCOPE:
        raise SchemaError("schema source format or scope drifted")
    if source["owner_profile"] != PROFILE:
        raise SchemaError("schema source cites another owner profile")
    if source["predecessor"] != PREDECESSOR:
        raise SchemaError("schema source cites another predecessor package")

    sequence_maximum = source["maximum_sequence_length"]
    node_maximum = source["maximum_schema_nodes"]
    depth_maximum = source["maximum_schema_depth"]
    for value, label, upper in (
        (sequence_maximum, "sequence", 1 << 20),
        (node_maximum, "node", 1 << 24),
        (depth_maximum, "depth", 1 << 12),
    ):
        if type(value) is not int or not 1 <= value <= upper:
            raise SchemaError(f"schema {label} bound is invalid")

    compilers = _catalog(source["body_compilers"], "body compiler")
    laws = _catalog(source["laws"], "law")
    order = source["view_order"]
    definitions = source["definitions"]
    views = source["views"]
    if (
        type(order) is not list
        or len(order) != 6
        or len(set(order)) != 6
        or any(type(view) is not str or not view for view in order)
        or type(definitions) is not dict
        or not definitions
        or list(definitions) != sorted(definitions)
        or type(views) is not dict
        or tuple(views) != tuple(order)
    ):
        raise SchemaError("view or definition catalog is malformed")

    visiting: set[str] = set()
    compiled_definitions: dict[str, dict[str, Any]] = {}
    used: set[str] = set()
    used_compilers: set[str] = set()
    used_laws: set[str] = set()
    source_nodes = 0
    maximum_seen_depth = 0

    def compile_node(node: Any, depth: int) -> dict[str, Any]:
        nonlocal source_nodes, maximum_seen_depth
        source_nodes += 1
        maximum_seen_depth = max(maximum_seen_depth, depth)
        if source_nodes > node_maximum or depth > depth_maximum:
            raise SchemaError("schema expansion crossed a constitutional bound")
        if type(node) is not dict or len(node) != 1:
            raise SchemaError("schema node has another shape")
        if "ref" in node:
            name = node["ref"]
            if type(name) is not str or name not in definitions:
                raise SchemaError("schema source has an unknown definition reference")
            used.add(name)
            return copy.deepcopy(compile_definition(name, depth + 1))
        if "atom" in node:
            atom = node["atom"]
            if type(atom) is not dict or type(atom.get("kind")) is not str:
                raise SchemaError("schema atom is malformed")
            kind = atom["kind"]
            if kind in {"unit", "meta-boolean", "admitted-module-effect"}:
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
                if set(atom) != {"kind", "law"} or atom["law"] not in laws:
                    raise SchemaError("law atom has an unknown exact law")
                used_laws.add(atom["law"])
            else:
                raise SchemaError("schema source uses an unknown atom kind")
            return {"node": "atom", "atom": copy.deepcopy(atom)}
        if "record" in node or "variant" in node:
            kind = "record" if "record" in node else "variant"
            entries = node[kind]
            if type(entries) is not list or not entries:
                raise SchemaError(f"{kind} source must be nonempty")
            compiled_entries: list[list[Any]] = []
            previous = -1
            for entry in entries:
                if type(entry) is not list or len(entry) != 2:
                    raise SchemaError(f"{kind} entry is malformed")
                ordinal, child = entry
                if type(ordinal) is not int or not 0 <= ordinal < 1 << 64:
                    raise SchemaError(f"{kind} ordinal is not a u64")
                if ordinal <= previous:
                    raise SchemaError(f"{kind} ordinals are not strict")
                previous = ordinal
                compiled_entries.append([ordinal, compile_node(child, depth + 1)])
            key = "fields" if kind == "record" else "cases"
            return {"node": kind, key: compiled_entries}
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
                or not 0 <= minimum <= maximum <= sequence_maximum
                or discipline not in {"ordered", "sorted-unique"}
            ):
                raise SchemaError("sequence source has invalid bounds or discipline")
            return {
                "node": "sequence",
                "min": minimum,
                "max": maximum,
                "discipline": discipline,
                "element": compile_node(sequence["element"], depth + 1),
            }
        raise SchemaError("schema source uses an unknown constructor")

    def compile_definition(name: str, depth: int) -> dict[str, Any]:
        if name in compiled_definitions:
            return compiled_definitions[name]
        if name in visiting:
            raise SchemaError("schema definition graph is cyclic")
        visiting.add(name)
        compiled = compile_node(definitions[name], depth + 1)
        visiting.remove(name)
        compiled_definitions[name] = compiled
        return compiled

    schemas: dict[str, Any] = {}
    owners: dict[str, str] = {}
    for view in order:
        entry = views[view]
        if type(entry) is not dict or set(entry) != {"owner_subject_kind", "schema"}:
            raise SchemaError("view source entry is malformed")
        expected_owner = (
            "pir.protocol" if view == "ExecutionView" else "pir.interactive-core"
        )
        if entry["owner_subject_kind"] != expected_owner:
            raise SchemaError("view source entry has the wrong owner kind")
        schemas[view] = compile_node(entry["schema"], 0)
        owners[view] = expected_owner
    if set(definitions) != used:
        raise SchemaError(
            "schema source contains unused definitions: "
            + ", ".join(sorted(set(definitions) - used))
        )
    if set(compilers) != used_compilers or set(laws) != used_laws:
        raise SchemaError("schema source contains an unused compiler or law")
    return (
        schemas,
        owners,
        {
            "definition_count": len(definitions),
            "source_node_count": source_nodes,
            "maximum_source_depth": maximum_seen_depth,
        },
    )


def _canonical_hex(value: Any, label: str) -> None:
    if type(value) is not str or not value or len(value) % 2:
        raise SchemaError(f"{label} is not nonempty even-length hexadecimal")
    try:
        decoded = bytes.fromhex(value)
    except ValueError as error:
        raise SchemaError(f"{label} is not hexadecimal") from error
    if decoded.hex() != value:
        raise SchemaError(f"{label} is not canonical lowercase hexadecimal")


def _validate_atom(atom: dict[str, Any], value: Any) -> None:
    kind = atom["kind"]
    if kind == "unit":
        if value is not None:
            raise SchemaError("unit atom is inhabited by a non-unit value")
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
            raise SchemaError("canonical body uses another compiler")
        _canonical_hex(value["body"], "canonical body")
    elif kind == "exact-profile-law":
        if type(value) is not dict or value != {
            "profile": PROFILE["profile_digest"],
            "kind": "pir.semantic-law",
            "name": atom["law"],
        }:
            raise SchemaError("exact profile law was substituted")
    elif kind == "admitted-module-effect":
        if type(value) is not dict or set(value) != {
            "module_body",
            "declaration_body",
            "payload_body",
        }:
            raise SchemaError("module-effect boundary has another shape")
        for field in ("module_body", "declaration_body", "payload_body"):
            _canonical_hex(value[field], f"module-effect {field}")
    else:  # pragma: no cover - source compilation excludes this path
        raise SchemaError("validator reached an unknown atom")


def validate(schema: dict[str, Any], value: Any) -> None:
    kind = schema.get("node")
    if kind == "atom":
        _validate_atom(schema["atom"], value)
        return
    if kind == "record":
        expected = [ordinal for ordinal, _child in schema["fields"]]
        if type(value) is not dict or list(value) != expected:
            raise SchemaError("record value has another exact field set or order")
        for ordinal, child in schema["fields"]:
            validate(child, value[ordinal])
        return
    if kind == "variant":
        if type(value) is not dict or set(value) != {"case", "value"}:
            raise SchemaError("variant value has another shape")
        selected = [
            child for ordinal, child in schema["cases"] if ordinal == value["case"]
        ]
        if len(selected) != 1:
            raise SchemaError("variant selected an absent case")
        validate(selected[0], value["value"])
        return
    if kind == "sequence":
        if type(value) is not list or not schema["min"] <= len(value) <= schema["max"]:
            raise SchemaError("sequence value is outside its exact length interval")
        if schema["discipline"] == "sorted-unique":
            encodings = [wire(item) for item in value]
            if any(left >= right for left, right in zip(encodings, encodings[1:])):
                raise SchemaError("sorted-unique sequence is not strict")
        for item in value:
            validate(schema["element"], item)
        return
    raise SchemaError("validator reached an unknown compiled node")


def atom_inhabitants(atom: dict[str, Any]) -> list[Any]:
    kind = atom["kind"]
    if kind == "unit":
        return [None]
    if kind == "natural":
        return list(dict.fromkeys((0, atom["max"])))
    if kind == "meta-boolean":
        return [False, True]
    if kind == "canonical-body":
        return [{"compiler": atom["compiler"], "body": "00"}]
    if kind == "exact-profile-law":
        return [
            {
                "profile": PROFILE["profile_digest"],
                "kind": "pir.semantic-law",
                "name": atom["law"],
            }
        ]
    if kind == "admitted-module-effect":
        return [
            {
                "module_body": "00",
                "declaration_body": "00",
                "payload_body": "00",
            }
        ]
    raise SchemaError("generator reached an unknown atom")


def _deduplicate(values: list[Any]) -> list[Any]:
    result: list[Any] = []
    seen: set[bytes] = set()
    for value in values:
        encoded = wire(value)
        if encoded not in seen:
            seen.add(encoded)
            result.append(value)
    return result


def inhabitants(schema: dict[str, Any]) -> list[Any]:
    """Generate an additive suite covering every reachable constructor branch."""

    kind = schema["node"]
    if kind == "atom":
        return atom_inhabitants(schema["atom"])
    if kind == "record":
        child_suites = [inhabitants(child) for _ordinal, child in schema["fields"]]
        baseline = {
            ordinal: copy.deepcopy(suite[0])
            for (ordinal, _child), suite in zip(schema["fields"], child_suites)
        }
        values: list[Any] = [baseline]
        for (ordinal, _child), suite in zip(schema["fields"], child_suites):
            for alternative in suite[1:]:
                candidate = copy.deepcopy(baseline)
                candidate[ordinal] = copy.deepcopy(alternative)
                values.append(candidate)
        return _deduplicate(values)
    if kind == "variant":
        return _deduplicate(
            [
                {"case": ordinal, "value": copy.deepcopy(value)}
                for ordinal, child in schema["cases"]
                for value in inhabitants(child)
            ]
        )
    if kind == "sequence":
        element_suite = inhabitants(schema["element"])
        values = []
        if schema["min"] == 0:
            values.append([])
        if schema["max"] > 0:
            length = max(1, schema["min"])
            for alternative in element_suite:
                values.append(
                    [copy.deepcopy(alternative)]
                    + [copy.deepcopy(element_suite[0]) for _ in range(length - 1)]
                )
        return _deduplicate(values)
    raise SchemaError("generator reached an unknown compiled node")


def coverage_requirements(
    schema: dict[str, Any], path: tuple[tuple[str, int], ...] = ()
) -> set[str]:
    prefix = "/".join(f"{kind}{ordinal}" for kind, ordinal in path) or "root"
    kind = schema["node"]
    if kind == "atom":
        return {
            f"{prefix}:atom:{schema['atom']['kind']}:{index}"
            for index, _value in enumerate(atom_inhabitants(schema["atom"]))
        }
    if kind == "record":
        result = {f"{prefix}:record"}
        for ordinal, child in schema["fields"]:
            result |= coverage_requirements(child, (*path, ("f", ordinal)))
        return result
    if kind == "variant":
        result: set[str] = set()
        for ordinal, child in schema["cases"]:
            result.add(f"{prefix}:variant:{ordinal}")
            result |= coverage_requirements(child, (*path, ("v", ordinal)))
        return result
    if kind == "sequence":
        result = {f"{prefix}:sequence:lower"}
        if schema["max"] > 0:
            result.add(f"{prefix}:sequence:nonempty")
            result |= coverage_requirements(schema["element"], (*path, ("s", 0)))
        return result
    raise SchemaError("coverage traversal reached an unknown compiled node")


def observe_coverage(
    schema: dict[str, Any],
    value: Any,
    path: tuple[tuple[str, int], ...] = (),
) -> set[str]:
    prefix = "/".join(f"{kind}{ordinal}" for kind, ordinal in path) or "root"
    kind = schema["node"]
    if kind == "atom":
        boundaries = atom_inhabitants(schema["atom"])
        return {
            f"{prefix}:atom:{schema['atom']['kind']}:{index}"
            for index, boundary in enumerate(boundaries)
            if boundary == value
        }
    if kind == "record":
        result = {f"{prefix}:record"}
        for ordinal, child in schema["fields"]:
            result |= observe_coverage(child, value[ordinal], (*path, ("f", ordinal)))
        return result
    if kind == "variant":
        result = {f"{prefix}:variant:{value['case']}"}
        child = next(
            child for ordinal, child in schema["cases"] if ordinal == value["case"]
        )
        result |= observe_coverage(child, value["value"], (*path, ("v", value["case"])))
        return result
    if kind == "sequence":
        result = set()
        if len(value) == schema["min"]:
            result.add(f"{prefix}:sequence:lower")
        if value:
            result.add(f"{prefix}:sequence:nonempty")
            for item in value:
                result |= observe_coverage(schema["element"], item, (*path, ("s", 0)))
        return result
    raise SchemaError("coverage traversal reached an unknown compiled node")


def compile_current() -> tuple[dict[str, Any], dict[str, str], dict[str, int]]:
    return compile_source(load_source())
