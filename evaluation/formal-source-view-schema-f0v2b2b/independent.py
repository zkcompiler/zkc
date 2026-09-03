"""Iterative B2B schema compiler and value validator."""

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
    "revision": 2,
    "profile_digest": "9a971206c68eab0b5b5e8124787bfce2f5335467a576b242190750e773941d2f",
    "profile_body_sha256": "fbba36f4b0e15dcc55ef60d4d251b0286c9627726c1bf6f827c95784fcd00f70",
}
PREDECESSOR = {
    "census_format": "zkc.formal-source-constructor-closure-f0v2b2a.inventory.v0",
    "census_sha256": "7d0eac60af6ee3351615e39300349f6f28c6f44eda2d5f532a12927f4a175dbe",
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


class IndependentError(ValueError):
    """The cold B2B compiler or validator refused its input."""


def _strict_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    value: dict[str, Any] = {}
    for key, child in pairs:
        if key in value:
            raise IndependentError(f"duplicate JSON key {key!r}")
        value[key] = child
    return value


def _wire(value: Any) -> bytes:
    try:
        return json.dumps(
            value, sort_keys=True, separators=(",", ":"), ensure_ascii=True
        ).encode("ascii")
    except (TypeError, ValueError) as error:
        raise IndependentError("cold value is not diagnostically canonical") from error


def digest(value: Any) -> str:
    return hashlib.sha256(_wire(value)).hexdigest()


def load_source(path: Path = SOURCE) -> dict[str, Any]:
    try:
        value = json.loads(
            path.read_text(encoding="utf-8"), object_pairs_hook=_strict_object
        )
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        raise IndependentError("cold compiler cannot read the B2B source") from error
    return value


def _check_atom(atom: Any, compilers: set[str], laws: set[str]) -> None:
    if type(atom) is not dict or type(atom.get("kind")) is not str:
        raise IndependentError("cold atom is malformed")
    kind = atom["kind"]
    if kind in {"unit", "meta-boolean", "admitted-module-effect"}:
        if set(atom) != {"kind"}:
            raise IndependentError("cold primitive atom has surplus fields")
    elif kind == "natural":
        if (
            set(atom) != {"kind", "max"}
            or type(atom["max"]) is not int
            or not 0 <= atom["max"] < 1 << 256
        ):
            raise IndependentError("cold natural atom bound is invalid")
    elif kind == "canonical-body":
        if set(atom) != {"kind", "compiler"} or atom["compiler"] not in compilers:
            raise IndependentError("cold canonical-body compiler is unknown")
    elif kind == "exact-profile-law":
        if set(atom) != {"kind", "law"} or atom["law"] not in laws:
            raise IndependentError("cold exact law is unknown")
    else:
        raise IndependentError("cold compiler found an unknown atom kind")


def _inspect_raw(
    root: Any,
    definitions: dict[str, Any],
    compilers: set[str],
    laws: set[str],
    sequence_limit: int,
    depth_limit: int,
) -> tuple[set[str], set[str], set[str], int, int]:
    dependencies: set[str] = set()
    used_compilers: set[str] = set()
    used_laws: set[str] = set()
    count = 0
    maximum_depth = 0
    stack: list[tuple[Any, int]] = [(root, 0)]
    while stack:
        node, depth = stack.pop()
        count += 1
        maximum_depth = max(maximum_depth, depth)
        if depth > depth_limit:
            raise IndependentError("cold source crossed its depth bound")
        if type(node) is not dict or len(node) != 1:
            raise IndependentError("cold source node has another shape")
        if "ref" in node:
            name = node["ref"]
            if type(name) is not str or name not in definitions:
                raise IndependentError("cold source references an unknown definition")
            dependencies.add(name)
            continue
        if "atom" in node:
            _check_atom(node["atom"], compilers, laws)
            if node["atom"]["kind"] == "canonical-body":
                used_compilers.add(node["atom"]["compiler"])
            elif node["atom"]["kind"] == "exact-profile-law":
                used_laws.add(node["atom"]["law"])
            continue
        if "record" in node or "variant" in node:
            kind = "record" if "record" in node else "variant"
            entries = node[kind]
            if type(entries) is not list or not entries:
                raise IndependentError(f"cold {kind} is empty or malformed")
            ordinals: list[int] = []
            children: list[Any] = []
            for entry in entries:
                if type(entry) is not list or len(entry) != 2:
                    raise IndependentError(f"cold {kind} entry is malformed")
                ordinal, child = entry
                if type(ordinal) is not int or not 0 <= ordinal < 1 << 64:
                    raise IndependentError(f"cold {kind} ordinal is not a u64")
                ordinals.append(ordinal)
                children.append(child)
            if any(left >= right for left, right in zip(ordinals, ordinals[1:])):
                raise IndependentError(f"cold {kind} ordinals are not strict")
            stack.extend((child, depth + 1) for child in reversed(children))
            continue
        if "sequence" in node:
            sequence = node["sequence"]
            if type(sequence) is not dict or set(sequence) != {
                "min",
                "max",
                "discipline",
                "element",
            }:
                raise IndependentError("cold sequence is malformed")
            minimum = sequence["min"]
            maximum = sequence["max"]
            if (
                type(minimum) is not int
                or type(maximum) is not int
                or not 0 <= minimum <= maximum <= sequence_limit
                or sequence["discipline"] not in {"ordered", "sorted-unique"}
            ):
                raise IndependentError("cold sequence contract is invalid")
            stack.append((sequence["element"], depth + 1))
            continue
        raise IndependentError("cold source uses an unknown constructor")
    return dependencies, used_compilers, used_laws, count, maximum_depth


def _expand(root: Any, compiled: dict[str, dict[str, Any]]) -> dict[str, Any]:
    work: list[tuple[str, Any]] = [("visit", root)]
    values: list[dict[str, Any]] = []
    while work:
        action, payload = work.pop()
        if action == "visit":
            node = payload
            if "ref" in node:
                values.append(copy.deepcopy(compiled[node["ref"]]))
            elif "atom" in node:
                values.append({"node": "atom", "atom": copy.deepcopy(node["atom"])})
            elif "record" in node or "variant" in node:
                kind = "record" if "record" in node else "variant"
                entries = node[kind]
                work.append((f"assemble-{kind}", [entry[0] for entry in entries]))
                work.extend(("visit", entry[1]) for entry in reversed(entries))
            elif "sequence" in node:
                work.append(("assemble-sequence", copy.deepcopy(node["sequence"])))
                work.append(("visit", node["sequence"]["element"]))
            else:  # pragma: no cover - raw inspection excludes this path
                raise IndependentError("cold expansion reached an unknown node")
        elif action in {"assemble-record", "assemble-variant"}:
            ordinals = payload
            count = len(ordinals)
            children = values[-count:]
            del values[-count:]
            kind = action.removeprefix("assemble-")
            key = "fields" if kind == "record" else "cases"
            values.append(
                {
                    "node": kind,
                    key: [[o, child] for o, child in zip(ordinals, children)],
                }
            )
        elif action == "assemble-sequence":
            child = values.pop()
            values.append(
                {
                    "node": "sequence",
                    "min": payload["min"],
                    "max": payload["max"],
                    "discipline": payload["discipline"],
                    "element": child,
                }
            )
        else:  # pragma: no cover - local worklist invariant
            raise AssertionError(f"unknown cold action {action}")
    if len(values) != 1:
        raise IndependentError("cold expansion left an invalid work stack")
    return values[0]


def compile_source(
    source: dict[str, Any],
) -> tuple[dict[str, Any], dict[str, str], dict[str, int]]:
    if type(source) is not dict or set(source) != OUTER_KEYS:
        raise IndependentError("cold source has another outer shape")
    if source["format"] != FORMAT or source["scope"] != SCOPE:
        raise IndependentError("cold source format or scope drifted")
    if source["owner_profile"] != PROFILE:
        raise IndependentError("cold source cites another owner profile")
    if source["predecessor"] != PREDECESSOR:
        raise IndependentError("cold source cites another predecessor package")

    bounds = (
        (source["maximum_sequence_length"], 1 << 20),
        (source["maximum_schema_nodes"], 1 << 24),
        (source["maximum_schema_depth"], 1 << 12),
    )
    if any(type(value) is not int or not 1 <= value <= cap for value, cap in bounds):
        raise IndependentError("cold source has an invalid constitutional bound")
    compilers = source["body_compilers"]
    laws = source["laws"]
    for value, label in ((compilers, "compiler"), (laws, "law")):
        if (
            type(value) is not list
            or not value
            or any(type(item) is not str or not item for item in value)
            or value != sorted(set(value))
        ):
            raise IndependentError(f"cold {label} catalog is not sorted-unique")

    definitions = source["definitions"]
    order = source["view_order"]
    views = source["views"]
    if (
        type(definitions) is not dict
        or not definitions
        or list(definitions) != sorted(definitions)
        or type(order) is not list
        or len(order) != 6
        or len(set(order)) != 6
        or type(views) is not dict
        or tuple(views) != tuple(order)
    ):
        raise IndependentError("cold definition or view catalog is malformed")

    dependency_graph: dict[str, set[str]] = {}
    used_compilers: set[str] = set()
    used_laws: set[str] = set()
    raw_nodes = 0
    maximum_raw_depth = 0
    for name, root in definitions.items():
        dependencies, compiler_uses, law_uses, count, depth = _inspect_raw(
            root,
            definitions,
            set(compilers),
            set(laws),
            source["maximum_sequence_length"],
            source["maximum_schema_depth"],
        )
        dependency_graph[name] = dependencies
        used_compilers |= compiler_uses
        used_laws |= law_uses
        raw_nodes += count
        maximum_raw_depth = max(maximum_raw_depth, depth)
    if raw_nodes > source["maximum_schema_nodes"]:
        raise IndependentError("cold source crossed its node bound")

    compiled: dict[str, dict[str, Any]] = {}
    remaining = set(definitions)
    while remaining:
        ready = sorted(
            name for name in remaining if dependency_graph[name] <= set(compiled)
        )
        if not ready:
            raise IndependentError("cold definition graph is cyclic")
        for name in ready:
            compiled[name] = _expand(definitions[name], compiled)
            remaining.remove(name)

    schemas: dict[str, Any] = {}
    owners: dict[str, str] = {}
    used: set[str] = set().union(*dependency_graph.values())
    for view in order:
        entry = views[view]
        if type(entry) is not dict or set(entry) != {"owner_subject_kind", "schema"}:
            raise IndependentError("cold view entry is malformed")
        expected_owner = (
            "pir.protocol" if view == "ExecutionView" else "pir.interactive-core"
        )
        if entry["owner_subject_kind"] != expected_owner:
            raise IndependentError("cold view has another owner kind")
        dependencies, compiler_uses, law_uses, count, depth = _inspect_raw(
            entry["schema"],
            definitions,
            set(compilers),
            set(laws),
            source["maximum_sequence_length"],
            source["maximum_schema_depth"],
        )
        used |= dependencies
        used_compilers |= compiler_uses
        used_laws |= law_uses
        raw_nodes += count
        maximum_raw_depth = max(maximum_raw_depth, depth)
        schemas[view] = _expand(entry["schema"], compiled)
        owners[view] = expected_owner
    if set(definitions) != used:
        raise IndependentError("cold source contains an unused definition")
    if set(compilers) != used_compilers or set(laws) != used_laws:
        raise IndependentError("cold source contains an unused compiler or law")
    if raw_nodes > source["maximum_schema_nodes"]:
        raise IndependentError("cold source crossed its node bound")
    return (
        schemas,
        owners,
        {
            "definition_count": len(definitions),
            "source_node_count": raw_nodes,
            "maximum_raw_depth": maximum_raw_depth,
        },
    )


def _hex(value: Any, label: str) -> None:
    if type(value) is not str or not value or len(value) % 2:
        raise IndependentError(f"cold {label} is not even nonempty hexadecimal")
    try:
        decoded = bytes.fromhex(value)
    except ValueError as error:
        raise IndependentError(f"cold {label} is not hexadecimal") from error
    if decoded.hex() != value:
        raise IndependentError(f"cold {label} is not canonical lowercase hexadecimal")


def _atom(atom: dict[str, Any], value: Any) -> None:
    kind = atom["kind"]
    if kind == "unit":
        if value is not None:
            raise IndependentError("cold unit is inhabited")
    elif kind == "natural":
        if type(value) is not int or not 0 <= value <= atom["max"]:
            raise IndependentError("cold natural crossed its bound")
    elif kind == "meta-boolean":
        if type(value) is not bool:
            raise IndependentError("cold Boolean has another type")
    elif kind == "canonical-body":
        if type(value) is not dict or set(value) != {"compiler", "body"}:
            raise IndependentError("cold canonical body has another shape")
        if value["compiler"] != atom["compiler"]:
            raise IndependentError("cold canonical body uses another compiler")
        _hex(value["body"], "canonical body")
    elif kind == "exact-profile-law":
        expected = {
            "profile": PROFILE["profile_digest"],
            "kind": "pir.semantic-law",
            "name": atom["law"],
        }
        if type(value) is not dict or value != expected:
            raise IndependentError("cold exact law was substituted")
    elif kind == "admitted-module-effect":
        if type(value) is not dict or set(value) != {
            "module_body",
            "declaration_body",
            "payload_body",
        }:
            raise IndependentError("cold module boundary has another shape")
        for name in ("module_body", "declaration_body", "payload_body"):
            _hex(value[name], f"module {name}")
    else:  # pragma: no cover - source compiler excludes this path
        raise IndependentError("cold validator reached an unknown atom")


def validate(schema: dict[str, Any], value: Any) -> None:
    work: list[tuple[dict[str, Any], Any]] = [(schema, value)]
    while work:
        node, current = work.pop()
        kind = node.get("node")
        if kind == "atom":
            _atom(node["atom"], current)
        elif kind == "record":
            expected = [ordinal for ordinal, _child in node["fields"]]
            if type(current) is not dict or list(current) != expected:
                raise IndependentError("cold record has another field set or order")
            work.extend(
                (child, current[ordinal]) for ordinal, child in reversed(node["fields"])
            )
        elif kind == "variant":
            if type(current) is not dict or set(current) != {"case", "value"}:
                raise IndependentError("cold variant has another shape")
            selected = [
                child for ordinal, child in node["cases"] if ordinal == current["case"]
            ]
            if len(selected) != 1:
                raise IndependentError("cold variant selected an absent case")
            work.append((selected[0], current["value"]))
        elif kind == "sequence":
            if (
                type(current) is not list
                or not node["min"] <= len(current) <= node["max"]
            ):
                raise IndependentError("cold sequence crossed its length interval")
            if node["discipline"] == "sorted-unique":
                encodings = [_wire(item) for item in current]
                if any(left >= right for left, right in zip(encodings, encodings[1:])):
                    raise IndependentError("cold sorted-unique sequence is not strict")
            work.extend((node["element"], item) for item in reversed(current))
        else:
            raise IndependentError("cold validator reached an unknown compiled node")


def compile_current() -> tuple[dict[str, Any], dict[str, str], dict[str, int]]:
    return compile_source(load_source())
