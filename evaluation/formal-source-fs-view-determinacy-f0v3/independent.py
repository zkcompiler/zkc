"""Iterative compiler and validator for the current FS-family grammar."""

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


class IndependentError(ValueError):
    """The cold compiler or validator refused its input."""


def _strict_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise IndependentError(f"duplicate JSON key {key!r}")
        result[key] = value
    return result


def wire(value: Any) -> bytes:
    return json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=True
    ).encode("ascii")


def digest(value: Any) -> str:
    return hashlib.sha256(wire(value)).hexdigest()


def load_source(path: Path = SOURCE) -> dict[str, Any]:
    try:
        return json.loads(
            path.read_text(encoding="utf-8"), object_pairs_hook=_strict_object
        )
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        raise IndependentError("cold compiler cannot read the source") from error


def _inspect(
    root: Any,
    definitions: dict[str, Any],
    compilers: set[str],
    laws: set[str],
    profiles: set[str],
    sequence_limit: int,
    depth_limit: int,
) -> tuple[set[str], set[str], set[str], int, int]:
    dependencies: set[str] = set()
    used_compilers: set[str] = set()
    used_laws: set[str] = set()
    nodes = 0
    maximum_depth = 0
    stack: list[tuple[Any, int]] = [(root, 0)]
    while stack:
        node, depth = stack.pop()
        nodes += 1
        maximum_depth = max(maximum_depth, depth)
        if depth > depth_limit or type(node) is not dict or len(node) != 1:
            raise IndependentError("cold source node is malformed or too deep")
        if "ref" in node:
            name = node["ref"]
            if type(name) is not str or name not in definitions:
                raise IndependentError("cold source has an unknown reference")
            dependencies.add(name)
        elif "atom" in node:
            atom = node["atom"]
            if type(atom) is not dict or type(atom.get("kind")) is not str:
                raise IndependentError("cold atom is malformed")
            kind = atom["kind"]
            if kind in {"unit", "meta-boolean"}:
                if set(atom) != {"kind"}:
                    raise IndependentError("cold primitive atom has surplus fields")
            elif kind == "natural":
                if (
                    set(atom) != {"kind", "max"}
                    or type(atom["max"]) is not int
                    or not 0 <= atom["max"] < 1 << 256
                ):
                    raise IndependentError("cold natural bound is invalid")
            elif kind == "canonical-body":
                if (
                    set(atom) != {"kind", "compiler"}
                    or atom["compiler"] not in compilers
                ):
                    raise IndependentError("cold body compiler is unknown")
                used_compilers.add(atom["compiler"])
            elif kind == "exact-profile-law":
                if (
                    set(atom) != {"kind", "profile", "law"}
                    or atom["profile"] not in profiles
                    or atom["law"] not in laws
                    or not atom["law"].startswith(atom["profile"] + ":")
                ):
                    raise IndependentError("cold exact law is unknown")
                used_laws.add(atom["law"])
            else:
                raise IndependentError("cold source uses an unknown atom")
        elif "record" in node or "variant" in node:
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
        elif "sequence" in node:
            sequence = node["sequence"]
            if type(sequence) is not dict or set(sequence) != {
                "min",
                "max",
                "discipline",
                "element",
            }:
                raise IndependentError("cold sequence is malformed")
            if (
                type(sequence["min"]) is not int
                or type(sequence["max"]) is not int
                or not 0 <= sequence["min"] <= sequence["max"] <= sequence_limit
                or sequence["discipline"] not in {"ordered", "sorted-unique"}
            ):
                raise IndependentError("cold sequence contract is invalid")
            stack.append((sequence["element"], depth + 1))
        else:
            raise IndependentError("cold source uses an unknown constructor")
    return dependencies, used_compilers, used_laws, nodes, maximum_depth


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
                work.append(("assemble-" + kind, [entry[0] for entry in entries]))
                work.extend(("visit", entry[1]) for entry in reversed(entries))
            elif "sequence" in node:
                work.append(("assemble-sequence", copy.deepcopy(node["sequence"])))
                work.append(("visit", node["sequence"]["element"]))
            else:  # pragma: no cover - inspection excludes this path
                raise IndependentError("cold expansion reached an unknown node")
        elif action in {"assemble-record", "assemble-variant"}:
            ordinals = payload
            children = values[-len(ordinals) :]
            del values[-len(ordinals) :]
            kind = action.removeprefix("assemble-")
            values.append(
                {
                    "node": kind,
                    "fields" if kind == "record" else "cases": [
                        [ordinal, child]
                        for ordinal, child in zip(ordinals, children, strict=True)
                    ],
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
            raise AssertionError("unknown cold work item")
    if len(values) != 1:
        raise IndependentError("cold expansion left an invalid stack")
    return values[0]


def compile_source(
    source: dict[str, Any],
) -> tuple[dict[str, Any], dict[str, str], dict[str, int]]:
    if type(source) is not dict or set(source) != OUTER_KEYS:
        raise IndependentError("cold source has another outer shape")
    if source["format"] != FORMAT or source["scope"] != SCOPE:
        raise IndependentError("cold source format or scope drifted")
    profiles = source["owner_profiles"]
    if (
        type(profiles) is not dict
        or list(profiles) != sorted(profiles)
        or set(profiles) != {"canonical-framed", "duplex-sponge"}
    ):
        raise IndependentError("cold owner-profile catalog is malformed")
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
            or profile["revision"] != 2
        ):
            raise IndependentError("cold owner-profile pin is malformed")
    for key, cap in (
        ("maximum_sequence_length", 1 << 20),
        ("maximum_schema_nodes", 1 << 24),
        ("maximum_schema_depth", 1 << 12),
    ):
        value = source[key]
        if type(value) is not int or not 1 <= value <= cap:
            raise IndependentError("cold constitutional bound is invalid")
    compilers = source["body_compilers"]
    laws = source["laws"]
    for value in (compilers, laws):
        if (
            type(value) is not list
            or not value
            or value != sorted(set(value))
            or any(type(item) is not str or not item for item in value)
        ):
            raise IndependentError("cold catalog is not sorted-unique")
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
        raise IndependentError("cold view or definition catalog is malformed")

    graph: dict[str, set[str]] = {}
    used_compilers: set[str] = set()
    used_laws: set[str] = set()
    nodes = 0
    maximum_depth = 0
    for name, root in definitions.items():
        dependencies, compiler_uses, law_uses, count, depth = _inspect(
            root,
            definitions,
            set(compilers),
            set(laws),
            set(profiles),
            source["maximum_sequence_length"],
            source["maximum_schema_depth"],
        )
        graph[name] = dependencies
        used_compilers |= compiler_uses
        used_laws |= law_uses
        nodes += count
        maximum_depth = max(maximum_depth, depth)
    if nodes > source["maximum_schema_nodes"]:
        raise IndependentError("cold source crossed its node bound")
    compiled: dict[str, dict[str, Any]] = {}
    remaining = set(definitions)
    while remaining:
        ready = sorted(name for name in remaining if graph[name] <= set(compiled))
        if not ready:
            raise IndependentError("cold definition graph is cyclic")
        for name in ready:
            compiled[name] = _expand(definitions[name], compiled)
            remaining.remove(name)

    schemas: dict[str, Any] = {}
    owners: dict[str, str] = {}
    used_definitions = set().union(*graph.values())
    for view in order:
        entry = views[view]
        if type(entry) is not dict or set(entry) != {"owner_subject_kind", "schema"}:
            raise IndependentError("cold view entry is malformed")
        owner = entry["owner_subject_kind"]
        if owner != EXPECTED_OWNERS[view]:
            raise IndependentError("cold view owner was substituted")
        dependencies, compiler_uses, law_uses, count, depth = _inspect(
            entry["schema"],
            definitions,
            set(compilers),
            set(laws),
            set(profiles),
            source["maximum_sequence_length"],
            source["maximum_schema_depth"],
        )
        used_definitions |= dependencies
        used_compilers |= compiler_uses
        used_laws |= law_uses
        nodes += count
        maximum_depth = max(maximum_depth, depth)
        schemas[view] = _expand(entry["schema"], compiled)
        owners[view] = owner
    if set(definitions) != used_definitions:
        raise IndependentError("cold source contains an unused definition")
    if set(compilers) != used_compilers or set(laws) != used_laws:
        raise IndependentError("cold source contains an unused compiler or law")
    if nodes > source["maximum_schema_nodes"]:
        raise IndependentError("cold source crossed its node bound")
    return schemas, owners, {
        "definition_count": len(definitions),
        "source_node_count": nodes,
        "maximum_source_depth": maximum_depth,
    }


def _hex(value: Any) -> None:
    if type(value) is not str or not value or len(value) % 2:
        raise IndependentError("cold body is not even nonempty hexadecimal")
    try:
        decoded = bytes.fromhex(value)
    except ValueError as error:
        raise IndependentError("cold body is not hexadecimal") from error
    if decoded.hex() != value:
        raise IndependentError("cold body is not canonical hexadecimal")


def validate(schema: dict[str, Any], value: Any, profiles: dict[str, Any]) -> None:
    work: list[tuple[dict[str, Any], Any]] = [(schema, value)]
    while work:
        node, current = work.pop()
        kind = node.get("node")
        if kind == "atom":
            atom = node["atom"]
            atom_kind = atom["kind"]
            if atom_kind == "unit":
                if current is not None:
                    raise IndependentError("cold unit is inhabited")
            elif atom_kind == "natural":
                if type(current) is not int or not 0 <= current <= atom["max"]:
                    raise IndependentError("cold natural crossed its bound")
            elif atom_kind == "meta-boolean":
                if type(current) is not bool:
                    raise IndependentError("cold Boolean has another type")
            elif atom_kind == "canonical-body":
                if type(current) is not dict or set(current) != {"compiler", "body"}:
                    raise IndependentError("cold body has another shape")
                if current["compiler"] != atom["compiler"]:
                    raise IndependentError("cold body compiler was substituted")
                _hex(current["body"])
            elif atom_kind == "exact-profile-law":
                expected = {
                    "profile": profiles[atom["profile"]]["profile_digest"],
                    "kind": "pir.semantic-law",
                    "name": atom["law"].split(":", 1)[1],
                }
                if current != expected:
                    raise IndependentError("cold owner law was substituted")
            else:  # pragma: no cover - compiler excludes this path
                raise IndependentError("cold validator reached an unknown atom")
        elif kind == "record":
            expected = [ordinal for ordinal, _child in node["fields"]]
            if type(current) is not dict or list(current) != expected:
                raise IndependentError("cold record has another field set or order")
            work.extend(
                (child, current[ordinal])
                for ordinal, child in reversed(node["fields"])
            )
        elif kind == "variant":
            if type(current) is not dict or set(current) != {"case", "value"}:
                raise IndependentError("cold variant has another shape")
            matches = [
                child
                for ordinal, child in node["cases"]
                if ordinal == current["case"]
            ]
            if len(matches) != 1:
                raise IndependentError("cold variant selected an absent case")
            work.append((matches[0], current["value"]))
        elif kind == "sequence":
            if (
                type(current) is not list
                or not node["min"] <= len(current) <= node["max"]
            ):
                raise IndependentError("cold sequence crossed its interval")
            if node["discipline"] == "sorted-unique":
                encodings = [wire(item) for item in current]
                if any(left >= right for left, right in zip(encodings, encodings[1:])):
                    raise IndependentError("cold sorted sequence is not strict")
            work.extend((node["element"], item) for item in reversed(current))
        else:
            raise IndependentError("cold validator reached an unknown node")


def validate_view(
    family: str,
    view: str,
    schemas: dict[str, Any],
    value: Any,
    profiles: dict[str, Any],
) -> None:
    """Cold family discriminator before iterative value validation."""

    if family not in {"canonical-framed", "duplex-sponge"}:
        raise IndependentError("cold FS view family is unknown")
    if view not in schemas or VIEW_FAMILIES.get(view) != family:
        raise IndependentError("cold view kind belongs to another FS family")
    validate(schemas[view], value, profiles)


def compile_current() -> tuple[dict[str, Any], dict[str, str], dict[str, int]]:
    return compile_source(load_source())
