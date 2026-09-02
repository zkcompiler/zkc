"""Iterative clean-room observer for the bounded F0-V2A schema candidate."""

from __future__ import annotations

import copy
import hashlib
import json
from typing import Any


class ColdError(ValueError):
    """The cold path rejects the candidate."""


VIEW_ORDER = (
    "public-binding-view-v0",
    "strategy-decision-view-v0",
    "public-coin-view-v0",
    "effect-view-v0",
    "claim-reduction-view-v0",
    "execution-view-v0",
)

KNOWN_COMPILERS = {
    "binding-ref-body-v0",
    "challenge-ref-body-v0",
    "claim-ref-body-v0",
    "core-id-body-v0",
    "decision-ref-body-v0",
    "execution-resolver-body-v0",
    "guard-body-v0",
    "module-message-body-v0",
    "protocol-declaration-ref-body-v0",
    "protocol-id-body-v0",
    "reduction-ref-body-v0",
    "run-record-schema-body-v0",
    "scope-ref-body-v0",
    "terminal-ref-body-v0",
    "value-domain-ref-body-v0",
    "value-ref-body-v0",
    "value-type-body-v0",
}

KNOWN_LAWS = {
    "core-admission-v0",
    "execution-and-replay-v0",
    "run-view-issuance-v0",
}


def _wire(value: Any) -> bytes:
    return json.dumps(
        value, ensure_ascii=True, separators=(",", ":"), sort_keys=True
    ).encode("ascii")


def _hash(value: Any) -> str:
    return hashlib.sha256(_wire(value)).hexdigest()


def _audit(root: Any) -> tuple[set[str], set[str]]:
    atoms: set[str] = set()
    structures: set[str] = set()
    stack: list[tuple[Any, int]] = [(root, 0)]
    seen_nodes = 0
    while stack:
        node, depth = stack.pop()
        seen_nodes += 1
        if seen_nodes > 16384 or depth > 48:
            raise ColdError("description exceeds its finite-tree envelope")
        if not isinstance(node, dict):
            raise ColdError("description node is not a record")
        tag = node.get("node")
        if tag == "atom":
            if set(node) != {"node", "atom"} or not isinstance(node["atom"], dict):
                raise ColdError("atom node has an alternate carrier")
            descriptor = node["atom"]
            atom_tag = descriptor.get("kind")
            atoms.add(atom_tag)
            if atom_tag in {
                "unit",
                "meta-boolean",
                "canonical-value",
                "admitted-module-effect",
            }:
                if set(descriptor) != {"kind"}:
                    raise ColdError("parameter-free atom has extra material")
            elif atom_tag in {"natural", "meta-symbol", "bytes"}:
                if set(descriptor) != {"kind", "max"}:
                    raise ColdError("bounded atom has the wrong carrier")
                maximum = descriptor["max"]
                cap = {
                    "natural": (1 << 256) - 1,
                    "meta-symbol": 4096,
                    "bytes": 1 << 20,
                }[atom_tag]
                if type(maximum) is not int or maximum < 0 or maximum > cap:
                    raise ColdError("bounded atom exceeds its constitution")
            elif atom_tag == "canonical-body":
                if set(descriptor) != {"kind", "compiler"}:
                    raise ColdError("canonical-body atom has the wrong carrier")
                if descriptor["compiler"] not in KNOWN_COMPILERS:
                    raise ColdError(
                        "canonical-body compiler is not in the closed catalog"
                    )
            elif atom_tag == "exact-profile-law":
                if set(descriptor) != {"kind", "law"}:
                    raise ColdError("law atom has the wrong carrier")
                if descriptor["law"] not in KNOWN_LAWS:
                    raise ColdError("law atom is not in the closed catalog")
            else:
                raise ColdError("description contains an unknown atom")
            continue
        if tag in {"record", "variant"}:
            member_key = "fields" if tag == "record" else "cases"
            if set(node) != {"node", member_key}:
                raise ColdError("aggregate description has extra material")
            members = node[member_key]
            if not isinstance(members, list) or len(members) == 0:
                raise ColdError("aggregate description is empty or malformed")
            ordinals: list[int] = []
            children: list[Any] = []
            for pair in members:
                if not isinstance(pair, list) or len(pair) != 2:
                    raise ColdError("aggregate member is not an ordinal/schema pair")
                ordinal, child = pair
                if type(ordinal) is not int or ordinal < 0 or ordinal >= 1 << 64:
                    raise ColdError("aggregate member ordinal is invalid")
                ordinals.append(ordinal)
                children.append(child)
            if ordinals != sorted(set(ordinals)):
                raise ColdError(
                    "aggregate member ordinals are not strict canonical order"
                )
            structures.add(tag)
            stack.extend((child, depth + 1) for child in reversed(children))
            continue
        if tag == "sequence":
            if set(node) != {"node", "element", "max"}:
                raise ColdError("sequence description has extra material")
            maximum = node["max"]
            if type(maximum) is not int or maximum < 0 or maximum > 16384:
                raise ColdError("sequence description has an invalid maximum")
            structures.add(tag)
            stack.append((node["element"], depth + 1))
            continue
        raise ColdError("description contains reflection or an unknown node")
    return atoms, structures


def _make_boundary(descriptor: dict[str, Any], value: Any) -> dict[str, Any]:
    atom_tag = descriptor["kind"]
    if atom_tag == "unit":
        if value is not None:
            raise ColdError("unit leaf has data")
        return {"kind": "unit"}
    if atom_tag == "natural":
        if type(value) is not int or value < 0 or value > descriptor["max"]:
            raise ColdError("natural leaf violates its exact maximum")
        return {"kind": "natural", "max": descriptor["max"]}
    if atom_tag == "meta-boolean":
        if type(value) is not bool:
            raise ColdError("Boolean leaf is not exactly Boolean")
        return {"kind": "meta-boolean"}
    if atom_tag == "meta-symbol":
        if type(value) is not str or value == "":
            raise ColdError("symbol leaf is empty or nontext")
        if len(value.encode("utf-8")) > descriptor["max"]:
            raise ColdError("symbol leaf exceeds its exact maximum")
        return {"kind": "meta-symbol", "max": descriptor["max"]}
    if atom_tag == "bytes":
        if type(value) is not str or len(value) % 2 != 0:
            raise ColdError("byte leaf is not lowercase even-length hex")
        try:
            decoded = bytes.fromhex(value)
        except ValueError as error:
            raise ColdError("byte leaf has a nonhex digit") from error
        if value != value.lower() or len(decoded) > descriptor["max"]:
            raise ColdError("byte leaf is noncanonical or too large")
        return {"kind": "bytes", "max": descriptor["max"]}
    if atom_tag == "canonical-body":
        if not isinstance(value, dict) or set(value) != {"compiler", "body", "valid"}:
            raise ColdError("canonical body leaf has the wrong record")
        if (
            value["compiler"] != descriptor["compiler"]
            or not isinstance(value["body"], str)
            or value["valid"] is not True
        ):
            raise ColdError("canonical body leaf fails its selected compiler")
        return {"kind": "canonical-body", "compiler": descriptor["compiler"]}
    if atom_tag == "canonical-value":
        if not isinstance(value, dict) or set(value) != {"type", "datum", "admitted"}:
            raise ColdError("canonical-value leaf has the wrong record")
        typed = value["type"]
        if value["admitted"] is not True or not isinstance(typed, dict):
            raise ColdError("canonical-value leaf lacks admission")
        if (
            typed.get("compiler") != "value-type-body-v0"
            or typed.get("valid") is not True
            or not isinstance(typed.get("body"), str)
        ):
            raise ColdError("canonical-value leaf lacks an exact admitted type")
        return {"kind": "canonical-value", "value_type_body": typed["body"]}
    if atom_tag == "exact-profile-law":
        if not isinstance(value, dict) or set(value) != {"profile", "kind", "name"}:
            raise ColdError("law leaf has the wrong reference record")
        if value["kind"] != "pir.semantic-law" or value["name"] != descriptor["law"]:
            raise ColdError("law leaf does not equal the schema-fixed declaration")
        return {"kind": "exact-profile-law", "law": descriptor["law"]}
    if atom_tag == "admitted-module-effect":
        required = {
            "module",
            "declaration",
            "payload",
            "supported",
            "payload_valid",
        }
        if not isinstance(value, dict) or set(value) != required:
            raise ColdError("module-effect leaf has the wrong carrier")
        declaration = value["declaration"]
        if not isinstance(declaration, dict) or set(declaration) != {
            "module",
            "kind",
            "ordinal",
        }:
            raise ColdError("module-effect declaration is malformed")
        if declaration["module"] != value["module"]:
            raise ColdError("module-effect owner and declaration diverge")
        if declaration["kind"] != "pir.core-effect":
            raise ColdError("module-effect declaration has the wrong kind")
        if type(declaration["ordinal"]) is not int or declaration["ordinal"] < 0:
            raise ColdError("module-effect declaration ordinal is malformed")
        if value["supported"] is not True:
            raise ColdError("module-effect semantics are not supported")
        if value["payload_valid"] is not True:
            raise ColdError("module-effect payload does not pass its owner schema")
        return {
            "kind": "admitted-module-effect",
            "module": value["module"],
            "declaration_kind": "pir.core-effect",
            "declaration_ordinal": declaration["ordinal"],
        }
    raise ColdError("cold boundary constructor received an unknown atom")


def _field_step(ordinal: int) -> dict[str, Any]:
    return {"step": "field", "ordinal": ordinal}


def _variant_step(ordinal: int) -> dict[str, Any]:
    return {"step": "variant", "ordinal": ordinal}


def _sequence_step(ordinal: int) -> dict[str, Any]:
    return {"step": "sequence", "ordinal": ordinal}


def _leaves(view: str, root_schema: Any, root_value: Any) -> list[dict[str, Any]]:
    # Stack entries are pushed in reverse canonical order. Unlike the reference
    # implementation, this never recursively calls the walker.
    pending: list[tuple[Any, Any, list[dict[str, Any]]]] = [
        (root_schema, root_value, [])
    ]
    leaves: list[dict[str, Any]] = []
    while pending:
        schema, value, path = pending.pop()
        tag = schema.get("node") if isinstance(schema, dict) else None
        if tag == "atom":
            if len(path) == 0:
                raise ColdError("root atom would have an empty field path")
            leaves.append(
                {
                    "coordinate": {
                        "view": view,
                        "path": copy.deepcopy(path),
                        "boundary": _make_boundary(schema["atom"], value),
                    },
                    "value": copy.deepcopy(value),
                }
            )
            continue
        if tag == "record":
            if not isinstance(value, dict):
                raise ColdError("record schema is paired with a nonrecord value")
            members = schema["fields"]
            expected = [pair[0] for pair in members]
            if list(value.keys()) != expected:
                raise ColdError(
                    "record value does not have the exact ordered field set"
                )
            for ordinal, child in reversed(members):
                pending.append((child, value[ordinal], [*path, _field_step(ordinal)]))
            continue
        if tag == "variant":
            if not isinstance(value, dict) or set(value) != {"case", "value"}:
                raise ColdError("variant schema is paired with a malformed value")
            selected = value["case"]
            if type(selected) is not int:
                raise ColdError("variant selector is not an ordinal")
            matches = [
                child for ordinal, child in schema["cases"] if ordinal == selected
            ]
            if len(matches) != 1:
                raise ColdError("variant value selects no exact case")
            pending.append(
                (matches[0], value["value"], [*path, _variant_step(selected)])
            )
            continue
        if tag == "sequence":
            if not isinstance(value, list) or len(value) > schema["max"]:
                raise ColdError("sequence value exceeds or violates its schema")
            for ordinal in range(len(value) - 1, -1, -1):
                pending.append(
                    (
                        schema["element"],
                        value[ordinal],
                        [*path, _sequence_step(ordinal)],
                    )
                )
            continue
        raise ColdError("cold walker encountered an unknown schema tag")
    return leaves


def _resolve(view: str, root_schema: Any, root_value: Any, coordinate: Any) -> Any:
    if not isinstance(coordinate, dict) or set(coordinate) != {
        "view",
        "path",
        "boundary",
    }:
        raise ColdError("coordinate does not have its exact three fields")
    if coordinate["view"] != view:
        raise ColdError("coordinate view does not equal the selected schema")
    path = coordinate["path"]
    if not isinstance(path, list) or len(path) == 0:
        raise ColdError("coordinate path is empty or not a sequence")
    schema = root_schema
    value = root_value
    for position, raw_step in enumerate(path):
        if not isinstance(raw_step, dict) or set(raw_step) != {"step", "ordinal"}:
            raise ColdError("coordinate step is malformed")
        operation = raw_step["step"]
        ordinal = raw_step["ordinal"]
        if type(ordinal) is not int or ordinal < 0:
            raise ColdError("coordinate ordinal is malformed")
        schema_tag = schema.get("node") if isinstance(schema, dict) else None
        if schema_tag == "record" and operation == "field":
            chosen = [child for key, child in schema["fields"] if key == ordinal]
            if len(chosen) != 1 or not isinstance(value, dict) or ordinal not in value:
                raise ColdError("coordinate record field does not exist")
            schema = chosen[0]
            value = value[ordinal]
        elif schema_tag == "variant" and operation == "variant":
            if (
                not isinstance(value, dict)
                or set(value) != {"case", "value"}
                or value["case"] != ordinal
            ):
                raise ColdError("coordinate variant arm is not active")
            chosen = [child for key, child in schema["cases"] if key == ordinal]
            if len(chosen) != 1:
                raise ColdError("coordinate variant arm is not declared")
            schema = chosen[0]
            value = value["value"]
        elif schema_tag == "sequence" and operation == "sequence":
            if not isinstance(value, list) or ordinal >= len(value):
                raise ColdError("coordinate sequence element is absent")
            schema = schema["element"]
            value = value[ordinal]
        else:
            raise ColdError("coordinate operation disagrees with schema node")
        if schema.get("node") == "atom" and position + 1 != len(path):
            raise ColdError("coordinate descends past an atom")
    if schema.get("node") != "atom":
        raise ColdError("coordinate stops before an atom")
    if coordinate["boundary"] != _make_boundary(schema["atom"], value):
        raise ColdError("coordinate boundary does not equal the instantiated atom")
    return copy.deepcopy(value)


def _sort_key(coordinate: Any) -> tuple[Any, ...]:
    if not isinstance(coordinate, dict):
        raise ColdError("manifest member is not a coordinate")
    order = {"field": 0, "variant": 1, "sequence": 2}
    result: list[tuple[int, int]] = []
    for step in coordinate.get("path", []):
        if not isinstance(step, dict) or set(step) != {"step", "ordinal"}:
            raise ColdError("manifest coordinate step is malformed")
        if step["step"] not in order or type(step["ordinal"]) is not int:
            raise ColdError("manifest coordinate step is unknown")
        result.append((order[step["step"]], step["ordinal"]))
    return coordinate.get("view"), tuple(result), _wire(coordinate.get("boundary"))


def _check_manifest(
    view: str,
    schema: Any,
    value: Any,
    supplied: Any,
    expected: list[dict[str, Any]],
) -> None:
    if not isinstance(supplied, list) or len(supplied) == 0:
        raise ColdError("complete manifest is not a nonempty sequence")
    for coordinate in supplied:
        _resolve(view, schema, value, coordinate)
    keys = [_sort_key(coordinate) for coordinate in supplied]
    if keys != sorted(keys) or len(keys) != len(set(keys)):
        raise ColdError("manifest is not canonical sorted-unique")
    if supplied != expected:
        raise ColdError("manifest is not the exact active atomic-leaf set")


def observe(candidate: object) -> dict[str, Any]:
    if not isinstance(candidate, dict) or set(candidate) != {
        "schemas",
        "values",
        "catalog",
        "requested_manifests",
    }:
        raise ColdError("candidate outer record differs from the contract")
    schemas = candidate["schemas"]
    values = candidate["values"]
    catalog = candidate["catalog"]
    manifests = candidate["requested_manifests"]
    for component in (schemas, values, catalog, manifests):
        if not isinstance(component, dict) or tuple(component.keys()) != VIEW_ORDER:
            raise ColdError("candidate catalog does not have the exact view order")

    atom_union: set[str] = set()
    structure_union: set[str] = set()
    evidence_by_view: dict[str, Any] = {}
    flattened: list[dict[str, Any]] = []
    for view in VIEW_ORDER:
        atoms, structures = _audit(schemas[view])
        atom_union |= atoms
        structure_union |= structures
        schema_hash = _hash(schemas[view])
        if catalog[view] != {"schema_digest": schema_hash}:
            raise ColdError("schema does not match its catalog-authenticated digest")
        leaves = _leaves(view, schemas[view], values[view])
        expected_manifest = [leaf["coordinate"] for leaf in leaves]
        _check_manifest(
            view,
            schemas[view],
            values[view],
            manifests[view],
            expected_manifest,
        )
        for leaf in leaves:
            if (
                _resolve(view, schemas[view], values[view], leaf["coordinate"])
                != leaf["value"]
            ):
                raise ColdError("cold resolver does not invert cold enumeration")
        evidence_by_view[view] = {
            "schema_digest": schema_hash,
            "leaf_count": len(leaves),
            "manifest_digest": _hash(expected_manifest),
        }
        flattened.extend(leaves)

    module_leaves = [
        leaf
        for leaf in flattened
        if leaf["coordinate"]["boundary"].get("kind") == "admitted-module-effect"
    ]
    if len(module_leaves) != 1:
        raise ColdError("fixture does not contain one exact module-effect atom")
    nested_payload = module_leaves[0]["value"]["payload"]
    if any(leaf["value"] == nested_payload for leaf in flattened):
        raise ColdError("generic enumeration reflected into module-owned payload")

    repeated = []
    for leaf in flattened:
        value = leaf["value"]
        if (
            leaf["coordinate"]["view"] == "public-coin-view-v0"
            and isinstance(value, dict)
            and value.get("compiler") == "value-ref-body-v0"
            and value.get("body") == "public-input:0"
            and value.get("valid") is True
        ):
            repeated.append(leaf)
    if len(repeated) != 3:
        raise ColdError("equal-content coordinate pressure count drifted")
    if len({_hash(leaf["coordinate"]) for leaf in repeated}) != 3:
        raise ColdError("equal-content leaves were aliased by coordinate")

    return {
        "views": evidence_by_view,
        "structural_nodes": sorted(structure_union),
        "atom_kinds": sorted(atom_union),
        "total_leaf_count": len(flattened),
        "opaque_module_effect_coordinate": module_leaves[0]["coordinate"],
        "equal_value_distinct_coordinate_count": len(repeated),
    }
