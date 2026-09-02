"""Recursive reference model for the bounded F0-V2A view-schema gate."""

from __future__ import annotations

import copy
import hashlib
import json
from typing import Any


class SchemaError(ValueError):
    """The candidate schema, value, coordinate, or manifest does not form."""


VIEW_ORDER = (
    "public-binding-view-v0",
    "strategy-decision-view-v0",
    "public-coin-view-v0",
    "effect-view-v0",
    "claim-reduction-view-v0",
    "execution-view-v0",
)

LEAF_COMPILERS = frozenset(
    {
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
)

LAW_REFS = frozenset(
    {
        "core-admission-v0",
        "execution-and-replay-v0",
        "run-view-issuance-v0",
    }
)

MAX_SCHEMA_DEPTH = 48
MAX_SCHEMA_NODES = 1 << 14
MAX_SEQUENCE_LENGTH = 1 << 14
MAX_NATURAL = (1 << 256) - 1
MAX_TEXT_BYTES = 4096
MAX_BYTES = 1 << 20


def _atom(kind: str, **parameters: Any) -> dict[str, Any]:
    return {"node": "atom", "atom": {"kind": kind, **parameters}}


def _record(*fields: tuple[int, dict[str, Any]]) -> dict[str, Any]:
    return {
        "node": "record",
        "fields": [[ordinal, schema] for ordinal, schema in fields],
    }


def _variant(*cases: tuple[int, dict[str, Any]]) -> dict[str, Any]:
    return {
        "node": "variant",
        "cases": [[ordinal, schema] for ordinal, schema in cases],
    }


def _sequence(element: dict[str, Any], maximum: int) -> dict[str, Any]:
    return {"node": "sequence", "element": element, "max": maximum}


def _body(compiler: str) -> dict[str, Any]:
    return _atom("canonical-body", compiler=compiler)


def _law(name: str) -> dict[str, Any]:
    return _atom("exact-profile-law", law=name)


def _unit_variant() -> dict[str, Any]:
    return _variant((0, _atom("unit")), (1, _body("scope-ref-body-v0")))


def _schemas() -> dict[str, dict[str, Any]]:
    public_binding = _record(
        (0, _body("core-id-body-v0")),
        (
            1,
            _sequence(
                _record(
                    (0, _body("scope-ref-body-v0")),
                    (1, _unit_variant()),
                    (2, _atom("bytes", max=32)),
                ),
                8,
            ),
        ),
        (
            2,
            _sequence(
                _record(
                    (0, _body("binding-ref-body-v0")),
                    (1, _body("value-ref-body-v0")),
                    (2, _body("value-type-body-v0")),
                    (
                        3,
                        _variant(
                            (0, _atom("unit")),
                            (1, _atom("unit")),
                            (2, _atom("unit")),
                            (3, _atom("unit")),
                        ),
                    ),
                    (4, _atom("canonical-value")),
                ),
                16,
            ),
        ),
    )

    strategy = _record(
        (0, _body("core-id-body-v0")),
        (
            1,
            _sequence(
                _record(
                    (0, _body("decision-ref-body-v0")),
                    (1, _body("guard-body-v0")),
                    (2, _body("value-type-body-v0")),
                    (3, _sequence(_body("decision-ref-body-v0"), 8)),
                ),
                8,
            ),
        ),
        (2, _law("core-admission-v0")),
        (
            3,
            _sequence(
                _record(
                    (0, _body("decision-ref-body-v0")),
                    (1, _body("value-type-body-v0")),
                ),
                8,
            ),
        ),
    )

    public_coin = _record(
        (0, _body("core-id-body-v0")),
        (1, _atom("meta-boolean")),
        (2, _sequence(_body("value-ref-body-v0"), 4)),
        (
            3,
            _sequence(
                _record(
                    (0, _body("challenge-ref-body-v0")),
                    (1, _body("value-type-body-v0")),
                    (2, _body("value-domain-ref-body-v0")),
                    (3, _body("protocol-declaration-ref-body-v0")),
                    (4, _sequence(_body("value-ref-body-v0"), 8)),
                ),
                8,
            ),
        ),
    )

    effect = _record(
        (0, _body("core-id-body-v0")),
        (
            1,
            _sequence(
                _record(
                    (0, _body("scope-ref-body-v0")),
                    (1, _body("guard-body-v0")),
                    (
                        2,
                        _variant(
                            (0, _body("module-message-body-v0")),
                            (1, _atom("admitted-module-effect")),
                        ),
                    ),
                    (3, _sequence(_body("value-type-body-v0"), 8)),
                ),
                16,
            ),
        ),
        (2, _sequence(_body("terminal-ref-body-v0"), 16)),
    )

    claim_reduction = _record(
        (0, _body("core-id-body-v0")),
        (
            1,
            _sequence(
                _record(
                    (0, _body("claim-ref-body-v0")),
                    (1, _atom("meta-symbol", max=64)),
                    (2, _body("value-ref-body-v0")),
                ),
                16,
            ),
        ),
        (
            2,
            _sequence(
                _record(
                    (0, _body("reduction-ref-body-v0")),
                    (1, _sequence(_body("claim-ref-body-v0"), 8)),
                    (2, _atom("natural", max=255)),
                ),
                16,
            ),
        ),
        (
            3,
            _sequence(
                _record(
                    (0, _body("terminal-ref-body-v0")),
                    (1, _body("claim-ref-body-v0")),
                    (2, _variant((0, _atom("unit")), (1, _atom("unit")))),
                ),
                16,
            ),
        ),
    )

    execution = _record(
        (0, _body("protocol-id-body-v0")),
        (1, _body("core-id-body-v0")),
        (
            2,
            _variant(
                (0, _atom("unit")),
                (1, _atom("bytes", max=64)),
            ),
        ),
        (3, _law("execution-and-replay-v0")),
        (4, _body("execution-resolver-body-v0")),
        (5, _body("run-record-schema-body-v0")),
        (6, _law("execution-and-replay-v0")),
        (7, _law("run-view-issuance-v0")),
    )

    return dict(
        zip(
            VIEW_ORDER,
            (
                public_binding,
                strategy,
                public_coin,
                effect,
                claim_reduction,
                execution,
            ),
            strict=True,
        )
    )


def _canonical_body(compiler: str, body: str) -> dict[str, Any]:
    return {"compiler": compiler, "body": body, "valid": True}


def _profile_law(name: str) -> dict[str, Any]:
    return {
        "profile": "interaction-v0-fixture",
        "kind": "pir.semantic-law",
        "name": name,
    }


def _canonical_value(type_name: str, datum: Any) -> dict[str, Any]:
    return {
        "type": _canonical_body("value-type-body-v0", type_name),
        "datum": datum,
        "admitted": True,
    }


def _module_effect() -> dict[str, Any]:
    return {
        "module": "module:imported-verification-v0",
        "declaration": {
            "module": "module:imported-verification-v0",
            "kind": "pir.core-effect",
            "ordinal": 0,
        },
        "payload": {
            "verifier": "semantic-verifier:fixture",
            "proof_input": [7, 11, 13],
        },
        "supported": True,
        "payload_valid": True,
    }


def _values() -> dict[str, dict[int, Any]]:
    core = _canonical_body("core-id-body-v0", "core:finite-schnorr-fixture")
    value_type = _canonical_body("value-type-body-v0", "scalar:z3")
    equal_value_ref = _canonical_body("value-ref-body-v0", "public-input:0")

    return {
        "public-binding-view-v0": {
            0: core,
            1: [
                {
                    0: _canonical_body("scope-ref-body-v0", "scope:0"),
                    1: {"case": 0, "value": None},
                    2: "00ff",
                },
                {
                    0: _canonical_body("scope-ref-body-v0", "scope:1"),
                    1: {
                        "case": 1,
                        "value": _canonical_body("scope-ref-body-v0", "scope:0"),
                    },
                    2: "0102",
                },
            ],
            2: [
                {
                    0: _canonical_body("binding-ref-body-v0", "binding:0"),
                    1: equal_value_ref,
                    2: value_type,
                    3: {"case": 0, "value": None},
                    4: _canonical_value("scalar:z3", 2),
                }
            ],
        },
        "strategy-decision-view-v0": {
            0: core,
            1: [
                {
                    0: _canonical_body("decision-ref-body-v0", "decision:0"),
                    1: _canonical_body("guard-body-v0", "guard:always"),
                    2: value_type,
                    3: [],
                }
            ],
            2: _profile_law("core-admission-v0"),
            3: [
                {
                    0: _canonical_body("decision-ref-body-v0", "decision:0"),
                    1: value_type,
                }
            ],
        },
        "public-coin-view-v0": {
            0: core,
            1: True,
            2: [equal_value_ref, copy.deepcopy(equal_value_ref)],
            3: [
                {
                    0: _canonical_body("challenge-ref-body-v0", "challenge:0"),
                    1: value_type,
                    2: _canonical_body("value-domain-ref-body-v0", "domain:z3"),
                    3: _canonical_body(
                        "protocol-declaration-ref-body-v0", "public-coin-law:0"
                    ),
                    4: [equal_value_ref],
                }
            ],
        },
        "effect-view-v0": {
            0: core,
            1: [
                {
                    0: _canonical_body("scope-ref-body-v0", "scope:1"),
                    1: _canonical_body("guard-body-v0", "guard:always"),
                    2: {"case": 1, "value": _module_effect()},
                    3: [value_type],
                }
            ],
            2: [_canonical_body("terminal-ref-body-v0", "terminal:0")],
        },
        "claim-reduction-view-v0": {
            0: core,
            1: [
                {
                    0: _canonical_body("claim-ref-body-v0", "claim:0"),
                    1: "acceptance",
                    2: equal_value_ref,
                }
            ],
            2: [
                {
                    0: _canonical_body("reduction-ref-body-v0", "reduction:0"),
                    1: [_canonical_body("claim-ref-body-v0", "claim:0")],
                    2: 1,
                }
            ],
            3: [
                {
                    0: _canonical_body("terminal-ref-body-v0", "terminal:0"),
                    1: _canonical_body("claim-ref-body-v0", "claim:0"),
                    2: {"case": 0, "value": None},
                }
            ],
        },
        "execution-view-v0": {
            0: _canonical_body("protocol-id-body-v0", "protocol:fresh-fixture"),
            1: core,
            2: {"case": 0, "value": None},
            3: _profile_law("execution-and-replay-v0"),
            4: _canonical_body(
                "execution-resolver-body-v0", "resolver:finite-schedule"
            ),
            5: _canonical_body("run-record-schema-body-v0", "run-record:v0"),
            6: _profile_law("execution-and-replay-v0"),
            7: _profile_law("run-view-issuance-v0"),
        },
    }


def _canonical_json(value: Any) -> bytes:
    return json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=True
    ).encode("ascii")


def _digest(value: Any) -> str:
    return hashlib.sha256(_canonical_json(value)).hexdigest()


def _schema_audit(schema: Any) -> tuple[frozenset[str], frozenset[str]]:
    atoms: set[str] = set()
    structures: set[str] = set()
    nodes = 0

    def walk(node: Any, depth: int) -> None:
        nonlocal nodes
        nodes += 1
        if nodes > MAX_SCHEMA_NODES or depth > MAX_SCHEMA_DEPTH:
            raise SchemaError("schema constitutional bound exceeded")
        if type(node) is not dict or set(node) not in (
            {"node", "atom"},
            {"node", "fields"},
            {"node", "cases"},
            {"node", "element", "max"},
        ):
            raise SchemaError("unknown or noncanonical schema node")
        kind = node.get("node")
        if kind == "atom":
            atom = node["atom"]
            if type(atom) is not dict or type(atom.get("kind")) is not str:
                raise SchemaError("malformed atom schema")
            atom_kind = atom["kind"]
            atoms.add(atom_kind)
            expected_keys: set[str]
            if atom_kind == "unit" or atom_kind in {
                "meta-boolean",
                "canonical-value",
                "admitted-module-effect",
            }:
                expected_keys = {"kind"}
            elif atom_kind in {"natural", "meta-symbol", "bytes"}:
                expected_keys = {"kind", "max"}
                maximum = atom.get("max")
                limit = {
                    "natural": MAX_NATURAL,
                    "meta-symbol": MAX_TEXT_BYTES,
                    "bytes": MAX_BYTES,
                }[atom_kind]
                if type(maximum) is not int or not 0 <= maximum <= limit:
                    raise SchemaError("invalid atom bound")
            elif atom_kind == "canonical-body":
                expected_keys = {"kind", "compiler"}
                if atom.get("compiler") not in LEAF_COMPILERS:
                    raise SchemaError("unknown leaf body compiler")
            elif atom_kind == "exact-profile-law":
                expected_keys = {"kind", "law"}
                if atom.get("law") not in LAW_REFS:
                    raise SchemaError("unknown exact profile law")
            else:
                raise SchemaError("unknown atom kind")
            if set(atom) != expected_keys:
                raise SchemaError("noncanonical atom schema")
            return
        if kind in {"record", "variant"}:
            structures.add(kind)
            key = "fields" if kind == "record" else "cases"
            entries = node[key]
            if type(entries) is not list or not entries:
                raise SchemaError(f"{kind} must be a nonempty sequence")
            previous = -1
            for entry in entries:
                if type(entry) is not list or len(entry) != 2:
                    raise SchemaError(f"malformed {kind} entry")
                ordinal, child = entry
                if type(ordinal) is not int or not 0 <= ordinal < 1 << 64:
                    raise SchemaError(f"invalid {kind} ordinal")
                if ordinal <= previous:
                    raise SchemaError(f"noncanonical {kind} ordinal order")
                previous = ordinal
                walk(child, depth + 1)
            return
        if kind == "sequence":
            structures.add(kind)
            maximum = node["max"]
            if type(maximum) is not int or not 0 <= maximum <= MAX_SEQUENCE_LENGTH:
                raise SchemaError("invalid sequence maximum")
            walk(node["element"], depth + 1)
            return
        raise SchemaError("unknown schema constructor")

    walk(schema, 0)
    return frozenset(atoms), frozenset(structures)


def _step(kind: str, ordinal: int) -> dict[str, Any]:
    return {"step": kind, "ordinal": ordinal}


def _boundary(atom: dict[str, Any], value: Any) -> dict[str, Any]:
    kind = atom["kind"]
    if kind == "unit":
        if value is not None:
            raise SchemaError("unit atom has a non-unit value")
        return {"kind": "unit"}
    if kind == "natural":
        if type(value) is not int or not 0 <= value <= atom["max"]:
            raise SchemaError("natural atom is outside its exact bound")
        return {"kind": "natural", "max": atom["max"]}
    if kind == "meta-boolean":
        if type(value) is not bool:
            raise SchemaError("MetaBoolean atom is not a Boolean")
        return {"kind": "meta-boolean"}
    if kind == "meta-symbol":
        if (
            type(value) is not str
            or not value
            or len(value.encode("utf-8")) > atom["max"]
        ):
            raise SchemaError("MetaSymbol atom is malformed or out of bounds")
        return {"kind": "meta-symbol", "max": atom["max"]}
    if kind == "bytes":
        if type(value) is not str or len(value) % 2:
            raise SchemaError("Bytes atom is not canonical hexadecimal")
        try:
            bytes.fromhex(value)
        except ValueError as error:
            raise SchemaError("Bytes atom is not canonical hexadecimal") from error
        if value.lower() != value or len(value) // 2 > atom["max"]:
            raise SchemaError("Bytes atom is noncanonical or out of bounds")
        return {"kind": "bytes", "max": atom["max"]}
    if kind == "canonical-body":
        if (
            type(value) is not dict
            or set(value) != {"compiler", "body", "valid"}
            or value.get("compiler") != atom["compiler"]
            or type(value.get("body")) is not str
            or value.get("valid") is not True
        ):
            raise SchemaError("canonical body does not match its exact compiler")
        return {"kind": "canonical-body", "compiler": atom["compiler"]}
    if kind == "canonical-value":
        if (
            type(value) is not dict
            or set(value) != {"type", "datum", "admitted"}
            or value.get("admitted") is not True
        ):
            raise SchemaError("canonical value is not admitted")
        value_type = value["type"]
        if (
            type(value_type) is not dict
            or value_type.get("compiler") != "value-type-body-v0"
            or value_type.get("valid") is not True
        ):
            raise SchemaError("canonical value carries an invalid ValueType")
        return {
            "kind": "canonical-value",
            "value_type_body": value_type["body"],
        }
    if kind == "exact-profile-law":
        if (
            type(value) is not dict
            or set(value) != {"profile", "kind", "name"}
            or value.get("kind") != "pir.semantic-law"
            or value.get("name") != atom["law"]
        ):
            raise SchemaError("exact profile-law atom was substituted")
        return {"kind": "exact-profile-law", "law": atom["law"]}
    if kind == "admitted-module-effect":
        if type(value) is not dict or set(value) != {
            "module",
            "declaration",
            "payload",
            "supported",
            "payload_valid",
        }:
            raise SchemaError("module effect atom is malformed")
        declaration = value["declaration"]
        if (
            type(declaration) is not dict
            or set(declaration) != {"module", "kind", "ordinal"}
            or declaration.get("kind") != "pir.core-effect"
            or declaration.get("module") != value["module"]
            or type(declaration.get("ordinal")) is not int
            or declaration["ordinal"] < 0
        ):
            raise SchemaError("module effect declaration does not match its owner")
        if value["supported"] is not True:
            raise SchemaError("exact module effect is unsupported")
        if value["payload_valid"] is not True:
            raise SchemaError("module effect payload fails its owner schema")
        return {
            "kind": "admitted-module-effect",
            "module": value["module"],
            "declaration_kind": "pir.core-effect",
            "declaration_ordinal": declaration["ordinal"],
        }
    raise SchemaError("unknown atom during boundary formation")


def _enumerate(view: str, schema: dict[str, Any], value: Any) -> list[dict[str, Any]]:
    entries: list[dict[str, Any]] = []

    def walk(node: dict[str, Any], current: Any, path: list[dict[str, Any]]) -> None:
        kind = node["node"]
        if kind == "atom":
            if not path:
                raise SchemaError("root atom would create an empty coordinate path")
            entries.append(
                {
                    "coordinate": {
                        "view": view,
                        "path": copy.deepcopy(path),
                        "boundary": _boundary(node["atom"], current),
                    },
                    "value": copy.deepcopy(current),
                }
            )
            return
        if kind == "record":
            if type(current) is not dict:
                raise SchemaError("record value is not a record")
            expected = [entry[0] for entry in node["fields"]]
            if list(current) != expected:
                raise SchemaError("record fields are missing, extra, or noncanonical")
            for ordinal, child in node["fields"]:
                walk(child, current[ordinal], [*path, _step("field", ordinal)])
            return
        if kind == "variant":
            if type(current) is not dict or set(current) != {"case", "value"}:
                raise SchemaError("variant value is malformed")
            case = current["case"]
            if type(case) is not int:
                raise SchemaError("variant case is not an ordinal")
            matching = [child for ordinal, child in node["cases"] if ordinal == case]
            if len(matching) != 1:
                raise SchemaError("variant selects an absent case")
            walk(matching[0], current["value"], [*path, _step("variant", case)])
            return
        if kind == "sequence":
            if type(current) is not list or len(current) > node["max"]:
                raise SchemaError("sequence value is malformed or out of bounds")
            for ordinal, element in enumerate(current):
                walk(
                    node["element"],
                    element,
                    [*path, _step("sequence", ordinal)],
                )
            return
        raise SchemaError("unknown schema constructor during enumeration")

    walk(schema, value, [])
    return entries


def _coordinate_key(coordinate: dict[str, Any]) -> tuple[Any, ...]:
    step_order = {"field": 0, "variant": 1, "sequence": 2}
    path_key: list[tuple[int, int]] = []
    for step in coordinate.get("path", []):
        if type(step) is not dict or set(step) != {"step", "ordinal"}:
            raise SchemaError("coordinate has a malformed path step")
        kind = step.get("step")
        ordinal = step.get("ordinal")
        if kind not in step_order or type(ordinal) is not int or ordinal < 0:
            raise SchemaError("coordinate has an unknown path step")
        path_key.append((step_order[kind], ordinal))
    return (
        coordinate.get("view"),
        tuple(path_key),
        _canonical_json(coordinate.get("boundary")),
    )


def _resolve(
    expected_view: str,
    schema: dict[str, Any],
    value: Any,
    coordinate: dict[str, Any],
) -> Any:
    if type(coordinate) is not dict or set(coordinate) != {"view", "path", "boundary"}:
        raise SchemaError("field coordinate is malformed")
    if coordinate["view"] != expected_view:
        raise SchemaError("field coordinate belongs to another view")
    path = coordinate["path"]
    if type(path) is not list or not path:
        raise SchemaError("field coordinate path must be nonempty")
    node: Any = schema
    current = value
    for index, step in enumerate(path):
        if type(step) is not dict or set(step) != {"step", "ordinal"}:
            raise SchemaError("field coordinate has a malformed path step")
        step_kind = step["step"]
        ordinal = step["ordinal"]
        if type(ordinal) is not int or ordinal < 0:
            raise SchemaError("field coordinate has an invalid ordinal")
        node_kind = node.get("node")
        if step_kind == "field" and node_kind == "record":
            matching = [child for field, child in node["fields"] if field == ordinal]
            if (
                len(matching) != 1
                or type(current) is not dict
                or ordinal not in current
            ):
                raise SchemaError("field coordinate selects an absent record field")
            node = matching[0]
            current = current[ordinal]
        elif step_kind == "variant" and node_kind == "variant":
            if (
                type(current) is not dict
                or current.get("case") != ordinal
                or set(current) != {"case", "value"}
            ):
                raise SchemaError("field coordinate selects an inactive variant case")
            matching = [child for case, child in node["cases"] if case == ordinal]
            if len(matching) != 1:
                raise SchemaError("field coordinate selects an absent variant case")
            node = matching[0]
            current = current["value"]
        elif step_kind == "sequence" and node_kind == "sequence":
            if type(current) is not list or ordinal >= len(current):
                raise SchemaError("field coordinate selects an absent sequence element")
            node = node["element"]
            current = current[ordinal]
        else:
            raise SchemaError("path step does not match the schema constructor")
        if node.get("node") == "atom" and index != len(path) - 1:
            raise SchemaError("field coordinate continues below an atomic boundary")
    if node.get("node") != "atom":
        raise SchemaError("field coordinate ends at an interior schema node")
    expected_boundary = _boundary(node["atom"], current)
    if coordinate["boundary"] != expected_boundary:
        raise SchemaError("field coordinate carries the wrong atomic boundary")
    return copy.deepcopy(current)


def _validate_manifest(
    view: str,
    schema: dict[str, Any],
    value: Any,
    requested: Any,
    exact: list[dict[str, Any]],
) -> None:
    if type(requested) is not list or not requested:
        raise SchemaError("complete manifest must be a nonempty sequence")
    for coordinate in requested:
        _resolve(view, schema, value, coordinate)
    keys = [_coordinate_key(coordinate) for coordinate in requested]
    if keys != sorted(keys) or len(set(keys)) != len(keys):
        raise SchemaError("manifest is reordered or contains duplicate coordinates")
    if requested != exact:
        raise SchemaError("manifest is not the exact complete active-leaf set")


def build_candidate() -> dict[str, Any]:
    schemas = _schemas()
    values = _values()
    catalog = {view: {"schema_digest": _digest(schemas[view])} for view in VIEW_ORDER}
    manifests = {
        view: [
            entry["coordinate"]
            for entry in _enumerate(view, schemas[view], values[view])
        ]
        for view in VIEW_ORDER
    }
    return {
        "schemas": schemas,
        "values": values,
        "catalog": catalog,
        "requested_manifests": manifests,
    }


def observe(candidate: object) -> dict[str, Any]:
    if type(candidate) is not dict or set(candidate) != {
        "schemas",
        "values",
        "catalog",
        "requested_manifests",
    }:
        raise SchemaError("candidate has the wrong outer shape")
    schemas = candidate["schemas"]
    values = candidate["values"]
    catalog = candidate["catalog"]
    manifests = candidate["requested_manifests"]
    for table in (schemas, values, catalog, manifests):
        if type(table) is not dict or tuple(table) != VIEW_ORDER:
            raise SchemaError("candidate view catalog is incomplete or noncanonical")

    all_atoms: set[str] = set()
    all_structures: set[str] = set()
    view_evidence: dict[str, Any] = {}
    all_entries: list[dict[str, Any]] = []
    for view in VIEW_ORDER:
        atoms, structures = _schema_audit(schemas[view])
        all_atoms.update(atoms)
        all_structures.update(structures)
        schema_digest = _digest(schemas[view])
        if catalog[view] != {"schema_digest": schema_digest}:
            raise SchemaError(
                "schema changed without its authenticated catalog commitment"
            )
        entries = _enumerate(view, schemas[view], values[view])
        exact_manifest = [entry["coordinate"] for entry in entries]
        _validate_manifest(
            view,
            schemas[view],
            values[view],
            manifests[view],
            exact_manifest,
        )
        for entry in entries:
            resolved = _resolve(view, schemas[view], values[view], entry["coordinate"])
            if resolved != entry["value"]:
                raise SchemaError("enumerator and resolver disagree on a leaf value")
        view_evidence[view] = {
            "schema_digest": schema_digest,
            "leaf_count": len(entries),
            "manifest_digest": _digest(exact_manifest),
        }
        all_entries.extend(entries)

    module_entries = [
        entry
        for entry in all_entries
        if entry["coordinate"]["boundary"]["kind"] == "admitted-module-effect"
    ]
    if len(module_entries) != 1:
        raise SchemaError("fixture must expose exactly one opaque module-effect leaf")
    module_payload = module_entries[0]["value"]["payload"]
    if any(entry["value"] == module_payload for entry in all_entries):
        raise SchemaError("module payload was reflected into a separate leaf")

    repeated = [
        entry
        for entry in all_entries
        if entry["value"] == _canonical_body("value-ref-body-v0", "public-input:0")
        and entry["coordinate"]["view"] == "public-coin-view-v0"
    ]
    if len(repeated) != 3 or len({_digest(row["coordinate"]) for row in repeated}) != 3:
        raise SchemaError("equal semantic values did not retain distinct coordinates")

    return {
        "views": view_evidence,
        "structural_nodes": sorted(all_structures),
        "atom_kinds": sorted(all_atoms),
        "total_leaf_count": len(all_entries),
        "opaque_module_effect_coordinate": module_entries[0]["coordinate"],
        "equal_value_distinct_coordinate_count": len(repeated),
    }


def mutated_candidate(name: str) -> dict[str, Any]:
    candidate = copy.deepcopy(build_candidate())
    schemas = candidate["schemas"]
    values = candidate["values"]
    manifests = candidate["requested_manifests"]

    if name == "unknown-node":
        schemas[VIEW_ORDER[0]]["fields"][0][1] = {
            "node": "reflect",
            "callback": "fields",
        }
    elif name == "unsorted-fields":
        schemas[VIEW_ORDER[0]]["fields"].reverse()
    elif name == "duplicate-field":
        schemas[VIEW_ORDER[0]]["fields"].insert(
            1, copy.deepcopy(schemas[VIEW_ORDER[0]]["fields"][0])
        )
    elif name == "empty-variant":
        schemas["execution-view-v0"]["fields"][2][1]["cases"] = []
    elif name == "unknown-atom":
        schemas["public-coin-view-v0"]["fields"][1][1] = _atom("host-object")
    elif name == "unknown-compiler":
        schemas[VIEW_ORDER[0]]["fields"][0][1]["atom"]["compiler"] = (
            "ambient-reflection-v0"
        )
    elif name == "module-payload-decomposition":
        module_case = schemas["effect-view-v0"]["fields"][1][1]["element"]["fields"][2][
            1
        ]["cases"][1]
        module_case[1] = _record((0, _atom("bytes", max=64)))
    elif name == "missing-value-field":
        values[VIEW_ORDER[0]].pop(2)
    elif name == "extra-value-field":
        values[VIEW_ORDER[0]][99] = None
    elif name == "inactive-variant-case":
        values["execution-view-v0"][2] = {"case": 9, "value": None}
    elif name == "sequence-overflow":
        values["public-coin-view-v0"][2] = [
            _canonical_body("value-ref-body-v0", f"value:{index}") for index in range(5)
        ]
    elif name == "law-substitution":
        values["strategy-decision-view-v0"][2] = _profile_law("execution-and-replay-v0")
    elif name == "leaf-compiler-substitution":
        values[VIEW_ORDER[0]][0] = _canonical_body(
            "protocol-id-body-v0", "core:finite-schnorr-fixture"
        )
    elif name == "unadmitted-canonical-value":
        values[VIEW_ORDER[0]][2][0][4]["admitted"] = False
    elif name == "unsupported-module-effect":
        values["effect-view-v0"][1][0][2]["value"]["supported"] = False
    elif name == "invalid-module-payload":
        values["effect-view-v0"][1][0][2]["value"]["payload_valid"] = False
    elif name == "module-owner-substitution":
        values["effect-view-v0"][1][0][2]["value"]["declaration"]["module"] = (
            "module:other"
        )
    elif name == "boolean-as-natural":
        values["public-coin-view-v0"][1] = 1
    elif name == "missing-manifest-leaf":
        manifests[VIEW_ORDER[0]].pop()
    elif name == "duplicate-manifest-leaf":
        manifests[VIEW_ORDER[0]].append(copy.deepcopy(manifests[VIEW_ORDER[0]][-1]))
    elif name == "reordered-manifest":
        manifests[VIEW_ORDER[0]].reverse()
    elif name == "wrong-boundary":
        manifests[VIEW_ORDER[0]][0]["boundary"] = {"kind": "unit"}
    elif name == "interior-path":
        manifests[VIEW_ORDER[0]][0]["path"].pop()
    elif name == "text-path-step":
        manifests[VIEW_ORDER[0]][0]["path"][0] = {"step": "field-name", "ordinal": 0}
    elif name == "out-of-range-sequence-path":
        coordinate = manifests[VIEW_ORDER[0]][1]
        sequence_step = next(
            step for step in coordinate["path"] if step["step"] == "sequence"
        )
        sequence_step["ordinal"] = 99
    elif name == "cross-view-coordinate":
        manifests[VIEW_ORDER[0]][0]["view"] = "effect-view-v0"
    elif name == "equal-value-coordinate-alias":
        public_coin_manifest = manifests["public-coin-view-v0"]
        equal_coordinates = [
            coordinate
            for coordinate in public_coin_manifest
            if coordinate["boundary"]
            == {"kind": "canonical-body", "compiler": "value-ref-body-v0"}
        ]
        if len(equal_coordinates) < 2:
            raise AssertionError("fixture lost equal-value coordinate controls")
        replacement = copy.deepcopy(equal_coordinates[0])
        index = public_coin_manifest.index(equal_coordinates[1])
        public_coin_manifest[index] = replacement
    else:
        raise KeyError(name)
    return candidate
