"""Cold byte-derived Oracle projector for F0-V2B2C1B2.

The module loads independent Foundation/schema/codec instances through the
B2C1B1 cold path, parses complete profiled Core and Protocol bytes into plain
records, and derives the six static views without importing the typed Oracle
owner evaluator.
"""

from __future__ import annotations

import heapq
import importlib.util
from pathlib import Path
import sys
from types import ModuleType
from typing import Any


ROOT = Path(__file__).resolve().parents[2]
FOUNDATION_COLD = (
    ROOT
    / "evaluation"
    / "formal-source-owner-projections-f0v2b2c1b1"
    / "independent.py"
)


class ColdOracleError(ValueError):
    pass


def _load(name: str, path: Path) -> ModuleType:
    if name in sys.modules:
        return sys.modules[name]
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:  # pragma: no cover - host failure
        raise ImportError(f"cannot load module at {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


cold = _load("_zkc_f0v2b2c1b2_cold_foundation", FOUNDATION_COLD)
k1 = cold.k1
b2b = cold.b2b
codec = cold.codec
VIEW_SCHEMAS = cold.VIEW_SCHEMAS
PROFILE_DIGEST = cold.PROFILE_DIGEST


def _record(value: object, ordinals: tuple[int, ...], label: str) -> tuple[object, ...]:
    try:
        return cold._record(value, ordinals, label)
    except Exception as error:
        raise ColdOracleError(str(error)) from error


def _sequence(value: object, label: str) -> tuple[object, ...]:
    try:
        return cold._sequence(value, label)
    except Exception as error:
        raise ColdOracleError(str(error)) from error


def _variant(value: object, cases: set[int], label: str) -> tuple[int, object]:
    try:
        return cold._variant(value, cases, label)
    except Exception as error:
        raise ColdOracleError(str(error)) from error


def _nat(value: object, label: str) -> int:
    try:
        return cold._nat(value, label)
    except Exception as error:
        raise ColdOracleError(str(error)) from error


def _bytes(value: object, label: str) -> bytes:
    try:
        return cold._bytes(value, label)
    except Exception as error:
        raise ColdOracleError(str(error)) from error


def _unit(value: object, label: str) -> None:
    try:
        cold._unit(value, label)
    except Exception as error:
        raise ColdOracleError(str(error)) from error


def _decode_schema(value: object, depth: int = 0) -> object:
    if depth > 48:
        raise ColdOracleError("value schema is too deep")
    tag, payload = _variant(value, set(range(9)), "value schema")
    if tag == 0:
        _unit(payload, "unit schema")
        return k1.UnitSchema()
    if tag == 1:
        _unit(payload, "Boolean schema")
        return k1.BoolSchema()
    if tag == 2:
        return k1.NatSchema(_nat(payload, "natural maximum"))
    if tag == 3:
        lower, upper = _record(payload, (0, 1), "integer schema")
        if type(lower) is not k1.IntValue or type(upper) is not k1.IntValue:
            raise ColdOracleError("integer bounds differ")
        return k1.IntSchema(lower.value, upper.value)
    if tag == 4:
        lower, upper = _record(payload, (0, 1), "bytes schema")
        return k1.BytesSchema(
            _nat(lower, "bytes minimum"), _nat(upper, "bytes maximum")
        )
    if tag == 5:
        return k1.SymbolSchema(_nat(payload, "symbol maximum"))
    if tag == 6:
        element, maximum = _record(payload, (0, 1), "sequence schema")
        return k1.SeqSchema(
            _decode_value_type(element, depth + 1),
            _nat(maximum, "sequence maximum"),
        )
    entries = _sequence(payload, "aggregate entries")
    pairs = tuple(
        (
            _nat(_record(item, (0, 1), "aggregate entry")[0], "entry ordinal"),
            _decode_value_type(_record(item, (0, 1), "aggregate entry")[1], depth + 1),
        )
        for item in entries
    )
    return k1.RecordSchema(pairs) if tag == 7 else k1.VariantSchema(pairs)


def _decode_value_type(value: object, depth: int = 0) -> object:
    domain, schema = _record(value, (0, 1), "value type")
    owner_case, owner_payload = _variant(domain, {0, 1}, "value-domain owner")
    owner_ref, kind, ordinal = _record(owner_payload, (0, 1, 2), "value domain")
    if type(kind) is not k1.Symbol:
        raise ColdOracleError("value-domain kind is not a Symbol")
    owner_bytes = _bytes(owner_ref, "value-domain owner")
    try:
        owner = (
            k1.decode_prior_meta_reference(owner_bytes)
            if owner_case == 0
            else k1.decode_content_reference(owner_bytes)
        )
        return k1.ValueType(
            k1.ValueDomain(owner, kind, _nat(ordinal, "value-domain ordinal")),
            _decode_schema(schema, depth + 1),
        )
    except ColdOracleError:
        raise
    except Exception as error:
        raise ColdOracleError(f"value type does not decode: {error}") from error


def _parse_value_ref(value: object) -> tuple[int, int, int]:
    return cold._parse_value_ref(value)


def _parse_guard(value: object) -> dict[str, Any]:
    guard = cold._parse_guard(value)
    if guard["tag"] != 0:
        raise ColdOracleError("Oracle isolation Core uses a nontrivial guard")
    return guard


def _parse_mode(value: object) -> dict[str, Any]:
    tag, payload = _variant(value, {0, 1, 2}, "Oracle publication mode")
    if tag == 0:
        _unit(payload, "FullCanonicalOracle payload")
        return {"tag": tag, "body": value}
    if tag == 1:
        value_type, contract, algorithm, evaluation = _record(
            payload, (0, 1, 2, 3), "PublicBinding mode"
        )
        return {
            "tag": tag,
            "body": value,
            "binding_type": value_type,
            "binding_contract": contract,
            "algorithm": _bytes(algorithm, "binding algorithm"),
            "evaluation": _bytes(evaluation, "binding evaluation"),
        }
    return {"tag": tag, "body": value, "domain_law": payload}


def _parse_oracle(value: object) -> dict[str, Any]:
    scope, origin, index_type, element_type, maximum, mode = _record(
        value, tuple(range(6)), "Oracle declaration"
    )
    origin_tag, origin_payload = _variant(origin, {0, 1}, "Oracle origin")
    _unit(origin_payload, "Oracle-origin payload")
    return {
        "scope": _nat(scope, "Oracle scope"),
        "origin": origin_tag,
        "index_type": index_type,
        "element_type": element_type,
        "maximum": _nat(maximum, "Oracle maximum"),
        "mode": _parse_mode(mode),
    }


def _parse_effect(value: object) -> dict[str, Any]:
    tag, payload = _variant(value, set(range(8)), "Core effect")
    if tag == 0:
        channel, payload_type = _record(payload, (0, 1), "Prover message")
        return {
            "tag": tag,
            "body": value,
            "channel": channel,
            "payload_type": payload_type,
        }
    if tag == 5:
        return {"tag": tag, "body": value, "terminal": _nat(payload, "terminal")}
    if tag != 6:
        raise ColdOracleError("effect belongs to another isolation slice")
    oracle_tag, oracle_payload = _variant(payload, {0, 1, 2}, "Oracle effect")
    if oracle_tag == 0:
        detail = {"oracle_tag": 0, "oracle": _nat(oracle_payload, "publication")}
    elif oracle_tag == 1:
        oracle, index, visibility = _record(oracle_payload, (0, 1, 2), "query")
        visibility_tag, visibility_payload = _variant(
            visibility, {0, 1}, "Oracle visibility"
        )
        _unit(visibility_payload, "Oracle-visibility payload")
        detail = {
            "oracle_tag": 1,
            "oracle": _nat(oracle, "query Oracle"),
            "index": _parse_value_ref(index),
            "visibility": visibility_tag,
        }
    else:
        detail = {"oracle_tag": 2, "query": _nat(oracle_payload, "answer query")}
    return {"tag": 6, "body": value, **detail}


def decode_core(domain_body: bytes) -> dict[str, Any]:
    if type(domain_body) is not bytes or not domain_body:
        raise ColdOracleError("Core domain body is not exact bytes")
    try:
        root = k1.decode_datum(domain_body)
    except Exception as error:
        raise ColdOracleError(f"Core domain does not decode: {error}") from error
    if k1.encode_datum(root) != domain_body:
        raise ColdOracleError("Core domain does not round-trip")
    fields = _record(root, tuple(range(14)), "InteractiveCore")
    tables = tuple(
        _sequence(value, f"InteractiveCore field {index}")
        for index, value in enumerate(fields)
    )
    if any(tables[index] for index in (2, 4, 7, 9, 10, 11)):
        raise ColdOracleError("Core contains another constructor slice")
    public_inputs = tuple(
        {"type": _record(item, (0,), "public input")[0]} for item in tables[1]
    )
    constants = tuple(
        {
            "type": _record(item, (0, 1), "constant")[0],
            "value": _record(item, (0, 1), "constant")[1],
        }
        for item in tables[3]
    )
    scopes: list[dict[str, int | None]] = []
    for item in tables[5]:
        parent, opening = _record(item, (0, 1), "scope")
        parent_tag, parent_payload = _variant(parent, {0, 1}, "scope parent")
        opening_tag, opening_payload = _variant(opening, {0, 1}, "scope opening")
        if parent_tag == 0:
            _unit(parent_payload, "absent parent")
        if opening_tag == 0:
            _unit(opening_payload, "initial opening")
        scopes.append(
            {
                "parent": None
                if parent_tag == 0
                else _nat(parent_payload, "scope parent"),
                "opening": None
                if opening_tag == 0
                else _nat(opening_payload, "scope opening"),
            }
        )
    bindings: list[dict[str, Any]] = []
    for item in tables[6]:
        scope, binding_class, value = _record(item, (0, 1, 2), "binding")
        class_tag, class_payload = _variant(binding_class, {0, 1, 2}, "binding class")
        _unit(class_payload, "binding-class payload")
        bindings.append(
            {
                "scope": _nat(scope, "binding scope"),
                "class": class_tag,
                "value": _parse_value_ref(value),
            }
        )
    terminals: list[dict[str, Any]] = []
    for item in tables[12]:
        verdict, outputs, checks, dispositions = _record(item, (0, 1, 2, 3), "terminal")
        verdict_tag, verdict_payload = _variant(verdict, {0, 1, 2}, "verdict")
        _unit(verdict_payload, "verdict payload")
        if _sequence(checks, "terminal checks") or _sequence(
            dispositions, "terminal dispositions"
        ):
            raise ColdOracleError("terminal belongs to another slice")
        terminals.append(
            {
                "verdict": verdict_tag,
                "outputs": tuple(
                    _parse_value_ref(value)
                    for value in _sequence(outputs, "terminal outputs")
                ),
            }
        )
    occurrences = tuple(
        {
            "scope": _nat(_record(item, (0, 1, 2), "occurrence")[0], "scope"),
            "guard": _parse_guard(_record(item, (0, 1, 2), "occurrence")[1]),
            "effect": _parse_effect(_record(item, (0, 1, 2), "occurrence")[2]),
        }
        for item in tables[13]
    )
    return {
        "used_modules": tuple(_bytes(item, "used module") for item in tables[0]),
        "public_inputs": public_inputs,
        "constants": constants,
        "scopes": tuple(scopes),
        "bindings": tuple(bindings),
        "oracles": tuple(_parse_oracle(item) for item in tables[8]),
        "terminals": tuple(terminals),
        "occurrences": occurrences,
    }


def _value_type_body(value: object) -> dict[str, str]:
    return cold._value_type(value)


def _type_datum(value_type: object) -> object:
    return k1.value_type_datum(value_type)


def _carrier_type(oracle: dict[str, Any]) -> object:
    index_type = _decode_value_type(oracle["index_type"])
    element_type = _decode_value_type(oracle["element_type"])
    entry = k1.ValueType(
        k1.RECORD_DOMAIN,
        k1.RecordSchema(((0, index_type), (1, element_type))),
    )
    return k1.ValueType(k1.SEQUENCE_DOMAIN, k1.SeqSchema(entry, oracle["maximum"]))


def _lookup_type(oracle: dict[str, Any]) -> object:
    element_type = _decode_value_type(oracle["element_type"])
    return k1.ValueType(
        k1.VARIANT_DOMAIN,
        k1.VariantSchema(((0, k1.UNIT_VALUE), (1, element_type))),
    )


def _publication_types(oracle: dict[str, Any]) -> tuple[object, ...]:
    tag = oracle["mode"]["tag"]
    if tag == 0:
        return (_type_datum(_carrier_type(oracle)),)
    if tag == 1:
        return (oracle["mode"]["binding_type"],)
    return ()


def _answer_type(oracle: dict[str, Any]) -> object:
    return (
        oracle["element_type"]
        if oracle["mode"]["tag"] == 2
        else _type_datum(_lookup_type(oracle))
    )


def _output_types(core: dict[str, Any]) -> tuple[tuple[object, ...], ...]:
    result: list[tuple[object, ...]] = []
    for index, occurrence in enumerate(core["occurrences"]):
        effect = occurrence["effect"]
        if effect["tag"] == 0:
            result.append((effect["payload_type"],))
        elif effect["tag"] == 5:
            result.append(())
        elif effect["oracle_tag"] == 0:
            result.append(_publication_types(core["oracles"][effect["oracle"]]))
        elif effect["oracle_tag"] == 1:
            result.append(())
        else:
            if not 0 <= effect["query"] < index:
                raise ColdOracleError("answer query is not earlier")
            query = core["occurrences"][effect["query"]]["effect"]
            result.append((_answer_type(core["oracles"][query["oracle"]]),))
    return tuple(result)


def _scope_paths(core: dict[str, Any]) -> tuple[tuple[int, ...], ...]:
    paths: list[tuple[int, ...]] = []
    for index in range(len(core["scopes"])):
        current: int | None = index
        path: list[int] = []
        while current is not None:
            path.append(current)
            current = core["scopes"][current]["parent"]
        paths.append(tuple(reversed(path)))
    return tuple(paths)


def _type_of(
    core: dict[str, Any],
    outputs: tuple[tuple[object, ...], ...],
    reference: tuple[int, int, int],
) -> object:
    tag, first, second = reference
    if tag == 0:
        return core["public_inputs"][first]["type"]
    if tag == 2:
        return core["constants"][first]["type"]
    if tag == 4:
        return outputs[first][second]
    raise ColdOracleError("ValueRef belongs to another slice")


def _producer(reference: tuple[int, int, int]) -> tuple[int, ...]:
    tag, first, second = reference
    if tag in (0, 2):
        return tag, first
    if tag == 4:
        return 8, first, second
    raise ColdOracleError("producer belongs to another slice")


def _pc_value(node: tuple[int, ...]) -> dict[str, Any]:
    tag, *args = node
    if tag == 8:
        return cold._v(
            8,
            {
                0: cold._ordinal("occurrence-ref-body-v0", args[0]),
                1: args[1],
            },
        )
    compiler = {
        0: "public-input-ref-body-v0",
        2: "constant-ref-body-v0",
        4: "scope-ref-body-v0",
        5: "binding-ref-body-v0",
        6: "occurrence-ref-body-v0",
        7: "occurrence-ref-body-v0",
        11: "terminal-ref-body-v0",
    }.get(tag)
    if compiler is None:
        raise ColdOracleError("PCNode belongs to another slice")
    return cold._v(tag, cold._ordinal(compiler, args[0]))


_PC_GRAPH_SCHEMA = cold._PC_GRAPH_SCHEMA
_PC_NODE_SCHEMA = cold._PC_NODE_SCHEMA
_PC_EDGE_SCHEMA = cold._PC_EDGE_SCHEMA


def _pc_key(node: tuple[int, ...]) -> bytes:
    return codec.encode_value(_PC_NODE_SCHEMA, _pc_value(node))


def _edge_value(pair: tuple[tuple[int, ...], tuple[int, ...]]) -> dict[int, Any]:
    return {0: _pc_value(pair[0]), 1: _pc_value(pair[1])}


def _edge_key(pair: tuple[tuple[int, ...], tuple[int, ...]]) -> bytes:
    return codec.encode_value(_PC_EDGE_SCHEMA, _edge_value(pair))


def _lifecycle(
    core: dict[str, Any],
) -> tuple[dict[int, int], dict[int, tuple[int, ...]], dict[int, tuple[int, ...]]]:
    publications: dict[int, int] = {}
    queries: dict[int, list[int]] = {index: [] for index in range(len(core["oracles"]))}
    answers: dict[int, list[int]] = {index: [] for index in range(len(core["oracles"]))}
    for occurrence_ref, occurrence in enumerate(core["occurrences"]):
        effect = occurrence["effect"]
        if effect["tag"] != 6:
            continue
        if effect["oracle_tag"] == 0:
            publications[effect["oracle"]] = occurrence_ref
        elif effect["oracle_tag"] == 1:
            queries[effect["oracle"]].append(occurrence_ref)
        else:
            query = core["occurrences"][effect["query"]]["effect"]
            answers[query["oracle"]].append(occurrence_ref)
    return (
        publications,
        {key: tuple(value) for key, value in queries.items()},
        {key: tuple(value) for key, value in answers.items()},
    )


def _graph(
    core: dict[str, Any], outputs: tuple[tuple[object, ...], ...]
) -> tuple[dict[int, Any], dict[str, Any]]:
    predecessors: dict[tuple[int, ...], set[tuple[int, ...]]] = {}
    successors: dict[tuple[int, ...], set[tuple[int, ...]]] = {}

    def node(value: tuple[int, ...]) -> tuple[int, ...]:
        predecessors.setdefault(value, set())
        successors.setdefault(value, set())
        return value

    def connect(source: tuple[int, ...], target: tuple[int, ...]) -> None:
        source, target = node(source), node(target)
        predecessors[target].add(source)
        successors[source].add(target)

    for index in range(len(core["public_inputs"])):
        node((0, index))
    for index in range(len(core["constants"])):
        node((2, index))
    for index, scope in enumerate(core["scopes"]):
        node((4, index))
        if scope["parent"] is not None:
            connect((4, scope["parent"]), (4, index))
    for index, binding in enumerate(core["bindings"]):
        connect((4, binding["scope"]), (5, index))
        connect(_producer(binding["value"]), (5, index))
    publications, _queries, _answers = _lifecycle(core)
    terminal_positions: dict[int, int] = {}
    earlier_terminals: list[tuple[int, ...]] = []
    for occurrence_ref, occurrence in enumerate(core["occurrences"]):
        activity, effect_node = node((6, occurrence_ref)), node((7, occurrence_ref))
        connect((4, occurrence["scope"]), activity)
        for terminal in earlier_terminals:
            connect(terminal, activity)
        connect(activity, effect_node)
        effect = occurrence["effect"]
        if effect["tag"] == 6 and effect["oracle_tag"] == 1:
            connect((7, publications[effect["oracle"]]), effect_node)
            connect(_producer(effect["index"]), effect_node)
        elif effect["tag"] == 6 and effect["oracle_tag"] == 2:
            query = core["occurrences"][effect["query"]]["effect"]
            connect((7, effect["query"]), effect_node)
            connect((7, publications[query["oracle"]]), effect_node)
        elif effect["tag"] == 5:
            for reference in core["terminals"][effect["terminal"]]["outputs"]:
                connect(_producer(reference), effect_node)
            terminal = node((11, effect["terminal"]))
            connect(effect_node, terminal)
            terminal_positions[effect["terminal"]] = occurrence_ref
            earlier_terminals.append(terminal)
        for output in range(len(outputs[occurrence_ref])):
            connect(effect_node, (8, occurrence_ref, output))

    remaining = {key: len(value) for key, value in predecessors.items()}
    heap = [(_pc_key(key), key) for key, count in remaining.items() if count == 0]
    heapq.heapify(heap)
    topological: list[tuple[int, ...]] = []
    while heap:
        _key, current = heapq.heappop(heap)
        topological.append(current)
        for child in successors[current]:
            remaining[child] -= 1
            if remaining[child] == 0:
                heapq.heappush(heap, (_pc_key(child), child))
    if len(topological) != len(predecessors):
        raise ColdOracleError("Oracle PCGraph is cyclic")
    classes: dict[tuple[int, ...], int] = {}
    for current in topological:
        inherited = max((classes[item] for item in predecessors[current]), default=0)
        if current[0] in (0, 2):
            assigned = 0
        elif current[0] == 7:
            effect = core["occurrences"][current[1]]["effect"]
            if effect["tag"] == 0 or (effect["tag"] == 6 and effect["oracle_tag"] == 0):
                assigned = 1 if inherited <= 1 else inherited
            elif effect["tag"] == 6 and effect["oracle_tag"] == 1:
                assigned = (
                    2
                    if effect["visibility"] == 1
                    else max(
                        classes[(6, current[1])],
                        classes[_producer(effect["index"])],
                    )
                )
            elif effect["tag"] == 6 and effect["oracle_tag"] == 2:
                query = core["occurrences"][effect["query"]]["effect"]
                assigned = (
                    2
                    if query["visibility"] == 1
                    else (
                        1 if classes[(6, current[1])] <= 1 else classes[(6, current[1])]
                    )
                )
            else:
                assigned = inherited
        else:
            assigned = inherited
        classes[current] = assigned

    activities = {(6, index) for index in range(len(core["occurrences"]))}
    terminals = {(11, index) for index in range(len(core["terminals"]))}
    terminal_outputs = {
        _producer(reference)
        for terminal in core["terminals"]
        for reference in terminal["outputs"]
    }
    observations: set[tuple[int, ...]] = set()
    for index, occurrence in enumerate(core["occurrences"]):
        effect = occurrence["effect"]
        if effect["tag"] == 0:
            observations.add((8, index, 0))
        elif effect["tag"] == 6 and effect["oracle_tag"] == 0:
            oracle = core["oracles"][effect["oracle"]]
            if oracle["mode"]["tag"] == 2:
                observations.add((7, index))
            else:
                observations.update(
                    (8, index, output) for output in range(len(outputs[index]))
                )
        elif (
            effect["tag"] == 6
            and effect["oracle_tag"] == 1
            and effect["visibility"] == 0
        ):
            observations.add((7, index))
        elif effect["tag"] == 6 and effect["oracle_tag"] == 2:
            query = core["occurrences"][effect["query"]]["effect"]
            if query["visibility"] == 0:
                observations.add((8, index, 0))
    sinks = activities | terminals | terminal_outputs | observations
    accepting = {
        (11, index)
        for index, terminal in enumerate(core["terminals"])
        if terminal["verdict"] == 0
    }
    acceptance = accepting | {
        _producer(reference)
        for index, terminal in enumerate(core["terminals"])
        if (11, index) in accepting
        for reference in terminal["outputs"]
    }
    logical_rows: list[dict[int, Any]] = []
    has_intersection = False
    for oracle_ref, oracle in enumerate(core["oracles"]):
        if oracle["mode"]["tag"] != 2:
            continue
        source = (7, publications[oracle_ref])
        cone = {source}
        pending = [source]
        while pending:
            current = pending.pop()
            for child in successors[current]:
                if child not in cone:
                    cone.add(child)
                    pending.append(child)
        intersection = cone & acceptance
        has_intersection = has_intersection or bool(intersection)
        logical_rows.append(
            {
                0: cold._ordinal("oracle-ref-body-v0", oracle_ref),
                1: [_pc_value(item) for item in sorted(cone, key=_pc_key)],
                2: [_pc_value(item) for item in sorted(intersection, key=_pc_key)],
            }
        )
    ordered_nodes = sorted(predecessors, key=_pc_key)
    edges = {
        (source, target)
        for target, sources in predecessors.items()
        for source in sources
    }
    ordered_edges = sorted(edges, key=_edge_key)
    graph = {
        0: [_pc_value(item) for item in ordered_nodes],
        1: [_edge_value(item) for item in ordered_edges],
        2: [_pc_value(item) for item in topological],
        3: [{0: _pc_value(item), 1: cold._v(classes[item])} for item in ordered_nodes],
        4: [_pc_value(item) for item in sorted(sinks, key=_pc_key)],
        5: [_pc_value(item) for item in sorted(acceptance, key=_pc_key)],
        6: logical_rows,
    }
    return graph, {
        "eligible": all(classes[item] in (0, 1) for item in sinks)
        and not has_intersection,
        "terminal_positions": terminal_positions,
        "nodes": len(predecessors),
        "edges": len(edges),
        "logical_intersections": int(has_intersection),
    }


def _mode_value(mode: dict[str, Any]) -> dict[str, Any]:
    if mode["tag"] == 0:
        return cold._v(0)
    if mode["tag"] == 1:
        return cold._v(
            1,
            {
                0: _value_type_body(mode["binding_type"]),
                1: cold._module_ref(mode["binding_contract"]),
                2: cold._identifier("algorithm-ref-body-v0", mode["algorithm"]),
                3: cold._identifier(
                    "evaluation-contract-id-body-v0", mode["evaluation"]
                ),
            },
        )
    return cold._v(2, cold._module_ref(mode["domain_law"]))


def _oracle_value(oracle: dict[str, Any]) -> dict[int, Any]:
    return {
        0: cold._ordinal("scope-ref-body-v0", oracle["scope"]),
        1: cold._v(oracle["origin"]),
        2: _value_type_body(oracle["index_type"]),
        3: _value_type_body(oracle["element_type"]),
        4: oracle["maximum"],
        5: _mode_value(oracle["mode"]),
    }


def _carrier_value(oracle: dict[str, Any]) -> dict[int, Any]:
    return {
        0: _value_type_body(oracle["index_type"]),
        1: _value_type_body(oracle["element_type"]),
        2: oracle["maximum"],
    }


def _effect_value(effect: dict[str, Any]) -> dict[str, Any]:
    if effect["tag"] == 0:
        return cold._v(
            0,
            {
                0: cold._module_ref(effect["channel"]),
                1: _value_type_body(effect["payload_type"]),
            },
        )
    if effect["tag"] == 5:
        return cold._v(5, cold._ordinal("terminal-ref-body-v0", effect["terminal"]))
    if effect["oracle_tag"] == 0:
        oracle_effect = cold._v(
            0, cold._ordinal("oracle-ref-body-v0", effect["oracle"])
        )
    elif effect["oracle_tag"] == 1:
        oracle_effect = cold._v(
            1,
            {
                0: cold._ordinal("oracle-ref-body-v0", effect["oracle"]),
                1: cold._value_ref(effect["index"]),
                2: cold._v(effect["visibility"]),
            },
        )
    else:
        oracle_effect = cold._v(
            2, cold._ordinal("occurrence-ref-body-v0", effect["query"])
        )
    return cold._v(6, oracle_effect)


def _move(core: dict[str, Any], effect: dict[str, Any]) -> dict[str, Any] | None:
    if effect["tag"] == 0:
        return cold._v(0, _value_type_body(effect["payload_type"]))
    if effect["tag"] == 6 and effect["oracle_tag"] == 0:
        oracle = core["oracles"][effect["oracle"]]
        if oracle["origin"] == 1:
            return cold._v(
                1,
                {
                    0: cold._ordinal("oracle-ref-body-v0", effect["oracle"]),
                    1: _carrier_value(oracle),
                    2: _mode_value(oracle["mode"]),
                },
            )
    return None


def project(
    core_profiled_body: bytes,
    core_reference: bytes,
    protocol_profiled_body: bytes,
    protocol_reference: bytes,
) -> tuple[dict[str, Any], dict[str, Any]]:
    try:
        core_profile, core_domain = cold._authenticated_subject(
            core_profiled_body,
            core_reference,
            "pir.interactive-core",
            "cold Oracle Core",
        )
        protocol_profile, protocol_domain = cold._authenticated_subject(
            protocol_profiled_body,
            protocol_reference,
            "pir.protocol",
            "cold Oracle Protocol",
        )
    except Exception as error:
        raise ColdOracleError(str(error)) from error
    if protocol_profile != core_profile:
        raise ColdOracleError("Core and Protocol profiles differ")
    protocol_core, interpretation = _record(
        protocol_domain, (0, 1), "cold Protocol domain"
    )
    if _bytes(protocol_core, "Protocol Core") != core_reference:
        raise ColdOracleError("Fresh Protocol names another Core")
    interpretation_tag, interpretation_payload = _variant(
        interpretation, {0}, "Fresh interpretation"
    )
    if interpretation_tag != 0:
        raise ColdOracleError("Protocol is not Fresh")
    _unit(interpretation_payload, "Fresh payload")

    core = decode_core(k1.encode_datum(core_domain))
    outputs = _output_types(core)
    paths = _scope_paths(core)
    graph, graph_evidence = _graph(core, outputs)
    publications, queries, answers = _lifecycle(core)
    core_atom = cold._identifier("core-id-body-v0", core_reference)
    protocol_atom = cold._identifier("protocol-id-body-v0", protocol_reference)

    public_binding = {
        0: core_atom,
        1: [
            {
                0: cold._ordinal("scope-ref-body-v0", index),
                1: cold._v(0)
                if scope["parent"] is None
                else cold._v(1, cold._ordinal("scope-ref-body-v0", scope["parent"])),
                2: cold._v(0)
                if scope["opening"] is None
                else cold._v(
                    1,
                    cold._ordinal("occurrence-ref-body-v0", scope["opening"]),
                ),
                3: [cold._ordinal("scope-ref-body-v0", item) for item in paths[index]],
            }
            for index, scope in enumerate(core["scopes"])
        ],
        2: [
            {
                0: cold._ordinal("binding-ref-body-v0", index),
                1: cold._ordinal("scope-ref-body-v0", binding["scope"]),
                2: cold._v(binding["class"]),
                3: cold._value_ref(binding["value"]),
                4: _value_type_body(_type_of(core, outputs, binding["value"])),
            }
            for index, binding in enumerate(core["bindings"])
        ],
    }

    decisions = tuple(
        (index, occurrence, move)
        for index, occurrence in enumerate(core["occurrences"])
        if (move := _move(core, occurrence["effect"])) is not None
    )
    decision_rows: list[dict[int, Any]] = []
    read_rows: list[dict[int, Any]] = []
    legal_rows: list[dict[int, Any]] = []
    for occurrence_ref, occurrence, move in decisions:
        decision_rows.append(
            {
                0: cold._ordinal("decision-ref-body-v0", occurrence_ref),
                1: cold._ordinal("occurrence-ref-body-v0", occurrence_ref),
                2: [
                    cold._ordinal("scope-ref-body-v0", item)
                    for item in paths[occurrence["scope"]]
                ],
                3: cold._guard(occurrence["guard"]["body"]),
                4: move,
                5: [
                    cold._ordinal("decision-ref-body-v0", prior)
                    for prior, _item, _prior_move in decisions
                    if prior < occurrence_ref
                ],
            }
        )
        for index, constant in enumerate(core["constants"]):
            read_rows.append(
                {
                    0: cold._ordinal("decision-ref-body-v0", occurrence_ref),
                    1: cold._v(0, cold._ordinal("constant-ref-body-v0", index)),
                    2: _value_type_body(constant["type"]),
                }
            )
        for prior_ref, prior_occurrence in enumerate(
            core["occurrences"][:occurrence_ref]
        ):
            effect = prior_occurrence["effect"]
            read_case: int | None = None
            read_type: object | None = None
            visible = True
            if effect["tag"] == 0:
                read_case, read_type = 3, effect["payload_type"]
            elif effect["tag"] == 6 and effect["oracle_tag"] == 0:
                read_case = 5
                types = _publication_types(core["oracles"][effect["oracle"]])
                read_type = types[0] if types else k1.value_type_datum(k1.UNIT_VALUE)
            elif effect["tag"] == 6 and effect["oracle_tag"] == 1:
                read_case, read_type = (
                    6,
                    core["oracles"][effect["oracle"]]["index_type"],
                )
                visible = effect["visibility"] == 0
            elif effect["tag"] == 6 and effect["oracle_tag"] == 2:
                query = core["occurrences"][effect["query"]]["effect"]
                read_case, read_type = 7, _answer_type(core["oracles"][query["oracle"]])
                visible = query["visibility"] == 0
            if read_case is not None and visible:
                read_rows.append(
                    {
                        0: cold._ordinal("decision-ref-body-v0", occurrence_ref),
                        1: cold._v(
                            read_case,
                            cold._ordinal("occurrence-ref-body-v0", prior_ref),
                        ),
                        2: _value_type_body(read_type),
                    }
                )
            if _move(core, effect) is not None:
                read_rows.append(
                    {
                        0: cold._ordinal("decision-ref-body-v0", occurrence_ref),
                        1: cold._v(9, cold._ordinal("decision-ref-body-v0", prior_ref)),
                        2: _value_type_body(
                            effect["payload_type"]
                            if effect["tag"] == 0
                            else _type_datum(
                                _carrier_type(core["oracles"][effect["oracle"]])
                            )
                        ),
                    }
                )
        legal_rows.append(
            {0: cold._ordinal("decision-ref-body-v0", occurrence_ref), 1: move}
        )
    strategy = {
        0: core_atom,
        1: decision_rows,
        2: cold._law("core-admission-v0"),
        3: read_rows,
        4: legal_rows,
    }
    public_coin = {0: core_atom, 1: graph, 2: graph_evidence["eligible"], 3: [], 4: []}

    value_rows: list[dict[int, Any]] = []
    for tag, name in ((0, "public_inputs"), (2, "constants")):
        for index, declaration in enumerate(core[name]):
            value_rows.append(
                {
                    0: cold._value_ref((tag, index, 0)),
                    1: _value_type_body(declaration["type"]),
                    2: [],
                }
            )
    occurrence_rows: list[dict[int, Any]] = []
    message_rows: list[dict[int, Any]] = []
    for occurrence_ref, occurrence in enumerate(core["occurrences"]):
        effect = occurrence["effect"]
        occurrence_rows.append(
            {
                0: cold._ordinal("occurrence-ref-body-v0", occurrence_ref),
                1: [
                    cold._ordinal("scope-ref-body-v0", item)
                    for item in paths[occurrence["scope"]]
                ],
                2: cold._guard(occurrence["guard"]["body"]),
                3: _effect_value(effect),
                4: [_value_type_body(item) for item in outputs[occurrence_ref]],
            }
        )
        if effect["tag"] == 0:
            message_rows.append(
                {
                    0: cold._ordinal("occurrence-ref-body-v0", occurrence_ref),
                    1: cold._v(0),
                    2: cold._v(
                        0,
                        {
                            0: cold._module_ref(effect["channel"]),
                            1: _value_type_body(effect["payload_type"]),
                        },
                    ),
                }
            )
        for output, output_type in enumerate(outputs[occurrence_ref]):
            predecessors: list[dict[str, str]] = []
            if effect["tag"] == 6 and effect["oracle_tag"] == 2:
                query = core["occurrences"][effect["query"]]["effect"]
                predecessors.append(cold._value_ref(query["index"]))
            value_rows.append(
                {
                    0: cold._value_ref((4, occurrence_ref, output)),
                    1: _value_type_body(output_type),
                    2: predecessors,
                }
            )
    oracle_rows = [
        {
            0: cold._ordinal("oracle-ref-body-v0", oracle_ref),
            1: _oracle_value(oracle),
            2: cold._ordinal("occurrence-ref-body-v0", publications[oracle_ref]),
            3: [
                cold._ordinal("occurrence-ref-body-v0", item)
                for item in queries[oracle_ref]
            ],
            4: [
                cold._ordinal("occurrence-ref-body-v0", item)
                for item in answers[oracle_ref]
            ],
        }
        for oracle_ref, oracle in enumerate(core["oracles"])
    ]
    terminal_rows = [
        {
            0: cold._ordinal("terminal-ref-body-v0", index),
            1: cold._v(terminal["verdict"]),
            2: [cold._value_ref(item) for item in terminal["outputs"]],
            3: [],
            4: [],
            5: cold._ordinal(
                "occurrence-ref-body-v0", graph_evidence["terminal_positions"][index]
            ),
        }
        for index, terminal in enumerate(core["terminals"])
    ]
    effect_view = {
        0: core_atom,
        1: occurrence_rows,
        2: value_rows,
        3: message_rows,
        4: oracle_rows,
        5: [],
        6: terminal_rows,
        7: [],
    }

    receipts: list[dict[str, Any]] = []
    for occurrence_ref, occurrence in enumerate(core["occurrences"]):
        effect = occurrence["effect"]
        if effect["tag"] != 6:
            continue
        if effect["oracle_tag"] == 0:
            receipts.append(
                cold._v(
                    0,
                    {
                        0: cold._ordinal("occurrence-ref-body-v0", occurrence_ref),
                        1: cold._ordinal("oracle-ref-body-v0", effect["oracle"]),
                        2: [_value_type_body(item) for item in outputs[occurrence_ref]],
                    },
                )
            )
        elif effect["oracle_tag"] == 1:
            receipts.append(
                cold._v(
                    1,
                    {
                        0: cold._ordinal("occurrence-ref-body-v0", occurrence_ref),
                        1: cold._ordinal("oracle-ref-body-v0", effect["oracle"]),
                        2: _value_type_body(
                            core["oracles"][effect["oracle"]]["index_type"]
                        ),
                        3: cold._v(effect["visibility"]),
                    },
                )
            )
        else:
            query = core["occurrences"][effect["query"]]["effect"]
            receipts.append(
                cold._v(
                    2,
                    {
                        0: cold._ordinal("occurrence-ref-body-v0", occurrence_ref),
                        1: cold._ordinal("oracle-ref-body-v0", query["oracle"]),
                        2: _value_type_body(
                            _answer_type(core["oracles"][query["oracle"]])
                        ),
                        3: cold._v(query["visibility"]),
                    },
                )
            )
    runtime = {
        0: [
            {
                0: cold._ordinal("occurrence-ref-body-v0", index),
                1: [_value_type_body(item) for item in outputs[index]],
            }
            for index in range(len(core["occurrences"]))
        ],
        1: [],
        2: receipts,
        3: [
            {
                0: cold._ordinal("terminal-ref-body-v0", index),
                1: cold._ordinal(
                    "occurrence-ref-body-v0",
                    graph_evidence["terminal_positions"][index],
                ),
                2: cold._v(terminal["verdict"]),
                3: [
                    _value_type_body(_type_of(core, outputs, item))
                    for item in terminal["outputs"]
                ],
            }
            for index, terminal in enumerate(core["terminals"])
        ],
    }
    execution = {
        0: protocol_atom,
        1: core_atom,
        2: cold._v(0),
        3: cold._law("core-admission-v0"),
        4: [],
        5: cold._law("execution-and-replay-v0"),
        6: runtime,
        7: cold._v(0),
        8: cold._law("execution-and-replay-v0"),
        9: cold._law("run-view-issuance-v0"),
    }
    views = {
        "PublicBindingView": public_binding,
        "StrategyDecisionView": strategy,
        "PublicCoinView": public_coin,
        "EffectView": effect_view,
        "ClaimReductionView": {0: core_atom, 1: [], 2: [], 3: []},
        "ExecutionView": execution,
    }
    return views, {
        "occurrences": len(core["occurrences"]),
        "oracles": len(core["oracles"]),
        "decisions": len(decision_rows),
        "oracle_receipt_schemas": len(receipts),
        "pc_graph": {
            "nodes": graph_evidence["nodes"],
            "edges": graph_evidence["edges"],
            "eligible": graph_evidence["eligible"],
            "logical_intersections": graph_evidence["logical_intersections"],
        },
    }


def encode_views(views: dict[str, Any]) -> dict[str, bytes]:
    if tuple(views) != tuple(b2b.load_source()["view_order"]):
        raise ColdOracleError("cold view table is incomplete or reordered")
    return {
        name: codec.encode_value(VIEW_SCHEMAS[name], value)
        for name, value in views.items()
    }
