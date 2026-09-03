#!/usr/bin/env python3
"""Cold byte-to-view projector for the B2C1B1 foundation slice.

This path does not import the reference owner evaluator.  It starts from the
complete profiled Core and Protocol bodies plus their exact references,
authenticates both identities and the Fresh-to-Core dependency, decodes into
plain records, independently derives all six view values, and uses the
iterative B2B schema compiler and B2C1A value codec.
"""

from __future__ import annotations

import heapq
import importlib.util
from pathlib import Path
import sys
from types import ModuleType
from typing import Any


ROOT = Path(__file__).resolve().parents[2]
CODEC = ROOT / "evaluation/formal-source-view-codec-f0v2b2c1a/independent.py"
PROFILE_DIGEST = "2a1d4f1429b25fcd315072b654f6f0a6816e167d3c06a3a0f29b8028a023349f"


class ColdProjectionError(ValueError):
    """The cold parser or projector cannot form the bounded exact view."""


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


codec = _load("_zkc_f0v2b2c1b1_cold_codec", CODEC)
k1 = codec.k1
b2b = codec.b2b
VIEW_SCHEMAS, _VIEW_OWNERS, _VIEW_STATS = b2b.compile_current()
_PUBLIC_COIN_SCHEMA = VIEW_SCHEMAS["PublicCoinView"]


def _record(value: object, ordinals: tuple[int, ...], label: str) -> tuple[object, ...]:
    if type(value) is not k1.DatumRecord:
        raise ColdProjectionError(f"{label} is not a record")
    if tuple(item[0] for item in value.fields) != ordinals:
        raise ColdProjectionError(f"{label} has another exact field sequence")
    return tuple(item[1] for item in value.fields)


def _sequence(value: object, label: str) -> tuple[object, ...]:
    if type(value) is not k1.DatumSeq or type(value.values) is not tuple:
        raise ColdProjectionError(f"{label} is not an immutable sequence")
    if len(value.values) > 1 << 14:
        raise ColdProjectionError(f"{label} exceeds the local sequence bound")
    return value.values


def _variant(value: object, cases: set[int], label: str) -> tuple[int, object]:
    if type(value) is not k1.DatumVariant or value.case not in cases:
        raise ColdProjectionError(f"{label} has another variant case")
    return value.case, value.payload


def _nat(value: object, label: str) -> int:
    if type(value) is not k1.Nat:
        raise ColdProjectionError(f"{label} is not a natural")
    return value.value


def _bytes(value: object, label: str) -> bytes:
    if type(value) is not k1.BytesValue or type(value.value) is not bytes:
        raise ColdProjectionError(f"{label} is not exact bytes")
    return value.value


def _unit(value: object, label: str) -> None:
    if type(value) is not k1.Unit:
        raise ColdProjectionError(f"{label} is not Unit")


def _profiled_body(body: bytes, label: str) -> tuple[object, object]:
    if type(body) is not bytes or not body:
        raise ColdProjectionError(f"{label} is not nonempty exact bytes")
    try:
        decoded = k1.decode_datum(body)
        if k1.encode_datum(decoded) != body:
            raise ColdProjectionError(f"{label} is not canonical")
        profile_value, domain = _record(decoded, (0, 1), label)
        profile = k1.decode_content_reference(_bytes(profile_value, f"{label} profile"))
    except ColdProjectionError:
        raise
    except Exception as error:
        raise ColdProjectionError(
            f"{label} does not decode exactly: {error}"
        ) from error
    if (
        profile.subject_kind != k1.SEMANTIC_LANGUAGE_PROFILE_KIND
        or profile.digest.hex() != PROFILE_DIGEST
    ):
        raise ColdProjectionError(f"{label} names another owner profile")
    return profile, domain


def _authenticated_subject(
    body: bytes, reference: bytes, subject_kind: str, label: str
) -> tuple[object, object]:
    profile, domain = _profiled_body(body, label)
    try:
        identifier = k1.decode_content_reference(reference)
        expected = k1.profiled_content_id(
            subject_kind,
            profile,
            domain,
            semantic_regime=k1.SEMANTIC_REGIME_ID,
        )
    except Exception as error:
        raise ColdProjectionError(
            f"{label} identity does not reconstruct: {error}"
        ) from error
    if identifier.subject_kind != subject_kind:
        raise ColdProjectionError(f"{label} reference has another subject kind")
    if expected.internal_reference() != reference:
        raise ColdProjectionError(f"{label} body and reference do not authenticate")
    return profile, domain


def _atom(compiler: str, datum: object) -> dict[str, str]:
    return {"compiler": compiler, "body": k1.encode_datum(datum).hex()}


def _ordinal(compiler: str, ordinal: int) -> dict[str, str]:
    return _atom(compiler, k1.Nat(ordinal))


def _identifier(compiler: str, reference: bytes) -> dict[str, str]:
    return _atom(compiler, k1.BytesValue(reference))


def _value_type(value: object) -> dict[str, str]:
    return _atom("value-type-body-v0", value)


def _value_ref_datum(reference: tuple[int, int, int]) -> object:
    tag, first, second = reference
    if tag < 4:
        return k1.DatumVariant(tag, k1.Nat(first))
    if tag == 4:
        return k1.DatumVariant(
            4,
            k1.DatumRecord(((0, k1.Nat(first)), (1, k1.Nat(second)))),
        )
    raise ColdProjectionError("unknown ValueRef tag")


def _value_ref(reference: tuple[int, int, int]) -> dict[str, str]:
    return _atom("value-ref-body-v0", _value_ref_datum(reference))


def _module_ref(value: object) -> dict[str, str]:
    return _atom("module-declaration-ref-body-v0", value)


def _guard(value: object) -> dict[str, str]:
    return _atom("guard-body-v0", value)


def _law(name: str) -> dict[str, str]:
    return {
        "profile": PROFILE_DIGEST,
        "kind": "pir.semantic-law",
        "name": name,
    }


def _v(case: int, payload: Any = None) -> dict[str, Any]:
    return {"case": case, "value": payload}


def _parse_value_ref(value: object) -> tuple[int, int, int]:
    tag, payload = _variant(value, set(range(5)), "ValueRef")
    if tag < 4:
        return tag, _nat(payload, "ValueRef ordinal"), 0
    occurrence, output = _record(payload, (0, 1), "occurrence-output ref")
    return 4, _nat(occurrence, "output occurrence"), _nat(output, "output ordinal")


def _parse_guard(value: object) -> dict[str, Any]:
    tag, payload = _variant(value, {0, 1}, "Guard")
    if tag == 0:
        _unit(payload, "Always guard payload")
        return {"tag": 0, "body": value, "inputs": ()}
    algorithm, contract, inputs = _record(payload, (0, 1, 2), "Evaluate guard")
    return {
        "tag": 1,
        "body": value,
        "algorithm": _bytes(algorithm, "guard algorithm"),
        "contract": _bytes(contract, "guard contract"),
        "inputs": tuple(
            _parse_value_ref(item) for item in _sequence(inputs, "guard inputs")
        ),
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
            "inputs": (),
        }
    if tag == 1:
        channel, algorithm, contract, inputs, payload_type = _record(
            payload, (0, 1, 2, 3, 4), "Verifier message"
        )
        return {
            "tag": tag,
            "body": value,
            "channel": channel,
            "algorithm": _bytes(algorithm, "Verifier-message algorithm"),
            "contract": _bytes(contract, "Verifier-message contract"),
            "inputs": tuple(
                _parse_value_ref(item)
                for item in _sequence(inputs, "Verifier-message inputs")
            ),
            "payload_type": payload_type,
        }
    if tag == 5:
        return {
            "tag": tag,
            "body": value,
            "terminal": _nat(payload, "terminal backlink"),
            "inputs": (),
        }
    raise ColdProjectionError("Core effect belongs to another B2C1B slice")


def decode_core(domain_body: bytes) -> dict[str, Any]:
    """Strictly decode the exact supported Core domain without owner objects."""

    if type(domain_body) is not bytes or not domain_body:
        raise ColdProjectionError("Core domain body is not nonempty bytes")
    try:
        root = k1.decode_datum(domain_body)
    except Exception as error:
        raise ColdProjectionError(f"Core domain decode failed: {error}") from error
    if k1.encode_datum(root) != domain_body:
        raise ColdProjectionError("Core domain does not round-trip byte-identically")
    fields = _record(root, tuple(range(14)), "InteractiveCore")
    tables = tuple(
        _sequence(field, f"InteractiveCore field {index}")
        for index, field in enumerate(fields)
    )
    if any(tables[index] for index in (7, 8, 9, 10, 11)):
        raise ColdProjectionError("Core contains a constructor from another slice")

    public_inputs = tuple(
        {"type": _record(item, (0,), "public input")[0]} for item in tables[1]
    )
    private_inputs = tuple(
        {"type": _record(item, (0,), "private input")[0]} for item in tables[2]
    )
    constants = tuple(
        {
            "type": _record(item, (0, 1), "constant")[0],
            "value": _record(item, (0, 1), "constant")[1],
        }
        for item in tables[3]
    )
    derived: list[dict[str, Any]] = []
    for item in tables[4]:
        algorithm, contract, inputs, result_type = _record(
            item, (0, 1, 2, 3), "derived value"
        )
        derived.append(
            {
                "algorithm": _bytes(algorithm, "derived algorithm"),
                "contract": _bytes(contract, "derived contract"),
                "inputs": tuple(
                    _parse_value_ref(child)
                    for child in _sequence(inputs, "derived inputs")
                ),
                "type": result_type,
            }
        )

    scopes: list[dict[str, int | None]] = []
    for item in tables[5]:
        parent, opening = _record(item, (0, 1), "scope")
        parent_tag, parent_payload = _variant(parent, {0, 1}, "scope parent")
        opening_tag, opening_payload = _variant(opening, {0, 1}, "scope opening")
        if parent_tag == 0:
            _unit(parent_payload, "absent scope parent")
        if opening_tag == 0:
            _unit(opening_payload, "initial scope opening")
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
            raise ColdProjectionError("terminal belongs to another B2C1B slice")
        terminals.append(
            {
                "verdict": verdict_tag,
                "outputs": tuple(
                    _parse_value_ref(child)
                    for child in _sequence(outputs, "terminal outputs")
                ),
            }
        )

    occurrences: list[dict[str, Any]] = []
    for item in tables[13]:
        scope, guard, effect = _record(item, (0, 1, 2), "occurrence")
        occurrences.append(
            {
                "scope": _nat(scope, "occurrence scope"),
                "guard": _parse_guard(guard),
                "effect": _parse_effect(effect),
            }
        )
    return {
        "used_modules": tuple(_bytes(item, "used module") for item in tables[0]),
        "public_inputs": public_inputs,
        "private_inputs": private_inputs,
        "constants": constants,
        "derived": tuple(derived),
        "scopes": tuple(scopes),
        "bindings": tuple(bindings),
        "terminals": tuple(terminals),
        "occurrences": tuple(occurrences),
    }


def _field(schema: dict[str, Any], ordinal: int) -> dict[str, Any]:
    if schema.get("node") != "record":
        raise ColdProjectionError("expected a compiled record schema")
    for field_ordinal, child in schema["fields"]:
        if field_ordinal == ordinal:
            return child
    raise ColdProjectionError(f"compiled schema lacks field {ordinal}")


_PC_GRAPH_SCHEMA = _field(_PUBLIC_COIN_SCHEMA, 1)
_PC_NODE_SCHEMA = _field(_PC_GRAPH_SCHEMA, 0)["element"]
_PC_EDGE_SCHEMA = _field(_PC_GRAPH_SCHEMA, 1)["element"]


def _scope_paths(core: dict[str, Any]) -> tuple[tuple[int, ...], ...]:
    paths: list[tuple[int, ...]] = []
    for ordinal, scope in enumerate(core["scopes"]):
        parent = scope["parent"]
        if parent is None:
            path = (ordinal,)
        elif not 0 <= parent < ordinal:
            raise ColdProjectionError("scope parent is not an earlier scope")
        else:
            path = (*paths[parent], ordinal)
        if len(path) > 384:
            raise ColdProjectionError("scope path exceeds the target depth")
        paths.append(path)
    return tuple(paths)


def _output_types(core: dict[str, Any]) -> tuple[tuple[object, ...], ...]:
    result: list[tuple[object, ...]] = []
    for occurrence in core["occurrences"]:
        effect = occurrence["effect"]
        result.append((effect["payload_type"],) if effect["tag"] in (0, 1) else ())
    return tuple(result)


def _type_of(
    core: dict[str, Any],
    outputs: tuple[tuple[object, ...], ...],
    reference: tuple[int, int, int],
) -> object:
    tag, first, second = reference
    tables = {
        0: core["public_inputs"],
        1: core["private_inputs"],
        2: core["constants"],
        3: core["derived"],
    }
    if tag in tables:
        table = tables[tag]
        if not 0 <= first < len(table):
            raise ColdProjectionError("ValueRef ordinal is absent")
        return table[first]["type"]
    if tag == 4 and 0 <= first < len(outputs) and 0 <= second < len(outputs[first]):
        return outputs[first][second]
    raise ColdProjectionError("occurrence-output ValueRef is absent")


def _producer(reference: tuple[int, int, int]) -> tuple[int, ...]:
    tag, first, second = reference
    if tag < 4:
        return tag, first
    if tag == 4:
        return 8, first, second
    raise ColdProjectionError("unknown ValueRef producer")


def _pc_value(node: tuple[int, ...]) -> dict[str, Any]:
    tag, *arguments = node
    if tag in (8, 12, 13) and len(arguments) == 2:
        return _v(
            tag,
            {
                0: _ordinal("occurrence-ref-body-v0", arguments[0]),
                1: arguments[1],
            },
        )
    compilers = {
        0: "public-input-ref-body-v0",
        1: "verifier-private-input-ref-body-v0",
        2: "constant-ref-body-v0",
        3: "derived-value-ref-body-v0",
        4: "scope-ref-body-v0",
        5: "binding-ref-body-v0",
        6: "occurrence-ref-body-v0",
        7: "occurrence-ref-body-v0",
        9: "claim-ref-body-v0",
        10: "reduction-ref-body-v0",
        11: "terminal-ref-body-v0",
    }
    if tag not in compilers or len(arguments) != 1:
        raise ColdProjectionError("unknown PCNode coordinate")
    return _v(tag, _ordinal(compilers[tag], arguments[0]))


def _pc_key(node: tuple[int, ...]) -> bytes:
    return codec.encode_value(_PC_NODE_SCHEMA, _pc_value(node))


def _edge_value(pair: tuple[tuple[int, ...], tuple[int, ...]]) -> dict[int, Any]:
    return {0: _pc_value(pair[0]), 1: _pc_value(pair[1])}


def _edge_key(pair: tuple[tuple[int, ...], tuple[int, ...]]) -> bytes:
    return codec.encode_value(_PC_EDGE_SCHEMA, _edge_value(pair))


def _graph(
    core: dict[str, Any], outputs: tuple[tuple[object, ...], ...]
) -> tuple[dict[int, Any], dict[str, Any]]:
    """Derive the supported PCGraph via predecessor sets and a byte-key heap."""

    predecessors: dict[tuple[int, ...], set[tuple[int, ...]]] = {}
    successors: dict[tuple[int, ...], set[tuple[int, ...]]] = {}

    def node(value: tuple[int, ...]) -> tuple[int, ...]:
        predecessors.setdefault(value, set())
        successors.setdefault(value, set())
        return value

    def connect(source: tuple[int, ...], target: tuple[int, ...]) -> None:
        source = node(source)
        target = node(target)
        predecessors[target].add(source)
        successors[source].add(target)

    for index in range(len(core["public_inputs"])):
        node((0, index))
    for index in range(len(core["private_inputs"])):
        node((1, index))
    for index in range(len(core["constants"])):
        node((2, index))
    for index, derived in enumerate(core["derived"]):
        target = node((3, index))
        for reference in derived["inputs"]:
            connect(_producer(reference), target)
    for index, scope in enumerate(core["scopes"]):
        target = node((4, index))
        if scope["parent"] is not None:
            connect((4, scope["parent"]), target)
    for index, binding in enumerate(core["bindings"]):
        target = node((5, index))
        connect((4, binding["scope"]), target)
        connect(_producer(binding["value"]), target)

    terminal_positions: dict[int, int] = {}
    earlier_terminal_nodes: list[tuple[int, ...]] = []
    for occurrence_ref, occurrence in enumerate(core["occurrences"]):
        activity = node((6, occurrence_ref))
        effect_node = node((7, occurrence_ref))
        connect((4, occurrence["scope"]), activity)
        for reference in occurrence["guard"]["inputs"]:
            connect(_producer(reference), activity)
        for prior_terminal in earlier_terminal_nodes:
            connect(prior_terminal, activity)
        connect(activity, effect_node)
        effect = occurrence["effect"]
        if effect["tag"] == 1:
            for reference in effect["inputs"]:
                connect(_producer(reference), effect_node)
        elif effect["tag"] == 5:
            terminal_ref = effect["terminal"]
            for reference in core["terminals"][terminal_ref]["outputs"]:
                connect(_producer(reference), effect_node)
            terminal_node = node((11, terminal_ref))
            connect(effect_node, terminal_node)
            terminal_positions[terminal_ref] = occurrence_ref
            earlier_terminal_nodes.append(terminal_node)
        for output_ref in range(len(outputs[occurrence_ref])):
            connect(effect_node, (8, occurrence_ref, output_ref))

    remaining = {key: len(value) for key, value in predecessors.items()}
    heap: list[tuple[bytes, tuple[int, ...]]] = [
        (_pc_key(key), key) for key, count in remaining.items() if count == 0
    ]
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
        raise ColdProjectionError("supported PCGraph is cyclic")

    classes: dict[tuple[int, ...], int] = {}
    for current in topological:
        inherited = max((classes[item] for item in predecessors[current]), default=0)
        if current[0] == 1:
            assigned = 2
        elif current[0] in (0, 2):
            assigned = 0
        elif current[0] == 7:
            effect_tag = core["occurrences"][current[1]]["effect"]["tag"]
            assigned = 1 if effect_tag == 0 and inherited <= 1 else inherited
        else:
            assigned = inherited
        classes[current] = assigned

    activities = {(6, index) for index in range(len(core["occurrences"]))}
    verifier_message_outputs = {
        (8, index, output)
        for index, occurrence in enumerate(core["occurrences"])
        if occurrence["effect"]["tag"] == 1
        for output in range(len(outputs[index]))
    }
    binding_observations = {(5, index) for index in range(len(core["bindings"]))}
    terminal_nodes = {(11, index) for index in range(len(core["terminals"]))}
    terminal_public_outputs = {
        _producer(reference)
        for terminal in core["terminals"]
        for reference in terminal["outputs"]
    }
    sinks = (
        activities
        | binding_observations
        | verifier_message_outputs
        | terminal_nodes
        | terminal_public_outputs
    )
    accepting_terminals = {
        (11, index)
        for index, terminal in enumerate(core["terminals"])
        if terminal["verdict"] == 0
    }
    acceptance = accepting_terminals | {
        _producer(reference)
        for index, terminal in enumerate(core["terminals"])
        if (11, index) in accepting_terminals
        for reference in terminal["outputs"]
    }
    ordered_nodes = sorted(predecessors, key=_pc_key)
    edges = {
        (source, target)
        for target, sources in predecessors.items()
        for source in sources
    }
    ordered_edges = sorted(edges, key=_edge_key)
    private_predecessors: list[tuple[int, ...]] = []
    for ordinal in range(len(core["private_inputs"])):
        source = (1, ordinal)
        seen = {source}
        pending = [source]
        reaches_sink = False
        while pending:
            current = pending.pop()
            reaches_sink = reaches_sink or current in sinks
            for child in successors[current]:
                if child not in seen:
                    seen.add(child)
                    pending.append(child)
        if reaches_sink:
            private_predecessors.append(source)
    private_predecessors.sort(key=_pc_key)
    graph = {
        0: [_pc_value(current) for current in ordered_nodes],
        1: [_edge_value(pair) for pair in ordered_edges],
        2: [_pc_value(current) for current in topological],
        3: [
            {0: _pc_value(current), 1: _v(classes[current])}
            for current in ordered_nodes
        ],
        4: [_pc_value(current) for current in sorted(sinks, key=_pc_key)],
        5: [_pc_value(current) for current in sorted(acceptance, key=_pc_key)],
        6: [],
    }
    return graph, {
        "eligible": all(classes[current] in (0, 1) for current in sinks),
        "private_predecessors": tuple(private_predecessors),
        "terminal_positions": terminal_positions,
        "classes": classes,
        "nodes": len(predecessors),
        "edges": len(edges),
    }


def _effect_value(effect: dict[str, Any]) -> dict[str, Any]:
    if effect["tag"] == 0:
        return _v(
            0,
            {
                0: _module_ref(effect["channel"]),
                1: _value_type(effect["payload_type"]),
            },
        )
    if effect["tag"] == 1:
        return _v(
            1,
            {
                0: _module_ref(effect["channel"]),
                1: _identifier("algorithm-ref-body-v0", effect["algorithm"]),
                2: _identifier("evaluation-contract-id-body-v0", effect["contract"]),
                3: [_value_ref(item) for item in effect["inputs"]],
                4: _value_type(effect["payload_type"]),
            },
        )
    if effect["tag"] == 5:
        return _v(5, _ordinal("terminal-ref-body-v0", effect["terminal"]))
    raise ColdProjectionError("unsupported effect reached the cold view projector")


def project(
    core_profiled_body: bytes,
    core_reference: bytes,
    protocol_profiled_body: bytes,
    protocol_reference: bytes,
) -> tuple[dict[str, Any], dict[str, Any]]:
    """Project six views from bytes and return bounded derivation evidence."""

    core_profile, core_domain = _authenticated_subject(
        core_profiled_body,
        core_reference,
        "pir.interactive-core",
        "cold Core",
    )
    protocol_profile, protocol_domain = _authenticated_subject(
        protocol_profiled_body,
        protocol_reference,
        "pir.protocol",
        "cold Protocol",
    )
    if protocol_profile != core_profile:
        raise ColdProjectionError("Core and Protocol owner profiles differ")
    protocol_core, interpretation = _record(
        protocol_domain, (0, 1), "cold Protocol domain"
    )
    if _bytes(protocol_core, "cold Protocol Core reference") != core_reference:
        raise ColdProjectionError("Fresh Protocol names another Core")
    interpretation_case, interpretation_body = _variant(
        interpretation, {0}, "cold Protocol interpretation"
    )
    if interpretation_case != 0:
        raise ColdProjectionError("cold Protocol is not Fresh")
    _unit(interpretation_body, "cold Fresh interpretation")

    core = decode_core(k1.encode_datum(core_domain))
    outputs = _output_types(core)
    paths = _scope_paths(core)
    graph, graph_evidence = _graph(core, outputs)
    core_atom = _identifier("core-id-body-v0", core_reference)
    protocol_atom = _identifier("protocol-id-body-v0", protocol_reference)

    public_binding = {
        0: core_atom,
        1: [
            {
                0: _ordinal("scope-ref-body-v0", index),
                1: _v(0)
                if scope["parent"] is None
                else _v(
                    1,
                    _ordinal("scope-ref-body-v0", scope["parent"]),
                ),
                2: _v(0)
                if scope["opening"] is None
                else _v(
                    1,
                    _ordinal("occurrence-ref-body-v0", scope["opening"]),
                ),
                3: [_ordinal("scope-ref-body-v0", item) for item in paths[index]],
            }
            for index, scope in enumerate(core["scopes"])
        ],
        2: [
            {
                0: _ordinal("binding-ref-body-v0", index),
                1: _ordinal("scope-ref-body-v0", binding["scope"]),
                2: _v(binding["class"]),
                3: _value_ref(binding["value"]),
                4: _value_type(_type_of(core, outputs, binding["value"])),
            }
            for index, binding in enumerate(core["bindings"])
        ],
    }

    decisions = tuple(
        (index, occurrence)
        for index, occurrence in enumerate(core["occurrences"])
        if occurrence["effect"]["tag"] == 0
    )
    decision_rows: list[dict[int, Any]] = []
    read_rows: list[dict[int, Any]] = []
    legal_rows: list[dict[int, Any]] = []
    opening_positions = tuple(
        -1 if scope["opening"] is None else scope["opening"] for scope in core["scopes"]
    )
    for occurrence_ref, occurrence in decisions:
        move = _v(0, _value_type(occurrence["effect"]["payload_type"]))
        decision_rows.append(
            {
                0: _ordinal("decision-ref-body-v0", occurrence_ref),
                1: _ordinal("occurrence-ref-body-v0", occurrence_ref),
                2: [
                    _ordinal("scope-ref-body-v0", item)
                    for item in paths[occurrence["scope"]]
                ],
                3: _guard(occurrence["guard"]["body"]),
                4: move,
                5: [
                    _ordinal("decision-ref-body-v0", prior)
                    for prior, _item in decisions
                    if prior < occurrence_ref
                ],
            }
        )
        for index, constant in enumerate(core["constants"]):
            read_rows.append(
                {
                    0: _ordinal("decision-ref-body-v0", occurrence_ref),
                    1: _v(0, _ordinal("constant-ref-body-v0", index)),
                    2: _value_type(constant["type"]),
                }
            )
        for index, declaration in enumerate(core["public_inputs"]):
            boundaries = tuple(
                opening_positions[binding["scope"]]
                for binding in core["bindings"]
                if binding["value"] == (0, index, 0)
            )
            if boundaries and min(boundaries) <= occurrence_ref:
                read_rows.append(
                    {
                        0: _ordinal("decision-ref-body-v0", occurrence_ref),
                        1: _v(1, _ordinal("public-input-ref-body-v0", index)),
                        2: _value_type(declaration["type"]),
                    }
                )
        for index, binding in enumerate(core["bindings"]):
            if opening_positions[binding["scope"]] <= occurrence_ref:
                read_rows.append(
                    {
                        0: _ordinal("decision-ref-body-v0", occurrence_ref),
                        1: _v(2, _ordinal("binding-ref-body-v0", index)),
                        2: _value_type(_type_of(core, outputs, binding["value"])),
                    }
                )
        for prior_ref, prior_occurrence in enumerate(
            core["occurrences"][:occurrence_ref]
        ):
            prior_effect = prior_occurrence["effect"]
            source_guard = prior_occurrence["guard"]
            use_guard = occurrence["guard"]
            guard_implies = (
                source_guard["tag"] == 0 or use_guard["body"] == source_guard["body"]
            )
            if prior_effect["tag"] in (0, 1) and guard_implies:
                read_rows.append(
                    {
                        0: _ordinal("decision-ref-body-v0", occurrence_ref),
                        1: _v(3, _ordinal("occurrence-ref-body-v0", prior_ref)),
                        2: _value_type(prior_effect["payload_type"]),
                    }
                )
                if prior_effect["tag"] == 0:
                    read_rows.append(
                        {
                            0: _ordinal("decision-ref-body-v0", occurrence_ref),
                            1: _v(9, _ordinal("decision-ref-body-v0", prior_ref)),
                            2: _value_type(prior_effect["payload_type"]),
                        }
                    )
        legal_rows.append(
            {0: _ordinal("decision-ref-body-v0", occurrence_ref), 1: move}
        )
    strategy = {
        0: core_atom,
        1: decision_rows,
        2: _law("core-admission-v0"),
        3: read_rows,
        4: legal_rows,
    }

    public_coin = {
        0: core_atom,
        1: graph,
        2: graph_evidence["eligible"],
        3: [_pc_value(item) for item in graph_evidence["private_predecessors"]],
        4: [],
    }

    value_rows: list[dict[int, Any]] = []
    for tag, name in (
        (0, "public_inputs"),
        (1, "private_inputs"),
        (2, "constants"),
        (3, "derived"),
    ):
        for index, declaration in enumerate(core[name]):
            predecessors = declaration["inputs"] if tag == 3 else ()
            value_rows.append(
                {
                    0: _value_ref((tag, index, 0)),
                    1: _value_type(declaration["type"]),
                    2: [_value_ref(item) for item in predecessors],
                }
            )

    occurrence_rows: list[dict[int, Any]] = []
    message_rows: list[dict[int, Any]] = []
    for occurrence_ref, occurrence in enumerate(core["occurrences"]):
        effect = occurrence["effect"]
        occurrence_rows.append(
            {
                0: _ordinal("occurrence-ref-body-v0", occurrence_ref),
                1: [
                    _ordinal("scope-ref-body-v0", item)
                    for item in paths[occurrence["scope"]]
                ],
                2: _guard(occurrence["guard"]["body"]),
                3: _effect_value(effect),
                4: [_value_type(item) for item in outputs[occurrence_ref]],
            }
        )
        if effect["tag"] == 0:
            message_rows.append(
                {
                    0: _ordinal("occurrence-ref-body-v0", occurrence_ref),
                    1: _v(0),
                    2: _v(
                        0,
                        {
                            0: _module_ref(effect["channel"]),
                            1: _value_type(effect["payload_type"]),
                        },
                    ),
                }
            )
        elif effect["tag"] == 1:
            message_rows.append(
                {
                    0: _ordinal("occurrence-ref-body-v0", occurrence_ref),
                    1: _v(1),
                    2: _v(
                        1,
                        {
                            0: _module_ref(effect["channel"]),
                            1: _identifier(
                                "algorithm-ref-body-v0", effect["algorithm"]
                            ),
                            2: _identifier(
                                "evaluation-contract-id-body-v0",
                                effect["contract"],
                            ),
                            3: [_value_ref(item) for item in effect["inputs"]],
                            4: _value_type(effect["payload_type"]),
                        },
                    ),
                }
            )
        for output_ordinal, output_type in enumerate(outputs[occurrence_ref]):
            predecessors = effect["inputs"] if effect["tag"] == 1 else ()
            value_rows.append(
                {
                    0: _value_ref((4, occurrence_ref, output_ordinal)),
                    1: _value_type(output_type),
                    2: [_value_ref(item) for item in predecessors],
                }
            )

    terminal_rows = [
        {
            0: _ordinal("terminal-ref-body-v0", index),
            1: _v(terminal["verdict"]),
            2: [_value_ref(item) for item in terminal["outputs"]],
            3: [],
            4: [],
            5: _ordinal(
                "occurrence-ref-body-v0",
                graph_evidence["terminal_positions"][index],
            ),
        }
        for index, terminal in enumerate(core["terminals"])
    ]
    effect_view = {
        0: core_atom,
        1: occurrence_rows,
        2: value_rows,
        3: message_rows,
        4: [],
        5: [],
        6: terminal_rows,
        7: [],
    }

    runtime = {
        0: [
            {
                0: _ordinal("occurrence-ref-body-v0", index),
                1: [_value_type(item) for item in outputs[index]],
            }
            for index in range(len(core["occurrences"]))
        ],
        1: [],
        2: [],
        3: [
            {
                0: _ordinal("terminal-ref-body-v0", index),
                1: _ordinal(
                    "occurrence-ref-body-v0",
                    graph_evidence["terminal_positions"][index],
                ),
                2: _v(terminal["verdict"]),
                3: [
                    _value_type(_type_of(core, outputs, item))
                    for item in terminal["outputs"]
                ],
            }
            for index, terminal in enumerate(core["terminals"])
        ],
    }
    execution = {
        0: protocol_atom,
        1: core_atom,
        2: _v(0),
        3: _law("core-admission-v0"),
        4: [],
        5: _law("execution-and-replay-v0"),
        6: runtime,
        7: _v(0),
        8: _law("execution-and-replay-v0"),
        9: _law("run-view-issuance-v0"),
    }
    views = {
        "PublicBindingView": public_binding,
        "StrategyDecisionView": strategy,
        "PublicCoinView": public_coin,
        "EffectView": effect_view,
        "ClaimReductionView": {0: core_atom, 1: [], 2: [], 3: []},
        "ExecutionView": execution,
    }
    evidence = {
        "occurrences": len(core["occurrences"]),
        "decisions": len(decision_rows),
        "guaranteed_reads": len(read_rows),
        "values": len(value_rows),
        "messages": len(message_rows),
        "private_predecessors": len(graph_evidence["private_predecessors"]),
        "pc_graph": {
            "nodes": graph_evidence["nodes"],
            "edges": graph_evidence["edges"],
            "eligible": graph_evidence["eligible"],
        },
    }
    return views, evidence


def encode_views(views: dict[str, Any]) -> dict[str, bytes]:
    if tuple(views) != tuple(b2b.load_source()["view_order"]):
        raise ColdProjectionError("cold view table is incomplete or reordered")
    return {
        name: codec.encode_value(VIEW_SCHEMAS[name], value)
        for name, value in views.items()
    }
