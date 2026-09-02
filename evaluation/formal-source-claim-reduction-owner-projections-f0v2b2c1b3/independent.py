"""Cold byte-derived claim/reduction projector for F0-V2B2C1B3.

This module authenticates complete Core and Fresh Protocol bytes, decodes them
into plain records, and independently derives all six owner views.  It does
not import the typed B2C1B3 evaluator or trust its retained Python objects.
"""

from __future__ import annotations

import heapq
import importlib.util
from pathlib import Path
import sys
from types import ModuleType
from typing import Any


ROOT = Path(__file__).resolve().parents[2]
PREDECESSOR_COLD = (
    ROOT
    / "evaluation"
    / "formal-source-oracle-owner-projections-f0v2b2c1b2"
    / "independent.py"
)


class ColdClaimReductionError(ValueError):
    """Fail-closed result from the independent byte-derived projector."""


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


prior = _load("_zkc_f0v2b2c1b3_cold_predecessor", PREDECESSOR_COLD)
cold = prior.cold
k1 = cold.k1
b2b = cold.b2b
codec = cold.codec
VIEW_SCHEMAS = cold.VIEW_SCHEMAS
PROFILE_DIGEST = cold.PROFILE_DIGEST


def _record(value: object, ordinals: tuple[int, ...], label: str) -> tuple[object, ...]:
    try:
        return cold._record(value, ordinals, label)
    except Exception as error:
        raise ColdClaimReductionError(str(error)) from error


def _sequence(value: object, label: str) -> tuple[object, ...]:
    try:
        return cold._sequence(value, label)
    except Exception as error:
        raise ColdClaimReductionError(str(error)) from error


def _variant(value: object, cases: set[int], label: str) -> tuple[int, object]:
    try:
        return cold._variant(value, cases, label)
    except Exception as error:
        raise ColdClaimReductionError(str(error)) from error


def _nat(value: object, label: str) -> int:
    try:
        return cold._nat(value, label)
    except Exception as error:
        raise ColdClaimReductionError(str(error)) from error


def _bytes(value: object, label: str) -> bytes:
    try:
        return cold._bytes(value, label)
    except Exception as error:
        raise ColdClaimReductionError(str(error)) from error


def _unit(value: object, label: str) -> None:
    try:
        cold._unit(value, label)
    except Exception as error:
        raise ColdClaimReductionError(str(error)) from error


def _parse_value_ref(value: object) -> tuple[int, int, int]:
    try:
        return cold._parse_value_ref(value)
    except Exception as error:
        raise ColdClaimReductionError(str(error)) from error


def _parse_guard(value: object) -> dict[str, Any]:
    try:
        return cold._parse_guard(value)
    except Exception as error:
        raise ColdClaimReductionError(str(error)) from error


def _parse_challenge(value: object) -> dict[str, Any]:
    fields = _record(value, tuple(range(7)), "Challenge")
    correlation_tag, correlation_payload = _variant(
        fields[4], {0, 1}, "coin correlation"
    )
    if correlation_tag == 0:
        _unit(correlation_payload, "independent correlation")
        correlation = {"tag": 0, "body": fields[4], "prior": ()}
    else:
        group, index, prior_members = _record(
            correlation_payload, (0, 1, 2), "joint correlation"
        )
        correlation = {
            "tag": 1,
            "body": fields[4],
            "group": group,
            "index": _nat(index, "joint index"),
            "prior": tuple(
                _nat(item, "prior joint member")
                for item in _sequence(prior_members, "prior joint members")
            ),
        }
    use_tag, use_payload = _variant(fields[5], {0, 1}, "reduction use")
    if use_tag == 0:
        _unit(use_payload, "exclusive reduction use")
        reduction_use = {"tag": 0, "body": fields[5]}
    else:
        reduction_use = {"tag": 1, "body": fields[5], "contract": use_payload}
    return {
        "scope": _nat(fields[0], "challenge scope"),
        "type": fields[1],
        "domain": fields[2],
        "fresh_law": fields[3],
        "correlation": correlation,
        "reduction_use": reduction_use,
        "conditions": tuple(
            _parse_value_ref(item)
            for item in _sequence(fields[6], "challenge conditions")
        ),
    }


def _parse_claim(value: object) -> dict[str, Any]:
    contract, scope, usage, source = _record(value, (0, 1, 2, 3), "claim")
    usage_tag, usage_payload = _variant(usage, {0, 1}, "claim usage")
    _unit(usage_payload, "claim usage payload")
    source_tag, source_payload = _variant(source, {0, 1}, "claim source")
    if source_tag == 0:
        parsed_source = {
            "tag": 0,
            "body": source,
            "binding": _nat(source_payload, "claim source binding"),
        }
    else:
        reduction, output = _record(
            source_payload, (0, 1), "reduction-output claim source"
        )
        parsed_source = {
            "tag": 1,
            "body": source,
            "reduction": _nat(reduction, "source reduction"),
            "output": _nat(output, "source output ordinal"),
        }
    return {
        "contract": contract,
        "scope": _nat(scope, "claim scope"),
        "usage": usage_tag,
        "source": parsed_source,
    }


def _parse_reduction(value: object) -> dict[str, Any]:
    fields = _record(value, tuple(range(7)), "reduction")
    publications: list[dict[str, int | None]] = []
    for item in _sequence(fields[5], "required publications"):
        publication, next_challenge = _record(item, (0, 1), "publication requirement")
        next_tag, next_payload = _variant(next_challenge, {0, 1}, "next challenge")
        if next_tag == 0:
            _unit(next_payload, "absent next challenge")
        publications.append(
            {
                "publication": _nat(publication, "publication occurrence"),
                "next_challenge": None
                if next_tag == 0
                else _nat(next_payload, "next challenge"),
            }
        )
    return {
        "contract": fields[0],
        "scope": _nat(fields[1], "reduction scope"),
        "input_claims": tuple(
            _nat(item, "input claim") for item in _sequence(fields[2], "input claims")
        ),
        "side_inputs": tuple(
            _parse_value_ref(item) for item in _sequence(fields[3], "side inputs")
        ),
        "required_challenges": tuple(
            _nat(item, "required challenge")
            for item in _sequence(fields[4], "required challenges")
        ),
        "required_publications": tuple(publications),
        "output_contracts": _sequence(fields[6], "output contracts"),
    }


def _parse_terminal(value: object) -> dict[str, Any]:
    verdict, outputs, checks, dispositions = _record(value, (0, 1, 2, 3), "terminal")
    verdict_tag, verdict_payload = _variant(verdict, {0, 1, 2}, "verdict")
    _unit(verdict_payload, "verdict payload")
    if _sequence(checks, "terminal checks"):
        raise ColdClaimReductionError("terminal checks belong to another slice")
    parsed_dispositions: list[dict[str, int]] = []
    for item in _sequence(dispositions, "terminal dispositions"):
        claim, disposition = _record(item, (0, 1), "claim disposition")
        disposition_tag, disposition_payload = _variant(
            disposition, {0, 1}, "claim disposition"
        )
        _unit(disposition_payload, "claim disposition payload")
        parsed_dispositions.append(
            {
                "claim": _nat(claim, "disposed claim"),
                "disposition": disposition_tag,
            }
        )
    return {
        "verdict": verdict_tag,
        "outputs": tuple(
            _parse_value_ref(item) for item in _sequence(outputs, "terminal outputs")
        ),
        "dispositions": tuple(parsed_dispositions),
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
    if tag == 2:
        return {
            "tag": tag,
            "body": value,
            "challenge": _nat(payload, "challenge backlink"),
        }
    if tag == 4:
        return {
            "tag": tag,
            "body": value,
            "reduction": _nat(payload, "reduction backlink"),
        }
    if tag == 5:
        return {
            "tag": tag,
            "body": value,
            "terminal": _nat(payload, "terminal backlink"),
        }
    raise ColdClaimReductionError(f"effect tag {tag} belongs to another slice")


def decode_core(domain_body: bytes) -> dict[str, Any]:
    """Decode canonical Core domain bytes without typed-owner objects."""

    if type(domain_body) is not bytes or not domain_body:
        raise ColdClaimReductionError("Core domain body is not exact bytes")
    try:
        root = k1.decode_datum(domain_body)
    except Exception as error:
        raise ColdClaimReductionError(
            f"Core domain does not decode: {error}"
        ) from error
    if k1.encode_datum(root) != domain_body:
        raise ColdClaimReductionError("Core domain does not round-trip")
    fields = _record(root, tuple(range(14)), "InteractiveCore")
    tables = tuple(
        _sequence(value, f"InteractiveCore field {index}")
        for index, value in enumerate(fields)
    )
    if any(tables[index] for index in (2, 4, 8, 9)):
        raise ColdClaimReductionError("Core contains another constructor slice")
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
    occurrences = tuple(
        {
            "scope": _nat(
                _record(item, (0, 1, 2), "occurrence")[0], "occurrence scope"
            ),
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
        "challenges": tuple(_parse_challenge(item) for item in tables[7]),
        "claims": tuple(_parse_claim(item) for item in tables[10]),
        "reductions": tuple(_parse_reduction(item) for item in tables[11]),
        "terminals": tuple(_parse_terminal(item) for item in tables[12]),
        "occurrences": occurrences,
    }


def _value_type_body(value: object) -> dict[str, str]:
    return cold._value_type(value)


def _output_types(core: dict[str, Any]) -> tuple[tuple[object, ...], ...]:
    outputs: list[tuple[object, ...]] = []
    for occurrence in core["occurrences"]:
        effect = occurrence["effect"]
        if effect["tag"] == 0:
            outputs.append((effect["payload_type"],))
        elif effect["tag"] == 2:
            outputs.append((core["challenges"][effect["challenge"]]["type"],))
        else:
            outputs.append(())
    return tuple(outputs)


def _scope_paths(core: dict[str, Any]) -> tuple[tuple[int, ...], ...]:
    paths: list[tuple[int, ...]] = []
    for index in range(len(core["scopes"])):
        current: int | None = index
        path: list[int] = []
        seen: set[int] = set()
        while current is not None:
            if current in seen or not 0 <= current < len(core["scopes"]):
                raise ColdClaimReductionError("scope path is cyclic or absent")
            seen.add(current)
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
    try:
        if tag == 0:
            return core["public_inputs"][first]["type"]
        if tag == 2:
            return core["constants"][first]["type"]
        if tag == 4:
            return outputs[first][second]
    except (IndexError, KeyError) as error:
        raise ColdClaimReductionError("ValueRef is absent") from error
    raise ColdClaimReductionError("ValueRef belongs to another slice")


def _producer(reference: tuple[int, int, int]) -> tuple[int, ...]:
    tag, first, second = reference
    if tag in (0, 2):
        return tag, first
    if tag == 4:
        return 8, first, second
    raise ColdClaimReductionError("producer belongs to another slice")


def _exact_positions(
    core: dict[str, Any], effect_tag: int, table: str, backlink: str
) -> dict[int, int]:
    positions: dict[int, list[int]] = {index: [] for index in range(len(core[table]))}
    for occurrence_ref, occurrence in enumerate(core["occurrences"]):
        effect = occurrence["effect"]
        if effect["tag"] == effect_tag:
            try:
                positions[effect[backlink]].append(occurrence_ref)
            except KeyError as error:
                raise ColdClaimReductionError(
                    f"{backlink} backlink is absent"
                ) from error
    if any(len(value) != 1 for value in positions.values()):
        raise ColdClaimReductionError(f"{table} backlinks are not one-to-one")
    return {key: value[0] for key, value in positions.items()}


def _derived_facts(core: dict[str, Any]) -> dict[str, Any]:
    challenge_positions = _exact_positions(core, 2, "challenges", "challenge")
    reduction_positions = _exact_positions(core, 4, "reductions", "reduction")
    terminal_positions = _exact_positions(core, 5, "terminals", "terminal")
    reduction_consumers: dict[int, list[int]] = {
        index: [] for index in range(len(core["challenges"]))
    }
    claim_uses: dict[int, list[tuple[str, int, int, int]]] = {
        index: [] for index in range(len(core["claims"]))
    }
    for reduction_ref, reduction in enumerate(core["reductions"]):
        occurrence_ref = reduction_positions[reduction_ref]
        for ordinal, claim_ref in enumerate(reduction["input_claims"]):
            if claim_ref not in claim_uses:
                raise ColdClaimReductionError("reduction input claim is absent")
            claim_uses[claim_ref].append(
                ("reduction", occurrence_ref, reduction_ref, ordinal)
            )
        for challenge_ref in reduction["required_challenges"]:
            if challenge_ref not in reduction_consumers:
                raise ColdClaimReductionError("required Challenge is absent")
            reduction_consumers[challenge_ref].append(reduction_ref)
    for terminal_ref, terminal in enumerate(core["terminals"]):
        occurrence_ref = terminal_positions[terminal_ref]
        for ordinal, disposition in enumerate(terminal["dispositions"]):
            claim_ref = disposition["claim"]
            if claim_ref not in claim_uses:
                raise ColdClaimReductionError("terminal claim is absent")
            claim_uses[claim_ref].append(
                ("terminal", occurrence_ref, terminal_ref, ordinal)
            )
    for challenge_ref, consumers in reduction_consumers.items():
        consumers.sort(key=lambda item: (reduction_positions[item], item))
        reduction_consumers[challenge_ref] = consumers
    return {
        "challenge_positions": challenge_positions,
        "reduction_positions": reduction_positions,
        "terminal_positions": terminal_positions,
        "reduction_consumers": {
            key: tuple(value) for key, value in reduction_consumers.items()
        },
        "claim_uses": {key: tuple(value) for key, value in claim_uses.items()},
    }


def _pc_value(node: tuple[int, ...]) -> dict[str, Any]:
    tag, *arguments = node
    if tag in (8, 12, 13):
        if len(arguments) != 2:
            raise ColdClaimReductionError("PCNode output arity differs")
        return cold._v(
            tag,
            {
                0: cold._ordinal("occurrence-ref-body-v0", arguments[0]),
                1: arguments[1],
            },
        )
    compiler = {
        0: "public-input-ref-body-v0",
        2: "constant-ref-body-v0",
        4: "scope-ref-body-v0",
        5: "binding-ref-body-v0",
        6: "occurrence-ref-body-v0",
        7: "occurrence-ref-body-v0",
        9: "claim-ref-body-v0",
        10: "reduction-ref-body-v0",
        11: "terminal-ref-body-v0",
    }.get(tag)
    if compiler is None or len(arguments) != 1:
        raise ColdClaimReductionError("PCNode belongs to another slice")
    return cold._v(tag, cold._ordinal(compiler, arguments[0]))


def _record_field(schema: dict[str, Any], ordinal: int) -> dict[str, Any]:
    selected = [child for field, child in schema["fields"] if field == ordinal]
    if len(selected) != 1:
        raise ColdClaimReductionError(f"record has no unique field {ordinal}")
    return selected[0]


_PC_GRAPH_SCHEMA = prior._PC_GRAPH_SCHEMA
_PC_NODE_SCHEMA = prior._PC_NODE_SCHEMA
_PC_EDGE_SCHEMA = prior._PC_EDGE_SCHEMA
_READ_SCHEMA = _record_field(VIEW_SCHEMAS["StrategyDecisionView"], 3)["element"]


def _pc_key(node: tuple[int, ...]) -> bytes:
    return codec.encode_value(_PC_NODE_SCHEMA, _pc_value(node))


def _edge_value(pair: tuple[tuple[int, ...], tuple[int, ...]]) -> dict[int, Any]:
    return {0: _pc_value(pair[0]), 1: _pc_value(pair[1])}


def _edge_key(pair: tuple[tuple[int, ...], tuple[int, ...]]) -> bytes:
    return codec.encode_value(_PC_EDGE_SCHEMA, _edge_value(pair))


def _graph(
    core: dict[str, Any],
    outputs: tuple[tuple[object, ...], ...],
    facts: dict[str, Any],
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

    prior_terminals: list[tuple[int, ...]] = []
    for occurrence_ref, occurrence in enumerate(core["occurrences"]):
        activity, effect_node = node((6, occurrence_ref)), node((7, occurrence_ref))
        connect((4, occurrence["scope"]), activity)
        for reference in occurrence["guard"]["inputs"]:
            connect(_producer(reference), activity)
        for terminal in prior_terminals:
            connect(terminal, activity)
        connect(activity, effect_node)
        effect = occurrence["effect"]
        if effect["tag"] == 2:
            challenge = core["challenges"][effect["challenge"]]
            for condition in challenge["conditions"]:
                connect(_producer(condition), effect_node)
            for prior_member in challenge["correlation"]["prior"]:
                connect(
                    (8, facts["challenge_positions"][prior_member], 0),
                    effect_node,
                )
        elif effect["tag"] == 4:
            reduction = core["reductions"][effect["reduction"]]
            for claim_ref in reduction["input_claims"]:
                connect((9, claim_ref), effect_node)
            for side_input in reduction["side_inputs"]:
                connect(_producer(side_input), effect_node)
            for challenge_ref in reduction["required_challenges"]:
                connect(
                    (8, facts["challenge_positions"][challenge_ref], 0),
                    effect_node,
                )
            for requirement in reduction["required_publications"]:
                connect((7, requirement["publication"]), effect_node)
            connect(effect_node, (10, effect["reduction"]))
        elif effect["tag"] == 5:
            terminal = core["terminals"][effect["terminal"]]
            for output in terminal["outputs"]:
                connect(_producer(output), effect_node)
            for disposition in terminal["dispositions"]:
                connect((9, disposition["claim"]), effect_node)
            connect(effect_node, (11, effect["terminal"]))
            prior_terminals.append((11, effect["terminal"]))
        for output_ordinal in range(len(outputs[occurrence_ref])):
            connect(effect_node, (8, occurrence_ref, output_ordinal))

    for claim_ref, claim in enumerate(core["claims"]):
        source = claim["source"]
        if source["tag"] == 0:
            connect((5, source["binding"]), (9, claim_ref))
        else:
            connect((10, source["reduction"]), (9, claim_ref))
    for reduction_ref, occurrence_ref in facts["reduction_positions"].items():
        connect((7, occurrence_ref), (10, reduction_ref))

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
        raise ColdClaimReductionError("claim/reduction PCGraph is cyclic")

    classes: dict[tuple[int, ...], int] = {}
    challenge_validity: dict[int, bool] = {}
    for current in topological:
        joined = max((classes[item] for item in predecessors[current]), default=0)
        if current[0] in (0, 2):
            assigned = 0
        elif current[0] == 7:
            effect = core["occurrences"][current[1]]["effect"]
            if effect["tag"] == 0:
                activity_class = classes[(6, current[1])]
                assigned = 1 if activity_class <= 1 else activity_class
            elif effect["tag"] == 2:
                challenge = core["challenges"][effect["challenge"]]
                activity_class = classes[(6, current[1])]
                condition_classes = [
                    classes[_producer(item)] for item in challenge["conditions"]
                ]
                prior_classes = [
                    classes[(8, facts["challenge_positions"][item], 0)]
                    for item in challenge["correlation"]["prior"]
                ]
                dependencies = [activity_class, *condition_classes, *prior_classes]
                if 3 in dependencies:
                    assigned = 3
                elif 2 in dependencies:
                    assigned = 2
                elif any(item != 0 for item in condition_classes) or any(
                    item != 1 for item in prior_classes
                ):
                    assigned = 3
                elif activity_class <= 1:
                    assigned = 1
                else:  # pragma: no cover - closed lattice cases above
                    assigned = 3
                challenge_validity[effect["challenge"]] = assigned == 1
            else:
                assigned = joined
        else:
            assigned = joined
        classes[current] = assigned

    activities = {(6, index) for index in range(len(core["occurrences"]))}
    challenge_sinks = {
        (7, occurrence) for occurrence in facts["challenge_positions"].values()
    }
    reduction_sinks = {(10, index) for index in range(len(core["reductions"]))}
    terminal_sinks = {(11, index) for index in range(len(core["terminals"]))}
    public_observations = {
        (8, occurrence_ref, 0)
        for occurrence_ref, occurrence in enumerate(core["occurrences"])
        if occurrence["effect"]["tag"] == 0
    }
    terminal_outputs = {
        _producer(output)
        for terminal in core["terminals"]
        for output in terminal["outputs"]
    }
    sinks = (
        activities
        | challenge_sinks
        | reduction_sinks
        | terminal_sinks
        | public_observations
        | terminal_outputs
    )
    accepting_terminals = {
        (11, terminal_ref)
        for terminal_ref, terminal in enumerate(core["terminals"])
        if terminal["verdict"] == 0
    }
    acceptance = (
        reduction_sinks
        | accepting_terminals
        | {
            _producer(output)
            for terminal_ref, terminal in enumerate(core["terminals"])
            if (11, terminal_ref) in accepting_terminals
            for output in terminal["outputs"]
        }
    )
    eligible = all(classes[item] in (0, 1) for item in sinks) and all(
        challenge_validity.get(index, False) for index in range(len(core["challenges"]))
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
        6: [],
    }
    return graph, {
        "nodes": len(predecessors),
        "edges": len(edges),
        "eligible": eligible,
        "classes": classes,
        "challenge_validity": challenge_validity,
        "acceptance_sinks": len(acceptance),
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
    compiler = {
        2: "challenge-ref-body-v0",
        4: "reduction-ref-body-v0",
        5: "terminal-ref-body-v0",
    }
    key = {2: "challenge", 4: "reduction", 5: "terminal"}
    if effect["tag"] not in compiler:
        raise ColdClaimReductionError("effect belongs to another slice")
    return cold._v(
        effect["tag"],
        cold._ordinal(compiler[effect["tag"]], effect[key[effect["tag"]]]),
    )


def _claim_source_value(source: dict[str, Any]) -> dict[str, Any]:
    if source["tag"] == 0:
        return cold._v(0, cold._ordinal("binding-ref-body-v0", source["binding"]))
    return cold._v(
        1,
        {
            0: cold._ordinal("reduction-ref-body-v0", source["reduction"]),
            1: source["output"],
        },
    )


def _claim_creation_value(
    core: dict[str, Any], facts: dict[str, Any], source: dict[str, Any]
) -> dict[str, Any]:
    if source["tag"] == 0:
        binding = source["binding"]
        scope = core["bindings"][binding]["scope"]
        opening = core["scopes"][scope]["opening"]
        return cold._v(
            0,
            {
                0: cold._ordinal("binding-ref-body-v0", binding),
                1: cold._v(0)
                if opening is None
                else cold._v(1, cold._ordinal("occurrence-ref-body-v0", opening)),
            },
        )
    return cold._v(
        1,
        {
            0: cold._ordinal(
                "occurrence-ref-body-v0",
                facts["reduction_positions"][source["reduction"]],
            ),
            1: cold._ordinal("reduction-ref-body-v0", source["reduction"]),
            2: source["output"],
        },
    )


def _correlation_value(value: dict[str, Any]) -> dict[str, Any]:
    if value["tag"] == 0:
        return cold._v(0)
    return cold._v(
        1,
        {
            0: cold._module_ref(value["group"]),
            1: value["index"],
            2: [
                cold._ordinal("challenge-ref-body-v0", item) for item in value["prior"]
            ],
        },
    )


def _reduction_use_value(value: dict[str, Any]) -> dict[str, Any]:
    if value["tag"] == 0:
        return cold._v(0)
    return cold._v(1, cold._module_ref(value["contract"]))


def _publication_value(requirement: dict[str, int | None]) -> dict[int, Any]:
    next_challenge = requirement["next_challenge"]
    return {
        0: cold._ordinal("occurrence-ref-body-v0", requirement["publication"]),
        1: cold._v(0)
        if next_challenge is None
        else cold._v(1, cold._ordinal("challenge-ref-body-v0", next_challenge)),
    }


def project(
    core_profiled_body: bytes,
    core_reference: bytes,
    protocol_profiled_body: bytes,
    protocol_reference: bytes,
) -> tuple[dict[str, Any], dict[str, Any]]:
    """Authenticate exact bytes and independently derive all owner views."""

    try:
        core_profile, core_domain = cold._authenticated_subject(
            core_profiled_body,
            core_reference,
            "pir.interactive-core",
            "cold claim/reduction Core",
        )
        protocol_profile, protocol_domain = cold._authenticated_subject(
            protocol_profiled_body,
            protocol_reference,
            "pir.protocol",
            "cold claim/reduction Protocol",
        )
    except Exception as error:
        raise ColdClaimReductionError(str(error)) from error
    if protocol_profile != core_profile:
        raise ColdClaimReductionError("Core and Protocol profiles differ")
    protocol_core, interpretation = _record(
        protocol_domain, (0, 1), "cold Protocol domain"
    )
    if _bytes(protocol_core, "Protocol Core") != core_reference:
        raise ColdClaimReductionError("Fresh Protocol names another Core")
    interpretation_tag, interpretation_payload = _variant(
        interpretation, {0}, "Fresh interpretation"
    )
    if interpretation_tag != 0:  # pragma: no cover - parser set closes this
        raise ColdClaimReductionError("Protocol is not Fresh")
    _unit(interpretation_payload, "Fresh payload")

    core = decode_core(k1.encode_datum(core_domain))
    outputs = _output_types(core)
    paths = _scope_paths(core)
    facts = _derived_facts(core)
    graph, graph_evidence = _graph(core, outputs, facts)
    core_atom = cold._identifier("core-id-body-v0", core_reference)
    protocol_atom = cold._identifier("protocol-id-body-v0", protocol_reference)

    public_binding = {
        0: core_atom,
        1: [
            {
                0: cold._ordinal("scope-ref-body-v0", scope_ref),
                1: cold._v(0)
                if scope["parent"] is None
                else cold._v(1, cold._ordinal("scope-ref-body-v0", scope["parent"])),
                2: cold._v(0)
                if scope["opening"] is None
                else cold._v(
                    1,
                    cold._ordinal("occurrence-ref-body-v0", scope["opening"]),
                ),
                3: [
                    cold._ordinal("scope-ref-body-v0", item)
                    for item in paths[scope_ref]
                ],
            }
            for scope_ref, scope in enumerate(core["scopes"])
        ],
        2: [
            {
                0: cold._ordinal("binding-ref-body-v0", binding_ref),
                1: cold._ordinal("scope-ref-body-v0", binding["scope"]),
                2: cold._v(binding["class"]),
                3: cold._value_ref(binding["value"]),
                4: _value_type_body(_type_of(core, outputs, binding["value"])),
            }
            for binding_ref, binding in enumerate(core["bindings"])
        ],
    }

    decisions = [
        (occurrence_ref, occurrence)
        for occurrence_ref, occurrence in enumerate(core["occurrences"])
        if occurrence["effect"]["tag"] == 0
    ]
    decision_rows: list[dict[int, Any]] = []
    read_rows: list[dict[int, Any]] = []
    legal_rows: list[dict[int, Any]] = []
    for occurrence_ref, occurrence in decisions:
        move = cold._v(0, _value_type_body(occurrence["effect"]["payload_type"]))
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
                    for prior, _prior_occurrence in decisions
                    if prior < occurrence_ref
                ],
            }
        )
        for input_ref, declaration in enumerate(core["public_inputs"]):
            read_rows.append(
                {
                    0: cold._ordinal("decision-ref-body-v0", occurrence_ref),
                    1: cold._v(1, cold._ordinal("public-input-ref-body-v0", input_ref)),
                    2: _value_type_body(declaration["type"]),
                }
            )
        for constant_ref, declaration in enumerate(core["constants"]):
            read_rows.append(
                {
                    0: cold._ordinal("decision-ref-body-v0", occurrence_ref),
                    1: cold._v(0, cold._ordinal("constant-ref-body-v0", constant_ref)),
                    2: _value_type_body(declaration["type"]),
                }
            )
        for binding_ref, binding in enumerate(core["bindings"]):
            if binding["scope"] in paths[occurrence["scope"]]:
                read_rows.append(
                    {
                        0: cold._ordinal("decision-ref-body-v0", occurrence_ref),
                        1: cold._v(
                            2, cold._ordinal("binding-ref-body-v0", binding_ref)
                        ),
                        2: _value_type_body(_type_of(core, outputs, binding["value"])),
                    }
                )
        for prior_ref, prior_occurrence in enumerate(
            core["occurrences"][:occurrence_ref]
        ):
            prior_effect = prior_occurrence["effect"]
            if prior_effect["tag"] == 0:
                for read_case, compiler in (
                    (3, "occurrence-ref-body-v0"),
                    (9, "decision-ref-body-v0"),
                ):
                    read_rows.append(
                        {
                            0: cold._ordinal("decision-ref-body-v0", occurrence_ref),
                            1: cold._v(read_case, cold._ordinal(compiler, prior_ref)),
                            2: _value_type_body(prior_effect["payload_type"]),
                        }
                    )
            elif prior_effect["tag"] == 2:
                read_rows.append(
                    {
                        0: cold._ordinal("decision-ref-body-v0", occurrence_ref),
                        1: cold._v(
                            4, cold._ordinal("occurrence-ref-body-v0", prior_ref)
                        ),
                        2: _value_type_body(
                            core["challenges"][prior_effect["challenge"]]["type"]
                        ),
                    }
                )
        legal_rows.append(
            {0: cold._ordinal("decision-ref-body-v0", occurrence_ref), 1: move}
        )
    read_rows.sort(key=lambda item: codec.encode_value(_READ_SCHEMA, item))
    strategy = {
        0: core_atom,
        1: decision_rows,
        2: cold._law("core-admission-v0"),
        3: read_rows,
        4: legal_rows,
    }

    challenge_rows = []
    for challenge_ref, challenge in enumerate(core["challenges"]):
        closure_nodes = {_producer(item) for item in challenge["conditions"]}
        challenge_rows.append(
            {
                0: cold._ordinal("challenge-ref-body-v0", challenge_ref),
                1: cold._ordinal(
                    "occurrence-ref-body-v0",
                    facts["challenge_positions"][challenge_ref],
                ),
                2: cold._ordinal("scope-ref-body-v0", challenge["scope"]),
                3: _value_type_body(challenge["type"]),
                4: cold._module_ref(challenge["domain"]),
                5: cold._module_ref(challenge["fresh_law"]),
                6: _correlation_value(challenge["correlation"]),
                7: _reduction_use_value(challenge["reduction_use"]),
                8: [cold._value_ref(item) for item in challenge["conditions"]],
                9: [_pc_value(item) for item in sorted(closure_nodes, key=_pc_key)],
                10: [
                    {
                        0: cold._ordinal("reduction-ref-body-v0", reduction_ref),
                        1: cold._ordinal("challenge-ref-body-v0", challenge_ref),
                    }
                    for reduction_ref in facts["reduction_consumers"][challenge_ref]
                ],
            }
        )
    public_coin = {
        0: core_atom,
        1: graph,
        2: graph_evidence["eligible"],
        3: [],
        4: challenge_rows,
    }

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
        for output_ordinal, output_type in enumerate(outputs[occurrence_ref]):
            predecessors = list(
                core["challenges"][effect["challenge"]]["conditions"]
                if effect["tag"] == 2
                else ()
            )
            if effect["tag"] == 2:
                predecessors.extend(
                    (
                        4,
                        facts["challenge_positions"][prior_member],
                        0,
                    )
                    for prior_member in core["challenges"][effect["challenge"]][
                        "correlation"
                    ]["prior"]
                )
            value_rows.append(
                {
                    0: cold._value_ref((4, occurrence_ref, output_ordinal)),
                    1: _value_type_body(output_type),
                    2: [cold._value_ref(item) for item in predecessors],
                }
            )
    terminal_rows = [
        {
            0: cold._ordinal("terminal-ref-body-v0", terminal_ref),
            1: cold._v(terminal["verdict"]),
            2: [cold._value_ref(item) for item in terminal["outputs"]],
            3: [],
            4: [
                {
                    0: cold._ordinal("claim-ref-body-v0", disposition["claim"]),
                    1: cold._v(disposition["disposition"]),
                }
                for disposition in terminal["dispositions"]
            ],
            5: cold._ordinal(
                "occurrence-ref-body-v0", facts["terminal_positions"][terminal_ref]
            ),
        }
        for terminal_ref, terminal in enumerate(core["terminals"])
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

    claim_rows: list[dict[int, Any]] = []
    for claim_ref, claim in enumerate(core["claims"]):
        uses = []
        for kind, occurrence_ref, owner_ref, ordinal in sorted(
            facts["claim_uses"][claim_ref],
            key=lambda item: (item[1], item[0], item[3]),
        ):
            uses.append(
                cold._v(
                    0 if kind == "reduction" else 1,
                    {
                        0: cold._ordinal("occurrence-ref-body-v0", occurrence_ref),
                        1: cold._ordinal(
                            "reduction-ref-body-v0"
                            if kind == "reduction"
                            else "terminal-ref-body-v0",
                            owner_ref,
                        ),
                        2: ordinal,
                    },
                )
            )
        claim_rows.append(
            {
                0: cold._ordinal("claim-ref-body-v0", claim_ref),
                1: cold._module_ref(claim["contract"]),
                2: cold._ordinal("scope-ref-body-v0", claim["scope"]),
                3: cold._v(claim["usage"]),
                4: _claim_source_value(claim["source"]),
                5: _claim_creation_value(core, facts, claim["source"]),
                6: uses,
            }
        )
    reduction_rows = [
        {
            0: cold._ordinal("reduction-ref-body-v0", reduction_ref),
            1: cold._module_ref(reduction["contract"]),
            2: cold._ordinal("scope-ref-body-v0", reduction["scope"]),
            3: cold._ordinal(
                "occurrence-ref-body-v0",
                facts["reduction_positions"][reduction_ref],
            ),
            4: [
                cold._ordinal("claim-ref-body-v0", item)
                for item in reduction["input_claims"]
            ],
            5: [cold._value_ref(item) for item in reduction["side_inputs"]],
            6: [
                cold._ordinal("challenge-ref-body-v0", item)
                for item in reduction["required_challenges"]
            ],
            7: [
                _publication_value(item) for item in reduction["required_publications"]
            ],
            8: [cold._module_ref(item) for item in reduction["output_contracts"]],
        }
        for reduction_ref, reduction in enumerate(core["reductions"])
    ]
    disposition_rows = [
        {
            0: cold._ordinal(
                "occurrence-ref-body-v0", facts["terminal_positions"][terminal_ref]
            ),
            1: cold._ordinal("terminal-ref-body-v0", terminal_ref),
            2: cold._ordinal("claim-ref-body-v0", disposition["claim"]),
            3: cold._v(disposition["disposition"]),
        }
        for terminal_ref, terminal in enumerate(core["terminals"])
        for disposition in terminal["dispositions"]
    ]
    claim_reduction = {
        0: core_atom,
        1: claim_rows,
        2: reduction_rows,
        3: disposition_rows,
    }

    resolver_rows = [
        {
            0: cold._ordinal("challenge-ref-body-v0", challenge_ref),
            1: cold._ordinal(
                "occurrence-ref-body-v0",
                facts["challenge_positions"][challenge_ref],
            ),
            2: _value_type_body(challenge["type"]),
            3: cold._module_ref(challenge["domain"]),
            4: cold._module_ref(challenge["fresh_law"]),
            5: [cold._value_ref(item) for item in challenge["conditions"]],
            6: [
                cold._ordinal("challenge-ref-body-v0", item)
                for item in challenge["correlation"]["prior"]
            ],
        }
        for challenge_ref, challenge in enumerate(core["challenges"])
    ]
    runtime = {
        0: [
            {
                0: cold._ordinal("occurrence-ref-body-v0", occurrence_ref),
                1: [_value_type_body(item) for item in outputs[occurrence_ref]],
            }
            for occurrence_ref in range(len(core["occurrences"]))
        ],
        1: [
            {
                0: cold._ordinal("challenge-ref-body-v0", challenge_ref),
                1: cold._ordinal(
                    "occurrence-ref-body-v0",
                    facts["challenge_positions"][challenge_ref],
                ),
                2: _value_type_body(challenge["type"]),
            }
            for challenge_ref, challenge in enumerate(core["challenges"])
        ],
        2: [],
        3: [
            {
                0: cold._ordinal("terminal-ref-body-v0", terminal_ref),
                1: cold._ordinal(
                    "occurrence-ref-body-v0",
                    facts["terminal_positions"][terminal_ref],
                ),
                2: cold._v(terminal["verdict"]),
                3: [
                    _value_type_body(_type_of(core, outputs, item))
                    for item in terminal["outputs"]
                ],
            }
            for terminal_ref, terminal in enumerate(core["terminals"])
        ],
    }
    execution = {
        0: protocol_atom,
        1: core_atom,
        2: cold._v(0),
        3: cold._law("core-admission-v0"),
        4: resolver_rows,
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
        "ClaimReductionView": claim_reduction,
        "ExecutionView": execution,
    }
    return views, {
        "occurrences": len(core["occurrences"]),
        "claims": len(core["claims"]),
        "reductions": len(core["reductions"]),
        "challenges": len(core["challenges"]),
        "decisions": len(decision_rows),
        "claim_uses": facts["claim_uses"],
        "reduction_consumers": facts["reduction_consumers"],
        "pc_graph": {
            "nodes": graph_evidence["nodes"],
            "edges": graph_evidence["edges"],
            "eligible": graph_evidence["eligible"],
            "challenge_validity": graph_evidence["challenge_validity"],
            "acceptance_sinks": graph_evidence["acceptance_sinks"],
        },
    }


def encode_views(views: dict[str, Any]) -> dict[str, bytes]:
    if tuple(views) != tuple(b2b.load_source()["view_order"]):
        raise ColdClaimReductionError("cold view table is incomplete or reordered")
    return {
        name: codec.encode_value(VIEW_SCHEMAS[name], value)
        for name, value in views.items()
    }
