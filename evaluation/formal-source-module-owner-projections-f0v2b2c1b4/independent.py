"""Cold byte-and-module-source projector for F0-V2B2C1B4.

This module authenticates complete Core, Fresh Protocol, and used semantic
module bytes; parses them into plain records; and independently derives all
six owner views.  It deliberately does not import the typed B2C1B4 model or
trust its retained Python objects.
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
    / "formal-source-claim-reduction-owner-projections-f0v2b2c1b3"
    / "independent.py"
)
MODULE_MAGIC = "f0v2b2c1b4.module-effect.v0"
MAX_LOCAL_ITEMS = 1 << 14


class ColdModuleError(ValueError):
    """The independent byte-derived module projection failed closed."""


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


prior = _load("_zkc_f0v2b2c1b4_cold_predecessor", PREDECESSOR_COLD)
cold = prior.cold
k1 = cold.k1
b2b = cold.b2b
codec = cold.codec
VIEW_SCHEMAS = cold.VIEW_SCHEMAS
PROFILE_DIGEST = cold.PROFILE_DIGEST
_PC_GRAPH_SCHEMA = prior._PC_GRAPH_SCHEMA
_PC_NODE_SCHEMA = prior._PC_NODE_SCHEMA
_PC_EDGE_SCHEMA = prior._PC_EDGE_SCHEMA
_READ_SCHEMA = prior._READ_SCHEMA


def _record(value: object, ordinals: tuple[int, ...], label: str) -> tuple[object, ...]:
    try:
        return cold._record(value, ordinals, label)
    except Exception as error:
        raise ColdModuleError(str(error)) from error


def _sequence(value: object, label: str) -> tuple[object, ...]:
    try:
        return cold._sequence(value, label)
    except Exception as error:
        raise ColdModuleError(str(error)) from error


def _variant(value: object, cases: set[int], label: str) -> tuple[int, object]:
    try:
        return cold._variant(value, cases, label)
    except Exception as error:
        raise ColdModuleError(str(error)) from error


def _nat(value: object, label: str) -> int:
    try:
        return cold._nat(value, label)
    except Exception as error:
        raise ColdModuleError(str(error)) from error


def _bytes(value: object, label: str) -> bytes:
    try:
        return cold._bytes(value, label)
    except Exception as error:
        raise ColdModuleError(str(error)) from error


def _unit(value: object, label: str) -> None:
    try:
        cold._unit(value, label)
    except Exception as error:
        raise ColdModuleError(str(error)) from error


def _symbol(value: object, label: str) -> str:
    if type(value) is not k1.Symbol:
        raise ColdModuleError(f"{label} is not a symbol")
    return value.value


def _bool(value: object, label: str) -> bool:
    tag, payload = _variant(value, {0, 1}, label)
    _unit(payload, f"{label} payload")
    return bool(tag)


def _value_ref(value: object) -> tuple[int, int, int]:
    try:
        return cold._parse_value_ref(value)
    except Exception as error:
        raise ColdModuleError(str(error)) from error


def _guard(value: object) -> dict[str, Any]:
    try:
        return cold._parse_guard(value)
    except Exception as error:
        raise ColdModuleError(str(error)) from error


def _module_ref(value: object) -> dict[str, Any]:
    tag, payload = _variant(value, {1}, "module declaration reference")
    if tag != 1:  # pragma: no cover - parser set closes this
        raise ColdModuleError("module declaration reference differs")
    module, kind, ordinal = _record(payload, (0, 1, 2), "module declaration")
    return {
        "body": value,
        "module": _bytes(module, "module declaration owner"),
        "kind": _symbol(kind, "module declaration kind"),
        "ordinal": _nat(ordinal, "module declaration ordinal"),
    }


def _module_payload(value: object) -> dict[str, Any]:
    (inputs,) = _record(value, (0,), "module payload")
    return {
        "body": value,
        "inputs": tuple(
            _value_ref(item) for item in _sequence(inputs, "module payload inputs")
        ),
    }


def _effect(value: object) -> dict[str, Any]:
    tag, payload = _variant(value, set(range(8)), "Core effect")
    if tag == 5:
        return {
            "tag": tag,
            "body": value,
            "terminal": _nat(payload, "terminal backlink"),
        }
    if tag == 7:
        module, declaration, module_payload = _record(
            payload, (0, 1, 2), "module effect"
        )
        return {
            "tag": tag,
            "body": value,
            "module": _bytes(module, "module-effect owner"),
            "declaration": _module_ref(declaration),
            "payload": _module_payload(module_payload),
        }
    raise ColdModuleError(f"effect tag {tag} belongs to another slice")


def _terminal(value: object) -> dict[str, Any]:
    verdict, outputs, checks, dispositions = _record(value, (0, 1, 2, 3), "terminal")
    verdict_tag, verdict_payload = _variant(verdict, {0, 1, 2}, "verdict")
    _unit(verdict_payload, "verdict payload")
    parsed_outputs = tuple(
        _value_ref(item) for item in _sequence(outputs, "terminal outputs")
    )
    if _sequence(checks, "terminal checks") or _sequence(
        dispositions, "terminal dispositions"
    ):
        raise ColdModuleError(
            "terminal checks and claim dispositions belong to another slice"
        )
    return {"verdict": verdict_tag, "outputs": parsed_outputs}


def decode_core(domain_body: bytes) -> dict[str, Any]:
    """Decode the complete bounded Core without typed-owner objects."""

    if type(domain_body) is not bytes or not domain_body:
        raise ColdModuleError("Core domain body is not nonempty exact bytes")
    try:
        root = k1.decode_datum(domain_body)
    except Exception as error:
        raise ColdModuleError(f"Core domain does not decode: {error}") from error
    if k1.encode_datum(root) != domain_body:
        raise ColdModuleError("Core domain does not round-trip")
    fields = _record(root, tuple(range(14)), "InteractiveCore")
    tables = tuple(
        _sequence(value, f"InteractiveCore field {index}")
        for index, value in enumerate(fields)
    )
    if any(tables[index] for index in (2, 3, 4, 7, 8, 9, 10, 11)):
        raise ColdModuleError("Core contains another constructor slice")
    public_inputs = tuple(
        {"type": _record(item, (0,), "public input")[0]} for item in tables[1]
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
                "parent": None if parent_tag == 0 else _nat(parent_payload, "parent"),
                "opening": None
                if opening_tag == 0
                else _nat(opening_payload, "opening"),
            }
        )
    bindings: list[dict[str, Any]] = []
    for item in tables[6]:
        scope, binding_class, reference = _record(item, (0, 1, 2), "binding")
        class_tag, class_payload = _variant(binding_class, {0, 1, 2}, "binding class")
        _unit(class_payload, "binding class payload")
        bindings.append(
            {
                "scope": _nat(scope, "binding scope"),
                "class": class_tag,
                "value": _value_ref(reference),
            }
        )
    occurrences: list[dict[str, Any]] = []
    for item in tables[13]:
        scope, guard, effect = _record(item, (0, 1, 2), "occurrence")
        occurrences.append(
            {
                "scope": _nat(scope, "occurrence scope"),
                "guard": _guard(guard),
                "effect": _effect(effect),
            }
        )
    return {
        "used_modules": tuple(_bytes(item, "used module") for item in tables[0]),
        "public_inputs": public_inputs,
        "scopes": tuple(scopes),
        "bindings": tuple(bindings),
        "terminals": tuple(_terminal(item) for item in tables[12]),
        "occurrences": tuple(occurrences),
    }


def _dependency(value: object) -> dict[str, int | None]:
    tag, payload = _variant(value, {0, 1, 2, 3}, "module dependency")
    if tag in (0, 1):
        _unit(payload, "node-local dependency payload")
        return {"tag": tag, "ordinal": None}
    return {"tag": tag, "ordinal": _nat(payload, "module dependency ordinal")}


def _output(value: object) -> dict[str, Any]:
    value_type, visibility, transfer, dependencies, sink = _record(
        value, (0, 1, 2, 3, 4), "module output"
    )
    visibility_tag, visibility_payload = _variant(
        visibility, {0, 1, 2, 3}, "module visibility"
    )
    _unit(visibility_payload, "module visibility payload")
    transfer_tag, transfer_payload = _variant(
        transfer, {0, 1, 2}, "module output transfer"
    )
    algorithm: bytes | None = None
    contract: bytes | None = None
    if transfer_tag == 0:
        algorithm_value, contract_value = _record(
            transfer_payload, (0, 1), "module reconstruction"
        )
        algorithm = _bytes(algorithm_value, "reconstruction algorithm")
        contract = _bytes(contract_value, "reconstruction contract")
    else:
        _unit(transfer_payload, "nondeterministic transfer payload")
    return {
        "type": value_type,
        "visibility": visibility_tag,
        "transfer": transfer_tag,
        "dependencies": tuple(
            _dependency(item)
            for item in _sequence(dependencies, "module output dependencies")
        ),
        "algorithm": algorithm,
        "contract": contract,
        "acceptance_relevant": _bool(sink, "module output sink"),
    }


def _control(value: object) -> dict[str, Any]:
    dependencies, sink = _record(value, (0, 1), "module control")
    return {
        "dependencies": tuple(
            _dependency(item)
            for item in _sequence(dependencies, "module control dependencies")
        ),
        "acceptance_relevant": _bool(sink, "module control sink"),
    }


def _semantics(value: object) -> dict[str, Any]:
    fields = _record(value, tuple(range(11)), "module declaration")
    if _symbol(fields[0], "module declaration magic") != MODULE_MAGIC:
        raise ColdModuleError("module declaration selects another schema")
    decision, decision_payload = _variant(fields[2], {0, 1, 2}, "module decision class")
    if decision == 0:
        _unit(decision_payload, "NoProverDecision payload")
        move_type = None
    else:
        move_type = decision_payload
    influence_tag, influence_payload = _variant(
        fields[6], {0, 1}, "module influence output"
    )
    if influence_tag == 0:
        _unit(influence_payload, "absent influence output")
    return {
        "body": value,
        "name": _symbol(fields[1], "module declaration name"),
        "decision": decision,
        "move_type": move_type,
        "payload_types": _sequence(fields[3], "module payload ABI"),
        "outputs": tuple(
            _output(item) for item in _sequence(fields[4], "module outputs")
        ),
        "controls": tuple(
            _control(item) for item in _sequence(fields[5], "module controls")
        ),
        "influence": None
        if influence_tag == 0
        else _nat(influence_payload, "module influence output"),
        "guard_behavior": _symbol(fields[7], "module guard behavior"),
        "replay_rule": _symbol(fields[8], "module replay rule"),
        "terminal_interaction": _symbol(fields[9], "module terminal interaction"),
        "work_bound": _nat(fields[10], "module work bound"),
    }


def _z3_type() -> tuple[object, object]:
    value_type = k1.ValueType(k1.NAT_DOMAIN, k1.NatSchema(2))
    return value_type, k1.value_type_datum(value_type)


def _expected_reconstruction() -> tuple[bytes, bytes]:
    z3, _datum = _z3_type()
    algorithm = k1.CanonicalAlgorithm(
        k1.Symbol("f0v2b2c1b4.reconstruct-identity-z3"),
        (z3,),
        k1.Variable(0, z3),
    )
    return (
        algorithm.identity.internal_reference(),
        k1.DEFAULT_EVALUATION_CONTRACT.identity.internal_reference(),
    )


def _dependency_shape(
    items: tuple[dict[str, int | None], ...],
) -> tuple[tuple[int, int | None], ...]:
    return tuple((item["tag"], item["ordinal"]) for item in items)


def _validate_semantics(semantics: dict[str, Any], ordinal: int) -> None:
    _z3, z3 = _z3_type()
    algorithm, contract = _expected_reconstruction()
    names = (
        "bounded-deterministic-public",
        "bounded-prover-decision",
        "bounded-prover-publication",
    )
    decisions = (0, 1, 2)
    visibilities = (3, 1, 3)
    transfers = (0, 2, 1)
    if not 0 <= ordinal < 3:
        raise ColdModuleError("module declaration ordinal is unsupported")
    if (
        semantics["name"] != names[ordinal]
        or semantics["decision"] != decisions[ordinal]
        or semantics["payload_types"] != (z3,)
        or semantics["guard_behavior"] != "inherit-exact-occurrence-guard"
        or semantics["replay_rule"] != "exact-module-event-replay"
        or semantics["terminal_interaction"] != "nonterminating"
        or semantics["work_bound"] != 8
        or len(semantics["outputs"]) != 1
        or len(semantics["controls"]) != 1
    ):
        raise ColdModuleError("module declaration differs from exact support")
    if (semantics["move_type"] is None) != (ordinal == 0):
        raise ColdModuleError("module decision move type differs")
    if semantics["move_type"] is not None and semantics["move_type"] != z3:
        raise ColdModuleError("module decision move ABI differs")
    output = semantics["outputs"][0]
    control = semantics["controls"][0]
    if (
        output["type"] != z3
        or output["visibility"] != visibilities[ordinal]
        or output["transfer"] != transfers[ordinal]
        or _dependency_shape(output["dependencies"]) != ((0, None), (1, None), (2, 0))
        or not output["acceptance_relevant"]
        or _dependency_shape(control["dependencies"]) != ((0, None), (1, None), (3, 0))
        or not control["acceptance_relevant"]
    ):
        raise ColdModuleError("module output/control semantics differ")
    if ordinal == 0:
        if output["algorithm"] != algorithm or output["contract"] != contract:
            raise ColdModuleError("deterministic reconstruction authority differs")
    elif output["algorithm"] is not None or output["contract"] is not None:
        raise ColdModuleError(
            "nondeterministic output carries reconstruction authority"
        )
    if semantics["influence"] != (0 if ordinal == 2 else None):
        raise ColdModuleError("module publication influence differs")


def _module_source(reference: bytes, body: bytes) -> dict[str, Any]:
    if type(reference) is not bytes or type(body) is not bytes or not body:
        raise ColdModuleError("module source is not exact nonempty bytes")
    try:
        identifier = k1.decode_content_reference(reference)
        decoded = k1.decode_datum(body)
        if k1.encode_datum(decoded) != body:
            raise ColdModuleError("module body is not canonical")
        expected = k1.content_id(
            k1.SEMANTIC_MODULE_KIND,
            body,
            semantic_regime=k1.SEMANTIC_REGIME_ID,
        )
    except ColdModuleError:
        raise
    except Exception as error:
        raise ColdModuleError(f"module source does not decode: {error}") from error
    if (
        identifier.subject_kind != k1.SEMANTIC_MODULE_KIND
        or identifier.semantic_regime != k1.SEMANTIC_REGIME_ID
        or expected.internal_reference() != reference
    ):
        raise ColdModuleError("module body and reference do not authenticate")
    imports, declarations, payload = _record(decoded, (0, 1, 2), "semantic module")
    if _sequence(imports, "module imports"):
        raise ColdModuleError("supported module unexpectedly imports another module")
    _unit(payload, "module domain payload")
    catalogs = _sequence(declarations, "module declaration catalogs")
    if len(catalogs) != 1:
        raise ColdModuleError("module catalog closure differs")
    kind, local_declarations = _record(catalogs[0], (0, 1), "module catalog")
    if _symbol(kind, "module catalog kind") != "pir.core-effect":
        raise ColdModuleError("module catalog has another kind")
    semantics = tuple(
        _semantics(item)
        for item in _sequence(local_declarations, "module local declarations")
    )
    if len(semantics) != 3:
        raise ColdModuleError("module declaration closure differs")
    for ordinal, item in enumerate(semantics):
        _validate_semantics(item, ordinal)
    return {"reference": reference, "body": body, "semantics": semantics}


def _source_closure(
    used_modules: tuple[bytes, ...],
    sources: tuple[tuple[bytes, bytes], ...],
) -> dict[bytes, dict[str, Any]]:
    if type(sources) is not tuple or any(
        type(item) is not tuple or len(item) != 2 for item in sources
    ):
        raise ColdModuleError("module source closure has another exact carrier")
    references = tuple(item[0] for item in sources)
    if references != tuple(sorted(set(references))):
        raise ColdModuleError("module source closure is not sorted and unique")
    if used_modules != references:
        raise ColdModuleError("used_modules and module preimage closure differ")
    return {reference: _module_source(reference, body) for reference, body in sources}


def _type_of(
    core: dict[str, Any],
    outputs: tuple[tuple[object, ...], ...],
    reference: tuple[int, int, int],
) -> object:
    tag, first, second = reference
    try:
        if tag == 0:
            return core["public_inputs"][first]["type"]
        if tag == 4:
            return outputs[first][second]
    except (IndexError, KeyError) as error:
        raise ColdModuleError("ValueRef is absent") from error
    raise ColdModuleError("ValueRef belongs to another slice")


def _producer(reference: tuple[int, int, int]) -> tuple[int, ...]:
    tag, first, second = reference
    if tag == 0:
        return 0, first
    if tag == 4:
        return 8, first, second
    raise ColdModuleError("producer belongs to another slice")


def _validate_core(
    core: dict[str, Any], sources: tuple[tuple[bytes, bytes], ...]
) -> dict[str, Any]:
    _z3, z3 = _z3_type()
    if (
        len(core["public_inputs"]) != 1
        or core["public_inputs"][0]["type"] != z3
        or core["scopes"] != ({"parent": None, "opening": None},)
        or core["bindings"] != ({"scope": 0, "class": 0, "value": (0, 0, 0)},)
        or len(core["terminals"]) != 1
        or not core["occurrences"]
        or len(core["occurrences"]) > MAX_LOCAL_ITEMS
    ):
        raise ColdModuleError("bounded module Core has another isolation shape")
    source_map = _source_closure(core["used_modules"], sources)
    module_occurrences: dict[int, dict[str, Any]] = {}
    outputs: list[tuple[object, ...]] = []
    available: set[tuple[int, int, int]] = {(0, 0, 0)}
    direct_owners: set[bytes] = set()
    for occurrence_ref, occurrence in enumerate(core["occurrences"]):
        if occurrence["scope"] != 0 or occurrence["guard"]["tag"] != 0:
            raise ColdModuleError("module occurrence leaves root/Always isolation")
        effect = occurrence["effect"]
        if effect["tag"] == 7:
            declaration = effect["declaration"]
            if effect["module"] != declaration["module"]:
                raise ColdModuleError(
                    "module effect owner and declaration owner differ"
                )
            if declaration["kind"] != "pir.core-effect":
                raise ColdModuleError("module declaration kind differs")
            try:
                source = source_map[effect["module"]]
                semantics = source["semantics"][declaration["ordinal"]]
            except (KeyError, IndexError) as error:
                raise ColdModuleError(
                    "module declaration coordinate is absent"
                ) from error
            _validate_semantics(semantics, declaration["ordinal"])
            if len(effect["payload"]["inputs"]) != len(semantics["payload_types"]):
                raise ColdModuleError("module payload arity differs")
            for reference, expected_type in zip(
                effect["payload"]["inputs"],
                semantics["payload_types"],
                strict=True,
            ):
                if reference not in available:
                    raise ColdModuleError(
                        "module payload names a future or absent value"
                    )
                if _type_of(core, tuple(outputs), reference) != expected_type:
                    raise ColdModuleError("module payload ABI differs")
            row = tuple(item["type"] for item in semantics["outputs"])
            outputs.append(row)
            for output_ordinal in range(len(row)):
                available.add((4, occurrence_ref, output_ordinal))
            module_occurrences[occurrence_ref] = semantics
            direct_owners.update((effect["module"], declaration["module"]))
        elif effect["tag"] == 5:
            outputs.append(())
        else:  # pragma: no cover - parser closes this
            raise ColdModuleError("occurrence belongs to another effect slice")
    if not module_occurrences:
        raise ColdModuleError("module isolation carrier contains no ModuleEffect")
    if core["used_modules"] != tuple(sorted(direct_owners)):
        raise ColdModuleError("used_modules differs from exact module-effect owners")
    terminal_positions = [
        index
        for index, occurrence in enumerate(core["occurrences"])
        if occurrence["effect"]["tag"] == 5 and occurrence["effect"]["terminal"] == 0
    ]
    if (
        terminal_positions != [len(core["occurrences"]) - 1]
        or core["terminals"][0] != {"verdict": 0, "outputs": ()}
        or any(
            occurrence["effect"]["tag"] == 5 and occurrence["effect"]["terminal"] != 0
            for occurrence in core["occurrences"]
        )
    ):
        raise ColdModuleError("terminal fallback or backlink differs")
    return {
        "sources": source_map,
        "module_semantics": module_occurrences,
        "outputs": tuple(outputs),
        "terminal_position": terminal_positions[0],
    }


def _pc_value(node: tuple[int, ...]) -> dict[str, Any]:
    try:
        return prior._pc_value(node)
    except Exception as error:
        raise ColdModuleError(str(error)) from error


def _pc_key(node: tuple[int, ...]) -> bytes:
    return codec.encode_value(_PC_NODE_SCHEMA, _pc_value(node))


def _edge_value(
    pair: tuple[tuple[int, ...], tuple[int, ...]],
) -> dict[int, Any]:
    return {0: _pc_value(pair[0]), 1: _pc_value(pair[1])}


def _edge_key(pair: tuple[tuple[int, ...], tuple[int, ...]]) -> bytes:
    return codec.encode_value(_PC_EDGE_SCHEMA, _edge_value(pair))


def _dependency_node(
    effect: dict[str, Any], dependency: dict[str, int | None], occurrence_ref: int
) -> tuple[int, ...]:
    tag = dependency["tag"]
    if tag == 0:
        return 6, occurrence_ref
    if tag == 1:
        return 7, occurrence_ref
    ordinal = dependency["ordinal"]
    if type(ordinal) is not int:
        raise ColdModuleError("indexed module dependency lacks an ordinal")
    if tag == 2:
        try:
            return _producer(effect["payload"]["inputs"][ordinal])
        except IndexError as error:
            raise ColdModuleError("payload dependency is absent") from error
    if tag == 3:
        return 13, occurrence_ref, ordinal
    raise ColdModuleError("module dependency tag differs")


def _join(values: list[int]) -> int:
    for value in (3, 2, 1):
        if value in values:
            return value
    return 0


def _graph(
    core: dict[str, Any], facts: dict[str, Any]
) -> tuple[dict[int, Any], dict[str, Any]]:
    nodes: set[tuple[int, ...]] = {(0, 0), (4, 0), (5, 0)}
    edges: set[tuple[tuple[int, ...], tuple[int, ...]]] = {
        ((0, 0), (5, 0)),
        ((4, 0), (5, 0)),
    }
    output_specs: dict[tuple[int, ...], dict[str, Any]] = {}
    public_observations: set[tuple[int, ...]] = set()
    acceptance_module: set[tuple[int, ...]] = set()
    for occurrence_ref, occurrence in enumerate(core["occurrences"]):
        activity = (6, occurrence_ref)
        effect_node = (7, occurrence_ref)
        nodes.update((activity, effect_node))
        edges.add(((4, 0), activity))
        edges.add((activity, effect_node))
        if occurrence["effect"]["tag"] == 7:
            effect = occurrence["effect"]
            semantics = facts["module_semantics"][occurrence_ref]
            for control_ordinal, control in enumerate(semantics["controls"]):
                control_node = (12, occurrence_ref, control_ordinal)
                nodes.add(control_node)
                for dependency in control["dependencies"]:
                    source = _dependency_node(effect, dependency, occurrence_ref)
                    nodes.add(source)
                    edges.add((source, control_node))
                if control["acceptance_relevant"]:
                    acceptance_module.add(control_node)
            for output_ordinal, output in enumerate(semantics["outputs"]):
                module_output = (13, occurrence_ref, output_ordinal)
                occurrence_output = (8, occurrence_ref, output_ordinal)
                nodes.update((module_output, occurrence_output))
                output_specs[module_output] = output
                for dependency in output["dependencies"]:
                    source = _dependency_node(effect, dependency, occurrence_ref)
                    nodes.add(source)
                    edges.add((source, module_output))
                edges.add((effect_node, occurrence_output))
                edges.add((module_output, occurrence_output))
                if output["visibility"] == 3:
                    public_observations.update((module_output, occurrence_output))
                if output["acceptance_relevant"]:
                    acceptance_module.add(module_output)
        else:
            terminal = (11, occurrence["effect"]["terminal"])
            nodes.add(terminal)
            edges.add((effect_node, terminal))

    incoming = {node: set() for node in nodes}
    outgoing = {node: set() for node in nodes}
    for source, target in edges:
        incoming[target].add(source)
        outgoing[source].add(target)
    indegree = {node: len(incoming[node]) for node in nodes}
    heap = [(_pc_key(node), node) for node in nodes if indegree[node] == 0]
    heapq.heapify(heap)
    topological: list[tuple[int, ...]] = []
    while heap:
        _key, node = heapq.heappop(heap)
        topological.append(node)
        for target in outgoing[node]:
            indegree[target] -= 1
            if indegree[target] == 0:
                heapq.heappush(heap, (_pc_key(target), target))
    if len(topological) != len(nodes):
        raise ColdModuleError("module PCGraph is cyclic")

    classes: dict[tuple[int, ...], int] = {}
    for node in topological:
        if node[0] in (0, 4):
            value = 0
        elif node in output_specs:
            joined = _join([classes[item] for item in incoming[node]])
            transfer = output_specs[node]["transfer"]
            if transfer == 0:
                value = joined
            elif transfer == 1:
                value = 1 if joined in (0, 1) else joined
            else:
                value = 3
        else:
            value = _join([classes[item] for item in incoming[node]])
        classes[node] = value
    terminal_ref = facts["terminal_position"]
    terminal_nodes = {(6, terminal_ref), (7, terminal_ref), (11, 0)}
    observation_activities = {
        (6, occurrence_ref)
        for occurrence_ref, semantics in facts["module_semantics"].items()
        if any(output["visibility"] == 3 for output in semantics["outputs"])
    }
    sinks = (
        terminal_nodes
        | public_observations
        | observation_activities
        | acceptance_module
    )
    acceptance = {(11, 0)} | acceptance_module
    eligible = all(classes[node] in (0, 1) for node in sinks)
    ordered_nodes = sorted(nodes, key=_pc_key)
    graph = {
        0: [_pc_value(node) for node in ordered_nodes],
        1: [_edge_value(edge) for edge in sorted(edges, key=_edge_key)],
        2: [_pc_value(node) for node in topological],
        3: [{0: _pc_value(node), 1: cold._v(classes[node])} for node in ordered_nodes],
        4: [_pc_value(node) for node in sorted(sinks, key=_pc_key)],
        5: [_pc_value(node) for node in sorted(acceptance, key=_pc_key)],
        6: [],
    }
    return graph, {
        "nodes": len(nodes),
        "edges": len(edges),
        "eligible": eligible,
        "classes": classes,
        "sinks": tuple(sorted(sinks, key=_pc_key)),
        "acceptance_sinks": tuple(sorted(acceptance, key=_pc_key)),
    }


def _admitted_effect(effect: dict[str, Any]) -> dict[str, str]:
    return {
        "module_body": k1.encode_datum(k1.BytesValue(effect["module"])).hex(),
        "declaration_body": k1.encode_datum(effect["declaration"]["body"]).hex(),
        "payload_body": k1.encode_datum(effect["payload"]["body"]).hex(),
    }


def _effect_value(effect: dict[str, Any]) -> dict[str, Any]:
    if effect["tag"] == 7:
        return cold._v(7, _admitted_effect(effect))
    if effect["tag"] == 5:
        return cold._v(5, cold._ordinal("terminal-ref-body-v0", effect["terminal"]))
    raise ColdModuleError("effect belongs to another slice")


def _module_move(effect: dict[str, Any], semantics: dict[str, Any]) -> dict[str, Any]:
    if semantics["move_type"] is None:
        raise ColdModuleError("NoProverDecision has no legal move")
    return cold._v(
        2,
        {
            0: _admitted_effect(effect),
            1: cold._value_type(semantics["move_type"]),
        },
    )


def _value_dependencies(
    effect: dict[str, Any],
    dependencies: tuple[dict[str, int | None], ...],
    occurrence_ref: int,
) -> tuple[tuple[int, int, int], ...]:
    result: list[tuple[int, int, int]] = []
    for dependency in dependencies:
        ordinal = dependency["ordinal"]
        if dependency["tag"] == 2 and type(ordinal) is int:
            result.append(effect["payload"]["inputs"][ordinal])
        elif dependency["tag"] == 3 and type(ordinal) is int:
            result.append((4, occurrence_ref, ordinal))
    return tuple(result)


def project(
    core_profiled_body: bytes,
    core_reference: bytes,
    protocol_profiled_body: bytes,
    protocol_reference: bytes,
    module_sources: tuple[tuple[bytes, bytes], ...],
) -> tuple[dict[str, Any], dict[str, Any]]:
    """Authenticate exact subject/source bytes and derive all owner views."""

    try:
        core_profile, core_domain = cold._authenticated_subject(
            core_profiled_body,
            core_reference,
            "pir.interactive-core",
            "cold module Core",
        )
        protocol_profile, protocol_domain = cold._authenticated_subject(
            protocol_profiled_body,
            protocol_reference,
            "pir.protocol",
            "cold module Protocol",
        )
    except Exception as error:
        raise ColdModuleError(str(error)) from error
    if protocol_profile != core_profile:
        raise ColdModuleError("Core and Protocol profiles differ")
    protocol_core, interpretation = _record(
        protocol_domain, (0, 1), "cold Protocol domain"
    )
    if _bytes(protocol_core, "Protocol Core") != core_reference:
        raise ColdModuleError("Fresh Protocol names another Core")
    interpretation_tag, interpretation_payload = _variant(
        interpretation, {0}, "Fresh interpretation"
    )
    if interpretation_tag != 0:  # pragma: no cover - parser closes this
        raise ColdModuleError("Protocol is not Fresh")
    _unit(interpretation_payload, "Fresh payload")

    core = decode_core(k1.encode_datum(core_domain))
    facts = _validate_core(core, module_sources)
    outputs = facts["outputs"]
    graph, graph_evidence = _graph(core, facts)
    core_atom = cold._identifier("core-id-body-v0", core_reference)
    protocol_atom = cold._identifier("protocol-id-body-v0", protocol_reference)

    public_binding = {
        0: core_atom,
        1: [
            {
                0: cold._ordinal("scope-ref-body-v0", 0),
                1: cold._v(0),
                2: cold._v(0),
                3: [cold._ordinal("scope-ref-body-v0", 0)],
            }
        ],
        2: [
            {
                0: cold._ordinal("binding-ref-body-v0", 0),
                1: cold._ordinal("scope-ref-body-v0", 0),
                2: cold._v(0),
                3: cold._value_ref((0, 0, 0)),
                4: cold._value_type(core["public_inputs"][0]["type"]),
            }
        ],
    }

    decisions = [
        (occurrence_ref, occurrence, facts["module_semantics"][occurrence_ref])
        for occurrence_ref, occurrence in enumerate(core["occurrences"])
        if occurrence_ref in facts["module_semantics"]
        and facts["module_semantics"][occurrence_ref]["decision"] != 0
    ]
    decision_rows: list[dict[int, Any]] = []
    read_rows: list[dict[int, Any]] = []
    legal_rows: list[dict[int, Any]] = []
    observed_module_reads = 0
    prior_move_reads = 0
    for occurrence_ref, occurrence, semantics in decisions:
        move = _module_move(occurrence["effect"], semantics)
        prior_decisions = [item for item in decisions if item[0] < occurrence_ref]
        decision_rows.append(
            {
                0: cold._ordinal("decision-ref-body-v0", occurrence_ref),
                1: cold._ordinal("occurrence-ref-body-v0", occurrence_ref),
                2: [cold._ordinal("scope-ref-body-v0", 0)],
                3: cold._guard(occurrence["guard"]["body"]),
                4: move,
                5: [
                    cold._ordinal("decision-ref-body-v0", prior_ref)
                    for prior_ref, _prior_occurrence, _prior_semantics in prior_decisions
                ],
            }
        )
        read_rows.extend(
            (
                {
                    0: cold._ordinal("decision-ref-body-v0", occurrence_ref),
                    1: cold._v(1, cold._ordinal("public-input-ref-body-v0", 0)),
                    2: cold._value_type(core["public_inputs"][0]["type"]),
                },
                {
                    0: cold._ordinal("decision-ref-body-v0", occurrence_ref),
                    1: cold._v(2, cold._ordinal("binding-ref-body-v0", 0)),
                    2: cold._value_type(core["public_inputs"][0]["type"]),
                },
            )
        )
        for prior_ref in range(occurrence_ref):
            prior_semantics = facts["module_semantics"].get(prior_ref)
            if prior_semantics is None:
                continue
            for output_ordinal, output in enumerate(prior_semantics["outputs"]):
                if output["visibility"] in (1, 3):
                    read_rows.append(
                        {
                            0: cold._ordinal("decision-ref-body-v0", occurrence_ref),
                            1: cold._v(
                                8,
                                {
                                    0: cold._ordinal(
                                        "occurrence-ref-body-v0", prior_ref
                                    ),
                                    1: output_ordinal,
                                },
                            ),
                            2: cold._value_type(output["type"]),
                        }
                    )
                    observed_module_reads += 1
        for prior_ref, _prior_occurrence, prior_semantics in prior_decisions:
            read_rows.append(
                {
                    0: cold._ordinal("decision-ref-body-v0", occurrence_ref),
                    1: cold._v(9, cold._ordinal("decision-ref-body-v0", prior_ref)),
                    2: cold._value_type(prior_semantics["move_type"]),
                }
            )
            prior_move_reads += 1
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
    public_coin = {0: core_atom, 1: graph, 2: graph_evidence["eligible"], 3: [], 4: []}

    value_rows: list[dict[int, Any]] = [
        {
            0: cold._value_ref((0, 0, 0)),
            1: cold._value_type(core["public_inputs"][0]["type"]),
            2: [],
        }
    ]
    occurrence_rows: list[dict[int, Any]] = []
    extension_rows: list[dict[int, Any]] = []
    for occurrence_ref, occurrence in enumerate(core["occurrences"]):
        occurrence_rows.append(
            {
                0: cold._ordinal("occurrence-ref-body-v0", occurrence_ref),
                1: [cold._ordinal("scope-ref-body-v0", 0)],
                2: cold._guard(occurrence["guard"]["body"]),
                3: _effect_value(occurrence["effect"]),
                4: [cold._value_type(item) for item in outputs[occurrence_ref]],
            }
        )
        if occurrence["effect"]["tag"] == 7:
            effect = occurrence["effect"]
            semantics = facts["module_semantics"][occurrence_ref]
            extension_rows.append(
                {
                    0: cold._ordinal("occurrence-ref-body-v0", occurrence_ref),
                    1: _admitted_effect(effect),
                }
            )
            for output_ordinal, output in enumerate(semantics["outputs"]):
                value_rows.append(
                    {
                        0: cold._value_ref((4, occurrence_ref, output_ordinal)),
                        1: cold._value_type(output["type"]),
                        2: [
                            cold._value_ref(item)
                            for item in _value_dependencies(
                                effect,
                                output["dependencies"],
                                occurrence_ref,
                            )
                        ],
                    }
                )
    terminal_rows = [
        {
            0: cold._ordinal("terminal-ref-body-v0", 0),
            1: cold._v(0),
            2: [],
            3: [],
            4: [],
            5: cold._ordinal("occurrence-ref-body-v0", facts["terminal_position"]),
        }
    ]
    effect_view = {
        0: core_atom,
        1: occurrence_rows,
        2: value_rows,
        3: [],
        4: [],
        5: [],
        6: terminal_rows,
        7: extension_rows,
    }
    claim_reduction = {0: core_atom, 1: [], 2: [], 3: []}
    runtime = {
        0: [
            {
                0: cold._ordinal("occurrence-ref-body-v0", occurrence_ref),
                1: [cold._value_type(item) for item in outputs[occurrence_ref]],
            }
            for occurrence_ref in range(len(core["occurrences"]))
        ],
        1: [],
        2: [],
        3: [
            {
                0: cold._ordinal("terminal-ref-body-v0", 0),
                1: cold._ordinal("occurrence-ref-body-v0", facts["terminal_position"]),
                2: cold._v(0),
                3: [],
            }
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
        "ClaimReductionView": claim_reduction,
        "ExecutionView": execution,
    }
    return views, {
        "occurrences": len(core["occurrences"]),
        "module_occurrences": len(facts["module_semantics"]),
        "module_sources": len(facts["sources"]),
        "decisions": len(decision_rows),
        "observed_module_reads": observed_module_reads,
        "prior_move_reads": prior_move_reads,
        "decision_classes": tuple(
            facts["module_semantics"][index]["decision"]
            for index in sorted(facts["module_semantics"])
        ),
        "pc_graph": {
            "nodes": graph_evidence["nodes"],
            "edges": graph_evidence["edges"],
            "eligible": graph_evidence["eligible"],
            "sinks": graph_evidence["sinks"],
            "acceptance_sinks": graph_evidence["acceptance_sinks"],
        },
    }


def encode_views(views: dict[str, Any]) -> dict[str, bytes]:
    if tuple(views) != tuple(b2b.load_source()["view_order"]):
        raise ColdModuleError("cold view table is incomplete or reordered")
    return {
        name: codec.encode_value(VIEW_SCHEMAS[name], value)
        for name, value in views.items()
    }
