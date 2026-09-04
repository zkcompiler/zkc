"""Recursive candidate compiler and owner derivation for bounded F0-V2B1."""

from __future__ import annotations

import copy
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
from types import ModuleType
from typing import Any


ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
SOURCE = HERE / "normalized-schema.json"
OWNER_MODEL = ROOT / "evaluation/formal-source-target-core-f1r1b/reference_model.py"


class BoundedError(ValueError):
    """The bounded source, owner subject, view, or manifest does not form."""


def _load_module(name: str, path: Path) -> ModuleType:
    if name in sys.modules:
        return sys.modules[name]
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:  # pragma: no cover - host failure
        raise ImportError(f"cannot load module at {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


owner = _load_module("_zkc_f0v2b1_reference_owner", OWNER_MODEL)

MAX_NODES = 1 << 15
MAX_DEPTH = 64
OUTER_KEYS = {
    "format",
    "scope",
    "maximum_sequence_length",
    "body_compilers",
    "laws",
    "view_order",
    "definitions",
    "views",
}


def _wire(value: Any) -> bytes:
    try:
        return json.dumps(
            value, sort_keys=True, separators=(",", ":"), ensure_ascii=True
        ).encode("ascii")
    except (TypeError, ValueError) as error:
        raise BoundedError("candidate contains a noncanonical JSON value") from error


def _digest(value: Any) -> str:
    return hashlib.sha256(_wire(value)).hexdigest()


def _load_source() -> dict[str, Any]:
    try:
        source = json.loads(SOURCE.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        raise BoundedError("cannot read the normalized B1 schema source") from error
    if type(source) is not dict or set(source) != OUTER_KEYS:
        raise BoundedError("normalized schema source has the wrong outer shape")
    if source["format"] != "zkc.formal-source-view-bodies-f0v2b1.schema-source.v0":
        raise BoundedError("normalized schema source has the wrong format")
    if source["scope"] != "f1r1b-finite-z3-schnorr-only":
        raise BoundedError("normalized schema source lost its bounded scope")
    return source


def _compile_source(source: dict[str, Any]) -> tuple[dict[str, Any], dict[str, str]]:
    maximum = source["maximum_sequence_length"]
    compilers = source["body_compilers"]
    laws = source["laws"]
    order = source["view_order"]
    definitions = source["definitions"]
    views = source["views"]
    if type(maximum) is not int or not 0 <= maximum <= 1 << 20:
        raise BoundedError("source sequence bound is invalid")
    for name, table in (("body compiler", compilers), ("law", laws)):
        if (
            type(table) is not list
            or not table
            or any(type(item) is not str or not item for item in table)
            or table != sorted(set(table))
        ):
            raise BoundedError(f"{name} catalog is not canonical sorted-unique")
    if (
        type(order) is not list
        or len(order) != 6
        or len(set(order)) != len(order)
        or type(definitions) is not dict
        or not definitions
        or type(views) is not dict
        or tuple(views) != tuple(order)
    ):
        raise BoundedError("view or definition catalog is malformed")

    visiting: set[str] = set()
    compiled_definitions: dict[str, Any] = {}
    used: set[str] = set()
    node_count = 0

    def compile_node(node: Any, depth: int) -> dict[str, Any]:
        nonlocal node_count
        node_count += 1
        if node_count > MAX_NODES or depth > MAX_DEPTH:
            raise BoundedError("schema expansion crossed its constitutional bound")
        if type(node) is not dict or len(node) != 1:
            raise BoundedError("schema source node has the wrong shape")
        if "ref" in node:
            name = node["ref"]
            if type(name) is not str or name not in definitions:
                raise BoundedError("schema source has an unknown definition reference")
            used.add(name)
            return copy.deepcopy(compile_definition(name, depth + 1))
        if "atom" in node:
            atom = node["atom"]
            if type(atom) is not dict or type(atom.get("kind")) is not str:
                raise BoundedError("schema source atom is malformed")
            kind = atom["kind"]
            if kind in {"unit", "meta-boolean"}:
                if set(atom) != {"kind"}:
                    raise BoundedError("primitive atom has surplus fields")
            elif kind == "natural":
                if (
                    set(atom) != {"kind", "max"}
                    or type(atom["max"]) is not int
                    or not 0 <= atom["max"] < 1 << 256
                ):
                    raise BoundedError("natural atom has an invalid bound")
            elif kind == "canonical-body":
                if (
                    set(atom) != {"kind", "compiler"}
                    or atom["compiler"] not in compilers
                ):
                    raise BoundedError("canonical-body atom has an unknown compiler")
            elif kind == "exact-profile-law":
                if set(atom) != {"kind", "law"} or atom["law"] not in laws:
                    raise BoundedError("law atom has an unknown exact law")
            else:
                raise BoundedError("schema source uses an unknown atom kind")
            return {"node": "atom", "atom": copy.deepcopy(atom)}
        if "record" in node or "variant" in node:
            kind = "record" if "record" in node else "variant"
            entries = node[kind]
            if type(entries) is not list or not entries:
                raise BoundedError(f"{kind} source must be nonempty")
            result: list[list[Any]] = []
            previous = -1
            for entry in entries:
                if type(entry) is not list or len(entry) != 2:
                    raise BoundedError(f"{kind} entry is malformed")
                ordinal, child = entry
                if type(ordinal) is not int or not 0 <= ordinal < 1 << 64:
                    raise BoundedError(f"{kind} ordinal is not a u64")
                if ordinal <= previous:
                    raise BoundedError(f"{kind} ordinals are not strict")
                previous = ordinal
                result.append([ordinal, compile_node(child, depth + 1)])
            key = "fields" if kind == "record" else "cases"
            return {"node": kind, key: result}
        if "sequence" in node:
            sequence = node["sequence"]
            if type(sequence) is not dict or set(sequence) != {"max", "element"}:
                raise BoundedError("sequence source is malformed")
            limit = sequence["max"]
            if type(limit) is not int or not 0 <= limit <= maximum:
                raise BoundedError("sequence source has an invalid bound")
            return {
                "node": "sequence",
                "max": limit,
                "element": compile_node(sequence["element"], depth + 1),
            }
        raise BoundedError("schema source uses an unknown constructor")

    def compile_definition(name: str, depth: int) -> dict[str, Any]:
        if name in compiled_definitions:
            return compiled_definitions[name]
        if name in visiting:
            raise BoundedError("schema definition graph is cyclic")
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
            raise BoundedError("view source entry is malformed")
        expected_owner = (
            "pir.protocol" if view == "ExecutionView" else "pir.interactive-core"
        )
        if entry["owner_subject_kind"] != expected_owner:
            raise BoundedError("view source entry has the wrong owner kind")
        schemas[view] = compile_node(entry["schema"], 0)
        owners[view] = expected_owner
    if set(definitions) != used:
        raise BoundedError(
            "schema source contains unused definitions: "
            + ", ".join(sorted(set(definitions) - used))
        )
    return schemas, owners


def _body(compiler: str, body: bytes) -> dict[str, Any]:
    if type(body) is not bytes or not body:
        raise BoundedError("owner body compiler produced an empty body")
    return {"compiler": compiler, "body": body.hex()}


def _datum_body(compiler: str, datum: object) -> dict[str, Any]:
    return _body(compiler, owner.k1.encode_datum(datum))


def _ordinal(compiler: str, value: int) -> dict[str, Any]:
    return _datum_body(compiler, owner.k1.Nat(value))


def _identifier(compiler: str, value: object) -> dict[str, Any]:
    try:
        body = value.internal_reference()
    except (AttributeError, TypeError, ValueError) as error:
        raise BoundedError(
            "owner identifier cannot form an internal reference"
        ) from error
    return _body(compiler, body)


def _value_ref(value: object) -> dict[str, Any]:
    return _datum_body("value-ref-body-v0", owner.value_ref_datum(value))


def _value_type(value: object) -> dict[str, Any]:
    return _datum_body("value-type-body-v0", owner.k1.value_type_datum(value))


def _module_ref(value: object) -> dict[str, Any]:
    return _datum_body(
        "module-declaration-ref-body-v0", owner.module_declaration_ref_datum(value)
    )


def _guard(value: object) -> dict[str, Any]:
    return _datum_body("guard-body-v0", owner._guard_datum(value))


def _law(profile_id: object, name: str) -> dict[str, Any]:
    return {
        "profile": profile_id.internal_reference().hex(),
        "kind": "pir.semantic-law",
        "name": name,
    }


def _variant(case: int, value: Any = None) -> dict[str, Any]:
    return {"case": case, "value": value}


def _scope_paths(core: object) -> tuple[tuple[int, ...], ...]:
    result: list[tuple[int, ...]] = []
    for ordinal, scope in enumerate(core.scopes):
        trail: list[int] = []
        seen: set[int] = set()
        current: int | None = ordinal
        while current is not None:
            if current in seen or not 0 <= current < len(core.scopes):
                raise BoundedError(
                    "admitted scope ancestry is not a finite rooted path"
                )
            seen.add(current)
            trail.append(current)
            current = core.scopes[current].parent
        result.append(tuple(reversed(trail)))
    return tuple(result)


def _output_types(core: object, occurrence: object) -> tuple[object, ...]:
    effect = occurrence.effect
    if type(effect) is owner.ProverMessageEffect:
        return (effect.payload_type,)
    if type(effect) is owner.ChallengeEffect:
        return (core.challenges[effect.challenge].value_type,)
    if type(effect) is owner.CheckEffect:
        return (owner.k1.BOOL,)
    if type(effect) is owner.TerminalEffect:
        return ()
    raise BoundedError("F0-V2B1 does not cover this effect constructor")


def _effect_value(effect: object) -> dict[str, Any]:
    if type(effect) is owner.ProverMessageEffect:
        return _variant(
            0, {0: _module_ref(effect.channel), 1: _value_type(effect.payload_type)}
        )
    if type(effect) is owner.ChallengeEffect:
        return _variant(2, _ordinal("challenge-ref-body-v0", effect.challenge))
    if type(effect) is owner.CheckEffect:
        return _variant(3, _ordinal("check-ref-body-v0", effect.check))
    if type(effect) is owner.TerminalEffect:
        return _variant(5, _ordinal("terminal-ref-body-v0", effect.terminal))
    raise BoundedError("F0-V2B1 does not cover this effect constructor")


def _pc_value(node: tuple[int, ...]) -> dict[str, Any]:
    tag, *arguments = node
    compiler = {
        0: "public-input-ref-body-v0",
        4: "scope-ref-body-v0",
        5: "binding-ref-body-v0",
        6: "occurrence-ref-body-v0",
        7: "occurrence-ref-body-v0",
        11: "terminal-ref-body-v0",
    }
    if tag == 8:
        return _variant(
            8,
            {
                0: _ordinal("occurrence-ref-body-v0", arguments[0]),
                1: arguments[1],
            },
        )
    if tag not in compiler or len(arguments) != 1:
        raise BoundedError("bounded PCNode is malformed")
    return _variant(tag, _ordinal(compiler[tag], arguments[0]))


def _pc_key(node: tuple[int, ...]) -> bytes:
    tag, *arguments = node
    if tag == 8:
        payload = owner.k1.DatumRecord(
            ((0, owner.k1.Nat(arguments[0])), (1, owner.k1.Nat(arguments[1])))
        )
    else:
        payload = owner.k1.Nat(arguments[0])
    return owner.k1.encode_datum(owner.k1.DatumVariant(tag, payload))


def _producer_node(reference: object) -> tuple[int, ...]:
    if type(reference) is owner.PublicInputRef:
        return (0, reference.ordinal)
    if type(reference) is owner.OccurrenceOutputRef:
        return (8, reference.occurrence, reference.output_ordinal)
    raise BoundedError("F0-V2B1 value producer is outside the bounded source slice")


def _pc_graph(core: object) -> tuple[dict[int, Any], dict[str, Any]]:
    nodes: set[tuple[int, ...]] = set()
    edges: set[tuple[tuple[int, ...], tuple[int, ...]]] = set()

    def add(node: tuple[int, ...]) -> tuple[int, ...]:
        nodes.add(node)
        return node

    def edge(source: tuple[int, ...], target: tuple[int, ...]) -> None:
        add(source)
        add(target)
        edges.add((source, target))

    for ordinal, _item in enumerate(core.public_inputs):
        add((0, ordinal))
    for ordinal, scope in enumerate(core.scopes):
        scope_node = add((4, ordinal))
        if scope.parent is not None:
            edge((4, scope.parent), scope_node)
    for ordinal, binding in enumerate(core.public_bindings):
        binding_node = add((5, ordinal))
        edge((4, binding.scope), binding_node)
        edge(_producer_node(binding.value), binding_node)

    challenge_occurrence: dict[int, int] = {}
    check_occurrence: dict[int, int] = {}
    terminal_occurrence: dict[int, int] = {}
    prior_terminal_nodes: list[tuple[int, ...]] = []
    output_types: dict[int, tuple[object, ...]] = {}
    for occurrence_ref, occurrence in enumerate(core.occurrences):
        activity = add((6, occurrence_ref))
        effect_node = add((7, occurrence_ref))
        edge((4, occurrence.scope), activity)
        if type(occurrence.guard) is owner.EvaluateGuard:
            for value in occurrence.guard.inputs:
                edge(_producer_node(value), activity)
        elif type(occurrence.guard) is not owner.AlwaysGuard:
            raise BoundedError("F0-V2B1 guard constructor is unsupported")
        for terminal in prior_terminal_nodes:
            edge(terminal, activity)
        edge(activity, effect_node)
        effect = occurrence.effect
        if type(effect) is owner.ChallengeEffect:
            if effect.challenge in challenge_occurrence:
                raise BoundedError("challenge occurrence backlink is not unique")
            challenge_occurrence[effect.challenge] = occurrence_ref
            challenge = core.challenges[effect.challenge]
            if type(challenge.correlation) is not owner.IndependentCorrelation:
                raise BoundedError("joint challenge derivation is deferred to F0-V2B2")
            if type(challenge.reduction_use) is not owner.ExclusiveReductionUse:
                raise BoundedError("shared challenge derivation is deferred to F0-V2B2")
            for value in challenge.public_conditions:
                edge(_producer_node(value), effect_node)
        elif type(effect) is owner.CheckEffect:
            if effect.check in check_occurrence:
                raise BoundedError("check occurrence backlink is not unique")
            check_occurrence[effect.check] = occurrence_ref
            for value in core.checks[effect.check].inputs:
                edge(_producer_node(value), effect_node)
        elif type(effect) is owner.TerminalEffect:
            if effect.terminal in terminal_occurrence:
                raise BoundedError("terminal occurrence backlink is not unique")
            terminal_occurrence[effect.terminal] = occurrence_ref
            terminal = core.terminals[effect.terminal]
            if terminal.claim_dispositions:
                raise BoundedError(
                    "claim disposition derivation is deferred to F0-V2B2"
                )
            for value in terminal.public_outputs:
                edge(_producer_node(value), effect_node)
            for check in terminal.required_true_checks:
                if check not in check_occurrence:
                    raise BoundedError(
                        "terminal cites a check without an earlier backlink"
                    )
                edge((8, check_occurrence[check], 0), effect_node)
            terminal_node = add((11, effect.terminal))
            edge(effect_node, terminal_node)
            prior_terminal_nodes.append(terminal_node)
        elif type(effect) is not owner.ProverMessageEffect:
            raise BoundedError("F0-V2B1 effect constructor is unsupported")
        output_types[occurrence_ref] = _output_types(core, occurrence)
        for output_ordinal, _value_type_item in enumerate(output_types[occurrence_ref]):
            edge(effect_node, (8, occurrence_ref, output_ordinal))

    if set(challenge_occurrence) != set(range(len(core.challenges))):
        raise BoundedError("challenge occurrence backlink coverage is incomplete")
    if set(check_occurrence) != set(range(len(core.checks))):
        raise BoundedError("check occurrence backlink coverage is incomplete")
    if set(terminal_occurrence) != set(range(len(core.terminals))):
        raise BoundedError("terminal occurrence backlink coverage is incomplete")

    incoming: dict[tuple[int, ...], set[tuple[int, ...]]] = {
        node: set() for node in nodes
    }
    outgoing: dict[tuple[int, ...], set[tuple[int, ...]]] = {
        node: set() for node in nodes
    }
    for source, target in edges:
        incoming[target].add(source)
        outgoing[source].add(target)
    available = sorted((node for node in nodes if not incoming[node]), key=_pc_key)
    remaining = {node: set(values) for node, values in incoming.items()}
    topological: list[tuple[int, ...]] = []
    while available:
        current = available.pop(0)
        topological.append(current)
        for target in outgoing[current]:
            remaining[target].remove(current)
            if (
                not remaining[target]
                and target not in topological
                and target not in available
            ):
                available.append(target)
        available.sort(key=_pc_key)
    if len(topological) != len(nodes):
        raise BoundedError("bounded PCGraph is cyclic")

    classes: dict[tuple[int, ...], int] = {}
    occurrence_by_ref = dict(enumerate(core.occurrences))
    for node in topological:
        joined = max((classes[source] for source in incoming[node]), default=0)
        tag = node[0]
        if tag == 0:
            value = 0
        elif tag == 7:
            effect = occurrence_by_ref[node[1]].effect
            if type(effect) in (owner.ProverMessageEffect, owner.ChallengeEffect):
                value = 1 if joined <= 1 else joined
            else:
                value = joined
        else:
            value = joined
        classes[node] = value

    activity_sinks = {(6, ordinal) for ordinal in range(len(core.occurrences))}
    check_sinks = {(7, occurrence) for occurrence in check_occurrence.values()}
    terminal_sinks = {(11, ordinal) for ordinal in range(len(core.terminals))}
    sinks = activity_sinks | check_sinks | terminal_sinks
    acceptance_sinks = check_sinks | {
        (11, ordinal)
        for ordinal, terminal in enumerate(core.terminals)
        if terminal.verdict is owner.TerminalVerdict.ACCEPT
    }
    eligible = all(classes[node] in (0, 1) for node in sinks)
    eligible = eligible and all(
        classes[(7, occurrence)] == 1 for occurrence in challenge_occurrence.values()
    )

    ordered_nodes = sorted(nodes, key=_pc_key)
    ordered_edges = sorted(edges, key=lambda pair: (_pc_key(pair[0]), _pc_key(pair[1])))
    graph_value = {
        0: [_pc_value(node) for node in ordered_nodes],
        1: [
            {0: _pc_value(source), 1: _pc_value(target)}
            for source, target in ordered_edges
        ],
        2: [_pc_value(node) for node in topological],
        3: [{0: _pc_value(node), 1: _variant(classes[node])} for node in ordered_nodes],
        4: [_pc_value(node) for node in sorted(sinks, key=_pc_key)],
        5: [_pc_value(node) for node in sorted(acceptance_sinks, key=_pc_key)],
        6: [],
    }
    evidence = {
        "node_count": len(nodes),
        "edge_count": len(edges),
        "topological_count": len(topological),
        "sink_count": len(sinks),
        "acceptance_sink_count": len(acceptance_sinks),
        "class_counts": {
            name: sum(value == tag for value in classes.values())
            for tag, name in enumerate(
                ("StaticPublic", "PublicHistory", "VerifierPrivate", "Invalid")
            )
        },
    }
    return graph_value, {
        **evidence,
        "eligible": eligible,
        "challenge_occurrence": challenge_occurrence,
        "check_occurrence": check_occurrence,
        "terminal_occurrence": terminal_occurrence,
        "output_types": output_types,
    }


def _derive_views(
    core_handle: object, protocol_handle: object
) -> tuple[dict[str, Any], dict[str, Any]]:
    if (
        type(core_handle) is not owner.AdmittedCore
        or core_handle._issuer is not owner._CORE_ISSUER
        or type(protocol_handle) is not owner.AdmittedFreshProtocol
        or protocol_handle._issuer is not owner._PROTOCOL_ISSUER
        or protocol_handle.core_handle is not core_handle
    ):
        raise BoundedError("view derivation requires exact live owner handles")
    core = core_handle.core
    if owner.core_id(core, core_handle.profile_id) != core_handle.core_id:
        raise BoundedError("retained Core body no longer matches its admitted ID")
    if (
        owner.protocol_id(core_handle.core_id, protocol_handle.profile_id)
        != protocol_handle.protocol_id
    ):
        raise BoundedError(
            "retained Protocol dependency no longer matches its admitted ID"
        )
    if any(
        (
            core.verifier_private_inputs,
            core.constants,
            core.derived_values,
            core.oracles,
            core.claims,
            core.reductions,
        )
    ):
        raise BoundedError("owner subject requires an F0-V2B2 constructor")
    paths = _scope_paths(core)
    graph, graph_evidence = _pc_graph(core)
    profile_id = core_handle.profile_id

    core_id = _identifier("core-id-body-v0", core_handle.core_id)
    protocol_id = _identifier("protocol-id-body-v0", protocol_handle.protocol_id)
    public_binding = {
        0: core_id,
        1: [
            {
                0: _ordinal("scope-ref-body-v0", ordinal),
                1: _variant(0)
                if scope.parent is None
                else _variant(1, _ordinal("scope-ref-body-v0", scope.parent)),
                2: _variant(0)
                if scope.opening is None
                else _variant(1, _ordinal("occurrence-ref-body-v0", scope.opening)),
                3: [_ordinal("scope-ref-body-v0", item) for item in paths[ordinal]],
            }
            for ordinal, scope in enumerate(core.scopes)
        ],
        2: [
            {
                0: _ordinal("binding-ref-body-v0", ordinal),
                1: _ordinal("scope-ref-body-v0", binding.scope),
                2: _variant(binding.binding_class.value),
                3: _value_ref(binding.value),
                4: _value_type(core.public_inputs[binding.value.ordinal].value_type),
            }
            for ordinal, binding in enumerate(core.public_bindings)
        ],
    }

    decisions: list[tuple[int, object]] = [
        (ordinal, occurrence)
        for ordinal, occurrence in enumerate(core.occurrences)
        if type(occurrence.effect) is owner.ProverMessageEffect
    ]
    decision_rows: list[dict[int, Any]] = []
    read_rows: list[dict[int, Any]] = []
    legal_rows: list[dict[int, Any]] = []
    for occurrence_ref, occurrence in decisions:
        move = _variant(0, _value_type(occurrence.effect.payload_type))
        prior = [item for item, _entry in decisions if item < occurrence_ref]
        decision_rows.append(
            {
                0: _ordinal("decision-ref-body-v0", occurrence_ref),
                1: _ordinal("occurrence-ref-body-v0", occurrence_ref),
                2: [
                    _ordinal("scope-ref-body-v0", item)
                    for item in paths[occurrence.scope]
                ],
                3: _guard(occurrence.guard),
                4: move,
                5: [_ordinal("decision-ref-body-v0", item) for item in prior],
            }
        )
        for input_ref, input_decl in enumerate(core.public_inputs):
            read_rows.append(
                {
                    0: _ordinal("decision-ref-body-v0", occurrence_ref),
                    1: _variant(1, _ordinal("public-input-ref-body-v0", input_ref)),
                    2: _value_type(input_decl.value_type),
                }
            )
        for binding_ref, binding in enumerate(core.public_bindings):
            if binding.scope == occurrence.scope:
                read_rows.append(
                    {
                        0: _ordinal("decision-ref-body-v0", occurrence_ref),
                        1: _variant(2, _ordinal("binding-ref-body-v0", binding_ref)),
                        2: _value_type(
                            core.public_inputs[binding.value.ordinal].value_type
                        ),
                    }
                )
        for prior_ref, prior_occurrence in enumerate(core.occurrences[:occurrence_ref]):
            prior_types = _output_types(core, prior_occurrence)
            if type(prior_occurrence.effect) is owner.ProverMessageEffect:
                read_rows.append(
                    {
                        0: _ordinal("decision-ref-body-v0", occurrence_ref),
                        1: _variant(3, _ordinal("occurrence-ref-body-v0", prior_ref)),
                        2: _value_type(prior_types[0]),
                    }
                )
                read_rows.append(
                    {
                        0: _ordinal("decision-ref-body-v0", occurrence_ref),
                        1: _variant(9, _ordinal("decision-ref-body-v0", prior_ref)),
                        2: _value_type(prior_types[0]),
                    }
                )
            elif type(prior_occurrence.effect) is owner.ChallengeEffect:
                read_rows.append(
                    {
                        0: _ordinal("decision-ref-body-v0", occurrence_ref),
                        1: _variant(4, _ordinal("occurrence-ref-body-v0", prior_ref)),
                        2: _value_type(prior_types[0]),
                    }
                )
        legal_rows.append(
            {
                0: _ordinal("decision-ref-body-v0", occurrence_ref),
                1: copy.deepcopy(move),
            }
        )
    read_rows.sort(key=_wire)
    strategy = {
        0: core_id,
        1: decision_rows,
        2: _law(profile_id, "core-admission-v0"),
        3: read_rows,
        4: legal_rows,
    }

    challenge_rows: list[dict[int, Any]] = []
    for challenge_ref, challenge in enumerate(core.challenges):
        occurrence_ref = graph_evidence["challenge_occurrence"][challenge_ref]
        challenge_rows.append(
            {
                0: _ordinal("challenge-ref-body-v0", challenge_ref),
                1: _ordinal("occurrence-ref-body-v0", occurrence_ref),
                2: _ordinal("scope-ref-body-v0", challenge.scope),
                3: _value_type(challenge.value_type),
                4: _module_ref(challenge.domain),
                5: _module_ref(challenge.fresh_law),
                6: _variant(0),
                7: _variant(0),
                8: [_value_ref(item) for item in challenge.public_conditions],
                9: [],
                10: [],
            }
        )
    public_coin = {
        0: core_id,
        1: graph,
        2: graph_evidence["eligible"],
        3: [],
        4: challenge_rows,
    }

    occurrence_rows: list[dict[int, Any]] = []
    value_rows: list[dict[int, Any]] = [
        {
            0: _value_ref(owner.PublicInputRef(ordinal)),
            1: _value_type(item.value_type),
            2: [],
        }
        for ordinal, item in enumerate(core.public_inputs)
    ]
    message_rows: list[dict[int, Any]] = []
    for occurrence_ref, occurrence in enumerate(core.occurrences):
        outputs = graph_evidence["output_types"][occurrence_ref]
        occurrence_rows.append(
            {
                0: _ordinal("occurrence-ref-body-v0", occurrence_ref),
                1: [
                    _ordinal("scope-ref-body-v0", item)
                    for item in paths[occurrence.scope]
                ],
                2: _guard(occurrence.guard),
                3: _effect_value(occurrence.effect),
                4: [_value_type(item) for item in outputs],
            }
        )
        for output_ordinal, output_type in enumerate(outputs):
            predecessors: tuple[object, ...] = ()
            if type(occurrence.effect) is owner.CheckEffect:
                predecessors = core.checks[occurrence.effect.check].inputs
            elif type(occurrence.effect) is owner.ChallengeEffect:
                predecessors = core.challenges[
                    occurrence.effect.challenge
                ].public_conditions
            value_rows.append(
                {
                    0: _value_ref(
                        owner.OccurrenceOutputRef(occurrence_ref, output_ordinal)
                    ),
                    1: _value_type(output_type),
                    2: [_value_ref(item) for item in predecessors],
                }
            )
        if type(occurrence.effect) is owner.ProverMessageEffect:
            message_rows.append(
                {
                    0: _ordinal("occurrence-ref-body-v0", occurrence_ref),
                    1: _variant(0),
                    2: _module_ref(occurrence.effect.channel),
                    3: _value_type(occurrence.effect.payload_type),
                }
            )
    check_rows = [
        {
            0: _ordinal("check-ref-body-v0", check_ref),
            1: _identifier("algorithm-ref-body-v0", check.algorithm),
            2: _identifier("evaluation-contract-id-body-v0", check.evaluation_contract),
            3: [_value_ref(item) for item in check.inputs],
            4: _ordinal(
                "occurrence-ref-body-v0", graph_evidence["check_occurrence"][check_ref]
            ),
        }
        for check_ref, check in enumerate(core.checks)
    ]
    terminal_rows = [
        {
            0: _ordinal("terminal-ref-body-v0", terminal_ref),
            1: _variant(terminal.verdict.value),
            2: [_value_ref(item) for item in terminal.public_outputs],
            3: [
                _ordinal("check-ref-body-v0", item)
                for item in terminal.required_true_checks
            ],
            4: [],
            5: _ordinal(
                "occurrence-ref-body-v0",
                graph_evidence["terminal_occurrence"][terminal_ref],
            ),
        }
        for terminal_ref, terminal in enumerate(core.terminals)
    ]
    effect = {
        0: core_id,
        1: occurrence_rows,
        2: value_rows,
        3: message_rows,
        4: [],
        5: check_rows,
        6: terminal_rows,
        7: [],
    }
    claim_reduction = {0: core_id, 1: [], 2: [], 3: []}

    resolver_rows = [
        {
            0: _ordinal("challenge-ref-body-v0", challenge_ref),
            1: _ordinal(
                "occurrence-ref-body-v0",
                graph_evidence["challenge_occurrence"][challenge_ref],
            ),
            2: _value_type(challenge.value_type),
            3: _module_ref(challenge.domain),
            4: _module_ref(challenge.fresh_law),
            5: [_value_ref(item) for item in challenge.public_conditions],
            6: [],
        }
        for challenge_ref, challenge in enumerate(core.challenges)
    ]
    runtime_schema = {
        0: [
            {
                0: _ordinal("occurrence-ref-body-v0", occurrence_ref),
                1: [
                    _value_type(item)
                    for item in graph_evidence["output_types"][occurrence_ref]
                ],
            }
            for occurrence_ref in range(len(core.occurrences))
        ],
        1: [
            {
                0: _ordinal("challenge-ref-body-v0", challenge_ref),
                1: _ordinal(
                    "occurrence-ref-body-v0",
                    graph_evidence["challenge_occurrence"][challenge_ref],
                ),
                2: _value_type(challenge.value_type),
            }
            for challenge_ref, challenge in enumerate(core.challenges)
        ],
        2: [],
        3: [
            {
                0: _ordinal("terminal-ref-body-v0", terminal_ref),
                1: _ordinal(
                    "occurrence-ref-body-v0",
                    graph_evidence["terminal_occurrence"][terminal_ref],
                ),
                2: _variant(terminal.verdict.value),
                3: [
                    _value_type(
                        core.public_inputs[item.ordinal].value_type
                        if type(item) is owner.PublicInputRef
                        else graph_evidence["output_types"][item.occurrence][
                            item.output_ordinal
                        ]
                    )
                    for item in terminal.public_outputs
                ],
            }
            for terminal_ref, terminal in enumerate(core.terminals)
        ],
    }
    execution = {
        0: protocol_id,
        1: core_id,
        2: _variant(0),
        3: _law(profile_id, "core-admission-v0"),
        4: resolver_rows,
        5: _law(profile_id, "execution-and-replay-v0"),
        6: runtime_schema,
        7: _variant(0),
        8: _law(profile_id, "execution-and-replay-v0"),
        9: _law(profile_id, "run-view-issuance-v0"),
    }
    values = {
        "PublicBindingView": public_binding,
        "StrategyDecisionView": strategy,
        "PublicCoinView": public_coin,
        "EffectView": effect,
        "ClaimReductionView": claim_reduction,
        "ExecutionView": execution,
    }
    evidence = {
        "core_digest": core_handle.core_id.digest.hex(),
        "protocol_digest": protocol_handle.protocol_id.digest.hex(),
        "decision_count": len(decision_rows),
        "guaranteed_read_count": len(read_rows),
        "occurrence_count": len(core.occurrences),
        "value_count": len(value_rows),
        "resolver_count": len(resolver_rows),
        "runtime_occurrence_count": len(runtime_schema[0]),
        "runtime_terminal_count": len(runtime_schema[3]),
        "pc_graph": {
            key: graph_evidence[key]
            for key in (
                "node_count",
                "edge_count",
                "topological_count",
                "sink_count",
                "acceptance_sink_count",
                "class_counts",
                "eligible",
            )
        },
    }
    return values, evidence


def _boundary(atom: dict[str, Any], value: Any) -> dict[str, Any]:
    kind = atom["kind"]
    if kind == "unit":
        if value is not None:
            raise BoundedError("unit schema received a non-unit value")
        return {"kind": "unit"}
    if kind == "natural":
        if type(value) is not int or not 0 <= value <= atom["max"]:
            raise BoundedError("natural value is outside its exact bound")
        return {"kind": "natural", "max": atom["max"]}
    if kind == "meta-boolean":
        if type(value) is not bool:
            raise BoundedError("MetaBoolean schema received a non-Boolean value")
        return {"kind": "meta-boolean"}
    if kind == "canonical-body":
        if type(value) is not dict or set(value) != {"compiler", "body"}:
            raise BoundedError("canonical-body value has the wrong shape")
        body = value["body"]
        if value["compiler"] != atom["compiler"] or type(body) is not str or not body:
            raise BoundedError(
                "canonical-body value uses the wrong compiler or empty body"
            )
        try:
            decoded = bytes.fromhex(body)
        except ValueError as error:
            raise BoundedError("canonical-body value is not hexadecimal") from error
        if decoded.hex() != body:
            raise BoundedError(
                "canonical-body value is not canonical lowercase hexadecimal"
            )
        return {"kind": "canonical-body", "compiler": atom["compiler"]}
    if kind == "exact-profile-law":
        if (
            type(value) is not dict
            or set(value) != {"profile", "kind", "name"}
            or value["kind"] != "pir.semantic-law"
            or value["name"] != atom["law"]
            or type(value["profile"]) is not str
            or not value["profile"]
        ):
            raise BoundedError("exact profile-law value was substituted")
        return {"kind": "exact-profile-law", "law": atom["law"]}
    raise BoundedError("unknown atom during view traversal")


def _enumerate(view: str, schema: dict[str, Any], value: Any) -> list[dict[str, Any]]:
    leaves: list[dict[str, Any]] = []

    def walk(node: dict[str, Any], current: Any, path: list[dict[str, int]]) -> None:
        kind = node["node"]
        if kind == "atom":
            if not path:
                raise BoundedError("view root cannot be an atom")
            leaves.append(
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
            expected = [ordinal for ordinal, _child in node["fields"]]
            if type(current) is not dict or list(current) != expected:
                raise BoundedError("record value does not match its exact fields")
            for ordinal, child in node["fields"]:
                walk(
                    child,
                    current[ordinal],
                    [*path, {"step": "field", "ordinal": ordinal}],
                )
            return
        if kind == "variant":
            if type(current) is not dict or set(current) != {"case", "value"}:
                raise BoundedError("variant value is malformed")
            matches = [
                child for case, child in node["cases"] if case == current["case"]
            ]
            if len(matches) != 1:
                raise BoundedError("variant selects an absent case")
            walk(
                matches[0],
                current["value"],
                [*path, {"step": "variant", "ordinal": current["case"]}],
            )
            return
        if kind == "sequence":
            if type(current) is not list or len(current) > node["max"]:
                raise BoundedError("sequence value is malformed or out of bounds")
            for ordinal, child_value in enumerate(current):
                walk(
                    node["element"],
                    child_value,
                    [*path, {"step": "sequence", "ordinal": ordinal}],
                )
            return
        raise BoundedError("unknown compiled schema node")

    walk(schema, value, [])
    return leaves


def _coordinate_key(coordinate: dict[str, Any]) -> tuple[Any, ...]:
    order = {"field": 0, "variant": 1, "sequence": 2}
    return (
        coordinate["view"],
        tuple((order[item["step"]], item["ordinal"]) for item in coordinate["path"]),
        _wire(coordinate["boundary"]),
    )


def admitted_handles() -> tuple[object, object]:
    fixture = owner.make_fixture()
    core = owner.admit_core(fixture.core_candidate, fixture.environment)
    if core.outcome != "Affirmative":
        raise BoundedError("exact F1-R1B Core no longer admits")
    protocol = owner.admit_fresh_protocol(
        core.handle, fixture.protocol_candidate, fixture.environment
    )
    if protocol.outcome != "Affirmative":
        raise BoundedError("exact F1-R1B Fresh Protocol no longer admits")
    return core.handle, protocol.handle


def build_candidate(
    core_handle: object | None = None, protocol_handle: object | None = None
) -> dict[str, Any]:
    if core_handle is None or protocol_handle is None:
        if core_handle is not None or protocol_handle is not None:
            raise BoundedError("both owner handles must be supplied together")
        core_handle, protocol_handle = admitted_handles()
    source = _load_source()
    schemas, owners = _compile_source(source)
    values, _owner_evidence = _derive_views(core_handle, protocol_handle)
    manifests = {
        view: [
            entry["coordinate"]
            for entry in _enumerate(view, schemas[view], values[view])
        ]
        for view in source["view_order"]
    }
    source_digest = _digest(source)
    return {
        "source_digest": source_digest,
        "schemas": schemas,
        "catalog": {
            view: {
                "owner_subject_kind": owners[view],
                "schema_digest": _digest(schemas[view]),
                "source_digest": source_digest,
            }
            for view in source["view_order"]
        },
        "values": values,
        "requested_manifests": manifests,
    }


def observe(
    candidate: object,
    core_handle: object | None = None,
    protocol_handle: object | None = None,
) -> dict[str, Any]:
    if core_handle is None or protocol_handle is None:
        if core_handle is not None or protocol_handle is not None:
            raise BoundedError("both owner handles must be supplied together")
        core_handle, protocol_handle = admitted_handles()
    if type(candidate) is not dict or set(candidate) != {
        "source_digest",
        "schemas",
        "catalog",
        "values",
        "requested_manifests",
    }:
        raise BoundedError("candidate package has the wrong outer shape")
    source = _load_source()
    order = source["view_order"]
    schemas, owners = _compile_source(source)
    expected_values, owner_evidence = _derive_views(core_handle, protocol_handle)
    if candidate["source_digest"] != _digest(source):
        raise BoundedError("candidate package names another schema source")
    if candidate["schemas"] != schemas:
        raise BoundedError("candidate package schema differs from compiled source")
    if candidate["values"] != expected_values:
        raise BoundedError("candidate view values differ from owner derivation")
    view_evidence: dict[str, Any] = {}
    total_leaves = 0
    for table in (
        candidate["catalog"],
        candidate["values"],
        candidate["requested_manifests"],
    ):
        if type(table) is not dict or tuple(table) != tuple(order):
            raise BoundedError("candidate view table is incomplete or reordered")
    for view in order:
        schema = schemas[view]
        value = expected_values[view]
        expected_catalog = {
            "owner_subject_kind": owners[view],
            "schema_digest": _digest(schema),
            "source_digest": _digest(source),
        }
        if candidate["catalog"][view] != expected_catalog:
            raise BoundedError("candidate schema catalog differs from owner source")
        leaves = _enumerate(view, schema, value)
        exact_manifest = [entry["coordinate"] for entry in leaves]
        supplied = candidate["requested_manifests"][view]
        if type(supplied) is not list or not supplied:
            raise BoundedError("complete manifest is empty or malformed")
        keys = [_coordinate_key(item) for item in supplied]
        if keys != sorted(keys) or len(keys) != len(set(keys)):
            raise BoundedError("complete manifest is not canonical sorted-unique")
        if supplied != exact_manifest:
            raise BoundedError("complete manifest differs from the active leaf set")
        view_evidence[view] = {
            "schema_digest": _digest(schema),
            "value_digest": _digest(value),
            "manifest_digest": _digest(exact_manifest),
            "leaf_count": len(leaves),
        }
        total_leaves += len(leaves)
    empty_families = {
        "oracles": len(expected_values["EffectView"][4]),
        "extensions": len(expected_values["EffectView"][7]),
        "claims": len(expected_values["ClaimReductionView"][1]),
        "reductions": len(expected_values["ClaimReductionView"][2]),
        "terminal_dispositions": len(expected_values["ClaimReductionView"][3]),
    }
    if any(empty_families.values()):
        raise BoundedError("B1 unsupported family unexpectedly became inhabited")
    return {
        "source_digest": _digest(source),
        "views": view_evidence,
        "total_leaf_count": total_leaves,
        "owner": owner_evidence,
        "explicit_empty_families": empty_families,
    }
