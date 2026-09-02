"""Clean-room bounded source compiler and finite owner-view oracle for F0-V2B1."""

from __future__ import annotations

from collections import deque
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


class ColdError(ValueError):
    """The independent bounded compiler or owner oracle refused its input."""


def _import_owner() -> ModuleType:
    name = "_zkc_f0v2b1_independent_owner"
    if name in sys.modules:
        return sys.modules[name]
    spec = importlib.util.spec_from_file_location(name, OWNER_MODEL)
    if spec is None or spec.loader is None:  # pragma: no cover - host failure
        raise ImportError(f"cannot load module at {OWNER_MODEL}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


owner = _import_owner()


def _bytes(value: Any) -> bytes:
    try:
        return json.dumps(
            value, sort_keys=True, separators=(",", ":"), ensure_ascii=True
        ).encode("ascii")
    except (TypeError, ValueError) as error:
        raise ColdError("cold path received a non-JSON value") from error


def _hash(value: Any) -> str:
    return hashlib.sha256(_bytes(value)).hexdigest()


def _source() -> dict[str, Any]:
    try:
        value = json.loads(SOURCE.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        raise ColdError("cold path cannot decode the schema source") from error
    required = (
        "format",
        "scope",
        "maximum_sequence_length",
        "body_compilers",
        "laws",
        "view_order",
        "definitions",
        "views",
    )
    if not isinstance(value, dict) or tuple(value) != required:
        raise ColdError("cold path sees another source outer record")
    if value["format"] != "zkc.formal-source-view-bodies-f0v2b1.schema-source.v0":
        raise ColdError("cold path sees another schema-source format")
    return value


def _compile(source: dict[str, Any]) -> tuple[dict[str, Any], dict[str, str]]:
    definitions = source["definitions"]
    compilers = source["body_compilers"]
    laws = source["laws"]
    limit = source["maximum_sequence_length"]
    order = source["view_order"]
    views = source["views"]
    if not isinstance(definitions, dict) or not isinstance(views, dict):
        raise ColdError("source catalogs are not maps")
    if tuple(views) != tuple(order) or len(order) != 6 or len(set(order)) != 6:
        raise ColdError("source view order is not exact")
    if compilers != sorted(set(compilers)) or laws != sorted(set(laws)):
        raise ColdError("source atom catalogs are not canonical")
    if type(limit) is not int or not 0 <= limit <= 1 << 20:
        raise ColdError("source maximum sequence length is invalid")

    def unfold(root: Any) -> tuple[dict[str, Any], set[str]]:
        produced: dict[tuple[Any, ...], dict[str, Any]] = {}
        active_refs: tuple[str, ...] = ()
        used: set[str] = set()
        work: list[tuple[Any, tuple[Any, ...], bool, tuple[str, ...], int]] = [
            (root, (), False, active_refs, 0)
        ]
        while work:
            node, path, returning, active, depth = work.pop()
            if depth > 64 or len(produced) + len(work) > 1 << 15:
                raise ColdError("cold schema expansion crossed its bound")
            if not isinstance(node, dict) or len(node) != 1:
                raise ColdError("cold schema node has the wrong shape")
            if "ref" in node:
                name = node["ref"]
                if not isinstance(name, str) or name not in definitions:
                    raise ColdError("cold schema has an unknown reference")
                if name in active:
                    raise ColdError("cold schema reference graph is cyclic")
                used.add(name)
                work.append(
                    (definitions[name], path, False, (*active, name), depth + 1)
                )
                continue
            key = next(iter(node))
            if key == "atom":
                atom = node[key]
                if not isinstance(atom, dict) or not isinstance(atom.get("kind"), str):
                    raise ColdError("cold atom is malformed")
                kind = atom["kind"]
                valid = (
                    kind in {"unit", "meta-boolean"}
                    and set(atom) == {"kind"}
                    or kind == "natural"
                    and set(atom) == {"kind", "max"}
                    and type(atom["max"]) is int
                    and 0 <= atom["max"] < 1 << 256
                    or kind == "canonical-body"
                    and set(atom) == {"kind", "compiler"}
                    and atom["compiler"] in compilers
                    or kind == "exact-profile-law"
                    and set(atom) == {"kind", "law"}
                    and atom["law"] in laws
                )
                if not valid:
                    raise ColdError("cold atom is outside the closed catalog")
                produced[path] = {"node": "atom", "atom": copy.deepcopy(atom)}
                continue
            if key in {"record", "variant"}:
                entries = node[key]
                if not isinstance(entries, list) or not entries:
                    raise ColdError("cold aggregate source is empty or malformed")
                ordinals = []
                for entry in entries:
                    if (
                        not isinstance(entry, list)
                        or len(entry) != 2
                        or type(entry[0]) is not int
                        or not 0 <= entry[0] < 1 << 64
                    ):
                        raise ColdError("cold aggregate entry is malformed")
                    ordinals.append(entry[0])
                if ordinals != sorted(set(ordinals)):
                    raise ColdError("cold aggregate ordinals are not strict")
                if not returning:
                    work.append((node, path, True, active, depth))
                    for position in range(len(entries) - 1, -1, -1):
                        work.append(
                            (
                                entries[position][1],
                                (*path, position),
                                False,
                                active,
                                depth + 1,
                            )
                        )
                else:
                    children = [
                        [ordinal, produced.pop((*path, position))]
                        for position, (ordinal, _child) in enumerate(entries)
                    ]
                    produced[path] = {
                        "node": key,
                        "fields" if key == "record" else "cases": children,
                    }
                continue
            if key == "sequence":
                sequence = node[key]
                if (
                    not isinstance(sequence, dict)
                    or set(sequence) != {"max", "element"}
                    or type(sequence["max"]) is not int
                    or not 0 <= sequence["max"] <= limit
                ):
                    raise ColdError("cold sequence source is malformed")
                if not returning:
                    work.append((node, path, True, active, depth))
                    work.append(
                        (sequence["element"], (*path, 0), False, active, depth + 1)
                    )
                else:
                    produced[path] = {
                        "node": "sequence",
                        "max": sequence["max"],
                        "element": produced.pop((*path, 0)),
                    }
                continue
            raise ColdError("cold schema source uses an unknown constructor")
        if set(produced) != {()}:
            raise ColdError("cold schema expansion left unresolved nodes")
        return produced[()], used

    schemas: dict[str, Any] = {}
    owners: dict[str, str] = {}
    used_all: set[str] = set()
    for view in order:
        entry = views[view]
        if not isinstance(entry, dict) or set(entry) != {
            "owner_subject_kind",
            "schema",
        }:
            raise ColdError("cold view declaration is malformed")
        expected = "pir.protocol" if view == "ExecutionView" else "pir.interactive-core"
        if entry["owner_subject_kind"] != expected:
            raise ColdError("cold view declaration has the wrong owner")
        schemas[view], used = unfold(entry["schema"])
        owners[view] = expected
        used_all |= used
    if used_all != set(definitions):
        raise ColdError("cold compiler found unused source definitions")
    return schemas, owners


def _datum(compiler: str, value: object) -> dict[str, str]:
    return {"compiler": compiler, "body": owner.k1.encode_datum(value).hex()}


def _id(compiler: str, value: object) -> dict[str, str]:
    return {"compiler": compiler, "body": value.internal_reference().hex()}


def _nat(compiler: str, value: int) -> dict[str, str]:
    return _datum(compiler, owner.k1.Nat(value))


def _v(case: int, value: Any = None) -> dict[str, Any]:
    return {"case": case, "value": value}


def _value_ref(value: object) -> dict[str, str]:
    return _datum("value-ref-body-v0", owner.value_ref_datum(value))


def _value_type(value: object) -> dict[str, str]:
    return _datum("value-type-body-v0", owner.k1.value_type_datum(value))


def _module(value: object) -> dict[str, str]:
    return _datum(
        "module-declaration-ref-body-v0", owner.module_declaration_ref_datum(value)
    )


def _guard(value: object) -> dict[str, str]:
    return _datum("guard-body-v0", owner._guard_datum(value))


def _law(profile: object, name: str) -> dict[str, str]:
    return {
        "profile": profile.internal_reference().hex(),
        "kind": "pir.semantic-law",
        "name": name,
    }


def _pc(node: tuple[int, ...]) -> dict[str, Any]:
    tag = node[0]
    if tag == 8:
        return _v(
            8,
            {
                0: _nat("occurrence-ref-body-v0", node[1]),
                1: node[2],
            },
        )
    compiler = {
        0: "public-input-ref-body-v0",
        4: "scope-ref-body-v0",
        5: "binding-ref-body-v0",
        6: "occurrence-ref-body-v0",
        7: "occurrence-ref-body-v0",
        11: "terminal-ref-body-v0",
    }.get(tag)
    if compiler is None or len(node) != 2:
        raise ColdError("cold PCNode is outside the bounded node algebra")
    return _v(tag, _nat(compiler, node[1]))


def _pc_wire(node: tuple[int, ...]) -> bytes:
    if node[0] == 8:
        payload = owner.k1.DatumRecord(
            ((0, owner.k1.Nat(node[1])), (1, owner.k1.Nat(node[2])))
        )
    else:
        payload = owner.k1.Nat(node[1])
    return owner.k1.encode_datum(owner.k1.DatumVariant(node[0], payload))


def _admit() -> tuple[object, object]:
    fixture = owner.make_fixture()
    core_result = owner.admit_core(fixture.core_candidate, fixture.environment)
    if core_result.outcome != "Affirmative":
        raise ColdError("cold owner model did not admit the finite Core")
    protocol_result = owner.admit_fresh_protocol(
        core_result.handle, fixture.protocol_candidate, fixture.environment
    )
    if protocol_result.outcome != "Affirmative":
        raise ColdError("cold owner model did not admit the Fresh Protocol")
    return core_result.handle, protocol_result.handle


def _fixture_shape(core: object) -> None:
    expected_effects = (
        "ProverMessageEffect",
        "ChallengeEffect",
        "ProverMessageEffect",
        "CheckEffect",
        "TerminalEffect",
        "TerminalEffect",
    )
    if (
        len(core.public_inputs) != 1
        or core.verifier_private_inputs
        or core.constants
        or core.derived_values
        or len(core.scopes) != 1
        or len(core.public_bindings) != 1
        or len(core.challenges) != 1
        or core.oracles
        or len(core.checks) != 1
        or core.claims
        or core.reductions
        or len(core.terminals) != 2
        or tuple(type(item.effect).__name__ for item in core.occurrences)
        != expected_effects
    ):
        raise ColdError(
            "cold finite owner oracle does not recognize this constructor shape"
        )
    if (
        core.scopes[0].parent is not None
        or core.scopes[0].opening is not None
        or core.public_bindings[0].scope != 0
        or type(core.public_bindings[0].value).__name__ != "PublicInputRef"
        or core.public_bindings[0].value.ordinal != 0
        or type(core.challenges[0].correlation).__name__ != "IndependentCorrelation"
        or type(core.challenges[0].reduction_use).__name__ != "ExclusiveReductionUse"
        or core.challenges[0].public_conditions
        or core.terminals[0].verdict.name != "ACCEPT"
        or core.terminals[0].required_true_checks != (0,)
        or core.terminals[1].verdict.name != "REJECT"
    ):
        raise ColdError("cold finite owner oracle found semantic fixture drift")


def _derive(
    core_handle: object, protocol_handle: object
) -> tuple[dict[str, Any], dict[str, Any]]:
    if (
        type(core_handle).__name__ != "AdmittedCore"
        or type(protocol_handle).__name__ != "AdmittedFreshProtocol"
        or protocol_handle.core_handle is not core_handle
    ):
        raise ColdError("cold derivation requires paired live owner handles")
    core = core_handle.core
    _fixture_shape(core)
    if owner.core_id(core, core_handle.profile_id) != core_handle.core_id:
        raise ColdError("cold derivation found a mutable retained Core")
    if (
        owner.protocol_id(core_handle.core_id, protocol_handle.profile_id)
        != protocol_handle.protocol_id
    ):
        raise ColdError("cold derivation found a mutable retained Protocol")

    z3 = core.public_inputs[0].value_type
    boolean = owner.k1.BOOL
    core_id = _id("core-id-body-v0", core_handle.core_id)
    protocol_id = _id("protocol-id-body-v0", protocol_handle.protocol_id)
    occurrence_types = ((z3,), (z3,), (z3,), (boolean,), (), ())
    occurrence_effects = (
        _v(0, {0: _module(core.occurrences[0].effect.channel), 1: _value_type(z3)}),
        _v(2, _nat("challenge-ref-body-v0", 0)),
        _v(0, {0: _module(core.occurrences[2].effect.channel), 1: _value_type(z3)}),
        _v(3, _nat("check-ref-body-v0", 0)),
        _v(5, _nat("terminal-ref-body-v0", 0)),
        _v(5, _nat("terminal-ref-body-v0", 1)),
    )

    public_binding = {
        0: core_id,
        1: [
            {
                0: _nat("scope-ref-body-v0", 0),
                1: _v(0),
                2: _v(0),
                3: [_nat("scope-ref-body-v0", 0)],
            }
        ],
        2: [
            {
                0: _nat("binding-ref-body-v0", 0),
                1: _nat("scope-ref-body-v0", 0),
                2: _v(core.public_bindings[0].binding_class.value),
                3: _value_ref(core.public_bindings[0].value),
                4: _value_type(z3),
            }
        ],
    }

    move = _v(0, _value_type(z3))
    decision_rows = [
        {
            0: _nat("decision-ref-body-v0", 0),
            1: _nat("occurrence-ref-body-v0", 0),
            2: [_nat("scope-ref-body-v0", 0)],
            3: _guard(core.occurrences[0].guard),
            4: copy.deepcopy(move),
            5: [],
        },
        {
            0: _nat("decision-ref-body-v0", 2),
            1: _nat("occurrence-ref-body-v0", 2),
            2: [_nat("scope-ref-body-v0", 0)],
            3: _guard(core.occurrences[2].guard),
            4: copy.deepcopy(move),
            5: [_nat("decision-ref-body-v0", 0)],
        },
    ]
    reads = [
        (0, 1, "public-input-ref-body-v0", 0),
        (0, 2, "binding-ref-body-v0", 0),
        (2, 1, "public-input-ref-body-v0", 0),
        (2, 2, "binding-ref-body-v0", 0),
        (2, 3, "occurrence-ref-body-v0", 0),
        (2, 4, "occurrence-ref-body-v0", 1),
        (2, 9, "decision-ref-body-v0", 0),
    ]
    read_rows = [
        {
            0: _nat("decision-ref-body-v0", decision),
            1: _v(case, _nat(compiler, ordinal)),
            2: _value_type(z3),
        }
        for decision, case, compiler, ordinal in reads
    ]
    read_rows.sort(key=_bytes)
    strategy = {
        0: core_id,
        1: decision_rows,
        2: _law(core_handle.profile_id, "core-admission-v0"),
        3: read_rows,
        4: [
            {0: _nat("decision-ref-body-v0", value), 1: copy.deepcopy(move)}
            for value in (0, 2)
        ],
    }

    p0 = (0, 0)
    scope = (4, 0)
    binding = (5, 0)
    activities = tuple((6, value) for value in range(6))
    effects = tuple((7, value) for value in range(6))
    outputs = tuple((8, value, 0) for value in range(4))
    terminals = ((11, 0), (11, 1))
    nodes = (p0, scope, binding, *activities, *effects, *outputs, *terminals)
    edges = {
        (scope, binding),
        (p0, binding),
        *((scope, value) for value in activities),
        (outputs[3], activities[4]),
        (terminals[0], activities[5]),
        *((activities[index], effects[index]) for index in range(6)),
        (p0, effects[3]),
        (outputs[0], effects[3]),
        (outputs[1], effects[3]),
        (outputs[2], effects[3]),
        (outputs[3], effects[4]),
        *((effects[index], outputs[index]) for index in range(4)),
        (effects[4], terminals[0]),
        (effects[5], terminals[1]),
    }
    ordered_nodes = sorted(nodes, key=_pc_wire)
    ordered_edges = sorted(
        edges, key=lambda pair: (_pc_wire(pair[0]), _pc_wire(pair[1]))
    )
    topological = (
        p0,
        scope,
        binding,
        activities[0],
        activities[1],
        activities[2],
        activities[3],
        effects[0],
        effects[1],
        effects[2],
        outputs[0],
        outputs[1],
        outputs[2],
        effects[3],
        outputs[3],
        activities[4],
        effects[4],
        terminals[0],
        activities[5],
        effects[5],
        terminals[1],
    )
    static = {p0, scope, binding, *activities[:4]}
    sinks = {*activities, effects[3], *terminals}
    acceptance = {effects[3], terminals[0]}
    graph = {
        0: [_pc(value) for value in ordered_nodes],
        1: [{0: _pc(left), 1: _pc(right)} for left, right in ordered_edges],
        2: [_pc(value) for value in topological],
        3: [
            {0: _pc(value), 1: _v(0 if value in static else 1)}
            for value in ordered_nodes
        ],
        4: [_pc(value) for value in sorted(sinks, key=_pc_wire)],
        5: [_pc(value) for value in sorted(acceptance, key=_pc_wire)],
        6: [],
    }
    challenge = core.challenges[0]
    public_coin = {
        0: core_id,
        1: graph,
        2: True,
        3: [],
        4: [
            {
                0: _nat("challenge-ref-body-v0", 0),
                1: _nat("occurrence-ref-body-v0", 1),
                2: _nat("scope-ref-body-v0", 0),
                3: _value_type(z3),
                4: _module(challenge.domain),
                5: _module(challenge.fresh_law),
                6: _v(0),
                7: _v(0),
                8: [],
                9: [],
                10: [],
            }
        ],
    }

    occurrence_rows = [
        {
            0: _nat("occurrence-ref-body-v0", index),
            1: [_nat("scope-ref-body-v0", 0)],
            2: _guard(occurrence.guard),
            3: occurrence_effects[index],
            4: [_value_type(item) for item in occurrence_types[index]],
        }
        for index, occurrence in enumerate(core.occurrences)
    ]
    value_rows = [
        {0: _value_ref(owner.PublicInputRef(0)), 1: _value_type(z3), 2: []},
        {
            0: _value_ref(owner.OccurrenceOutputRef(0, 0)),
            1: _value_type(z3),
            2: [],
        },
        {
            0: _value_ref(owner.OccurrenceOutputRef(1, 0)),
            1: _value_type(z3),
            2: [],
        },
        {
            0: _value_ref(owner.OccurrenceOutputRef(2, 0)),
            1: _value_type(z3),
            2: [],
        },
        {
            0: _value_ref(owner.OccurrenceOutputRef(3, 0)),
            1: _value_type(boolean),
            2: [_value_ref(value) for value in core.checks[0].inputs],
        },
    ]
    messages = [
        {
            0: _nat("occurrence-ref-body-v0", index),
            1: _v(0),
            2: _module(core.occurrences[index].effect.channel),
            3: _value_type(z3),
        }
        for index in (0, 2)
    ]
    check = core.checks[0]
    checks = [
        {
            0: _nat("check-ref-body-v0", 0),
            1: _id("algorithm-ref-body-v0", check.algorithm),
            2: _id("evaluation-contract-id-body-v0", check.evaluation_contract),
            3: [_value_ref(item) for item in check.inputs],
            4: _nat("occurrence-ref-body-v0", 3),
        }
    ]
    terminal_rows = [
        {
            0: _nat("terminal-ref-body-v0", index),
            1: _v(item.verdict.value),
            2: [],
            3: [
                _nat("check-ref-body-v0", value) for value in item.required_true_checks
            ],
            4: [],
            5: _nat("occurrence-ref-body-v0", index + 4),
        }
        for index, item in enumerate(core.terminals)
    ]
    effect = {
        0: core_id,
        1: occurrence_rows,
        2: value_rows,
        3: messages,
        4: [],
        5: checks,
        6: terminal_rows,
        7: [],
    }

    resolver = {
        0: _nat("challenge-ref-body-v0", 0),
        1: _nat("occurrence-ref-body-v0", 1),
        2: _value_type(z3),
        3: _module(challenge.domain),
        4: _module(challenge.fresh_law),
        5: [],
        6: [],
    }
    runtime = {
        0: [
            {
                0: _nat("occurrence-ref-body-v0", index),
                1: [_value_type(item) for item in occurrence_types[index]],
            }
            for index in range(6)
        ],
        1: [
            {
                0: _nat("challenge-ref-body-v0", 0),
                1: _nat("occurrence-ref-body-v0", 1),
                2: _value_type(z3),
            }
        ],
        2: [],
        3: [
            {
                0: _nat("terminal-ref-body-v0", index),
                1: _nat("occurrence-ref-body-v0", index + 4),
                2: _v(item.verdict.value),
                3: [],
            }
            for index, item in enumerate(core.terminals)
        ],
    }
    execution = {
        0: protocol_id,
        1: core_id,
        2: _v(0),
        3: _law(core_handle.profile_id, "core-admission-v0"),
        4: [resolver],
        5: _law(core_handle.profile_id, "execution-and-replay-v0"),
        6: runtime,
        7: _v(0),
        8: _law(core_handle.profile_id, "execution-and-replay-v0"),
        9: _law(core_handle.profile_id, "run-view-issuance-v0"),
    }
    values = {
        "PublicBindingView": public_binding,
        "StrategyDecisionView": strategy,
        "PublicCoinView": public_coin,
        "EffectView": effect,
        "ClaimReductionView": {0: core_id, 1: [], 2: [], 3: []},
        "ExecutionView": execution,
    }
    evidence = {
        "core_digest": core_handle.core_id.digest.hex(),
        "protocol_digest": protocol_handle.protocol_id.digest.hex(),
        "decision_count": 2,
        "guaranteed_read_count": 7,
        "occurrence_count": 6,
        "value_count": 5,
        "resolver_count": 1,
        "runtime_occurrence_count": 6,
        "runtime_terminal_count": 2,
        "pc_graph": {
            "node_count": 21,
            "edge_count": 27,
            "topological_count": 21,
            "sink_count": 9,
            "acceptance_sink_count": 2,
            "class_counts": {
                "StaticPublic": 7,
                "PublicHistory": 14,
                "VerifierPrivate": 0,
                "Invalid": 0,
            },
            "eligible": True,
        },
    }
    return values, evidence


def _boundary(atom: dict[str, Any], value: Any) -> dict[str, Any]:
    kind = atom["kind"]
    if kind == "unit":
        if value is not None:
            raise ColdError("cold unit leaf is inhabited")
        return {"kind": "unit"}
    if kind == "natural":
        if type(value) is not int or not 0 <= value <= atom["max"]:
            raise ColdError("cold natural leaf is outside its bound")
        return {"kind": "natural", "max": atom["max"]}
    if kind == "meta-boolean":
        if type(value) is not bool:
            raise ColdError("cold MetaBoolean leaf has another type")
        return {"kind": "meta-boolean"}
    if kind == "canonical-body":
        if not isinstance(value, dict) or set(value) != {"compiler", "body"}:
            raise ColdError("cold canonical body has another shape")
        body = value["body"]
        if (
            value["compiler"] != atom["compiler"]
            or not isinstance(body, str)
            or not body
        ):
            raise ColdError("cold canonical body uses another compiler")
        try:
            decoded = bytes.fromhex(body)
        except ValueError as error:
            raise ColdError("cold canonical body is not hexadecimal") from error
        if decoded.hex() != body:
            raise ColdError("cold canonical body is not canonical hexadecimal")
        return {"kind": "canonical-body", "compiler": atom["compiler"]}
    if kind == "exact-profile-law":
        if (
            not isinstance(value, dict)
            or set(value) != {"profile", "kind", "name"}
            or value["kind"] != "pir.semantic-law"
            or value["name"] != atom["law"]
            or not isinstance(value["profile"], str)
            or not value["profile"]
        ):
            raise ColdError("cold law leaf was substituted")
        return {"kind": "exact-profile-law", "law": atom["law"]}
    raise ColdError("cold traversal reached an unknown atom")


def _leaves(view: str, schema: dict[str, Any], value: Any) -> list[dict[str, Any]]:
    leaves: list[dict[str, Any]] = []
    queue: deque[tuple[dict[str, Any], Any, list[dict[str, int]]]] = deque(
        [(schema, value, [])]
    )
    while queue:
        node, current, path = queue.popleft()
        kind = node.get("node")
        if kind == "atom":
            if not path:
                raise ColdError("cold view root is atomic")
            leaves.append(
                {
                    "coordinate": {
                        "view": view,
                        "path": path,
                        "boundary": _boundary(node["atom"], current),
                    },
                    "value": copy.deepcopy(current),
                }
            )
        elif kind == "record":
            expected = [ordinal for ordinal, _child in node["fields"]]
            if not isinstance(current, dict) or list(current) != expected:
                raise ColdError("cold record value has another field set")
            for ordinal, child in node["fields"]:
                queue.append(
                    (
                        child,
                        current[ordinal],
                        [*path, {"step": "field", "ordinal": ordinal}],
                    )
                )
        elif kind == "variant":
            if not isinstance(current, dict) or set(current) != {"case", "value"}:
                raise ColdError("cold variant value is malformed")
            selected = [
                child for case, child in node["cases"] if case == current["case"]
            ]
            if len(selected) != 1:
                raise ColdError("cold variant selected an absent arm")
            queue.append(
                (
                    selected[0],
                    current["value"],
                    [*path, {"step": "variant", "ordinal": current["case"]}],
                )
            )
        elif kind == "sequence":
            if not isinstance(current, list) or len(current) > node["max"]:
                raise ColdError("cold sequence value is malformed or too long")
            for ordinal, child_value in enumerate(current):
                queue.append(
                    (
                        node["element"],
                        child_value,
                        [*path, {"step": "sequence", "ordinal": ordinal}],
                    )
                )
        else:
            raise ColdError("cold traversal reached an unknown schema node")
    leaves.sort(key=lambda leaf: _coordinate_key(leaf["coordinate"]))
    return leaves


def _coordinate_key(coordinate: dict[str, Any]) -> tuple[Any, ...]:
    rank = {"field": 0, "variant": 1, "sequence": 2}
    return (
        coordinate["view"],
        tuple((rank[step["step"]], step["ordinal"]) for step in coordinate["path"]),
        _bytes(coordinate["boundary"]),
    )


def build_candidate(
    core: object | None = None, protocol: object | None = None
) -> dict[str, Any]:
    if core is None or protocol is None:
        if core is not None or protocol is not None:
            raise ColdError("both cold owner handles must be supplied together")
        core, protocol = _admit()
    source = _source()
    schemas, owners = _compile(source)
    values, _evidence = _derive(core, protocol)
    manifests = {
        view: [
            leaf["coordinate"] for leaf in _leaves(view, schemas[view], values[view])
        ]
        for view in source["view_order"]
    }
    source_digest = _hash(source)
    return {
        "source_digest": source_digest,
        "schemas": schemas,
        "catalog": {
            view: {
                "owner_subject_kind": owners[view],
                "schema_digest": _hash(schemas[view]),
                "source_digest": source_digest,
            }
            for view in source["view_order"]
        },
        "values": values,
        "requested_manifests": manifests,
    }


def observe(
    candidate: object,
    core: object | None = None,
    protocol: object | None = None,
) -> dict[str, Any]:
    if not isinstance(candidate, dict) or set(candidate) != {
        "source_digest",
        "schemas",
        "catalog",
        "values",
        "requested_manifests",
    }:
        raise ColdError("cold candidate has another outer shape")
    if core is None or protocol is None:
        if core is not None or protocol is not None:
            raise ColdError("both cold owner handles must be supplied together")
        core, protocol = _admit()
    source = _source()
    order = source["view_order"]
    schemas, owners = _compile(source)
    values, owner_evidence = _derive(core, protocol)
    if candidate["source_digest"] != _hash(source):
        raise ColdError("cold candidate cites another schema source")
    if candidate["schemas"] != schemas:
        raise ColdError("cold candidate schemas differ from source expansion")
    if candidate["values"] != values:
        raise ColdError("cold candidate values differ from the finite owner oracle")
    for table in (
        candidate["catalog"],
        candidate["values"],
        candidate["requested_manifests"],
    ):
        if not isinstance(table, dict) or tuple(table) != tuple(order):
            raise ColdError("cold candidate has an incomplete view table")
    view_evidence: dict[str, Any] = {}
    total = 0
    for view in order:
        expected_catalog = {
            "owner_subject_kind": owners[view],
            "schema_digest": _hash(schemas[view]),
            "source_digest": _hash(source),
        }
        if candidate["catalog"][view] != expected_catalog:
            raise ColdError("cold candidate catalog differs from the source")
        leaves = _leaves(view, schemas[view], values[view])
        exact = [leaf["coordinate"] for leaf in leaves]
        supplied = candidate["requested_manifests"][view]
        if not isinstance(supplied, list) or not supplied:
            raise ColdError("cold complete manifest is empty")
        keys = [_coordinate_key(item) for item in supplied]
        if keys != sorted(keys) or len(keys) != len(set(keys)):
            raise ColdError("cold complete manifest is not canonical sorted-unique")
        if supplied != exact:
            raise ColdError("cold complete manifest differs from active leaves")
        view_evidence[view] = {
            "schema_digest": _hash(schemas[view]),
            "value_digest": _hash(values[view]),
            "manifest_digest": _hash(exact),
            "leaf_count": len(leaves),
        }
        total += len(leaves)
    empty = {
        "oracles": len(values["EffectView"][4]),
        "extensions": len(values["EffectView"][7]),
        "claims": len(values["ClaimReductionView"][1]),
        "reductions": len(values["ClaimReductionView"][2]),
        "terminal_dispositions": len(values["ClaimReductionView"][3]),
    }
    if any(empty.values()):
        raise ColdError("cold bounded-only family is unexpectedly inhabited")
    return {
        "source_digest": _hash(source),
        "views": view_evidence,
        "total_leaf_count": total,
        "owner": owner_evidence,
        "explicit_empty_families": empty,
    }
