"""Independent canonical-byte six-view projector for F0-V2B2D3.

This path never imports the typed D1 or D3 owner.  It authenticates and parses
the five frozen D1 carriers through D1's cold path, then composes the already
checked B1--B5B2 cold projection laws over the complete constructor census.
"""

from __future__ import annotations

import hashlib
import importlib.util
from pathlib import Path
import sys
from types import ModuleType
from typing import Any, Mapping


ROOT = Path(__file__).resolve().parents[2]
D1_COLD = ROOT / "evaluation/formal-source-integrated-graph-f0v2b2d1/independent.py"
B4_COLD = ROOT / "evaluation/formal-source-module-owner-projections-f0v2b2c1b4/independent.py"


class ColdIntegratedViewsError(ValueError):
    """Fail-closed result from the D3 independent path."""


def _load(name: str, path: Path) -> ModuleType:
    if name in sys.modules:
        return sys.modules[name]
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:  # pragma: no cover - host failure
        raise ImportError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


d1 = _load("_zkc_f0v2b2d3_cold_d1", D1_COLD)
b4 = _load("_zkc_f0v2b2d3_cold_b4", B4_COLD)
schema = d1.schema
b3 = d1.b3cold
oracle = d1.oraclecold
cold = d1.cold
codec = d1.codec
k1 = d1.k1

VIEW_SCHEMAS: dict[str, Any] = {}
VIEW_ORDER: tuple[str, ...] = ()


def configure(profile_digest: str, profile_body_sha256: str) -> dict[str, Any]:
    """Compile the exact B5B2 candidate grammar through D1's cold route."""

    global VIEW_SCHEMAS, VIEW_ORDER
    evidence = d1.configure(profile_digest, profile_body_sha256)
    VIEW_SCHEMAS = d1.VIEW_SCHEMAS
    VIEW_ORDER = tuple(schema.SCHEMA_SOURCE["view_order"])
    return evidence


def _authenticate(
    core_profiled_body: bytes,
    core_reference: bytes,
    protocol_profiled_body: bytes,
    protocol_reference: bytes,
    module_sources: tuple[tuple[bytes, bytes], ...],
    algorithm_preimages: tuple[tuple[bytes, bytes], ...],
    evaluation_contract_reference: bytes,
) -> tuple[dict[str, Any], dict[int, dict[str, Any]]]:
    try:
        core_profile, core_domain = cold._authenticated_subject(
            core_profiled_body,
            core_reference,
            "pir.interactive-core",
            "cold integrated Core",
        )
        protocol_profile, protocol_domain = cold._authenticated_subject(
            protocol_profiled_body,
            protocol_reference,
            "pir.protocol",
            "cold integrated Fresh Protocol",
        )
    except Exception as error:
        raise ColdIntegratedViewsError(str(error)) from error
    if core_profile != protocol_profile:
        raise ColdIntegratedViewsError("Core and Protocol profiles differ")
    protocol_core, interpretation = d1._record(
        protocol_domain, (0, 1), "Fresh Protocol"
    )
    tag, payload = d1._variant(interpretation, {0}, "Fresh interpretation")
    if tag != 0:  # pragma: no cover - parser set closes this
        raise ColdIntegratedViewsError("Protocol interpretation differs")
    d1._unit(payload, "Fresh interpretation payload")
    if d1._bytes(protocol_core, "Fresh Protocol Core") != core_reference:
        raise ColdIntegratedViewsError("Fresh Protocol names another Core")
    domain_body = k1.encode_datum(core_domain)
    if hashlib.sha256(domain_body).hexdigest() not in d1.SUPPORTED_DOMAIN_SHA256:
        raise ColdIntegratedViewsError("Core lies outside five exact D1 carriers")
    core = d1._decode_core(core_domain)
    sources = d1._source_closure(core["used_modules"], module_sources)
    modules = d1._module_occurrences(core, sources)
    d1._algorithm_closure(
        core, modules, algorithm_preimages, evaluation_contract_reference
    )
    return core, modules


def _output_types(
    core: dict[str, Any], modules: Mapping[int, dict[str, Any]]
) -> tuple[tuple[object, ...], ...]:
    rows: list[tuple[object, ...]] = []
    for occurrence_ref, occurrence in enumerate(core["occurrences"]):
        effect = occurrence["effect"]
        tag = effect["tag"]
        if tag in (0, 1):
            rows.append((effect["payload_type"],))
        elif tag == 2:
            rows.append((core["challenges"][effect["challenge"]]["type"],))
        elif tag == 3:
            rows.append((k1.value_type_datum(k1.BOOL),))
        elif tag in (4, 5):
            rows.append(())
        elif tag == 6:
            oracle_tag = effect["oracle_tag"]
            if oracle_tag == 0:
                rows.append(oracle._publication_types(core["oracles"][effect["oracle"]]))
            elif oracle_tag == 1:
                rows.append(())
            else:
                query = core["occurrences"][effect["query"]]["effect"]
                rows.append((oracle._answer_type(core["oracles"][query["oracle"]]),))
        elif tag == 7:
            rows.append(tuple(item["type"] for item in modules[occurrence_ref]["outputs"]))
        else:  # pragma: no cover - parser closes this
            raise ColdIntegratedViewsError("effect output rule is absent")
    return tuple(rows)


def _guard_implies(use: dict[str, Any], source: dict[str, Any]) -> bool:
    return source["tag"] == 0 or use["body"] == source["body"]


def _scope_is_ancestor(
    paths: tuple[tuple[int, ...], ...], ancestor: int, descendant: int
) -> bool:
    return ancestor in paths[descendant]


def _module_effect(effect: dict[str, Any]) -> dict[str, Any]:
    """Parse the admitted atom through B4's unchanged cold parser."""

    try:
        return b4._effect(effect["body"])
    except Exception as error:
        raise ColdIntegratedViewsError(str(error)) from error


def _effect_value(effect: dict[str, Any]) -> dict[str, Any]:
    tag = effect["tag"]
    try:
        if tag in (0, 1):
            return cold._effect_value(effect)
        if tag in (2, 4):
            return b3._effect_value(effect)
        if tag in (3, 5):
            return schema._effect_value(effect)
        if tag == 6:
            return oracle._effect_value(effect)
        if tag == 7:
            return b4._effect_value(_module_effect(effect))
    except Exception as error:
        raise ColdIntegratedViewsError(str(error)) from error
    raise ColdIntegratedViewsError("effect constructor is unsupported")


def _decision_move(
    core: dict[str, Any], occurrence_ref: int, modules: Mapping[int, dict[str, Any]]
) -> dict[str, Any] | None:
    effect = core["occurrences"][occurrence_ref]["effect"]
    if effect["tag"] in (0, 6):
        return oracle._move(core, effect)
    semantics = modules.get(occurrence_ref)
    if semantics is not None and semantics["decision"] != 0:
        return b4._module_move(_module_effect(effect), semantics)
    return None


def _output_predecessors(
    core: dict[str, Any],
    positions: Mapping[str, Mapping[int, int]],
    modules: Mapping[int, dict[str, Any]],
    occurrence_ref: int,
    output_ordinal: int,
) -> tuple[tuple[int, int, int], ...]:
    effect = core["occurrences"][occurrence_ref]["effect"]
    tag = effect["tag"]
    if tag == 1:
        return effect["inputs"]
    if tag == 2:
        challenge = core["challenges"][effect["challenge"]]
        prior = (
            tuple(
                (4, positions["challenge"][item], 0)
                for item in challenge["correlation"]["prior"]
            )
            if challenge["correlation"]["tag"] == 1
            else ()
        )
        return (*challenge["conditions"], *prior)
    if tag == 3:
        return core["checks"][effect["check"]]["inputs"]
    if tag == 6 and effect["oracle_tag"] == 2:
        query = core["occurrences"][effect["query"]]["effect"]
        return (query["index"],)
    if tag == 7:
        result: list[tuple[int, int, int]] = []
        module_effect = _module_effect(effect)
        for dependency in modules[occurrence_ref]["outputs"][output_ordinal][
            "dependencies"
        ]:
            if dependency["tag"] == 2:
                ordinal = dependency["ordinal"]
                if type(ordinal) is not int:
                    raise ColdIntegratedViewsError(
                        "module payload dependency lacks ordinal"
                    )
                result.append(module_effect["payload"]["inputs"][ordinal])
            elif dependency["tag"] == 3:
                ordinal = dependency["ordinal"]
                if type(ordinal) is not int:
                    raise ColdIntegratedViewsError(
                        "module prior-output dependency lacks ordinal"
                    )
                result.append((4, occurrence_ref, ordinal))
        return tuple(result)
    return ()


def _oracle_lifecycle(
    core: dict[str, Any], positions: Mapping[str, Mapping[int, int]]
) -> tuple[dict[int, list[int]], dict[int, list[int]]]:
    queries = {index: [] for index in range(len(core["oracles"]))}
    answers = {index: [] for index in range(len(core["oracles"]))}
    for occurrence_ref, occurrence in enumerate(core["occurrences"]):
        effect = occurrence["effect"]
        if effect["tag"] == 6 and effect["oracle_tag"] == 1:
            queries[effect["oracle"]].append(occurrence_ref)
        elif effect["tag"] == 6 and effect["oracle_tag"] == 2:
            query = core["occurrences"][effect["query"]]["effect"]
            answers[query["oracle"]].append(occurrence_ref)
    if set(positions["publication"]) != set(queries) or any(
        len(queries[index]) != len(answers[index]) for index in queries
    ):
        raise ColdIntegratedViewsError("Oracle lifecycle is incomplete")
    return queries, answers


def _claim_uses(
    core: dict[str, Any], positions: Mapping[str, Mapping[int, int]]
) -> dict[int, tuple[tuple[str, int, int, int], ...]]:
    uses: dict[int, list[tuple[str, int, int, int]]] = {
        index: [] for index in range(len(core["claims"]))
    }
    for reduction_ref, reduction in enumerate(core["reductions"]):
        for ordinal, claim_ref in enumerate(reduction["input_claims"]):
            uses[claim_ref].append(
                ("reduction", positions["reduction"][reduction_ref], reduction_ref, ordinal)
            )
    for terminal_ref, terminal in enumerate(core["terminals"]):
        for ordinal, claim_ref in enumerate(terminal["claims"]):
            uses[claim_ref].append(
                ("terminal", positions["terminal"][terminal_ref], terminal_ref, ordinal)
            )
    return {
        key: tuple(sorted(value, key=lambda item: (item[1], item[0], item[3])))
        for key, value in uses.items()
    }


def project(
    core_profiled_body: bytes,
    core_reference: bytes,
    protocol_profiled_body: bytes,
    protocol_reference: bytes,
    module_sources: tuple[tuple[bytes, bytes], ...],
    algorithm_preimages: tuple[tuple[bytes, bytes], ...],
    evaluation_contract_reference: bytes,
) -> tuple[dict[str, Any], dict[str, Any]]:
    """Authenticate exact bytes and project the complete normalized universe."""

    if not VIEW_SCHEMAS or not VIEW_ORDER:
        raise ColdIntegratedViewsError("candidate profile and schema are not configured")
    public_coin, graph_evidence = d1.project(
        core_profiled_body,
        core_reference,
        protocol_profiled_body,
        protocol_reference,
        module_sources,
        algorithm_preimages,
        evaluation_contract_reference,
    )
    core, modules = _authenticate(
        core_profiled_body,
        core_reference,
        protocol_profiled_body,
        protocol_reference,
        module_sources,
        algorithm_preimages,
        evaluation_contract_reference,
    )
    positions = d1._positions(core)
    paths = cold._scope_paths(core)
    outputs = _output_types(core, modules)
    core_atom = cold._identifier("core-id-body-v0", core_reference)
    protocol_atom = cold._identifier("protocol-id-body-v0", protocol_reference)

    public_binding = {
        0: core_atom,
        1: [
            {
                0: cold._ordinal("scope-ref-body-v0", scope_ref),
                1: cold._v(0)
                if scope["parent"] is None
                else cold._v(
                    1, cold._ordinal("scope-ref-body-v0", scope["parent"])
                ),
                2: cold._v(0)
                if scope["opening"] is None
                else cold._v(
                    1, cold._ordinal("occurrence-ref-body-v0", scope["opening"])
                ),
                3: [cold._ordinal("scope-ref-body-v0", item) for item in paths[scope_ref]],
            }
            for scope_ref, scope in enumerate(core["scopes"])
        ],
        2: [
            {
                0: cold._ordinal("binding-ref-body-v0", binding_ref),
                1: cold._ordinal("scope-ref-body-v0", binding["scope"]),
                2: cold._v(binding["class"]),
                3: cold._value_ref(binding["value"]),
                4: cold._value_type(cold._type_of(core, outputs, binding["value"])),
            }
            for binding_ref, binding in enumerate(core["bindings"])
        ],
    }

    decisions = [
        (occurrence_ref, move)
        for occurrence_ref in range(len(core["occurrences"]))
        if (move := _decision_move(core, occurrence_ref, modules)) is not None
    ]
    decision_rows: list[dict[int, Any]] = []
    read_rows: list[dict[int, Any]] = []
    legal_rows: list[dict[int, Any]] = []
    move_by_occurrence = dict(decisions)
    for occurrence_ref, move in decisions:
        occurrence = core["occurrences"][occurrence_ref]
        prior_decisions = [item for item, _move in decisions if item < occurrence_ref]
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
                    cold._ordinal("decision-ref-body-v0", item)
                    for item in prior_decisions
                ],
            }
        )
        for input_ref, declaration in enumerate(core["public_inputs"]):
            read_rows.append(
                {
                    0: cold._ordinal("decision-ref-body-v0", occurrence_ref),
                    1: cold._v(1, cold._ordinal("public-input-ref-body-v0", input_ref)),
                    2: cold._value_type(declaration["type"]),
                }
            )
        for constant_ref, declaration in enumerate(core["constants"]):
            read_rows.append(
                {
                    0: cold._ordinal("decision-ref-body-v0", occurrence_ref),
                    1: cold._v(0, cold._ordinal("constant-ref-body-v0", constant_ref)),
                    2: cold._value_type(declaration["type"]),
                }
            )
        for binding_ref, binding in enumerate(core["bindings"]):
            if _scope_is_ancestor(paths, binding["scope"], occurrence["scope"]):
                read_rows.append(
                    {
                        0: cold._ordinal("decision-ref-body-v0", occurrence_ref),
                        1: cold._v(2, cold._ordinal("binding-ref-body-v0", binding_ref)),
                        2: cold._value_type(
                            cold._type_of(core, outputs, binding["value"])
                        ),
                    }
                )
        for prior_ref, prior_occurrence in enumerate(
            core["occurrences"][:occurrence_ref]
        ):
            effect = prior_occurrence["effect"]
            read_case: int | None = None
            read_type: object | None = None
            visible = _guard_implies(occurrence["guard"], prior_occurrence["guard"])
            if effect["tag"] in (0, 1):
                read_case, read_type = 3, effect["payload_type"]
            elif effect["tag"] == 2:
                read_case, read_type = 4, core["challenges"][effect["challenge"]]["type"]
            elif effect["tag"] == 6 and effect["oracle_tag"] == 0:
                read_case = 5
                publication_types = oracle._publication_types(
                    core["oracles"][effect["oracle"]]
                )
                read_type = (
                    publication_types[0]
                    if publication_types
                    else k1.value_type_datum(k1.UNIT_VALUE)
                )
            elif effect["tag"] == 6 and effect["oracle_tag"] == 1:
                read_case, read_type = 6, core["oracles"][effect["oracle"]]["index_type"]
                visible = visible and effect["visibility"] == 0
            elif effect["tag"] == 6 and effect["oracle_tag"] == 2:
                query = core["occurrences"][effect["query"]]["effect"]
                read_case = 7
                read_type = oracle._answer_type(core["oracles"][query["oracle"]])
                visible = visible and query["visibility"] == 0
            if read_case is not None and visible:
                read_rows.append(
                    {
                        0: cold._ordinal("decision-ref-body-v0", occurrence_ref),
                        1: cold._v(
                            read_case,
                            cold._ordinal("occurrence-ref-body-v0", prior_ref),
                        ),
                        2: cold._value_type(read_type),
                    }
                )
            prior_semantics = modules.get(prior_ref)
            if prior_semantics is not None:
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
        for prior_ref in prior_decisions:
            effect = core["occurrences"][prior_ref]["effect"]
            if effect["tag"] == 0:
                prior_type = effect["payload_type"]
            elif effect["tag"] == 6:
                prior_type = oracle._type_datum(
                    oracle._carrier_type(core["oracles"][effect["oracle"]])
                )
            else:
                prior_type = modules[prior_ref]["move_type"]
            if prior_type is None or move_by_occurrence[prior_ref] is None:
                raise ColdIntegratedViewsError("prior decision has no move type")
            read_rows.append(
                {
                    0: cold._ordinal("decision-ref-body-v0", occurrence_ref),
                    1: cold._v(9, cold._ordinal("decision-ref-body-v0", prior_ref)),
                    2: cold._value_type(prior_type),
                }
            )
        legal_rows.append(
            {0: cold._ordinal("decision-ref-body-v0", occurrence_ref), 1: move}
        )
    read_rows.sort(key=lambda item: codec.encode_value(b3._READ_SCHEMA, item))
    strategy = {
        0: core_atom,
        1: decision_rows,
        2: cold._law("core-admission-v0"),
        3: read_rows,
        4: legal_rows,
    }

    value_rows: list[dict[int, Any]] = []
    for tag, name in (
        (0, "public_inputs"),
        (1, "private_inputs"),
        (2, "constants"),
        (3, "derived"),
    ):
        for ordinal, declaration in enumerate(core[name]):
            value_rows.append(
                {
                    0: cold._value_ref((tag, ordinal, 0)),
                    1: cold._value_type(declaration["type"]),
                    2: [
                        cold._value_ref(item)
                        for item in declaration.get("inputs", ())
                    ],
                }
            )
    occurrence_rows: list[dict[int, Any]] = []
    message_rows: list[dict[int, Any]] = []
    extension_rows: list[dict[int, Any]] = []
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
                4: [cold._value_type(item) for item in outputs[occurrence_ref]],
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
                            1: cold._value_type(effect["payload_type"]),
                        },
                    ),
                }
            )
        elif effect["tag"] == 1:
            message_rows.append(
                {
                    0: cold._ordinal("occurrence-ref-body-v0", occurrence_ref),
                    1: cold._v(1),
                    2: cold._v(
                        1,
                        {
                            0: cold._module_ref(effect["channel"]),
                            1: cold._identifier(
                                "algorithm-ref-body-v0", effect["algorithm"]
                            ),
                            2: cold._identifier(
                                "evaluation-contract-id-body-v0", effect["contract"]
                            ),
                            3: [cold._value_ref(item) for item in effect["inputs"]],
                            4: cold._value_type(effect["payload_type"]),
                        },
                    ),
                }
            )
        elif effect["tag"] == 7:
            extension_rows.append(
                {
                    0: cold._ordinal("occurrence-ref-body-v0", occurrence_ref),
                    1: b4._admitted_effect(_module_effect(effect)),
                }
            )
        for output_ordinal, output_type in enumerate(outputs[occurrence_ref]):
            value_rows.append(
                {
                    0: cold._value_ref((4, occurrence_ref, output_ordinal)),
                    1: cold._value_type(output_type),
                    2: [
                        cold._value_ref(item)
                        for item in _output_predecessors(
                            core,
                            positions,
                            modules,
                            occurrence_ref,
                            output_ordinal,
                        )
                    ],
                }
            )
    queries, answers = _oracle_lifecycle(core, positions)
    oracle_rows = [
        {
            0: cold._ordinal("oracle-ref-body-v0", oracle_ref),
            1: oracle._oracle_value(declaration),
            2: cold._ordinal(
                "occurrence-ref-body-v0", positions["publication"][oracle_ref]
            ),
            3: [
                cold._ordinal("occurrence-ref-body-v0", item)
                for item in queries[oracle_ref]
            ],
            4: [
                cold._ordinal("occurrence-ref-body-v0", item)
                for item in answers[oracle_ref]
            ],
        }
        for oracle_ref, declaration in enumerate(core["oracles"])
    ]
    check_rows = [
        {
            0: cold._ordinal("check-ref-body-v0", check_ref),
            1: cold._identifier("algorithm-ref-body-v0", check["algorithm"]),
            2: cold._identifier(
                "evaluation-contract-id-body-v0", check["contract"]
            ),
            3: [cold._value_ref(item) for item in check["inputs"]],
            4: cold._ordinal(
                "occurrence-ref-body-v0", positions["check"][check_ref]
            ),
        }
        for check_ref, check in enumerate(core["checks"])
    ]
    terminal_rows = [
        {
            0: cold._ordinal("terminal-ref-body-v0", terminal_ref),
            1: cold._v(terminal["verdict"]),
            2: [cold._value_ref(item) for item in terminal["outputs"]],
            3: [cold._ordinal("check-ref-body-v0", item) for item in terminal["checks"]],
            4: [
                cold._ordinal("reduction-ref-body-v0", item)
                for item in terminal["reductions"]
            ],
            5: [cold._ordinal("claim-ref-body-v0", item) for item in terminal["claims"]],
            6: cold._ordinal(
                "occurrence-ref-body-v0", positions["terminal"][terminal_ref]
            ),
        }
        for terminal_ref, terminal in enumerate(core["terminals"])
    ]
    effect_view = {
        0: core_atom,
        1: occurrence_rows,
        2: value_rows,
        3: message_rows,
        4: oracle_rows,
        5: check_rows,
        6: terminal_rows,
        7: extension_rows,
    }

    claim_uses = _claim_uses(core, positions)
    facts = {"reduction_positions": positions["reduction"]}
    claim_rows = []
    for claim_ref, claim in enumerate(core["claims"]):
        uses = [
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
            for kind, occurrence_ref, owner_ref, ordinal in claim_uses[claim_ref]
        ]
        claim_rows.append(
            {
                0: cold._ordinal("claim-ref-body-v0", claim_ref),
                1: cold._module_ref(claim["contract"]),
                2: cold._ordinal("scope-ref-body-v0", claim["scope"]),
                3: cold._v(claim["usage"]),
                4: b3._claim_source_value(claim["source"]),
                5: b3._claim_creation_value(core, facts, claim["source"]),
                6: uses,
            }
        )
    reduction_rows = [
        {
            0: cold._ordinal("reduction-ref-body-v0", reduction_ref),
            1: cold._module_ref(reduction["contract"]),
            2: cold._ordinal("scope-ref-body-v0", reduction["scope"]),
            3: cold._ordinal(
                "occurrence-ref-body-v0", positions["reduction"][reduction_ref]
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
                b3._publication_value(item)
                for item in reduction["required_publications"]
            ],
            8: [
                cold._module_ref(item) for item in reduction["output_contracts"]
            ],
        }
        for reduction_ref, reduction in enumerate(core["reductions"])
    ]
    disposition_rows = [
        {
            0: cold._ordinal(
                "occurrence-ref-body-v0", positions["terminal"][terminal_ref]
            ),
            1: cold._ordinal("terminal-ref-body-v0", terminal_ref),
            2: cold._ordinal("claim-ref-body-v0", claim_ref),
            3: cold._v(0 if terminal["verdict"] == 0 else 1),
        }
        for terminal_ref, terminal in enumerate(core["terminals"])
        for claim_ref in terminal["claims"]
    ]
    requirement_rows = [
        {
            0: cold._ordinal(
                "occurrence-ref-body-v0", positions["terminal"][terminal_ref]
            ),
            1: cold._ordinal("terminal-ref-body-v0", terminal_ref),
            2: [
                cold._ordinal("reduction-ref-body-v0", item)
                for item in terminal["reductions"]
            ],
        }
        for terminal_ref, terminal in enumerate(core["terminals"])
    ]
    claim_reduction = {
        0: core_atom,
        1: claim_rows,
        2: reduction_rows,
        3: disposition_rows,
        4: requirement_rows,
    }

    resolver_rows = [
        {
            0: cold._ordinal("challenge-ref-body-v0", challenge_ref),
            1: cold._ordinal(
                "occurrence-ref-body-v0", positions["challenge"][challenge_ref]
            ),
            2: cold._value_type(challenge["type"]),
            3: cold._module_ref(challenge["domain"]),
            4: cold._module_ref(challenge["fresh_law"]),
            5: [cold._value_ref(item) for item in challenge["conditions"]],
            6: [
                cold._ordinal("challenge-ref-body-v0", item)
                for item in (
                    challenge["correlation"]["prior"]
                    if challenge["correlation"]["tag"] == 1
                    else ()
                )
            ],
        }
        for challenge_ref, challenge in enumerate(core["challenges"])
    ]
    oracle_receipts = []
    for occurrence_ref, occurrence in enumerate(core["occurrences"]):
        effect = occurrence["effect"]
        if effect["tag"] != 6:
            continue
        if effect["oracle_tag"] == 0:
            oracle_receipts.append(
                cold._v(
                    0,
                    {
                        0: cold._ordinal("occurrence-ref-body-v0", occurrence_ref),
                        1: cold._ordinal("oracle-ref-body-v0", effect["oracle"]),
                        2: [cold._value_type(item) for item in outputs[occurrence_ref]],
                    },
                )
            )
        elif effect["oracle_tag"] == 1:
            oracle_receipts.append(
                cold._v(
                    1,
                    {
                        0: cold._ordinal("occurrence-ref-body-v0", occurrence_ref),
                        1: cold._ordinal("oracle-ref-body-v0", effect["oracle"]),
                        2: cold._value_type(core["oracles"][effect["oracle"]]["index_type"]),
                        3: cold._v(effect["visibility"]),
                    },
                )
            )
        else:
            query = core["occurrences"][effect["query"]]["effect"]
            oracle_receipts.append(
                cold._v(
                    2,
                    {
                        0: cold._ordinal("occurrence-ref-body-v0", occurrence_ref),
                        1: cold._ordinal("oracle-ref-body-v0", query["oracle"]),
                        2: cold._value_type(
                            oracle._answer_type(core["oracles"][query["oracle"]])
                        ),
                        3: cold._v(query["visibility"]),
                    },
                )
            )
    runtime = {
        0: [
            {
                0: cold._ordinal("occurrence-ref-body-v0", occurrence_ref),
                1: [cold._value_type(item) for item in output_types],
            }
            for occurrence_ref, output_types in enumerate(outputs)
        ],
        1: [
            {
                0: cold._ordinal("challenge-ref-body-v0", challenge_ref),
                1: cold._ordinal(
                    "occurrence-ref-body-v0", positions["challenge"][challenge_ref]
                ),
                2: cold._value_type(challenge["type"]),
            }
            for challenge_ref, challenge in enumerate(core["challenges"])
        ],
        2: oracle_receipts,
        3: [
            {
                0: cold._ordinal("terminal-ref-body-v0", terminal_ref),
                1: cold._ordinal(
                    "occurrence-ref-body-v0", positions["terminal"][terminal_ref]
                ),
                2: cold._v(terminal["verdict"]),
                3: [
                    cold._value_type(cold._type_of(core, outputs, item))
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
    if tuple(views) != VIEW_ORDER:
        raise ColdIntegratedViewsError("cold view table is incomplete or reordered")
    for name, value in views.items():
        codec.encode_value(VIEW_SCHEMAS[name], value)
    return views, {
        "occurrences": len(core["occurrences"]),
        "decisions": len(decisions),
        "oracle_modes": tuple(item["mode"]["tag"] for item in core["oracles"]),
        "oracle_visibilities": tuple(
            occurrence["effect"]["visibility"]
            for occurrence in core["occurrences"]
            if occurrence["effect"]["tag"] == 6
            and occurrence["effect"]["oracle_tag"] == 1
        ),
        "module_decisions": tuple(item["decision"] for item in modules.values()),
        "pc_graph": graph_evidence,
    }


def encode_views(views: Mapping[str, Any]) -> dict[str, bytes]:
    if tuple(views) != VIEW_ORDER:
        raise ColdIntegratedViewsError("cold view table is incomplete or reordered")
    return {
        name: codec.encode_value(VIEW_SCHEMAS[name], value)
        for name, value in views.items()
    }
