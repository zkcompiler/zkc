"""Typed six-view projector for the five exact F0-V2B2D1 carriers.

The projector keeps D1 as the Core-admission and PublicCoin graph owner.  It
composes the constructor-local projection laws already exercised by B1--B5B2
instead of introducing another semantic interpretation of those constructors.
"""

from __future__ import annotations

import importlib.util
from pathlib import Path
import sys
from types import ModuleType, SimpleNamespace
from typing import Any, Mapping


ROOT = Path(__file__).resolve().parents[2]
D1_MODEL = ROOT / "evaluation/formal-source-integrated-graph-f0v2b2d1/model.py"
B4_MODEL = (
    ROOT
    / "evaluation"
    / "formal-source-module-owner-projections-f0v2b2c1b4"
    / "model.py"
)


class IntegratedViewsError(ValueError):
    """The exact admitted D1 subject cannot produce the requested view set."""


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


d1 = _load("_zkc_f0v2b2d1_model", D1_MODEL)
b4 = _load("_zkc_f0v2b2d3_b4", B4_MODEL)
b5 = d1.b5
b3 = d1.b3
oracle = d1.oracle
foundation = d1.foundation
base = d1.base
codec = d1.codec
k1 = d1.k1

VIEW_SCHEMAS = d1.VIEW_SCHEMAS
VIEW_ORDER = tuple(b5.candidate_schema_source()["view_order"])


def _protocol_reference(core_handle: object, protocol_handle: object) -> object:
    if (
        type(protocol_handle) is not d1.b2c0.AdmittedFreshProtocolSnapshot
        or not protocol_handle._issued_by(d1.b2c0._PROTOCOL_ISSUER)
        or protocol_handle.core_handle is not core_handle
        or protocol_handle.profile_reference != core_handle.profile_reference
        or protocol_handle.closure_fingerprint != core_handle.closure.fingerprint
        or protocol_handle.evaluator_fingerprint != d1.EVALUATOR_FINGERPRINT
    ):
        raise IntegratedViewsError("Fresh Protocol authority differs from D1 Core")
    return k1.decode_content_reference(protocol_handle.protocol_reference)


def _b4_effect(effect: object) -> object:
    if type(effect) is not d1.ModuleEffectRef:
        raise IntegratedViewsError("module effect carrier differs")
    return b4.ModuleEffectRef(
        effect.module,
        effect.declaration,
        b4.ModulePayload(effect.payload.inputs),
    )


def _module_atom(effect: object) -> dict[str, str]:
    """Adapt D1's carrier to B4's checked admitted-effect encoder."""

    return b4._admitted_effect_value(_b4_effect(effect))


def _b4_semantics(semantics: object) -> object:
    """Translate isomorphic D1 records so B4 remains the move-law owner."""

    def dependency(value: object) -> object:
        return b4.ModuleDependency(
            b4.ModuleDependencyKind(value.kind.value), value.ordinal
        )

    return b4.ModuleSemantics(
        semantics.name,
        semantics.payload_input_types,
        b4.ModuleDecisionClass(semantics.decision_class.value),
        semantics.move_type,
        tuple(
            b4.ModuleOutputSpec(
                output.value_type,
                b4.ModuleVisibility(output.visibility.value),
                b4.ModuleOutputTransfer(output.transfer.value),
                tuple(dependency(item) for item in output.dependencies),
                output.reconstruction_algorithm,
                output.reconstruction_contract,
                output.acceptance_relevant,
            )
            for output in semantics.outputs
        ),
        tuple(
            b4.ModuleControlSpec(
                tuple(dependency(item) for item in control.dependencies),
                control.acceptance_relevant,
            )
            for control in semantics.controls
        ),
        semantics.influence_output,
        semantics.guard_behavior,
        semantics.replay_rule,
        semantics.terminal_interaction,
        semantics.work_bound,
    )


def _effect_value(effect: object) -> dict[str, Any]:
    """Dispatch to the constructor-local effect encoders."""

    if type(effect) in (base.ProverMessageEffect, foundation.VerifierMessageEffect):
        return foundation._effect_value(effect)
    if type(effect) in (base.ChallengeEffect, b3.ApplyReductionEffect):
        return b3._effect_value(effect)
    if type(effect) in (
        oracle.PublishOracleEffect,
        oracle.QueryOracleEffect,
        oracle.AnswerOracleEffect,
    ):
        return oracle._effect_value(effect)
    if type(effect) in (base.CheckEffect, base.TerminalEffect):
        return b5._effect_value(effect)
    if type(effect) is d1.ModuleEffectRef:
        return foundation._v(7, _module_atom(effect))
    raise IntegratedViewsError(f"unsupported effect {type(effect).__name__}")


def _module_move(effect: object, semantics: object) -> dict[str, Any]:
    return b4._module_move_value(_b4_effect(effect), _b4_semantics(semantics))


def _decision_move(
    core: object, occurrence_ref: int, modules: Mapping[int, object]
) -> dict[str, Any] | None:
    effect = core.occurrences[occurrence_ref].effect
    if type(effect) in (base.ProverMessageEffect, oracle.PublishOracleEffect):
        return oracle._decision_move(core, effect)
    if type(effect) is d1.ModuleEffectRef:
        semantics = modules[occurrence_ref]
        if semantics.decision_class is not d1.ModuleDecisionClass.NO_PROVER_DECISION:
            return _module_move(effect, semantics)
    return None


def _scope_is_ancestor(
    paths: tuple[tuple[int, ...], ...], ancestor: int, descendant: int
) -> bool:
    return ancestor in paths[descendant]


def _module_value_dependencies(
    effect: object, semantics: object, output_ordinal: int, occurrence_ref: int
) -> tuple[object, ...]:
    result: list[object] = []
    for dependency in semantics.outputs[output_ordinal].dependencies:
        if dependency.kind is d1.ModuleDependencyKind.PAYLOAD_INPUT:
            if dependency.ordinal is None:
                raise IntegratedViewsError("module payload dependency lacks ordinal")
            result.append(effect.payload.inputs[dependency.ordinal])
        elif dependency.kind is d1.ModuleDependencyKind.PRIOR_OUTPUT:
            if dependency.ordinal is None:
                raise IntegratedViewsError("module prior-output dependency lacks ordinal")
            result.append(base.OccurrenceOutputRef(occurrence_ref, dependency.ordinal))
    return tuple(result)


def _output_predecessors(
    core: object,
    positions: Mapping[str, Mapping[int, int]],
    modules: Mapping[int, object],
    occurrence_ref: int,
    output_ordinal: int,
) -> tuple[object, ...]:
    effect = core.occurrences[occurrence_ref].effect
    if type(effect) is foundation.VerifierMessageEffect:
        return effect.inputs
    if type(effect) is base.ChallengeEffect:
        challenge = core.challenges[effect.challenge]
        prior = (
            tuple(
                base.OccurrenceOutputRef(positions["challenge"][item], 0)
                for item in challenge.correlation.prior_members
            )
            if type(challenge.correlation) is base.JointCorrelation
            else ()
        )
        return (*challenge.public_conditions, *prior)
    if type(effect) is base.CheckEffect:
        return core.checks[effect.check].inputs
    if type(effect) is oracle.AnswerOracleEffect:
        query = core.occurrences[effect.query].effect
        return (query.index,)
    if type(effect) is d1.ModuleEffectRef:
        return _module_value_dependencies(
            effect, modules[occurrence_ref], output_ordinal, occurrence_ref
        )
    return ()


def _oracle_lifecycle(
    core: object, positions: Mapping[str, Mapping[int, int]]
) -> tuple[dict[int, list[int]], dict[int, list[int]]]:
    queries = {index: [] for index in range(len(core.oracles))}
    answers = {index: [] for index in range(len(core.oracles))}
    for occurrence_ref, occurrence in enumerate(core.occurrences):
        effect = occurrence.effect
        if type(effect) is oracle.QueryOracleEffect:
            queries[effect.oracle].append(occurrence_ref)
        elif type(effect) is oracle.AnswerOracleEffect:
            query = core.occurrences[effect.query].effect
            answers[query.oracle].append(occurrence_ref)
    if set(positions["publication"]) != set(queries) or any(
        len(queries[index]) != len(answers[index]) for index in queries
    ):
        raise IntegratedViewsError("Oracle lifecycle is incomplete")
    return queries, answers


def _claim_uses(
    core: object, positions: Mapping[str, Mapping[int, int]]
) -> dict[int, tuple[tuple[str, int, int, int], ...]]:
    uses: dict[int, list[tuple[str, int, int, int]]] = {
        index: [] for index in range(len(core.claims))
    }
    for reduction_ref, reduction in enumerate(core.reductions):
        occurrence_ref = positions["reduction"][reduction_ref]
        for ordinal, claim_ref in enumerate(reduction.input_claims):
            uses[claim_ref].append(
                ("reduction", occurrence_ref, reduction_ref, ordinal)
            )
    for terminal_ref, terminal in enumerate(core.terminals):
        occurrence_ref = positions["terminal"][terminal_ref]
        for ordinal, claim_ref in enumerate(terminal.terminal_claims):
            uses[claim_ref].append(("terminal", occurrence_ref, terminal_ref, ordinal))
    return {
        key: tuple(sorted(value, key=lambda item: (item[1], item[0], item[3])))
        for key, value in uses.items()
    }


def project_admitted_values(
    core: object,
    core_identifier: object,
    protocol_identifier: object,
    *,
    scenario: str = "integrated-baseline",
) -> dict[str, Any]:
    """Pure six-view projection from already admitted owner values.

    Admission authority remains the caller's responsibility.  The original
    ``project_views`` entry point below still authenticates D1 handles before
    delegating here; later composition packages can reuse the exact projector
    after their own stricter admitted-carrier gate instead of forking it.
    """

    core_atom = foundation._identifier("core-id-body-v0", core_identifier)
    protocol_atom = foundation._identifier(
        "protocol-id-body-v0", protocol_identifier
    )
    paths = foundation._scope_paths(core)
    positions = d1._positions(core)
    modules = d1._module_occurrence_semantics(
        core, scenario == "invalid-module-control-sink"
    )
    outputs = d1._output_types(core, modules)

    public_binding = {
        0: core_atom,
        1: [
            {
                0: foundation._ordinal("scope-ref-body-v0", scope_ref),
                1: foundation._v(0)
                if scope.parent is None
                else foundation._v(
                    1, foundation._ordinal("scope-ref-body-v0", scope.parent)
                ),
                2: foundation._v(0)
                if scope.opening is None
                else foundation._v(
                    1, foundation._ordinal("occurrence-ref-body-v0", scope.opening)
                ),
                3: [
                    foundation._ordinal("scope-ref-body-v0", item)
                    for item in paths[scope_ref]
                ],
            }
            for scope_ref, scope in enumerate(core.scopes)
        ],
        2: [
            {
                0: foundation._ordinal("binding-ref-body-v0", binding_ref),
                1: foundation._ordinal("scope-ref-body-v0", binding.scope),
                2: foundation._v(binding.binding_class.value),
                3: foundation._value_ref(binding.value),
                4: foundation._value_type_body(
                    foundation._value_type(core, outputs, binding.value)
                ),
            }
            for binding_ref, binding in enumerate(core.public_bindings)
        ],
    }

    decisions = [
        (occurrence_ref, move)
        for occurrence_ref in range(len(core.occurrences))
        if (move := _decision_move(core, occurrence_ref, modules)) is not None
    ]
    decision_rows: list[dict[int, Any]] = []
    read_rows: list[dict[int, Any]] = []
    legal_rows: list[dict[int, Any]] = []
    for occurrence_ref, move in decisions:
        occurrence = core.occurrences[occurrence_ref]
        prior_decisions = [item for item, _move in decisions if item < occurrence_ref]
        decision_rows.append(
            {
                0: foundation._ordinal("decision-ref-body-v0", occurrence_ref),
                1: foundation._ordinal("occurrence-ref-body-v0", occurrence_ref),
                2: [
                    foundation._ordinal("scope-ref-body-v0", item)
                    for item in paths[occurrence.scope]
                ],
                3: foundation._guard_body(occurrence.guard),
                4: move,
                5: [
                    foundation._ordinal("decision-ref-body-v0", item)
                    for item in prior_decisions
                ],
            }
        )
        for input_ref, declaration in enumerate(core.public_inputs):
            read_rows.append(
                {
                    0: foundation._ordinal("decision-ref-body-v0", occurrence_ref),
                    1: foundation._v(
                        1,
                        foundation._ordinal("public-input-ref-body-v0", input_ref),
                    ),
                    2: foundation._value_type_body(declaration.value_type),
                }
            )
        for constant_ref, declaration in enumerate(core.constants):
            read_rows.append(
                {
                    0: foundation._ordinal("decision-ref-body-v0", occurrence_ref),
                    1: foundation._v(
                        0, foundation._ordinal("constant-ref-body-v0", constant_ref)
                    ),
                    2: foundation._value_type_body(declaration.value_type),
                }
            )
        for binding_ref, binding in enumerate(core.public_bindings):
            if _scope_is_ancestor(paths, binding.scope, occurrence.scope):
                read_rows.append(
                    {
                        0: foundation._ordinal("decision-ref-body-v0", occurrence_ref),
                        1: foundation._v(
                            2,
                            foundation._ordinal("binding-ref-body-v0", binding_ref),
                        ),
                        2: foundation._value_type_body(
                            foundation._value_type(core, outputs, binding.value)
                        ),
                    }
                )
        for prior_ref, prior_occurrence in enumerate(
            core.occurrences[:occurrence_ref]
        ):
            prior_effect = prior_occurrence.effect
            read_case: int | None = None
            read_type: object | None = None
            visible = foundation._guard_implies(
                occurrence.guard, prior_occurrence.guard
            )
            if type(prior_effect) in (
                base.ProverMessageEffect,
                foundation.VerifierMessageEffect,
            ):
                read_case, read_type = 3, prior_effect.payload_type
            elif type(prior_effect) is base.ChallengeEffect:
                read_case = 4
                read_type = core.challenges[prior_effect.challenge].value_type
            elif type(prior_effect) is oracle.PublishOracleEffect:
                publication_types = oracle.oracle_publication_types(
                    core.oracles[prior_effect.oracle]
                )
                read_case = 5
                read_type = publication_types[0] if publication_types else k1.UNIT_VALUE
            elif type(prior_effect) is oracle.QueryOracleEffect:
                read_case = 6
                read_type = core.oracles[prior_effect.oracle].index_type
                visible = visible and (
                    prior_effect.visibility is oracle.OracleVisibility.PUBLIC
                )
            elif type(prior_effect) is oracle.AnswerOracleEffect:
                query = core.occurrences[prior_effect.query].effect
                read_case = 7
                read_type = oracle.oracle_answer_type(core.oracles[query.oracle])
                visible = visible and (
                    query.visibility is oracle.OracleVisibility.PUBLIC
                )
            if read_case is not None and visible:
                read_rows.append(
                    {
                        0: foundation._ordinal("decision-ref-body-v0", occurrence_ref),
                        1: foundation._v(
                            read_case,
                            foundation._ordinal("occurrence-ref-body-v0", prior_ref),
                        ),
                        2: foundation._value_type_body(read_type),
                    }
                )
            prior_semantics = modules.get(prior_ref)
            if prior_semantics is not None:
                for output_ordinal, output in enumerate(prior_semantics.outputs):
                    if output.visibility in (
                        d1.ModuleVisibility.PROVER_ONLY,
                        d1.ModuleVisibility.PUBLIC,
                    ):
                        read_rows.append(
                            {
                                0: foundation._ordinal(
                                    "decision-ref-body-v0", occurrence_ref
                                ),
                                1: foundation._v(
                                    8,
                                    {
                                        0: foundation._ordinal(
                                            "occurrence-ref-body-v0", prior_ref
                                        ),
                                        1: output_ordinal,
                                    },
                                ),
                                2: foundation._value_type_body(output.value_type),
                            }
                        )
        for prior_ref in prior_decisions:
            prior_move = dict(decisions)[prior_ref]
            prior_type = (
                core.occurrences[prior_ref].effect.payload_type
                if type(core.occurrences[prior_ref].effect)
                is base.ProverMessageEffect
                else (
                    oracle.oracle_carrier_type(
                        core.oracles[core.occurrences[prior_ref].effect.oracle]
                    )
                    if type(core.occurrences[prior_ref].effect)
                    is oracle.PublishOracleEffect
                    else modules[prior_ref].move_type
                )
            )
            if prior_type is None or prior_move is None:
                raise IntegratedViewsError("prior decision has no move type")
            read_rows.append(
                {
                    0: foundation._ordinal("decision-ref-body-v0", occurrence_ref),
                    1: foundation._v(
                        9, foundation._ordinal("decision-ref-body-v0", prior_ref)
                    ),
                    2: foundation._value_type_body(prior_type),
                }
            )
        legal_rows.append(
            {0: foundation._ordinal("decision-ref-body-v0", occurrence_ref), 1: move}
        )
    read_rows.sort(key=lambda item: codec.encode_value(b3._READ_SCHEMA, item))
    strategy = {
        0: core_atom,
        1: decision_rows,
        2: b5._law("core-admission-v0"),
        3: read_rows,
        4: legal_rows,
    }

    public_coin, _graph_evidence = d1.project_public_coin_values(
        core, core_identifier, scenario
    )

    value_rows: list[dict[int, Any]] = []
    value_tables = (
        (base.PublicInputRef, core.public_inputs, "value_type"),
        (base.VerifierPrivateInputRef, core.verifier_private_inputs, "value_type"),
        (base.ConstantRef, core.constants, "value_type"),
        (base.DerivedValueRef, core.derived_values, "result_type"),
    )
    for reference_type, table, type_field in value_tables:
        for ordinal, declaration in enumerate(table):
            predecessors = declaration.inputs if type_field == "result_type" else ()
            value_rows.append(
                {
                    0: foundation._value_ref(reference_type(ordinal)),
                    1: foundation._value_type_body(getattr(declaration, type_field)),
                    2: [foundation._value_ref(item) for item in predecessors],
                }
            )
    occurrence_rows: list[dict[int, Any]] = []
    message_rows: list[dict[int, Any]] = []
    extension_rows: list[dict[int, Any]] = []
    for occurrence_ref, occurrence in enumerate(core.occurrences):
        occurrence_rows.append(
            {
                0: foundation._ordinal("occurrence-ref-body-v0", occurrence_ref),
                1: [
                    foundation._ordinal("scope-ref-body-v0", item)
                    for item in paths[occurrence.scope]
                ],
                2: foundation._guard_body(occurrence.guard),
                3: _effect_value(occurrence.effect),
                4: [
                    foundation._value_type_body(item)
                    for item in outputs[occurrence_ref]
                ],
            }
        )
        effect = occurrence.effect
        if type(effect) is base.ProverMessageEffect:
            message_rows.append(
                {
                    0: foundation._ordinal("occurrence-ref-body-v0", occurrence_ref),
                    1: foundation._v(0),
                    2: foundation._v(
                        0,
                        {
                            0: foundation._module_ref(effect.channel),
                            1: foundation._value_type_body(effect.payload_type),
                        },
                    ),
                }
            )
        elif type(effect) is foundation.VerifierMessageEffect:
            message_rows.append(
                {
                    0: foundation._ordinal("occurrence-ref-body-v0", occurrence_ref),
                    1: foundation._v(1),
                    2: foundation._v(
                        1,
                        {
                            0: foundation._module_ref(effect.channel),
                            1: foundation._identifier(
                                "algorithm-ref-body-v0", effect.algorithm
                            ),
                            2: foundation._identifier(
                                "evaluation-contract-id-body-v0",
                                effect.evaluation_contract,
                            ),
                            3: [foundation._value_ref(item) for item in effect.inputs],
                            4: foundation._value_type_body(effect.payload_type),
                        },
                    ),
                }
            )
        elif type(effect) is d1.ModuleEffectRef:
            extension_rows.append(
                {
                    0: foundation._ordinal("occurrence-ref-body-v0", occurrence_ref),
                    1: _module_atom(effect),
                }
            )
        for output_ordinal, output_type in enumerate(outputs[occurrence_ref]):
            value_rows.append(
                {
                    0: foundation._value_ref(
                        base.OccurrenceOutputRef(occurrence_ref, output_ordinal)
                    ),
                    1: foundation._value_type_body(output_type),
                    2: [
                        foundation._value_ref(item)
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
            0: foundation._ordinal("oracle-ref-body-v0", oracle_ref),
            1: oracle._oracle_value(declaration),
            2: foundation._ordinal(
                "occurrence-ref-body-v0", positions["publication"][oracle_ref]
            ),
            3: [
                foundation._ordinal("occurrence-ref-body-v0", item)
                for item in queries[oracle_ref]
            ],
            4: [
                foundation._ordinal("occurrence-ref-body-v0", item)
                for item in answers[oracle_ref]
            ],
        }
        for oracle_ref, declaration in enumerate(core.oracles)
    ]
    check_rows = [
        {
            0: foundation._ordinal("check-ref-body-v0", check_ref),
            1: foundation._identifier("algorithm-ref-body-v0", check.algorithm),
            2: foundation._identifier(
                "evaluation-contract-id-body-v0", check.evaluation_contract
            ),
            3: [foundation._value_ref(item) for item in check.inputs],
            4: foundation._ordinal(
                "occurrence-ref-body-v0", positions["check"][check_ref]
            ),
        }
        for check_ref, check in enumerate(core.checks)
    ]
    terminal_rows = [
        {
            0: foundation._ordinal("terminal-ref-body-v0", terminal_ref),
            1: foundation._v(terminal.verdict.value),
            2: [foundation._value_ref(item) for item in terminal.public_outputs],
            3: [
                foundation._ordinal("check-ref-body-v0", item)
                for item in terminal.required_true_checks
            ],
            4: [
                foundation._ordinal("reduction-ref-body-v0", item)
                for item in terminal.required_applied_reductions
            ],
            5: [
                foundation._ordinal("claim-ref-body-v0", item)
                for item in terminal.terminal_claims
            ],
            6: foundation._ordinal(
                "occurrence-ref-body-v0", positions["terminal"][terminal_ref]
            ),
        }
        for terminal_ref, terminal in enumerate(core.terminals)
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
    validation = SimpleNamespace(reduction_positions=positions["reduction"])
    claim_rows: list[dict[int, Any]] = []
    for claim_ref, claim in enumerate(core.claims):
        uses = [
            foundation._v(
                0 if kind == "reduction" else 1,
                {
                    0: foundation._ordinal("occurrence-ref-body-v0", occurrence_ref),
                    1: foundation._ordinal(
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
                0: foundation._ordinal("claim-ref-body-v0", claim_ref),
                1: foundation._module_ref(claim.contract),
                2: foundation._ordinal("scope-ref-body-v0", claim.scope),
                3: foundation._v(claim.usage.value),
                4: b3._claim_source_value(claim.source),
                5: b3._claim_creation_value(core, validation, claim.source),
                6: uses,
            }
        )
    reduction_rows = [
        {
            0: foundation._ordinal("reduction-ref-body-v0", reduction_ref),
            1: foundation._module_ref(reduction.contract),
            2: foundation._ordinal("scope-ref-body-v0", reduction.scope),
            3: foundation._ordinal(
                "occurrence-ref-body-v0", positions["reduction"][reduction_ref]
            ),
            4: [
                foundation._ordinal("claim-ref-body-v0", item)
                for item in reduction.input_claims
            ],
            5: [foundation._value_ref(item) for item in reduction.side_inputs],
            6: [
                foundation._ordinal("challenge-ref-body-v0", item)
                for item in reduction.required_challenges
            ],
            7: [
                b3._reduction_publication_value(item)
                for item in reduction.required_publications
            ],
            8: [foundation._module_ref(item) for item in reduction.output_contracts],
        }
        for reduction_ref, reduction in enumerate(core.reductions)
    ]
    disposition_rows = [
        {
            0: foundation._ordinal(
                "occurrence-ref-body-v0", positions["terminal"][terminal_ref]
            ),
            1: foundation._ordinal("terminal-ref-body-v0", terminal_ref),
            2: foundation._ordinal("claim-ref-body-v0", claim_ref),
            3: foundation._v(
                0 if terminal.verdict is base.TerminalVerdict.ACCEPT else 1
            ),
        }
        for terminal_ref, terminal in enumerate(core.terminals)
        for claim_ref in terminal.terminal_claims
    ]
    requirement_rows = [
        {
            0: foundation._ordinal(
                "occurrence-ref-body-v0", positions["terminal"][terminal_ref]
            ),
            1: foundation._ordinal("terminal-ref-body-v0", terminal_ref),
            2: [
                foundation._ordinal("reduction-ref-body-v0", item)
                for item in terminal.required_applied_reductions
            ],
        }
        for terminal_ref, terminal in enumerate(core.terminals)
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
            0: foundation._ordinal("challenge-ref-body-v0", challenge_ref),
            1: foundation._ordinal(
                "occurrence-ref-body-v0", positions["challenge"][challenge_ref]
            ),
            2: foundation._value_type_body(challenge.value_type),
            3: foundation._module_ref(challenge.domain),
            4: foundation._module_ref(challenge.fresh_law),
            5: [foundation._value_ref(item) for item in challenge.public_conditions],
            6: [
                foundation._ordinal("challenge-ref-body-v0", item)
                for item in (
                    challenge.correlation.prior_members
                    if type(challenge.correlation) is base.JointCorrelation
                    else ()
                )
            ],
        }
        for challenge_ref, challenge in enumerate(core.challenges)
    ]
    oracle_receipts: list[dict[str, Any]] = []
    for occurrence_ref, occurrence in enumerate(core.occurrences):
        item = occurrence.effect
        if type(item) is oracle.PublishOracleEffect:
            oracle_receipts.append(
                foundation._v(
                    0,
                    {
                        0: foundation._ordinal(
                            "occurrence-ref-body-v0", occurrence_ref
                        ),
                        1: foundation._ordinal("oracle-ref-body-v0", item.oracle),
                        2: [
                            foundation._value_type_body(value_type)
                            for value_type in outputs[occurrence_ref]
                        ],
                    },
                )
            )
        elif type(item) is oracle.QueryOracleEffect:
            oracle_receipts.append(
                foundation._v(
                    1,
                    {
                        0: foundation._ordinal(
                            "occurrence-ref-body-v0", occurrence_ref
                        ),
                        1: foundation._ordinal("oracle-ref-body-v0", item.oracle),
                        2: foundation._value_type_body(
                            core.oracles[item.oracle].index_type
                        ),
                        3: foundation._v(item.visibility.value),
                    },
                )
            )
        elif type(item) is oracle.AnswerOracleEffect:
            query = core.occurrences[item.query].effect
            oracle_receipts.append(
                foundation._v(
                    2,
                    {
                        0: foundation._ordinal(
                            "occurrence-ref-body-v0", occurrence_ref
                        ),
                        1: foundation._ordinal("oracle-ref-body-v0", query.oracle),
                        2: foundation._value_type_body(
                            oracle.oracle_answer_type(core.oracles[query.oracle])
                        ),
                        3: foundation._v(query.visibility.value),
                    },
                )
            )
    runtime = {
        0: [
            {
                0: foundation._ordinal("occurrence-ref-body-v0", occurrence_ref),
                1: [foundation._value_type_body(item) for item in output_types],
            }
            for occurrence_ref, output_types in enumerate(outputs)
        ],
        1: [
            {
                0: foundation._ordinal("challenge-ref-body-v0", challenge_ref),
                1: foundation._ordinal(
                    "occurrence-ref-body-v0", positions["challenge"][challenge_ref]
                ),
                2: foundation._value_type_body(challenge.value_type),
            }
            for challenge_ref, challenge in enumerate(core.challenges)
        ],
        2: oracle_receipts,
        3: [
            {
                0: foundation._ordinal("terminal-ref-body-v0", terminal_ref),
                1: foundation._ordinal(
                    "occurrence-ref-body-v0", positions["terminal"][terminal_ref]
                ),
                2: foundation._v(terminal.verdict.value),
                3: [
                    foundation._value_type_body(
                        foundation._value_type(core, outputs, item)
                    )
                    for item in terminal.public_outputs
                ],
            }
            for terminal_ref, terminal in enumerate(core.terminals)
        ],
    }
    execution = {
        0: protocol_atom,
        1: core_atom,
        2: foundation._v(0),
        3: b5._law("core-admission-v0"),
        4: resolver_rows,
        5: b5._law("execution-and-replay-v0"),
        6: runtime,
        7: foundation._v(0),
        8: b5._law("execution-and-replay-v0"),
        9: b5._law("run-view-issuance-v0"),
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
        raise IntegratedViewsError("view order differs from candidate schema")
    for name, value in views.items():
        codec.encode_value(VIEW_SCHEMAS[name], value)
    return views


def project_views(core_handle: object, protocol_handle: object) -> dict[str, Any]:
    """Project all six normalized bodies from one exact admitted D1 pair."""

    core, scenario = d1._retained_core(core_handle)
    protocol_identifier = _protocol_reference(core_handle, protocol_handle)
    core_identifier = k1.decode_content_reference(core_handle.core_reference)
    return project_admitted_values(
        core,
        core_identifier,
        protocol_identifier,
        scenario=scenario,
    )


def encode_views(views: Mapping[str, Any]) -> dict[str, bytes]:
    if tuple(views) != VIEW_ORDER:
        raise IntegratedViewsError("view table is incomplete or reordered")
    return {
        name: codec.encode_value(VIEW_SCHEMAS[name], value)
        for name, value in views.items()
    }
