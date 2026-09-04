#!/usr/bin/env python3
"""Derive candidate construction and execution views from the live subject."""

from __future__ import annotations

import importlib.util
import json
from pathlib import Path
import sys
from types import ModuleType
from typing import Any

import model


ROOT = Path(__file__).resolve().parents[2]
VIEW_PACKAGE = ROOT / "evaluation/formal-source-fs-view-determinacy-f0v3"


def _load(name: str, path: Path) -> ModuleType:
    if name in sys.modules:
        return sys.modules[name]
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise ImportError(f"cannot load {path.relative_to(ROOT)}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


view_model = _load("_zkc_fs_view_model", VIEW_PACKAGE / "model.py")
view_independent = _load(
    "_zkc_fs_view_independent", VIEW_PACKAGE / "independent.py"
)
support = _load("_zkc_fs_view_support", VIEW_PACKAGE / "support.py")
k1 = model.k1
target = model.target


class ViewUnderdetermined(RuntimeError):
    """The owner text does not define one required view coordinate."""


def _record(*values: Any) -> dict[int, Any]:
    return {index: value for index, value in enumerate(values)}


def _variant(case: int, value: Any = None) -> dict[str, Any]:
    return {"case": case, "value": value}


def _body(compiler: str, value: Any) -> dict[str, str]:
    encoded = json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=True
    ).encode("ascii")
    return {"compiler": compiler, "body": encoded.hex()}


def _raw(compiler: str, value: bytes) -> dict[str, str]:
    return {"compiler": compiler, "body": value.hex()}


def _identifier(identifier: Any, compiler: str) -> dict[str, str]:
    return _raw(compiler, identifier.internal_reference())


def _value_type(value_type: Any) -> dict[str, str]:
    return _raw(
        "value-type-body-v0", k1.encode_datum(k1.value_type_datum(value_type))
    )


def _algorithm_use(use: model.AlgorithmUse) -> dict[int, Any]:
    return _record(
        _identifier(use.algorithm.identity, "algorithm-ref-body-v0"),
        _identifier(
            use.evaluation_contract.identity,
            "evaluation-contract-id-body-v0",
        ),
    )


def _ref(compiler: str, value: Any) -> dict[str, str]:
    return _body(compiler, value)


def _law(name: str) -> dict[str, str]:
    return support.law("canonical-framed", name)


def _interaction_law(subject: model.Subject, name: str) -> dict[str, str]:
    return {
        "profile": subject.fixture.environment.profile_id.digest.hex(),
        "kind": "pir.semantic-law",
        "name": name,
    }


def _occurrence_kind(occurrence: Any) -> str:
    effect = occurrence.effect
    if type(effect) is target.ProverMessageEffect:
        return "ProverMessage"
    if type(effect) is target.ChallengeEffect:
        return "Challenge"
    if type(effect) is target.CheckEffect:
        return "Check"
    if type(effect) is target.TerminalEffect:
        return "Terminal"
    raise model.SubjectError("portable projection encountered an unknown occurrence kind")


def _occurrence_is_framed(core: Any, occurrence: Any) -> bool:
    return (
        type(occurrence.guard) is not target.AlwaysGuard
        or type(occurrence.effect) is target.ProverMessageEffect
        or (
            type(occurrence.effect) is target.ChallengeEffect
            and bool(core.challenges[occurrence.effect.challenge].public_conditions)
        )
    )


def _frame_schedule(core: Any) -> tuple[list[dict[int, Any]], dict[int, dict[int, Any]]]:
    schedule: list[dict[int, Any]] = []
    challenge_frame_entries: dict[int, dict[int, Any]] = {}
    for index, occurrence in enumerate(core.occurrences):
        if not _occurrence_is_framed(core, occurrence):
            continue
        coordinate = _record(
            index,
            _ref("occurrence-ref-body-v0", index),
            _ref("occurrence-kind-body-v0", _occurrence_kind(occurrence)),
        )
        schedule.append(coordinate)
        if type(occurrence.effect) is target.ChallengeEffect:
            challenge_frame_entries[occurrence.effect.challenge] = coordinate
    return schedule, challenge_frame_entries


def _scope_path(core: Any, scope_ref: int) -> list[dict[str, str]]:
    path: list[int] = []
    current: int | None = scope_ref
    while current is not None:
        path.append(current)
        current = core.scopes[current].parent
    return [_ref("scope-ref-body-v0", item) for item in reversed(path)]


def _static_atom(tag: int, payload: Any, required: bool) -> dict[int, Any]:
    return _record(_variant(0, _variant(tag, payload)), required)


def _symbolic_draw(challenge_ref: int) -> dict[int, Any]:
    return _record(
        _variant(1, _ref("challenge-ref-body-v0", challenge_ref)),
        True,
    )


def _required_influence(core: Any, construction: model.TranscriptConstruction, tid: Any, cid: Any) -> list[dict[int, Any]]:
    occurrences = sorted(
        (
            occurrence.effect.challenge,
            index,
            occurrence,
        )
        for index, occurrence in enumerate(core.occurrences)
        if type(occurrence.effect) is target.ChallengeEffect
    )
    result: list[dict[int, Any]] = []
    for challenge_ref, challenge_index, challenge_occurrence in occurrences:
        challenge = core.challenges[challenge_ref]
        ancestry: set[int] = set()
        current: int | None = challenge.scope
        while current is not None:
            ancestry.add(current)
            current = core.scopes[current].parent
        entries = [
            _static_atom(0, cid, True),
            _static_atom(1, tid, True),
            _static_atom(
                2,
                _raw(
                    "protocol-declaration-ref-body-v0",
                    k1.encode_datum(
                        model._module_ref_body(construction.application_domain)
                    ),
                ),
                True,
            ),
        ]

        def add_scopes(opening: int | None) -> None:
            for scope_ref, scope in enumerate(core.scopes):
                if scope.opening != opening:
                    continue
                required = scope_ref in ancestry
                entries.append(
                    _static_atom(3, _scope_path(core, scope_ref), required)
                )
                for binding_ref, binding in enumerate(core.public_bindings):
                    if binding.scope == scope_ref:
                        entries.append(
                            _static_atom(
                                4,
                                _ref("binding-ref-body-v0", binding_ref),
                                required,
                            )
                        )

        add_scopes(None)
        for index, occurrence in enumerate(core.occurrences[: challenge_index + 1]):
            add_scopes(index)
            if type(occurrence.guard) is not target.AlwaysGuard:
                entries.append(
                    _static_atom(
                        5,
                        _ref("occurrence-ref-body-v0", index),
                        True,
                    )
                )
            effect = occurrence.effect
            if type(effect) is target.ChallengeEffect:
                entries.extend(
                    _static_atom(
                        11,
                        _record(
                            _ref("challenge-ref-body-v0", effect.challenge),
                            input_ordinal,
                        ),
                        index == challenge_index,
                    )
                    for input_ordinal, _condition in enumerate(
                        core.challenges[effect.challenge].public_conditions
                    )
                )
                if index < challenge_index:
                    entries.append(_symbolic_draw(effect.challenge))
            elif index < challenge_index and type(effect) is target.ProverMessageEffect:
                entries.append(
                    _static_atom(
                        6,
                        _ref("occurrence-ref-body-v0", index),
                        True,
                    )
                )
        result.append(
            _record(_ref("challenge-ref-body-v0", challenge_ref), entries)
        )
    return result


def _sampling_input_types(core: Any, construction: model.TranscriptConstruction, challenge_ref: int) -> list[dict[str, str]]:
    challenge = core.challenges[challenge_ref]
    outputs = target._output_types(core)
    value_types = [construction.transcript_bytes_type]
    value_types.extend(
        target._value_type(core, outputs, condition)
        for condition in challenge.public_conditions
    )
    if type(challenge.correlation) is target.JointCorrelation:
        value_types.extend(
            core.challenges[prior].value_type
            for prior in challenge.correlation.prior_members
        )
    return [_value_type(value_type) for value_type in value_types]


def _challenge_rule_value(
    core: Any,
    construction: model.TranscriptConstruction,
    rule: model.ChallengeRule,
    position: int,
) -> dict[int, Any]:
    input_types = _sampling_input_types(core, construction, rule.challenge)
    return _record(
        _ref("challenge-ref-body-v0", rule.challenge),
        position,
        _record(
            _algorithm_use(rule.accept),
            input_types,
            _value_type(k1.BOOL),
        ),
        _record(
            _algorithm_use(rule.decode),
            input_types,
            _value_type(core.challenges[rule.challenge].value_type),
        ),
        _record(rule.draw_bytes, rule.maximum_draws),
    )


def _construction_views(
    core: Any,
    construction: model.TranscriptConstruction,
    checked: model.CheckedConstruction | None,
) -> tuple[dict[str, Any], tuple[int, ...]]:
    tid = _identifier(
        construction.identifier, "transcript-construction-id-body-v0"
    )
    cid = _identifier(construction.core_id, "core-id-body-v0")
    schedule, challenge_frame_entries = _frame_schedule(core)
    transcript = _record(
        tid,
        cid,
        _value_type(construction.transcript_state_type),
        _value_type(construction.transcript_bytes_type),
        _raw(
            "canonical-value-body-v0",
            k1.encode_datum(construction.initial_state.datum),
        ),
        _law("canonical-framed-body-grammar-v0"),
        _algorithm_use(construction.absorb),
        _algorithm_use(construction.squeeze_bytes),
        _algorithm_use(construction.advance_state),
        _raw(
            "protocol-declaration-ref-body-v0",
            k1.encode_datum(
                model._module_ref_body(construction.application_domain)
            ),
        ),
        _raw(
            "semantic-failure-type-body-v0",
            k1.encode_datum(
                k1.semantic_failure_type_datum(
                    construction.sampling_exhausted_failure
                )
            ),
        ),
        _law("canonical-framed-source-views-v0"),
        schedule,
    )

    influence = _record(
        tid,
        cid,
        [
            _record(
                _ref("scope-ref-body-v0", scope_ref),
                _variant(0)
                if scope.parent is None
                else _variant(1, _ref("scope-ref-body-v0", scope.parent)),
                _variant(0)
                if scope.opening is None
                else _variant(1, _ref("occurrence-ref-body-v0", scope.opening)),
            )
            for scope_ref, scope in enumerate(core.scopes)
        ],
        _required_influence(core, construction, tid, cid),
        [
            _record(_ref("challenge-ref-body-v0", challenge_ref), [])
            for challenge_ref in range(len(core.challenges))
        ],
        _law("canonical-framed-prefix-and-domain-v0"),
    )

    values = {
        "CanonicalTranscriptDeclarationView": transcript,
        "CanonicalRequiredInfluenceView": influence,
    }
    missing = tuple(
        rule.challenge
        for rule in construction.challenge_rules
        if rule.challenge not in challenge_frame_entries
    )
    if not missing:
        values["CanonicalChallengeTransitionView"] = _record(
            tid,
            cid,
            _law("canonical-framed-prefix-and-domain-v0"),
            _law("canonical-framed-body-grammar-v0"),
            _law("canonical-framed-admission-and-execution-v0"),
            _law("canonical-framed-admission-and-execution-v0"),
            _law("canonical-framed-admission-and-execution-v0"),
            [
                _challenge_rule_value(
                    core,
                    construction,
                    rule,
                    challenge_frame_entries[rule.challenge][0],
                )
                for rule in construction.challenge_rules
            ],
        )
    if checked is not None:
        values["CanonicalFSConstructionView"] = _record(
            _body("runtime-schema-body-v0", "CheckedFSConstruction"),
            _identifier(checked.source_protocol_id, "protocol-id-body-v0"),
            _identifier(checked.target_protocol_id, "protocol-id-body-v0"),
            _identifier(checked.shared_core_id, "core-id-body-v0"),
            _identifier(
                checked.transcript_construction_id,
                "transcript-construction-id-body-v0",
            ),
            [
                _record(
                    _ref("occurrence-ref-body-v0", left),
                    _ref("occurrence-ref-body-v0", right),
                )
                for left, right in checked.occurrence_map
            ],
            [
                _record(
                    _ref("value-ref-body-v0", left),
                    _ref("value-ref-body-v0", right),
                )
                for left, right in checked.value_map
            ],
            [
                _record(
                    _ref("challenge-ref-body-v0", left),
                    _ref("challenge-ref-body-v0", right),
                )
                for left, right in checked.challenge_map
            ],
            _record(
                _variant(0),
                _law("canonical-framed-same-core-construction-v0"),
            ),
        )
    return values, missing


def construction_views(subject: model.Subject) -> dict[str, Any]:
    values, _missing = _construction_views(
        subject.fixture.core_candidate.core,
        subject.construction,
        subject.checked,
    )
    return values


def execution_view(subject: model.Subject) -> dict[str, Any]:
    construction = subject.construction
    _schedule, challenge_frame_entries = _frame_schedule(
        subject.fixture.core_candidate.core
    )
    occurrence_by_challenge = {
        occurrence.effect.challenge: occurrence_ref
        for occurrence_ref, occurrence in enumerate(
            subject.fixture.core_candidate.core.occurrences
        )
        if type(occurrence.effect) is target.ChallengeEffect
    }
    missing = tuple(
        rule.challenge
        for rule in construction.challenge_rules
        if rule.challenge not in challenge_frame_entries
    )
    if missing:
        raise ViewUnderdetermined(
            "docs-next/pir/fiat-shamir.md Section 13 requires each resolver "
            "coordinate to name the challenge occurrence's frame_schedule "
            f"entry, but unframed challenge refs {list(missing)} have none"
        )
    return {
        "protocol_id": model.identifier_text(subject.fs_protocol.identifier),
        "core_id": model.identifier_text(construction.core_id),
        "transcript_construction_id": model.identifier_text(
            construction.identifier
        ),
        "challenge_interpretation": {
            "kind": "FiatShamir",
            "construction": model.identifier_text(construction.identifier),
        },
        "visible_history_law": _interaction_law(subject, "visible-history-v0"),
        "resolver_coordinates": [
            {
                "challenge_ref": rule.challenge,
                "occurrence_ref": occurrence_by_challenge[rule.challenge],
                "value_type": _value_type(
                    subject.fixture.core_candidate.core.challenges[
                        rule.challenge
                    ].value_type
                ),
                "frame_schedule_coordinate": challenge_frame_entries[
                    rule.challenge
                ],
                "decoding_coordinate": _challenge_rule_value(
                    subject.fixture.core_candidate.core,
                    construction,
                    rule,
                    challenge_frame_entries[rule.challenge][0],
                ),
            }
            for rule in construction.challenge_rules
        ],
        "generated_execution_law": _law(
            "canonical-framed-protocol-execution-v0"
        ),
        "run_record_schema": {
            "variant": ["TerminalCompletion", "InterpretationFailure"],
            "challenge_receipt": "FSChallengeReceipt",
            "interpretation_failure_receipt": "FSInterpretationFailureReceipt",
        },
        "interpretation_failure_schema": "FSSamplingFailureReceipt",
        "outcome_partition": [
            "Accepted",
            "Rejected",
            "Aborted",
            "InterpretationFailed",
            "StrategyStopped",
            "OperationalNoncompletion",
        ],
        "replay_qualification_law": _law("canonical-framed-replay-v0"),
        "relation_run_view_issuance_law": _interaction_law(
            subject, "run-view-issuance-v0"
        ),
    }


def _compiled_predecessor() -> tuple[
    dict[str, Any], dict[str, Any], dict[str, Any]
]:
    recursive, recursive_digests, _ = view_model.compile_current()
    iterative, iterative_digests, _ = view_independent.compile_current()
    if recursive_digests != iterative_digests:
        raise model.SubjectError("predecessor family-view schema compilers disagree")
    return recursive, iterative, view_model.load_source()["owner_profiles"]


def _validate_values(values: dict[str, Any]) -> dict[str, str]:
    recursive, iterative, profiles = _compiled_predecessor()
    for name, value in values.items():
        view_model.validate_view(
            "canonical-framed", name, recursive, value, profiles
        )
        view_independent.validate_view(
            "canonical-framed", name, iterative, value, profiles
        )
    return {
        name: view_model.digest(value)
        for name, value in sorted(values.items())
    }


def validate_against_predecessor(
    subject: model.Subject,
) -> tuple[dict[str, str], tuple[int, ...]]:
    values, missing = _construction_views(
        subject.fixture.core_candidate.core,
        subject.construction,
        subject.checked,
    )
    return _validate_values(values), missing


def validate_portable_projection_suite() -> dict[str, Any]:
    """Validate repaired bodies against one heterogeneous admitted Core."""

    suite = model.make_portable_projection_suite()
    values, missing = _construction_views(
        suite.core,
        suite.construction,
        None,
    )
    if missing:
        raise model.SubjectError(
            "portable projection suite unexpectedly has unframed challenges"
        )
    digests = _validate_values(values)
    if set(values) != {
        "CanonicalTranscriptDeclarationView",
        "CanonicalRequiredInfluenceView",
        "CanonicalChallengeTransitionView",
    }:
        raise model.SubjectError("portable projection suite emitted another view set")

    transition_rules = values["CanonicalChallengeTransitionView"][7]
    if len(transition_rules) != 2:
        raise model.SubjectError("portable transition view did not retain both rules")
    if [rule[0]["body"] for rule in transition_rules] != [
        _ref("challenge-ref-body-v0", challenge)["body"]
        for challenge in (0, 1)
    ]:
        raise model.SubjectError("portable transition rules are not challenge ordered")
    if [rule[1] for rule in transition_rules] != list(
        suite.challenge_occurrences
    ):
        raise model.SubjectError("portable transition positions are not exact")
    if transition_rules[0][3][2] == transition_rules[1][3][2]:
        raise model.SubjectError("portable decoder result types are not distinct")
    if [rule[4] for rule in transition_rules] != [
        _record(1, 1),
        _record(2, 3),
    ]:
        raise model.SubjectError("portable transition draw bounds drifted")

    influence = values["CanonicalRequiredInfluenceView"][3]
    if len(influence) != 2:
        raise model.SubjectError("portable influence view omitted a challenge")

    def static_tag(entry: dict[int, Any]) -> int | None:
        atom = entry[0]
        if atom["case"] != 0:
            return None
        return atom["value"]["case"]

    first_entries = influence[0][1]
    first_binding_entries = [
        entry for entry in first_entries if static_tag(entry) == 4
    ]
    if len(first_binding_entries) != 2:
        raise model.SubjectError(
            "portable influence view did not retain both root bindings"
        )
    if first_binding_entries[0][0] == first_binding_entries[1][0]:
        raise model.SubjectError("portable root binding coordinates alias")

    second_entries = influence[1][1]
    symbolic = [entry for entry in second_entries if entry[0]["case"] == 1]
    if len(symbolic) != 1 or symbolic[0] != _symbolic_draw(0):
        raise model.SubjectError(
            "portable influence view omitted the earlier symbolic draw"
        )

    return {
        "core_id": model.identifier_text(suite.admitted_core.core_id),
        "transcript_construction_id": model.identifier_text(
            suite.construction.identifier
        ),
        "challenge_rule_count": len(transition_rules),
        "challenge_positions": [rule[1] for rule in transition_rules],
        "decoder_result_types_distinct": True,
        "draw_bounds": [[rule[4][0], rule[4][1]] for rule in transition_rules],
        "root_binding_atom_count": len(first_binding_entries),
        "symbolic_earlier_draw_count": len(symbolic),
        "construction_view_sha256": digests,
    }
