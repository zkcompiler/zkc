"""Typed witness path into the F0-V3 candidate view values."""

from __future__ import annotations

import importlib.util
import json
from pathlib import Path
import sys
from typing import Any

from support import algorithm_use, body, law, raw_body, record, ref, variant


ROOT = Path(__file__).resolve().parents[2]
K2_PATH = ROOT / "evaluation/k2-protocol-fiat-shamir/reference_model.py"
DUPLEX_ROOT = ROOT / "evaluation/duplex-sponge-transcript"
DUPLEX_CASE = DUPLEX_ROOT / "cases/construction.json"


def _load_k2() -> Any:
    name = "_zkc_f0v3_typed_k2"
    if name in sys.modules:
        return sys.modules[name]
    spec = importlib.util.spec_from_file_location(name, K2_PATH)
    if spec is None or spec.loader is None:
        raise RuntimeError("cannot load the K2 witness")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def _identifier(identifier: object, compiler: str) -> dict[str, str]:
    value = identifier.internal_reference()
    if type(value) is not bytes:
        raise RuntimeError("K2 identifier did not expose canonical reference bytes")
    return raw_body(compiler, value)


def _scope(scope: object) -> dict[int, Any]:
    return record(
        ref("scope-ref-body-v0", scope.name),
        variant(0) if scope.parent is None else variant(1, ref("scope-ref-body-v0", scope.parent)),
        (
            variant(0)
            if scope.open_before is None
            else variant(1, ref("occurrence-ref-body-v0", scope.open_before))
        ),
    )


def _value_type(k2: Any, core: object, value_ref: object) -> dict[str, str]:
    if value_ref.kind is k2.RefKind.INPUT:
        selected = tuple(item for item in core.inputs if item.name == value_ref.name)
        if len(selected) != 1:
            raise RuntimeError("typed fixture condition names another input")
        sort = selected[0].value_sort
    else:
        selected = tuple(item for item in core.schedule if item.name == value_ref.name)
        if len(selected) != 1:
            raise RuntimeError("typed fixture condition names another occurrence")
        occurrence = selected[0]
        if occurrence.kind is k2.OccurrenceKind.CHALLENGE:
            sort = k2.ValueSort.NAT
        elif occurrence.kind is k2.OccurrenceKind.PROVER_MESSAGE:
            sort = occurrence.prover_value_sort
        else:
            raise RuntimeError("typed fixture condition result type is not represented")
    names = {
        k2.ValueSort.BYTES: "Bytes",
        k2.ValueSort.NAT: "Natural",
        k2.ValueSort.BOOL: "Boolean",
        k2.ValueSort.ORACLE: "Oracle",
    }
    return ref("value-type-body-v0", names[sort])


def _scope_path(core: object, name: str) -> list[dict[str, str]]:
    by_name = {item.name: item for item in core.scopes}
    path: list[str] = []
    current: str | None = name
    while current is not None:
        path.append(current)
        current = by_name[current].parent
    return [ref("scope-ref-body-v0", item) for item in reversed(path)]


def _framed_occurrence(k2: Any, occurrence: object) -> bool:
    return (
        occurrence.guard.kind is not k2.PredicateKind.ALWAYS
        or occurrence.kind
        in {
            k2.OccurrenceKind.PROVER_MESSAGE,
            k2.OccurrenceKind.VERIFIER_MESSAGE,
            k2.OccurrenceKind.ORACLE_PUBLISH,
            k2.OccurrenceKind.ORACLE_QUERY,
            k2.OccurrenceKind.ORACLE_ANSWER,
        }
        or (
            occurrence.kind is k2.OccurrenceKind.CHALLENGE
            and bool(occurrence.dependencies)
        )
    )


def _static_atom(tag: int, payload: Any, required: bool) -> dict[int, Any]:
    return record(variant(0, variant(tag, payload)), required)


def _symbolic_draw(challenge: str) -> dict[int, Any]:
    return record(
        variant(1, ref("challenge-ref-body-v0", challenge)),
        True,
    )


def _required_entries(k2: Any, core: object, construction: object, cid: Any, tid: Any) -> list[dict[int, Any]]:
    challenges = [
        (index, item)
        for index, item in enumerate(core.schedule)
        if item.kind is k2.OccurrenceKind.CHALLENGE
    ]
    action_tags = {
        k2.OccurrenceKind.PROVER_MESSAGE: 6,
        k2.OccurrenceKind.VERIFIER_MESSAGE: 7,
        k2.OccurrenceKind.ORACLE_PUBLISH: 8,
        k2.OccurrenceKind.ORACLE_QUERY: 9,
        k2.OccurrenceKind.ORACLE_ANSWER: 10,
    }
    by_scope = {item.name: item for item in core.scopes}

    def ancestry(scope: str) -> set[str]:
        result: set[str] = set()
        current: str | None = scope
        while current is not None:
            result.add(current)
            current = by_scope[current].parent
        return result

    result: list[dict[int, Any]] = []
    for challenge_index, challenge in challenges:
        required_scopes = ancestry(challenge.scope)
        entries = [
            _static_atom(0, cid, True),
            _static_atom(1, tid, True),
            _static_atom(
                2,
                body(
                    "protocol-declaration-ref-body-v0",
                    construction.application_domain.hex(),
                ),
                True,
            ),
        ]

        def add_scopes(open_before: str | None) -> None:
            for scope in core.scopes:
                if scope.open_before != open_before:
                    continue
                is_required = scope.name in required_scopes
                entries.append(
                    _static_atom(3, _scope_path(core, scope.name), is_required)
                )
                for binding in core.inputs:
                    if (
                        binding.scope == scope.name
                        and binding.role is not k2.InputRole.VERIFIER_PRIVATE
                    ):
                        entries.append(
                            _static_atom(
                                4,
                                ref("binding-ref-body-v0", binding.name),
                                is_required,
                            )
                        )

        add_scopes(None)
        for index, occurrence in enumerate(core.schedule[: challenge_index + 1]):
            add_scopes(occurrence.name)
            if occurrence.guard.kind is not k2.PredicateKind.ALWAYS:
                entries.append(
                    _static_atom(
                        5,
                        ref("occurrence-ref-body-v0", occurrence.name),
                        True,
                    )
                )
            if occurrence.kind is k2.OccurrenceKind.CHALLENGE:
                entries.extend(
                    _static_atom(
                        11,
                        record(
                            ref("challenge-ref-body-v0", occurrence.name),
                            ordinal,
                        ),
                        index == challenge_index,
                    )
                    for ordinal, _dependency in enumerate(occurrence.dependencies)
                )
                if index < challenge_index:
                    entries.append(_symbolic_draw(occurrence.name))
            elif index < challenge_index and occurrence.kind in action_tags:
                entries.append(
                    _static_atom(
                        action_tags[occurrence.kind],
                        ref("occurrence-ref-body-v0", occurrence.name),
                        True,
                    )
                )
        result.append(
            record(ref("challenge-ref-body-v0", challenge.name), entries)
        )
    return result


def _canonical_values(k2: Any, core: object, construction: object, checked: object) -> dict[str, Any]:
    cid = _identifier(k2.core_id(core), "core-id-body-v0")
    tid = _identifier(k2.construction_id(core, construction), "transcript-construction-id-body-v0")
    schedule = [
        record(
            index,
            ref("occurrence-ref-body-v0", item.name),
            ref("occurrence-kind-body-v0", item.kind.value),
        )
        for index, item in enumerate(core.schedule)
        if _framed_occurrence(k2, item)
    ]
    challenge_items = [
        (index, item)
        for index, item in enumerate(core.schedule)
        if item.kind is k2.OccurrenceKind.CHALLENGE
    ]
    influence_entries = _required_entries(k2, core, construction, cid, tid)
    additions = []
    for _index, challenge in challenge_items:
        names = [
            publication.publication
            for reduction in core.reductions
            for publication in reduction.required_publications
            if publication.next_challenge == challenge.name
        ]
        additions.append(
            record(
                ref("challenge-ref-body-v0", challenge.name),
                [ref("value-ref-body-v0", name) for name in names],
            )
        )
    transcript = record(
        tid,
        cid,
        ref("value-type-body-v0", f"Bytes[{construction.state_bytes}]"),
        ref("value-type-body-v0", "Bytes"),
        body("canonical-value-body-v0", k2.INITIAL_TRANSCRIPT_STATE.hex()),
        law("canonical-framed", "canonical-framed-body-grammar-v0"),
        algorithm_use(construction.version + ":absorb", "k2-absorb-contract-v1"),
        algorithm_use(construction.version + ":squeeze", "k2-squeeze-contract-v1"),
        algorithm_use(construction.version + ":advance", "k2-advance-contract-v1"),
        body("protocol-declaration-ref-body-v0", construction.application_domain.hex()),
        ref("semantic-failure-type-body-v0", "SamplingExhausted"),
        law("canonical-framed", "canonical-framed-source-views-v0"),
        schedule,
    )
    influence = record(
        tid,
        cid,
        [_scope(scope) for scope in core.scopes],
        influence_entries,
        additions,
        law("canonical-framed", "canonical-framed-prefix-and-domain-v0"),
    )
    rules = []
    for position, item in challenge_items:
        input_types = [ref("value-type-body-v0", "Bytes")]
        input_types.extend(_value_type(k2, core, dependency) for dependency in item.dependencies)
        rules.append(
            record(
                ref("challenge-ref-body-v0", item.name),
                position,
                record(
                    algorithm_use("big-endian-rejection-accept-v1", "k2-accept-contract-v1"),
                    input_types,
                    ref("value-type-body-v0", "Boolean"),
                ),
                record(
                    algorithm_use("big-endian-rejection-decode-v1", "k2-decode-contract-v1"),
                    input_types,
                    ref("value-type-body-v0", "Natural"),
                ),
                record(construction.sample_bytes, construction.max_attempts),
            )
        )
    transition = record(
        tid,
        cid,
        law("canonical-framed", "canonical-framed-prefix-and-domain-v0"),
        law("canonical-framed", "canonical-framed-body-grammar-v0"),
        law("canonical-framed", "canonical-framed-admission-and-execution-v0"),
        law("canonical-framed", "canonical-framed-admission-and-execution-v0"),
        law("canonical-framed", "canonical-framed-admission-and-execution-v0"),
        rules,
    )
    result = checked.result
    result_value = record(
        body("runtime-schema-body-v0", "CheckedFSConstruction"),
        _identifier(result.source_protocol_id, "protocol-id-body-v0"),
        _identifier(result.target_protocol_id, "protocol-id-body-v0"),
        _identifier(result.shared_core_id, "core-id-body-v0"),
        _identifier(result.transcript_construction_id, "transcript-construction-id-body-v0"),
        [
            record(ref("occurrence-ref-body-v0", left), ref("occurrence-ref-body-v0", right))
            for left, right in result.occurrence_map
        ],
        [
            record(ref("value-ref-body-v0", left), ref("value-ref-body-v0", right))
            for left, right in result.value_map
        ],
        [
            record(ref("challenge-ref-body-v0", left), ref("challenge-ref-body-v0", right))
            for left, right in result.challenge_map
        ],
        record(
            variant(0),
            law("canonical-framed", "canonical-framed-same-core-construction-v0"),
        ),
    )
    values = {
        "CanonicalTranscriptDeclarationView": transcript,
        "CanonicalRequiredInfluenceView": influence,
        "CanonicalFSConstructionView": result_value,
    }
    values["CanonicalChallengeTransitionView"] = transition
    return values


def _k2_raw(k2: Any, name: str, core: object, construction: object, checked: object) -> dict[str, Any]:
    result = checked.result
    return {
        "name": name,
        "ids": {
            "core": k2.core_id(core).internal_reference().hex(),
            "construction": k2.construction_id(core, construction).internal_reference().hex(),
            "fresh_protocol": result.source_protocol_id.internal_reference().hex(),
            "fs_protocol": result.target_protocol_id.internal_reference().hex(),
        },
        "construction": {
            "application_domain": construction.application_domain.hex(),
            "sample_bytes": construction.sample_bytes,
            "max_attempts": construction.max_attempts,
            "state_bytes": construction.state_bytes,
            "version": construction.version,
            "initial_state": k2.INITIAL_TRANSCRIPT_STATE.hex(),
        },
        "inputs": [
            {
                "name": item.name,
                "role": item.role.value,
                "scope": item.scope,
                "value_sort": item.value_sort.value,
            }
            for item in core.inputs
        ],
        "scopes": [
            {"name": item.name, "parent": item.parent, "open_before": item.open_before}
            for item in core.scopes
        ],
        "schedule": [
            {
                "name": item.name,
                "kind": item.kind.value,
                "scope": item.scope,
                "dependencies": [
                    {"kind": ref_value.kind.value, "name": ref_value.name}
                    for ref_value in item.dependencies
                ],
                "guard_nontrivial": item.guard.kind is not k2.PredicateKind.ALWAYS,
                "prover_value_sort": item.prover_value_sort.value,
            }
            for item in core.schedule
        ],
        "additions": [
            {
                "challenge": item.name,
                "publications": [
                    publication.publication
                    for reduction in core.reductions
                    for publication in reduction.required_publications
                    if publication.next_challenge == item.name
                ],
            }
            for item in core.schedule
            if item.kind is k2.OccurrenceKind.CHALLENGE
        ],
        "result": {
            "occurrence_map": [list(pair) for pair in result.occurrence_map],
            "value_map": [list(pair) for pair in result.value_map],
            "challenge_map": [list(pair) for pair in result.challenge_map],
        },
    }


def k2_cases() -> list[tuple[str, dict[str, Any], dict[str, Any]]]:
    k2 = _load_k2()
    cases = []
    for name, fixture in (("schnorr", k2.schnorr_fixture), ("oracle", k2.oracle_fixture)):
        core, construction, _invocation, _strategy = fixture()
        k2.admit_core(core)
        construction.admit()
        outcome = k2.check_fs_construction(core, core, construction)
        if outcome.kind is not k2.QualifiedViewOutcomeKind.AFFIRMATIVE:
            raise RuntimeError(f"typed K2 {name} construction was not affirmative")
        checked = outcome.value
        cases.append(
            (
                name,
                _k2_raw(k2, name, core, construction, checked),
                _canonical_values(k2, core, construction, checked),
            )
        )
    return cases


def _duplex_values(construction: Any, construction_module: Any) -> dict[str, Any]:
    core = construction.core
    cid_text = construction_module.core_id(core)
    tid_text = construction_module.construction_id(construction)
    cid = body("core-id-body-v0", cid_text)
    tid = body("transcript-construction-id-body-v0", tid_text)
    bindings = [ref("binding-ref-body-v0", item.name) for item in core.initial_bindings]
    messages = [item for item in core.schedule if item.kind == "ProverMessage"]
    challenges = [item for item in core.schedule if item.kind == "Challenge"]
    schedule = [
        record(index, ref("occurrence-ref-body-v0", item.name), ref("occurrence-kind-body-v0", item.kind))
        for index, item in enumerate(core.schedule)
    ]
    salt_coordinate = record(variant(0), 0)
    material_schema = record(
        salt_coordinate,
        ref("value-type-body-v0", "Sigma5Sequence"),
        construction.salt_length,
    )
    message_entries = [
        record(
            ref("occurrence-ref-body-v0", item.occurrence),
            algorithm_use(item.codec + ":" + item.to_term()["algorithm"], "duplex-message-codec-contract-v0"),
            item.encoded_length,
        )
        for item in construction.message_codecs
    ]
    transcript = record(
        tid,
        cid,
        variant(0),
        ref("value-type-body-v0", "Sigma5"),
        body("canonical-value-body-v0", 0),
        3,
        2,
        record(
            ref("value-type-body-v0", "DuplexState<Sigma5,rate=3,capacity=2>"),
            law("duplex-sponge", "duplex-sponge-state-transition-v0"),
        ),
        record(
            ref("value-type-body-v0", f"BinaryInstance<{construction.instance_bit_bound}>"),
            law("duplex-sponge", "duplex-sponge-body-grammar-v0"),
        ),
        record(bindings, law("duplex-sponge", "duplex-sponge-source-views-v0")),
        algorithm_use("StartHash:" + construction.provider_interface[0], "duplex-start-contract-v0"),
        algorithm_use("ForwardPermutation:" + construction.provider_interface[1], "duplex-permutation-contract-v0"),
        law("duplex-sponge", "duplex-sponge-state-transition-v0"),
        law("duplex-sponge", "duplex-sponge-state-transition-v0"),
        material_schema,
        message_entries,
        record(
            [
                record(ref("occurrence-ref-body-v0", item.name), ref("value-type-body-v0", item.value_type))
                for item in messages
            ],
            [
                record(ref("challenge-ref-body-v0", item.name), ref("value-type-body-v0", item.value_type))
                for item in challenges
            ],
        ),
        schedule,
        schedule,
        record(len(core.schedule), sum(item.encoded_length for item in construction.message_codecs), sum(item.squeeze_length for item in construction.challenge_decoders)),
    )
    coverage_entries = []
    prior_messages: list[Any] = []
    for item in core.schedule:
        if item.kind == "ProverMessage":
            prior_messages.append(item)
        elif item.kind == "Challenge":
            atoms = [variant(0, binding) for binding in bindings]
            atoms.append(variant(1, salt_coordinate))
            atoms.extend(
                variant(2, ref("occurrence-ref-body-v0", message.name))
                for message in prior_messages
            )
            coverage_entries.append(record(ref("challenge-ref-body-v0", item.name), atoms))
    coverage = record(
        tid,
        cid,
        bindings,
        salt_coordinate,
        coverage_entries,
        [ref("occurrence-ref-body-v0", item.name) for item in messages],
        [ref("challenge-ref-body-v0", item.name) for item in challenges],
        law("duplex-sponge", "duplex-sponge-prover-required-prefix-v0"),
        law("duplex-sponge", "duplex-sponge-state-transition-v0"),
        [],
    )
    decoder_entries = [
        record(
            ref("challenge-ref-body-v0", item.occurrence),
            item.squeeze_length,
            algorithm_use(item.decoder + ":" + item.to_term()["algorithm"], "duplex-decoder-contract-v0"),
        )
        for item in construction.challenge_decoders
    ]
    transition = record(
        tid,
        cid,
        decoder_entries,
        law("duplex-sponge", "duplex-sponge-admission-and-execution-v0"),
        law("duplex-sponge", "duplex-sponge-state-transition-v0"),
        variant(0),
        variant(0),
        variant(0),
        [ref("challenge-ref-body-v0", item.name) for item in challenges],
        [ref("challenge-ref-body-v0", item.name) for item in challenges],
        [
            record(ref("challenge-ref-body-v0", item.name), ref("occurrence-ref-body-v0", item.name), index)
            for index, item in enumerate(challenges)
        ],
    )
    return {
        "DuplexTranscriptDeclarationView": transcript,
        "DuplexEncodedInputCoverageView": coverage,
        "DuplexChallengeTransitionView": transition,
    }


def duplex_case() -> tuple[dict[str, Any], dict[str, Any]]:
    if str(DUPLEX_ROOT) not in sys.path:
        sys.path.insert(0, str(DUPLEX_ROOT))
    from duplexmodel import construction as construction_module

    raw = json.loads(DUPLEX_CASE.read_text(encoding="utf-8"))
    construction = construction_module.parse_construction(raw)
    return raw, _duplex_values(construction, construction_module)
