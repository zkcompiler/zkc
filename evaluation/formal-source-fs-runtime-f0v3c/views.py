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


def construction_views(subject: model.Subject) -> dict[str, Any]:
    construction = subject.construction
    checked = subject.checked
    tid = _identifier(
        construction.identifier, "transcript-construction-id-body-v0"
    )
    cid = _identifier(construction.core_id, "core-id-body-v0")
    occurrence_kinds = (
        "ProverMessage",
        "Challenge",
        "ProverMessage",
        "Check",
        "Terminal",
        "Terminal",
    )
    schedule = [
        _record(
            index,
            _ref("occurrence-ref-body-v0", index),
            _ref("occurrence-kind-body-v0", kind),
        )
        for index, kind in enumerate(occurrence_kinds)
    ]
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

    prover_kind = _ref("occurrence-kind-body-v0", "ProverMessage")
    influence = _record(
        tid,
        cid,
        [prover_kind],
        [_record(_ref("scope-ref-body-v0", 0), _variant(0), _variant(0))],
        [
            _record(
                _ref("challenge-ref-body-v0", 0),
                [
                    _record(
                        _ref("occurrence-ref-body-v0", 0),
                        [prover_kind],
                        False,
                    )
                ],
            )
        ],
        [_record(_ref("challenge-ref-body-v0", 0), [])],
        _law("canonical-framed-prefix-and-domain-v0"),
    )

    rule = construction.challenge_rules[0]
    transition = _record(
        tid,
        cid,
        _law("canonical-framed-prefix-and-domain-v0"),
        _record(
            _algorithm_use(rule.accept),
            [_value_type(construction.transcript_bytes_type)],
            _value_type(k1.BOOL),
        ),
        _record(
            _algorithm_use(rule.decode),
            [_value_type(construction.transcript_bytes_type)],
            _value_type(model.Z3),
        ),
        _record(rule.draw_bytes, rule.maximum_draws),
        _law("canonical-framed-body-grammar-v0"),
        _law("canonical-framed-admission-and-execution-v0"),
        _law("canonical-framed-admission-and-execution-v0"),
        _law("canonical-framed-admission-and-execution-v0"),
        [_record(_ref("challenge-ref-body-v0", 0), 1)],
    )

    checked_value = _record(
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
    return {
        "CanonicalTranscriptDeclarationView": transcript,
        "CanonicalRequiredInfluenceView": influence,
        "CanonicalChallengeTransitionView": transition,
        "CanonicalFSConstructionView": checked_value,
    }


def execution_view(subject: model.Subject) -> dict[str, Any]:
    construction = subject.construction
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
                "challenge_ref": 0,
                "occurrence_ref": 1,
                "value_type": _value_type(model.Z3),
                "frame_schedule_coordinate": {
                    "condition_frames": [],
                    "prefix_occurrences": [0],
                },
                "decoding_coordinate": {
                    "accept_algorithm": model.identifier_text(
                        construction.challenge_rules[0].accept.algorithm.identity
                    ),
                    "decode_algorithm": model.identifier_text(
                        construction.challenge_rules[0].decode.algorithm.identity
                    ),
                },
            }
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


def validate_against_predecessor(subject: model.Subject) -> dict[str, str]:
    recursive, recursive_digests, _ = view_model.compile_current()
    iterative, iterative_digests, _ = view_independent.compile_current()
    if recursive_digests != iterative_digests:
        raise model.SubjectError("predecessor family-view schema compilers disagree")
    values = construction_views(subject)
    profiles = view_model.load_source()["owner_profiles"]
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
