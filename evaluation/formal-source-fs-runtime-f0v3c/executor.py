#!/usr/bin/env python3
"""First path: generate finite Core runs with canonical-framed resolver hooks."""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
from typing import Any

import model


k1 = model.k1
target = model.target


@dataclass(frozen=True)
class RunCase:
    name: str
    source: str
    statement: int
    commitment: int
    response: int | None = None
    witness: int | None = None
    nonce: int | None = None


@dataclass(frozen=True)
class ExecutionResult:
    case: RunCase
    lane: str
    record: dict[str, Any]
    transcript_prefix: tuple[str, ...]
    transition_receipts: tuple[dict[str, Any], ...]
    derived: dict[str, Any]


def honest_cases() -> tuple[RunCase, ...]:
    return tuple(
        RunCase(
            f"honest-s{statement}-w{witness}-n{nonce}",
            "honest",
            statement,
            nonce,
            witness=witness,
            nonce=nonce,
        )
        for statement in range(3)
        for witness in range(3)
        for nonce in range(3)
    )


def verifier_cases() -> tuple[RunCase, ...]:
    return tuple(
        RunCase(
            f"verifier-s{statement}-a{commitment}-z{response}",
            "verifier-input",
            statement,
            commitment,
            response=response,
        )
        for statement in range(3)
        for commitment in range(3)
        for response in range(3)
    )


def all_cases() -> tuple[RunCase, ...]:
    return honest_cases() + verifier_cases()


def _record(*values: Any) -> Any:
    return k1.DatumRecord(tuple(enumerate(values)))


def _variant(case: int, payload: Any = k1.UNIT) -> Any:
    return k1.DatumVariant(case, payload)


def _seq(values: tuple[Any, ...]) -> Any:
    return k1.DatumSeq(values)


def _module_ref(reference: Any) -> Any:
    return _variant(
        1,
        _record(
            k1.BytesValue(reference.module.internal_reference()),
            k1.Symbol(reference.declaration_kind),
            k1.Nat(reference.local_ordinal),
        ),
    )


def _frame(tag: str, body: Any) -> tuple[dict[str, str], Any]:
    tags = {
        "CoreHeader": 0,
        "ConstructionHeader": 1,
        "ApplicationDomainHeader": 2,
        "ScopeOpened": 3,
        "PublicBinding": 4,
        "GuardOutcome": 5,
        "ProverMessage": 6,
    }
    datum = _variant(tags[tag], body)
    octets = k1.encode_datum(datum)
    value = k1.admit_value(
        model.TRANSCRIPT_BYTES_TYPE, k1.BytesValue(octets)
    )
    return {"kind": tag, "body": octets.hex()}, value


def _core_header(subject: model.Subject) -> tuple[dict[str, str], Any]:
    return _frame(
        "CoreHeader",
        k1.BytesValue(subject.construction.core_id.internal_reference()),
    )


def _construction_header(subject: model.Subject) -> tuple[dict[str, str], Any]:
    return _frame(
        "ConstructionHeader",
        k1.BytesValue(subject.construction.identifier.internal_reference()),
    )


def _application_header(subject: model.Subject) -> tuple[dict[str, str], Any]:
    return _frame(
        "ApplicationDomainHeader",
        _module_ref(subject.construction.application_domain),
    )


def _scope_opened() -> tuple[dict[str, str], Any]:
    return _frame("ScopeOpened", _seq((k1.Nat(0),)))


def _public_binding(statement: int) -> tuple[dict[str, str], Any]:
    value = k1.admit_value(model.Z3, k1.Nat(statement))
    return _frame(
        "PublicBinding",
        _record(
            k1.Nat(0),
            _variant(0),
            k1.value_type_datum(model.Z3),
            value.datum,
        ),
    )


def _prover_message(
    subject: model.Subject, occurrence: int, channel_ordinal: int, payload: int
) -> tuple[dict[str, str], Any]:
    module_id = subject.fixture.module.identity
    channel = target.ModuleDeclarationRef(
        module_id, "pir.message-channel", channel_ordinal
    )
    value = k1.admit_value(model.Z3, k1.Nat(payload))
    return _frame(
        "ProverMessage",
        _record(
            k1.Nat(occurrence),
            _module_ref(channel),
            k1.value_type_datum(model.Z3),
            value.datum,
        ),
    )


def _guard_outcome(occurrence: int, active: bool) -> tuple[dict[str, str], Any]:
    return _frame("GuardOutcome", _record(k1.Nat(occurrence), active))


def _namespace(subject: model.Subject, draw_ordinal: int) -> Any:
    challenge = subject.fixture.core_candidate.core.challenges[0]
    body = _record(
        k1.BytesValue(subject.construction.identifier.internal_reference()),
        k1.BytesValue(subject.construction.core_id.internal_reference()),
        _seq((k1.Nat(0),)),
        k1.Nat(0),
        _module_ref(challenge.domain),
        k1.value_type_datum(challenge.value_type),
        _variant(0),
        k1.Nat(draw_ordinal),
    )
    return k1.admit_value(
        model.TRANSCRIPT_BYTES_TYPE,
        k1.BytesValue(k1.encode_datum(body)),
    )


def _absorb(
    subject: model.Subject,
    state: Any,
    frame: tuple[dict[str, str], Any],
    transitions: list[dict[str, Any]],
    prefix: list[str],
) -> Any:
    frame_record, frame_value = frame
    post = model.evaluate(subject.construction.absorb, (state, frame_value))
    transitions.append(
        {
            "kind": "Absorbed",
            "frame": frame_record,
            "pre_state": model.canonical_value_json(state),
            "post_state": model.canonical_value_json(post),
        }
    )
    prefix.append(frame_record["body"])
    return post


def _draw(
    subject: model.Subject,
    state: Any,
    transitions: list[dict[str, Any]],
) -> tuple[Any, Any | None, list[dict[str, Any]], Any]:
    rule = subject.construction.challenge_rules[0]
    draws: list[dict[str, Any]] = []
    prefix_state = state
    prefix_count = len(transitions)
    for draw_ordinal in range(rule.maximum_draws):
        pre_state = state
        namespace = _namespace(subject, draw_ordinal)
        requested = k1.admit_value(model.NATURAL_TYPE, k1.Nat(rule.draw_bytes))
        output = model.evaluate(
            subject.construction.squeeze_bytes,
            (pre_state, namespace, requested),
        )
        if not isinstance(output.datum, k1.BytesValue) or len(output.datum.value) != rule.draw_bytes:
            raise model.SubjectError("squeeze output violated the exact length postcondition")
        post_state = model.evaluate(
            subject.construction.advance_state,
            (pre_state, namespace, requested, output),
        )
        accepted_value = model.evaluate(rule.accept, (output,))
        if type(accepted_value.datum) is not bool:
            raise model.SubjectError("acceptance algorithm did not return a Boolean datum")
        receipt = {
            "challenge": 0,
            "draw_ordinal": draw_ordinal,
            "requested_bytes": rule.draw_bytes,
            "namespace": model.canonical_value_json(namespace),
            "pre_state": model.canonical_value_json(pre_state),
            "post_state": model.canonical_value_json(post_state),
            "output": model.canonical_value_json(output),
            "accepted": accepted_value.datum,
        }
        draws.append(receipt)
        transitions.append({"kind": "Squeezed", "draw": receipt})
        state = post_state
        if accepted_value.datum:
            decoded = model.evaluate(rule.decode, (output,))
            return state, decoded, draws, (prefix_count, prefix_state)
    return state, None, draws, (prefix_count, prefix_state)


def _occurrence(occurrence: int, active: bool, outputs: tuple[Any, ...]) -> dict[str, Any]:
    return {
        "occurrence": occurrence,
        "status": "Active" if active else "Inactive",
        "outputs": [model.canonical_value_json(value) for value in outputs],
    }


def _failure_payload(subject: model.Subject) -> Any:
    failure = subject.construction.sampling_exhausted_failure
    return k1.admit_value(
        failure.payload_type,
        _record(k1.Nat(0), k1.Nat(model.MAXIMUM_DRAWS)),
    )


def execute(subject: model.Subject, case: RunCase) -> ExecutionResult:
    state = subject.construction.initial_state
    transitions: list[dict[str, Any]] = []
    prefix: list[str] = []
    for frame in (
        _core_header(subject),
        _construction_header(subject),
        _application_header(subject),
        _scope_opened(),
        _public_binding(case.statement),
    ):
        state = _absorb(subject, state, frame, transitions, prefix)

    occurrence_receipts: list[dict[str, Any]] = []
    commitment = k1.admit_value(model.Z3, k1.Nat(case.commitment))
    state = _absorb(
        subject,
        state,
        _prover_message(subject, 0, 0, case.commitment),
        transitions,
        prefix,
    )
    occurrence_receipts.append(_occurrence(0, True, (commitment,)))

    transcript_prefix = tuple(prefix)
    state, challenge, draws, frozen_prefix = _draw(subject, state, transitions)
    prefix_count, prefix_state = frozen_prefix
    invocation = model.invocation_id(subject, case.statement)
    if challenge is None:
        payload = _failure_payload(subject)
        sampling_receipt = {
            "challenge": 0,
            "prefix_receipt_count": prefix_count,
            "prefix_state": model.canonical_value_json(prefix_state),
            "draws": draws,
            "final_state": model.canonical_value_json(state),
        }
        record = {
            "variant": "InterpretationFailure",
            "record": {
                "protocol_id": model.identifier_text(subject.fs_protocol.identifier),
                "invocation_id": model.identifier_text(invocation),
                "occurrence_prefix": occurrence_receipts,
                "challenge_receipts": [],
                "failure": {
                    "failure_type": k1.encode_datum(
                        k1.semantic_failure_type_datum(
                            subject.construction.sampling_exhausted_failure
                        )
                    ).hex(),
                    "payload": model.canonical_value_json(payload),
                },
                "interpretation_receipt": {
                    "kind": "FiatShamirSamplingFailure",
                    "construction": model.identifier_text(
                        subject.construction.identifier
                    ),
                    "receipt": sampling_receipt,
                },
            },
        }
        return ExecutionResult(
            case,
            "InterpretationFailed",
            record,
            transcript_prefix,
            tuple(transitions),
            {"kind": "exhaustion", "draws": len(draws)},
        )

    occurrence_receipts.append(_occurrence(1, True, (challenge,)))
    challenge_receipt = {
        "interpretation": "FiatShamir",
        "receipt": {
            "challenge": 0,
            "prefix_receipt_count": prefix_count,
            "prefix_state": model.canonical_value_json(prefix_state),
            "draws": draws,
            "accepted_value": model.canonical_value_json(challenge),
            "post_state": model.canonical_value_json(state),
        },
    }

    challenge_number = challenge.datum.value
    if case.source == "honest":
        assert case.witness is not None and case.nonce is not None
        response_number = (case.nonce + challenge_number * case.witness) % 3
    else:
        assert case.response is not None
        response_number = case.response
    response = k1.admit_value(model.Z3, k1.Nat(response_number))
    state = _absorb(
        subject,
        state,
        _prover_message(subject, 2, 1, response_number),
        transitions,
        prefix,
    )
    occurrence_receipts.append(_occurrence(2, True, (response,)))

    statement = k1.admit_value(model.Z3, k1.Nat(case.statement))
    check = model.evaluate(
        model.AlgorithmUse(
            subject.fixture.schnorr_algorithm, model.EVALUATION_CONTRACT
        ),
        (statement, commitment, challenge, response),
    )
    occurrence_receipts.append(_occurrence(3, True, (check,)))

    active_accept = bool(check.datum)
    state = _absorb(
        subject,
        state,
        _guard_outcome(4, active_accept),
        transitions,
        prefix,
    )
    occurrence_receipts.append(_occurrence(4, active_accept, ()))
    if active_accept:
        terminal = 0
        lane = "Accepted"
    else:
        occurrence_receipts.append(_occurrence(5, True, ()))
        terminal = 1
        lane = "Rejected"

    record = {
        "variant": "TerminalCompletion",
        "record": {
            "protocol_id": model.identifier_text(subject.fs_protocol.identifier),
            "invocation_id": model.identifier_text(invocation),
            "occurrence_receipts": occurrence_receipts,
            "challenge_receipts": [challenge_receipt],
            "oracle_receipts": [],
            "terminal": terminal,
            "terminal_public_outputs": [],
        },
    }
    return ExecutionResult(
        case,
        lane,
        record,
        transcript_prefix,
        tuple(transitions),
        {"kind": "value", "value": challenge_number, "draws": len(draws)},
    )


def record_digest(record: dict[str, Any]) -> str:
    import json

    body = json.dumps(
        record, sort_keys=True, separators=(",", ":"), ensure_ascii=True
    ).encode("ascii")
    return hashlib.sha256(body).hexdigest()
