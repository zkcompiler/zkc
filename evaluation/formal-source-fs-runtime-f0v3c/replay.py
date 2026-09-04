#!/usr/bin/env python3
"""Second path: independently reconstruct and exhaust one completed record."""

from __future__ import annotations

from typing import Any

import model


k1 = model.k1
target = model.target


class ReplayMismatch(ValueError):
    """The supplied completed record is not exactly the independently derived one."""


def _correlation_body(correlation: Any) -> Any:
    if not hasattr(correlation, "prior_members"):
        return _v(0)
    return _v(
        1,
        _r(
            _declaration(correlation.group),
            k1.Nat(correlation.index),
            _s(tuple(k1.Nat(item) for item in correlation.prior_members)),
        ),
    )


def challenge_namespace(
    construction: Any,
    core: Any,
    challenge_ref: int,
    draw_ordinal: int,
) -> Any:
    """Independently reconstruct the canonical namespace used by replay."""

    challenge = core.challenges[challenge_ref]
    path: list[int] = []
    current: int | None = challenge.scope
    while current is not None:
        path.append(current)
        current = core.scopes[current].parent
    octets = k1.encode_datum(
        _r(
            k1.BytesValue(construction.identifier.internal_reference()),
            k1.BytesValue(construction.core_id.internal_reference()),
            _s(tuple(k1.Nat(item) for item in reversed(path))),
            k1.Nat(challenge_ref),
            _declaration(challenge.domain),
            k1.value_type_datum(challenge.value_type),
            _correlation_body(challenge.correlation),
            k1.Nat(draw_ordinal),
        )
    )
    return k1.admit_value(
        construction.transcript_bytes_type, k1.BytesValue(octets)
    )


def derive_challenge(
    construction: Any,
    core: Any,
    challenge_ref: int,
    state: Any,
    public_condition_values: tuple[Any, ...],
    prior_member_values: tuple[Any, ...],
    transitions: list[dict[str, Any]],
) -> tuple[Any, Any | None, tuple[dict[str, Any], ...], int, Any]:
    """Independent replay implementation of one heterogeneous rule."""

    matching = tuple(
        rule for rule in construction.challenge_rules if rule.challenge == challenge_ref
    )
    if len(matching) != 1:
        raise ReplayMismatch("replay challenge lacks one exact rule")
    rule = matching[0]
    challenge = core.challenges[challenge_ref]
    if len(public_condition_values) != len(challenge.public_conditions):
        raise ReplayMismatch("replay condition arity differs")
    if len(prior_member_values) != len(
        tuple(getattr(challenge.correlation, "prior_members", ()))
    ):
        raise ReplayMismatch("replay prior-member arity differs")

    prefix_state = state
    prefix_count = len(transitions)
    draws: list[dict[str, Any]] = []
    requested = k1.admit_value(construction.natural_type, k1.Nat(rule.draw_bytes))
    for draw_ordinal in range(rule.maximum_draws):
        pre_state = state
        namespace = challenge_namespace(
            construction, core, challenge_ref, draw_ordinal
        )
        output = model.evaluate(
            construction.squeeze_bytes, (pre_state, namespace, requested)
        )
        if (
            type(output.datum) is not k1.BytesValue
            or len(output.datum.value) != rule.draw_bytes
        ):
            raise ReplayMismatch("independent squeeze violated the length law")
        post_state = model.evaluate(
            construction.advance_state,
            (pre_state, namespace, requested, output),
        )
        sampling_inputs = (
            output,
            *public_condition_values,
            *prior_member_values,
        )
        accepted = model.evaluate(rule.accept, sampling_inputs)
        if type(accepted.datum) is not bool:
            raise ReplayMismatch("independent acceptance was not Boolean")
        receipt = {
            "challenge": challenge_ref,
            "draw_ordinal": draw_ordinal,
            "requested_bytes": rule.draw_bytes,
            "namespace": model.canonical_value_json(namespace),
            "pre_state": model.canonical_value_json(pre_state),
            "post_state": model.canonical_value_json(post_state),
            "output": model.canonical_value_json(output),
            "accepted": accepted.datum,
        }
        draws.append(receipt)
        transitions.append({"kind": "Squeezed", "draw": receipt})
        state = post_state
        if accepted.datum:
            value = model.evaluate(rule.decode, sampling_inputs)
            return state, value, tuple(draws), prefix_count, prefix_state
    return state, None, tuple(draws), prefix_count, prefix_state


def _r(*values: Any) -> Any:
    return k1.DatumRecord(tuple(enumerate(values)))


def _v(case: int, payload: Any = k1.UNIT) -> Any:
    return k1.DatumVariant(case, payload)


def _s(values: tuple[Any, ...]) -> Any:
    return k1.DatumSeq(values)


def _declaration(reference: Any) -> Any:
    return _v(
        1,
        _r(
            k1.BytesValue(reference.module.internal_reference()),
            k1.Symbol(reference.declaration_kind),
            k1.Nat(reference.local_ordinal),
        ),
    )


def _admit_frame(label: str, tag: int, payload: Any) -> tuple[dict[str, str], Any]:
    octets = k1.encode_datum(_v(tag, payload))
    admitted = k1.admit_value(
        model.TRANSCRIPT_BYTES_TYPE, k1.BytesValue(octets)
    )
    return {"kind": label, "body": octets.hex()}, admitted


def _header_frames(subject: model.Subject, statement: int) -> tuple[tuple[dict[str, str], Any], ...]:
    statement_value = k1.admit_value(model.Z3, k1.Nat(statement))
    return (
        _admit_frame(
            "CoreHeader",
            0,
            k1.BytesValue(subject.construction.core_id.internal_reference()),
        ),
        _admit_frame(
            "ConstructionHeader",
            1,
            k1.BytesValue(subject.construction.identifier.internal_reference()),
        ),
        _admit_frame(
            "ApplicationDomainHeader",
            2,
            _declaration(subject.construction.application_domain),
        ),
        _admit_frame("ScopeOpened", 3, _s((k1.Nat(0),))),
        _admit_frame(
            "PublicBinding",
            4,
            _r(
                k1.Nat(0),
                _v(0),
                k1.value_type_datum(model.Z3),
                statement_value.datum,
            ),
        ),
    )


def _message_frame(
    subject: model.Subject, occurrence: int, channel: int, payload: int
) -> tuple[dict[str, str], Any]:
    value = k1.admit_value(model.Z3, k1.Nat(payload))
    channel_ref = target.ModuleDeclarationRef(
        subject.fixture.module.identity, "pir.message-channel", channel
    )
    return _admit_frame(
        "ProverMessage",
        6,
        _r(
            k1.Nat(occurrence),
            _declaration(channel_ref),
            k1.value_type_datum(model.Z3),
            value.datum,
        ),
    )


def _guard_frame(active: bool) -> tuple[dict[str, str], Any]:
    return _admit_frame("GuardOutcome", 5, _r(k1.Nat(4), active))


def _challenge_namespace(subject: model.Subject, ordinal: int) -> Any:
    challenge = subject.fixture.core_candidate.core.challenges[0]
    octets = k1.encode_datum(
        _r(
            k1.BytesValue(subject.construction.identifier.internal_reference()),
            k1.BytesValue(subject.construction.core_id.internal_reference()),
            _s((k1.Nat(0),)),
            k1.Nat(0),
            _declaration(challenge.domain),
            k1.value_type_datum(challenge.value_type),
            _v(0),
            k1.Nat(ordinal),
        )
    )
    return k1.admit_value(model.TRANSCRIPT_BYTES_TYPE, k1.BytesValue(octets))


def _absorption(
    subject: model.Subject,
    state: Any,
    framed: tuple[dict[str, str], Any],
    transitions: list[dict[str, Any]],
) -> Any:
    descriptor, encoded = framed
    next_state = model.evaluate(subject.construction.absorb, (state, encoded))
    transitions.append(
        {
            "kind": "Absorbed",
            "frame": descriptor,
            "pre_state": model.canonical_value_json(state),
            "post_state": model.canonical_value_json(next_state),
        }
    )
    return next_state


def _independent_draws(
    subject: model.Subject,
    state: Any,
    transitions: list[dict[str, Any]],
) -> tuple[Any, Any | None, list[dict[str, Any]], int, Any]:
    rule = subject.construction.challenge_rules[0]
    count_before = len(transitions)
    state_before = state
    draws: list[dict[str, Any]] = []
    count_value = k1.admit_value(model.NATURAL_TYPE, k1.Nat(rule.draw_bytes))
    for ordinal in range(rule.maximum_draws):
        before = state
        namespace = _challenge_namespace(subject, ordinal)
        output = model.evaluate(
            subject.construction.squeeze_bytes,
            (before, namespace, count_value),
        )
        if type(output.datum) is not k1.BytesValue or len(output.datum.value) != rule.draw_bytes:
            raise ReplayMismatch("independent squeeze violated the length law")
        after = model.evaluate(
            subject.construction.advance_state,
            (before, namespace, count_value, output),
        )
        accepted = model.evaluate(rule.accept, (output,))
        if type(accepted.datum) is not bool:
            raise ReplayMismatch("independent acceptance was not Boolean")
        receipt = {
            "challenge": 0,
            "draw_ordinal": ordinal,
            "requested_bytes": rule.draw_bytes,
            "namespace": model.canonical_value_json(namespace),
            "pre_state": model.canonical_value_json(before),
            "post_state": model.canonical_value_json(after),
            "output": model.canonical_value_json(output),
            "accepted": accepted.datum,
        }
        draws.append(receipt)
        transitions.append({"kind": "Squeezed", "draw": receipt})
        state = after
        if accepted.datum:
            return (
                state,
                model.evaluate(rule.decode, (output,)),
                draws,
                count_before,
                state_before,
            )
    return state, None, draws, count_before, state_before


def _occurrence(index: int, active: bool, outputs: tuple[Any, ...]) -> dict[str, Any]:
    return {
        "occurrence": index,
        "status": "Active" if active else "Inactive",
        "outputs": [model.canonical_value_json(value) for value in outputs],
    }


def _sampling_payload(subject: model.Subject) -> Any:
    failure = subject.construction.sampling_exhausted_failure
    return k1.admit_value(
        failure.payload_type,
        _r(k1.Nat(0), k1.Nat(subject.construction.challenge_rules[0].maximum_draws)),
    )


def _derive(subject: model.Subject, case: dict[str, Any]) -> tuple[str, dict[str, Any], tuple[dict[str, Any], ...]]:
    exact_case_keys = {
        "name",
        "source",
        "statement",
        "commitment",
        "response",
        "witness",
        "nonce",
    }
    if type(case) is not dict or set(case) != exact_case_keys:
        raise ReplayMismatch("replay case has missing or surplus fields")
    state = subject.construction.initial_state
    transitions: list[dict[str, Any]] = []
    for frame in _header_frames(subject, case["statement"]):
        state = _absorption(subject, state, frame, transitions)

    commitment = k1.admit_value(model.Z3, k1.Nat(case["commitment"]))
    state = _absorption(
        subject,
        state,
        _message_frame(subject, 0, 0, case["commitment"]),
        transitions,
    )
    occurrences = [_occurrence(0, True, (commitment,))]
    state, challenge, draws, prefix_count, prefix_state = _independent_draws(
        subject, state, transitions
    )
    invocation = model.invocation_id(subject, case["statement"])
    if challenge is None:
        payload = _sampling_payload(subject)
        failure_record = {
            "variant": "InterpretationFailure",
            "record": {
                "protocol_id": model.identifier_text(subject.fs_protocol.identifier),
                "invocation_id": model.identifier_text(invocation),
                "occurrence_prefix": occurrences,
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
                    "receipt": {
                        "challenge": 0,
                        "prefix_receipt_count": prefix_count,
                        "prefix_state": model.canonical_value_json(prefix_state),
                        "draws": draws,
                        "final_state": model.canonical_value_json(state),
                    },
                },
            },
        }
        return "InterpretationFailed", failure_record, tuple(transitions)

    occurrences.append(_occurrence(1, True, (challenge,)))
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
    if case["source"] == "honest":
        if case["response"] is not None or case["witness"] is None or case["nonce"] is None:
            raise ReplayMismatch("honest replay case has inconsistent private inputs")
        response_number = (
            case["nonce"] + challenge.datum.value * case["witness"]
        ) % 3
    elif case["source"] == "verifier-input":
        if case["response"] is None or case["witness"] is not None or case["nonce"] is not None:
            raise ReplayMismatch("verifier replay case has inconsistent inputs")
        response_number = case["response"]
    else:
        raise ReplayMismatch("replay case has an unknown source")

    response = k1.admit_value(model.Z3, k1.Nat(response_number))
    state = _absorption(
        subject,
        state,
        _message_frame(subject, 2, 1, response_number),
        transitions,
    )
    occurrences.append(_occurrence(2, True, (response,)))
    statement = k1.admit_value(model.Z3, k1.Nat(case["statement"]))
    check = model.evaluate(
        model.AlgorithmUse(
            subject.fixture.schnorr_algorithm, model.EVALUATION_CONTRACT
        ),
        (statement, commitment, challenge, response),
    )
    occurrences.append(_occurrence(3, True, (check,)))
    accept_terminal = bool(check.datum)
    state = _absorption(subject, state, _guard_frame(accept_terminal), transitions)
    occurrences.append(_occurrence(4, accept_terminal, ()))
    if accept_terminal:
        lane, terminal = "Accepted", 0
    else:
        occurrences.append(_occurrence(5, True, ()))
        lane, terminal = "Rejected", 1
    terminal_record = {
        "variant": "TerminalCompletion",
        "record": {
            "protocol_id": model.identifier_text(subject.fs_protocol.identifier),
            "invocation_id": model.identifier_text(invocation),
            "occurrence_receipts": occurrences,
            "challenge_receipts": [challenge_receipt],
            "oracle_receipts": [],
            "terminal": terminal,
            "terminal_public_outputs": [],
        },
    }
    return lane, terminal_record, tuple(transitions)


def replay(
    subject: model.Subject,
    case: dict[str, Any],
    supplied_record: dict[str, Any],
) -> tuple[str, tuple[dict[str, Any], ...]]:
    """Recompute and compare the closed record, including exact field sets."""

    lane, expected_record, transitions = _derive(subject, case)
    if type(supplied_record) is not dict or supplied_record != expected_record:
        raise ReplayMismatch("completed record variant or exact field set mismatched")
    return lane, transitions
