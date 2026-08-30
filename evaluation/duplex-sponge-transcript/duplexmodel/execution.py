"""Prepared public replay and bounded generation-prefix simulation."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any

from .construction import (
    TranscriptConstruction,
    challenge_domain,
    construction_id,
    core_id,
    decode_challenge,
    encode_message,
    protocol_id,
)
from .diagnostics import (
    InstanceBoundExceeded,
    MalformedInput,
    ReplayContextMismatch,
    DeterministicLimitExceeded,
)
from .independent import (
    independent_absorb,
    independent_squeeze,
    independent_start,
)
from .terms import exact_keys, exact_nat, semantic_id
from .transition import (
    DuplexState,
    absorb,
    squeeze,
    start,
    symbols,
)


PUBLIC_INPUT_SCHEMA = "zkc.duplex-sponge-transcript.public-inputs.v1"
PUBLIC_PROOF_SCHEMA = "zkc.duplex-sponge-transcript.public-proof.v1"


@dataclass(frozen=True)
class PublicInputs:
    statement: tuple[int, int]
    max_trace_events: int
    max_permutation_calls: int

    def semantic_term(self) -> dict[str, object]:
        return {"statement": list(self.statement)}


@dataclass(frozen=True)
class ReplayContext:
    core_id: str
    construction_id: str
    protocol_id: str
    invocation_id: str

    def to_term(self) -> dict[str, str]:
        return {
            "core_id": self.core_id,
            "construction_id": self.construction_id,
            "protocol_id": self.protocol_id,
            "invocation_id": self.invocation_id,
        }


@dataclass(frozen=True)
class PublicProof:
    salt: tuple[int, ...]
    prover_messages: tuple[object, ...]

    def to_term(self) -> dict[str, object]:
        return {
            "schema": PUBLIC_PROOF_SCHEMA,
            "salt": list(self.salt),
            "prover_messages": [
                list(value) if type(value) is tuple else value
                for value in self.prover_messages
            ],
        }


@dataclass(frozen=True)
class PreparedReplay:
    proof: PublicProof
    context: ReplayContext

    @property
    def salt(self) -> tuple[int, ...]:
        return self.proof.salt

    @property
    def prover_messages(self) -> tuple[object, ...]:
        return self.proof.prover_messages

    def to_term(self) -> dict[str, object]:
        """Return proof bytes only; derived replay context is not serialized."""

        return self.proof.to_term()


@dataclass(frozen=True)
class TraceEvent:
    kind: str
    occurrence: str
    state: DuplexState
    symbols: tuple[int, ...]
    permutation_calls: int

    def to_term(self) -> dict[str, object]:
        return {
            "kind": self.kind,
            "occurrence": self.occurrence,
            "state": self.state.to_term(),
            "symbols": list(self.symbols),
            "permutation_calls": self.permutation_calls,
        }


@dataclass(frozen=True)
class ExecutionRecord:
    replay_context: ReplayContext
    instance_bytes: bytes
    salt: tuple[int, ...]
    prover_messages: tuple[object, ...]
    challenges: tuple[object, ...]
    trace: tuple[TraceEvent, ...]
    total_permutation_calls: int

    def to_term(self) -> dict[str, object]:
        return {
            "replay_context": self.replay_context.to_term(),
            "instance_hex": self.instance_bytes.hex(),
            "salt": list(self.salt),
            "prover_messages": [
                list(value) if type(value) is tuple else value
                for value in self.prover_messages
            ],
            "challenges": [
                list(value) if type(value) is tuple else value
                for value in self.challenges
            ],
            "trace": [event.to_term() for event in self.trace],
            "total_permutation_calls": self.total_permutation_calls,
        }


def parse_public_inputs(value: Any) -> PublicInputs:
    obj = exact_keys(
        value,
        {"schema", "statement", "public_resource_limits", "non_claims"},
        where="public inputs",
    )
    if obj["schema"] != PUBLIC_INPUT_SCHEMA:
        raise MalformedInput("public-input schema differs")
    statement = exact_keys(obj["statement"], {"first", "second"}, where="Statement")
    first = exact_nat(statement["first"], maximum=255, where="Statement.first")
    second = exact_nat(statement["second"], maximum=255, where="Statement.second")
    limits = exact_keys(
        obj["public_resource_limits"],
        {"max_trace_events", "max_permutation_calls"},
        where="public resource limits",
    )
    max_trace_events = exact_nat(
        limits["max_trace_events"], maximum=256, where="max trace events"
    )
    max_permutation_calls = exact_nat(
        limits["max_permutation_calls"], maximum=256, where="max permutation calls"
    )
    if type(obj["non_claims"]) is not list or any(
        type(item) is not str for item in obj["non_claims"]
    ):
        raise MalformedInput("public nonclaims must be a string list")
    return PublicInputs((first, second), max_trace_events, max_permutation_calls)


def _normalize_message(value: Any) -> object:
    if value is None:
        return None
    if type(value) is not list:
        raise MalformedInput("serialized prover message must be an array or null")
    return symbols(value, where="serialized prover message")


def expected_replay_context(
    construction: TranscriptConstruction,
    inputs: PublicInputs,
) -> ReplayContext:
    core = core_id(construction.core)
    construction_subject = construction_id(construction)
    protocol = protocol_id(construction, "DuplexSponge")
    invocation = semantic_id(
        "pir.protocol-invocation",
        {
            "protocol_id": protocol,
            "statement": inputs.semantic_term(),
        },
    )
    return ReplayContext(core, construction_subject, protocol, invocation)


def parse_public_proof(
    value: Any,
    construction: TranscriptConstruction,
    inputs: PublicInputs,
) -> PreparedReplay:
    obj = exact_keys(value, {"schema", "salt", "prover_messages"}, where="public proof")
    if obj["schema"] != PUBLIC_PROOF_SCHEMA:
        raise MalformedInput("public-proof schema differs")
    salt = symbols(obj["salt"], where="proof salt")
    if len(salt) != construction.salt_length:
        raise MalformedInput("proof salt has the wrong exact length")
    if type(obj["prover_messages"]) is not list:
        raise MalformedInput("proof messages must be an ordered list")
    messages = tuple(_normalize_message(item) for item in obj["prover_messages"])
    declarations = tuple(
        item for item in construction.core.schedule if item.kind == "ProverMessage"
    )
    if len(messages) != len(declarations):
        raise MalformedInput("proof must carry exactly every prover-message occurrence")
    for value, declaration, codec in zip(
        messages, declarations, construction.message_codecs, strict=True
    ):
        # Encoding performs the exact type check.
        encode_message(codec.codec, declaration.value_type, value)
    return PreparedReplay(
        PublicProof(salt, messages),
        expected_replay_context(construction, inputs),
    )


def project_instance(
    construction: TranscriptConstruction,
    inputs: PublicInputs,
) -> bytes:
    values = {"first": inputs.statement[0], "second": inputs.statement[1]}
    projected = bytes(values[field] for field in construction.instance_codec.fields)
    if len(projected) * 8 > construction.instance_bit_bound:
        raise InstanceBoundExceeded(
            "projected runtime instance exceeds construction instance_bit_bound"
        )
    return projected


def _require_replay_context(
    construction: TranscriptConstruction,
    inputs: PublicInputs,
    prepared: PreparedReplay,
) -> None:
    if prepared.context != expected_replay_context(construction, inputs):
        raise ReplayContextMismatch(
            "replay was not prepared for this Core, construction, Protocol, and Statement"
        )


def _enforce_resource_limits(
    inputs: PublicInputs,
    trace_events: int,
    permutation_calls: int,
) -> None:
    if trace_events > inputs.max_trace_events:
        raise DeterministicLimitExceeded(
            "public trace-event validation limit exhausted"
        )
    if permutation_calls > inputs.max_permutation_calls:
        raise DeterministicLimitExceeded(
            "public permutation-call validation limit exhausted"
        )


def replay(
    construction: TranscriptConstruction,
    inputs: PublicInputs,
    prepared: PreparedReplay,
) -> ExecutionRecord:
    _require_replay_context(construction, inputs, prepared)
    proof = prepared.proof
    instance = project_instance(construction, inputs)
    oracle = construction.provider_semantics.forward_oracle()
    state = start(oracle, instance)
    trace: list[TraceEvent] = [TraceEvent("Start", "runtime-instance", state, (), 0)]
    total_calls = 0
    absorbed_salt = absorb(oracle, state, proof.salt)
    state = absorbed_salt.state
    total_calls += absorbed_salt.permutation_calls
    trace.append(
        TraceEvent("AbsorbSalt", "proof-salt", state, proof.salt, absorbed_salt.permutation_calls)
    )
    message_occurrences = tuple(
        item for item in construction.core.schedule if item.kind == "ProverMessage"
    )
    challenge_occurrences = tuple(
        item for item in construction.core.schedule if item.kind == "Challenge"
    )
    challenges: list[object] = []
    for message, message_occurrence, message_codec, challenge_occurrence, challenge_decoder in zip(
        proof.prover_messages,
        message_occurrences,
        construction.message_codecs,
        challenge_occurrences,
        construction.challenge_decoders,
        strict=True,
    ):
        encoded = encode_message(
            message_codec.codec, message_occurrence.value_type, message
        )
        absorbed = absorb(oracle, state, encoded)
        state = absorbed.state
        total_calls += absorbed.permutation_calls
        trace.append(
            TraceEvent(
                "AbsorbMessage",
                message_occurrence.name,
                state,
                encoded,
                absorbed.permutation_calls,
            )
        )
        squeezed = squeeze(
            oracle, state, challenge_decoder.squeeze_length
        )
        state = squeezed.state
        total_calls += squeezed.permutation_calls
        challenge = decode_challenge(
            challenge_decoder.decoder,
            challenge_occurrence.value_type,
            squeezed.output,
        )
        if challenge not in challenge_domain(challenge_occurrence.value_type):
            raise MalformedInput("decoded challenge left its declared type")
        challenges.append(challenge)
        trace.append(
            TraceEvent(
                "SqueezeChallenge",
                challenge_occurrence.name,
                state,
                squeezed.output,
                squeezed.permutation_calls,
            )
        )
    _enforce_resource_limits(inputs, len(trace), total_calls)
    return ExecutionRecord(
        prepared.context,
        instance,
        proof.salt,
        proof.prover_messages,
        tuple(challenges),
        tuple(trace),
        total_calls,
    )


def independent_replay(
    construction: TranscriptConstruction,
    inputs: PublicInputs,
    prepared: PreparedReplay,
) -> ExecutionRecord:
    _require_replay_context(construction, inputs, prepared)
    proof = prepared.proof
    instance = project_instance(construction, inputs)
    provider = construction.provider_semantics
    raw_state = independent_start(
        instance,
        provider.start_matrix,
        provider.start_offset,
    )
    trace: list[TraceEvent] = [
        TraceEvent("Start", "runtime-instance", DuplexState(*raw_state), (), 0)
    ]
    raw_state, calls = independent_absorb(
        raw_state,
        proof.salt,
        provider.permutation_matrix,
        provider.permutation_offset,
    )
    total_calls = calls
    trace.append(
        TraceEvent("AbsorbSalt", "proof-salt", DuplexState(*raw_state), proof.salt, calls)
    )
    message_occurrences = tuple(
        item for item in construction.core.schedule if item.kind == "ProverMessage"
    )
    challenge_occurrences = tuple(
        item for item in construction.core.schedule if item.kind == "Challenge"
    )
    challenges: list[object] = []
    for message, message_occurrence, message_codec, challenge_occurrence, challenge_decoder in zip(
        proof.prover_messages,
        message_occurrences,
        construction.message_codecs,
        challenge_occurrences,
        construction.challenge_decoders,
        strict=True,
    ):
        encoded = encode_message(
            message_codec.codec, message_occurrence.value_type, message
        )
        raw_state, calls = independent_absorb(
            raw_state,
            encoded,
            provider.permutation_matrix,
            provider.permutation_offset,
        )
        total_calls += calls
        trace.append(
            TraceEvent(
                "AbsorbMessage",
                message_occurrence.name,
                DuplexState(*raw_state),
                encoded,
                calls,
            )
        )
        raw_state, output, calls = independent_squeeze(
            raw_state,
            challenge_decoder.squeeze_length,
            provider.permutation_matrix,
            provider.permutation_offset,
        )
        total_calls += calls
        challenge = decode_challenge(
            challenge_decoder.decoder, challenge_occurrence.value_type, output
        )
        challenges.append(challenge)
        trace.append(
            TraceEvent(
                "SqueezeChallenge",
                challenge_occurrence.name,
                DuplexState(*raw_state),
                output,
                calls,
            )
        )
    _enforce_resource_limits(inputs, len(trace), total_calls)
    return ExecutionRecord(
        prepared.context,
        instance,
        proof.salt,
        proof.prover_messages,
        tuple(challenges),
        tuple(trace),
        total_calls,
    )


def derive_generation_prefix_challenges(
    construction: TranscriptConstruction,
    inputs: PublicInputs,
    prepared: PreparedReplay,
) -> tuple[object, ...]:
    """Simulate the frozen prefix selected by the generation-support fixture.

    This bounded helper omits the last squeeze by fixture policy.  It does not
    establish challenge necessity or implement a prover.
    """

    _require_replay_context(construction, inputs, prepared)
    proof = prepared.proof
    instance = project_instance(construction, inputs)
    oracle = construction.provider_semantics.forward_oracle()
    state = start(oracle, instance)
    state = absorb(oracle, state, proof.salt).state
    messages = tuple(
        item for item in construction.core.schedule if item.kind == "ProverMessage"
    )
    challenges = tuple(
        item for item in construction.core.schedule if item.kind == "Challenge"
    )
    derived: list[object] = []
    for index, (value, message, codec) in enumerate(
        zip(proof.prover_messages, messages, construction.message_codecs, strict=True)
    ):
        if index == len(messages) - 1:
            break
        encoded = encode_message(codec.codec, message.value_type, value)
        state = absorb(oracle, state, encoded).state
        decoder = construction.challenge_decoders[index]
        squeezed = squeeze(oracle, state, decoder.squeeze_length)
        state = squeezed.state
        derived.append(
            decode_challenge(decoder.decoder, challenges[index].value_type, squeezed.output)
        )
    return tuple(derived)
