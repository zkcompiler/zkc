"""Deliberately wrong transition substitutions used as finite falsifiers.

Each substitution below changes one reviewed source law.  A killed mutation
means only that the frozen finite witness distinguishes that substitution from
the selected transition; it is not a completeness or security result.
"""

from __future__ import annotations

from .construction import TranscriptConstruction, decode_challenge, encode_message
from .execution import PreparedReplay, PublicInputs, project_instance
from .transition import (
    RATE,
    DuplexState,
    absorb,
    squeeze,
    start,
)


def _schedule(
    construction: TranscriptConstruction,
) -> tuple[tuple[object, ...], tuple[object, ...]]:
    messages = tuple(
        item for item in construction.core.schedule if item.kind == "ProverMessage"
    )
    challenges = tuple(
        item for item in construction.core.schedule if item.kind == "Challenge"
    )
    return messages, challenges


def _decoded_symbols(value: object) -> tuple[int, ...]:
    return value if type(value) is tuple else (value,)  # type: ignore[return-value]


def prefix_xof_challenges(
    construction: TranscriptConstruction,
    inputs: PublicInputs,
    proof: PreparedReplay,
) -> tuple[object, ...]:
    """Reset for every cumulative prefix instead of continuing duplex state."""

    prefix = list(proof.salt)
    oracle = construction.provider_semantics.forward_oracle()
    instance = project_instance(construction, inputs)
    messages, challenges = _schedule(construction)
    decoded: list[object] = []
    for value, message, codec, challenge, decoder in zip(
        proof.prover_messages,
        messages,
        construction.message_codecs,
        challenges,
        construction.challenge_decoders,
        strict=True,
    ):
        prefix.extend(encode_message(codec.codec, message.value_type, value))
        state = start(oracle, instance)
        state = absorb(oracle, state, tuple(prefix)).state
        output = squeeze(oracle, state, decoder.squeeze_length).output
        decoded.append(
            decode_challenge(decoder.decoder, challenge.value_type, output)
        )
    return tuple(decoded)


def salt_after_first_message_challenges(
    construction: TranscriptConstruction,
    inputs: PublicInputs,
    proof: PreparedReplay,
) -> tuple[object, ...]:
    """Place the salt after the first encoded prover message."""

    oracle = construction.provider_semantics.forward_oracle()
    state = start(oracle, project_instance(construction, inputs))
    messages, challenges = _schedule(construction)
    decoded: list[object] = []
    for index, (value, message, codec, challenge, decoder) in enumerate(
        zip(
            proof.prover_messages,
            messages,
            construction.message_codecs,
            challenges,
            construction.challenge_decoders,
            strict=True,
        )
    ):
        state = absorb(
            oracle,
            state,
            encode_message(codec.codec, message.value_type, value),
        ).state
        if index == 0:
            state = absorb(oracle, state, proof.salt).state
        squeezed = squeeze(oracle, state, decoder.squeeze_length)
        state = squeezed.state
        decoded.append(
            decode_challenge(decoder.decoder, challenge.value_type, squeezed.output)
        )
    return tuple(decoded)


def reabsorbed_challenge_schedule(
    construction: TranscriptConstruction,
    inputs: PublicInputs,
    proof: PreparedReplay,
) -> tuple[object, ...]:
    """Reabsorb each decoded challenge before processing the next message."""

    oracle = construction.provider_semantics.forward_oracle()
    state = start(oracle, project_instance(construction, inputs))
    state = absorb(oracle, state, proof.salt).state
    messages, challenges = _schedule(construction)
    decoded: list[object] = []
    for value, message, codec, challenge, decoder in zip(
        proof.prover_messages,
        messages,
        construction.message_codecs,
        challenges,
        construction.challenge_decoders,
        strict=True,
    ):
        state = absorb(
            oracle,
            state,
            encode_message(codec.codec, message.value_type, value),
        ).state
        squeezed = squeeze(oracle, state, decoder.squeeze_length)
        challenge_value = decode_challenge(
            decoder.decoder, challenge.value_type, squeezed.output
        )
        decoded.append(challenge_value)
        state = absorb(oracle, squeezed.state, _decoded_symbols(challenge_value)).state
    return tuple(decoded)


def omitted_final_verifier_squeeze(
    construction: TranscriptConstruction,
    inputs: PublicInputs,
    proof: PreparedReplay,
) -> tuple[object, ...]:
    """Execute all messages but omit the verifier's final challenge squeeze."""

    oracle = construction.provider_semantics.forward_oracle()
    state = start(oracle, project_instance(construction, inputs))
    state = absorb(oracle, state, proof.salt).state
    messages, challenges = _schedule(construction)
    decoded: list[object] = []
    for index, (value, message, codec, challenge, decoder) in enumerate(
        zip(
            proof.prover_messages,
            messages,
            construction.message_codecs,
            challenges,
            construction.challenge_decoders,
            strict=True,
        )
    ):
        state = absorb(
            oracle,
            state,
            encode_message(codec.codec, message.value_type, value),
        ).state
        if index == len(messages) - 1:
            break
        squeezed = squeeze(oracle, state, decoder.squeeze_length)
        state = squeezed.state
        decoded.append(
            decode_challenge(decoder.decoder, challenge.value_type, squeezed.output)
        )
    return tuple(decoded)


def transition_mutation_kills(
    construction: TranscriptConstruction,
    inputs: PublicInputs,
    proof: PreparedReplay,
    expected_challenges: tuple[object, ...],
) -> dict[str, bool]:
    """Run nine source-law substitutions against their finite witnesses."""

    oracle = construction.provider_semantics.forward_oracle()
    initial = start(oracle, project_instance(construction, inputs))
    after_salt = absorb(oracle, initial, proof.salt).state
    before_first_challenge = absorb(
        oracle,
        after_salt,
        encode_message(
            construction.message_codecs[0].codec,
            construction.core.schedule[0].value_type,
            proof.prover_messages[0],
        ),
    ).state
    partial = squeeze(oracle, before_first_challenge, 2).state

    correct_empty = absorb(oracle, partial, ()).state
    empty_as_identity = partial

    filled = absorb(oracle, initial, (1, 2, 3)).state
    eager_permutation = DuplexState(oracle.permutation(filled.cells), 0, RATE)

    correct_overwrite = absorb(oracle, partial, (4,)).state
    combined_cells = list(partial.cells)
    combined_cells[0] = (combined_cells[0] + 4) % 5
    combine_instead = DuplexState(tuple(combined_cells), 1, RATE)

    first = squeeze(oracle, before_first_challenge, 1)
    correct_continuation = squeeze(oracle, first.state, 3).output
    restarted_stream = squeeze(oracle, before_first_challenge, 3).output

    correct_after_full = absorb(oracle, filled, (4,)).state
    reset_squeeze_index = DuplexState(
        correct_after_full.cells,
        correct_after_full.absorb_index,
        0,
    )

    return {
        "EmptyAbsorbAsIdentity": correct_empty != empty_as_identity,
        "EagerPermutationAtFullRate": filled != eager_permutation,
        "CombineInsteadOfOverwrite": correct_overwrite != combine_instead,
        "RestartOutputStream": correct_continuation != restarted_stream,
        "ResetSqueezeIndexAfterAbsorbPermutation": (
            correct_after_full != reset_squeeze_index
        ),
        "PrefixXofSubstitution": (
            prefix_xof_challenges(construction, inputs, proof)
            != expected_challenges
        ),
        "SaltAfterFirstMessage": (
            salt_after_first_message_challenges(construction, inputs, proof)
            != expected_challenges
        ),
        "DecodedChallengeReabsorption": (
            reabsorbed_challenge_schedule(construction, inputs, proof)
            != expected_challenges
        ),
        "OmitFinalVerifierSqueeze": (
            omitted_final_verifier_squeeze(construction, inputs, proof)
            != expected_challenges
        ),
    }
