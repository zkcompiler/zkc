"""Independent arithmetic oracle for the selected finite Schnorr cover.

This file deliberately imports neither the Analysis reference model nor the
portable-arithmetic implementation.  It reconstructs the representative set,
Foundation canonical bytes used by the stream receipt, and extractor outputs
from elementary integer arithmetic.  Agreement is bounded falsification
evidence, not a proof of the portable evaluator or Foundation encoder.
"""

from __future__ import annotations

from hashlib import sha256


GROUP_MODULUS = 23
SUBGROUP_ORDER = 11
GENERATOR = 2
STATEMENT = 8
CHALLENGE_COUNT = 8

Transcript = tuple[int, int, int, int]
Representative = tuple[Transcript, Transcript]


def _u64(value: int) -> bytes:
    if type(value) is not int or not 0 <= value < 1 << 64:
        raise ValueError("value is outside the unsigned 64-bit carrier")
    return value.to_bytes(8, "big")


def _frame(body: bytes) -> bytes:
    return _u64(len(body)) + body


def _nat(value: int) -> bytes:
    if type(value) is not int or value < 0:
        raise ValueError("natural must be nonnegative")
    width = max(1, (value.bit_length() + 7) // 8)
    return b"\x03" + _frame(value.to_bytes(width, "big"))


def _record(fields: tuple[tuple[int, bytes], ...]) -> bytes:
    if tuple(ordinal for ordinal, _ in fields) != tuple(
        sorted({ordinal for ordinal, _ in fields})
    ):
        raise ValueError("record ordinals are not canonical")
    return b"\x08" + _u64(len(fields)) + b"".join(
        _u64(ordinal) + _frame(child) for ordinal, child in fields
    )


def encode_representative(value: Representative) -> bytes:
    def transcript(item: Transcript) -> bytes:
        if type(item) is not tuple or len(item) != 4:
            raise ValueError("transcript has another shape")
        return _record(tuple((ordinal, _nat(leaf)) for ordinal, leaf in enumerate(item)))

    first, second = value
    return _record(((0, transcript(first)), (1, transcript(second))))


def verifier_accepts(transcript: Transcript) -> bool:
    statement, commitment, challenge, response = transcript
    return (
        statement == STATEMENT
        and 0 <= challenge < CHALLENGE_COUNT
        and pow(GENERATOR, response, GROUP_MODULUS)
        == (
            commitment
            * pow(statement, challenge, GROUP_MODULUS)
        )
        % GROUP_MODULUS
    )


def representative_stream() -> tuple[Representative, ...]:
    commitments = tuple(
        value
        for value in range(GROUP_MODULUS)
        if any(
            pow(GENERATOR, exponent, GROUP_MODULUS) == value
            for exponent in range(SUBGROUP_ORDER)
        )
    )
    result: list[Representative] = []
    for commitment in commitments:
        for first_challenge in range(CHALLENGE_COUNT):
            for second_challenge in range(first_challenge + 1, CHALLENGE_COUNT):
                responses = []
                for challenge in (first_challenge, second_challenge):
                    accepted = tuple(
                        response
                        for response in range(SUBGROUP_ORDER)
                        if verifier_accepts(
                            (STATEMENT, commitment, challenge, response)
                        )
                    )
                    if len(accepted) != 1:
                        raise AssertionError(
                            "one selected residue has no unique response"
                        )
                    responses.append(accepted[0])
                result.append(
                    (
                        (
                            STATEMENT,
                            commitment,
                            first_challenge,
                            responses[0],
                        ),
                        (
                            STATEMENT,
                            commitment,
                            second_challenge,
                            responses[1],
                        ),
                    )
                )
    encoded = tuple(encode_representative(item) for item in result)
    if len(result) != 308 or encoded != tuple(sorted(set(encoded))):
        raise AssertionError("independent representative stream is not canonical")
    return tuple(result)


def extract(pair: Representative) -> int:
    first, second = pair
    denominator = (first[2] - second[2]) % SUBGROUP_ORDER
    return (
        (first[3] - second[3])
        * pow(denominator, -1, SUBGROUP_ORDER)
    ) % SUBGROUP_ORDER


def ordered_stream_digest(values: tuple[Representative, ...]) -> bytes:
    digest = sha256()
    for value in values:
        body = encode_representative(value)
        digest.update(_u64(len(body)))
        digest.update(body)
    return digest.digest()


def expected_result() -> tuple[int, bytes, tuple[int, ...]]:
    values = representative_stream()
    return len(values), ordered_stream_digest(values), tuple(extract(item) for item in values)


if __name__ == "__main__":
    count, digest, outputs = expected_result()
    print(f"representatives={count}")
    print(f"stream_sha256={digest.hex()}")
    print(f"extractor_outputs={sorted(set(outputs))}")
