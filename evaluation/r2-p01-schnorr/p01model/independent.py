"""Independent byte reconstruction for the frozen P01 FS v3 support point.

This module intentionally does not import P01's transcript framing, duplex,
query, sampling, or codec helpers.  It consumes the public construction shape
and finite integer parameters, reconstructs the bytes with a second small
implementation, and returns a comparison artifact.  Agreement is useful
falsification evidence; it is not an independent cryptographic implementation
or a Fiat--Shamir theorem.
"""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
from typing import Any


RATE_BYTES = 168
SESSION_DOMAIN = b"irtf-cfrg-fiat-shamir/session-id"
EXPECTED_MODEL = "StrongFiatShamirTranscriptConstruction.v3"
EXPECTED_ATOMS = ("statement:y", "message:commitment")


class IndependentReconstructionError(ValueError):
    """The public construction or input is outside this frozen checker."""


def _frame(label: str, payload: bytes) -> bytes:
    try:
        label_bytes = label.encode("ascii")
    except (AttributeError, UnicodeEncodeError) as error:
        raise IndependentReconstructionError("frame label is not ASCII") from error
    if not isinstance(payload, bytes):
        raise IndependentReconstructionError("frame payload is not bytes")
    if not label_bytes or len(label_bytes) >= 1 << 16 or len(payload) >= 1 << 32:
        raise IndependentReconstructionError("frame is outside the finite ABI")
    return (
        len(label_bytes).to_bytes(2, "big")
        + label_bytes
        + len(payload).to_bytes(4, "big")
        + payload
    )


def _init(seed: bytes) -> bytes:
    if not isinstance(seed, bytes) or len(seed) != 32:
        raise IndependentReconstructionError("duplex seed must be 32 bytes")
    return seed + bytes(RATE_BYTES - len(seed))


def _squeeze(absorbed: bytes, count: int) -> bytes:
    if not isinstance(absorbed, bytes) or count < 0:
        raise IndependentReconstructionError("duplex squeeze input is malformed")
    return hashlib.shake_128(absorbed).digest(count)


def _fixed_width(value: int, modulus: int) -> bytes:
    if (
        not isinstance(value, int)
        or isinstance(value, bool)
        or not isinstance(modulus, int)
        or isinstance(modulus, bool)
        or modulus <= 2
        or value <= 0
        or value >= modulus
    ):
        raise IndependentReconstructionError("group value is outside the finite field")
    return value.to_bytes(max(1, (modulus.bit_length() + 7) // 8), "big")


@dataclass(frozen=True)
class IndependentFSReconstruction:
    query: bytes
    challenge_byte: int
    challenge: int
    statement_frame: bytes
    commitment_frame: bytes

    @property
    def query_sha256(self) -> str:
        return hashlib.sha256(self.query).hexdigest()

    def public_term(self) -> dict[str, Any]:
        return {
            "law": "p01.independent-fs-v3-byte-reconstruction.v1",
            "query_hex": self.query.hex(),
            "query_byte_length": len(self.query),
            "query_sha256": self.query_sha256,
            "challenge_byte": self.challenge_byte,
            "challenge": self.challenge,
            "statement_frame_hex": self.statement_frame.hex(),
            "commitment_frame_hex": self.commitment_frame.hex(),
            "non_claim": "byte-level agreement only; no ROM, QROM, or security theorem",
        }


def reconstruct_fs_v3(
    construction: Any,
    *,
    p: int,
    challenge_size: int,
    application_context: str,
    statement: int,
    commitment: int,
) -> IndependentFSReconstruction:
    """Reconstruct the exact P01 v3 query without P01 transcript helpers."""

    if (
        getattr(construction, "model", None) != EXPECTED_MODEL
        or getattr(construction, "framing", None) != "typed-length-delimited.v1"
        or getattr(construction, "sampler", None)
        != "shake128-one-byte-mod-8.v1"
        or getattr(construction, "challenge_namespace", None)
        != "zkc/p01/schnorr/challenge/c/v2"
        or challenge_size != 8
    ):
        raise IndependentReconstructionError("construction is not exact P01 FS v3")
    try:
        construction_id = construction.identity.encode("ascii")
        context_contract_id = construction.runtime_context.identity.encode("ascii")
        context_bytes = application_context.encode("utf-8")
        atoms = tuple(construction.atoms)
    except (AttributeError, UnicodeEncodeError, TypeError) as error:
        raise IndependentReconstructionError("construction identities are malformed") from error
    if tuple(getattr(atom, "occurrence", None) for atom in atoms) != EXPECTED_ATOMS:
        raise IndependentReconstructionError("Statement/commitment prefix is not exact")

    tag = b"".join(
        (
            _frame("construction-id", construction_id),
            _frame("runtime-context-contract-id", context_contract_id),
            _frame("runtime-context-value", context_bytes),
        )
    )
    session_absorbed = _init(SESSION_DOMAIN) + tag
    session_id = _squeeze(session_absorbed, 32)

    statement_bytes = _fixed_width(statement, p)
    commitment_bytes = _fixed_width(commitment, p)
    frames: list[bytes] = []
    for atom, payload in zip(atoms, (statement_bytes, commitment_bytes), strict=True):
        try:
            label = (
                f"{atom.source_kind}:{atom.occurrence}:"
                f"{atom.value_domain_id}:{atom.codec}"
            )
        except AttributeError as error:
            raise IndependentReconstructionError("typed atom is malformed") from error
        frames.append(_frame(label, payload))

    query = _init(session_id) + b"".join(frames)
    challenge_byte = _squeeze(query, 1)[0]
    return IndependentFSReconstruction(
        query=query,
        challenge_byte=challenge_byte,
        challenge=challenge_byte % challenge_size,
        statement_frame=frames[0],
        commitment_frame=frames[1],
    )


__all__ = [
    "IndependentFSReconstruction",
    "IndependentReconstructionError",
    "reconstruct_fs_v3",
]
