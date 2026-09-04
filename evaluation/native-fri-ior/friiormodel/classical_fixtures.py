"""Strict authored-input roles for the frozen exact classical FRI packet.

The public input and proof terms are intentionally retyped by the separately
coded public verifier.  This module owns only the operational replay policy
and the owner-local generation input; importing it does not make either one a
protocol-semantic authority.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any

from .classical import (
    DEGREE_BOUNDS,
    DEFAULT_CLASSICAL_LIMITS,
    GoldilocksElement,
)
from .terms import ModelFailure, OutcomeClass, ResourceLimits


def _malformed(code: str, detail: str) -> ModelFailure:
    return ModelFailure(
        OutcomeClass.MALFORMED,
        "classical-fixtures:formation",
        code,
        detail,
    )


def _object(value: object, keys: tuple[str, ...], *, code: str) -> dict[str, Any]:
    if type(value) is not dict or set(value) != set(keys):
        raise _malformed(code, "object members do not match the exact role schema")
    return value


def _integer(value: object, low: int, high: int, *, code: str) -> int:
    if type(value) is not int or not low <= value <= high:
        raise _malformed(code, "integer lies outside its exact canonical range")
    return value


def _hex(value: object, minimum: int, maximum: int, *, code: str) -> bytes:
    if (
        type(value) is not str
        or len(value) % 2
        or not 2 * minimum <= len(value) <= 2 * maximum
    ):
        raise _malformed(code, "byte string is not bounded canonical hexadecimal")
    try:
        decoded = bytes.fromhex(value)
    except ValueError as error:
        raise _malformed(code, "byte string is not hexadecimal") from error
    if decoded.hex() != value:
        raise _malformed(code, "byte string is not canonical lowercase hexadecimal")
    return decoded


@dataclass(frozen=True, slots=True)
class ClassicalOwnerGenerationInput:
    """Declassified toy values that occupy owner-only generation roles."""

    source_coefficients: tuple[GoldilocksElement, ...]
    salt_seed: bytes


def parse_classical_owner_generation(
    value: object,
) -> ClassicalOwnerGenerationInput:
    obj = _object(
        value,
        (
            "schema",
            "authority",
            "source_coefficients",
            "salt_seed",
            "disclosure",
            "nonclaims",
        ),
        code="FRI-IOR-CLASSICAL-FIXTURE-001",
    )
    disclosure = _object(
        obj["disclosure"],
        ("classification", "contains_real_secret"),
        code="FRI-IOR-CLASSICAL-FIXTURE-001",
    )
    if (
        obj["schema"] != "zkc.classical-fri.owner-generation-input.v1"
        or obj["authority"] != "owner-generation-input-not-public-report-input"
        or disclosure
        != {
            "classification": (
                "declassified-public-test-vector-populates-owner-only-roles"
            ),
            "contains_real_secret": False,
        }
        or obj["nonclaims"]
        != [
            "does-not-establish-confidentiality-or-secure-randomness",
            "deterministic-salt-derivation-is-test-generation-only",
        ]
    ):
        raise _malformed(
            "FRI-IOR-CLASSICAL-FIXTURE-001",
            "owner generation authority, disclosure, or nonclaims drifted",
        )
    raw_coefficients = obj["source_coefficients"]
    if type(raw_coefficients) is not list or len(raw_coefficients) != DEGREE_BOUNDS[0]:
        raise _malformed(
            "FRI-IOR-CLASSICAL-FIXTURE-002",
            "the owner source polynomial requires exactly eight coefficients",
        )
    coefficients = tuple(
        GoldilocksElement(
            _integer(
                coefficient,
                0,
                (1 << 64) - (1 << 32),
                code="FRI-IOR-CLASSICAL-FIXTURE-002",
            )
        )
        for coefficient in raw_coefficients
    )
    salt_seed = _hex(
        obj["salt_seed"],
        1,
        64,
        code="FRI-IOR-CLASSICAL-FIXTURE-003",
    )
    return ClassicalOwnerGenerationInput(coefficients, salt_seed)


def parse_classical_replay_policy(value: object) -> ResourceLimits:
    obj = _object(
        value,
        ("schema", "authority", "limits", "claims"),
        code="FRI-IOR-CLASSICAL-FIXTURE-010",
    )
    if (
        obj["schema"] != "zkc.classical-fri.public-replay-policy.v1"
        or obj["authority"] != "repository-frozen-report-local-operational-policy"
        or obj["claims"]
        != {
            "part_of_protocol_semantics": False,
            "proves_resource_optimality": False,
            "semantic_authority": False,
        }
    ):
        raise _malformed(
            "FRI-IOR-CLASSICAL-FIXTURE-010",
            "classical replay policy authority or claims drifted",
        )
    limits = _object(
        obj["limits"],
        tuple(ResourceLimits.__dataclass_fields__),
        code="FRI-IOR-CLASSICAL-FIXTURE-011",
    )
    formed = ResourceLimits(
        **{
            name: _integer(
                limits[name],
                0,
                1 << 20,
                code="FRI-IOR-CLASSICAL-FIXTURE-011",
            )
            for name in limits
        }
    )
    if formed != DEFAULT_CLASSICAL_LIMITS:
        raise _malformed(
            "FRI-IOR-CLASSICAL-FIXTURE-012",
            "the frozen exact-control limits differ from the reviewed policy",
        )
    return formed


__all__ = [
    "ClassicalOwnerGenerationInput",
    "parse_classical_owner_generation",
    "parse_classical_replay_policy",
]
