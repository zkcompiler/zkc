"""Closed public carriers for the committed finite FRI verifier.

The carriers contain only public input and proof material.  In particular,
they have no field for a native trace, complete logical oracle, source
polynomial, commitment-construction salts beyond opened leaves, or private
generation data.  Query positions are absent from the proof: the verifier
derives them from the raw Fiat--Shamir inputs and then checks the four
occurrence selectors against that result.
"""

from __future__ import annotations

from dataclasses import dataclass
from types import MappingProxyType
from typing import Any

from .commitment import MerkleCap, PairOpening
from .field import Fp2, canonical_polynomial
from .profile import EXACT_PROFILE, FriIorProfile
from .terms import (
    SemanticId,
    encode_term,
    malformed,
    semantic_id,
)
from .transcript import (
    MAX_GRINDING_NONCE,
    TranscriptConstructionPlan,
)


MAX_OPENING_TABLE_ENTRIES = 2 * EXACT_PROFILE.ordered_query_count


def _freeze_closed_term(value: Any) -> Any:
    """Copy one closed finite term into an immutable host representation."""

    if value is None or type(value) in (bool, int, str, bytes):
        frozen = value
    elif type(value) in (tuple, list):
        frozen = tuple(_freeze_closed_term(item) for item in value)
    elif type(value) in (dict, MappingProxyType):
        if not all(isinstance(key, str) for key in value):
            raise malformed(
                "proof:public-input-formation",
                "FRI-IOR-PROOF-001",
                "closed public maps require text keys",
            )
        frozen = MappingProxyType(
            {
                key: _freeze_closed_term(value[key])
                for key in sorted(value, key=lambda item: item.encode("utf-8"))
            }
        )
    else:
        raise malformed(
            "proof:public-input-formation",
            "FRI-IOR-PROOF-002",
            "public statement and context values must be closed finite terms",
        )
    # Reuse the regime's depth, node, and byte bounds at the carrier boundary.
    encode_term(frozen)
    return frozen


def _term_copy(value: Any) -> Any:
    """Return an ordinary closed term without returning mutable internal state."""

    if type(value) in (dict, MappingProxyType):
        return {key: _term_copy(item) for key, item in value.items()}
    if isinstance(value, tuple):
        return [_term_copy(item) for item in value]
    return value


@dataclass(frozen=True, slots=True)
class CommittedFriPublicInputs:
    """Raw public statement/context plus exact semantic construction choices."""

    profile: FriIorProfile
    transcript_plan: TranscriptConstructionPlan
    statement: Any
    application_context: Any

    def __post_init__(self) -> None:
        if not isinstance(self.profile, FriIorProfile):
            raise malformed(
                "proof:public-input-formation",
                "FRI-IOR-PROOF-003",
                "committed FRI public input requires a FriIorProfile",
            )
        if not isinstance(self.transcript_plan, TranscriptConstructionPlan):
            raise malformed(
                "proof:public-input-formation",
                "FRI-IOR-PROOF-004",
                "committed FRI public input requires a transcript construction plan",
            )
        object.__setattr__(self, "statement", _freeze_closed_term(self.statement))
        object.__setattr__(
            self,
            "application_context",
            _freeze_closed_term(self.application_context),
        )
        # Bound the complete carrier, not only each raw term in isolation.  This
        # keeps ``identity`` total for every successfully formed value.
        encode_term(self.to_term())

    def to_term(self) -> dict[str, Any]:
        return {
            "schema": "zkc.fri-ior.committed-public-inputs.v1",
            "profile": self.profile.to_term(),
            "transcript_plan": self.transcript_plan.to_term(),
            "statement": _term_copy(self.statement),
            "application_context": _term_copy(self.application_context),
        }

    @property
    def identity(self) -> SemanticId:
        return semantic_id(
            "committed-fri-public-inputs",
            "fri-ior.committed-public-inputs.v1",
            self.to_term(),
        )


@dataclass(frozen=True, slots=True)
class OpeningTableEntry:
    """One physical opening, keyed canonically by layer and pair index."""

    layer: int
    opening: PairOpening

    def __post_init__(self) -> None:
        if type(self.layer) is not int or self.layer < 0:
            raise malformed(
                "proof:opening-table-formation",
                "FRI-IOR-PROOF-005",
                "an opening-table layer must be a non-negative integer",
            )
        if not isinstance(self.opening, PairOpening):
            raise malformed(
                "proof:opening-table-formation",
                "FRI-IOR-PROOF-006",
                "an opening-table entry requires a PairOpening",
            )

    @property
    def key(self) -> tuple[int, int]:
        return (self.layer, self.opening.pair_index)

    def to_term(self) -> dict[str, Any]:
        return {
            "layer": self.layer,
            "opening": self.opening.to_term(),
        }


@dataclass(frozen=True, slots=True)
class OccurrenceSelector:
    """Map one transcript draw to its two physical opening-table rows."""

    ordinal: int
    layer0_opening_index: int
    layer1_opening_index: int

    def __post_init__(self) -> None:
        for name in (
            "ordinal",
            "layer0_opening_index",
            "layer1_opening_index",
        ):
            value = getattr(self, name)
            if type(value) is not int or value < 0:
                raise malformed(
                    "proof:selector-formation",
                    "FRI-IOR-PROOF-007",
                    "occurrence-selector coordinates must be non-negative integers",
                )

    def to_term(self) -> dict[str, int]:
        return {
            "ordinal": self.ordinal,
            "layer0_opening_index": self.layer0_opening_index,
            "layer1_opening_index": self.layer1_opening_index,
        }


@dataclass(frozen=True, slots=True)
class PublicFriProof:
    """The exact public proof carrier consumed by committed verification."""

    cap0: MerkleCap
    cap1: MerkleCap
    terminal_coefficients: tuple[Fp2, ...]
    grinding_nonce: int
    opening_table: tuple[OpeningTableEntry, ...]
    occurrence_selectors: tuple[OccurrenceSelector, ...]

    def __post_init__(self) -> None:
        if not isinstance(self.cap0, MerkleCap) or not isinstance(self.cap1, MerkleCap):
            raise malformed(
                "proof:carrier-formation",
                "FRI-IOR-PROOF-008",
                "a public FRI proof requires two formed Merkle caps",
            )
        canonical_polynomial(
            self.terminal_coefficients,
            EXACT_PROFILE.terminal_max_coefficient_count,
        )
        if type(self.grinding_nonce) is not int or not (
            0 <= self.grinding_nonce <= MAX_GRINDING_NONCE
        ):
            raise malformed(
                "proof:carrier-formation",
                "FRI-IOR-PROOF-009",
                "the public grinding nonce must be an unsigned 32-bit integer",
            )
        if (
            not isinstance(self.opening_table, tuple)
            or len(self.opening_table) > MAX_OPENING_TABLE_ENTRIES
            or not all(
                isinstance(entry, OpeningTableEntry) for entry in self.opening_table
            )
        ):
            raise malformed(
                "proof:carrier-formation",
                "FRI-IOR-PROOF-010",
                "the opening table exceeds its bound or contains a wrong-kind value",
            )
        if (
            not isinstance(self.occurrence_selectors, tuple)
            or len(self.occurrence_selectors) > EXACT_PROFILE.ordered_query_count
            or not all(
                isinstance(selector, OccurrenceSelector)
                for selector in self.occurrence_selectors
            )
        ):
            raise malformed(
                "proof:carrier-formation",
                "FRI-IOR-PROOF-011",
                "the selector sequence exceeds its bound or contains a wrong-kind value",
            )
        # Enforce the closed-term intrinsic bounds without deciding table
        # canonicality or occurrence coverage at formation time.
        encode_term(self.to_term())

    def to_term(self) -> dict[str, Any]:
        return {
            "schema": "zkc.fri-ior.public-proof.v1",
            "cap0": self.cap0.to_term(),
            "cap1": self.cap1.to_term(),
            "terminal_polynomial": {
                "coefficient_order": "ascending",
                "coefficients": [
                    coefficient.to_term()
                    for coefficient in self.terminal_coefficients
                ],
            },
            "grinding_nonce": self.grinding_nonce,
            "opening_table": [entry.to_term() for entry in self.opening_table],
            "occurrence_selectors": [
                selector.to_term() for selector in self.occurrence_selectors
            ],
        }

    @property
    def canonical_byte_length(self) -> int:
        return len(encode_term(self.to_term()))

    @property
    def identity(self) -> SemanticId:
        return semantic_id(
            "committed-fri-proof",
            "fri-ior.committed-proof.v1",
            self.to_term(),
        )


__all__ = [
    "CommittedFriPublicInputs",
    "MAX_OPENING_TABLE_ENTRIES",
    "OccurrenceSelector",
    "OpeningTableEntry",
    "PublicFriProof",
]
