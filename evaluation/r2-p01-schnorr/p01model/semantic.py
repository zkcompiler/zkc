"""Challenge-neutral Schnorr conversation and Fresh/FS realizations.

The finite model deliberately tests a repair candidate rather than mirroring
the current durable target.  The shared Core contains a public challenge slot,
not Fresh sampling machinery.  A realization supplies either public coins or
an exact transcript program.  Required FS sources are derived from Statement
purpose and prior protected proof messages; they are not authored observation
bits.
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from enum import Enum
import hashlib
from typing import Any

from .terms import (
    Outcome,
    Result,
    TermEncodingError,
    affirmative,
    result,
    semantic_id,
)


STATEMENT = "statement:y"
APPLICATION_CONTEXT = "fs-context:application"
COMMITMENT = "message:commitment"
CHALLENGE = "challenge:c"
RESPONSE = "message:response"
CHECK = "check:schnorr-equation"
TERMINAL = "terminal:verifier-decision"
HONEST_WITNESS_SOURCE = "local:witness:x"
HONEST_NONCE_SOURCE = "local:nonce:r"

CANONICAL_SCHEDULE = (COMMITMENT, CHALLENGE, RESPONSE, CHECK, TERMINAL)


def _closed_content_id(value: Any) -> bool:
    if not isinstance(value, str) or len(value) != 71 or not value.startswith("sha256:"):
        return False
    return all(character in "0123456789abcdef" for character in value[7:])


def _bounded_text(value: Any, limit: int = 256) -> bool:
    if not isinstance(value, str) or not value:
        return False
    try:
        return len(value.encode("utf-8")) <= limit
    except UnicodeEncodeError:
        return False


class ParticipantRole(str, Enum):
    PROVER = "Prover"
    VERIFIER = "Verifier"
    PUBLIC_ENVIRONMENT = "PublicEnvironment"


class ApplicationContextAuthority(str, Enum):
    """Authority that supplies an FS invocation's public application context."""

    APPLICATION = "Application"
    PUBLIC_ENVIRONMENT = "PublicEnvironment"


class OccurrenceActor(str, Enum):
    PROVER = "Prover"
    VERIFIER = "Verifier"
    PUBLIC_ENVIRONMENT = "PublicEnvironment"
    CHALLENGE_RESOLVER = "ChallengeResolver"


class OccurrenceKind(str, Enum):
    INITIAL_PUBLIC_INPUT = "InitialPublicInput"
    PROOF_MESSAGE = "ProofMessage"
    CHALLENGE = "Challenge"
    VERIFIER_CHECK = "VerifierCheck"
    TERMINAL = "Terminal"


def _contract_id(domain: str, **fields: Any) -> str:
    return semantic_id(domain, fields)


def group_parameters_id(profile: AlgebraProfile) -> str:
    return _contract_id(
        "p01.group-parameters.v1",
        representation="PrimeOrderSubgroupOfMultiplicativeIntegers",
        p=profile.p,
        q=profile.q,
        generator=profile.generator,
    )


def group_domain_id(profile: AlgebraProfile) -> str:
    return _contract_id(
        "p01.value-domain.v2",
        kind="PrimeOrderSubgroupElement",
        ambient_modulus=profile.p,
        subgroup_order=profile.q,
    )


def scalar_domain_id(profile: AlgebraProfile) -> str:
    return _contract_id(
        "p01.value-domain.v2",
        kind="ScalarModuloQ",
        modulus=profile.q,
    )


def challenge_domain_id(profile: AlgebraProfile) -> str:
    return _contract_id(
        "p01.value-domain.v2",
        kind="InitialSegmentChallengeSet",
        scalar_domain_id=scalar_domain_id(profile),
        lower_bound=0,
        upper_bound_exclusive=profile.challenge_size,
        scalar_embedding="CanonicalNaturalEmbedding",
    )


def application_context_domain_id() -> str:
    return _contract_id(
        "p01.value-domain.v2",
        kind="BoundedApplicationContext",
        encoding="CanonicalUtf8",
        minimum_bytes=1,
        maximum_bytes=256,
    )


def boolean_domain_id() -> str:
    return _contract_id("p01.value-domain.v2", kind="Boolean")


def decision_domain_id() -> str:
    return _contract_id(
        "p01.value-domain.v2",
        kind="VerifierDisposition",
        values=("Accept", "Reject"),
    )


def schnorr_check_contract_id(profile: AlgebraProfile) -> str:
    return _contract_id(
        "p01.verifier-check-contract.v2",
        group_parameters_id=group_parameters_id(profile),
        input_domains=(
            ("statement", group_domain_id(profile)),
            ("commitment", group_domain_id(profile)),
            ("challenge", challenge_domain_id(profile)),
            ("response", scalar_domain_id(profile)),
        ),
        equation="g^z=A*Y^c",
    )


def terminal_contract_id(profile: AlgebraProfile) -> str:
    return _contract_id(
        "p01.terminal-contract.v2",
        check_contract_id=schnorr_check_contract_id(profile),
        output_domain_id=decision_domain_id(),
        law="AcceptIffCheckElseReject",
    )


def _is_prime(value: int) -> bool:
    if value < 2:
        return False
    if value % 2 == 0:
        return value == 2
    divisor = 3
    while divisor * divisor <= value:
        if value % divisor == 0:
            return False
        divisor += 2
    return True


def _frame(label: str, payload: bytes) -> bytes:
    label_bytes = label.encode("ascii")
    if len(label_bytes) >= 1 << 16 or len(payload) >= 1 << 32:
        raise ValueError("P01 transcript frame exceeds its bounded ABI")
    return (
        len(label_bytes).to_bytes(2, "big")
        + label_bytes
        + len(payload).to_bytes(4, "big")
        + payload
    )


_SHAKE128_RATE_BYTES = 168
_CFRG_SESSION_ID_DOMAIN = b"irtf-cfrg-fiat-shamir/session-id"


class _Shake128Duplex:
    """Exact finite SHAKE128 XOF-duplex state used by P01 FS v3.

    SHAKE's Python API exposes repeatable prefix reads rather than a consuming
    reader.  Keeping an explicit read offset gives the CFRG Init/Absorb/Squeeze
    behavior, including resetting the reader after a later nonempty Absorb.
    """

    def __init__(self, session_id: bytes) -> None:
        if not isinstance(session_id, bytes) or len(session_id) != 32:
            raise ValueError("SHAKE128 duplex Init requires a 32-byte session id")
        self._absorbed = bytearray(
            session_id + bytes(_SHAKE128_RATE_BYTES - len(session_id))
        )
        self._read_offset = 0

    @property
    def absorbed_bytes(self) -> bytes:
        return bytes(self._absorbed)

    def absorb(self, payload: bytes) -> None:
        if not isinstance(payload, bytes):
            raise TypeError("SHAKE128 duplex Absorb requires bytes")
        if payload:
            self._absorbed.extend(payload)
            self._read_offset = 0

    def squeeze(self, length: int) -> bytes:
        if not isinstance(length, int) or isinstance(length, bool) or length < 0:
            raise ValueError("SHAKE128 duplex Squeeze length must be nonnegative")
        end = self._read_offset + length
        stream = hashlib.shake_128(self.absorbed_bytes).digest(end)
        output = stream[self._read_offset : end]
        self._read_offset = end
        return output


def _derive_cfrg_session_id(tag: bytes) -> bytes:
    if not isinstance(tag, bytes) or not tag:
        raise ValueError("P01 FS v3 session tag must be nonempty bytes")
    state = _Shake128Duplex(_CFRG_SESSION_ID_DOMAIN)
    state.absorb(tag)
    return state.squeeze(32)


@dataclass(frozen=True)
class AlgebraProfile:
    """Finite evaluator bundle, not the identity of every contained domain."""

    p: int
    q: int
    generator: int
    challenge_size: int
    group_codec: str = "fixed-width-group-element.v1"
    scalar_codec: str = "fixed-width-scalar.v1"

    def term(self) -> dict[str, Any]:
        return {
            "p": self.p,
            "q": self.q,
            "generator": self.generator,
            "challenge_size": self.challenge_size,
            "group_codec": self.group_codec,
            "scalar_codec": self.scalar_codec,
        }

    @property
    def identity(self) -> str:
        return semantic_id("p01.finite-evaluation-profile.v2", self.term())

    @property
    def group_width(self) -> int:
        return max(1, (self.p.bit_length() + 7) // 8)

    @property
    def scalar_width(self) -> int:
        return max(1, (self.q.bit_length() + 7) // 8)

    def valid_group_element(self, value: Any) -> bool:
        return (
            isinstance(value, int)
            and not isinstance(value, bool)
            and 1 <= value < self.p
            and pow(value, self.q, self.p) == 1
        )

    def valid_scalar(self, value: Any) -> bool:
        return (
            isinstance(value, int)
            and not isinstance(value, bool)
            and 0 <= value < self.q
        )

    def valid_challenge(self, value: Any) -> bool:
        return (
            isinstance(value, int)
            and not isinstance(value, bool)
            and 0 <= value < self.challenge_size
        )

    def encode_group(self, value: int) -> bytes:
        if not self.valid_group_element(value):
            raise ValueError("value is not in the declared prime-order subgroup")
        return value.to_bytes(self.group_width, "big")

    def encode_scalar(self, value: int) -> bytes:
        if not self.valid_scalar(value):
            raise ValueError("value is not in the declared scalar domain")
        return value.to_bytes(self.scalar_width, "big")


def admit_algebra(profile: AlgebraProfile) -> Result:
    if not isinstance(profile, AlgebraProfile):
        return result(
            Outcome.MALFORMED,
            "algebra-profile",
            "P01-ALG-001",
            "algebra profile has the wrong type",
        )
    numeric_fields = (
        profile.p,
        profile.q,
        profile.generator,
        profile.challenge_size,
    )
    if (
        any(
            not isinstance(value, int) or isinstance(value, bool)
            for value in numeric_fields
        )
        or not isinstance(profile.group_codec, str)
        or not isinstance(profile.scalar_codec, str)
    ):
        return result(
            Outcome.MALFORMED,
            "algebra-profile",
            "P01-ALG-001",
            "algebra profile fields have the wrong types",
        )
    if (
        any(value.bit_length() > 16 for value in numeric_fields)
        or not _bounded_text(profile.group_codec, 128)
        or not _bounded_text(profile.scalar_codec, 128)
    ):
        return result(
            Outcome.RESOURCE_EXCEEDED,
            "algebra-profile:finite-evaluator-bound",
            "P01-ALG-009",
            "algebra profile exceeds the explicit finite evaluator bounds",
        )
    if not _is_prime(profile.p) or not _is_prime(profile.q):
        return result(
            Outcome.SEMANTIC_NEGATIVE,
            "algebra-profile",
            "P01-ALG-002",
            "p and q must be prime in this finite profile",
            subject=profile.identity,
        )
    if (profile.p - 1) % profile.q != 0:
        return result(
            Outcome.SEMANTIC_NEGATIVE,
            "algebra-profile",
            "P01-ALG-003",
            "q must divide p-1",
            subject=profile.identity,
        )
    if not profile.valid_group_element(profile.generator) or profile.generator == 1:
        return result(
            Outcome.SEMANTIC_NEGATIVE,
            "algebra-profile",
            "P01-ALG-004",
            "generator must have nontrivial order q",
            subject=profile.identity,
        )
    if pow(profile.generator, profile.q, profile.p) != 1:
        return result(
            Outcome.SEMANTIC_NEGATIVE,
            "algebra-profile",
            "P01-ALG-005",
            "generator does not satisfy the declared order equation",
            subject=profile.identity,
        )
    if (
        not isinstance(profile.challenge_size, int)
        or isinstance(profile.challenge_size, bool)
        or profile.challenge_size < 2
        or profile.challenge_size >= profile.q
        or profile.challenge_size & (profile.challenge_size - 1)
    ):
        return result(
            Outcome.SEMANTIC_NEGATIVE,
            "algebra-profile",
            "P01-ALG-006",
            "challenge size must be a power of two strictly between 1 and q",
            subject=profile.identity,
        )
    if profile.group_codec != "fixed-width-group-element.v1" or profile.scalar_codec != "fixed-width-scalar.v1":
        return result(
            Outcome.UNSUPPORTED,
            "algebra-profile",
            "P01-ALG-007",
            "the finite evaluator supports only its two pinned codecs",
            subject=profile.identity,
        )
    return affirmative(
        "algebra-profile",
        "P01-ALG-OK",
        "the finite algebra profile is admitted",
        subject=profile.identity,
    )


@dataclass(frozen=True)
class OccurrenceContract:
    occurrence: str
    kind: OccurrenceKind
    actor: OccurrenceActor
    recipients: tuple[ParticipantRole, ...]
    value_domain_id: str
    codec: str
    semantic_purpose: str
    semantic_contract_id: str

    def term(self) -> dict[str, Any]:
        return {
            "occurrence": self.occurrence,
            "kind": self.kind.value,
            "actor": self.actor.value,
            "recipients": [role.value for role in self.recipients],
            "value_domain_id": self.value_domain_id,
            "codec": self.codec,
            "semantic_purpose": self.semantic_purpose,
            "semantic_contract_id": self.semantic_contract_id,
        }


def canonical_occurrence_contracts(
    profile: AlgebraProfile,
) -> tuple[OccurrenceContract, ...]:
    all_roles = (
        ParticipantRole.PROVER,
        ParticipantRole.VERIFIER,
        ParticipantRole.PUBLIC_ENVIRONMENT,
    )
    return (
        OccurrenceContract(
            STATEMENT,
            OccurrenceKind.INITIAL_PUBLIC_INPUT,
            OccurrenceActor.PUBLIC_ENVIRONMENT,
            all_roles,
            group_domain_id(profile),
            profile.group_codec,
            "Statement",
            _contract_id(
                "p01.initial-input-contract.v2",
                purpose="Statement",
                value_domain_id=group_domain_id(profile),
            ),
        ),
        OccurrenceContract(
            COMMITMENT,
            OccurrenceKind.PROOF_MESSAGE,
            OccurrenceActor.PROVER,
            (ParticipantRole.VERIFIER,),
            group_domain_id(profile),
            profile.group_codec,
            "ProtocolValue",
            _contract_id(
                "p01.proof-message-contract.v2",
                role="SchnorrCommitment",
                value_domain_id=group_domain_id(profile),
            ),
        ),
        OccurrenceContract(
            CHALLENGE,
            OccurrenceKind.CHALLENGE,
            OccurrenceActor.CHALLENGE_RESOLVER,
            (ParticipantRole.PROVER, ParticipantRole.VERIFIER),
            challenge_domain_id(profile),
            "fixed-width-challenge.v1",
            "ProtocolValue",
            _contract_id(
                "p01.challenge-slot-contract.v2",
                value_domain_id=challenge_domain_id(profile),
                visibility="PublicAfterResolution",
            ),
        ),
        OccurrenceContract(
            RESPONSE,
            OccurrenceKind.PROOF_MESSAGE,
            OccurrenceActor.PROVER,
            (ParticipantRole.VERIFIER,),
            scalar_domain_id(profile),
            profile.scalar_codec,
            "ProtocolValue",
            _contract_id(
                "p01.proof-message-contract.v2",
                role="SchnorrResponse",
                value_domain_id=scalar_domain_id(profile),
            ),
        ),
        OccurrenceContract(
            CHECK,
            OccurrenceKind.VERIFIER_CHECK,
            OccurrenceActor.VERIFIER,
            (ParticipantRole.VERIFIER,),
            boolean_domain_id(),
            "canonical-boolean.v1",
            "VerifierDecision",
            schnorr_check_contract_id(profile),
        ),
        OccurrenceContract(
            TERMINAL,
            OccurrenceKind.TERMINAL,
            OccurrenceActor.VERIFIER,
            all_roles,
            decision_domain_id(),
            "verifier-disposition.v1",
            "Terminal",
            terminal_contract_id(profile),
        ),
    )


@dataclass(frozen=True)
class DeterministicRule:
    output_occurrence: str
    semantic_contract_id: str
    named_inputs: tuple[tuple[str, str], ...]

    def term(self) -> dict[str, Any]:
        return {
            "output_occurrence": self.output_occurrence,
            "semantic_contract_id": self.semantic_contract_id,
            "named_inputs": [
                {"name": name, "occurrence": occurrence}
                for name, occurrence in self.named_inputs
            ],
        }


@dataclass(frozen=True)
class ConversationCore:
    roles: tuple[ParticipantRole, ...]
    occurrences: tuple[OccurrenceContract, ...]
    verifier_check: DeterministicRule
    terminal_route: DeterministicRule
    model: str = "ChallengeNeutralConversationCore.v3"

    def term(self) -> dict[str, Any]:
        return {
            "model": self.model,
            "roles": [role.value for role in self.roles],
            "occurrences": [contract.term() for contract in self.occurrences],
            "verifier_check": self.verifier_check.term(),
            "terminal_route": self.terminal_route.term(),
        }

    @property
    def identity(self) -> str:
        return semantic_id("p01.conversation-core.v3", self.term())

    def contract_for(self, occurrence: str) -> OccurrenceContract:
        matches = tuple(
            contract
            for contract in self.occurrences
            if contract.occurrence == occurrence
        )
        if len(matches) != 1:
            raise KeyError(occurrence)
        return matches[0]

    @property
    def public_statements(self) -> tuple[str, ...]:
        return tuple(
            contract.occurrence
            for contract in self.occurrences
            if contract.kind is OccurrenceKind.INITIAL_PUBLIC_INPUT
            and contract.semantic_purpose == "Statement"
        )

    @property
    def proof_messages(self) -> tuple[str, ...]:
        return tuple(
            contract.occurrence
            for contract in self.occurrences
            if contract.kind is OccurrenceKind.PROOF_MESSAGE
        )

    @property
    def schedule(self) -> tuple[str, ...]:
        return tuple(
            contract.occurrence
            for contract in self.occurrences
            if contract.kind is not OccurrenceKind.INITIAL_PUBLIC_INPUT
        )

    def visible_public_before(
        self, role: ParticipantRole, occurrence: str
    ) -> tuple[str, ...]:
        if occurrence not in self.schedule:
            raise KeyError(occurrence)
        position = self.schedule.index(occurrence)
        visible: list[str] = []
        for contract in self.occurrences:
            if contract.kind is OccurrenceKind.INITIAL_PUBLIC_INPUT:
                if role in contract.recipients:
                    visible.append(contract.occurrence)
                continue
            if contract.occurrence not in self.schedule:
                continue
            if self.schedule.index(contract.occurrence) >= position:
                continue
            if (
                role in contract.recipients
                or contract.actor.value == role.value
            ):
                visible.append(contract.occurrence)
        return tuple(visible)


def canonical_core(profile: AlgebraProfile) -> ConversationCore:
    return ConversationCore(
        roles=(
            ParticipantRole.PROVER,
            ParticipantRole.VERIFIER,
            ParticipantRole.PUBLIC_ENVIRONMENT,
        ),
        occurrences=canonical_occurrence_contracts(profile),
        verifier_check=DeterministicRule(
            CHECK,
            schnorr_check_contract_id(profile),
            (
                ("statement", STATEMENT),
                ("commitment", COMMITMENT),
                ("challenge", CHALLENGE),
                ("response", RESPONSE),
            ),
        ),
        terminal_route=DeterministicRule(
            TERMINAL,
            terminal_contract_id(profile),
            (("check", CHECK),),
        ),
    )


def _duplicates(values: tuple[str, ...]) -> bool:
    return len(set(values)) != len(values)


def admit_core(core: ConversationCore, profile: AlgebraProfile) -> Result:
    if not isinstance(core, ConversationCore):
        return result(
            Outcome.MALFORMED,
            "core-admission",
            "P01-CORE-001",
            "Core has the wrong type",
        )
    if (
        not isinstance(core.model, str)
        or not isinstance(core.roles, tuple)
        or any(not isinstance(role, ParticipantRole) for role in core.roles)
        or not isinstance(core.occurrences, tuple)
        or any(
            not isinstance(contract, OccurrenceContract)
            or not isinstance(contract.occurrence, str)
            or not isinstance(contract.kind, OccurrenceKind)
            or not isinstance(contract.actor, OccurrenceActor)
            or not isinstance(contract.recipients, tuple)
            or any(
                not isinstance(role, ParticipantRole)
                for role in contract.recipients
            )
            or not isinstance(contract.value_domain_id, str)
            or not isinstance(contract.codec, str)
            or not isinstance(contract.semantic_purpose, str)
            or not isinstance(contract.semantic_contract_id, str)
            for contract in core.occurrences
        )
        or not isinstance(core.verifier_check, DeterministicRule)
        or not isinstance(core.terminal_route, DeterministicRule)
        or any(
            not isinstance(rule.output_occurrence, str)
            or not isinstance(rule.semantic_contract_id, str)
            or not isinstance(rule.named_inputs, tuple)
            or any(
                not isinstance(binding, tuple)
                or len(binding) != 2
                or not all(isinstance(part, str) for part in binding)
                for binding in rule.named_inputs
            )
            for rule in (core.verifier_check, core.terminal_route)
        )
    ):
        return result(
            Outcome.MALFORMED,
            "core-admission",
            "P01-CORE-001",
            "Core fields are outside the closed typed grammar",
        )
    if (
        len(core.roles) > 8
        or len(core.occurrences) > 32
        or any(len(rule.named_inputs) > 32 for rule in (core.verifier_check, core.terminal_route))
        or not _bounded_text(core.model, 128)
        or any(
            not _bounded_text(contract.occurrence)
            or not _bounded_text(contract.value_domain_id, 128)
            or not _bounded_text(contract.codec, 128)
            or not _bounded_text(contract.semantic_purpose, 128)
            or not _bounded_text(contract.semantic_contract_id, 128)
            for contract in core.occurrences
        )
    ):
        return result(
            Outcome.RESOURCE_EXCEEDED,
            "core-admission:finite-evaluator-bound",
            "P01-CORE-012",
            "Core exceeds the explicit finite evaluator bounds",
        )
    algebra_result = admit_algebra(profile)
    if algebra_result.outcome is not Outcome.AFFIRMATIVE:
        return algebra_result
    if core.model != "ChallengeNeutralConversationCore.v3":
        return result(
            Outcome.UNSUPPORTED,
            "core-admission:model",
            "P01-CORE-011",
            "Core model version is unsupported by the finite evaluator",
            subject=core.identity,
        )
    expected_roles = (
        ParticipantRole.PROVER,
        ParticipantRole.VERIFIER,
        ParticipantRole.PUBLIC_ENVIRONMENT,
    )
    if core.roles != expected_roles:
        return result(
            Outcome.SEMANTIC_NEGATIVE,
            "core-admission:roles",
            "P01-CORE-005",
            "finite Core does not have the exact participant-role set",
            subject=core.identity,
        )
    occurrence_names = tuple(contract.occurrence for contract in core.occurrences)
    if _duplicates(occurrence_names):
        return result(
            Outcome.SEMANTIC_NEGATIVE,
            "core-admission:occurrences",
            "P01-CORE-004",
            "occurrence contracts are duplicated",
            subject=core.identity,
        )
    if not core.schedule:
        return result(
            Outcome.SEMANTIC_NEGATIVE,
            "core-admission:schedule",
            "P01-CORE-003",
            "conversation has no scheduled effect occurrences",
            subject=core.identity,
        )
    known_domains = {
        group_domain_id(profile),
        scalar_domain_id(profile),
        challenge_domain_id(profile),
        boolean_domain_id(),
        decision_domain_id(),
    }
    for contract in core.occurrences:
        canonical_recipients = tuple(
            role for role in core.roles if role in contract.recipients
        )
        if (
            not isinstance(contract.kind, OccurrenceKind)
            or not isinstance(contract.actor, OccurrenceActor)
            or not contract.recipients
            or _duplicates(tuple(role.value for role in contract.recipients))
            or any(role not in core.roles for role in contract.recipients)
            or contract.recipients != canonical_recipients
            or contract.value_domain_id not in known_domains
            or not contract.codec
            or not _closed_content_id(contract.semantic_contract_id)
        ):
            return result(
                Outcome.SEMANTIC_NEGATIVE,
                f"core-admission:occurrence-contract:{contract.occurrence}",
                "P01-CORE-006",
                "occurrence contract has an invalid actor, recipient, domain, codec, or semantic contract",
                subject=core.identity,
            )
    initial_contracts = tuple(
        contract
        for contract in core.occurrences
        if contract.kind is OccurrenceKind.INITIAL_PUBLIC_INPUT
    )
    scheduled_contracts = tuple(
        contract
        for contract in core.occurrences
        if contract.kind is not OccurrenceKind.INITIAL_PUBLIC_INPUT
    )
    if core.occurrences != initial_contracts + scheduled_contracts:
        return result(
            Outcome.SEMANTIC_NEGATIVE,
            "core-admission:occurrence-order",
            "P01-CORE-010",
            "initial public inputs must precede every scheduled occurrence",
            subject=core.identity,
        )
    rules = (core.verifier_check, core.terminal_route)
    positions = {event: index for index, event in enumerate(core.schedule)}
    initial = {
        contract.occurrence
        for contract in core.occurrences
        if contract.kind is OccurrenceKind.INITIAL_PUBLIC_INPUT
    }
    deterministic_occurrences = {
        contract.occurrence
        for contract in core.occurrences
        if contract.kind
        in (OccurrenceKind.VERIFIER_CHECK, OccurrenceKind.TERMINAL)
    }
    outputs = tuple(rule.output_occurrence for rule in rules)
    if set(outputs) != deterministic_occurrences or _duplicates(outputs):
        return result(
            Outcome.SEMANTIC_NEGATIVE,
            "core-admission:deterministic-rules",
            "P01-CORE-007",
            "deterministic rules are not total and unique for verifier operations",
            subject=core.identity,
        )
    for rule in rules:
        try:
            output_contract = core.contract_for(rule.output_occurrence)
        except KeyError:
            output_contract = None
        input_names = tuple(name for name, _ in rule.named_inputs)
        if (
            output_contract is None
            or output_contract.semantic_contract_id != rule.semantic_contract_id
            or not _closed_content_id(rule.semantic_contract_id)
            or _duplicates(input_names)
        ):
            return result(
                Outcome.SEMANTIC_NEGATIVE,
                f"core-admission:deterministic-rule:{rule.output_occurrence}",
                "P01-CORE-008",
                "deterministic rule has an invalid output contract or operand naming",
                subject=core.identity,
            )
        source_order = {
            contract.occurrence: index
            for index, contract in enumerate(core.occurrences)
        }
        canonical_named_inputs = tuple(
            sorted(
                rule.named_inputs,
                key=lambda binding: (
                    source_order.get(binding[1], len(source_order)),
                    binding[0],
                ),
            )
        )
        if rule.named_inputs != canonical_named_inputs:
            return result(
                Outcome.SEMANTIC_NEGATIVE,
                f"core-admission:deterministic-rule-order:{rule.output_occurrence}",
                "P01-CORE-013",
                "set- and map-like Core fields must use their canonical order",
                subject=core.identity,
            )
        for _, source in rule.named_inputs:
            if source in initial:
                continue
            if (
                source not in positions
                or positions[source] >= positions[rule.output_occurrence]
            ):
                return result(
                    Outcome.SEMANTIC_NEGATIVE,
                    f"core-availability:{rule.output_occurrence}",
                    "P01-CORE-009",
                    "deterministic input is not in the operation's causal past",
                    subject=core.identity,
                    source=source,
                )
    return affirmative(
        "core-admission",
        "P01-CORE-OK",
        "typed challenge-neutral finite Core is admitted",
        subject=core.identity,
    )


def admit_application_context(value: Any) -> Result:
    """Admit one runtime context value; it is never part of protocol identity."""

    if not isinstance(value, str):
        return result(
            Outcome.MALFORMED,
            "runtime-application-context",
            "P01-CTX-001",
            "application context must be a string",
        )
    try:
        encoded = value.encode("utf-8")
    except UnicodeEncodeError:
        encoded = b""
    if not encoded or len(encoded) > 256:
        return result(
            Outcome.SEMANTIC_NEGATIVE,
            "runtime-application-context",
            "P01-CTX-002",
            "application context must be nonempty canonical UTF-8 of at most 256 bytes",
        )
    return affirmative(
        "runtime-application-context",
        "P01-CTX-OK",
        "runtime application context is admitted",
        subject=semantic_id(
            "p01.runtime-application-context.v1", {"utf8": value}
        ),
    )


def check_public_coin_eligibility(
    core: ConversationCore, profile: AlgebraProfile
) -> Result:
    """Derive the structural premise needed by either challenge realization."""

    core_result = admit_core(core, profile)
    if core_result.outcome is not Outcome.AFFIRMATIVE:
        return core_result
    try:
        challenge = core.contract_for(CHALLENGE)
    except KeyError:
        return result(
            Outcome.SEMANTIC_NEGATIVE,
            "source-correspondence:public-coin-eligibility",
            "P01-PCOIN-001",
            "Core has no unique canonical public challenge occurrence",
            subject=core.identity,
        )
    if (
        challenge.actor is not OccurrenceActor.CHALLENGE_RESOLVER
        or challenge.recipients
        != (ParticipantRole.PROVER, ParticipantRole.VERIFIER)
        or challenge.value_domain_id != challenge_domain_id(profile)
    ):
        return result(
            Outcome.SEMANTIC_NEGATIVE,
            "source-correspondence:public-coin-eligibility",
            "P01-PCOIN-001",
            "challenge slot is not an external, public, operand-free resolution point",
            subject=core.identity,
        )
    return affirmative(
        "source-correspondence:public-coin-eligibility",
        "P01-PCOIN-OK",
        "Core exposes the exact public challenge slot required by Fresh and Fiat-Shamir",
        subject=core.identity,
    )


def check_schnorr_correspondence(
    core: ConversationCore, profile: AlgebraProfile
) -> Result:
    """Check source-specific actors, domains, contracts, order, and verifier law."""

    core_result = admit_core(core, profile)
    if core_result.outcome is not Outcome.AFFIRMATIVE:
        return core_result
    expected_occurrences = canonical_occurrence_contracts(profile)
    expected_names = tuple(
        contract.occurrence for contract in expected_occurrences
    )
    actual_names = tuple(contract.occurrence for contract in core.occurrences)
    if len(actual_names) != len(expected_names) or set(actual_names) != set(
        expected_names
    ):
        return result(
            Outcome.SEMANTIC_NEGATIVE,
            "source-correspondence:sigma-contract:closed-occurrence-set",
            "P01-CORR-002",
            "Core omits, renames, or adds an occurrence outside minimal Schnorr",
            subject=core.identity,
        )
    positions = {event: index for index, event in enumerate(core.schedule)}
    if not (
        positions[COMMITMENT]
        < positions[CHALLENGE]
        < positions[RESPONSE]
        < positions[CHECK]
        < positions[TERMINAL]
    ):
        return result(
            Outcome.SEMANTIC_NEGATIVE,
            "source-correspondence:sigma-three-move-order",
            "P01-CORR-001",
            "Core is admissible as a conversation but not a Schnorr three-move order",
            subject=core.identity,
        )
    if core.occurrences != expected_occurrences:
        for expected in expected_occurrences:
            try:
                actual = core.contract_for(expected.occurrence)
            except KeyError:
                actual = None
            if actual != expected:
                return result(
                    Outcome.SEMANTIC_NEGATIVE,
                    f"source-correspondence:sigma-contract:{expected.occurrence}",
                    "P01-CORR-002",
                    "actor, direction, domain, codec, purpose, or semantic contract differs from Schnorr",
                    subject=core.identity,
                    occurrence=expected.occurrence,
                )
        return result(
            Outcome.SEMANTIC_NEGATIVE,
            "source-correspondence:sigma-contract:closed-occurrence-set",
            "P01-CORR-002",
            "Core contains an extra or reordered occurrence outside minimal Schnorr",
            subject=core.identity,
        )
    expected_core = canonical_core(profile)
    if (
        core.verifier_check != expected_core.verifier_check
        or core.terminal_route != expected_core.terminal_route
    ):
        return result(
            Outcome.SEMANTIC_NEGATIVE,
            "source-correspondence:sigma-deterministic-rules",
            "P01-CORR-003",
            "verifier computation does not consume the exact Schnorr operands",
            subject=core.identity,
        )
    return affirmative(
        "source-correspondence:sigma",
        "P01-CORR-OK",
        "Core has the typed Schnorr roles, messages, challenge slot, verifier equation, and terminal law",
        subject=core.identity,
        check_contract_id=schnorr_check_contract_id(profile),
    )


@dataclass(frozen=True)
class HonestLocalInput:
    name: str
    value_domain_id: str
    purpose: str
    distribution_contract_id: str | None = None

    def term(self) -> dict[str, str]:
        return {
            "name": self.name,
            "value_domain_id": self.value_domain_id,
            "purpose": self.purpose,
            "distribution_contract_id": self.distribution_contract_id,
        }


@dataclass(frozen=True)
class HonestTransitionRule:
    output_occurrence: str
    named_inputs: tuple[tuple[str, str], ...]
    semantic_contract_id: str

    def term(self) -> dict[str, Any]:
        return {
            "output_occurrence": self.output_occurrence,
            "named_inputs": [
                {"name": name, "source": source}
                for name, source in self.named_inputs
            ],
            "semantic_contract_id": self.semantic_contract_id,
        }


@dataclass(frozen=True)
class HonestProverContract:
    core_id: str
    statement_occurrence: str
    witness_precondition_contract_id: str
    local_inputs: tuple[HonestLocalInput, ...]
    commitment_rule: HonestTransitionRule
    response_rule: HonestTransitionRule
    local_state_contract_id: str
    model: str = "SchnorrHonestProverContract.v1"

    def term(self) -> dict[str, Any]:
        return {
            "model": self.model,
            "core_id": self.core_id,
            "statement_occurrence": self.statement_occurrence,
            "witness_precondition_contract_id": self.witness_precondition_contract_id,
            "local_inputs": [value.term() for value in self.local_inputs],
            "commitment_rule": self.commitment_rule.term(),
            "response_rule": self.response_rule.term(),
            "local_state_contract_id": self.local_state_contract_id,
        }

    @property
    def identity(self) -> str:
        return semantic_id("p01.honest-prover-contract.v1", self.term())


def honest_witness_precondition_contract_id(profile: AlgebraProfile) -> str:
    """Identify the relation-witness law shared with Relations correspondence."""

    return _contract_id(
        "p01.honest-witness-precondition.v1",
        group_parameters_id=group_parameters_id(profile),
        statement_domain_id=group_domain_id(profile),
        witness_domain_id=scalar_domain_id(profile),
        law="Y=g^x",
    )


def canonical_honest_prover_contract(
    core: ConversationCore, profile: AlgebraProfile
) -> HonestProverContract:
    scalar_id = scalar_domain_id(profile)
    nonce_distribution = _contract_id(
        "p01.honest-randomness-contract.v1",
        value_domain_id=scalar_id,
        conditioning_domain="EveryAdmittedStatementWitnessPair",
        law="FreshExactUniformIndependentNoncePerInvocation",
        mass_numerator=1,
        mass_denominator=profile.q,
        failure_mass_numerator=0,
        failure_mass_denominator=1,
        single_use=True,
    )
    commitment_rule_id = _contract_id(
        "p01.honest-prover-transition.v1",
        group_parameters_id=group_parameters_id(profile),
        output_domain_id=group_domain_id(profile),
        law="A=g^r",
    )
    response_rule_id = _contract_id(
        "p01.honest-prover-transition.v1",
        scalar_domain_id=scalar_id,
        challenge_domain_id=challenge_domain_id(profile),
        law="z=r+c*x mod q",
    )
    local_state_contract = _contract_id(
        "p01.honest-prover-local-state.v1",
        retained_source=HONEST_NONCE_SOURCE,
        retention_interval=(COMMITMENT, RESPONSE),
        single_use=True,
    )
    return HonestProverContract(
        core_id=core.identity,
        statement_occurrence=STATEMENT,
        witness_precondition_contract_id=honest_witness_precondition_contract_id(
            profile
        ),
        local_inputs=(
            HonestLocalInput(
                HONEST_WITNESS_SOURCE, scalar_id, "RelationWitness"
            ),
            HonestLocalInput(
                HONEST_NONCE_SOURCE,
                scalar_id,
                "PrivateRandomness",
                nonce_distribution,
            ),
        ),
        commitment_rule=HonestTransitionRule(
            COMMITMENT,
            (("nonce", HONEST_NONCE_SOURCE),),
            commitment_rule_id,
        ),
        response_rule=HonestTransitionRule(
            RESPONSE,
            (
                ("retained_nonce", HONEST_NONCE_SOURCE),
                ("witness", HONEST_WITNESS_SOURCE),
                ("challenge", CHALLENGE),
            ),
            response_rule_id,
        ),
        local_state_contract_id=local_state_contract,
    )


def admit_honest_prover_contract(
    contract: HonestProverContract,
    core: ConversationCore,
    profile: AlgebraProfile,
) -> Result:
    if not isinstance(contract, HonestProverContract):
        return result(
            Outcome.MALFORMED,
            "honest-prover-contract",
            "P01-HONEST-000",
            "honest prover contract has the wrong type",
        )
    correspondence = check_schnorr_correspondence(core, profile)
    if correspondence.outcome is not Outcome.AFFIRMATIVE:
        return correspondence
    try:
        contract_id = contract.identity
    except (AttributeError, TermEncodingError, TypeError, ValueError):
        return result(
            Outcome.MALFORMED,
            "honest-prover-contract",
            "P01-HONEST-000",
            "honest prover contract is outside the closed typed grammar",
        )
    expected = canonical_honest_prover_contract(core, profile)
    if contract.core_id != core.identity:
        return result(
            Outcome.MISMATCH,
            "honest-prover-contract:core",
            "P01-HONEST-001",
            "honest prover contract names a different conversation Core",
            subject=contract_id,
        )
    if contract != expected:
        return result(
            Outcome.SEMANTIC_NEGATIVE,
            "honest-prover-contract:exact-transition-laws",
            "P01-HONEST-002",
            "witness, randomness, state, or transition law differs from minimal Schnorr",
            subject=contract_id,
            expected_contract_id=expected.identity,
        )
    return affirmative(
        "honest-prover-contract",
        "P01-HONEST-OK",
        "typed Schnorr honest-prover transition contract is admitted",
        subject=contract_id,
        non_claim="not implementation conformance, completeness, or an adversary restriction",
    )


class RealizationKind(str, Enum):
    FRESH = "FreshPublicCoin"
    FIAT_SHAMIR = "FiatShamir"


def public_challenge_prefix_id(core: ConversationCore) -> str | Result:
    """Identify the typed public history schema immediately before challenge."""

    if not isinstance(core, ConversationCore):
        return result(
            Outcome.MALFORMED,
            "fresh-prefix:derivation",
            "P01-FRESH-DERIVE-001",
            "public challenge prefix requires a ConversationCore",
        )
    try:
        schedule = core.schedule
        challenge_position = schedule.index(CHALLENGE)
        prefix_occurrences = tuple(
            contract
            for contract in core.occurrences
            if contract.kind is OccurrenceKind.INITIAL_PUBLIC_INPUT
            or (
                contract.occurrence in schedule
                and schedule.index(contract.occurrence) < challenge_position
            )
        )
        return semantic_id(
            "p01.public-challenge-prefix.v1",
            {
                "challenge_occurrence": CHALLENGE,
                "prefix_occurrences": [
                    contract.term() for contract in prefix_occurrences
                ],
            },
        )
    except (
        AttributeError,
        KeyError,
        TermEncodingError,
        TypeError,
        ValueError,
    ):
        return result(
            Outcome.MISSING_DEPENDENCY,
            "fresh-prefix:derivation",
            "P01-FRESH-DERIVE-001",
            "Core does not expose a closed typed public prefix before challenge",
        )


def fresh_conditional_kernel_contract_id(
    core: ConversationCore, profile: AlgebraProfile
) -> str | Result:
    algebra_result = admit_algebra(profile)
    if algebra_result.outcome is not Outcome.AFFIRMATIVE:
        return algebra_result
    prefix_id = public_challenge_prefix_id(core)
    if isinstance(prefix_id, Result):
        return prefix_id
    return _contract_id(
        "p01.fresh-challenge-kernel.v1",
        prefix_schema_id=prefix_id,
        challenge_occurrence=CHALLENGE,
        challenge_domain_id=challenge_domain_id(profile),
        resolver=OccurrenceActor.PUBLIC_ENVIRONMENT.value,
        conditioning_domain="EveryPrefixValueAssignmentAdmittedByTheTypedPrefixSchema",
        law="ForEveryAdmissiblePrefixExactUniformIndependentDraw",
        mass_numerator=1,
        mass_denominator=profile.challenge_size,
        failure_mass_numerator=0,
        failure_mass_denominator=1,
        disclosure="AtChallengeBoundaryAfterPrefix",
        excluded_influences=("ProverPrivateState", "VerifierPrivateState"),
    )


@dataclass(frozen=True)
class FreshRealization:
    core_id: str
    conditional_kernel_contract_id: str
    challenge_occurrence: str = CHALLENGE
    resolver: OccurrenceActor = OccurrenceActor.PUBLIC_ENVIRONMENT

    def term(self) -> dict[str, str]:
        return {
            "kind": RealizationKind.FRESH.value,
            "core_id": self.core_id,
            "conditional_kernel_contract_id": self.conditional_kernel_contract_id,
            "challenge_occurrence": self.challenge_occurrence,
            "resolver": self.resolver.value,
        }

    @property
    def identity(self) -> str:
        return semantic_id("p01.fresh-realization.v2", self.term())


@dataclass(frozen=True)
class TranscriptAtom:
    source_kind: str
    occurrence: str
    value_domain_id: str
    codec: str

    def term(self) -> dict[str, str]:
        return {
            "source_kind": self.source_kind,
            "occurrence": self.occurrence,
            "value_domain_id": self.value_domain_id,
            "codec": self.codec,
        }


@dataclass(frozen=True)
class RuntimeContextContract:
    source: str
    semantic_purpose: str
    value_domain_id: str
    codec: str

    def term(self) -> dict[str, str]:
        return {
            "source": self.source,
            "semantic_purpose": self.semantic_purpose,
            "value_domain_id": self.value_domain_id,
            "codec": self.codec,
        }

    @property
    def identity(self) -> str:
        return semantic_id("p01.runtime-context-contract.v1", self.term())


def canonical_runtime_context_contract() -> RuntimeContextContract:
    return RuntimeContextContract(
        APPLICATION_CONTEXT,
        "ApplicationContext",
        application_context_domain_id(),
        "bounded-utf8.v1",
    )


@dataclass(frozen=True)
class ChallengeDecoderContract:
    squeeze_bytes: int
    byte_order: str
    reduction: str
    modulus: int
    codomain_id: str
    bias_numerator: int
    bias_denominator: int
    failure_numerator: int
    failure_denominator: int

    def term(self) -> dict[str, Any]:
        return {
            "squeeze_bytes": self.squeeze_bytes,
            "byte_order": self.byte_order,
            "reduction": self.reduction,
            "modulus": self.modulus,
            "codomain_id": self.codomain_id,
            "bias_numerator": self.bias_numerator,
            "bias_denominator": self.bias_denominator,
            "failure_numerator": self.failure_numerator,
            "failure_denominator": self.failure_denominator,
        }

    @property
    def identity(self) -> str:
        return semantic_id("p01.challenge-decoder-contract.v1", self.term())


def p01_language_id(profile: AlgebraProfile) -> str:
    return _contract_id(
        "p01.schnorr-language.v1",
        kind="DiscreteLogKnowledgeLanguage",
        group_parameters_id=group_parameters_id(profile),
        statement_domain_id=group_domain_id(profile),
        witness_domain_id=scalar_domain_id(profile),
        relation="Exists x in Z_q such that Y=g^x",
    )


def canonical_source_fresh_protocol_id(
    core: ConversationCore,
    profile: AlgebraProfile,
    fresh: FreshRealization,
) -> str:
    """Reconstruct the exact construction-independent Fresh Protocol ID."""

    return ProtocolVariant(
        core_id=core.identity,
        honest_prover_contract_id=canonical_honest_prover_contract(
            core, profile
        ).identity,
        realization_kind=RealizationKind.FRESH,
        realization_id=fresh.identity,
    ).identity


def p01_argument_system_id(
    core: ConversationCore,
    profile: AlgebraProfile,
    fresh: FreshRealization,
) -> str:
    return _contract_id(
        "p01.schnorr-public-coin-argument-system.v1",
        kind="ThreeMoveSchnorrSigma",
        language_id=p01_language_id(profile),
        core_id=core.identity,
        honest_prover_contract_id=canonical_honest_prover_contract(
            core, profile
        ).identity,
        source_fresh_protocol_id=canonical_source_fresh_protocol_id(
            core, profile, fresh
        ),
        fresh_realization_id=fresh.identity,
        conditional_kernel_contract_id=fresh.conditional_kernel_contract_id,
    )


def p01_proof_flavor_id(core: ConversationCore, profile: AlgebraProfile) -> str:
    return _contract_id(
        "p01.fs-proof-flavor.v1",
        kind="BatchableCommitmentResponse",
        proof_fields=(
            (
                COMMITMENT,
                core.contract_for(COMMITMENT).value_domain_id,
                profile.group_codec,
            ),
            (
                RESPONSE,
                core.contract_for(RESPONSE).value_domain_id,
                profile.scalar_codec,
            ),
        ),
        serialization="ExactFixedWidthCommitmentThenResponse",
    )


def p01_application_domain_id() -> str:
    return _contract_id(
        "p01.fs-application-domain.v1",
        application="zkc/p01/minimal-schnorr",
        version=3,
        purpose="FiniteSemanticWitness",
    )


def p01_duplex_suite_id() -> str:
    return _contract_id(
        "p01.fs-duplex-suite.v1",
        primitive="SHAKE128",
        model="CFRG-XOFDuplex-v03",
        rate_bytes=_SHAKE128_RATE_BYTES,
        init="AbsorbSessionIdThenZeroPadToRate",
        absorb="IncrementalBytesResetReaderWhenNonEmpty",
        squeeze="ContinueUniformXOFByteStream",
    )


def p01_session_derivation_rule_id() -> str:
    return _contract_id(
        "p01.fs-session-derivation-rule.v1",
        duplex_suite_id=p01_duplex_suite_id(),
        initialization_domain=_CFRG_SESSION_ID_DOMAIN,
        action="InitDomainThenAbsorbInjectivelyFramedTagThenSqueeze32",
        output_bytes=32,
    )


def p01_salt_policy_id() -> str:
    return _contract_id(
        "p01.fs-salt-policy.v1",
        policy="NoSalt",
        theorem_effect="NoZeroKnowledgeClaimGrantedByConstruction",
    )


def p01_composition_context_id() -> str:
    return _contract_id(
        "p01.fs-composition-context.v1",
        context="Standalone",
        child_occurrences=(),
    )


def canonical_challenge_decoder_contract(
    profile: AlgebraProfile,
) -> ChallengeDecoderContract:
    return ChallengeDecoderContract(
        squeeze_bytes=1,
        byte_order="LittleEndian",
        reduction="LE2IP(buf) mod 8",
        modulus=8,
        codomain_id=challenge_domain_id(profile),
        bias_numerator=0,
        bias_denominator=1,
        failure_numerator=0,
        failure_denominator=1,
    )


def source_public_coin_basis_id(
    fresh: FreshRealization,
    core: ConversationCore,
    profile: AlgebraProfile,
) -> str:
    return _contract_id(
        "p01.fs-source-public-coin-basis.v1",
        core_id=core.identity,
        honest_prover_contract_id=canonical_honest_prover_contract(
            core, profile
        ).identity,
        fresh_realization_id=fresh.identity,
        conditional_kernel_contract_id=fresh.conditional_kernel_contract_id,
        challenge_occurrence=fresh.challenge_occurrence,
        challenge_domain_id=challenge_domain_id(profile),
        resolver=fresh.resolver.value,
    )


def _canonical_fresh_basis(
    core: ConversationCore,
    profile: AlgebraProfile,
) -> tuple[FreshRealization, str]:
    kernel_contract_id = fresh_conditional_kernel_contract_id(core, profile)
    if isinstance(kernel_contract_id, Result):
        raise ValueError(kernel_contract_id.detail)
    fresh = FreshRealization(core.identity, kernel_contract_id)
    return fresh, source_public_coin_basis_id(fresh, core, profile)


@dataclass(frozen=True)
class TranscriptConstruction:
    core_id: str
    suite_domain: str
    runtime_context: RuntimeContextContract
    atoms: tuple[TranscriptAtom, ...]
    challenge_occurrence: str
    challenge_namespace: str
    framing: str
    sampler: str
    model: str = "StrongFiatShamirTranscriptConstruction.v3"
    source_fresh_protocol_id: str = ""
    source_fresh_realization_id: str = ""
    source_public_coin_basis_id: str = ""
    language_id: str = ""
    argument_system_id: str = ""
    application_domain_id: str = ""
    proof_flavor_id: str = ""
    duplex_suite_id: str = ""
    session_derivation_rule_id: str = ""
    salt_policy_id: str = ""
    composition_context_id: str = ""
    application_authority: ApplicationContextAuthority = (
        ApplicationContextAuthority.APPLICATION
    )
    decoder: ChallengeDecoderContract | None = None

    def term(self) -> dict[str, Any]:
        return {
            "model": self.model,
            "core_id": self.core_id,
            "suite_domain": self.suite_domain,
            "runtime_context": self.runtime_context.term(),
            "atoms": [atom.term() for atom in self.atoms],
            "challenge_occurrence": self.challenge_occurrence,
            "challenge_namespace": self.challenge_namespace,
            "framing": self.framing,
            "sampler": self.sampler,
            "source_fresh_protocol_id": self.source_fresh_protocol_id,
            "source_fresh_realization_id": self.source_fresh_realization_id,
            "source_public_coin_basis_id": self.source_public_coin_basis_id,
            "language_id": self.language_id,
            "argument_system_id": self.argument_system_id,
            "application_domain_id": self.application_domain_id,
            "proof_flavor_id": self.proof_flavor_id,
            "duplex_suite_id": self.duplex_suite_id,
            "session_derivation_rule_id": self.session_derivation_rule_id,
            "salt_policy_id": self.salt_policy_id,
            "composition_context_id": self.composition_context_id,
            "application_authority": self.application_authority.value,
            "decoder": self.decoder.term() if self.decoder is not None else None,
        }

    @property
    def identity(self) -> str:
        return semantic_id("p01.transcript-construction.v3", self.term())


def required_challenge_atoms(
    core: ConversationCore,
) -> tuple[TranscriptAtom, ...] | Result:
    """Derive strong-FS sources; authors cannot opt a prior proof message out."""

    if not isinstance(core, ConversationCore):
        return result(
            Outcome.MALFORMED,
            "transcript-prefix:derivation",
            "P01-FS-DERIVE-001",
            "strong-FS source derivation requires a ConversationCore",
        )
    try:
        schedule = core.schedule
        if CHALLENGE not in schedule:
            raise KeyError(CHALLENGE)
        challenge_position = schedule.index(CHALLENGE)
        proof_messages = core.proof_messages
        prior_messages = tuple(
            occurrence
            for occurrence in schedule[:challenge_position]
            if occurrence in proof_messages
        )
        return tuple(
            TranscriptAtom(
                "InitialStatement",
                occurrence,
                core.contract_for(occurrence).value_domain_id,
                core.contract_for(occurrence).codec,
            )
            for occurrence in core.public_statements
        ) + tuple(
            TranscriptAtom(
                "PriorProofMessage",
                occurrence,
                core.contract_for(occurrence).value_domain_id,
                core.contract_for(occurrence).codec,
            )
            for occurrence in prior_messages
        )
    except (AttributeError, KeyError, TypeError, ValueError):
        return result(
            Outcome.MISSING_DEPENDENCY,
            "transcript-prefix:derivation",
            "P01-FS-DERIVE-001",
            "required typed challenge prefix is absent or malformed",
        )


def canonical_transcript_construction(
    core: ConversationCore,
    profile: AlgebraProfile,
) -> TranscriptConstruction:
    if not isinstance(profile, AlgebraProfile) or profile.challenge_size != 8:
        raise ValueError("P01 FS v3 is defined only for the exact mod-8 profile")
    atoms = required_challenge_atoms(core)
    if isinstance(atoms, Result):
        raise ValueError(atoms.detail)
    fresh, source_basis_id = _canonical_fresh_basis(core, profile)
    return TranscriptConstruction(
        core_id=core.identity,
        suite_domain="zkc/p01/minimal-schnorr/fs/v3",
        runtime_context=canonical_runtime_context_contract(),
        atoms=atoms,
        challenge_occurrence=CHALLENGE,
        challenge_namespace="zkc/p01/schnorr/challenge/c/v2",
        framing="typed-length-delimited.v1",
        sampler="shake128-one-byte-mod-8.v1",
        source_fresh_protocol_id=canonical_source_fresh_protocol_id(
            core, profile, fresh
        ),
        source_fresh_realization_id=fresh.identity,
        source_public_coin_basis_id=source_basis_id,
        language_id=p01_language_id(profile),
        argument_system_id=p01_argument_system_id(core, profile, fresh),
        application_domain_id=p01_application_domain_id(),
        proof_flavor_id=p01_proof_flavor_id(core, profile),
        duplex_suite_id=p01_duplex_suite_id(),
        session_derivation_rule_id=p01_session_derivation_rule_id(),
        salt_policy_id=p01_salt_policy_id(),
        composition_context_id=p01_composition_context_id(),
        application_authority=ApplicationContextAuthority.APPLICATION,
        decoder=canonical_challenge_decoder_contract(profile),
    )


def admit_transcript_construction(
    construction: TranscriptConstruction,
    core: ConversationCore,
    profile: AlgebraProfile,
    *,
    source_fresh: FreshRealization | None = None,
) -> Result:
    if not isinstance(construction, TranscriptConstruction):
        return result(
            Outcome.MALFORMED,
            "transcript-construction",
            "P01-FS-000",
            "transcript construction has the wrong type",
        )
    if (
        not isinstance(construction.core_id, str)
        or not isinstance(construction.suite_domain, str)
        or not isinstance(construction.runtime_context, RuntimeContextContract)
        or not isinstance(construction.runtime_context.source, str)
        or not isinstance(construction.runtime_context.semantic_purpose, str)
        or not isinstance(construction.runtime_context.value_domain_id, str)
        or not isinstance(construction.runtime_context.codec, str)
        or not isinstance(construction.atoms, tuple)
        or any(
            not isinstance(atom, TranscriptAtom)
            or not isinstance(atom.source_kind, str)
            or not isinstance(atom.occurrence, str)
            or not isinstance(atom.value_domain_id, str)
            or not isinstance(atom.codec, str)
            for atom in construction.atoms
        )
        or not isinstance(construction.challenge_occurrence, str)
        or not isinstance(construction.challenge_namespace, str)
        or not isinstance(construction.framing, str)
        or not isinstance(construction.sampler, str)
        or not isinstance(construction.model, str)
        or not isinstance(construction.source_fresh_protocol_id, str)
        or not isinstance(construction.source_fresh_realization_id, str)
        or not isinstance(construction.source_public_coin_basis_id, str)
        or not isinstance(construction.language_id, str)
        or not isinstance(construction.argument_system_id, str)
        or not isinstance(construction.application_domain_id, str)
        or not isinstance(construction.proof_flavor_id, str)
        or not isinstance(construction.duplex_suite_id, str)
        or not isinstance(construction.session_derivation_rule_id, str)
        or not isinstance(construction.salt_policy_id, str)
        or not isinstance(construction.composition_context_id, str)
        or not isinstance(
            construction.application_authority, ApplicationContextAuthority
        )
        or not isinstance(construction.decoder, ChallengeDecoderContract)
        or not isinstance(construction.decoder.squeeze_bytes, int)
        or isinstance(construction.decoder.squeeze_bytes, bool)
        or not isinstance(construction.decoder.byte_order, str)
        or not isinstance(construction.decoder.reduction, str)
        or not isinstance(construction.decoder.modulus, int)
        or isinstance(construction.decoder.modulus, bool)
        or not isinstance(construction.decoder.codomain_id, str)
        or any(
            not isinstance(value, int) or isinstance(value, bool)
            for value in (
                construction.decoder.bias_numerator,
                construction.decoder.bias_denominator,
                construction.decoder.failure_numerator,
                construction.decoder.failure_denominator,
            )
        )
    ):
        return result(
            Outcome.MALFORMED,
            "transcript-construction",
            "P01-FS-000",
            "transcript construction fields are outside the closed typed grammar",
        )
    static_identity_fields = (
        construction.core_id,
        construction.source_fresh_protocol_id,
        construction.source_fresh_realization_id,
        construction.source_public_coin_basis_id,
        construction.language_id,
        construction.argument_system_id,
        construction.application_domain_id,
        construction.proof_flavor_id,
        construction.duplex_suite_id,
        construction.session_derivation_rule_id,
        construction.salt_policy_id,
        construction.composition_context_id,
        construction.decoder.codomain_id,
    )
    if any(not identity for identity in static_identity_fields):
        return result(
            Outcome.MALFORMED,
            "transcript-construction:static-identities",
            "P01-FS-020",
            "transcript construction is missing a required static semantic identity",
        )
    if (
        len(construction.atoms) > 32
        or not _bounded_text(construction.core_id, 128)
        or not _bounded_text(construction.suite_domain)
        or not _bounded_text(construction.runtime_context.source)
        or not _bounded_text(
            construction.runtime_context.semantic_purpose, 128
        )
        or not _bounded_text(
            construction.runtime_context.value_domain_id, 128
        )
        or not _bounded_text(construction.runtime_context.codec, 128)
        or any(
            not _bounded_text(atom.source_kind, 128)
            or not _bounded_text(atom.occurrence)
            or not _bounded_text(atom.value_domain_id, 128)
            or not _bounded_text(atom.codec, 128)
            for atom in construction.atoms
        )
        or not _bounded_text(construction.challenge_occurrence)
        or not _bounded_text(construction.challenge_namespace)
        or not _bounded_text(construction.framing, 128)
        or not _bounded_text(construction.sampler, 128)
        or not _bounded_text(construction.model, 128)
        or any(
            not _bounded_text(identity, 128)
            for identity in (
                construction.source_fresh_protocol_id,
                construction.source_fresh_realization_id,
                construction.source_public_coin_basis_id,
                construction.language_id,
                construction.argument_system_id,
                construction.application_domain_id,
                construction.proof_flavor_id,
                construction.duplex_suite_id,
                construction.session_derivation_rule_id,
                construction.salt_policy_id,
                construction.composition_context_id,
                construction.decoder.codomain_id,
            )
        )
        or not _bounded_text(construction.decoder.byte_order, 32)
        or not _bounded_text(construction.decoder.reduction, 128)
        or any(
            value < 0 or value.bit_length() > 16
            for value in (
                construction.decoder.squeeze_bytes,
                construction.decoder.modulus,
                construction.decoder.bias_numerator,
                construction.decoder.bias_denominator,
                construction.decoder.failure_numerator,
                construction.decoder.failure_denominator,
            )
        )
    ):
        return result(
            Outcome.RESOURCE_EXCEEDED,
            "transcript-construction:finite-evaluator-bound",
            "P01-FS-018",
            "transcript construction exceeds the explicit finite evaluator bounds",
        )
    if any(
        not _closed_content_id(identity) for identity in static_identity_fields
    ):
        return result(
            Outcome.MALFORMED,
            "transcript-construction:static-identities",
            "P01-FS-020",
            "transcript construction contains a malformed static semantic identity",
        )
    public_coin_result = check_public_coin_eligibility(core, profile)
    if public_coin_result.outcome is not Outcome.AFFIRMATIVE:
        return public_coin_result
    correspondence_result = check_schnorr_correspondence(core, profile)
    if correspondence_result.outcome is not Outcome.AFFIRMATIVE:
        return correspondence_result
    if construction.core_id != core.identity:
        return result(
            Outcome.MISMATCH,
            "transcript-construction:scope",
            "P01-FS-001",
            "transcript construction has the wrong conversation Core",
            subject=construction.identity,
        )
    if construction.model != "StrongFiatShamirTranscriptConstruction.v3":
        return result(
            Outcome.UNSUPPORTED,
            "transcript-construction:model",
            "P01-FS-004",
            "transcript-construction model is unsupported",
            subject=construction.identity,
        )
    try:
        suite_domain_bytes = construction.suite_domain.encode("ascii")
    except UnicodeEncodeError:
        suite_domain_bytes = b""
    if (
        not suite_domain_bytes
        or len(suite_domain_bytes) > 256
        or construction.suite_domain
        != "zkc/p01/minimal-schnorr/fs/v3"
    ):
        return result(
            Outcome.SEMANTIC_NEGATIVE,
            "transcript-initialization:suite-domain",
            "P01-FS-019",
            "construction does not bind the exact fixed FS suite domain",
            subject=construction.identity,
        )
    try:
        expected_fresh, expected_source_basis_id = _canonical_fresh_basis(
            core, profile
        )
    except (AttributeError, TermEncodingError, TypeError, ValueError) as error:
        return result(
            Outcome.CHECKER_FAILURE,
            "transcript-construction:source-public-coin-basis",
            "P01-FS-DERIVE-003",
            "admitted Core did not yield a closed source Fresh basis",
            subject=construction.identity,
            cause=str(error),
        )
    admitted_source_fresh = (
        expected_fresh if source_fresh is None else source_fresh
    )
    fresh_result = admit_fresh_realization(admitted_source_fresh, core, profile)
    if fresh_result.outcome is not Outcome.AFFIRMATIVE:
        return fresh_result
    if admitted_source_fresh.identity != expected_fresh.identity:
        return result(
            Outcome.MISMATCH,
            "transcript-construction:source-public-coin-basis",
            "P01-FS-021",
            "supplied Fresh realization is not the exact canonical source basis",
            subject=construction.identity,
            expected_fresh_realization_id=expected_fresh.identity,
            actual_fresh_realization_id=admitted_source_fresh.identity,
        )
    actual_source_basis_id = source_public_coin_basis_id(
        admitted_source_fresh, core, profile
    )
    expected_source_protocol_id = canonical_source_fresh_protocol_id(
        core, profile, expected_fresh
    )
    if (
        construction.source_fresh_protocol_id != expected_source_protocol_id
        or construction.source_fresh_realization_id != expected_fresh.identity
        or construction.source_public_coin_basis_id != expected_source_basis_id
        or actual_source_basis_id != expected_source_basis_id
    ):
        return result(
            Outcome.MISMATCH,
            "transcript-construction:source-public-coin-basis",
            "P01-FS-021",
            "construction does not bind the exact admitted Fresh realization "
            "and conditional kernel basis",
            subject=construction.identity,
            expected_fresh_protocol_id=expected_source_protocol_id,
            expected_fresh_realization_id=expected_fresh.identity,
            expected_source_public_coin_basis_id=expected_source_basis_id,
        )
    expected_static_ids = (
        p01_language_id(profile),
        p01_argument_system_id(core, profile, expected_fresh),
        p01_application_domain_id(),
        p01_proof_flavor_id(core, profile),
        p01_duplex_suite_id(),
        p01_session_derivation_rule_id(),
        p01_salt_policy_id(),
        p01_composition_context_id(),
    )
    actual_static_ids = (
        construction.language_id,
        construction.argument_system_id,
        construction.application_domain_id,
        construction.proof_flavor_id,
        construction.duplex_suite_id,
        construction.session_derivation_rule_id,
        construction.salt_policy_id,
        construction.composition_context_id,
    )
    if actual_static_ids != expected_static_ids:
        return result(
            Outcome.SEMANTIC_NEGATIVE,
            "transcript-initialization:static-context",
            "P01-FS-022",
            "language, argument, application, proof flavor, duplex, session, "
            "salt, or composition identity differs from P01 FS v3",
            subject=construction.identity,
            expected_static_ids=expected_static_ids,
        )
    if (
        construction.application_authority
        is not ApplicationContextAuthority.APPLICATION
    ):
        return result(
            Outcome.SEMANTIC_NEGATIVE,
            "transcript-initialization:application-authority",
            "P01-FS-023",
            "runtime application context is not owned by the application boundary",
            subject=construction.identity,
        )
    if construction.runtime_context != canonical_runtime_context_contract():
        return result(
            Outcome.SEMANTIC_NEGATIVE,
            "transcript-initialization:application-context",
            "P01-FS-017",
            "construction does not own the exact typed runtime application-context contract",
            subject=construction.identity,
        )
    expected_atoms = required_challenge_atoms(core)
    if isinstance(expected_atoms, Result):
        return result(
            Outcome.CHECKER_FAILURE,
            "transcript-prefix:derivation",
            "P01-FS-DERIVE-002",
            "admitted source correspondence did not yield a challenge prefix",
            subject=construction.identity,
            cause=expected_atoms.term(),
        )
    if construction.atoms != expected_atoms:
        if len(set(construction.atoms)) != len(construction.atoms):
            return result(
                Outcome.SEMANTIC_NEGATIVE,
                "transcript-prefix:challenge:c",
                "P01-FS-008",
                "challenge prefix duplicates a source",
                subject=construction.identity,
            )
        missing = tuple(
            atom for atom in expected_atoms if atom not in construction.atoms
        )
        extra = tuple(
            atom for atom in construction.atoms if atom not in expected_atoms
        )
        if len(construction.atoms) < len(expected_atoms) and missing:
            return result(
                Outcome.SEMANTIC_NEGATIVE,
                "transcript-prefix:challenge:c",
                "P01-FS-005",
                "a required challenge source is missing",
                subject=construction.identity,
                expected_source=missing[0].occurrence,
            )
        for index, expected in enumerate(expected_atoms):
            actual = construction.atoms[index]
            if actual.occurrence != expected.occurrence:
                boundary = (
                    "transcript-prefix:ordered-exactness:c"
                    if not extra
                    else "transcript-atom:typed-occurrence-source"
                )
                return result(
                    Outcome.SEMANTIC_NEGATIVE,
                    boundary,
                    "P01-FS-006",
                    "challenge atom cites the wrong occurrence or order",
                    subject=construction.identity,
                    expected_source=expected.occurrence,
                    actual_source=actual.occurrence,
                )
            if actual != expected:
                return result(
                    Outcome.SEMANTIC_NEGATIVE,
                    "transcript-atom:typed-occurrence-source",
                    "P01-FS-007",
                    "challenge atom has the wrong kind, domain, or codec",
                    subject=construction.identity,
                )
        return result(
            Outcome.SEMANTIC_NEGATIVE,
            "transcript-prefix:challenge:c",
            "P01-FS-008",
            "challenge prefix has extra or duplicated sources",
            subject=construction.identity,
        )
    if construction.challenge_occurrence != CHALLENGE:
        return result(
            Outcome.MISMATCH,
            "transcript-construction:challenge",
            "P01-FS-010",
            "construction derives the wrong challenge occurrence",
            subject=construction.identity,
        )
    try:
        namespace_bytes = construction.challenge_namespace.encode("ascii")
    except (AttributeError, UnicodeEncodeError):
        namespace_bytes = b""
    if (
        not namespace_bytes
        or len(namespace_bytes) > 256
        or construction.challenge_namespace
        != "zkc/p01/schnorr/challenge/c/v2"
        or construction.challenge_namespace in {
            STATEMENT,
            COMMITMENT,
            RESPONSE,
        }
    ):
        return result(
            Outcome.SEMANTIC_NEGATIVE,
            "squeeze-sample:namespace",
            "P01-FS-011",
            "challenge occurrence namespace is not the exact P01 FS v3 namespace",
            subject=construction.identity,
        )
    if construction.framing != "typed-length-delimited.v1":
        return result(
            Outcome.SEMANTIC_NEGATIVE,
            "transcript-framing:injectivity",
            "P01-FS-012",
            "transcript framing is not the pinned injective framing",
            subject=construction.identity,
        )
    if construction.sampler != "shake128-one-byte-mod-8.v1":
        return result(
            Outcome.UNSUPPORTED,
            "squeeze-sample:algorithm",
            "P01-FS-013",
            "squeeze/sample algorithm is unsupported",
            subject=construction.identity,
        )
    expected_decoder = canonical_challenge_decoder_contract(profile)
    if profile.challenge_size != 8 or construction.decoder != expected_decoder:
        return result(
            Outcome.SEMANTIC_NEGATIVE,
            "squeeze-sample:decoder-contract",
            "P01-FS-025",
            "P01 FS v3 requires the exact one-byte, little-endian, zero-bias "
            "mod-8 decoder with zero failure",
            subject=construction.identity,
            expected_decoder_id=expected_decoder.identity,
        )
    return affirmative(
        "transcript-construction",
        "P01-FS-OK",
        "strong statement- and commitment-bound construction is admitted",
        subject=construction.identity,
        required_sources=[atom.occurrence for atom in expected_atoms],
        runtime_context_contract_id=construction.runtime_context.identity,
        source_fresh_protocol_id=expected_source_protocol_id,
        source_fresh_realization_id=expected_fresh.identity,
        source_public_coin_basis_id=expected_source_basis_id,
        challenge_decoder_contract_id=expected_decoder.identity,
        decoder_distribution="ExactUniformOn[0,8)",
        decoder_failure_probability="0",
        self_binding_law=(
            "the construction identity is bound by query execution, never "
            "stored in its own preimage"
        ),
        theorem_non_claim=(
            "construction admission grants no ROM, QROM, knowledge-soundness, "
            "or zero-knowledge theorem"
        ),
    )


@dataclass(frozen=True)
class ProtocolVariant:
    core_id: str
    honest_prover_contract_id: str
    realization_kind: RealizationKind
    realization_id: str

    def term(self) -> dict[str, str]:
        return {
            "core_id": self.core_id,
            "honest_prover_contract_id": self.honest_prover_contract_id,
            "realization_kind": self.realization_kind.value,
            "realization_id": self.realization_id,
        }

    @property
    def identity(self) -> str:
        return semantic_id("p01.protocol-variant.v2", self.term())


def admit_fresh_realization(
    fresh: FreshRealization,
    core: ConversationCore,
    profile: AlgebraProfile,
) -> Result:
    if not isinstance(fresh, FreshRealization):
        return result(
            Outcome.MALFORMED,
            "fresh-realization",
            "P01-FRESH-000",
            "Fresh realization has the wrong type",
        )
    if (
        not isinstance(fresh.core_id, str)
        or not isinstance(fresh.conditional_kernel_contract_id, str)
        or not isinstance(fresh.challenge_occurrence, str)
        or not isinstance(fresh.resolver, OccurrenceActor)
    ):
        return result(
            Outcome.MALFORMED,
            "fresh-realization",
            "P01-FRESH-000",
            "Fresh realization fields are outside the closed typed grammar",
        )
    if (
        not _closed_content_id(fresh.core_id)
        or not _closed_content_id(fresh.conditional_kernel_contract_id)
        or not _bounded_text(fresh.challenge_occurrence)
    ):
        return result(
            Outcome.MALFORMED,
            "fresh-realization",
            "P01-FRESH-003",
            "Fresh realization contains a malformed identity or occurrence reference",
        )
    public_coin_result = check_public_coin_eligibility(core, profile)
    if public_coin_result.outcome is not Outcome.AFFIRMATIVE:
        return public_coin_result
    if fresh.core_id != core.identity:
        return result(
            Outcome.MISMATCH,
            "fresh-realization:scope",
            "P01-FRESH-001",
            "Fresh realization has the wrong conversation Core",
            subject=fresh.identity,
        )
    expected_kernel = fresh_conditional_kernel_contract_id(core, profile)
    if isinstance(expected_kernel, Result):
        return result(
            Outcome.CHECKER_FAILURE,
            "fresh-realization:kernel-derivation",
            "P01-FRESH-DERIVE-002",
            "admitted Core did not yield a conditional public-coin kernel",
            subject=fresh.identity,
            cause=expected_kernel.term(),
        )
    if (
        fresh.challenge_occurrence != CHALLENGE
        or fresh.resolver is not OccurrenceActor.PUBLIC_ENVIRONMENT
        or fresh.conditional_kernel_contract_id
        != expected_kernel
    ):
        return result(
            Outcome.SEMANTIC_NEGATIVE,
            "fresh-realization:public-coin-contract",
            "P01-FRESH-002",
            "Fresh realization does not name the exact conditional public-coin kernel",
            subject=fresh.identity,
        )
    return affirmative(
        "fresh-realization",
        "P01-FRESH-OK",
        "Fresh realization binds the challenge slot to the exact prefix-conditional public-coin kernel",
        subject=fresh.identity,
        kernel_contract_id=fresh.conditional_kernel_contract_id,
        non_claim="not evidence that any execution sampled from this kernel",
    )


def make_fresh_protocol(
    core: ConversationCore, profile: AlgebraProfile
) -> tuple[ProtocolVariant, FreshRealization]:
    kernel_contract_id = fresh_conditional_kernel_contract_id(core, profile)
    if isinstance(kernel_contract_id, Result):
        raise ValueError(kernel_contract_id.detail)
    realization = FreshRealization(core.identity, kernel_contract_id)
    honest_contract = canonical_honest_prover_contract(core, profile)
    return (
        ProtocolVariant(
            core.identity,
            honest_contract.identity,
            RealizationKind.FRESH,
            realization.identity,
        ),
        realization,
    )


def make_fs_protocol(
    core: ConversationCore,
    construction: TranscriptConstruction,
    profile: AlgebraProfile,
) -> ProtocolVariant:
    honest_contract = canonical_honest_prover_contract(core, profile)
    return ProtocolVariant(
        core.identity,
        honest_contract.identity,
        RealizationKind.FIAT_SHAMIR,
        construction.identity,
    )


def admit_protocol(
    protocol: ProtocolVariant,
    core: ConversationCore,
    profile: AlgebraProfile,
    *,
    fresh: FreshRealization | None = None,
    construction: TranscriptConstruction | None = None,
) -> Result:
    if not isinstance(protocol, ProtocolVariant):
        return result(
            Outcome.MALFORMED,
            "protocol-admission",
            "P01-PROTO-000",
            "Protocol has the wrong type",
        )
    if (
        not isinstance(protocol.core_id, str)
        or not isinstance(protocol.honest_prover_contract_id, str)
        or not isinstance(protocol.realization_kind, RealizationKind)
        or not isinstance(protocol.realization_id, str)
    ):
        return result(
            Outcome.MALFORMED,
            "protocol-admission",
            "P01-PROTO-000",
            "Protocol fields are outside the closed typed grammar",
        )
    if (
        not _closed_content_id(protocol.core_id)
        or not _closed_content_id(protocol.honest_prover_contract_id)
        or not _closed_content_id(protocol.realization_id)
    ):
        return result(
            Outcome.MALFORMED,
            "protocol-admission",
            "P01-PROTO-008",
            "Protocol contains a malformed semantic identity",
        )
    core_result = admit_core(core, profile)
    if core_result.outcome is not Outcome.AFFIRMATIVE:
        return core_result
    public_coin_result = check_public_coin_eligibility(core, profile)
    if public_coin_result.outcome is not Outcome.AFFIRMATIVE:
        return public_coin_result
    correspondence_result = check_schnorr_correspondence(core, profile)
    if correspondence_result.outcome is not Outcome.AFFIRMATIVE:
        return correspondence_result
    if protocol.core_id != core.identity:
        return result(
            Outcome.MISMATCH,
            "protocol-admission:core",
            "P01-PROTO-001",
            "Protocol names the wrong Core",
            subject=protocol.identity,
        )
    honest_contract = canonical_honest_prover_contract(core, profile)
    honest_result = admit_honest_prover_contract(
        honest_contract, core, profile
    )
    if honest_result.outcome is not Outcome.AFFIRMATIVE:
        return honest_result
    if protocol.honest_prover_contract_id != honest_contract.identity:
        return result(
            Outcome.MISMATCH,
            "protocol-admission:honest-prover-contract",
            "P01-PROTO-009",
            "Protocol does not bind the exact Schnorr honest-prover contract",
            subject=protocol.identity,
            expected_honest_prover_contract_id=honest_contract.identity,
        )
    if protocol.realization_kind is RealizationKind.FRESH:
        if (
            not isinstance(fresh, FreshRealization)
            or construction is not None
        ):
            return result(
                Outcome.SEMANTIC_NEGATIVE,
                "challenge-interpretation:construction-closure",
                "P01-PROTO-002",
                "Fresh requires exactly one Fresh realization and no transcript construction",
                subject=protocol.identity,
            )
        fresh_result = admit_fresh_realization(fresh, core, profile)
        if fresh_result.outcome is not Outcome.AFFIRMATIVE:
            return fresh_result
        if protocol.realization_id != fresh.identity:
            return result(
                Outcome.MISMATCH,
                "protocol-admission:fresh-realization",
                "P01-PROTO-003",
                "Fresh realization identity or scope does not match",
                subject=protocol.identity,
            )
    elif protocol.realization_kind is RealizationKind.FIAT_SHAMIR:
        if (
            not isinstance(construction, TranscriptConstruction)
            or fresh is not None
        ):
            return result(
                Outcome.SEMANTIC_NEGATIVE,
                "challenge-interpretation:construction-closure",
                "P01-PROTO-005",
                "Fiat-Shamir requires exactly one transcript construction and no Fresh realization",
                subject=protocol.identity,
            )
        construction_result = admit_transcript_construction(
            construction, core, profile
        )
        if construction_result.outcome is not Outcome.AFFIRMATIVE:
            return construction_result
        if protocol.realization_id != construction.identity:
            return result(
                Outcome.MISMATCH,
                "protocol-admission:fs-realization",
                "P01-PROTO-006",
                "Protocol references a different transcript construction",
                subject=protocol.identity,
            )
    else:
        return result(
            Outcome.UNSUPPORTED,
            "protocol-admission:realization-kind",
            "P01-PROTO-007",
            "challenge realization kind is unsupported",
            subject=protocol.identity,
        )
    return affirmative(
        "protocol-admission",
        "P01-PROTO-OK",
        "Protocol variant is admitted",
        subject=protocol.identity,
        core_id=core.identity,
    )


def checked_fs_factorization(
    fresh_protocol: ProtocolVariant,
    fs_protocol: ProtocolVariant,
    construction: TranscriptConstruction,
    core: ConversationCore,
    profile: AlgebraProfile,
    fresh: FreshRealization,
) -> Result:
    fresh_admission = admit_protocol(
        fresh_protocol,
        core,
        profile,
        fresh=fresh,
    )
    if fresh_admission.outcome is not Outcome.AFFIRMATIVE:
        return fresh_admission
    construction_admission = admit_transcript_construction(
        construction,
        core,
        profile,
        source_fresh=fresh,
    )
    if construction_admission.outcome is not Outcome.AFFIRMATIVE:
        return construction_admission
    fs_admission = admit_protocol(
        fs_protocol,
        core,
        profile,
        construction=construction,
    )
    if fs_admission.outcome is not Outcome.AFFIRMATIVE:
        return fs_admission
    if fresh_protocol.realization_kind is not RealizationKind.FRESH:
        return result(
            Outcome.MISMATCH,
            "relations:fresh-fs-factorization",
            "P01-FACT-001",
            "source is not Fresh",
        )
    if fs_protocol.realization_kind is not RealizationKind.FIAT_SHAMIR:
        return result(
            Outcome.MISMATCH,
            "relations:fresh-fs-factorization",
            "P01-FACT-002",
            "target is not Fiat-Shamir",
        )
    if fresh_protocol.core_id != fs_protocol.core_id:
        return result(
            Outcome.SEMANTIC_NEGATIVE,
            "relations:fresh-fs-factorization",
            "P01-FACT-003",
            "Fresh and FS variants do not share one Core",
        )
    if (
        fresh_protocol.honest_prover_contract_id
        != fs_protocol.honest_prover_contract_id
    ):
        return result(
            Outcome.SEMANTIC_NEGATIVE,
            "relations:fresh-fs-factorization",
            "P01-FACT-005",
            "Fresh and FS variants do not share one honest-prover contract",
        )
    if (
        construction.core_id != fresh_protocol.core_id
        or construction.source_fresh_protocol_id != fresh_protocol.identity
        or construction.source_fresh_realization_id != fresh.identity
        or construction.source_public_coin_basis_id
        != source_public_coin_basis_id(fresh, core, profile)
        or fs_protocol.realization_id != construction.identity
    ):
        return result(
            Outcome.MISMATCH,
            "relations:fresh-fs-factorization",
            "P01-FACT-004",
            "construction does not realize the exact target over the admitted "
            "Fresh basis and shared Core",
        )
    factorization_id = semantic_id(
        "p01.checked-fs-factorization.v2",
        {
            "fresh": fresh_protocol.identity,
            "fs": fs_protocol.identity,
            "core": fresh_protocol.core_id,
            "honest_prover_contract": fresh_protocol.honest_prover_contract_id,
            "construction": construction.identity,
            "source_fresh_protocol": construction.source_fresh_protocol_id,
            "source_public_coin_basis": construction.source_public_coin_basis_id,
        },
    )
    return affirmative(
        "relations:fresh-fs-factorization",
        "P01-FACT-OK",
        "Fresh and FS are distinct variants over one neutral Core",
        subject=factorization_id,
        fresh_protocol_id=fresh_protocol.identity,
        fs_protocol_id=fs_protocol.identity,
        core_id=fresh_protocol.core_id,
        honest_prover_contract_id=fresh_protocol.honest_prover_contract_id,
        source_fresh_protocol_id=construction.source_fresh_protocol_id,
        source_public_coin_basis_id=construction.source_public_coin_basis_id,
    )


def _transcript_state(
    construction: TranscriptConstruction,
    profile: AlgebraProfile,
    application_context: str,
    statement: int,
    commitment: int,
) -> tuple[_Shake128Duplex, tuple[dict[str, Any], ...]]:
    """Execute the exact P01 v3 Init/Absorb prefix up to its one squeeze."""

    execution_core = canonical_core(profile)
    construction_result = admit_transcript_construction(
        construction,
        execution_core,
        profile,
    )
    if construction_result.outcome is not Outcome.AFFIRMATIVE:
        raise ValueError(
            "challenge execution requires an admitted P01 FS v3 construction: "
            f"{construction_result.code}"
        )
    context_result = admit_application_context(application_context)
    if context_result.outcome is not Outcome.AFFIRMATIVE:
        raise ValueError(context_result.detail)
    context_bytes = application_context.encode("utf-8")
    statement_bytes = profile.encode_group(statement)
    commitment_bytes = profile.encode_group(commitment)
    tag = (
        _frame("construction-id", construction.identity.encode("ascii"))
        + _frame(
            "runtime-context-contract-id",
            construction.runtime_context.identity.encode("ascii"),
        )
        + _frame("runtime-context-value", context_bytes)
    )
    session_id = _derive_cfrg_session_id(tag)
    state = _Shake128Duplex(session_id)
    atom_values = {
        STATEMENT: statement_bytes,
        COMMITMENT: commitment_bytes,
    }
    receipts: list[dict[str, Any]] = []
    for atom in construction.atoms:
        payload = atom_values[atom.occurrence]
        label = (
            f"{atom.source_kind}:{atom.occurrence}:"
            f"{atom.value_domain_id}:{atom.codec}"
        )
        encoded = _frame(label, payload)
        state.absorb(encoded)
        receipts.append(
            {
                "source_kind": atom.source_kind,
                "occurrence": atom.occurrence,
                "value_domain_id": atom.value_domain_id,
                "codec": atom.codec,
                "encoded_hex": encoded.hex(),
            }
        )
    return state, tuple(receipts)


def transcript_query(
    construction: TranscriptConstruction,
    profile: AlgebraProfile,
    application_context: str,
    statement: int,
    commitment: int,
) -> tuple[bytes, tuple[dict[str, Any], ...]]:
    """Return the exact bytes absorbed by the P01 v3 challenge XOF state."""

    state, receipts = _transcript_state(
        construction,
        profile,
        application_context,
        statement,
        commitment,
    )
    return state.absorbed_bytes, receipts


def derive_fs_challenge(
    construction: TranscriptConstruction,
    profile: AlgebraProfile,
    application_context: str,
    statement: int,
    commitment: int,
) -> tuple[int, bytes, tuple[dict[str, Any], ...]]:
    if (
        profile.challenge_size != 8
        or construction.decoder != canonical_challenge_decoder_contract(profile)
        or construction.sampler != "shake128-one-byte-mod-8.v1"
    ):
        raise ValueError(
            "challenge execution requires the exact admitted mod-8 decoder"
        )
    state, receipts = _transcript_state(
        construction,
        profile,
        application_context,
        statement,
        commitment,
    )
    query = state.absorbed_bytes
    squeezed = state.squeeze(construction.decoder.squeeze_bytes)
    sampled_word = int.from_bytes(
        squeezed,
        "little",
    )
    challenge = sampled_word % construction.decoder.modulus
    if not profile.valid_challenge(challenge):
        raise AssertionError("pinned one-byte mod-8 decoder escaped its codomain")
    return challenge, query, receipts


def mutate_core(core: ConversationCore, **changes: Any) -> ConversationCore:
    """Test-only canonical rebuild helper; identities are always recomputed."""

    return replace(core, **changes)


def mutate_construction(
    construction: TranscriptConstruction, **changes: Any
) -> TranscriptConstruction:
    """Test-only canonical rebuild helper; identities are always recomputed."""

    return replace(construction, **changes)
