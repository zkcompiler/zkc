"""Minimal noninteractive proof interface for the finite P01 FS protocol.

The interface serializes exactly the two prover messages ``(A, z)``.  The
runtime application context and Schnorr Statement are external inputs, while
the challenge is always recomputed by the admitted transcript construction.
There is no API parameter, proof field, or fallback path for a caller-supplied
challenge.

This module owns only the finite proof ABI and verification routing.  It binds
the verifier-check and terminal contract identities already owned by the
``ConversationCore``; it does not mint duplicate equation or terminal
identities, and it makes no general Fiat--Shamir or security claim.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Any

from .semantic import (
    CHALLENGE,
    CHECK,
    COMMITMENT,
    RESPONSE,
    STATEMENT,
    TERMINAL,
    AlgebraProfile,
    ConversationCore,
    ProtocolVariant,
    RealizationKind,
    TranscriptConstruction,
    admit_application_context,
    admit_protocol,
    derive_fs_challenge,
    group_domain_id,
    scalar_domain_id,
)
from .terms import Outcome, Result, TermEncodingError, affirmative, result, semantic_id


_SERIALIZATION = "exact-fixed-width-product.v1"
_MODEL = "FiatShamirProofInterface.v1"


@dataclass(frozen=True)
class ExternalInputSpec:
    occurrence: str
    value_domain_id: str
    codec: str

    def term(self) -> dict[str, str]:
        return {
            "occurrence": self.occurrence,
            "value_domain_id": self.value_domain_id,
            "codec": self.codec,
        }


@dataclass(frozen=True)
class ProofFieldSpec:
    occurrence: str
    value_domain_id: str
    codec: str
    width: int

    def term(self) -> dict[str, Any]:
        return {
            "occurrence": self.occurrence,
            "value_domain_id": self.value_domain_id,
            "codec": self.codec,
            "width": self.width,
        }


@dataclass(frozen=True)
class ChallengeRecomputationSpec:
    occurrence: str
    construction_id: str
    runtime_sources: tuple[str, ...]

    def term(self) -> dict[str, Any]:
        return {
            "occurrence": self.occurrence,
            "construction_id": self.construction_id,
            "runtime_sources": list(self.runtime_sources),
        }


@dataclass(frozen=True)
class FiatShamirProofInterface:
    """Identity-bearing ABI bound to one admitted finite FS Protocol."""

    protocol_id: str
    core_id: str
    algebra_profile_id: str
    construction_id: str
    external_inputs: tuple[ExternalInputSpec, ...]
    proof_fields: tuple[ProofFieldSpec, ...]
    challenge_recomputation: ChallengeRecomputationSpec
    verifier_check_occurrence: str
    verifier_check_contract_id: str
    terminal_occurrence: str
    terminal_contract_id: str
    serialization: str = _SERIALIZATION
    model: str = _MODEL

    def term(self) -> dict[str, Any]:
        return {
            "model": self.model,
            "protocol_id": self.protocol_id,
            "core_id": self.core_id,
            "algebra_profile_id": self.algebra_profile_id,
            "construction_id": self.construction_id,
            "external_inputs": [item.term() for item in self.external_inputs],
            "proof_fields": [field.term() for field in self.proof_fields],
            "challenge_recomputation": self.challenge_recomputation.term(),
            "verifier_check_occurrence": self.verifier_check_occurrence,
            "verifier_check_contract_id": self.verifier_check_contract_id,
            "terminal_occurrence": self.terminal_occurrence,
            "terminal_contract_id": self.terminal_contract_id,
            "serialization": self.serialization,
        }

    @property
    def identity(self) -> str:
        return semantic_id("p01.fs-proof-interface.v1", self.term())

    @property
    def proof_width(self) -> int:
        return sum(field.width for field in self.proof_fields)


def canonical_fs_proof_interface(
    protocol: ProtocolVariant,
    construction: TranscriptConstruction,
    core: ConversationCore,
    profile: AlgebraProfile,
) -> FiatShamirProofInterface:
    """Construct the sole P01 FS proof ABI; admission remains separate."""

    return FiatShamirProofInterface(
        protocol_id=protocol.identity,
        core_id=core.identity,
        algebra_profile_id=profile.identity,
        construction_id=construction.identity,
        external_inputs=(
            ExternalInputSpec(
                construction.runtime_context.source,
                construction.runtime_context.value_domain_id,
                construction.runtime_context.codec,
            ),
            ExternalInputSpec(
                STATEMENT,
                group_domain_id(profile),
                core.contract_for(STATEMENT).codec,
            ),
        ),
        proof_fields=(
            ProofFieldSpec(
                COMMITMENT,
                group_domain_id(profile),
                core.contract_for(COMMITMENT).codec,
                profile.group_width,
            ),
            ProofFieldSpec(
                RESPONSE,
                scalar_domain_id(profile),
                core.contract_for(RESPONSE).codec,
                profile.scalar_width,
            ),
        ),
        challenge_recomputation=ChallengeRecomputationSpec(
            CHALLENGE,
            construction.identity,
            (construction.runtime_context.source, STATEMENT, COMMITMENT),
        ),
        verifier_check_occurrence=core.verifier_check.output_occurrence,
        verifier_check_contract_id=core.verifier_check.semantic_contract_id,
        terminal_occurrence=core.terminal_route.output_occurrence,
        terminal_contract_id=core.terminal_route.semantic_contract_id,
    )


def _safe_interface_id(value: Any) -> str:
    try:
        identity = value.identity
    except (AttributeError, TermEncodingError, TypeError, ValueError):
        return ""
    return identity if isinstance(identity, str) else ""


def _operand_type_failure(
    interface: Any,
    protocol: Any,
    construction: Any,
    core: Any,
    profile: Any,
    *,
    boundary: str,
) -> Result | None:
    expected = (
        (interface, FiatShamirProofInterface, "interface"),
        (protocol, ProtocolVariant, "protocol"),
        (construction, TranscriptConstruction, "construction"),
        (core, ConversationCore, "core"),
        (profile, AlgebraProfile, "profile"),
    )
    wrong = tuple(name for value, kind, name in expected if not isinstance(value, kind))
    if not wrong:
        return None
    return result(
        Outcome.MALFORMED,
        boundary,
        "P01-IFACE-000",
        "FS proof-interface operation has a raw operand of the wrong type",
        wrong_operands=list(wrong),
    )


def admit_fs_proof_interface(
    interface: FiatShamirProofInterface,
    protocol: ProtocolVariant,
    construction: TranscriptConstruction,
    core: ConversationCore,
    profile: AlgebraProfile,
) -> Result:
    """Admit the exact external-input, proof-byte, and verifier bindings."""

    type_failure = _operand_type_failure(
        interface,
        protocol,
        construction,
        core,
        profile,
        boundary="fs-proof-interface:admission",
    )
    if type_failure is not None:
        return type_failure
    nested_values = (
        isinstance(interface.external_inputs, tuple)
        and all(isinstance(item, ExternalInputSpec) for item in interface.external_inputs)
        and isinstance(interface.proof_fields, tuple)
        and all(isinstance(item, ProofFieldSpec) for item in interface.proof_fields)
        and isinstance(
            interface.challenge_recomputation, ChallengeRecomputationSpec
        )
    )
    if not nested_values:
        return result(
            Outcome.MALFORMED,
            "fs-proof-interface:admission:shape",
            "P01-IFACE-001",
            "FS proof interface has malformed nested vocabulary",
            subject=_safe_interface_id(interface),
        )
    protocol_result = admit_protocol(
        protocol,
        core,
        profile,
        construction=construction,
    )
    if protocol_result.outcome is not Outcome.AFFIRMATIVE:
        return protocol_result
    interface_id = _safe_interface_id(interface)
    if not interface_id:
        return result(
            Outcome.MALFORMED,
            "fs-proof-interface:admission:identity",
            "P01-IFACE-002",
            "FS proof interface has no closed semantic identity",
        )
    if protocol.realization_kind is not RealizationKind.FIAT_SHAMIR:
        return result(
            Outcome.SEMANTIC_NEGATIVE,
            "fs-proof-interface:admission:realization",
            "P01-IFACE-003",
            "noninteractive proof interface requires an admitted Fiat-Shamir Protocol",
            subject=interface_id,
        )
    expected = canonical_fs_proof_interface(protocol, construction, core, profile)
    if (
        interface.protocol_id != protocol.identity
        or interface.core_id != core.identity
        or interface.algebra_profile_id != profile.identity
        or interface.construction_id != construction.identity
    ):
        return result(
            Outcome.MISMATCH,
            "fs-proof-interface:admission:scope",
            "P01-IFACE-004",
            "interface does not bind the exact Protocol, Core, construction, and algebra profile",
            subject=interface_id,
            expected_interface_id=expected.identity,
        )
    if interface.external_inputs != expected.external_inputs:
        return result(
            Outcome.SEMANTIC_NEGATIVE,
            "fs-proof-interface:admission:external-inputs",
            "P01-IFACE-005",
            "external inputs are not exactly runtime application context followed by Statement",
            subject=interface_id,
        )
    if interface.proof_fields != expected.proof_fields:
        return result(
            Outcome.SEMANTIC_NEGATIVE,
            "fs-proof-interface:admission:proof-abi",
            "P01-IFACE-006",
            "proof ABI is not exactly fixed-width commitment followed by response",
            subject=interface_id,
            expected_width=expected.proof_width,
        )
    if interface.challenge_recomputation != expected.challenge_recomputation:
        return result(
            Outcome.SEMANTIC_NEGATIVE,
            "fs-proof-interface:admission:challenge",
            "P01-IFACE-007",
            "challenge is not the exact construction-derived value over context, Statement, and commitment",
            subject=interface_id,
        )
    if (
        interface.verifier_check_occurrence != expected.verifier_check_occurrence
        or interface.verifier_check_contract_id
        != expected.verifier_check_contract_id
        or interface.terminal_occurrence != expected.terminal_occurrence
        or interface.terminal_contract_id != expected.terminal_contract_id
    ):
        return result(
            Outcome.MISMATCH,
            "fs-proof-interface:admission:verifier-routing",
            "P01-IFACE-008",
            "interface does not reference the Core-owned check and terminal contracts exactly",
            subject=interface_id,
        )
    if interface.serialization != _SERIALIZATION or interface.model != _MODEL:
        return result(
            Outcome.UNSUPPORTED,
            "fs-proof-interface:admission:serialization",
            "P01-IFACE-009",
            "proof-interface model or serialization law is unsupported",
            subject=interface_id,
        )
    if interface != expected:
        return result(
            Outcome.SEMANTIC_NEGATIVE,
            "fs-proof-interface:admission:exactness",
            "P01-IFACE-010",
            "interface differs from the complete canonical FS proof interface",
            subject=interface_id,
            expected_interface_id=expected.identity,
        )
    return affirmative(
        "fs-proof-interface:admission",
        "P01-IFACE-OK",
        "minimal FS proof interface is admitted",
        subject=interface_id,
        protocol_id=protocol.identity,
        proof_fields=(COMMITMENT, RESPONSE),
        serialized_challenge=False,
        proof_width=interface.proof_width,
        verifier_check_contract_id=interface.verifier_check_contract_id,
        terminal_contract_id=interface.terminal_contract_id,
    )


@dataclass(frozen=True)
class FSExternalInputs:
    interface_id: str
    application_context: str
    statement: int

    def term(self) -> dict[str, Any]:
        return {
            "interface_id": self.interface_id,
            "application_context": self.application_context,
            "statement": self.statement,
        }

    @property
    def identity(self) -> str:
        return semantic_id("p01.fs-external-inputs.v1", self.term())


def _check_fs_external_input_shape(
    external_inputs: FSExternalInputs,
    interface: FiatShamirProofInterface,
    profile: AlgebraProfile,
) -> Result:
    if not isinstance(external_inputs, FSExternalInputs):
        return result(
            Outcome.MALFORMED,
            "fs-proof-interface:external-inputs",
            "P01-INPUT-001",
            "external inputs have the wrong type",
        )
    if not isinstance(interface, FiatShamirProofInterface) or not isinstance(
        profile, AlgebraProfile
    ):
        return result(
            Outcome.MALFORMED,
            "fs-proof-interface:external-inputs",
            "P01-INPUT-002",
            "interface or algebra profile has the wrong type",
        )
    interface_id = _safe_interface_id(interface)
    if not interface_id or external_inputs.interface_id != interface_id:
        return result(
            Outcome.MISMATCH,
            "fs-proof-interface:external-inputs:scope",
            "P01-INPUT-003",
            "runtime external inputs name a different proof interface",
            subject=interface_id,
        )
    context_result = admit_application_context(external_inputs.application_context)
    if context_result.outcome is not Outcome.AFFIRMATIVE:
        return result(
            context_result.outcome,
            "fs-proof-interface:external-inputs:application-context",
            "P01-INPUT-004",
            "runtime application context is not admitted",
            subject=interface_id,
            cause=context_result.term(),
        )
    if not profile.valid_group_element(external_inputs.statement):
        outcome = (
            Outcome.MALFORMED
            if not isinstance(external_inputs.statement, int)
            or isinstance(external_inputs.statement, bool)
            else Outcome.SEMANTIC_NEGATIVE
        )
        return result(
            outcome,
            "fs-proof-interface:external-inputs:statement",
            "P01-INPUT-005",
            "runtime Statement is not an admitted prime-order subgroup element",
            subject=interface_id,
        )
    return affirmative(
        "fs-proof-interface:external-inputs",
        "P01-INPUT-OK",
        "runtime application context and Statement are admitted external inputs",
        subject=external_inputs.identity,
        interface_id=interface_id,
    )


def admit_fs_external_inputs(
    external_inputs: FSExternalInputs,
    interface: FiatShamirProofInterface,
    protocol: ProtocolVariant,
    construction: TranscriptConstruction,
    core: ConversationCore,
    profile: AlgebraProfile,
) -> Result:
    """Admit runtime inputs only against an independently admitted interface."""

    type_failure = _operand_type_failure(
        interface,
        protocol,
        construction,
        core,
        profile,
        boundary="fs-proof-interface:external-inputs",
    )
    if type_failure is not None:
        return type_failure
    if not isinstance(external_inputs, FSExternalInputs):
        return result(
            Outcome.MALFORMED,
            "fs-proof-interface:external-inputs",
            "P01-INPUT-001",
            "external inputs have the wrong type",
        )
    interface_result = admit_fs_proof_interface(
        interface, protocol, construction, core, profile
    )
    if interface_result.outcome is not Outcome.AFFIRMATIVE:
        return interface_result
    return _check_fs_external_input_shape(external_inputs, interface, profile)


@dataclass(frozen=True)
class DecodedFSProof:
    """Canonical decoded proof; intentionally contains no challenge field."""

    interface_id: str
    encoded: bytes
    commitment: int
    response: int

    def term(self) -> dict[str, Any]:
        return {
            "interface_id": self.interface_id,
            "encoded": self.encoded,
            "commitment": self.commitment,
            "response": self.response,
        }

    @property
    def identity(self) -> str:
        return semantic_id("p01.decoded-fs-proof.v1", self.term())


def _decode_admitted_proof(
    interface: FiatShamirProofInterface,
    proof_bytes: bytes,
    profile: AlgebraProfile,
) -> DecodedFSProof | Result:
    expected_width = profile.group_width + profile.scalar_width
    actual_width = len(proof_bytes)
    if actual_width < expected_width:
        return result(
            Outcome.MALFORMED,
            "fs-proof-interface:decode:truncated",
            "P01-PROOF-002",
            "proof is truncated before the exact commitment-response product ends",
            subject=interface.identity,
            expected_width=expected_width,
            actual_width=actual_width,
        )
    if actual_width > expected_width:
        return result(
            Outcome.MALFORMED,
            "fs-proof-interface:decode:trailing-bytes",
            "P01-PROOF-003",
            "proof has trailing bytes; a serialized challenge or any extra field is forbidden",
            subject=interface.identity,
            expected_width=expected_width,
            actual_width=actual_width,
            trailing_width=actual_width - expected_width,
        )
    commitment_bytes = proof_bytes[: profile.group_width]
    response_bytes = proof_bytes[profile.group_width :]
    commitment = int.from_bytes(commitment_bytes, "big")
    response = int.from_bytes(response_bytes, "big")
    if not profile.valid_group_element(commitment):
        return result(
            Outcome.MALFORMED,
            "fs-proof-interface:decode:noncanonical-commitment",
            "P01-PROOF-004",
            "commitment bytes do not canonically encode an admitted subgroup element",
            subject=interface.identity,
        )
    if not profile.valid_scalar(response):
        return result(
            Outcome.MALFORMED,
            "fs-proof-interface:decode:noncanonical-response",
            "P01-PROOF-005",
            "response bytes do not canonically encode a scalar modulo q",
            subject=interface.identity,
        )
    canonical = profile.encode_group(commitment) + profile.encode_scalar(response)
    if canonical != proof_bytes:
        return result(
            Outcome.MALFORMED,
            "fs-proof-interface:decode:noncanonical-roundtrip",
            "P01-PROOF-006",
            "decoded proof does not round-trip to the exact original bytes",
            subject=interface.identity,
        )
    return DecodedFSProof(interface.identity, proof_bytes, commitment, response)


def decode_fs_proof(
    interface: FiatShamirProofInterface,
    protocol: ProtocolVariant,
    construction: TranscriptConstruction,
    core: ConversationCore,
    profile: AlgebraProfile,
    proof_bytes: bytes,
) -> DecodedFSProof | Result:
    """Fully consume and canonically decode exactly ``(A,z)``."""

    type_failure = _operand_type_failure(
        interface,
        protocol,
        construction,
        core,
        profile,
        boundary="fs-proof-interface:decode",
    )
    if type_failure is not None:
        return type_failure
    if not isinstance(proof_bytes, bytes):
        return result(
            Outcome.MALFORMED,
            "fs-proof-interface:decode:raw-type",
            "P01-PROOF-001",
            "proof input must be an immutable bytes value",
            subject=_safe_interface_id(interface),
        )
    interface_result = admit_fs_proof_interface(
        interface, protocol, construction, core, profile
    )
    if interface_result.outcome is not Outcome.AFFIRMATIVE:
        return interface_result
    return _decode_admitted_proof(interface, proof_bytes, profile)


def encode_fs_proof(
    interface: FiatShamirProofInterface,
    protocol: ProtocolVariant,
    construction: TranscriptConstruction,
    core: ConversationCore,
    profile: AlgebraProfile,
    commitment: int,
    response: int,
) -> bytes | Result:
    """Canonically encode exactly ``(A,z)``; no challenge parameter exists."""

    type_failure = _operand_type_failure(
        interface,
        protocol,
        construction,
        core,
        profile,
        boundary="fs-proof-interface:encode",
    )
    if type_failure is not None:
        return type_failure
    if (
        not isinstance(commitment, int)
        or isinstance(commitment, bool)
        or not isinstance(response, int)
        or isinstance(response, bool)
    ):
        return result(
            Outcome.MALFORMED,
            "fs-proof-interface:encode:raw-type",
            "P01-PROOF-ENC-001",
            "commitment and response must be integer values",
            subject=_safe_interface_id(interface),
        )
    interface_result = admit_fs_proof_interface(
        interface, protocol, construction, core, profile
    )
    if interface_result.outcome is not Outcome.AFFIRMATIVE:
        return interface_result
    if not profile.valid_group_element(commitment):
        return result(
            Outcome.SEMANTIC_NEGATIVE,
            "fs-proof-interface:encode:commitment-domain",
            "P01-PROOF-ENC-002",
            "commitment is outside the admitted subgroup domain",
            subject=interface.identity,
        )
    if not profile.valid_scalar(response):
        return result(
            Outcome.SEMANTIC_NEGATIVE,
            "fs-proof-interface:encode:response-domain",
            "P01-PROOF-ENC-003",
            "response is outside the scalar domain",
            subject=interface.identity,
        )
    encoded = profile.encode_group(commitment) + profile.encode_scalar(response)
    if len(encoded) != interface.proof_width:
        return result(
            Outcome.CHECKER_FAILURE,
            "fs-proof-interface:encode:width",
            "P01-PROOF-ENC-004",
            "canonical encoder escaped the admitted proof width",
            subject=interface.identity,
        )
    return encoded


class VerifierDisposition(str, Enum):
    ACCEPT = "Accept"
    REJECT = "Reject"


@dataclass(frozen=True)
class FSVerificationRecord:
    interface_id: str
    protocol_id: str
    construction_id: str
    external_inputs_id: str
    decoded_proof_id: str
    challenge: int
    challenge_query_id: str
    verifier_check_contract_id: str
    terminal_contract_id: str
    check_value: bool
    disposition: VerifierDisposition

    def term(self) -> dict[str, Any]:
        return {
            "interface_id": self.interface_id,
            "protocol_id": self.protocol_id,
            "construction_id": self.construction_id,
            "external_inputs_id": self.external_inputs_id,
            "decoded_proof_id": self.decoded_proof_id,
            "challenge": self.challenge,
            "challenge_query_id": self.challenge_query_id,
            "verifier_check_contract_id": self.verifier_check_contract_id,
            "terminal_contract_id": self.terminal_contract_id,
            "check_value": self.check_value,
            "disposition": self.disposition.value,
        }

    @property
    def identity(self) -> str:
        return semantic_id("p01.fs-verification-record.v1", self.term())


def evaluate_fs_proof(
    interface: FiatShamirProofInterface,
    protocol: ProtocolVariant,
    construction: TranscriptConstruction,
    core: ConversationCore,
    profile: AlgebraProfile,
    external_inputs: FSExternalInputs,
    proof_bytes: bytes,
) -> FSVerificationRecord | Result:
    """Decode, derive ``c``, and execute the exact Core-owned verifier route."""

    type_failure = _operand_type_failure(
        interface,
        protocol,
        construction,
        core,
        profile,
        boundary="fs-proof-interface:verify",
    )
    if type_failure is not None:
        return type_failure
    if not isinstance(external_inputs, FSExternalInputs):
        return result(
            Outcome.MALFORMED,
            "fs-proof-interface:verify:external-inputs",
            "P01-VERIFY-001",
            "verification external inputs have the wrong type",
            subject=_safe_interface_id(interface),
        )
    if not isinstance(proof_bytes, bytes):
        return result(
            Outcome.MALFORMED,
            "fs-proof-interface:verify:proof",
            "P01-VERIFY-002",
            "verification proof must be an immutable bytes value",
            subject=_safe_interface_id(interface),
        )
    interface_result = admit_fs_proof_interface(
        interface, protocol, construction, core, profile
    )
    if interface_result.outcome is not Outcome.AFFIRMATIVE:
        return interface_result
    inputs_result = _check_fs_external_input_shape(
        external_inputs, interface, profile
    )
    if inputs_result.outcome is not Outcome.AFFIRMATIVE:
        return inputs_result
    decoded = _decode_admitted_proof(interface, proof_bytes, profile)
    if isinstance(decoded, Result):
        return decoded
    try:
        challenge, query, _ = derive_fs_challenge(
            construction,
            profile,
            external_inputs.application_context,
            external_inputs.statement,
            decoded.commitment,
        )
    except (AssertionError, AttributeError, TypeError, ValueError) as error:
        return result(
            Outcome.CHECKER_FAILURE,
            "fs-proof-interface:verify:challenge-recomputation",
            "P01-VERIFY-003",
            f"admitted challenge recomputation failed: {error}",
            subject=interface.identity,
        )
    if not profile.valid_challenge(challenge):
        return result(
            Outcome.CHECKER_FAILURE,
            "fs-proof-interface:verify:challenge-codomain",
            "P01-VERIFY-004",
            "recomputed challenge escaped the Core challenge domain",
            subject=interface.identity,
        )

    # Admission has already established that these are the canonical Schnorr
    # deterministic rules.  The evaluator dispatches through their existing
    # Core-owned IDs; it does not create another equation or terminal identity.
    if (
        interface.verifier_check_contract_id
        != core.verifier_check.semantic_contract_id
        or interface.terminal_contract_id
        != core.terminal_route.semantic_contract_id
        or interface.verifier_check_occurrence != CHECK
        or interface.terminal_occurrence != TERMINAL
    ):
        return result(
            Outcome.MISMATCH,
            "fs-proof-interface:verify:core-routing",
            "P01-VERIFY-005",
            "verification route differs from the admitted Core contracts",
            subject=interface.identity,
        )
    left = pow(profile.generator, decoded.response, profile.p)
    right = (
        decoded.commitment
        * pow(external_inputs.statement, challenge, profile.p)
    ) % profile.p
    check_value = left == right
    disposition = (
        VerifierDisposition.ACCEPT
        if check_value
        else VerifierDisposition.REJECT
    )
    query_id = semantic_id(
        "p01.fs-challenge-query.v1",
        {"construction_id": construction.identity, "query": query},
    )
    return FSVerificationRecord(
        interface_id=interface.identity,
        protocol_id=protocol.identity,
        construction_id=construction.identity,
        external_inputs_id=external_inputs.identity,
        decoded_proof_id=decoded.identity,
        challenge=challenge,
        challenge_query_id=query_id,
        verifier_check_contract_id=core.verifier_check.semantic_contract_id,
        terminal_contract_id=core.terminal_route.semantic_contract_id,
        check_value=check_value,
        disposition=disposition,
    )


def check_fs_proof(
    interface: FiatShamirProofInterface,
    protocol: ProtocolVariant,
    construction: TranscriptConstruction,
    core: ConversationCore,
    profile: AlgebraProfile,
    external_inputs: FSExternalInputs,
    proof_bytes: bytes,
) -> Result:
    """Return the finite verifier decision as an explicit Result judgment."""

    verification = evaluate_fs_proof(
        interface,
        protocol,
        construction,
        core,
        profile,
        external_inputs,
        proof_bytes,
    )
    if isinstance(verification, Result):
        return verification
    common = {
        "interface_id": verification.interface_id,
        "protocol_id": verification.protocol_id,
        "verification_record_id": verification.identity,
        "challenge": verification.challenge,
        "challenge_query_id": verification.challenge_query_id,
        "verifier_check_contract_id": verification.verifier_check_contract_id,
        "terminal_contract_id": verification.terminal_contract_id,
        "finite_scope": "one decoded P01 proof invocation; no security theorem",
    }
    if verification.disposition is VerifierDisposition.ACCEPT:
        return affirmative(
            "fs-proof-interface:verify",
            "P01-VERIFY-ACCEPT",
            "canonical (commitment,response) proof accepts under the recomputed challenge and Core verifier rule",
            subject=verification.identity,
            disposition=verification.disposition.value,
            **common,
        )
    return result(
        Outcome.SEMANTIC_NEGATIVE,
        "fs-proof-interface:verify",
        "P01-VERIFY-REJECT",
        "canonical (commitment,response) proof rejects under the recomputed challenge and Core verifier rule",
        subject=verification.identity,
        disposition=verification.disposition.value,
        **common,
    )
