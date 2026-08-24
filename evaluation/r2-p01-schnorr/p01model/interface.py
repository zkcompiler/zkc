"""Exact proof ABI and public verification for the finite P01 FS protocol.

The proof contains exactly ``(commitment, response)``.  Application context and
Statement are external public inputs; the challenge is always recomputed by the
admitted transcript construction.  Schnorr equation and terminal evaluation
are delegated to :func:`execution.evaluate_schnorr_verifier`, the same owner
used by exact execution replay.
"""

from __future__ import annotations

from dataclasses import dataclass
import re
from typing import Any

from .execution import (
    CheckedPublicExecution,
    Disposition,
    EvaluatorBasis,
    PublicResourceUsage,
    PublicVerifierDecision,
    TranscriptReadReceipt,
    admit_evaluator_basis,
    evaluate_schnorr_verifier,
    public_usage_fits,
    public_trace_value,
    requalify_public_execution,
)
from .provenance import (
    ArtifactContentId,
    EvidenceRecordId,
    ProvenanceError,
    ValidationBasisId,
    artifact_content_id,
    canonical_json_content_id,
    evidence_record_id,
)
from .semantic import (
    CHALLENGE,
    COMMITMENT,
    RESPONSE,
    STATEMENT,
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


_CONTENT_ID = re.compile(r"sha256:[0-9a-f]{64}\Z")
_SERIALIZATION = "exact-fixed-width-product.v2"
_MODEL = "FiatShamirProofInterface.v2"
_FS_PUBLIC_VERIFICATION_USAGE = PublicResourceUsage(2, 2, 5)


def _is_content_id(value: Any) -> bool:
    return isinstance(value, str) and _CONTENT_ID.fullmatch(value) is not None


def _safe_identity(value: Any) -> str:
    try:
        identity = value.identity
    except (AttributeError, ProvenanceError, TermEncodingError, TypeError, ValueError):
        return ""
    if isinstance(identity, (ArtifactContentId, EvidenceRecordId)):
        return str(identity)
    return identity if _is_content_id(identity) else ""


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
            "proof_fields": [item.term() for item in self.proof_fields],
            "challenge_recomputation": self.challenge_recomputation.term(),
            "verifier_check_occurrence": self.verifier_check_occurrence,
            "verifier_check_contract_id": self.verifier_check_contract_id,
            "terminal_occurrence": self.terminal_occurrence,
            "terminal_contract_id": self.terminal_contract_id,
            "serialization": self.serialization,
        }

    @property
    def identity(self) -> str:
        return semantic_id("p01.fs-proof-interface.v2", self.term())

    @property
    def proof_width(self) -> int:
        return sum(field.width for field in self.proof_fields)


def canonical_fs_proof_interface(
    protocol: ProtocolVariant,
    construction: TranscriptConstruction,
    core: ConversationCore,
    profile: AlgebraProfile,
) -> FiatShamirProofInterface:
    return FiatShamirProofInterface(
        protocol.identity,
        core.identity,
        profile.identity,
        construction.identity,
        (
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
        (
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
        ChallengeRecomputationSpec(
            CHALLENGE,
            construction.identity,
            (construction.runtime_context.source, STATEMENT, COMMITMENT),
        ),
        core.verifier_check.output_occurrence,
        core.verifier_check.semantic_contract_id,
        core.terminal_route.output_occurrence,
        core.terminal_route.semantic_contract_id,
    )


def admit_fs_proof_interface(
    interface: FiatShamirProofInterface,
    protocol: ProtocolVariant,
    construction: TranscriptConstruction,
    core: ConversationCore,
    profile: AlgebraProfile,
) -> Result:
    if not isinstance(interface, FiatShamirProofInterface):
        return result(
            Outcome.MALFORMED,
            "fs-proof-interface",
            "P01-IFACE-001",
            "FS proof interface has the wrong type",
        )
    try:
        interface_id = interface.identity
    except (AttributeError, TermEncodingError, TypeError, ValueError):
        return result(
            Outcome.MALFORMED,
            "fs-proof-interface",
            "P01-IFACE-001",
            "FS proof interface is outside the closed grammar",
        )
    protocol_result = admit_protocol(
        protocol,
        core,
        profile,
        construction=construction,
    )
    if protocol_result.outcome is not Outcome.AFFIRMATIVE:
        return protocol_result
    if protocol.realization_kind is not RealizationKind.FIAT_SHAMIR:
        return result(
            Outcome.UNSUPPORTED,
            "fs-proof-interface:realization",
            "P01-IFACE-002",
            "proof interface requires an admitted Fiat-Shamir Protocol",
            subject=interface_id,
        )
    expected = canonical_fs_proof_interface(protocol, construction, core, profile)
    if interface != expected:
        return result(
            Outcome.MISMATCH,
            "fs-proof-interface:exact-abi",
            "P01-IFACE-003",
            "proof interface differs from the exact two-field FS ABI",
            subject=interface_id,
            expected_interface_id=expected.identity,
        )
    return affirmative(
        "fs-proof-interface",
        "P01-IFACE-OK",
        "exact statement-external, challenge-recomputing FS ABI is admitted",
        subject=interface_id,
    )


@dataclass(frozen=True)
class FSExternalInputs:
    application_context: str
    statement: int

    def term(self) -> dict[str, Any]:
        return {
            "application_context": self.application_context,
            "statement": self.statement,
        }

    @property
    def identity(self) -> ArtifactContentId:
        return canonical_json_content_id(self.term())


def admit_fs_external_inputs(
    external_inputs: FSExternalInputs,
    interface: FiatShamirProofInterface,
    protocol: ProtocolVariant,
    construction: TranscriptConstruction,
    core: ConversationCore,
    profile: AlgebraProfile,
) -> Result:
    interface_result = admit_fs_proof_interface(
        interface, protocol, construction, core, profile
    )
    if interface_result.outcome is not Outcome.AFFIRMATIVE:
        return interface_result
    if not isinstance(external_inputs, FSExternalInputs):
        return result(
            Outcome.MALFORMED,
            "fs-external-inputs",
            "P01-EXT-001",
            "FS external inputs have the wrong type",
        )
    context_result = admit_application_context(external_inputs.application_context)
    if context_result.outcome is not Outcome.AFFIRMATIVE:
        return context_result
    if not profile.valid_group_element(external_inputs.statement):
        return result(
            Outcome.SEMANTIC_NEGATIVE,
            "fs-external-inputs:statement",
            "P01-EXT-002",
            "external Statement is outside the admitted group domain",
            subject=_safe_identity(external_inputs),
        )
    return affirmative(
        "fs-external-inputs",
        "P01-EXT-OK",
        "FS application context and Statement are admitted external inputs",
            subject=str(external_inputs.identity),
    )


@dataclass(frozen=True)
class DecodedFSProof:
    interface_id: str
    commitment: int
    response: int

    def term(self) -> dict[str, Any]:
        return {
            "interface_id": self.interface_id,
            "commitment": self.commitment,
            "response": self.response,
        }

    @property
    def identity(self) -> str:
        return semantic_id("p01.decoded-fs-proof.v2", self.term())


def decode_fs_proof(
    proof_bytes: bytes,
    interface: FiatShamirProofInterface,
    protocol: ProtocolVariant,
    construction: TranscriptConstruction,
    core: ConversationCore,
    profile: AlgebraProfile,
) -> DecodedFSProof | Result:
    interface_result = admit_fs_proof_interface(
        interface, protocol, construction, core, profile
    )
    if interface_result.outcome is not Outcome.AFFIRMATIVE:
        return interface_result
    if not isinstance(proof_bytes, bytes) or len(proof_bytes) != interface.proof_width:
        return result(
            Outcome.MALFORMED,
            "fs-proof-decoding:length",
            "P01-PROOF-001",
            "proof bytes do not have the exact fixed product width",
            subject=interface.identity,
        )
    commitment_width = interface.proof_fields[0].width
    commitment = int.from_bytes(proof_bytes[:commitment_width], "big")
    response = int.from_bytes(proof_bytes[commitment_width:], "big")
    if not profile.valid_group_element(commitment) or not profile.valid_scalar(response):
        return result(
            Outcome.SEMANTIC_NEGATIVE,
            "fs-proof-decoding:field-domain",
            "P01-PROOF-002",
            "decoded commitment or response is outside its declared domain",
            subject=interface.identity,
        )
    decoded = DecodedFSProof(interface.identity, commitment, response)
    if encode_fs_proof(decoded, interface, protocol, construction, core, profile) != proof_bytes:
        return result(
            Outcome.MISMATCH,
            "fs-proof-decoding:canonicality",
            "P01-PROOF-003",
            "proof bytes are not the canonical encoding of decoded fields",
            subject=decoded.identity,
        )
    return decoded


def encode_fs_proof(
    proof: DecodedFSProof,
    interface: FiatShamirProofInterface,
    protocol: ProtocolVariant,
    construction: TranscriptConstruction,
    core: ConversationCore,
    profile: AlgebraProfile,
) -> bytes | Result:
    interface_result = admit_fs_proof_interface(
        interface, protocol, construction, core, profile
    )
    if interface_result.outcome is not Outcome.AFFIRMATIVE:
        return interface_result
    if (
        not isinstance(proof, DecodedFSProof)
        or proof.interface_id != interface.identity
        or not profile.valid_group_element(proof.commitment)
        or not profile.valid_scalar(proof.response)
    ):
        return result(
            Outcome.MALFORMED,
            "fs-proof-encoding",
            "P01-PROOF-004",
            "decoded proof is malformed or belongs to a different interface",
            subject=_safe_identity(proof),
        )
    return profile.encode_group(proof.commitment) + profile.encode_scalar(proof.response)


@dataclass(frozen=True)
class FSVerificationRecord:
    interface_id: str
    protocol_id: str
    external_inputs_id: ArtifactContentId
    proof_artifact_id: ArtifactContentId
    construction_id: str
    verifier_basis_id: ValidationBasisId
    challenge: int
    query_hex: str
    reads: tuple[TranscriptReadReceipt, ...]
    usage: PublicResourceUsage
    decision: PublicVerifierDecision

    def term(self) -> dict[str, Any]:
        return {
            "interface_id": self.interface_id,
            "protocol_id": self.protocol_id,
            "external_inputs_id": str(self.external_inputs_id),
            "proof_artifact_id": str(self.proof_artifact_id),
            "construction_id": self.construction_id,
            "verifier_basis_id": str(self.verifier_basis_id),
            "challenge": self.challenge,
            "query_hex": self.query_hex,
            "reads": [receipt.term() for receipt in self.reads],
            "usage": self.usage.term(),
            "verification_executions": self.verification_executions,
            "decision": self.decision.term(),
        }

    @property
    def identity(self) -> EvidenceRecordId:
        return evidence_record_id("fs-verification-record", self.term())

    @property
    def disposition(self) -> Disposition:
        return self.decision.disposition

    @property
    def verification_executions(self) -> int:
        return 1


def _transcript_receipts(
    raw_receipts: tuple[dict[str, Any], ...]
) -> tuple[TranscriptReadReceipt, ...]:
    return tuple(
        TranscriptReadReceipt(
            raw["source_kind"],
            raw["occurrence"],
            raw["value_domain_id"],
            raw["codec"],
            raw["encoded_hex"],
        )
        for raw in raw_receipts
    )


def fs_proof_artifact_id(proof_bytes: bytes) -> ArtifactContentId:
    """Identify exact public proof bytes, independently of decoded meaning."""

    return artifact_content_id(proof_bytes)


def evaluate_fs_proof(
    proof_bytes: bytes,
    external_inputs: FSExternalInputs,
    interface: FiatShamirProofInterface,
    evaluator_basis: EvaluatorBasis,
    protocol: ProtocolVariant,
    construction: TranscriptConstruction,
    core: ConversationCore,
    profile: AlgebraProfile,
) -> FSVerificationRecord | Result:
    """Decode, recompute the challenge, and invoke the shared public verifier."""

    basis_result = admit_evaluator_basis(evaluator_basis)
    if basis_result.outcome is not Outcome.AFFIRMATIVE:
        return basis_result
    if protocol.identity not in evaluator_basis.supported_protocol_ids:
        return result(
            Outcome.UNSUPPORTED,
            "fs-proof-verification:verifier-basis",
            "P01-VERIFY-003",
            "FS Protocol is outside the exact public verifier basis",
            subject=str(evaluator_basis.identity),
        )
    if (
        not public_usage_fits(
            _FS_PUBLIC_VERIFICATION_USAGE,
            evaluator_basis.hard_caps,
        )
        or evaluator_basis.hard_caps.max_replay_executions < 1
    ):
        return result(
            Outcome.RESOURCE_EXCEEDED,
            "fs-proof-verification:resources",
            "P01-VERIFY-004",
            "FS proof verification exceeds the public evaluator hard caps",
            subject=str(evaluator_basis.identity),
            required_usage=_FS_PUBLIC_VERIFICATION_USAGE.term(),
            required_verification_executions=1,
        )
    external_result = admit_fs_external_inputs(
        external_inputs, interface, protocol, construction, core, profile
    )
    if external_result.outcome is not Outcome.AFFIRMATIVE:
        return external_result
    decoded = decode_fs_proof(
        proof_bytes, interface, protocol, construction, core, profile
    )
    if isinstance(decoded, Result):
        return decoded
    try:
        challenge, query, raw_receipts = derive_fs_challenge(
            construction,
            profile,
            external_inputs.application_context,
            external_inputs.statement,
            decoded.commitment,
        )
        receipts = _transcript_receipts(raw_receipts)
    except (KeyError, TypeError, ValueError):
        return result(
            Outcome.MALFORMED,
            "fs-proof-verification:challenge",
            "P01-VERIFY-001",
            "challenge recomputation failed on admitted public inputs",
            subject=decoded.identity,
        )
    decision = evaluate_schnorr_verifier(
        core,
        profile,
        statement=external_inputs.statement,
        commitment=decoded.commitment,
        challenge=challenge,
        response=decoded.response,
    )
    if isinstance(decision, Result):
        return decision
    return FSVerificationRecord(
        interface.identity,
        protocol.identity,
        external_inputs.identity,
        fs_proof_artifact_id(proof_bytes),
        construction.identity,
        evaluator_basis.identity,
        challenge,
        query.hex(),
        receipts,
        _FS_PUBLIC_VERIFICATION_USAGE,
        decision,
    )


def check_fs_proof(
    proof_bytes: bytes,
    external_inputs: FSExternalInputs,
    interface: FiatShamirProofInterface,
    evaluator_basis: EvaluatorBasis,
    protocol: ProtocolVariant,
    construction: TranscriptConstruction,
    core: ConversationCore,
    profile: AlgebraProfile,
) -> Result:
    verification = evaluate_fs_proof(
        proof_bytes,
        external_inputs,
        interface,
        evaluator_basis,
        protocol,
        construction,
        core,
        profile,
    )
    if isinstance(verification, Result):
        return verification
    if verification.disposition is Disposition.REJECT:
        return result(
            Outcome.SEMANTIC_NEGATIVE,
            "fs-proof-verification:terminal",
            "P01-VERIFY-002",
            "proof reached the shared public verifier's Reject terminal",
            subject=str(verification.identity),
        )
    return affirmative(
        "fs-proof-verification",
        "P01-VERIFY-OK",
        "proof reached the shared public verifier's Accept terminal",
        subject=str(verification.identity),
    )


def check_fs_execution_projection(
    checked: CheckedPublicExecution,
    interface: FiatShamirProofInterface,
    *,
    proof_bytes: bytes | None = None,
) -> Result:
    """Check the exact FS execution -> external-input/proof ABI projection.

    ``proof_bytes`` may be supplied to test a published artifact.  If omitted,
    the canonical bytes are derived from the checked execution.  In either
    case, the verifier record must agree with the checked execution's exact
    challenge query, reads, decision, and terminal value.
    """

    replayed = requalify_public_execution(checked)
    if isinstance(replayed, Result):
        return replayed
    if (
        replayed.protocol.realization_kind is not RealizationKind.FIAT_SHAMIR
        or not isinstance(replayed.construction, TranscriptConstruction)
        or replayed.invocation.application_context is None
    ):
        return result(
            Outcome.MISMATCH,
            "fs-execution-projection:realization",
            "P01-FS-PROJECTION-001",
            "checked execution is not a complete FS realization",
            subject=str(replayed.identity),
        )
    interface_result = admit_fs_proof_interface(
        interface,
        replayed.protocol,
        replayed.construction,
        replayed.core,
        replayed.profile,
    )
    if interface_result.outcome is not Outcome.AFFIRMATIVE:
        return interface_result
    commitment = public_trace_value(replayed.record, COMMITMENT)
    response = public_trace_value(replayed.record, RESPONSE)
    if isinstance(commitment, Result) or isinstance(response, Result):
        return result(
            Outcome.MALFORMED,
            "fs-execution-projection:messages",
            "P01-FS-PROJECTION-001",
            "checked execution lacks its exact two public proof messages",
            subject=str(replayed.identity),
        )
    decoded = DecodedFSProof(interface.identity, commitment, response)
    canonical_bytes = encode_fs_proof(
        decoded,
        interface,
        replayed.protocol,
        replayed.construction,
        replayed.core,
        replayed.profile,
    )
    if isinstance(canonical_bytes, Result):
        return canonical_bytes
    if proof_bytes is not None and proof_bytes != canonical_bytes:
        return result(
            Outcome.MISMATCH,
            "fs-execution-projection:proof-bytes",
            "P01-FS-PROJECTION-002",
            "published proof bytes differ from the checked execution projection",
            subject=str(replayed.identity),
        )
    external_inputs = FSExternalInputs(
        replayed.invocation.application_context,
        replayed.invocation.statement,
    )
    verification = evaluate_fs_proof(
        canonical_bytes,
        external_inputs,
        interface,
        replayed.evaluator_basis,
        replayed.protocol,
        replayed.construction,
        replayed.core,
        replayed.profile,
    )
    if isinstance(verification, Result):
        return verification
    receipt = replayed.record.challenge_receipt
    if (
        verification.challenge != receipt.challenge
        or verification.query_hex != receipt.query_hex
        or verification.reads != receipt.reads
        or verification.usage != replayed.record.usage
        or verification.verification_executions != replayed.replay_executions
        or verification.decision != replayed.record.verifier_decision
    ):
        return result(
            Outcome.MISMATCH,
            "fs-execution-projection:exact-verifier-record",
            "P01-FS-PROJECTION-003",
            "proof-interface verification differs from checked execution replay",
            subject=str(replayed.identity),
            verification_record_id=str(verification.identity),
        )
    return affirmative(
        "fs-execution-projection",
        "P01-FS-PROJECTION-OK",
        "checked FS execution projects exactly to external inputs, proof bytes, challenge, and terminal",
        subject=str(replayed.identity),
        interface_id=interface.identity,
        proof_artifact_id=str(fs_proof_artifact_id(canonical_bytes)),
        verification_record_id=str(verification.identity),
    )
