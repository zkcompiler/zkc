from __future__ import annotations

from dataclasses import dataclass
from dataclasses import replace
import inspect
import json
from pathlib import Path
import pickle
import sys
import unittest


MODEL_ROOT = Path(__file__).resolve().parents[1]
REPO_ROOT = MODEL_ROOT.parents[1]
sys.path.insert(0, str(MODEL_ROOT))

from p01model.execution import (  # noqa: E402
    ChallengeReceipt,
    CheckedPublicExecution,
    Disposition,
    FreshChallengeBinding,
    LocalGenerationQualification,
    LocalGenerationRecord,
    LocalResourcePlan,
    OwnerLocalBindingStore,
    OwnerLocalInvocationRef,
    OwnerLocalPrecommitmentHandle,
    PortableExecutionRecord,
    PublicInvocation,
    PublicInvocationPrefix,
    PublicReplayRequest,
    PublicResourcePlan,
    ResponsePlan,
    build_evaluator_basis,
    build_portable_execution,
    check_checked_public_execution,
    check_fresh_public_execution,
    check_local_generation_qualification,
    export_checked_public_statement,
    export_checked_public_transcript,
    generate_local_execution,
    issue_relations_checked_statement,
    qualify_local_generation,
    qualify_public_execution,
    requalify_public_execution,
)
from p01model.interface import (  # noqa: E402
    DecodedFSProof,
    FSExternalInputs,
    FSVerificationRecord,
    canonical_fs_proof_interface,
    check_fs_execution_projection,
    check_fs_proof,
    encode_fs_proof,
    evaluate_fs_proof,
    fs_proof_artifact_id,
)
from p01model.provenance import (  # noqa: E402
    ArtifactContentId,
    EvidenceRecordId,
    ValidationBasisId,
    artifact_content_id,
    canonical_json_bytes,
    load_bounded_json_bytes,
)
from p01model.relations import (  # noqa: E402
    CheckedPublicExecutionStatement,
    CheckedRelationSatisfaction,
    RelationSatisfactionOwner,
    SchnorrRelationInstance,
    canonical_schnorr_relation,
    check_relation_satisfaction,
)
from p01model.semantic import (  # noqa: E402
    CHALLENGE,
    AlgebraProfile,
    canonical_core,
    canonical_transcript_construction,
    make_fresh_protocol,
    make_fs_protocol,
)
from p01model.terms import Outcome, Result  # noqa: E402


APPLICATION_CONTEXT = "zkc/p01/test-session/alpha"
STATEMENT_VALUE = 13
COMMITMENT_VALUE = 16
FRESH_CHALLENGE = 3
FRESH_RESPONSE = 3
FS_CHALLENGE = 6
FS_RESPONSE = 2
FS_PROOF = bytes.fromhex("1002")
PRIVATE_GENERATION_PATH = (
    REPO_ROOT / "evaluation/r2-p01-schnorr/cases/private-generation.json"
)
PRIVATE_GENERATION_SCHEMA = "zkc.r2.p01.private-generation-input.v3"
PRIVATE_GENERATION_CLASSIFICATION = (
    "DeclassifiedTestVectorPopulatesPrivateSemanticRoles"
)
PRIVATE_GENERATION_POLICY = {
    "portable_identity": False,
    "public_report_digest": False,
    "cross_process_authority_replay": False,
    "allowed_use": (
        "owner-local precommitment audit and public-projection comparison"
    ),
}


@dataclass(frozen=True)
class PrivateGenerationInput:
    """Test-only owner-local values with no portable identity or term API."""

    witness: int
    nonce: int
    local_resources: LocalResourcePlan


def _private_mapping(value: object, keys: set[str], where: str) -> dict:
    if not isinstance(value, dict) or set(value) != keys:
        raise ValueError(f"{where} has a different closed object shape")
    return value


def _private_nonnegative_integer(value: object, where: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value < 0:
        raise ValueError(f"{where} must be a nonnegative integer")
    return value


def _decode_private_generation_input(raw: bytes) -> PrivateGenerationInput:
    """Decode the bounded sidecar without hashing or minting a portable ID."""

    value = _private_mapping(
        load_bounded_json_bytes(raw, maximum=4096),
        {
            "schema",
            "classification",
            "witness",
            "nonce",
            "local_resource_plan",
            "policy",
        },
        "private generation input",
    )
    if value["schema"] != PRIVATE_GENERATION_SCHEMA:
        raise ValueError("private generation schema differs")
    if value["classification"] != PRIVATE_GENERATION_CLASSIFICATION:
        raise ValueError("private generation classification differs")
    policy = _private_mapping(
        value["policy"], set(PRIVATE_GENERATION_POLICY), "private generation policy"
    )
    if policy != PRIVATE_GENERATION_POLICY:
        raise ValueError("private generation policy differs")
    resources = _private_mapping(
        value["local_resource_plan"],
        {"max_strategy_steps", "max_public_reads", "max_private_reads"},
        "private local resource plan",
    )
    return PrivateGenerationInput(
        _private_nonnegative_integer(value["witness"], "private witness"),
        _private_nonnegative_integer(value["nonce"], "private nonce"),
        LocalResourcePlan(
            _private_nonnegative_integer(
                resources["max_strategy_steps"], "local max_strategy_steps"
            ),
            _private_nonnegative_integer(
                resources["max_public_reads"], "local max_public_reads"
            ),
            _private_nonnegative_integer(
                resources["max_private_reads"], "local max_private_reads"
            ),
        ),
    )


def _load_private_generation_input() -> PrivateGenerationInput:
    return _decode_private_generation_input(PRIVATE_GENERATION_PATH.read_bytes())


class PhaseBExecutionInterfaceTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.private_generation = _load_private_generation_input()
        cls.profile = AlgebraProfile(p=23, q=11, generator=2, challenge_size=8)
        cls.core = canonical_core(cls.profile)
        cls.fresh_protocol, cls.fresh = make_fresh_protocol(
            cls.core, cls.profile
        )
        cls.construction = canonical_transcript_construction(
            cls.core, cls.profile
        )
        cls.fs_protocol = make_fs_protocol(
            cls.core, cls.construction, cls.profile
        )
        cls.public_case_bundle_id = artifact_content_id(
            (
                REPO_ROOT
                / "evaluation/r2-p01-schnorr/cases/public-inputs.json"
            ).read_bytes()
        )
        cls.evaluator_basis = build_evaluator_basis(
            REPO_ROOT,
            (cls.fresh_protocol.identity, cls.fs_protocol.identity),
        )

        cls.fresh_binding = FreshChallengeBinding(
            cls.core.identity,
            cls.fresh_protocol.identity,
            CHALLENGE,
            FRESH_CHALLENGE,
            artifact_content_id(b"p01-test-fresh-support-point\n"),
        )
        cls.fresh_invocation = PublicInvocation(
            cls.profile.identity,
            cls.core.identity,
            cls.fresh_protocol.identity,
            STATEMENT_VALUE,
            None,
            cls.fresh_binding,
        )
        cls.fs_invocation = PublicInvocation(
            cls.profile.identity,
            cls.core.identity,
            cls.fs_protocol.identity,
            STATEMENT_VALUE,
            APPLICATION_CONTEXT,
        )
        cls.fresh_prefix = PublicInvocationPrefix(
            cls.profile.identity,
            cls.core.identity,
            cls.fresh_protocol.identity,
            STATEMENT_VALUE,
            None,
        )
        cls.fs_prefix = PublicInvocationPrefix(
            cls.profile.identity,
            cls.core.identity,
            cls.fs_protocol.identity,
            STATEMENT_VALUE,
            APPLICATION_CONTEXT,
        )

        cls.fresh_record = cls._require_value(
            build_portable_execution(
                cls.fresh_invocation,
                COMMITMENT_VALUE,
                FRESH_RESPONSE,
                cls.fresh_protocol,
                cls.profile,
                cls.core,
                fresh=cls.fresh,
            ),
            "Fresh public record",
        )
        cls.fs_record = cls._require_value(
            build_portable_execution(
                cls.fs_invocation,
                COMMITMENT_VALUE,
                FS_RESPONSE,
                cls.fs_protocol,
                cls.profile,
                cls.core,
                construction=cls.construction,
            ),
            "FS public record",
        )
        cls.fresh_request = PublicReplayRequest(
            cls.fresh_invocation,
            cls.fresh_record,
            cls.evaluator_basis.identity,
            cls.public_case_bundle_id,
        )
        cls.fs_request = PublicReplayRequest(
            cls.fs_invocation,
            cls.fs_record,
            cls.evaluator_basis.identity,
            cls.public_case_bundle_id,
        )
        cls.fresh_checked = cls._require_value(
            qualify_public_execution(
                cls.fresh_request,
                cls.evaluator_basis,
                cls.fresh_protocol,
                cls.profile,
                cls.core,
                fresh=cls.fresh,
            ),
            "Fresh public qualification",
        )
        cls.fs_checked = cls._require_value(
            qualify_public_execution(
                cls.fs_request,
                cls.evaluator_basis,
                cls.fs_protocol,
                cls.profile,
                cls.core,
                construction=cls.construction,
            ),
            "FS public qualification",
        )
        cls.fs_interface = canonical_fs_proof_interface(
            cls.fs_protocol,
            cls.construction,
            cls.core,
            cls.profile,
        )
        cls.fs_external_inputs = FSExternalInputs(
            APPLICATION_CONTEXT,
            STATEMENT_VALUE,
        )
        cls.relation = canonical_schnorr_relation(cls.profile)
        cls.instance = SchnorrRelationInstance(
            cls.relation.identity,
            STATEMENT_VALUE,
        )

    @staticmethod
    def _require_value(value: object, label: str) -> object:
        if isinstance(value, Result):
            raise AssertionError(f"{label} failed: {value.term()}")
        return value

    def assert_result(
        self,
        value: object,
        outcome: Outcome,
        boundary: str,
        code: str,
    ) -> Result:
        self.assertIsInstance(value, Result)
        assert isinstance(value, Result)
        self.assertIs(value.outcome, outcome)
        self.assertEqual(value.boundary, boundary)
        self.assertEqual(value.code, code)
        return value

    def new_satisfaction_authority(
        self,
    ) -> tuple[RelationSatisfactionOwner, object, CheckedRelationSatisfaction]:
        owner = RelationSatisfactionOwner()
        assignment = owner.allocate_witness(
            self.instance, self.private_generation.witness
        )
        satisfaction = check_relation_satisfaction(
            assignment,
            self.instance,
            self.relation,
            self.profile,
            owner=owner,
        )
        self.assertIsInstance(satisfaction, CheckedRelationSatisfaction)
        assert isinstance(satisfaction, CheckedRelationSatisfaction)
        self.assertIs(satisfaction.outcome, Outcome.AFFIRMATIVE)
        return owner, assignment, satisfaction

    def begin_owner_local_invocation(
        self,
        prefix: PublicInvocationPrefix,
        protocol: object,
        *,
        store: OwnerLocalBindingStore | None = None,
    ) -> tuple[
        OwnerLocalBindingStore,
        OwnerLocalInvocationRef,
        RelationSatisfactionOwner,
        object,
        CheckedRelationSatisfaction,
    ]:
        owner, assignment, satisfaction = self.new_satisfaction_authority()
        store = store or OwnerLocalBindingStore()
        realization = (
            {"fresh": self.fresh}
            if protocol is self.fresh_protocol
            else {"construction": self.construction}
        )
        invocation_ref = store.begin_invocation(
            prefix,
            protocol,
            self.profile,
            self.core,
            **realization,
        )
        self.assertIsInstance(invocation_ref, OwnerLocalInvocationRef)
        assert isinstance(invocation_ref, OwnerLocalInvocationRef)
        return store, invocation_ref, owner, assignment, satisfaction

    def allocate_precommitment(
        self,
        prefix: PublicInvocationPrefix,
        protocol: object,
        response_plan: ResponsePlan = ResponsePlan.CANONICAL,
        *,
        evaluator_basis: object | None = None,
        public_resources: PublicResourcePlan | None = None,
        local_resources: LocalResourcePlan | None = None,
    ) -> tuple[
        OwnerLocalBindingStore,
        OwnerLocalInvocationRef,
        OwnerLocalPrecommitmentHandle,
        RelationSatisfactionOwner,
        object,
        CheckedRelationSatisfaction,
    ]:
        store, invocation_ref, owner, assignment, satisfaction = (
            self.begin_owner_local_invocation(prefix, protocol)
        )
        precommit_kwargs = {
            "local_resources": (
                local_resources
                if local_resources is not None
                else self.private_generation.local_resources
            )
        }
        if public_resources is not None:
            precommit_kwargs["public_resources"] = public_resources
        handle = store.precommit(
            invocation_ref,
            assignment,
            owner,
            self.private_generation.nonce,
            satisfaction,
            response_plan,
            evaluator_basis or self.evaluator_basis,
            **precommit_kwargs,
        )
        self.assertIsInstance(handle, OwnerLocalPrecommitmentHandle)
        assert isinstance(handle, OwnerLocalPrecommitmentHandle)
        return store, invocation_ref, handle, owner, assignment, satisfaction

    def test_private_generation_sidecar_is_closed_and_owner_local_only(self) -> None:
        private_input = self.private_generation
        self.assertEqual(private_input.witness, 7)
        self.assertEqual(private_input.nonce, 4)
        self.assertEqual(private_input.local_resources, LocalResourcePlan(2, 1, 2))
        self.assertFalse(hasattr(private_input, "identity"))
        self.assertFalse(hasattr(private_input, "term"))

        raw_value = load_bounded_json_bytes(
            PRIVATE_GENERATION_PATH.read_bytes(), maximum=4096
        )
        self.assertIsInstance(raw_value, dict)
        mutations = []
        for label in (
            "schema",
            "classification",
            "policy",
            "extra-key",
            "negative-value",
            "resource-shape",
        ):
            candidate = json.loads(json.dumps(raw_value))
            if label == "schema":
                candidate["schema"] = "zkc.r2.p01.private-generation-input.other"
            elif label == "classification":
                candidate["classification"] = "PortableSecretInput"
            elif label == "policy":
                candidate["policy"]["public_report_digest"] = True
            elif label == "extra-key":
                candidate["portable_id"] = "forbidden"
            elif label == "negative-value":
                candidate["nonce"] = -1
            else:
                candidate["local_resource_plan"]["max_trace_events"] = 5
            mutations.append((label, candidate))

        for label, candidate in mutations:
            with self.subTest(label=label), self.assertRaises(ValueError):
                _decode_private_generation_input(canonical_json_bytes(candidate))

    def test_fresh_and_fs_public_records_are_canonical(self) -> None:
        self.assertIsInstance(self.fresh_record, PortableExecutionRecord)
        self.assertIsInstance(self.fs_record, PortableExecutionRecord)
        self.assertIs(
            self.fresh_record.verifier_decision.disposition,
            Disposition.ACCEPT,
        )
        self.assertIs(
            self.fs_record.verifier_decision.disposition,
            Disposition.ACCEPT,
        )
        self.assertEqual(
            self.fresh_record.challenge_receipt.challenge,
            FRESH_CHALLENGE,
        )
        self.assertEqual(self.fresh_record.usage.hash_queries, 0)
        self.assertEqual(self.fs_record.challenge_receipt.challenge, FS_CHALLENGE)
        self.assertEqual(self.fs_record.usage.transcript_atoms, 2)
        self.assertEqual(self.fs_record.usage.hash_queries, 2)
        self.assertEqual(self.fs_record.usage.trace_events, 5)

    def test_public_identity_lanes_and_exports_are_typed(self) -> None:
        self.assertIsInstance(self.evaluator_basis.identity, ValidationBasisId)
        for invocation in (self.fresh_invocation, self.fs_invocation):
            self.assertIsInstance(invocation.identity, ArtifactContentId)
        for request in (self.fresh_request, self.fs_request):
            self.assertIsInstance(request.identity, ArtifactContentId)
            self.assertIsInstance(request.evaluator_basis_id, ValidationBasisId)
            self.assertIsInstance(request.public_case_bundle_id, ArtifactContentId)
        for record in (self.fresh_record, self.fs_record):
            self.assertIsInstance(record.identity, ArtifactContentId)
        for checked in (self.fresh_checked, self.fs_checked):
            self.assertIsInstance(checked, CheckedPublicExecution)
            self.assertIsInstance(checked.identity, EvidenceRecordId)
            statement = self._require_value(
                export_checked_public_statement(checked),
                "Statement export",
            )
            transcript = self._require_value(
                export_checked_public_transcript(checked),
                "transcript export",
            )
            self.assertIsInstance(statement.identity, EvidenceRecordId)
            self.assertIsInstance(statement.checked_execution_id, EvidenceRecordId)
            self.assertIsInstance(statement.record_id, ArtifactContentId)
            self.assertIsInstance(statement.source_event_id, ArtifactContentId)
            self.assertIsInstance(transcript.identity, EvidenceRecordId)
            self.assertIsInstance(transcript.checked_execution_id, EvidenceRecordId)
            self.assertIsInstance(transcript.invocation_id, ArtifactContentId)
            relations_view = self._require_value(
                issue_relations_checked_statement(checked),
                "Relations Statement view",
            )
            self.assertIsInstance(relations_view, CheckedPublicExecutionStatement)
            self.assertFalse(hasattr(relations_view, "identity"))
            self.assertFalse(hasattr(relations_view, "term"))

    def test_exact_public_requalification_preserves_the_evidence_record(self) -> None:
        for checked in (self.fresh_checked, self.fs_checked):
            with self.subTest(realization=checked.protocol.realization_kind.value):
                replayed = self._require_value(
                    requalify_public_execution(checked),
                    "public requalification",
                )
                self.assertEqual(replayed, checked)
                self.assertEqual(replayed.identity, checked.identity)
                self.assert_result(
                    check_checked_public_execution(checked),
                    Outcome.AFFIRMATIVE,
                    "checked-public-execution",
                    "P01-CHECKED-OK",
                )

        tampered_record = replace(
            self.fs_record,
            trace=self.fs_record.trace[:-1]
            + (replace(self.fs_record.trace[-1], value=Disposition.REJECT.value),),
        )
        tampered_checked = replace(
            self.fs_checked,
            replay_request=replace(
                self.fs_request,
                candidate=tampered_record,
            ),
        )
        self.assert_result(
            requalify_public_execution(tampered_checked),
            Outcome.MISMATCH,
            "public-replay:exact-record",
            "P01-REPLAY-003",
        )
        self.assert_result(
            check_fresh_public_execution(self.fresh_checked),
            Outcome.AFFIRMATIVE,
            "fresh-public-verification",
            "P01-FRESH-PUBLIC-OK",
        )

    def test_fs_vector_is_c6_z2_and_exact_proof_1002(self) -> None:
        self.assertEqual(self.fs_record.challenge_receipt.challenge, FS_CHALLENGE)
        decoded = DecodedFSProof(
            self.fs_interface.identity,
            COMMITMENT_VALUE,
            FS_RESPONSE,
        )
        encoded = self._require_value(
            encode_fs_proof(
                decoded,
                self.fs_interface,
                self.fs_protocol,
                self.construction,
                self.core,
                self.profile,
            ),
            "FS proof encoding",
        )
        self.assertEqual(encoded, FS_PROOF)
        self.assertEqual(encoded.hex(), "1002")
        self.assertIsInstance(fs_proof_artifact_id(encoded), ArtifactContentId)

    def test_public_fs_proof_accepts_and_uses_typed_evidence(self) -> None:
        verification = self._require_value(
            evaluate_fs_proof(
                FS_PROOF,
                self.fs_external_inputs,
                self.fs_interface,
                self.evaluator_basis,
                self.fs_protocol,
                self.construction,
                self.core,
                self.profile,
            ),
            "FS proof verification",
        )
        self.assertIsInstance(verification, FSVerificationRecord)
        self.assertIs(verification.disposition, Disposition.ACCEPT)
        self.assertEqual(verification.challenge, FS_CHALLENGE)
        self.assertEqual(verification.usage.transcript_atoms, 2)
        self.assertEqual(verification.usage.hash_queries, 2)
        self.assertEqual(verification.usage.trace_events, 5)
        self.assertEqual(verification.verification_executions, 1)
        self.assertEqual(
            verification.term()["usage"],
            {
                "transcript_atoms": 2,
                "hash_queries": 2,
                "trace_events": 5,
            },
        )
        self.assertEqual(verification.term()["verification_executions"], 1)
        self.assertIsInstance(verification.external_inputs_id, ArtifactContentId)
        self.assertIsInstance(verification.proof_artifact_id, ArtifactContentId)
        self.assertIsInstance(verification.verifier_basis_id, ValidationBasisId)
        self.assertIsInstance(verification.identity, EvidenceRecordId)
        self.assert_result(
            check_fs_proof(
                FS_PROOF,
                self.fs_external_inputs,
                self.fs_interface,
                self.evaluator_basis,
                self.fs_protocol,
                self.construction,
                self.core,
                self.profile,
            ),
            Outcome.AFFIRMATIVE,
            "fs-proof-verification",
            "P01-VERIFY-OK",
        )
        self.assert_result(
            check_fs_execution_projection(
                self.fs_checked,
                self.fs_interface,
                proof_bytes=FS_PROOF,
            ),
            Outcome.AFFIRMATIVE,
            "fs-execution-projection",
            "P01-FS-PROJECTION-OK",
        )

    def test_public_fs_proof_reject_is_not_checker_failure(self) -> None:
        rejecting_proof = bytes.fromhex("1003")
        verification = self._require_value(
            evaluate_fs_proof(
                rejecting_proof,
                self.fs_external_inputs,
                self.fs_interface,
                self.evaluator_basis,
                self.fs_protocol,
                self.construction,
                self.core,
                self.profile,
            ),
            "rejecting FS proof evaluation",
        )
        self.assertIsInstance(verification, FSVerificationRecord)
        self.assertIs(verification.disposition, Disposition.REJECT)
        self.assert_result(
            check_fs_proof(
                rejecting_proof,
                self.fs_external_inputs,
                self.fs_interface,
                self.evaluator_basis,
                self.fs_protocol,
                self.construction,
                self.core,
                self.profile,
            ),
            Outcome.SEMANTIC_NEGATIVE,
            "fs-proof-verification:terminal",
            "P01-VERIFY-002",
        )

    def test_projection_rejects_noncanonical_published_bytes(self) -> None:
        self.assert_result(
            check_fs_execution_projection(
                self.fs_checked,
                self.fs_interface,
                proof_bytes=bytes.fromhex("1003"),
            ),
            Outcome.MISMATCH,
            "fs-execution-projection:proof-bytes",
            "P01-FS-PROJECTION-002",
        )

    def test_proof_length_trailing_and_field_domain_fail_first(self) -> None:
        malformed_cases = (
            (b"\x10", Outcome.MALFORMED, "P01-PROOF-001"),
            (b"\x10\x02\x00", Outcome.MALFORMED, "P01-PROOF-001"),
            (b"\x00\x02", Outcome.SEMANTIC_NEGATIVE, "P01-PROOF-002"),
            (b"\x10\x0b", Outcome.SEMANTIC_NEGATIVE, "P01-PROOF-002"),
        )
        for proof, outcome, code in malformed_cases:
            with self.subTest(proof=proof.hex(), code=code):
                checked = check_fs_proof(
                    proof,
                    self.fs_external_inputs,
                    self.fs_interface,
                    self.evaluator_basis,
                    self.fs_protocol,
                    self.construction,
                    self.core,
                    self.profile,
                )
                boundary = (
                    "fs-proof-decoding:length"
                    if code == "P01-PROOF-001"
                    else "fs-proof-decoding:field-domain"
                )
                self.assert_result(checked, outcome, boundary, code)

    def test_public_replay_enforces_caller_and_basis_resource_bounds(self) -> None:
        caller_limits = (
            PublicResourcePlan(1, 2, 5, 1),
            PublicResourcePlan(2, 1, 5, 1),
            PublicResourcePlan(2, 2, 4, 1),
            PublicResourcePlan(2, 2, 5, 0),
        )
        for resources in caller_limits:
            with self.subTest(resources=resources):
                caller_limited = replace(
                    self.fs_request,
                    resources=resources,
                )
                self.assert_result(
                    qualify_public_execution(
                        caller_limited,
                        self.evaluator_basis,
                        self.fs_protocol,
                        self.profile,
                        self.core,
                        construction=self.construction,
                    ),
                    Outcome.RESOURCE_EXCEEDED,
                    "public-replay:resources",
                    "P01-REPLAY-004",
                )

        low_cap_basis = build_evaluator_basis(
            REPO_ROOT,
            (self.fresh_protocol.identity, self.fs_protocol.identity),
            PublicResourcePlan(2, 1, 5, 1),
        )
        basis_limited_request = replace(
            self.fs_request,
            evaluator_basis_id=low_cap_basis.identity,
        )
        self.assert_result(
            qualify_public_execution(
                basis_limited_request,
                low_cap_basis,
                self.fs_protocol,
                self.profile,
                self.core,
                construction=self.construction,
            ),
            Outcome.RESOURCE_EXCEEDED,
            "public-replay:resources",
            "P01-REPLAY-004",
        )

    def test_public_fs_proof_enforces_evaluator_resource_bounds(self) -> None:
        insufficient_basis = build_evaluator_basis(
            REPO_ROOT,
            (self.fs_protocol.identity,),
            PublicResourcePlan(0, 0, 0, 0),
        )
        self.assert_result(
            check_fs_proof(
                FS_PROOF,
                self.fs_external_inputs,
                self.fs_interface,
                insufficient_basis,
                self.fs_protocol,
                self.construction,
                self.core,
                self.profile,
            ),
            Outcome.RESOURCE_EXCEEDED,
            "fs-proof-verification:resources",
            "P01-VERIFY-004",
        )

    def test_protocol_support_is_required_by_replay_and_proof_verification(self) -> None:
        fresh_only_basis = build_evaluator_basis(
            REPO_ROOT,
            (self.fresh_protocol.identity,),
        )
        unsupported_request = replace(
            self.fs_request,
            evaluator_basis_id=fresh_only_basis.identity,
        )
        self.assert_result(
            qualify_public_execution(
                unsupported_request,
                fresh_only_basis,
                self.fs_protocol,
                self.profile,
                self.core,
                construction=self.construction,
            ),
            Outcome.MISMATCH,
            "public-replay:scope",
            "P01-REPLAY-002",
        )
        self.assert_result(
            evaluate_fs_proof(
                FS_PROOF,
                self.fs_external_inputs,
                self.fs_interface,
                fresh_only_basis,
                self.fs_protocol,
                self.construction,
                self.core,
                self.profile,
            ),
            Outcome.UNSUPPORTED,
            "fs-proof-verification:verifier-basis",
            "P01-VERIFY-003",
        )

    def test_owner_local_canonical_transition_and_qualification_for_both_variants(
        self,
    ) -> None:
        cases = (
            (
                self.fresh_prefix,
                self.fresh_protocol,
                self.fresh_record,
                {"fresh_challenge": self.fresh_binding},
            ),
            (
                self.fs_prefix,
                self.fs_protocol,
                self.fs_record,
                {},
            ),
        )
        for prefix, protocol, expected_record, finalization in cases:
            with self.subTest(realization=protocol.realization_kind.value):
                store, invocation_ref, handle, _, _, _ = (
                    self.allocate_precommitment(prefix, protocol)
                )
                generation = self._require_value(
                    generate_local_execution(
                        store,
                        invocation_ref,
                        handle,
                        **finalization,
                    ),
                    "canonical local generation",
                )
                self.assertIsInstance(generation, LocalGenerationRecord)
                self.assertIs(generation.invocation_ref, invocation_ref)
                self.assertIs(generation.precommitment_handle, handle)
                self.assertIs(generation.response_plan, ResponsePlan.CANONICAL)
                self.assertEqual(generation.portable_record, expected_record)
                self.assertIs(
                    generation.portable_record.verifier_decision.disposition,
                    Disposition.ACCEPT,
                )
                qualification = self._require_value(
                    qualify_local_generation(
                        store,
                        generation,
                        public_case_bundle_id=self.public_case_bundle_id,
                    ),
                    "local generation qualification",
                )
                self.assertIsInstance(
                    qualification,
                    LocalGenerationQualification,
                )
                self.assertIsNot(
                    qualification.audit_reconstruction,
                    qualification.generation,
                )
                self.assertEqual(
                    qualification.checked_public_execution.record,
                    expected_record,
                )
                self.assert_result(
                    check_local_generation_qualification(
                        store,
                        qualification,
                        public_case_bundle_id=self.public_case_bundle_id,
                    ),
                    Outcome.AFFIRMATIVE,
                    "local-generation-qualification",
                    "P01-LOCAL-QUAL-OK",
                )

    def test_staged_api_excludes_challenge_from_precommitment_phase(self) -> None:
        store = OwnerLocalBindingStore()
        self.assert_result(
            store.begin_invocation(
                self.fresh_invocation,
                self.fresh_protocol,
                self.profile,
                self.core,
                fresh=self.fresh,
            ),
            Outcome.MALFORMED,
            "public-invocation-prefix",
            "P01-INV-001",
        )

        store, invocation_ref, handle, _, _, _ = self.allocate_precommitment(
            self.fresh_prefix,
            self.fresh_protocol,
        )
        self.assert_result(
            store.resolve_challenge(invocation_ref),
            Outcome.REFUSED,
            "local-precommitment:causality",
            "P01-LOCAL-EXEC-002",
        )

        precommit_parameters = set(
            inspect.signature(OwnerLocalBindingStore.precommit).parameters
        )
        self.assertTrue(
            {
                "challenge",
                "fresh_challenge",
                "commitment",
            }.isdisjoint(precommit_parameters)
        )
        generation = self._require_value(
            generate_local_execution(
                store,
                invocation_ref,
                handle,
                fresh_challenge=self.fresh_binding,
            ),
            "Fresh staged generation",
        )
        self.assertEqual(
            [(receipt.source, receipt.stage) for receipt in generation.access_receipts],
            [
                ("local:nonce:r", "message:commitment"),
                ("public:challenge:c", "message:response"),
                ("local:witness:x", "message:response"),
            ],
        )
        resolved = store.resolve_challenge(invocation_ref)
        self.assertIsInstance(resolved, ChallengeReceipt)
        self.assertEqual(
            resolved,
            generation.portable_record.challenge_receipt,
        )

    def test_equal_content_invocation_occurrences_cannot_share_handles(self) -> None:
        equal_prefix = PublicInvocationPrefix(
            self.fs_prefix.algebra_profile_id,
            self.fs_prefix.core_id,
            self.fs_prefix.protocol_id,
            self.fs_prefix.statement,
            self.fs_prefix.application_context,
        )
        self.assertEqual(equal_prefix, self.fs_prefix)
        self.assertIsNot(equal_prefix, self.fs_prefix)

        store, first_ref, owner, assignment, satisfaction = (
            self.begin_owner_local_invocation(self.fs_prefix, self.fs_protocol)
        )
        second_ref = store.begin_invocation(
            equal_prefix,
            self.fs_protocol,
            self.profile,
            self.core,
            construction=self.construction,
        )
        self.assertIsInstance(second_ref, OwnerLocalInvocationRef)
        assert isinstance(second_ref, OwnerLocalInvocationRef)
        self.assertIsNot(first_ref, second_ref)

        handle = store.precommit(
            first_ref,
            assignment,
            owner,
            self.private_generation.nonce,
            satisfaction,
            ResponsePlan.CANONICAL,
            self.evaluator_basis,
            local_resources=self.private_generation.local_resources,
        )
        self.assertIsInstance(handle, OwnerLocalPrecommitmentHandle)
        assert isinstance(handle, OwnerLocalPrecommitmentHandle)
        self.assert_result(
            generate_local_execution(store, second_ref, handle),
            Outcome.REFUSED,
            "local-precommitment:authority",
            "P01-LOCAL-BIND-003",
        )
        generation = self._require_value(
            generate_local_execution(store, first_ref, handle),
            "exact occurrence finalization",
        )
        self.assertIs(generation.invocation_ref, first_ref)
        self.assertEqual(generation.portable_record, self.fs_record)

    def test_equal_content_completed_invocation_substitution_lacks_authority(
        self,
    ) -> None:
        store, invocation_ref, handle, _, _, _ = self.allocate_precommitment(
            self.fs_prefix,
            self.fs_protocol,
        )
        generation = self._require_value(
            generate_local_execution(store, invocation_ref, handle),
            "exact completed invocation",
        )
        equal_invocation = PublicInvocation(
            generation.invocation.algebra_profile_id,
            generation.invocation.core_id,
            generation.invocation.protocol_id,
            generation.invocation.statement,
            generation.invocation.application_context,
            generation.invocation.fresh_challenge,
        )
        self.assertEqual(equal_invocation, generation.invocation)
        self.assertIsNot(equal_invocation, generation.invocation)
        substituted = LocalGenerationRecord(
            invocation_ref=generation.invocation_ref,
            invocation=equal_invocation,
            precommitment_handle=generation.precommitment_handle,
            response_plan=generation.response_plan,
            evaluator_basis=generation.evaluator_basis,
            protocol=generation.protocol,
            profile=generation.profile,
            core=generation.core,
            fresh=generation.fresh,
            construction=generation.construction,
            public_resources=generation.public_resources,
            local_resources=generation.local_resources,
            portable_record=generation.portable_record,
            local_usage=generation.local_usage,
            access_receipts=generation.access_receipts,
        )
        self.assert_result(
            qualify_local_generation(
                store,
                substituted,
                public_case_bundle_id=self.public_case_bundle_id,
            ),
            Outcome.REFUSED,
            "local-generation-qualification:authority",
            "P01-LOCAL-QUAL-001",
        )

    def test_precommitment_and_finalization_are_single_use(self) -> None:
        store, invocation_ref, handle, owner, assignment, satisfaction = (
            self.allocate_precommitment(self.fs_prefix, self.fs_protocol)
        )
        self.assert_result(
            store.precommit(
                invocation_ref,
                assignment,
                owner,
                self.private_generation.nonce,
                satisfaction,
                ResponsePlan.CANONICAL,
                self.evaluator_basis,
                local_resources=self.private_generation.local_resources,
            ),
            Outcome.REFUSED,
            "local-precommitment:occurrence",
            "P01-LOCAL-BIND-003",
        )
        generation = self._require_value(
            generate_local_execution(store, invocation_ref, handle),
            "first finalization",
        )
        self.assertEqual(generation.portable_record, self.fs_record)
        self.assert_result(
            generate_local_execution(store, invocation_ref, handle),
            Outcome.REFUSED,
            "local-precommitment:single-use",
            "P01-LOCAL-BIND-003",
        )

    def test_fs_caller_cannot_override_challenge_and_failed_attempt_is_consuming(
        self,
    ) -> None:
        store, invocation_ref, handle, _, _, _ = self.allocate_precommitment(
            self.fs_prefix,
            self.fs_protocol,
        )
        self.assert_result(
            generate_local_execution(
                store,
                invocation_ref,
                handle,
                fresh_challenge=self.fresh_binding,
            ),
            Outcome.SEMANTIC_NEGATIVE,
            "local-finalization:fs-challenge",
            "P01-LOCAL-EXEC-001",
        )
        self.assert_result(
            store.resolve_challenge(invocation_ref),
            Outcome.REFUSED,
            "local-precommitment:causality",
            "P01-LOCAL-EXEC-002",
        )
        self.assert_result(
            generate_local_execution(store, invocation_ref, handle),
            Outcome.REFUSED,
            "local-precommitment:single-use",
            "P01-LOCAL-BIND-003",
        )

    def test_missing_or_malformed_fresh_finalization_consumes_handle(self) -> None:
        malformed_binding = replace(
            self.fresh_binding,
            value=self.profile.challenge_size,
        )
        cases = (
            (
                "missing",
                {},
                Outcome.MALFORMED,
                "local-finalization:fresh-challenge",
                "P01-LOCAL-EXEC-001",
            ),
            (
                "malformed",
                {"fresh_challenge": malformed_binding},
                Outcome.MISMATCH,
                "public-invocation:fresh-input",
                "P01-INV-004",
            ),
        )
        for label, finalization, outcome, boundary, code in cases:
            with self.subTest(label=label):
                store, invocation_ref, handle, _, _, _ = (
                    self.allocate_precommitment(
                        self.fresh_prefix,
                        self.fresh_protocol,
                    )
                )
                self.assert_result(
                    generate_local_execution(
                        store,
                        invocation_ref,
                        handle,
                        **finalization,
                    ),
                    outcome,
                    boundary,
                    code,
                )
                self.assert_result(
                    store.resolve_challenge(invocation_ref),
                    Outcome.REFUSED,
                    "local-precommitment:causality",
                    "P01-LOCAL-EXEC-002",
                )
                self.assert_result(
                    generate_local_execution(
                        store,
                        invocation_ref,
                        handle,
                        fresh_challenge=self.fresh_binding,
                    ),
                    Outcome.REFUSED,
                    "local-precommitment:single-use",
                    "P01-LOCAL-BIND-003",
                )

    def test_finalization_has_no_commitment_semantic_or_resource_overrides(
        self,
    ) -> None:
        parameters = set(inspect.signature(generate_local_execution).parameters)
        self.assertEqual(
            parameters,
            {
                "store",
                "invocation_ref",
                "precommitment_handle",
                "fresh_challenge",
            },
        )
        self.assertTrue(
            {
                "commitment",
                "response_plan",
                "evaluator_basis",
                "protocol",
                "profile",
                "core",
                "fresh",
                "construction",
                "public_resources",
                "local_resources",
            }.isdisjoint(parameters)
        )

        store, invocation_ref, handle, _, _, _ = self.allocate_precommitment(
            self.fs_prefix,
            self.fs_protocol,
        )
        generation = self._require_value(
            generate_local_execution(store, invocation_ref, handle),
            "frozen FS finalization",
        )
        self.assertEqual(generation.portable_record, self.fs_record)
        self.assertEqual(
            generation.portable_record.trace[0].value,
            COMMITMENT_VALUE,
        )
        self.assertEqual(
            generation.portable_record.challenge_receipt.challenge,
            FS_CHALLENGE,
        )

    def test_local_generation_enforces_frozen_local_public_and_protocol_bounds(
        self,
    ) -> None:
        store, invocation_ref, owner, assignment, satisfaction = (
            self.begin_owner_local_invocation(self.fs_prefix, self.fs_protocol)
        )
        self.assert_result(
            store.precommit(
                invocation_ref,
                assignment,
                owner,
                self.private_generation.nonce,
                satisfaction,
                ResponsePlan.CANONICAL,
                self.evaluator_basis,
                local_resources=LocalResourcePlan(1, 1, 2),
            ),
            Outcome.RESOURCE_EXCEEDED,
            "local-generation:resources",
            "P01-LOCAL-EXEC-003",
        )
        retry_handle = store.precommit(
            invocation_ref,
            assignment,
            owner,
            self.private_generation.nonce,
            satisfaction,
            ResponsePlan.CANONICAL,
            self.evaluator_basis,
            local_resources=self.private_generation.local_resources,
        )
        self.assertIsInstance(retry_handle, OwnerLocalPrecommitmentHandle)
        assert isinstance(retry_handle, OwnerLocalPrecommitmentHandle)
        retried = self._require_value(
            generate_local_execution(store, invocation_ref, retry_handle),
            "transactional precommit validation retry",
        )
        self.assertEqual(retried.portable_record, self.fs_record)

        bounded_store, bounded_ref, bounded_handle, _, _, _ = (
            self.allocate_precommitment(
                self.fs_prefix,
                self.fs_protocol,
                public_resources=PublicResourcePlan(2, 1, 5, 1),
            )
        )
        self.assert_result(
            generate_local_execution(bounded_store, bounded_ref, bounded_handle),
            Outcome.RESOURCE_EXCEEDED,
            "local-generation:public-resources",
            "P01-LOCAL-EXEC-003",
        )
        bounded_receipt = bounded_store.resolve_challenge(bounded_ref)
        self.assertIsInstance(bounded_receipt, ChallengeReceipt)
        assert isinstance(bounded_receipt, ChallengeReceipt)
        self.assertEqual(bounded_receipt.challenge, FS_CHALLENGE)

        fresh_only_basis = build_evaluator_basis(
            REPO_ROOT,
            (self.fresh_protocol.identity,),
        )
        unsupported_store, unsupported_ref, owner, assignment, satisfaction = (
            self.begin_owner_local_invocation(self.fs_prefix, self.fs_protocol)
        )
        self.assert_result(
            unsupported_store.precommit(
                unsupported_ref,
                assignment,
                owner,
                self.private_generation.nonce,
                satisfaction,
                ResponsePlan.CANONICAL,
                fresh_only_basis,
                local_resources=self.private_generation.local_resources,
            ),
            Outcome.UNSUPPORTED,
            "local-generation:protocol-support",
            "P01-LOCAL-EXEC-001",
        )

    def test_abort_is_local_refusal_while_invalid_response_is_public_reject(
        self,
    ) -> None:
        abort_store, abort_ref, abort_handle, _, _, _ = (
            self.allocate_precommitment(
                self.fs_prefix,
                self.fs_protocol,
                ResponsePlan.ABORT,
            )
        )
        aborted = generate_local_execution(
            abort_store,
            abort_ref,
            abort_handle,
        )
        self.assert_result(
            aborted,
            Outcome.REFUSED,
            "local-generation:explicit-abort",
            "P01-LOCAL-EXEC-004",
        )
        self.assertNotIsInstance(aborted, LocalGenerationRecord)
        abort_receipt = abort_store.resolve_challenge(abort_ref)
        self.assertIsInstance(abort_receipt, ChallengeReceipt)
        assert isinstance(abort_receipt, ChallengeReceipt)
        self.assertEqual(abort_receipt.challenge, FS_CHALLENGE)
        self.assert_result(
            generate_local_execution(abort_store, abort_ref, abort_handle),
            Outcome.REFUSED,
            "local-precommitment:single-use",
            "P01-LOCAL-BIND-003",
        )

        invalid_store, invalid_ref, invalid_handle, _, _, _ = (
            self.allocate_precommitment(
                self.fs_prefix,
                self.fs_protocol,
                ResponsePlan.INVALID,
            )
        )
        invalid = self._require_value(
            generate_local_execution(
                invalid_store,
                invalid_ref,
                invalid_handle,
            ),
            "invalid-response local generation",
        )
        self.assertIsInstance(invalid, LocalGenerationRecord)
        self.assertIs(
            invalid.portable_record.verifier_decision.disposition,
            Disposition.REJECT,
        )
        qualification = self._require_value(
            qualify_local_generation(
                invalid_store,
                invalid,
                public_case_bundle_id=self.public_case_bundle_id,
            ),
            "invalid-response exact qualification",
        )
        self.assertIs(
            qualification.checked_public_execution.record.verifier_decision.disposition,
            Disposition.REJECT,
        )
        self.assert_result(
            check_fs_proof(
                bytes.fromhex("1003"),
                self.fs_external_inputs,
                self.fs_interface,
                self.evaluator_basis,
                self.fs_protocol,
                self.construction,
                self.core,
                self.profile,
            ),
            Outcome.SEMANTIC_NEGATIVE,
            "fs-proof-verification:terminal",
            "P01-VERIFY-002",
        )

    def test_precommitment_requires_exact_satisfied_assignment_and_owner(
        self,
    ) -> None:
        owner, assignment, satisfaction = self.new_satisfaction_authority()
        same_scalar_other_occurrence = owner.allocate_witness(
            self.instance, self.private_generation.witness
        )
        foreign_owner = RelationSatisfactionOwner()
        store = OwnerLocalBindingStore()

        exact_ref = store.begin_invocation(
            self.fs_prefix,
            self.fs_protocol,
            self.profile,
            self.core,
            construction=self.construction,
        )
        self.assertIsInstance(exact_ref, OwnerLocalInvocationRef)
        exact = store.precommit(
            exact_ref,
            assignment,
            owner,
            self.private_generation.nonce,
            satisfaction,
            ResponsePlan.CANONICAL,
            self.evaluator_basis,
            local_resources=self.private_generation.local_resources,
        )
        self.assertIsInstance(exact, OwnerLocalPrecommitmentHandle)

        for candidate_assignment, candidate_owner in (
            (same_scalar_other_occurrence, owner),
            (assignment, foreign_owner),
        ):
            candidate_ref = store.begin_invocation(
                self.fs_prefix,
                self.fs_protocol,
                self.profile,
                self.core,
                construction=self.construction,
            )
            self.assertIsInstance(candidate_ref, OwnerLocalInvocationRef)
            with self.subTest(
                assignment_is_exact=candidate_assignment is assignment,
                owner_is_exact=candidate_owner is owner,
            ):
                self.assert_result(
                    store.precommit(
                        candidate_ref,
                        candidate_assignment,
                        candidate_owner,
                        self.private_generation.nonce,
                        satisfaction,
                        ResponsePlan.CANONICAL,
                        self.evaluator_basis,
                        local_resources=self.private_generation.local_resources,
                    ),
                    Outcome.REFUSED,
                    "owner-local-binding:relation-authority",
                    "P01-LOCAL-BIND-002",
                )

    def test_foreign_fabricated_and_wrong_owner_local_coordinates_are_refused(
        self,
    ) -> None:
        owning_store, invocation_ref, handle, _, _, _ = (
            self.allocate_precommitment(self.fs_prefix, self.fs_protocol)
        )
        foreign_store = OwnerLocalBindingStore()
        foreign_ref = foreign_store.begin_invocation(
            self.fs_prefix,
            self.fs_protocol,
            self.profile,
            self.core,
            construction=self.construction,
        )
        self.assertIsInstance(foreign_ref, OwnerLocalInvocationRef)
        assert isinstance(foreign_ref, OwnerLocalInvocationRef)

        fabricated_ref = OwnerLocalInvocationRef(object(), object(), 0)
        fabricated_handle = OwnerLocalPrecommitmentHandle(object(), object(), 0)
        cases = (
            (foreign_store, invocation_ref, handle),
            (owning_store, foreign_ref, handle),
            (owning_store, fabricated_ref, handle),
            (owning_store, invocation_ref, fabricated_handle),
        )
        for store, candidate_ref, candidate_handle in cases:
            with self.subTest(
                foreign_store=store is foreign_store,
                fabricated_ref=candidate_ref is fabricated_ref,
                fabricated_handle=candidate_handle is fabricated_handle,
            ):
                self.assert_result(
                    generate_local_execution(
                        store,
                        candidate_ref,
                        candidate_handle,
                    ),
                    Outcome.REFUSED,
                    "local-precommitment:authority",
                    "P01-LOCAL-BIND-003",
                )

        self.assert_result(
            foreign_store.resolve_challenge(invocation_ref),
            Outcome.REFUSED,
            "local-precommitment:authority",
            "P01-LOCAL-BIND-003",
        )
        generation = self._require_value(
            generate_local_execution(owning_store, invocation_ref, handle),
            "exact owner-local coordinates",
        )
        self.assertEqual(generation.portable_record, self.fs_record)

    def test_unprecommitted_invocation_cannot_finalize_with_fabricated_handle(
        self,
    ) -> None:
        store, invocation_ref, _, _, _ = self.begin_owner_local_invocation(
            self.fs_prefix,
            self.fs_protocol,
        )
        fabricated_handle = OwnerLocalPrecommitmentHandle(object(), object(), 0)
        self.assert_result(
            generate_local_execution(store, invocation_ref, fabricated_handle),
            Outcome.REFUSED,
            "local-precommitment:authority",
            "P01-LOCAL-BIND-003",
        )

    def test_owner_local_values_are_nonserializable_and_portable_record_is_clean(
        self,
    ) -> None:
        store, invocation_ref, handle, owner, assignment, satisfaction = (
            self.allocate_precommitment(self.fs_prefix, self.fs_protocol)
        )
        generation = self._require_value(
            generate_local_execution(store, invocation_ref, handle),
            "owner-local generation",
        )
        qualification = self._require_value(
            qualify_local_generation(
                store,
                generation,
                public_case_bundle_id=self.public_case_bundle_id,
            ),
            "owner-local qualification",
        )
        local_values = (
            owner,
            assignment.local_occurrence,
            assignment,
            satisfaction,
            invocation_ref,
            handle,
            generation,
            *generation.access_receipts,
            qualification,
        )
        for value in local_values:
            with self.subTest(local_type=type(value).__name__):
                self.assertFalse(hasattr(value, "identity"))
                self.assertFalse(hasattr(value, "term"))
                with self.assertRaises(TypeError):
                    pickle.dumps(value)

        portable = generation.portable_record
        self.assertEqual(pickle.loads(pickle.dumps(portable)), portable)
        rendered = json.dumps(portable.term(), sort_keys=True).lower()
        for forbidden in (
            "private",
            "owner",
            "witness",
            "nonce",
            "strategy",
            "response_plan",
            "access_receipt",
            "secret_scalar",
        ):
            with self.subTest(forbidden=forbidden):
                self.assertNotIn(forbidden, rendered)

    def test_read_only_audit_survives_consumption_without_resurrecting_handle(
        self,
    ) -> None:
        store, invocation_ref, handle, _, _, _ = self.allocate_precommitment(
            self.fs_prefix,
            self.fs_protocol,
        )
        honest = self._require_value(
            generate_local_execution(store, invocation_ref, handle),
            "canonical local generation",
        )
        invalid_store, invalid_ref, invalid_handle, _, _, _ = (
            self.allocate_precommitment(
                self.fs_prefix,
                self.fs_protocol,
                ResponsePlan.INVALID,
            )
        )
        invalid = self._require_value(
            generate_local_execution(
                invalid_store,
                invalid_ref,
                invalid_handle,
            ),
            "invalid local generation",
        )
        self.assert_result(
            generate_local_execution(store, invocation_ref, handle),
            Outcome.REFUSED,
            "local-precommitment:single-use",
            "P01-LOCAL-BIND-003",
        )

        qualification = self._require_value(
            qualify_local_generation(
                store,
                honest,
                public_case_bundle_id=self.public_case_bundle_id,
            ),
            "canonical local qualification",
        )
        self.assertEqual(
            qualification.audit_reconstruction.portable_record,
            honest.portable_record,
        )
        self.assert_result(
            check_local_generation_qualification(
                store,
                qualification,
                public_case_bundle_id=self.public_case_bundle_id,
            ),
            Outcome.AFFIRMATIVE,
            "local-generation-qualification",
            "P01-LOCAL-QUAL-OK",
        )
        audit_view_qualification = self._require_value(
            qualify_local_generation(
                store,
                qualification.audit_reconstruction,
                public_case_bundle_id=self.public_case_bundle_id,
            ),
            "non-authoritative equal-coordinate audit view",
        )
        self.assertIs(
            audit_view_qualification.generation,
            qualification.audit_reconstruction,
        )
        self.assertEqual(
            audit_view_qualification.checked_public_execution,
            qualification.checked_public_execution,
        )
        self.assert_result(
            generate_local_execution(store, invocation_ref, handle),
            Outcome.REFUSED,
            "local-precommitment:single-use",
            "P01-LOCAL-BIND-003",
        )

        with self.assertRaises(AttributeError):
            honest.portable_record = invalid.portable_record
        with self.assertRaises(AttributeError):
            honest.access_receipts[0].stage = "tampered"
        with self.assertRaises(AttributeError):
            qualification.audit_reconstruction = invalid

        forged_audit = LocalGenerationQualification(
            qualification.generation,
            invalid,
            qualification.checked_public_execution,
        )
        self.assert_result(
            check_local_generation_qualification(
                store,
                forged_audit,
                public_case_bundle_id=self.public_case_bundle_id,
            ),
            Outcome.MISMATCH,
            "local-generation-qualification:retained-audit",
            "P01-LOCAL-QUAL-001",
        )

        forged_public = LocalGenerationQualification(
            qualification.generation,
            qualification.audit_reconstruction,
            self.fresh_checked,
        )
        self.assert_result(
            check_local_generation_qualification(
                store,
                forged_public,
                public_case_bundle_id=self.public_case_bundle_id,
            ),
            Outcome.MISMATCH,
            "local-generation-qualification:retained-public-evidence",
            "P01-LOCAL-QUAL-001",
        )

        corrupted = LocalGenerationQualification(
            qualification.generation,
            qualification.audit_reconstruction,
            qualification.checked_public_execution,
        )
        object.__setattr__(corrupted, "audit_reconstruction", invalid)
        self.assert_result(
            check_local_generation_qualification(
                store,
                corrupted,
                public_case_bundle_id=self.public_case_bundle_id,
            ),
            Outcome.MISMATCH,
            "local-generation-qualification:retained-audit",
            "P01-LOCAL-QUAL-001",
        )


if __name__ == "__main__":
    unittest.main()
