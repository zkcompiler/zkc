from __future__ import annotations

from dataclasses import replace
from pathlib import Path
import hashlib
import sys
import unittest


MODEL_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(MODEL_ROOT))

from p01model.relations import (
    ApplicabilityClaim,
    QualifiedExecutionStatement,
    SchnorrRelationInstance,
    SchnorrWitnessAssignment,
    TranscriptFork,
    admit_instance,
    admit_relation,
    admit_witness_assignment,
    canonical_schnorr_relation,
    check_accepting_transcript,
    check_grounding_shape,
    check_relation_satisfaction,
    check_special_soundness_fork,
    exhaustive_shvzk_distribution_equality,
    exhaustive_special_soundness,
    grounding_candidate,
    honest_transcript,
    probe_analysis_applicability,
)
from p01model.semantic import (
    APPLICATION_CONTEXT,
    CHALLENGE,
    CHECK,
    COMMITMENT,
    RESPONSE,
    STATEMENT,
    TERMINAL,
    AlgebraProfile,
    OccurrenceActor,
    OccurrenceContract,
    OccurrenceKind,
    ParticipantRole,
    TranscriptAtom,
    admit_algebra,
    admit_application_context,
    admit_core,
    admit_fresh_realization,
    admit_honest_prover_contract,
    admit_protocol,
    admit_transcript_construction,
    application_context_domain_id,
    canonical_core,
    canonical_honest_prover_contract,
    canonical_runtime_context_contract,
    canonical_transcript_construction,
    challenge_domain_id,
    check_public_coin_eligibility,
    check_schnorr_correspondence,
    checked_fs_factorization,
    derive_fs_challenge,
    fresh_conditional_kernel_contract_id,
    group_domain_id,
    group_parameters_id,
    make_fresh_protocol,
    make_fs_protocol,
    mutate_construction,
    mutate_core,
    public_challenge_prefix_id,
    required_challenge_atoms,
    scalar_domain_id,
)
from p01model.terms import Outcome, Result, semantic_id


def _replace_occurrence(core: object, occurrence: str, **changes: object) -> object:
    contracts = tuple(
        replace(contract, **changes)
        if contract.occurrence == occurrence
        else contract
        for contract in core.occurrences
    )
    return mutate_core(core, occurrences=contracts)


def _closed_id(label: str) -> str:
    return semantic_id("p01.test.closed-id.v1", {"label": label})


class ResultAssertions(unittest.TestCase):
    def assert_result(
        self,
        checked: object,
        outcome: Outcome,
        boundary: str,
        code: str,
    ) -> None:
        self.assertIsInstance(checked, Result)
        self.assertEqual(checked.outcome, outcome)
        self.assertEqual(checked.boundary, boundary)
        self.assertEqual(checked.code, code)


class P01SemanticAdmissionTest(ResultAssertions):
    """First-failure tests for the challenge-neutral ConversationCore.v2."""

    def setUp(self) -> None:
        self.profile = AlgebraProfile(p=23, q=11, generator=2, challenge_size=8)
        self.core = canonical_core(self.profile)
        self.construction = canonical_transcript_construction(
            self.core, self.profile
        )
        self.fresh_protocol, self.fresh = make_fresh_protocol(
            self.core, self.profile
        )
        self.fs_protocol = make_fs_protocol(
            self.core, self.construction, self.profile
        )

    def test_canonical_fresh_and_fs_variants_are_admitted(self) -> None:
        checks = (
            (admit_algebra(self.profile), "algebra-profile", "P01-ALG-OK"),
            (admit_core(self.core, self.profile), "core-admission", "P01-CORE-OK"),
            (
                check_public_coin_eligibility(self.core, self.profile),
                "source-correspondence:public-coin-eligibility",
                "P01-PCOIN-OK",
            ),
            (
                check_schnorr_correspondence(self.core, self.profile),
                "source-correspondence:sigma",
                "P01-CORR-OK",
            ),
            (
                admit_transcript_construction(
                    self.construction, self.core, self.profile
                ),
                "transcript-construction",
                "P01-FS-OK",
            ),
            (
                admit_fresh_realization(self.fresh, self.core, self.profile),
                "fresh-realization",
                "P01-FRESH-OK",
            ),
            (
                admit_protocol(
                    self.fresh_protocol,
                    self.core,
                    self.profile,
                    fresh=self.fresh,
                ),
                "protocol-admission",
                "P01-PROTO-OK",
            ),
            (
                admit_protocol(
                    self.fs_protocol,
                    self.core,
                    self.profile,
                    construction=self.construction,
                ),
                "protocol-admission",
                "P01-PROTO-OK",
            ),
        )
        for checked, boundary, code in checks:
            with self.subTest(code=code):
                self.assert_result(checked, Outcome.AFFIRMATIVE, boundary, code)

    def test_closed_grammar_gates_raw_objects_and_raw_nested_fields(self) -> None:
        raw_core = _replace_occurrence(self.core, COMMITMENT, actor="Prover")
        raw_construction = replace(self.construction, atoms=("raw-atom",))
        raw_fresh = replace(self.fresh, resolver="PublicEnvironment")
        raw_protocol = replace(
            self.fresh_protocol,
            realization_kind="FreshPublicCoin",
        )
        cases = (
            (admit_algebra("raw"), "algebra-profile", "P01-ALG-001"),
            (admit_core("raw", self.profile), "core-admission", "P01-CORE-001"),
            (admit_core(raw_core, self.profile), "core-admission", "P01-CORE-001"),
            (
                admit_transcript_construction("raw", self.core, self.profile),
                "transcript-construction",
                "P01-FS-000",
            ),
            (
                admit_transcript_construction(
                    raw_construction, self.core, self.profile
                ),
                "transcript-construction",
                "P01-FS-000",
            ),
            (
                admit_fresh_realization(raw_fresh, self.core, self.profile),
                "fresh-realization",
                "P01-FRESH-000",
            ),
            (
                admit_protocol(raw_protocol, self.core, self.profile),
                "protocol-admission",
                "P01-PROTO-000",
            ),
        )
        for checked, boundary, code in cases:
            with self.subTest(boundary=boundary, code=code):
                self.assert_result(checked, Outcome.MALFORMED, boundary, code)

    def test_algebra_malformed_negative_and_unsupported_are_distinct(self) -> None:
        malformed = replace(self.profile, p="23")
        non_prime = replace(self.profile, p=21)
        unsupported = replace(self.profile, group_codec="compressed-group.v9")
        self.assert_result(
            admit_algebra(malformed),
            Outcome.MALFORMED,
            "algebra-profile",
            "P01-ALG-001",
        )
        self.assert_result(
            admit_algebra(non_prime),
            Outcome.SEMANTIC_NEGATIVE,
            "algebra-profile",
            "P01-ALG-002",
        )
        self.assert_result(
            admit_algebra(unsupported),
            Outcome.UNSUPPORTED,
            "algebra-profile",
            "P01-ALG-007",
        )

    def test_schedule_and_visibility_are_derived_from_core_occurrence_contracts(self) -> None:
        self.assertEqual(self.core.public_statements, (STATEMENT,))
        self.assertEqual(self.core.proof_messages, (COMMITMENT, RESPONSE))
        self.assertNotIn(
            APPLICATION_CONTEXT,
            tuple(contract.occurrence for contract in self.core.occurrences),
        )
        self.assertEqual(
            self.core.schedule,
            (COMMITMENT, CHALLENGE, RESPONSE, CHECK, TERMINAL),
        )
        before_commitment = self.core.visible_public_before(
            ParticipantRole.PROVER, COMMITMENT
        )
        before_response = self.core.visible_public_before(
            ParticipantRole.PROVER, RESPONSE
        )
        self.assertEqual(before_commitment, (STATEMENT,))
        self.assertNotIn(CHALLENGE, before_commitment)
        self.assertEqual(
            before_response,
            (STATEMENT, COMMITMENT, CHALLENGE),
        )

    def test_semantic_identities_depend_on_minimal_bases_not_evaluation_bundle_ids(self) -> None:
        narrower_challenge_profile = replace(self.profile, challenge_size=4)
        self.assertNotEqual(
            self.profile.identity,
            narrower_challenge_profile.identity,
        )
        self.assertEqual(
            group_parameters_id(self.profile),
            group_parameters_id(narrower_challenge_profile),
        )
        self.assertEqual(
            group_domain_id(self.profile),
            group_domain_id(narrower_challenge_profile),
        )
        self.assertEqual(
            scalar_domain_id(self.profile),
            scalar_domain_id(narrower_challenge_profile),
        )
        self.assertEqual(
            canonical_schnorr_relation(self.profile).identity,
            canonical_schnorr_relation(narrower_challenge_profile).identity,
        )
        self.assertNotEqual(
            challenge_domain_id(self.profile),
            challenge_domain_id(narrower_challenge_profile),
        )
        self.assertNotEqual(
            self.core.identity,
            canonical_core(narrower_challenge_profile).identity,
        )
        self.assertNotIn("evaluation_profile_id", self.core.term())

    def test_fs_runtime_context_is_not_a_core_occurrence(self) -> None:
        context_occurrence = OccurrenceContract(
            APPLICATION_CONTEXT,
            OccurrenceKind.INITIAL_PUBLIC_INPUT,
            OccurrenceActor.PUBLIC_ENVIRONMENT,
            self.core.roles,
            application_context_domain_id(),
            "bounded-utf8.v1",
            "ApplicationContext",
            _closed_id("application-context-in-core"),
        )
        candidate = mutate_core(
            self.core,
            occurrences=(
                self.core.occurrences[0],
                context_occurrence,
                *self.core.occurrences[1:],
            ),
        )
        self.assert_result(
            admit_core(candidate, self.profile),
            Outcome.SEMANTIC_NEGATIVE,
            f"core-admission:occurrence-contract:{APPLICATION_CONTEXT}",
            "P01-CORE-006",
        )

    def test_schnorr_actor_direction_domain_codec_and_purpose_are_profile_owned(self) -> None:
        commitment = self.core.contract_for(COMMITMENT)
        response = self.core.contract_for(RESPONSE)
        mutations = (
            {"actor": OccurrenceActor.VERIFIER},
            {"recipients": (ParticipantRole.PROVER,)},
            {"value_domain_id": scalar_domain_id(self.profile)},
            {"codec": self.profile.scalar_codec},
            {"semantic_purpose": "Auxiliary"},
            {"semantic_contract_id": response.semantic_contract_id},
        )
        for changes in mutations:
            with self.subTest(changes=changes):
                candidate = _replace_occurrence(
                    self.core, COMMITMENT, **changes
                )
                self.assert_result(
                    admit_core(candidate, self.profile),
                    Outcome.AFFIRMATIVE,
                    "core-admission",
                    "P01-CORE-OK",
                )
                self.assert_result(
                    check_schnorr_correspondence(candidate, self.profile),
                    Outcome.SEMANTIC_NEGATIVE,
                    f"source-correspondence:sigma-contract:{COMMITMENT}",
                    "P01-CORR-002",
                )
        self.assertEqual(commitment.value_domain_id, group_domain_id(self.profile))

    def test_check_contract_must_agree_before_source_correspondence(self) -> None:
        foreign_contract = self.core.contract_for(COMMITMENT).semantic_contract_id
        occurrence_only = _replace_occurrence(
            self.core,
            CHECK,
            semantic_contract_id=foreign_contract,
        )
        self.assert_result(
            admit_core(occurrence_only, self.profile),
            Outcome.SEMANTIC_NEGATIVE,
            f"core-admission:deterministic-rule:{CHECK}",
            "P01-CORE-008",
        )

        internally_agreed = mutate_core(
            occurrence_only,
            verifier_check=replace(
                occurrence_only.verifier_check,
                semantic_contract_id=foreign_contract,
            ),
        )
        self.assert_result(
            admit_core(internally_agreed, self.profile),
            Outcome.AFFIRMATIVE,
            "core-admission",
            "P01-CORE-OK",
        )
        self.assert_result(
            check_schnorr_correspondence(internally_agreed, self.profile),
            Outcome.SEMANTIC_NEGATIVE,
            f"source-correspondence:sigma-contract:{CHECK}",
            "P01-CORR-002",
        )

    def test_verifier_operand_binding_and_terminal_route_are_exact(self) -> None:
        wrong_operands = mutate_core(
            self.core,
            verifier_check=replace(
                self.core.verifier_check,
                named_inputs=(
                    ("statement", STATEMENT),
                    ("commitment", COMMITMENT),
                    ("challenge", CHALLENGE),
                    ("response", CHALLENGE),
                ),
            ),
        )
        wrong_terminal = mutate_core(
            self.core,
            terminal_route=replace(
                self.core.terminal_route,
                named_inputs=(("check", RESPONSE),),
            ),
        )
        for candidate in (wrong_operands, wrong_terminal):
            with self.subTest(core_id=candidate.identity):
                self.assert_result(
                    admit_core(candidate, self.profile),
                    Outcome.AFFIRMATIVE,
                    "core-admission",
                    "P01-CORE-OK",
                )
                self.assert_result(
                    check_schnorr_correspondence(candidate, self.profile),
                    Outcome.SEMANTIC_NEGATIVE,
                    "source-correspondence:sigma-deterministic-rules",
                    "P01-CORR-003",
                )

    def test_future_operand_binding_fails_core_availability(self) -> None:
        candidate = mutate_core(
            self.core,
            verifier_check=replace(
                self.core.verifier_check,
                named_inputs=self.core.verifier_check.named_inputs
                + (("future", TERMINAL),),
            ),
        )
        self.assert_result(
            admit_core(candidate, self.profile),
            Outcome.SEMANTIC_NEGATIVE,
            f"core-availability:{CHECK}",
            "P01-CORE-009",
        )

    def test_required_occurrence_totality_rejects_omission_without_key_error(self) -> None:
        without_commitment = mutate_core(
            self.core,
            occurrences=tuple(
                contract
                for contract in self.core.occurrences
                if contract.occurrence != COMMITMENT
            ),
            verifier_check=replace(
                self.core.verifier_check,
                named_inputs=tuple(
                    binding
                    for binding in self.core.verifier_check.named_inputs
                    if binding[1] != COMMITMENT
                ),
            ),
        )
        self.assert_result(
            admit_core(without_commitment, self.profile),
            Outcome.AFFIRMATIVE,
            "core-admission",
            "P01-CORE-OK",
        )
        self.assert_result(
            check_schnorr_correspondence(without_commitment, self.profile),
            Outcome.SEMANTIC_NEGATIVE,
            "source-correspondence:sigma-contract:closed-occurrence-set",
            "P01-CORR-002",
        )

        without_challenge = mutate_core(
            self.core,
            occurrences=tuple(
                contract
                for contract in self.core.occurrences
                if contract.occurrence != CHALLENGE
            ),
            verifier_check=replace(
                self.core.verifier_check,
                named_inputs=tuple(
                    binding
                    for binding in self.core.verifier_check.named_inputs
                    if binding[1] != CHALLENGE
                ),
            ),
        )
        derived = required_challenge_atoms(without_challenge)
        self.assert_result(
            derived,
            Outcome.MISSING_DEPENDENCY,
            "transcript-prefix:derivation",
            "P01-FS-DERIVE-001",
        )

    def test_reordered_conversation_is_generic_but_not_schnorr(self) -> None:
        by_name = {contract.occurrence: contract for contract in self.core.occurrences}
        candidate = mutate_core(
            self.core,
            occurrences=(
                by_name[STATEMENT],
                by_name[CHALLENGE],
                by_name[COMMITMENT],
                by_name[RESPONSE],
                by_name[CHECK],
                by_name[TERMINAL],
            ),
            verifier_check=replace(
                self.core.verifier_check,
                named_inputs=(
                    ("statement", STATEMENT),
                    ("challenge", CHALLENGE),
                    ("commitment", COMMITMENT),
                    ("response", RESPONSE),
                ),
            ),
        )
        self.assert_result(
            admit_core(candidate, self.profile),
            Outcome.AFFIRMATIVE,
            "core-admission",
            "P01-CORE-OK",
        )
        self.assert_result(
            check_schnorr_correspondence(candidate, self.profile),
            Outcome.SEMANTIC_NEGATIVE,
            "source-correspondence:sigma-three-move-order",
            "P01-CORR-001",
        )
        fresh_protocol, fresh = make_fresh_protocol(candidate, self.profile)
        self.assert_result(
            admit_protocol(
                fresh_protocol, candidate, self.profile, fresh=fresh
            ),
            Outcome.SEMANTIC_NEGATIVE,
            "source-correspondence:sigma-three-move-order",
            "P01-CORR-001",
        )

    def test_public_coin_eligibility_is_an_independent_structural_premise(self) -> None:
        candidate = _replace_occurrence(
            self.core,
            CHALLENGE,
            actor=OccurrenceActor.VERIFIER,
        )
        self.assert_result(
            admit_core(candidate, self.profile),
            Outcome.AFFIRMATIVE,
            "core-admission",
            "P01-CORE-OK",
        )
        self.assert_result(
            check_public_coin_eligibility(candidate, self.profile),
            Outcome.SEMANTIC_NEGATIVE,
            "source-correspondence:public-coin-eligibility",
            "P01-PCOIN-001",
        )
        protocol, fresh = make_fresh_protocol(candidate, self.profile)
        self.assert_result(
            admit_protocol(protocol, candidate, self.profile, fresh=fresh),
            Outcome.SEMANTIC_NEGATIVE,
            "source-correspondence:public-coin-eligibility",
            "P01-PCOIN-001",
        )

    def test_fresh_realization_requires_public_environment_authority(self) -> None:
        private_fresh = replace(
            self.fresh,
            resolver=OccurrenceActor.VERIFIER,
        )
        private_protocol = replace(
            self.fresh_protocol,
            realization_id=private_fresh.identity,
        )
        self.assert_result(
            admit_fresh_realization(private_fresh, self.core, self.profile),
            Outcome.SEMANTIC_NEGATIVE,
            "fresh-realization:public-coin-contract",
            "P01-FRESH-002",
        )
        self.assert_result(
            admit_protocol(
                private_protocol,
                self.core,
                self.profile,
                fresh=private_fresh,
            ),
            Outcome.SEMANTIC_NEGATIVE,
            "fresh-realization:public-coin-contract",
            "P01-FRESH-002",
        )

    def test_honest_prover_contract_is_explicit_and_protocol_bound(self) -> None:
        honest = canonical_honest_prover_contract(self.core, self.profile)
        admitted = admit_honest_prover_contract(
            honest, self.core, self.profile
        )
        self.assert_result(
            admitted,
            Outcome.AFFIRMATIVE,
            "honest-prover-contract",
            "P01-HONEST-OK",
        )
        self.assertEqual(
            self.fresh_protocol.honest_prover_contract_id,
            honest.identity,
        )
        self.assertEqual(
            self.fs_protocol.honest_prover_contract_id,
            honest.identity,
        )

        wrong_transition = replace(
            honest,
            response_rule=replace(
                honest.response_rule,
                named_inputs=(
                    ("retained_nonce", "local:nonce:r"),
                    ("witness", "local:witness:x"),
                    ("challenge", COMMITMENT),
                ),
            ),
        )
        self.assert_result(
            admit_honest_prover_contract(
                wrong_transition, self.core, self.profile
            ),
            Outcome.SEMANTIC_NEGATIVE,
            "honest-prover-contract:exact-transition-laws",
            "P01-HONEST-002",
        )

        wrong_protocol = replace(
            self.fs_protocol,
            honest_prover_contract_id=_closed_id("foreign-honest-contract"),
        )
        self.assert_result(
            admit_protocol(
                wrong_protocol,
                self.core,
                self.profile,
                construction=self.construction,
            ),
            Outcome.MISMATCH,
            "protocol-admission:honest-prover-contract",
            "P01-PROTO-009",
        )

    def test_fresh_kernel_is_conditioned_on_the_typed_public_prefix(self) -> None:
        self.assertEqual(
            self.fresh.conditional_kernel_contract_id,
            fresh_conditional_kernel_contract_id(self.core, self.profile),
        )
        changed_prefix_core = _replace_occurrence(
            self.core,
            COMMITMENT,
            semantic_purpose="AuxiliaryProtocolValue",
        )
        self.assertNotEqual(
            public_challenge_prefix_id(self.core),
            public_challenge_prefix_id(changed_prefix_core),
        )
        self.assertNotEqual(
            fresh_conditional_kernel_contract_id(self.core, self.profile),
            fresh_conditional_kernel_contract_id(
                changed_prefix_core, self.profile
            ),
        )

        wrong_kernel = replace(
            self.fresh,
            conditional_kernel_contract_id=_closed_id("unconditional-coin"),
        )
        self.assert_result(
            admit_fresh_realization(wrong_kernel, self.core, self.profile),
            Outcome.SEMANTIC_NEGATIVE,
            "fresh-realization:public-coin-contract",
            "P01-FRESH-002",
        )

    def test_fresh_and_fs_share_core_but_not_protocol_identity(self) -> None:
        self.assertEqual(self.fresh_protocol.core_id, self.fs_protocol.core_id)
        self.assertEqual(self.fresh_protocol.core_id, self.core.identity)
        self.assertNotEqual(self.fresh_protocol.identity, self.fs_protocol.identity)
        checked = checked_fs_factorization(
            self.fresh_protocol,
            self.fs_protocol,
            self.construction,
            self.core,
            self.profile,
            self.fresh,
        )
        self.assert_result(
            checked,
            Outcome.AFFIRMATIVE,
            "relations:fresh-fs-factorization",
            "P01-FACT-OK",
        )

    def test_fresh_and_fs_reject_mixed_realization_authorities(self) -> None:
        cases = (
            (
                admit_protocol(
                    self.fresh_protocol,
                    self.core,
                    self.profile,
                    fresh=self.fresh,
                    construction=self.construction,
                ),
                "P01-PROTO-002",
            ),
            (
                admit_protocol(
                    self.fs_protocol,
                    self.core,
                    self.profile,
                    fresh=self.fresh,
                    construction=self.construction,
                ),
                "P01-PROTO-005",
            ),
        )
        for checked, code in cases:
            with self.subTest(code=code):
                self.assert_result(
                    checked,
                    Outcome.SEMANTIC_NEGATIVE,
                    "challenge-interpretation:construction-closure",
                    code,
                )

    def test_strong_fs_sources_are_derived_from_statement_and_prior_messages(self) -> None:
        expected = (
            TranscriptAtom(
                "InitialStatement",
                STATEMENT,
                group_domain_id(self.profile),
                self.profile.group_codec,
            ),
            TranscriptAtom(
                "PriorProofMessage",
                COMMITMENT,
                group_domain_id(self.profile),
                self.profile.group_codec,
            ),
        )
        self.assertEqual(required_challenge_atoms(self.core), expected)
        self.assertEqual(self.construction.atoms, expected)

    def test_statement_and_prior_commitment_cannot_be_omitted(self) -> None:
        cases = (
            ((self.construction.atoms[0],), COMMITMENT),
            ((self.construction.atoms[1],), STATEMENT),
        )
        for atoms, expected_source in cases:
            with self.subTest(expected_source=expected_source):
                candidate = mutate_construction(self.construction, atoms=atoms)
                checked = admit_transcript_construction(
                    candidate, self.core, self.profile
                )
                self.assert_result(
                    checked,
                    Outcome.SEMANTIC_NEGATIVE,
                    f"transcript-prefix:{CHALLENGE}",
                    "P01-FS-005",
                )
                self.assertEqual(
                    checked.evidence["expected_source"], expected_source
                )

    def test_transcript_atom_substitution_codec_domain_order_and_duplication(self) -> None:
        statement_atom, commitment_atom = self.construction.atoms
        cases = (
            (
                (replace(statement_atom, occurrence=RESPONSE), commitment_atom),
                "transcript-atom:typed-occurrence-source",
                "P01-FS-006",
            ),
            (
                (replace(statement_atom, codec=self.profile.scalar_codec), commitment_atom),
                "transcript-atom:typed-occurrence-source",
                "P01-FS-007",
            ),
            (
                (
                    replace(
                        statement_atom,
                        value_domain_id=scalar_domain_id(self.profile),
                    ),
                    commitment_atom,
                ),
                "transcript-atom:typed-occurrence-source",
                "P01-FS-007",
            ),
            (
                (commitment_atom, statement_atom),
                "transcript-prefix:ordered-exactness:c",
                "P01-FS-006",
            ),
            (
                (statement_atom, commitment_atom, commitment_atom),
                f"transcript-prefix:{CHALLENGE}",
                "P01-FS-008",
            ),
        )
        for atoms, boundary, code in cases:
            with self.subTest(code=code, boundary=boundary):
                candidate = mutate_construction(self.construction, atoms=atoms)
                self.assert_result(
                    admit_transcript_construction(
                        candidate, self.core, self.profile
                    ),
                    Outcome.SEMANTIC_NEGATIVE,
                    boundary,
                    code,
                )

    def test_transcript_initialization_context_namespace_and_framing_are_exact(self) -> None:
        context = canonical_runtime_context_contract()
        cases = (
            (
                {"model": "StrongFiatShamirTranscriptConstruction.v1"},
                Outcome.UNSUPPORTED,
                "transcript-construction:model",
                "P01-FS-004",
            ),
            (
                {"suite_domain": "zkc/p01/wrong-suite/v1"},
                Outcome.SEMANTIC_NEGATIVE,
                "transcript-initialization:suite-domain",
                "P01-FS-019",
            ),
            (
                {"runtime_context": replace(context, source=STATEMENT)},
                Outcome.SEMANTIC_NEGATIVE,
                "transcript-initialization:application-context",
                "P01-FS-017",
            ),
            (
                {
                    "runtime_context": replace(
                        context, semantic_purpose="Statement"
                    )
                },
                Outcome.SEMANTIC_NEGATIVE,
                "transcript-initialization:application-context",
                "P01-FS-017",
            ),
            (
                {
                    "runtime_context": replace(
                        context,
                        value_domain_id=group_domain_id(self.profile),
                    )
                },
                Outcome.SEMANTIC_NEGATIVE,
                "transcript-initialization:application-context",
                "P01-FS-017",
            ),
            (
                {
                    "runtime_context": replace(
                        context, codec=self.profile.group_codec
                    )
                },
                Outcome.SEMANTIC_NEGATIVE,
                "transcript-initialization:application-context",
                "P01-FS-017",
            ),
            (
                {"challenge_namespace": COMMITMENT},
                Outcome.SEMANTIC_NEGATIVE,
                "squeeze-sample:namespace",
                "P01-FS-011",
            ),
            (
                {"framing": "ambiguous-concatenation.v1"},
                Outcome.SEMANTIC_NEGATIVE,
                "transcript-framing:injectivity",
                "P01-FS-012",
            ),
            (
                {"sampler": "unknown-sampler.v1"},
                Outcome.UNSUPPORTED,
                "squeeze-sample:algorithm",
                "P01-FS-013",
            ),
        )
        for changes, outcome, boundary, code in cases:
            with self.subTest(code=code):
                candidate = mutate_construction(self.construction, **changes)
                self.assert_result(
                    admit_transcript_construction(
                        candidate, self.core, self.profile
                    ),
                    outcome,
                    boundary,
                    code,
                )

    def test_wrong_challenge_domain_first_fails_public_coin_eligibility(self) -> None:
        candidate_core = _replace_occurrence(
            self.core,
            CHALLENGE,
            value_domain_id=scalar_domain_id(self.profile),
        )
        self.assert_result(
            admit_core(candidate_core, self.profile),
            Outcome.AFFIRMATIVE,
            "core-admission",
            "P01-CORE-OK",
        )
        self.assert_result(
            check_public_coin_eligibility(candidate_core, self.profile),
            Outcome.SEMANTIC_NEGATIVE,
            "source-correspondence:public-coin-eligibility",
            "P01-PCOIN-001",
        )

    def test_runtime_context_changes_query_but_not_semantic_identities(self) -> None:
        rebuilt = canonical_transcript_construction(self.core, self.profile)
        rebuilt_protocol = make_fs_protocol(self.core, rebuilt, self.profile)
        self.assertEqual(rebuilt.identity, self.construction.identity)
        self.assertEqual(rebuilt_protocol.identity, self.fs_protocol.identity)

        _, query_a, receipts_a = derive_fs_challenge(
            self.construction,
            self.profile,
            "zkc.test.p01/application-a",
            13,
            16,
        )
        _, query_b, receipts_b = derive_fs_challenge(
            self.construction,
            self.profile,
            "zkc.test.p01/application-b",
            13,
            16,
        )
        self.assertNotEqual(query_a, query_b)
        self.assertEqual(
            tuple(receipt["occurrence"] for receipt in receipts_a),
            (STATEMENT, COMMITMENT),
        )
        self.assertEqual(receipts_a, receipts_b)
        self.assertNotIn("application-a", repr(self.construction.term()))
        self.assertNotIn("application-b", repr(self.fs_protocol.term()))

    def test_runtime_context_admission_has_malformed_and_semantic_boundaries(self) -> None:
        self.assert_result(
            admit_application_context(b"bytes"),
            Outcome.MALFORMED,
            "runtime-application-context",
            "P01-CTX-001",
        )
        for value in ("", "x" * 257):
            with self.subTest(length=len(value)):
                self.assert_result(
                    admit_application_context(value),
                    Outcome.SEMANTIC_NEGATIVE,
                    "runtime-application-context",
                    "P01-CTX-002",
                )
        with self.assertRaises(ValueError):
            derive_fs_challenge(
                self.construction,
                self.profile,
                "",
                13,
                16,
            )

    def test_sampler_width_is_derived_from_challenge_bits(self) -> None:
        profile = replace(self.profile, challenge_size=4)
        core = canonical_core(profile)
        construction = canonical_transcript_construction(core, profile)
        challenge, query, _ = derive_fs_challenge(
            construction,
            profile,
            "zkc.test.p01/sampler-width",
            pow(profile.generator, 7, profile.p),
            pow(profile.generator, 4, profile.p),
        )
        expected = hashlib.shake_128(query).digest(1)[0] & 0b11
        self.assertEqual(challenge, expected)
        self.assertTrue(profile.valid_challenge(challenge))


class P01RelationAndFiniteAnalysisTest(ResultAssertions):
    """Relation, grounding-shape, finite algebra, and theorem refusal stay split."""

    def setUp(self) -> None:
        self.profile = AlgebraProfile(p=23, q=11, generator=2, challenge_size=8)
        self.relation = canonical_schnorr_relation(self.profile)
        self.instance = SchnorrRelationInstance(
            self.relation.identity,
            public_statement=13,
        )
        self.witness = SchnorrWitnessAssignment(
            self.instance.identity,
            "witness:x",
            secret_scalar=7,
        )

    def _statement_adapter(
        self,
        value: int = 13,
        *,
        occurrence: str = STATEMENT,
        suffix: str = "canonical",
    ) -> QualifiedExecutionStatement:
        return QualifiedExecutionStatement(
            qualification_id=_closed_id(f"qualification:{suffix}"),
            execution_id=_closed_id(f"execution:{suffix}"),
            protocol_id=_closed_id(f"protocol:{suffix}"),
            core_id=_closed_id(f"core:{suffix}"),
            evaluation_profile_id=self.profile.identity,
            occurrence=occurrence,
            value=value,
            source_event_id=_closed_id(f"event:{suffix}"),
        )

    def test_relation_instance_witness_and_satisfaction_are_separate(self) -> None:
        checks = (
            (
                admit_relation(self.relation, self.profile),
                "relations:relation-admission",
                "P01-REL-OK",
            ),
            (
                admit_instance(self.instance, self.relation, self.profile),
                "relations:instance-admission",
                "P01-INS-OK",
            ),
            (
                admit_witness_assignment(
                    self.witness, self.instance, self.relation, self.profile
                ),
                "relations:witness-admission",
                "P01-WIT-OK",
            ),
            (
                check_relation_satisfaction(
                    self.witness, self.instance, self.relation, self.profile
                ),
                "relations:satisfaction",
                "P01-SAT-OK",
            ),
        )
        for checked, boundary, code in checks:
            with self.subTest(code=code):
                self.assert_result(checked, Outcome.AFFIRMATIVE, boundary, code)

    def test_relation_raw_types_group_scalar_and_equation_fail_separately(self) -> None:
        self.assert_result(
            admit_relation("raw", self.profile),
            Outcome.MALFORMED,
            "relations:relation-admission",
            "P01-REL-001",
        )
        self.assert_result(
            admit_instance("raw", self.relation, self.profile),
            Outcome.MALFORMED,
            "relations:instance-admission",
            "P01-INS-001",
        )

        invalid_statement = replace(self.instance, public_statement=0)
        self.assert_result(
            admit_instance(invalid_statement, self.relation, self.profile),
            Outcome.SEMANTIC_NEGATIVE,
            "relations:instance-admission:statement-domain",
            "P01-INS-003",
        )
        invalid_scalar = replace(self.witness, secret_scalar=self.profile.q)
        self.assert_result(
            admit_witness_assignment(
                invalid_scalar, self.instance, self.relation, self.profile
            ),
            Outcome.SEMANTIC_NEGATIVE,
            "relations:witness-admission:scalar-domain",
            "P01-WIT-004",
        )
        wrong_witness = replace(self.witness, secret_scalar=6)
        self.assert_result(
            check_relation_satisfaction(
                wrong_witness, self.instance, self.relation, self.profile
            ),
            Outcome.SEMANTIC_NEGATIVE,
            "relations:satisfaction",
            "P01-SAT-001",
        )

    def test_grounding_shape_requires_exact_operands_and_statement_equality(self) -> None:
        statement = self._statement_adapter()
        grounding = grounding_candidate(self.instance, self.relation, statement)
        affirmative = check_grounding_shape(
            grounding,
            self.instance,
            self.relation,
            statement,
            self.profile,
        )
        self.assert_result(
            affirmative,
            Outcome.AFFIRMATIVE,
            "relations:execution-grounding-shape",
            "P01-GRD-SHAPE-OK",
        )
        self.assertIn("does not authenticate", affirmative.evidence["non_claim"])

        wrong_operands = replace(
            grounding,
            qualification_id=_closed_id("qualification:other"),
        )
        self.assert_result(
            check_grounding_shape(
                wrong_operands,
                self.instance,
                self.relation,
                statement,
                self.profile,
            ),
            Outcome.MISMATCH,
            "relations:execution-grounding-shape:exact-operands",
            "P01-GRD-007",
        )

        wrong_value_statement = self._statement_adapter(
            value=3,
            suffix="wrong-value",
        )
        wrong_value_grounding = grounding_candidate(
            self.instance, self.relation, wrong_value_statement
        )
        self.assert_result(
            check_grounding_shape(
                wrong_value_grounding,
                self.instance,
                self.relation,
                wrong_value_statement,
                self.profile,
            ),
            Outcome.MISMATCH,
            "relations:execution-grounding-shape:value",
            "P01-GRD-008",
        )

    def test_grounding_adapter_shape_refuses_bad_identity_and_occurrence(self) -> None:
        malformed = replace(
            self._statement_adapter(),
            qualification_id="caller-label",
        )
        malformed_grounding = grounding_candidate(
            self.instance, self.relation, malformed
        )
        self.assert_result(
            check_grounding_shape(
                malformed_grounding,
                self.instance,
                self.relation,
                malformed,
                self.profile,
            ),
            Outcome.MALFORMED,
            "relations:execution-grounding-shape:qualification",
            "P01-GRD-002",
        )

        wrong_occurrence = self._statement_adapter(
            occurrence=COMMITMENT,
            suffix="wrong-occurrence",
        )
        wrong_occurrence_grounding = grounding_candidate(
            self.instance, self.relation, wrong_occurrence
        )
        self.assert_result(
            check_grounding_shape(
                wrong_occurrence_grounding,
                self.instance,
                self.relation,
                wrong_occurrence,
                self.profile,
            ),
            Outcome.MISMATCH,
            "relations:execution-grounding-shape:occurrence",
            "P01-GRD-004",
        )

    def test_valid_and_invalid_transcripts_reach_verifier_equation(self) -> None:
        accepted = honest_transcript(
            self.instance,
            witness_scalar=7,
            nonce=4,
            challenge=3,
            profile=self.profile,
        )
        self.assert_result(
            check_accepting_transcript(
                accepted, self.instance, self.relation, self.profile
            ),
            Outcome.AFFIRMATIVE,
            "analysis:finite-transcript",
            "P01-TRN-OK",
        )

        rejected = replace(
            accepted,
            response=(accepted.response + 1) % self.profile.q,
        )
        self.assert_result(
            check_accepting_transcript(
                rejected, self.instance, self.relation, self.profile
            ),
            Outcome.SEMANTIC_NEGATIVE,
            "analysis:finite-transcript:verifier-equation",
            "P01-TRN-008",
        )

    def test_finite_special_soundness_requires_one_prefix_and_distinct_challenges(self) -> None:
        left = honest_transcript(self.instance, 7, 4, 3, self.profile)
        right = honest_transcript(self.instance, 7, 4, 4, self.profile)
        affirmative = check_special_soundness_fork(
            TranscriptFork(left, right),
            self.instance,
            self.relation,
            self.profile,
        )
        self.assert_result(
            affirmative,
            Outcome.AFFIRMATIVE,
            "analysis:finite-special-soundness",
            "P01-SS-OK",
        )
        self.assertEqual(affirmative.evidence["extracted_scalar"], 7)

        equal_challenge = check_special_soundness_fork(
            TranscriptFork(left, left),
            self.instance,
            self.relation,
            self.profile,
        )
        self.assert_result(
            equal_challenge,
            Outcome.SEMANTIC_NEGATIVE,
            "analysis:finite-special-soundness:distinct-challenges",
            "P01-SS-006",
        )

        different_commitment = honest_transcript(
            self.instance, 7, 5, 4, self.profile
        )
        self.assert_result(
            check_special_soundness_fork(
                TranscriptFork(left, different_commitment),
                self.instance,
                self.relation,
                self.profile,
            ),
            Outcome.MISMATCH,
            "analysis:finite-special-soundness:common-first-message",
            "P01-SS-005",
        )

    def test_exhaustive_special_soundness_and_shvzk_are_reproducible(self) -> None:
        special_soundness = exhaustive_special_soundness(self.profile)
        self.assert_result(
            special_soundness,
            Outcome.AFFIRMATIVE,
            "analysis:finite-special-soundness:exhaustive",
            "P01-SS-ENUM-OK",
        )
        self.assertEqual(
            special_soundness.evidence["unordered_distinct_challenge_forks"],
            3388,
        )

        shvzk = exhaustive_shvzk_distribution_equality(self.profile)
        self.assert_result(
            shvzk,
            Outcome.AFFIRMATIVE,
            "analysis:finite-shvzk:exhaustive",
            "P01-SHVZK-OK",
        )
        self.assertEqual(shvzk.evidence["compared_conditional_distributions"], 88)
        self.assertIn("not malicious-verifier ZK", shvzk.evidence["non_claim"])

    def test_finite_facts_cannot_author_general_theorem_capabilities(self) -> None:
        refusals = {
            ApplicabilityClaim.GENERAL_SPECIAL_SOUNDNESS: "P01-APP-101",
            ApplicabilityClaim.GENERAL_SHVZK: "P01-APP-102",
            ApplicabilityClaim.GENERAL_HVZK: "P01-APP-103",
            ApplicabilityClaim.KNOWLEDGE_SOUNDNESS: "P01-APP-104",
            ApplicabilityClaim.FIAT_SHAMIR_ROM: "P01-APP-105",
            ApplicabilityClaim.FIAT_SHAMIR_QROM: "P01-APP-106",
        }
        for claim, code in refusals.items():
            with self.subTest(claim=claim.value):
                checked = probe_analysis_applicability(claim, self.profile)
                self.assert_result(
                    checked,
                    Outcome.REFUSED,
                    f"analysis:applicability:{claim.value}",
                    code,
                )
                self.assertEqual(
                    checked.evidence["non_promotion_law"],
                    "finite evidence cannot author theorem applicability",
                )


if __name__ == "__main__":
    unittest.main()
