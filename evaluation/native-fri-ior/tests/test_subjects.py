"""Tests for the typed semantic factorization and construction subjects."""

from __future__ import annotations

from dataclasses import replace
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import friiormodel.subjects as subjects_model  # noqa: E402
from friiormodel.commitment import EXACT_COMMITMENT_PROFILE  # noqa: E402
from friiormodel.profile import EXACT_ALGEBRA_PROFILE  # noqa: E402
from friiormodel.provenance import (  # noqa: E402
    ArtifactContentId,
    CanonicalContentId,
    ValidationBasisId,
)
from friiormodel.subjects import (  # noqa: E402
    CANONICAL_PUBLIC_OCCURRENCE_PROTECTION_MAP,
    CHECKED_FIAT_SHAMIR_CONSTRUCTION,
    COMMITTED_CORE_NONCLAIMS,
    COMMITTED_FRI_CORE,
    COMMITMENT_COMPILATION_CAPABILITIES,
    COMMITMENT_COMPILATION_DECLARATION,
    COMMITMENT_COMPILATION_NONCLAIMS,
    COMMITMENT_COMPILATION_REQUIREMENTS,
    DECLARATION_STATUS,
    FIAT_SHAMIR_CHALLENGE_INTERPRETATION,
    FIAT_SHAMIR_CONSTRUCTION_CAPABILITIES,
    FIAT_SHAMIR_CONSTRUCTION_DECLARATION,
    FIAT_SHAMIR_CONSTRUCTION_NONCLAIMS,
    FIAT_SHAMIR_CONSTRUCTION_REQUIREMENTS,
    FIAT_SHAMIR_INTERPRETATION_NONCLAIMS,
    FIAT_SHAMIR_WORK_AUGMENTED_PROTOCOL,
    FRESH_CHALLENGE_INTERPRETATION,
    FRESH_INTERPRETATION_NONCLAIMS,
    FRESH_WORK_AUGMENTED_PROTOCOL,
    GRINDING_AUGMENTATION_CAPABILITIES,
    GRINDING_AUGMENTATION_DECLARATION,
    GRINDING_AUGMENTATION_NONCLAIMS,
    GRINDING_AUGMENTATION_REQUIREMENTS,
    NATIVE_CORE_NONCLAIMS,
    NATIVE_FRI_CORE,
    POST_FINAL_CHALLENGE_PUBLIC_RESPONSE,
    PROTOCOL_NONCLAIMS,
    WORK_AUGMENTED_COMMITTED_FRI_CORE,
    WORK_AUGMENTED_CORE_NONCLAIMS,
    CheckedCommitmentCompilationDeclaration,
    CheckedFiatShamirConstruction,
    CheckedFiatShamirConstructionDeclaration,
    CheckedGrindingAugmentationDeclaration,
    FiatShamirChallengeInterpretation,
    FiatShamirWorkAugmentedProtocol,
    FreshChallengeInterpretation,
    FreshWorkAugmentedProtocol,
    WorkAugmentedCommittedFriCore,
    admit_fiat_shamir_construction,
    admit_selected_subject,
    transcript_plan_identity,
)
from friiormodel.terms import (  # noqa: E402
    ModelFailure,
    OutcomeClass,
    SemanticId,
    semantic_id,
)
from friiormodel.transcript import (  # noqa: E402
    CANONICAL_CONSTRUCTION_PLAN,
    EXACT_GRINDING_PROFILE,
    admit_construction_plan,
)


def _identity_from_term(subject: object) -> SemanticId:
    return semantic_id(
        subject.SUBJECT_KIND,
        subject.IDENTITY_DOMAIN,
        subject.to_term(),
    )


def _all_keys(value: object) -> set[str]:
    keys: set[str] = set()
    if isinstance(value, dict):
        keys.update(value)
        for item in value.values():
            keys.update(_all_keys(item))
    elif isinstance(value, (list, tuple)):
        for item in value:
            keys.update(_all_keys(item))
    return keys


class CoreFactorizationTest(unittest.TestCase):
    def test_three_core_subjects_have_distinct_canonical_identities(self) -> None:
        subjects = (
            NATIVE_FRI_CORE,
            COMMITTED_FRI_CORE,
            WORK_AUGMENTED_COMMITTED_FRI_CORE,
        )
        identities = tuple(subject.identity for subject in subjects)
        self.assertEqual(len(set(identities)), 3)
        for subject in subjects:
            with self.subTest(subject=type(subject).__name__):
                self.assertIsInstance(subject.identity, SemanticId)
                self.assertEqual(subject.identity, _identity_from_term(subject))

    def test_core_identities_bind_only_their_semantic_dependencies(self) -> None:
        native_term = NATIVE_FRI_CORE.to_term()
        committed_term = COMMITTED_FRI_CORE.to_term()
        work_term = WORK_AUGMENTED_COMMITTED_FRI_CORE.to_term()

        self.assertEqual(
            native_term["algebra_profile_id"],
            EXACT_ALGEBRA_PROFILE.identity.to_term(),
        )
        self.assertNotIn("commitment_profile_id", native_term)
        self.assertNotIn("grinding_profile_id", native_term)

        self.assertEqual(
            committed_term["algebra_profile_id"],
            EXACT_ALGEBRA_PROFILE.identity.to_term(),
        )
        self.assertEqual(
            committed_term["commitment_profile_id"],
            EXACT_COMMITMENT_PROFILE.identity.to_term(),
        )
        self.assertNotIn("grinding_profile_id", committed_term)

        self.assertEqual(
            work_term["grinding_profile_id"],
            EXACT_GRINDING_PROFILE.identity.to_term(),
        )
        self.assertEqual(
            work_term["preserved_committed_core_id"],
            COMMITTED_FRI_CORE.identity.to_term(),
        )

    def test_statement_and_application_binding_are_typed_context_ports(self) -> None:
        expected = [
            {
                "occurrence": "statement",
                "port_kind": "Context",
                "owner": "PublicEnvironment",
                "visibility": "Public",
                "multiplicity": "ExactlyOne",
                "semantic_purpose": "Statement",
                "value_type": "ClosedFiniteTerm",
            },
            {
                "occurrence": "application-context",
                "port_kind": "Context",
                "owner": "PublicEnvironment",
                "visibility": "Public",
                "multiplicity": "ExactlyOne",
                "semantic_purpose": "ApplicationBinding",
                "value_type": "ClosedFiniteTerm",
            },
        ]
        self.assertEqual(NATIVE_FRI_CORE.to_term()["public_context_ports"], expected)
        self.assertEqual(COMMITTED_FRI_CORE.to_term()["public_context_ports"], expected)
        self.assertEqual(
            WORK_AUGMENTED_COMMITTED_FRI_CORE.to_term()["public_context_ports"],
            expected,
        )

    def test_target_only_profile_changes_do_not_rotate_native_core(self) -> None:
        native_id = NATIVE_FRI_CORE.identity
        alternate_commitment_id = semantic_id(
            "fri-commitment-profile",
            "fri-ior.commitment-profile.v1",
            {"variant": "alternate-commitment-semantics"},
        )
        alternate_committed = replace(
            COMMITTED_FRI_CORE,
            commitment_profile_id=alternate_commitment_id,
        )
        alternate_work = replace(
            WORK_AUGMENTED_COMMITTED_FRI_CORE,
            committed_core=alternate_committed,
        )
        self.assertEqual(NATIVE_FRI_CORE.identity, native_id)
        self.assertNotEqual(alternate_committed.identity, COMMITTED_FRI_CORE.identity)
        self.assertNotEqual(
            alternate_work.identity,
            WORK_AUGMENTED_COMMITTED_FRI_CORE.identity,
        )

        alternate_grinding_id = semantic_id(
            "fri-grinding-profile",
            "fri-ior.grinding-profile.v1",
            {"variant": "alternate-work-predicate"},
        )
        grinding_changed = replace(
            WORK_AUGMENTED_COMMITTED_FRI_CORE,
            grinding_profile_id=alternate_grinding_id,
        )
        self.assertEqual(grinding_changed.committed_core.identity, COMMITTED_FRI_CORE.identity)
        self.assertNotEqual(
            grinding_changed.identity,
            WORK_AUGMENTED_COMMITTED_FRI_CORE.identity,
        )
        self.assertEqual(NATIVE_FRI_CORE.identity, native_id)

    def test_native_core_has_logical_access_without_commitment_or_work(self) -> None:
        term = NATIVE_FRI_CORE.to_term()
        self.assertEqual(term["oracle_publication"]["mode"], "LogicalAccess")
        self.assertEqual(
            term["query_model"]["physical_openings"],
            "absent",
        )
        self.assertIn("declared-dependency-order", term["checks"])
        self.assertNotIn("strategy-non-anticipation", term["checks"])
        self.assertIn(
            "adversary-strategy-non-anticipation",
            term["nonclaims"],
        )
        schedule = term["event_schedule"]
        for forbidden in ("cap", "opening", "authentication", "work", "nonce"):
            self.assertFalse(
                any(forbidden in event for event in schedule),
                forbidden,
            )
        self.assertEqual(tuple(term["nonclaims"]), NATIVE_CORE_NONCLAIMS)

    def test_committed_core_has_authentication_but_no_work(self) -> None:
        term = COMMITTED_FRI_CORE.to_term()
        self.assertEqual(term["publication_model"]["oracle_publication"], "absent")
        self.assertEqual(
            term["publication_model"]["private_logical_oracle_capability"],
            "absent",
        )
        self.assertIn("cap-authentication", term["checks"])
        self.assertTrue(any("opening" in event for event in term["event_schedule"]))
        self.assertFalse(any("work" in event for event in term["event_schedule"]))
        self.assertFalse(any("nonce" in event for event in term["event_schedule"]))
        self.assertEqual(tuple(term["nonclaims"]), COMMITTED_CORE_NONCLAIMS)

    def test_work_augmented_core_preserves_committed_checks_and_inserts_gate(self) -> None:
        committed = COMMITTED_FRI_CORE.to_term()
        augmented = WORK_AUGMENTED_COMMITTED_FRI_CORE.to_term()
        self.assertEqual(
            augmented["preserved_committed_core_id"],
            COMMITTED_FRI_CORE.identity.to_term(),
        )
        self.assertEqual(augmented["preserved_checks"], committed["checks"])
        schedule = augmented["event_schedule"]
        terminal = schedule.index("publish-terminal-polynomial")
        work_seed = schedule.index("fresh-work-seed")
        nonce = schedule.index("publish-grinding-nonce")
        work_check = schedule.index("check-work-seed-and-nonce")
        query_vector = schedule.index(
            "sample-fresh-ordered-query-occurrence-vector"
        )
        self.assertLess(terminal, work_seed)
        self.assertLess(work_seed, nonce)
        self.assertLess(nonce, work_check)
        self.assertLess(work_check, query_vector)
        self.assertIs(augmented["challenge_contract"]["public_coin"], True)
        self.assertEqual(
            tuple(augmented["challenge_contract"]["occurrences"]),
            (
                "fold-challenge[0]",
                "fold-challenge[1]",
                "work-seed",
                "query-occurrences",
            ),
        )
        self.assertEqual(
            augmented["challenge_contract"]["occurrence_types"][-1],
            {
                "occurrence": "query-occurrences",
                "value_type": (
                    "OrderedQueryOccurrenceVector<length=4,index-domain=D0,with-replacement>"
                ),
            },
        )
        self.assertEqual(
            len(augmented["challenge_contract"]["occurrences"]),
            len(set(augmented["challenge_contract"]["occurrences"])),
        )
        self.assertEqual(
            tuple(augmented["nonclaims"]),
            WORK_AUGMENTED_CORE_NONCLAIMS,
        )

    def test_acceptance_affecting_public_occurrence_inventory_is_exact(self) -> None:
        occurrences = WORK_AUGMENTED_COMMITTED_FRI_CORE.to_term()[
            "acceptance_affecting_public_occurrences"
        ]
        self.assertEqual(
            tuple(occurrences),
            (
                "statement",
                "application-context",
                "cap[0]",
                "fold-challenge[0]",
                "cap[1]",
                "fold-challenge[1]",
                "terminal-polynomial",
                "work-seed",
                "grinding-nonce",
                "query-occurrences",
                "opening-table-and-occurrence-selectors",
            ),
        )
        self.assertEqual(len(occurrences), len(set(occurrences)))


class ProtocolFactorizationTest(unittest.TestCase):
    def test_fresh_and_fiat_shamir_share_exactly_the_augmented_core(self) -> None:
        fresh = FRESH_WORK_AUGMENTED_PROTOCOL
        fiat_shamir = FIAT_SHAMIR_WORK_AUGMENTED_PROTOCOL
        self.assertEqual(fresh.core.identity, fiat_shamir.core.identity)
        self.assertEqual(
            fresh.core.identity,
            WORK_AUGMENTED_COMMITTED_FRI_CORE.identity,
        )
        self.assertEqual(
            fresh.to_term()["core_id"],
            fiat_shamir.to_term()["core_id"],
        )
        self.assertNotEqual(
            fresh.challenge_interpretation.identity,
            fiat_shamir.challenge_interpretation.identity,
        )
        self.assertNotEqual(fresh.identity, fiat_shamir.identity)
        fresh_term = fresh.to_term()
        fiat_shamir_term = fiat_shamir.to_term()
        fresh_term.pop("challenge_interpretation_id")
        fiat_shamir_term.pop("challenge_interpretation_id")
        self.assertEqual(fresh_term, fiat_shamir_term)

    def test_challenge_interpretations_have_one_kind_but_distinct_terms(self) -> None:
        fresh = FRESH_CHALLENGE_INTERPRETATION
        fiat_shamir = FIAT_SHAMIR_CHALLENGE_INTERPRETATION
        self.assertEqual(fresh.identity.subject_kind, "challenge-interpretation")
        self.assertEqual(fiat_shamir.identity.subject_kind, "challenge-interpretation")
        self.assertEqual(fresh.identity.domain, fiat_shamir.identity.domain)
        self.assertEqual(fresh.to_term()["kind"], "Fresh")
        self.assertEqual(fiat_shamir.to_term()["kind"], "FiatShamir")
        self.assertNotIn("transcript_construction", fresh.to_term())
        self.assertIn("transcript_construction", fiat_shamir.to_term())
        fresh_query = fresh.to_term()["resolution"][-1]
        self.assertEqual(fresh_query["occurrence"], "query-occurrences")
        self.assertEqual(
            fresh_query["source"],
            "verifier-fresh-direct-uniform-sampling",
        )
        fs_query = fiat_shamir.to_term()["core_query_resolution"]
        self.assertEqual(fs_query["core_occurrence"], "query-occurrences")
        self.assertEqual(fs_query["construction_internal_state"], "query-seed")
        self.assertNotIn(
            "query-seed",
            fresh.to_term()["challenge_occurrences"],
        )
        self.assertEqual(
            tuple(fresh.to_term()["nonclaims"]),
            FRESH_INTERPRETATION_NONCLAIMS,
        )
        self.assertEqual(
            tuple(fiat_shamir.to_term()["nonclaims"]),
            FIAT_SHAMIR_INTERPRETATION_NONCLAIMS,
        )

    def test_interpretations_cannot_diverge_from_core_challenge_inventory(
        self,
    ) -> None:
        narrowed = WorkAugmentedCommittedFriCore(
            COMMITTED_FRI_CORE,
            challenge_occurrences=("fold-challenge[0]",),
        )
        for constructor in (
            lambda: FreshChallengeInterpretation(narrowed),
            lambda: FiatShamirChallengeInterpretation(
                narrowed,
                CANONICAL_CONSTRUCTION_PLAN,
            ),
        ):
            with self.subTest(constructor=constructor):
                with self.assertRaises(ModelFailure) as raised:
                    constructor()
                self.assertIs(
                    raised.exception.outcome,
                    OutcomeClass.KIND_MISMATCH,
                )
                self.assertEqual(
                    raised.exception.code,
                    "FRI-IOR-SUBJECT-033",
                )

    def test_transcript_plan_has_a_separate_semantic_identity(self) -> None:
        result = admit_construction_plan(CANONICAL_CONSTRUCTION_PLAN)
        self.assertIs(result.outcome, OutcomeClass.AFFIRMATIVE)
        plan_id = transcript_plan_identity(CANONICAL_CONSTRUCTION_PLAN)
        self.assertIsInstance(plan_id, SemanticId)
        self.assertEqual(plan_id, CANONICAL_CONSTRUCTION_PLAN.identity)
        self.assertEqual(plan_id.subject_kind, "transcript-construction-plan")
        self.assertEqual(
            FIAT_SHAMIR_CHALLENGE_INTERPRETATION.to_term()[
                "transcript_construction_plan_id"
            ],
            plan_id.to_term(),
        )
        self.assertEqual(
            FIAT_SHAMIR_CHALLENGE_INTERPRETATION.to_term()[
                "transcript_construction"
            ],
            CANONICAL_CONSTRUCTION_PLAN.to_term(),
        )
        self.assertNotEqual(plan_id, FIAT_SHAMIR_CHALLENGE_INTERPRETATION.identity)

    def test_protocol_nonclaims_are_exact(self) -> None:
        for protocol in (
            FRESH_WORK_AUGMENTED_PROTOCOL,
            FIAT_SHAMIR_WORK_AUGMENTED_PROTOCOL,
        ):
            self.assertEqual(tuple(protocol.to_term()["nonclaims"]), PROTOCOL_NONCLAIMS)


class ConstructionDeclarationTest(unittest.TestCase):
    def test_commitment_compilation_has_typed_direction_and_exact_obligations(self) -> None:
        declaration = COMMITMENT_COMPILATION_DECLARATION
        term = declaration.to_term()
        self.assertEqual(term["source_core_id"], NATIVE_FRI_CORE.identity.to_term())
        self.assertEqual(term["target_core_id"], COMMITTED_FRI_CORE.identity.to_term())
        self.assertEqual(
            tuple(term["required_capabilities"]),
            COMMITMENT_COMPILATION_CAPABILITIES,
        )
        self.assertEqual(
            tuple(term["admission_requirements"]),
            COMMITMENT_COMPILATION_REQUIREMENTS,
        )
        self.assertEqual(tuple(term["nonclaims"]), COMMITMENT_COMPILATION_NONCLAIMS)

    def test_grinding_augmentation_has_typed_direction_and_exact_obligations(self) -> None:
        declaration = GRINDING_AUGMENTATION_DECLARATION
        term = declaration.to_term()
        self.assertEqual(term["source_core_id"], COMMITTED_FRI_CORE.identity.to_term())
        self.assertEqual(
            term["target_core_id"],
            WORK_AUGMENTED_COMMITTED_FRI_CORE.identity.to_term(),
        )
        self.assertEqual(
            tuple(term["required_capabilities"]),
            GRINDING_AUGMENTATION_CAPABILITIES,
        )
        self.assertEqual(
            tuple(term["admission_requirements"]),
            GRINDING_AUGMENTATION_REQUIREMENTS,
        )
        self.assertEqual(tuple(term["nonclaims"]), GRINDING_AUGMENTATION_NONCLAIMS)

    def test_fiat_shamir_declaration_names_same_core_protocol_endpoints(self) -> None:
        term = FIAT_SHAMIR_CONSTRUCTION_DECLARATION.to_term()
        self.assertEqual(
            term["source_protocol_id"],
            FRESH_WORK_AUGMENTED_PROTOCOL.identity.to_term(),
        )
        self.assertEqual(
            term["target_protocol_id"],
            FIAT_SHAMIR_WORK_AUGMENTED_PROTOCOL.identity.to_term(),
        )
        self.assertEqual(
            term["shared_core_id"],
            WORK_AUGMENTED_COMMITTED_FRI_CORE.identity.to_term(),
        )
        self.assertEqual(
            tuple(term["required_capabilities"]),
            FIAT_SHAMIR_CONSTRUCTION_CAPABILITIES,
        )
        self.assertEqual(
            tuple(term["admission_requirements"]),
            FIAT_SHAMIR_CONSTRUCTION_REQUIREMENTS,
        )
        self.assertEqual(
            tuple(term["nonclaims"]),
            FIAT_SHAMIR_CONSTRUCTION_NONCLAIMS,
        )

    def test_declarations_do_not_self_author_their_discharge(self) -> None:
        declarations = (
            COMMITMENT_COMPILATION_DECLARATION,
            GRINDING_AUGMENTATION_DECLARATION,
            FIAT_SHAMIR_CONSTRUCTION_DECLARATION,
        )
        for declaration in declarations:
            with self.subTest(declaration=type(declaration).__name__):
                term = declaration.to_term()
                self.assertEqual(term["declaration_status"], DECLARATION_STATUS)
                self.assertIn(
                    "proof-that-the-declared-requirements-hold",
                    term["nonclaims"],
                )
                self.assertNotIn("checked", term)
                self.assertNotIn("holds", term)
                self.assertNotIn("evidence", term)


class CheckedFiatShamirAdmissionTest(unittest.TestCase):
    def test_exact_construction_is_structurally_admitted_and_keyed(self) -> None:
        admission = admit_fiat_shamir_construction(
            FIAT_SHAMIR_CONSTRUCTION_DECLARATION,
            CANONICAL_PUBLIC_OCCURRENCE_PROTECTION_MAP,
        )
        self.assertIs(admission.result.outcome, OutcomeClass.AFFIRMATIVE)
        self.assertEqual(admission.result.code, "FRI-IOR-SUBJECT-101")
        checked = admission.checked_construction
        self.assertIsNotNone(checked)
        self.assertEqual(checked, CHECKED_FIAT_SHAMIR_CONSTRUCTION)
        term = checked.to_term()
        self.assertEqual(
            term["work_augmented_committed_core_id"],
            WORK_AUGMENTED_COMMITTED_FRI_CORE.identity.to_term(),
        )
        self.assertEqual(
            term["transcript_plan_id"],
            transcript_plan_identity(CANONICAL_CONSTRUCTION_PLAN).to_term(),
        )
        self.assertEqual(
            term["fresh_protocol_id"],
            FRESH_WORK_AUGMENTED_PROTOCOL.identity.to_term(),
        )
        self.assertEqual(
            term["fiat_shamir_protocol_id"],
            FIAT_SHAMIR_WORK_AUGMENTED_PROTOCOL.identity.to_term(),
        )
        self.assertEqual(
            term["admission_scope"],
            "structural-construction-only",
        )
        self.assertEqual(tuple(term["nonclaims"]), FIAT_SHAMIR_CONSTRUCTION_NONCLAIMS)

    def test_protection_map_is_total_and_positions_are_exact(self) -> None:
        core_occurrences = tuple(
            WORK_AUGMENTED_COMMITTED_FRI_CORE.to_term()[
                "acceptance_affecting_public_occurrences"
            ]
        )
        mapped = tuple(
            entry.core_occurrence
            for entry in CANONICAL_PUBLIC_OCCURRENCE_PROTECTION_MAP
        )
        self.assertEqual(mapped, core_occurrences)
        by_name = {
            entry.core_occurrence: entry
            for entry in CANONICAL_PUBLIC_OCCURRENCE_PROTECTION_MAP
        }
        self.assertEqual(by_name["statement"].transcript_position, 0)
        self.assertEqual(by_name["cap[0]"].transcript_position, 2)
        self.assertEqual(by_name["terminal-polynomial"].transcript_position, 6)
        self.assertEqual(by_name["grinding-nonce"].transcript_position, 8)
        self.assertEqual(by_name["query-occurrences"].transcript_position, 11)
        self.assertNotIn("query-seed", by_name)
        plan_by_name = {
            step.occurrence: (index, step)
            for index, step in enumerate(CANONICAL_CONSTRUCTION_PLAN.steps)
        }
        seed_position, seed_step = plan_by_name["query-seed"]
        vector_position, vector_step = plan_by_name["query-occurrences"]
        self.assertEqual(seed_step.kind, "DeriveChallenge")
        self.assertEqual(vector_step.kind, "SampleOccurrences")
        self.assertLess(seed_position, vector_position)
        self.assertIn("query-occurrences", seed_step.protected_occurrences)
        final_response = by_name["opening-table-and-occurrence-selectors"]
        self.assertIsNone(final_response.transcript_position)
        self.assertEqual(
            final_response.disposition,
            POST_FINAL_CHALLENGE_PUBLIC_RESPONSE,
        )

    def test_protection_map_requires_typed_statement_context_ports(self) -> None:
        term = WORK_AUGMENTED_COMMITTED_FRI_CORE.to_term()
        term["public_context_ports"] = term["public_context_ports"][:1]
        with self.assertRaises(ModelFailure) as raised:
            subjects_model._expected_protection_map(
                term,
                CANONICAL_CONSTRUCTION_PLAN,
            )
        self.assertIs(raised.exception.outcome, OutcomeClass.REFUSED)
        self.assertEqual(raised.exception.code, "FRI-IOR-SUBJECT-036")

    def test_omitted_extra_and_reordered_map_entries_fail_totality(self) -> None:
        exact = CANONICAL_PUBLIC_OCCURRENCE_PROTECTION_MAP
        mutations = (
            exact[:-1],
            exact + (exact[-1],),
            (exact[1], exact[0], *exact[2:]),
        )
        for mutation in mutations:
            with self.subTest(length=len(mutation)):
                admission = admit_fiat_shamir_construction(
                    FIAT_SHAMIR_CONSTRUCTION_DECLARATION,
                    mutation,
                )
                self.assertIs(admission.result.outcome, OutcomeClass.REFUSED)
                self.assertEqual(admission.result.code, "FRI-IOR-SUBJECT-028")
                self.assertIsNone(admission.checked_construction)

    def test_wrong_position_or_protection_set_is_refused(self) -> None:
        exact = CANONICAL_PUBLIC_OCCURRENCE_PROTECTION_MAP
        wrong_position = replace(exact[0], transcript_position=1)
        wrong_dependents = replace(exact[0], protected_dependents=("query-seed",))
        for replacement in (wrong_position, wrong_dependents):
            mutation = (replacement, *exact[1:])
            admission = admit_fiat_shamir_construction(
                FIAT_SHAMIR_CONSTRUCTION_DECLARATION,
                mutation,
            )
            self.assertIs(admission.result.outcome, OutcomeClass.REFUSED)
            self.assertEqual(admission.result.code, "FRI-IOR-SUBJECT-029")

    def test_added_or_omitted_core_occurrence_fails_totality_before_identity(self) -> None:
        exact_occurrences = (
            *WORK_AUGMENTED_COMMITTED_FRI_CORE.acceptance_affecting_public_occurrences,
        )
        for core, code in (
            (
                WorkAugmentedCommittedFriCore(
                    COMMITTED_FRI_CORE,
                    acceptance_affecting_public_occurrences=(
                        *exact_occurrences,
                        "new-acceptance-affecting-publication",
                    ),
                ),
                "FRI-IOR-SUBJECT-022",
            ),
            (
                WorkAugmentedCommittedFriCore(
                    COMMITTED_FRI_CORE,
                    acceptance_affecting_public_occurrences=exact_occurrences[:-1],
                ),
                "FRI-IOR-SUBJECT-028",
            ),
        ):
            fresh = FreshWorkAugmentedProtocol(
                core,
                FreshChallengeInterpretation(core),
            )
            fiat_shamir = FiatShamirWorkAugmentedProtocol(
                core,
                FiatShamirChallengeInterpretation(core),
            )
            declaration = CheckedFiatShamirConstructionDeclaration(
                fresh,
                fiat_shamir,
            )
            admission = admit_fiat_shamir_construction(
                declaration,
                CANONICAL_PUBLIC_OCCURRENCE_PROTECTION_MAP,
            )
            self.assertIs(admission.result.outcome, OutcomeClass.REFUSED)
            self.assertEqual(admission.result.code, code)

    def test_non_public_coin_source_core_is_refused(self) -> None:
        core = WorkAugmentedCommittedFriCore(
            COMMITTED_FRI_CORE,
            public_coin=False,
        )
        fresh = FreshWorkAugmentedProtocol(core, FreshChallengeInterpretation(core))
        target = FiatShamirWorkAugmentedProtocol(
            core,
            FiatShamirChallengeInterpretation(core),
        )
        declaration = CheckedFiatShamirConstructionDeclaration(fresh, target)
        admission = admit_fiat_shamir_construction(
            declaration,
            CANONICAL_PUBLIC_OCCURRENCE_PROTECTION_MAP,
        )
        self.assertIs(admission.result.outcome, OutcomeClass.REFUSED)
        self.assertEqual(admission.result.code, "FRI-IOR-SUBJECT-027")

    def test_checked_construction_rejects_an_unissued_admission_token(self) -> None:
        with self.assertRaises(ModelFailure) as raised:
            CheckedFiatShamirConstruction(
                FIAT_SHAMIR_CONSTRUCTION_DECLARATION.identity,
                WORK_AUGMENTED_COMMITTED_FRI_CORE.identity,
                transcript_plan_identity(CANONICAL_CONSTRUCTION_PLAN),
                FRESH_WORK_AUGMENTED_PROTOCOL.identity,
                FIAT_SHAMIR_WORK_AUGMENTED_PROTOCOL.identity,
                CANONICAL_PUBLIC_OCCURRENCE_PROTECTION_MAP,
                _token=object(),
            )
        self.assertIs(raised.exception.outcome, OutcomeClass.MISSING_DEPENDENCY)
        self.assertEqual(raised.exception.code, "FRI-IOR-SUBJECT-023")


class KindAndIdentityBoundaryTest(unittest.TestCase):
    def test_wrong_core_and_interpretation_kinds_are_rejected(self) -> None:
        constructors = (
            lambda: WorkAugmentedCommittedFriCore(NATIVE_FRI_CORE),
            lambda: FreshChallengeInterpretation(COMMITTED_FRI_CORE),
            lambda: FreshWorkAugmentedProtocol(
                WORK_AUGMENTED_COMMITTED_FRI_CORE,
                FIAT_SHAMIR_CHALLENGE_INTERPRETATION,
            ),
            lambda: FiatShamirWorkAugmentedProtocol(
                WORK_AUGMENTED_COMMITTED_FRI_CORE,
                FRESH_CHALLENGE_INTERPRETATION,
            ),
        )
        for constructor in constructors:
            with self.subTest(constructor=constructor), self.assertRaises(
                ModelFailure
            ) as raised:
                constructor()
            self.assertIs(raised.exception.outcome, OutcomeClass.KIND_MISMATCH)
            self.assertEqual(raised.exception.code, "FRI-IOR-SUBJECT-001")

    def test_construction_endpoint_direction_is_typed(self) -> None:
        constructors = (
            lambda: CheckedCommitmentCompilationDeclaration(
                COMMITTED_FRI_CORE,
                NATIVE_FRI_CORE,
            ),
            lambda: CheckedGrindingAugmentationDeclaration(
                NATIVE_FRI_CORE,
                WORK_AUGMENTED_COMMITTED_FRI_CORE,
            ),
            lambda: CheckedFiatShamirConstructionDeclaration(
                FIAT_SHAMIR_WORK_AUGMENTED_PROTOCOL,
                FRESH_WORK_AUGMENTED_PROTOCOL,
            ),
        )
        for constructor in constructors:
            with self.subTest(constructor=constructor), self.assertRaises(
                ModelFailure
            ) as raised:
                constructor()
            self.assertIs(raised.exception.outcome, OutcomeClass.KIND_MISMATCH)
            self.assertEqual(raised.exception.code, "FRI-IOR-SUBJECT-001")

    def test_same_core_is_enforced_even_for_correct_protocol_classes(self) -> None:
        different = WorkAugmentedCommittedFriCore(
            COMMITTED_FRI_CORE,
            acceptance_affecting_public_occurrences=(
                *WORK_AUGMENTED_COMMITTED_FRI_CORE.acceptance_affecting_public_occurrences,
                "different-public-occurrence",
            ),
        )
        target = FiatShamirWorkAugmentedProtocol(
            different,
            FiatShamirChallengeInterpretation(different),
        )
        with self.assertRaises(ModelFailure) as raised:
            CheckedFiatShamirConstructionDeclaration(
                FRESH_WORK_AUGMENTED_PROTOCOL,
                target,
            )
        self.assertIs(raised.exception.outcome, OutcomeClass.KIND_MISMATCH)
        self.assertEqual(raised.exception.code, "FRI-IOR-SUBJECT-006")

    def test_spoofed_endpoint_subclasses_are_not_admission_types(self) -> None:
        class SpoofedCore(WorkAugmentedCommittedFriCore):
            @property
            def identity(self) -> SemanticId:
                return WORK_AUGMENTED_COMMITTED_FRI_CORE.identity

            def to_term(self) -> dict[str, object]:
                term = super().to_term()
                term["acceptance_affecting_public_occurrences"] = [
                    "query-occurrences"
                ]
                return term

        class SpoofedDeclaration(CheckedFiatShamirConstructionDeclaration):
            @property
            def identity(self) -> SemanticId:
                return FIAT_SHAMIR_CONSTRUCTION_DECLARATION.identity

        with self.assertRaises(ModelFailure) as raised:
            FreshChallengeInterpretation(SpoofedCore(COMMITTED_FRI_CORE))
        self.assertIs(raised.exception.outcome, OutcomeClass.KIND_MISMATCH)
        self.assertEqual(raised.exception.code, "FRI-IOR-SUBJECT-001")

        spoofed = SpoofedDeclaration(
            FRESH_WORK_AUGMENTED_PROTOCOL,
            FIAT_SHAMIR_WORK_AUGMENTED_PROTOCOL,
        )
        admission = admit_fiat_shamir_construction(
            spoofed,
            CANONICAL_PUBLIC_OCCURRENCE_PROTECTION_MAP,
        )
        self.assertIs(admission.result.outcome, OutcomeClass.KIND_MISMATCH)
        self.assertEqual(admission.result.code, "FRI-IOR-SUBJECT-025")

    def test_well_formed_alternate_transcript_plan_is_unsupported(self) -> None:
        alternate_law = semantic_id(
            "fri-ior-semantic-law",
            "fri-ior.semantic-law.v1",
            {"name": "alternate-transcript-hash-law"},
        )
        alternate = replace(
            CANONICAL_CONSTRUCTION_PLAN,
            semantic_law_ids=(
                alternate_law,
                *CANONICAL_CONSTRUCTION_PLAN.semantic_law_ids[1:],
            ),
        )
        with self.assertRaises(ModelFailure) as raised:
            FiatShamirChallengeInterpretation(
                WORK_AUGMENTED_COMMITTED_FRI_CORE,
                alternate,
            )
        self.assertIs(raised.exception.outcome, OutcomeClass.UNSUPPORTED)
        self.assertEqual(raised.exception.code, "FRI-IOR-SUBJECT-003")

    def test_subject_admission_refuses_identity_proxies_and_malformed_values(self) -> None:
        for subject in (
            NATIVE_FRI_CORE,
            COMMITTED_FRI_CORE,
            WORK_AUGMENTED_COMMITTED_FRI_CORE,
            FRESH_WORK_AUGMENTED_PROTOCOL,
            FIAT_SHAMIR_WORK_AUGMENTED_PROTOCOL,
            COMMITMENT_COMPILATION_DECLARATION,
            GRINDING_AUGMENTATION_DECLARATION,
            FIAT_SHAMIR_CONSTRUCTION_DECLARATION,
            CHECKED_FIAT_SHAMIR_CONSTRUCTION,
        ):
            result = admit_selected_subject(subject)
            self.assertIs(result.outcome, OutcomeClass.AFFIRMATIVE)
            self.assertEqual(result.subject, subject.identity)
        proxy = admit_selected_subject(NATIVE_FRI_CORE.identity)
        self.assertIs(proxy.outcome, OutcomeClass.KIND_MISMATCH)
        self.assertEqual(proxy.code, "FRI-IOR-SUBJECT-007")
        malformed = admit_selected_subject({"schema": "looks-like-a-subject"})
        self.assertIs(malformed.outcome, OutcomeClass.MALFORMED)
        self.assertEqual(malformed.code, "FRI-IOR-SUBJECT-008")

    def test_semantic_subjects_do_not_use_content_validation_or_evidence_ids(self) -> None:
        subjects = (
            NATIVE_FRI_CORE,
            COMMITTED_FRI_CORE,
            WORK_AUGMENTED_COMMITTED_FRI_CORE,
            FRESH_CHALLENGE_INTERPRETATION,
            FIAT_SHAMIR_CHALLENGE_INTERPRETATION,
            FRESH_WORK_AUGMENTED_PROTOCOL,
            FIAT_SHAMIR_WORK_AUGMENTED_PROTOCOL,
            COMMITMENT_COMPILATION_DECLARATION,
            GRINDING_AUGMENTATION_DECLARATION,
            FIAT_SHAMIR_CONSTRUCTION_DECLARATION,
            CHECKED_FIAT_SHAMIR_CONSTRUCTION,
        )
        forbidden_keys = {
            "artifact_content_id",
            "canonical_content_id",
            "validation_basis_id",
            "execution_id",
            "evidence_id",
            "report_id",
        }
        for subject in subjects:
            with self.subTest(subject=type(subject).__name__):
                self.assertIsInstance(subject.identity, SemanticId)
                self.assertNotIsInstance(subject.identity, ArtifactContentId)
                self.assertNotIsInstance(subject.identity, CanonicalContentId)
                self.assertNotIsInstance(subject.identity, ValidationBasisId)
                self.assertTrue(forbidden_keys.isdisjoint(_all_keys(subject.to_term())))


if __name__ == "__main__":
    unittest.main()
