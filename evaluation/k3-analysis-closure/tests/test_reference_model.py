from __future__ import annotations

from dataclasses import fields, replace
from fractions import Fraction
from functools import lru_cache
import hashlib
from pathlib import Path
import sys
from types import MappingProxyType
import unittest
from unittest.mock import patch


PACKAGE_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(PACKAGE_ROOT))

import reference_model as model  # noqa: E402


def activate_analysis_profiles(profiles: object) -> object:
    """Patch one complete authenticated profile set into the test model."""

    return patch.multiple(
        model,
        K3C_ANALYSIS_SEMANTIC_PROFILES=profiles,
        K3C_ANALYSIS_KERNEL_PROFILE=profiles.kernel,
        K3C_ANALYSIS_KERNEL_PROFILE_ID=profiles.kernel.identity,
        K3C_ANALYSIS_PROPERTY_PROFILE=profiles.property,
        K3C_ANALYSIS_PROPERTY_PROFILE_ID=profiles.property.identity,
        K3C_ANALYSIS_TRANSPORT_PROFILE=profiles.transport,
        K3C_ANALYSIS_TRANSPORT_PROFILE_ID=profiles.transport.identity,
        K3C_ANALYSIS_THEOREM_SOURCE_VALIDATION_PROFILE=(
            profiles.theorem_source_validation
        ),
        K3C_ANALYSIS_THEOREM_SOURCE_VALIDATION_PROFILE_ID=(
            profiles.theorem_source_validation.identity
        ),
        K3C_ANALYSIS_KERNEL_PROFILE_BUNDLE=profiles.kernel_bundle,
        K3C_ANALYSIS_PROPERTY_PROFILE_BUNDLE=profiles.property_bundle,
        K3C_ANALYSIS_TRANSPORT_PROFILE_BUNDLE=profiles.transport_bundle,
        K3C_ANALYSIS_THEOREM_SOURCE_VALIDATION_PROFILE_BUNDLE=(
            profiles.theorem_source_validation_bundle
        ),
        K3C_PROFILE_BUNDLE=profiles.bundle,
        K3C_PROFILE_PREIMAGES=profiles.bundle,
    )


@lru_cache(maxsize=1)
def fixed_context() -> tuple[object, ...]:
    source, source_model, target_model = model.selected_fixed_member_fixture()
    profile = model.derive_schnorr_special_soundness_profile(source)
    correspondence = model.derive_fs_correspondence(source, source_model, target_model)
    assumptions = model.fixed_member_required_hypotheses(
        model.SELECTED_AFK_FAMILY,
        source,
        source_model,
        target_model,
        correspondence,
    )
    outcome = model.form_concrete_family_instance_correspondence(
        model.SELECTED_AFK_FAMILY,
        source,
        source_model,
        target_model,
        assumptions,
        correspondence=correspondence,
    )
    if outcome.kind is not model.AttemptKind.AFFIRMATIVE:
        raise AssertionError(outcome)
    return (
        source,
        profile,
        source_model,
        target_model,
        correspondence,
        assumptions,
        outcome.value,
    )


@lru_cache(maxsize=1)
def family_context() -> tuple[object, ...]:
    schema = model.afk_v2_theorem_schema()
    family = model.SELECTED_AFK_FAMILY
    candidate = model.derive_family_applicability_input(schema, family)
    premises = model.family_applicability_premise_ids(family)
    application = model.check_afk_family_applicability(
        schema, family, premises, candidate=candidate
    )
    if application.kind is not model.AttemptKind.AFFIRMATIVE:
        raise AssertionError(application)
    source_capability = model.assume_external_family_source_capability_for_fixture(
        family, authority_label="test-assumed-all-n-source-authority"
    )
    theorem_truth = model.assume_afk_theorem_truth(schema)
    transport = model.transport_afk_family_knowledge(
        source_capability, application.value, theorem_truth
    )
    if transport.kind is not model.AttemptKind.AFFIRMATIVE:
        raise AssertionError(transport)
    return (
        schema,
        family,
        candidate,
        premises,
        application.value,
        source_capability,
        theorem_truth,
        transport.value,
    )


def fixed_source_judgment() -> model.EstablishedJudgment:
    source, profile, source_model, *_ = fixed_context()
    proposition = model.form_special_soundness_proposition(
        source,
        source_model,
        profile,
        (
            model.schnorr_relation_correspondence_hypothesis_id(profile),
            model.k2_static_view_support_hypothesis_id(source),
            model.ASSUMED_SCHNORR_TWO_SPECIAL_SOUNDNESS,
        ),
    )
    return model.establish_conditionally(
        proposition, model.schnorr_special_soundness_rule(proposition)
    )


class SemanticProfileIntegrationTest(unittest.TestCase):
    @staticmethod
    def probe_body() -> object:
        return model.k1.DatumRecord(
            ((0, model.k1.Symbol("k3c-profile-locality-probe")),)
        )

    def test_transport_profile_has_one_exact_transitive_import_closure(self) -> None:
        profiles = model.K3C_ANALYSIS_SEMANTIC_PROFILES
        self.assertEqual(profiles.kernel.profile_imports, ())
        self.assertEqual(
            profiles.property.profile_imports,
            model._profile_imports(
                profiles.kernel,
                profiles.k3b_profiles.relations_correspondence,
            ),
        )
        self.assertEqual(
            profiles.transport.profile_imports,
            (profiles.property.identity,),
        )
        context = model.k1.effective_semantic_context(
            profiles.transport.identity,
            model.K3C_ANALYSIS_TRANSPORT_PROFILE_BUNDLE,
            semantic_regime=model.k1.SEMANTIC_REGIME_ID,
        )
        self.assertEqual(len(context.authenticated_profiles), 7)
        relations_closure = model.k3.K3B_ROOT_PROFILE_PREIMAGES[
            profiles.k3b_profiles.relations_correspondence.identity
        ]
        self.assertEqual(
            set(model.K3C_ANALYSIS_TRANSPORT_PROFILE_BUNDLE),
            {
                *relations_closure,
                profiles.kernel.identity,
                profiles.property.identity,
                profiles.transport.identity,
            },
        )

    def test_theorem_source_validation_is_a_one_way_child_profile(self) -> None:
        profiles = model.K3C_ANALYSIS_SEMANTIC_PROFILES
        self.assertEqual(
            profiles.theorem_source_validation.profile_imports,
            (profiles.transport.identity,),
        )
        self.assertNotIn(
            profiles.theorem_source_validation.identity,
            profiles.transport.profile_imports,
        )
        context = model.k1.effective_semantic_context(
            profiles.theorem_source_validation.identity,
            model.K3C_ANALYSIS_THEOREM_SOURCE_VALIDATION_PROFILE_BUNDLE,
            semantic_regime=model.k1.SEMANTIC_REGIME_ID,
        )
        self.assertEqual(len(context.authenticated_profiles), 8)
        self.assertEqual(
            set(model.K3C_PROFILE_BUNDLE),
            set(model.K3C_ANALYSIS_THEOREM_SOURCE_VALIDATION_PROFILE_BUNDLE),
        )

    def test_property_and_transport_subjects_authenticate_exact_profiles(self) -> None:
        property_id = model.AFK_POSITIVE_POLYNOMIAL_Q_ONE
        property_body = model._formed_analysis_body(
            property_id,
            "analysis.positive-polynomial",
        )
        property_context = model.k1.authenticate_profiled_semantic_content(
            property_id,
            model.K3C_ANALYSIS_PROPERTY_PROFILE_ID,
            model.analysis_domain_body_v0(
                "analysis.positive-polynomial",
                property_body,
            ),
            model.K3C_ANALYSIS_PROPERTY_PROFILE_BUNDLE,
            supported_profiles=(model.K3C_ANALYSIS_PROPERTY_PROFILE_ID,),
        )
        self.assertEqual(
            property_context.selected_profile,
            model.K3C_ANALYSIS_PROPERTY_PROFILE_ID,
        )

        transport_id = model.family_goal_id(
            model.SELECTED_AFK_FAMILY,
            "source-two-special-soundness",
        )
        transport_body = model._formed_analysis_body(
            transport_id,
            "analysis.goal",
        )
        transport_context = model.k1.authenticate_profiled_semantic_content(
            transport_id,
            model.K3C_ANALYSIS_TRANSPORT_PROFILE_ID,
            model.analysis_domain_body_v0("analysis.goal", transport_body),
            model.K3C_ANALYSIS_TRANSPORT_PROFILE_BUNDLE,
            supported_profiles=(model.K3C_ANALYSIS_TRANSPORT_PROFILE_ID,),
        )
        self.assertEqual(
            transport_context.selected_profile,
            model.K3C_ANALYSIS_TRANSPORT_PROFILE_ID,
        )

    def test_profile_subject_partition_refuses_cross_lane_minting(self) -> None:
        with self.assertRaisesRegex(model.AnalysisError, "raw Analysis profile"):
            model.analysis_profiled_content_id(
                "analysis.positive-polynomial",
                self.probe_body(),
                model.K3C_ANALYSIS_PROPERTY_PROFILE,
            )

        property_id = model.AFK_POSITIVE_POLYNOMIAL_Q_ONE
        property_body = model._formed_analysis_body(
            property_id,
            "analysis.positive-polynomial",
        )
        with self.assertRaises(model.AnalysisError):
            model._form_analysis_profiled_content_id(
                "analysis.positive-polynomial",
                property_body,
                model.K3C_ANALYSIS_TRANSPORT_PROFILE,
            )

        transport_id = model.family_goal_id(
            model.SELECTED_AFK_FAMILY,
            "source-two-special-soundness",
        )
        transport_body = model._formed_analysis_body(transport_id, "analysis.goal")
        with self.assertRaisesRegex(model.AnalysisError, "requires profile"):
            model._form_analysis_profiled_content_id(
                "analysis.goal",
                transport_body,
                model.K3C_ANALYSIS_PROPERTY_PROFILE,
            )

        validation_body = model._formed_analysis_body(
            model.AFK_V2_THM4_SOURCE_VALIDATION,
            "analysis.theorem-source-validation",
        )
        for wrong_profile in (
            model.K3C_ANALYSIS_PROPERTY_PROFILE,
            model.K3C_ANALYSIS_TRANSPORT_PROFILE,
        ):
            with self.subTest(wrong_profile=wrong_profile.profile_family.value):
                with self.assertRaises(model.AnalysisError):
                    model._form_analysis_profiled_content_id(
                        "analysis.theorem-source-validation",
                        validation_body,
                        wrong_profile,
                    )
        self.assertTrue(
            {"analysis.question", "analysis.goal", "analysis.proposition"}
            <= {
                item.value
                for item in model.K3C_ANALYSIS_PROPERTY_PROFILE.supported_subject_kinds
            }
        )
        self.assertTrue(
            {"analysis.question", "analysis.goal", "analysis.proposition"}
            <= {
                item.value
                for item in model.K3C_ANALYSIS_TRANSPORT_PROFILE.supported_subject_kinds
            }
        )

    def test_profile_bundle_refuses_missing_and_extra_preimages(self) -> None:
        profiles = model.K3C_ANALYSIS_SEMANTIC_PROFILES
        missing = dict(model.K3C_ANALYSIS_TRANSPORT_PROFILE_BUNDLE)
        missing.pop(profiles.property.identity)
        with self.assertRaises(model.k1._Control) as caught:
            model.k1.effective_semantic_context(
                profiles.transport.identity,
                missing,
                semantic_regime=model.k1.SEMANTIC_REGIME_ID,
            )
        self.assertIs(
            caught.exception.outcome,
            model.k1.Outcome.MISSING_DEPENDENCY,
        )

        unrelated = model.make_k3c_analysis_semantic_profiles(
            transport_law=model._profile_law_source(
                "zkc.analysis.bounded-transport-law.v1",
                ("unreferenced-profile-locality-probe",),
            )
        ).transport
        with self.assertRaises(model.k1._Control) as caught:
            model.k1.effective_semantic_context(
                profiles.transport.identity,
                {
                    **model.K3C_ANALYSIS_TRANSPORT_PROFILE_BUNDLE,
                    unrelated.identity: unrelated,
                },
                semantic_regime=model.k1.SEMANTIC_REGIME_ID,
            )
        self.assertIs(caught.exception.outcome, model.k1.Outcome.REFUSED)

    def test_profile_changes_rotate_only_their_dependency_cone(self) -> None:
        baseline = model.K3C_ANALYSIS_SEMANTIC_PROFILES
        changed_transport = model.make_k3c_analysis_semantic_profiles(
            transport_law=model._profile_law_source(
                "zkc.analysis.bounded-transport-law.v1",
                ("transport-local-change",),
            )
        )
        self.assertEqual(baseline.kernel.identity, changed_transport.kernel.identity)
        self.assertEqual(
            baseline.property.identity,
            changed_transport.property.identity,
        )
        self.assertNotEqual(
            baseline.transport.identity,
            changed_transport.transport.identity,
        )
        body = model.k1.BytesValue(b"k3c-profile-locality-probe")
        self.assertEqual(
            model.k1.profiled_content_id(
                "analysis.property-profile",
                baseline.property.identity,
                body,
                semantic_regime=model.k1.SEMANTIC_REGIME_ID,
            ),
            model.k1.profiled_content_id(
                "analysis.property-profile",
                changed_transport.property.identity,
                body,
                semantic_regime=model.k1.SEMANTIC_REGIME_ID,
            ),
        )
        self.assertNotEqual(
            model.k1.profiled_content_id(
                "analysis.family-theorem-applicability-result",
                baseline.transport.identity,
                body,
                semantic_regime=model.k1.SEMANTIC_REGIME_ID,
            ),
            model.k1.profiled_content_id(
                "analysis.family-theorem-applicability-result",
                changed_transport.transport.identity,
                body,
                semantic_regime=model.k1.SEMANTIC_REGIME_ID,
            ),
        )

        changed_validation = model.make_k3c_analysis_semantic_profiles(
            theorem_source_validation_law=model._profile_law_source(
                "zkc.analysis.afk-theorem-source-validation-law.v0",
                ("validation-only-local-change",),
            )
        )
        self.assertEqual(
            baseline.transport.identity,
            changed_validation.transport.identity,
        )
        self.assertNotEqual(
            baseline.theorem_source_validation.identity,
            changed_validation.theorem_source_validation.identity,
        )

        changed_kernel = model.make_k3c_analysis_semantic_profiles(
            kernel_law=model._profile_law_source(
                "zkc.analysis.kernel-law.v1",
                ("kernel-local-change",),
            )
        )
        self.assertNotEqual(baseline.kernel.identity, changed_kernel.kernel.identity)
        self.assertNotEqual(
            baseline.property.identity,
            changed_kernel.property.identity,
        )
        self.assertNotEqual(
            baseline.transport.identity,
            changed_kernel.transport.identity,
        )

        changed_k3b = model.k3.make_k3b_semantic_profiles(
            relations_law=b"zkc-k3b-relations-correspondence-law-v1"
        )
        changed_relations = model.make_k3c_analysis_semantic_profiles(
            k3b_profiles=changed_k3b
        )
        self.assertEqual(baseline.kernel.identity, changed_relations.kernel.identity)
        self.assertNotEqual(
            baseline.property.identity,
            changed_relations.property.identity,
        )
        self.assertNotEqual(
            baseline.transport.identity,
            changed_relations.transport.identity,
        )

    def test_validation_profile_and_transport_profile_have_no_backflow(self) -> None:
        schema = model.afk_v2_theorem_schema()
        baseline_schema_id = model.fs_theorem_schema_id(schema)
        baseline_question_body = model.theorem_truth_question_body(schema)
        baseline_goal_id = model.theorem_truth_goal_id(schema)
        baseline_validation_id = model.theorem_source_validation_id(schema)
        baseline_digest = model.theorem_statement_digest(schema)

        validation_only = model.make_k3c_analysis_semantic_profiles(
            theorem_source_validation_law=model._profile_law_source(
                "zkc.analysis.afk-theorem-source-validation-law.v0",
                ("validation-only-nonbackflow-probe",),
            )
        )
        with activate_analysis_profiles(validation_only):
            changed_validation_id = model.theorem_source_validation_id(schema)
            self.assertEqual(baseline_schema_id, model.fs_theorem_schema_id(schema))
            self.assertEqual(
                baseline_question_body,
                model.theorem_truth_question_body(schema),
            )
            self.assertEqual(baseline_goal_id, model.theorem_truth_goal_id(schema))
        self.assertNotEqual(baseline_validation_id, changed_validation_id)

        semantic_change = model.make_k3c_analysis_semantic_profiles(
            transport_law=model._profile_law_source(
                "zkc.analysis.bounded-transport-law.v0",
                ("semantic-transport-forward-rotation-probe",),
            )
        )
        with activate_analysis_profiles(semantic_change):
            changed_digest = model.theorem_statement_digest(schema)
            changed_schema_id = model.fs_theorem_schema_id(schema)
            changed_schema = replace(
                schema,
                authority=replace(
                    schema.authority,
                    statement_content_sha256=changed_digest,
                ),
            )
            changed_validation = model.theorem_source_validation_id(changed_schema)
        self.assertNotEqual(baseline_digest, changed_digest)
        self.assertNotEqual(baseline_schema_id, changed_schema_id)
        self.assertNotEqual(baseline_validation_id, changed_validation)

    def test_property_source_identities_follow_their_owning_profiles(self) -> None:
        proposition = model._SCHNORR_PINNED_PROPOSITION
        baseline_schnorr = (
            model.analysis_proposition_id(proposition),
            model.schnorr_semantic_basis_id(proposition),
        )
        family = model.SELECTED_AFK_FAMILY
        authority = model.fixture_ref(
            "k3c.external-proof-authority",
            "profile-locality-external-source",
        )
        baseline_hypothesis, baseline_result, _ = model._family_source_components(
            family,
            authority,
        )
        changed = model.make_k3c_analysis_semantic_profiles(
            transport_law=model._profile_law_source(
                "zkc.analysis.bounded-transport-law.v0",
                ("downstream-only-source-locality-probe",),
            )
        )
        with activate_analysis_profiles(changed):
            self.assertEqual(
                baseline_schnorr,
                (
                    model.analysis_proposition_id(proposition),
                    model.schnorr_semantic_basis_id(proposition),
                ),
            )
            hypothesis, result, _ = model._family_source_components(
                family,
                authority,
            )
            self.assertNotEqual(baseline_hypothesis, hypothesis)
            self.assertNotEqual(baseline_result, result)

    def test_analysis_law_sources_are_canonical_closed_data(self) -> None:
        for profile in (
            model.K3C_ANALYSIS_KERNEL_PROFILE,
            model.K3C_ANALYSIS_PROPERTY_PROFILE,
            model.K3C_ANALYSIS_TRANSPORT_PROFILE,
            model.K3C_ANALYSIS_THEOREM_SOURCE_VALIDATION_PROFILE,
        ):
            with self.subTest(profile=profile.profile_family.value):
                decoded = model.k1.decode_datum(profile.semantic_law_source)
                self.assertEqual(
                    model.k1.encode_datum(decoded),
                    profile.semantic_law_source,
                )
                self.assertIsInstance(decoded, model.k1.DatumRecord)

    def test_fixture_subjects_remain_direct_k1_identities(self) -> None:
        label = "direct-k1-foundation-fixture"
        body = model.k1.DatumRecord(((0, model.k1.Symbol(label)),))
        fixture = model.fixture_ref("analysis.hypothesis", label)
        self.assertEqual(
            fixture,
            model.k1.content_id(
                "analysis.hypothesis",
                model.k1.encode_datum(body),
                semantic_regime=model.k1.SEMANTIC_REGIME_ID,
            ),
        )
        self.assertNotEqual(
            fixture,
            model.k1.profiled_content_id(
                "analysis.hypothesis",
                model.K3C_ANALYSIS_PROPERTY_PROFILE_ID,
                body,
                semantic_regime=model.k1.SEMANTIC_REGIME_ID,
            ),
        )


class ImportAndFiniteSourceTest(unittest.TestCase):
    def test_import_chain_is_exact(self) -> None:
        self.assertIs(model.k2, model.k3.k2)
        self.assertIs(model.k1, model.k3.k1)
        self.assertIs(model.k1, model.k2.k1)

    def test_native_protocol_ids_are_owner_derived(self) -> None:
        source, *_ = fixed_context()
        self.assertEqual(
            source.protocol_source.core_id, model.k2.core_id(source.case.core)
        )
        self.assertEqual(
            source.protocol_source.construction_id,
            model.k2.construction_id(source.case.core, source.case.construction),
        )

    def test_source_quantifier_order_is_extractor_then_pair(self) -> None:
        prefix = model.fresh_special_soundness_model().quantifiers
        self.assertEqual(
            tuple((item.kind, item.binder) for item in prefix),
            (
                (
                    model.QuantifierKind.EXISTS_DETERMINISTIC_TRANSCRIPT_EXTRACTOR,
                    "deterministic-transcript-extractor",
                ),
                (model.QuantifierKind.FOR_ALL_VALUE, "accepted-transcript-pair"),
            ),
        )

    def test_source_conclusion_is_not_a_knowledge_error(self) -> None:
        conclusion = fixed_source_judgment().proposition.goal.conclusion
        self.assertIsInstance(conclusion, model.SpecialSoundnessConclusion)
        self.assertFalse(hasattr(conclusion, "knowledge_error"))

    def test_two_accepting_transcripts_extract_relation_witness(self) -> None:
        source, profile, *_ = fixed_context()
        result = model.extract_schnorr_witness(
            source,
            profile,
            model.SchnorrTranscript(8, 16, 1, 7),
            model.SchnorrTranscript(8, 16, 6, 0),
        )
        self.assertIs(result.kind, model.AttemptKind.AFFIRMATIVE)
        self.assertEqual(result.value.witness, 3)
        self.assertEqual(pow(2, result.value.witness, 23), 8)

    def test_equal_challenges_do_not_meet_source_domain(self) -> None:
        source, profile, *_ = fixed_context()
        transcript = model.SchnorrTranscript(8, 16, 1, 7)
        result = model.extract_schnorr_witness(source, profile, transcript, transcript)
        self.assertIs(result.kind, model.AttemptKind.CANNOT_ANSWER)

    def test_changed_commitment_does_not_meet_source_domain(self) -> None:
        source, profile, *_ = fixed_context()
        result = model.extract_schnorr_witness(
            source,
            profile,
            model.SchnorrTranscript(8, 16, 1, 7),
            model.SchnorrTranscript(8, 8, 6, 0),
        )
        self.assertIs(result.kind, model.AttemptKind.CANNOT_ANSWER)

    def test_fixed_source_judgment_remains_conditional(self) -> None:
        judgment = fixed_source_judgment()
        self.assertIn(
            model.ASSUMED_SCHNORR_TWO_SPECIAL_SOUNDNESS,
            judgment.conditional_hypotheses,
        )
        model.require_established_judgment(judgment)

    def test_bounded_schnorr_assumption_is_not_a_shadow_theorem_schema(self) -> None:
        self.assertEqual(
            model.SCHNORR_TWO_SPECIAL_SOUNDNESS_THEOREM_ID,
            model.k1.content_id(
                "k3c.external.theorem-assumption",
                model.k1.encode_datum(
                    model._schnorr_two_special_soundness_theorem_assumption_body()
                ),
                semantic_regime=model.k1.SEMANTIC_REGIME_ID,
            ),
        )
        self.assertNotIn(
            "analysis.theorem-schema",
            {
                item.value
                for item in model.K3C_ANALYSIS_PROPERTY_PROFILE.supported_subject_kinds
            },
        )
        self.assertIn(
            "analysis.theorem-schema",
            {
                item.value
                for item in model.K3C_ANALYSIS_TRANSPORT_PROFILE.supported_subject_kinds
            },
        )


class GlobalTheoremSchemaTest(unittest.TestCase):
    def test_verified_pdf_digest_is_pinned(self) -> None:
        authority = model.afk_v2_theorem_schema().authority
        self.assertEqual(
            authority.artifact_sha256,
            "93837e2dd7c0e99ef3d06bbb4f235d9ed0dcafb8b96e56d867e7548751e9122c",
        )
        self.assertEqual(authority.artifact_media_type, "application/pdf")

    def test_statement_digest_is_independent_and_recomputable(self) -> None:
        schema = model.afk_v2_theorem_schema()
        body = model._selected_statement_template_body(
            schema.source_property_template,
            schema.target_property_template,
            schema.source_experiment_template,
            schema.target_experiment_template,
            schema.required_source_view_templates,
            schema.map_templates,
            schema.side_condition_templates,
            schema.local_operator_catalog,
            schema.transform_program_template,
            schema.conclusion_law_template,
        )
        unprofiled_digest = hashlib.sha256(model.k1.encode_datum(body)).hexdigest()
        digest = model.theorem_statement_digest(schema)
        self.assertEqual(digest, schema.authority.statement_content_sha256)
        self.assertEqual(
            digest,
            "dea40bdec3e81668fc10289aafbcbc5be9cce1b0078f1df302e7ba6e5cd2cd49",
        )
        self.assertNotEqual(digest, unprofiled_digest)
        self.assertNotEqual(digest, schema.authority.artifact_sha256)

    def test_source_profile_has_all_eleven_required_views(self) -> None:
        roles = tuple(
            item.canonical_clauses[0]
            for item in model.AFK_REQUIRED_SOURCE_VIEW_COMPONENTS
        )
        self.assertEqual(len(roles), 11)
        self.assertIn("BoundedBitStringIndexContract", roles)

    def test_prover_rerun_authority_includes_remark_two(self) -> None:
        self.assertIn("Remark-2", model.AFK_PRIMARY_SOURCE_LOCATORS)
        self.assertIn("Remark-6", model.AFK_PRIMARY_SOURCE_LOCATORS)
        self.assertIn(
            "Section-5-prose-immediately-before-Lemma-4",
            model.AFK_PRIMARY_SOURCE_LOCATORS,
        )
        self.assertEqual(
            model.afk_v2_theorem_schema().authority.exact_locators,
            model.AFK_PRIMARY_SOURCE_LOCATORS,
        )

    def test_prover_coin_resampling_contract_is_rejected(self) -> None:
        resampling_contract = model.RandomOracleCapabilityContractProfile(
            "uniform-black-box-extractor",
            "theorem-granted",
            "AFK-v2-Section-5-before-Lemma-4-and-Remark-6-govern-existing-points",
            "values-remain-in-exact-C8-random-function-codomain",
            "all-adversary-oracle-calls-count-toward-Q",
            "theorem-granted",
            "AFK-v2-Remark-6-governs-table-coupling-across-reruns",
            "resample-randomized-prover-coins-on-every-rerun",
            "AssumedTheorem-AFK-v2-Theorem-4-plus-process-correspondence",
            "symbolic-contract-not-local-transition-execution",
        )
        with self.assertRaises(model.ExperimentError):
            model.random_oracle_capability_contract_id(resampling_contract)

    def test_resampling_extractor_profile_cannot_enter_afk_execution(self) -> None:
        resampling_profile = replace(
            model.AFK_EXTRACTOR_PROFILE_BODY,
            prover_rerun_coin_law="resample-prover-coins-between-reruns",
        )
        changed = replace(
            model.afk_execution_body_profile(8),
            extractor_profile_id=model.extractor_profile_id(resampling_profile),
        )
        with self.assertRaises(model.ExperimentError):
            model.experiment_execution_body_id(changed)

    def test_global_schema_contains_no_fixed_family_anchor(self) -> None:
        representation = repr(model.afk_v2_theorem_schema()).lower()
        for forbidden in (
            "schnorr",
            "member-selector",
            "native-subject",
            "model-instantiation",
            "n0=1",
        ):
            self.assertNotIn(forbidden, representation)

    def test_global_schema_fields_are_template_only(self) -> None:
        names = {item.name for item in fields(model.FSTheoremSchema)}
        self.assertFalse(
            names
            & {
                "family_definition_id",
                "source_model_id",
                "target_model_id",
                "source_member_selector_id",
                "target_member_selector_id",
                "formula_ids",
            }
        )

    def test_source_metadata_rotates_validation_not_theorem_meaning(self) -> None:
        schema = model.afk_v2_theorem_schema()
        changed = replace(
            schema, authority=replace(schema.authority, artifact_sha256="0" * 64)
        )
        self.assertEqual(
            model.fs_theorem_schema_id(changed),
            model.fs_theorem_schema_id(schema),
        )
        self.assertEqual(
            model.theorem_truth_goal_id(changed),
            model.theorem_truth_goal_id(schema),
        )
        self.assertEqual(
            model.theorem_truth_proposition_id(changed),
            model.theorem_truth_proposition_id(schema),
        )
        self.assertNotEqual(
            model.theorem_source_validation_id(changed),
            model.theorem_source_validation_id(schema),
        )
        with self.assertRaises(model.TheoremError):
            model.assume_afk_theorem_truth(changed)

    def test_forged_statement_digest_is_rejected_without_rotating_meaning(self) -> None:
        schema = model.afk_v2_theorem_schema()
        forged = replace(
            schema,
            authority=replace(
                schema.authority,
                statement_content_sha256="0" * 64,
            ),
        )
        self.assertEqual(
            model.fs_theorem_schema_id(forged),
            model.fs_theorem_schema_id(schema),
        )
        self.assertEqual(
            model.theorem_statement_digest(forged),
            model.theorem_statement_digest(schema),
        )
        self.assertEqual(
            model.theorem_truth_goal_id(forged),
            model.theorem_truth_goal_id(schema),
        )
        with self.assertRaisesRegex(model.TheoremError, "statement digest"):
            model.theorem_source_validation_id(forged)
        with self.assertRaises(model.TheoremError):
            model.assume_afk_theorem_truth(forged)

    def test_forged_proof_status_is_rejected_without_rotating_meaning(self) -> None:
        schema = model.afk_v2_theorem_schema()
        forged = replace(
            schema,
            proof_status=replace(
                schema.proof_status,
                canonical_clauses=(
                    *schema.proof_status.canonical_clauses[:-1],
                    "schema-admission-establishes-truth",
                ),
            ),
        )
        self.assertEqual(
            model.fs_theorem_schema_id(forged),
            model.fs_theorem_schema_id(schema),
        )
        self.assertEqual(
            model.theorem_statement_digest(forged),
            model.theorem_statement_digest(schema),
        )
        with self.assertRaisesRegex(model.TheoremError, "proof status"):
            model.theorem_source_validation_id(forged)
        with self.assertRaises(model.TheoremError):
            model.assume_afk_theorem_truth(forged)

    def test_theorem_truth_question_is_exactly_source_free(self) -> None:
        body = model.theorem_truth_question_body(model.afk_v2_theorem_schema())
        reason = model.analysis_profile_declaration_ref(
            model.K3C_ANALYSIS_TRANSPORT_PROFILE,
            model.K3C_ANALYSIS_PROPERTY_PROFILE,
            "analysis.semantic-law",
            "source-free-premise-reason",
        )
        self.assertEqual(
            body.context,
            model.k1.DatumVariant(
                0,
                model.analysis_profile_declaration_ref_body(reason),
            ),
        )

    def test_theorem_truth_goal_identity_is_question_only(self) -> None:
        schema = model.afk_v2_theorem_schema()
        question_id = model._analysis_transport_id(
            "analysis.question",
            model.theorem_truth_question_body(schema),
        )
        self.assertEqual(
            model.theorem_truth_goal_id(schema),
            model._analysis_transport_id(
                "analysis.goal",
                model.AnalysisGoalBodyV0(question_id),
            ),
        )

    def test_statement_component_outside_closed_catalog_is_refused(self) -> None:
        schema = model.afk_v2_theorem_schema()
        changed_component = replace(
            schema.source_property_template,
            canonical_clauses=("different-source-property",),
        )
        changed = replace(schema, source_property_template=changed_component)
        with self.assertRaisesRegex(model.TheoremError, "closed transport catalog"):
            model.fs_theorem_schema_id(changed)
        with self.assertRaisesRegex(model.TheoremError, "closed transport catalog"):
            model.theorem_source_validation_id(changed)

    def test_missing_source_view_is_rejected(self) -> None:
        schema = model.afk_v2_theorem_schema()
        with self.assertRaises(model.TheoremError):
            model.fs_theorem_schema_id(
                replace(
                    schema,
                    required_source_view_templates=schema.required_source_view_templates[
                        :-1
                    ],
                )
            )

    def test_operator_reordering_is_rejected(self) -> None:
        schema = model.afk_v2_theorem_schema()
        with self.assertRaises(model.TheoremError):
            model.fs_theorem_schema_id(
                replace(
                    schema,
                    local_operator_catalog=tuple(
                        reversed(schema.local_operator_catalog)
                    ),
                )
            )

    def test_operator_arity_mutation_is_rejected(self) -> None:
        schema = model.afk_v2_theorem_schema()
        operators = list(schema.local_operator_catalog)
        operators[1] = replace(operators[1], operand_sorts=("Probability",))
        with self.assertRaises(model.TheoremError):
            model.fs_theorem_schema_id(
                replace(schema, local_operator_catalog=tuple(operators))
            )

    def test_family_operator_declared_sorts_are_checked(self) -> None:
        binding = model.family_operator_bindings(model.SELECTED_AFK_FAMILY)[1]
        with self.assertRaises(model.TheoremError):
            model.family_operator_binding_id(
                replace(binding, result_sort="Probability")
            )
        with self.assertRaises(model.TheoremError):
            model.family_operator_binding_id(
                replace(binding, parameter_sorts=("Zed:Nonsense",))
            )

    def test_closed_operator_grammar_rejects_cycles_and_huge_literals(self) -> None:
        huge = model.LocalOperatorTemplate(
            3,
            ("LocalQueryCount(0)",),
            "ExpectedCount(LocalAdversaryInvocation(1))",
            "expected-count(Q+99999999999999999999)",
        )
        with self.assertRaises(model.TheoremError):
            model._parse_local_operator_template(huge, 8)
        cyclic = model.LocalOperatorTemplate(
            0,
            ("Probability",),
            "SignedProbabilityLowerBound",
            "divide((epsilon-operator0(Q,N)),qKS(n))",
        )
        with patch.object(model, "AFK_LOCAL_OPERATOR_CATALOG", (cyclic,)):
            with self.assertRaises(model.TheoremError):
                model._parse_local_operator_template(cyclic, 8)

    def test_extractor_contract_carries_its_exact_codomain(self) -> None:
        n8 = model.afk_extractor_ro_capability_contract_id(8)
        n11 = model.afk_extractor_ro_capability_contract_id(11)
        self.assertNotEqual(n8, n11)
        body = model.afk_extractor_experiment_body_profile(11)
        self.assertEqual(body.random_function_process.capability_contract_id, n11)
        model.single_experiment_body_id(body)

    def test_operator_ast_outside_closed_catalog_is_refused(self) -> None:
        schema = model.afk_v2_theorem_schema()
        operators = list(schema.local_operator_catalog)
        operators[3] = replace(operators[3], template_ast="expected-count(Q+1)")
        changed = replace(schema, local_operator_catalog=tuple(operators))
        with self.assertRaisesRegex(model.TheoremError, "closed AFK catalog"):
            model.fs_theorem_schema_id(changed)

    def test_schema_admission_is_not_theorem_truth(self) -> None:
        schema = model.afk_v2_theorem_schema()
        self.assertNotIn(model.ASSUMED_AFK_V2_THM4, tuple(schema.__dict__.values()))
        self.assertEqual(model.assume_afk_theorem_truth(schema).treatment, "Assumed")


class FamilyApplicabilityTest(unittest.TestCase):
    def test_family_and_applicability_goal_identities_are_question_only(self) -> None:
        family = model.SELECTED_AFK_FAMILY
        schema = model.afk_v2_theorem_schema()
        candidate = model.derive_family_applicability_input(schema, family)
        for role in (
            "source-two-special-soundness",
            "target-adaptive-knowledge-q-lt-N",
        ):
            with self.subTest(role=role):
                question_id = model.family_question_id(family, role)
                self.assertEqual(
                    model.family_goal_id(family, role),
                    model._analysis_transport_id(
                        "analysis.goal",
                        model.AnalysisGoalBodyV0(question_id),
                    ),
                )
        applicability_question_id = model.family_applicability_question_id(
            family,
            candidate,
        )
        self.assertEqual(
            model.family_applicability_goal_id(family, candidate),
            model._analysis_transport_id(
                "analysis.goal",
                model.AnalysisGoalBodyV0(applicability_question_id),
            ),
        )

    def test_attempt_taxonomy_matches_qualified_analysis_outcomes(self) -> None:
        self.assertEqual(
            {item.value for item in model.AttemptKind},
            {
                "affirmative",
                "negative",
                "unsupported",
                "cannot-answer",
                "refused",
                "malformed",
                "deterministic-limit-exceeded",
                "checker-failure",
            },
        )

    def test_selected_family_keeps_N_constant_across_n(self) -> None:
        family = model.SELECTED_AFK_FAMILY
        self.assertEqual(family.challenge_cardinality, 8)
        self.assertEqual(
            family.challenge_cardinality_law, "one-fixed-N-for-all-logical-n"
        )

    def test_varying_N_across_n_is_malformed(self) -> None:
        family = model.SELECTED_AFK_FAMILY
        with self.assertRaises(model.TheoremError):
            model.family_definition_id(
                replace(family, challenge_cardinality_law="N-is-a-function-of-n")
            )

    def test_ro_index_carrier_must_be_finite_bounded_bitstrings(self) -> None:
        family = model.SELECTED_AFK_FAMILY
        with self.assertRaises(model.TheoremError):
            model.family_definition_id(
                replace(
                    family,
                    ro_index_domain=replace(
                        family.ro_index_domain, carrier="canonical-bytes"
                    ),
                )
            )

    def test_family_operator_catalog_has_exact_four_roles(self) -> None:
        bindings = model.family_operator_bindings(model.SELECTED_AFK_FAMILY)
        self.assertEqual(tuple(item.local_ordinal for item in bindings), (0, 1, 2, 3))
        self.assertEqual(len({item.formula_id for item in bindings}), 4)

    def test_exact_family_applicability_is_affirmative(self) -> None:
        port = family_context()[4]
        model.require_family_applicability_port(port)
        self.assertEqual(port.purpose, "afk-family-property-transport-only")

    def test_malformed_support_returns_typed_outcome(self) -> None:
        schema, family = family_context()[:2]
        result = model.check_afk_family_applicability(
            schema,
            family,
            (model.fixture_ref("analysis.proposition", "not-a-hypothesis"),),
        )
        self.assertIs(result.kind, model.AttemptKind.MALFORMED)

    def test_missing_each_applicability_premise_cannot_answer(self) -> None:
        schema, family, candidate, premises, *_ = family_context()
        for missing in premises:
            with self.subTest(missing=missing.internal_reference().hex()[-8:]):
                result = model.check_afk_family_applicability(
                    schema,
                    family,
                    tuple(item for item in premises if item != missing),
                    candidate=candidate,
                )
                self.assertIs(result.kind, model.AttemptKind.CANNOT_ANSWER)

    def test_theorem_truth_is_refused_as_applicability_evidence(self) -> None:
        schema, family, candidate, premises, *_ = family_context()
        result = model.check_afk_family_applicability(
            schema,
            family,
            (*premises, model.ASSUMED_AFK_V2_THM4),
            candidate=candidate,
        )
        self.assertIs(result.kind, model.AttemptKind.REFUSED)

    def test_extra_applicability_evidence_is_refused(self) -> None:
        schema, family, candidate, premises, *_ = family_context()
        result = model.check_afk_family_applicability(
            schema,
            family,
            (*premises, model.fixture_hypothesis("unrequested")),
            candidate=candidate,
        )
        self.assertIs(result.kind, model.AttemptKind.REFUSED)

    def test_wrong_source_goal_is_refused_as_false_applicability(self) -> None:
        schema, family, candidate, premises, *_ = family_context()
        changed = replace(
            candidate,
            source_property_goal_id=model.fixture_ref(
                "analysis.goal", "wrong-family-source"
            ),
        )
        result = model.check_afk_family_applicability(
            schema, family, premises, candidate=changed
        )
        self.assertIs(result.kind, model.AttemptKind.REFUSED)

    def test_q_equals_two_substitution_is_refused(self) -> None:
        schema, family, candidate, premises, *_ = family_context()
        substitution = replace(
            candidate.parameter_substitution,
            positive_polynomial_id=model.positive_polynomial_id(
                model.AFK_POSITIVE_POLYNOMIAL_PROFILE_ID,
                (2,),
            ),
        )
        result = model.check_afk_family_applicability(
            schema,
            family,
            premises,
            candidate=replace(candidate, parameter_substitution=substitution),
        )
        self.assertIs(result.kind, model.AttemptKind.REFUSED)

    def test_ro_index_domain_identity_mismatch_is_refused(self) -> None:
        schema, family, candidate, premises, *_ = family_context()
        substitution = replace(
            candidate.parameter_substitution,
            ro_index_domain_id=model.fixture_ref(
                "analysis.family-ro-index-domain", "wrong-domain"
            ),
        )
        result = model.check_afk_family_applicability(
            schema,
            family,
            premises,
            candidate=replace(candidate, parameter_substitution=substitution),
        )
        self.assertIs(result.kind, model.AttemptKind.REFUSED)

    def test_formula_binding_mutation_is_refused(self) -> None:
        schema, family, candidate, premises, *_ = family_context()
        bindings = list(candidate.operator_bindings)
        bindings[0] = replace(
            bindings[0],
            formula_id=model.fixture_ref(
                "analysis.quantitative-formula", "wrong-kappa"
            ),
        )
        result = model.check_afk_family_applicability(
            schema,
            family,
            premises,
            candidate=replace(candidate, operator_bindings=tuple(bindings)),
        )
        self.assertIs(result.kind, model.AttemptKind.REFUSED)

    def test_second_constant_N_family_does_not_rotate_global_theorem(self) -> None:
        schema = model.afk_v2_theorem_schema()
        other = model.form_afk_asymptotic_family(
            "constant-N16-family", challenge_cardinality=16
        )
        result = model.check_afk_family_applicability(
            schema, other, model.family_applicability_premise_ids(other)
        )
        self.assertIs(result.kind, model.AttemptKind.AFFIRMATIVE)
        self.assertEqual(
            result.value.theorem_schema_id, model.fs_theorem_schema_id(schema)
        )


class FamilyTransportTest(unittest.TestCase):
    def test_live_reissuance_does_not_rotate_inert_applicability_identity(self) -> None:
        schema, family, candidate, premises, first, *_ = family_context()
        second_outcome = model.check_afk_family_applicability(
            schema, family, premises, candidate=candidate
        )
        self.assertIs(second_outcome.kind, model.AttemptKind.AFFIRMATIVE)
        second = second_outcome.value
        self.assertEqual(first.checked_result, second.checked_result)
        self.assertEqual(first.authority_binding, second.authority_binding)
        self.assertEqual(first.port_id, second.port_id)
        self.assertIsNot(first.live_capability._token, second.live_capability._token)

    def test_live_reissuance_does_not_rotate_family_judgment_identity(self) -> None:
        schema, family, candidate, premises, first_port, _, _, first = family_context()
        second_port = model.check_afk_family_applicability(
            schema, family, premises, candidate=candidate
        ).value
        source = model.assume_external_family_source_capability_for_fixture(
            family, authority_label="test-assumed-all-n-source-authority"
        )
        truth = model.assume_afk_theorem_truth(schema)
        second_outcome = model.transport_afk_family_knowledge(
            source, second_port, truth
        )
        self.assertIs(second_outcome.kind, model.AttemptKind.AFFIRMATIVE)
        second = second_outcome.value
        self.assertEqual(first.judgment, second.judgment)
        self.assertEqual(first.checked_result, second.checked_result)
        self.assertEqual(first.authority_binding, second.authority_binding)
        self.assertEqual(first_port.checked_result, second_port.checked_result)
        self.assertIsNot(first.live_capability._token, second.live_capability._token)

    def test_transport_policy_closure_is_derived_from_exact_used_bindings(self) -> None:
        port, source, truth, capability = family_context()[4:8]
        expected = model.derive_source_policy_closure(
            (
                port.authority_binding,
                source.authority_binding,
                truth.authority_binding,
            )
        )
        self.assertEqual(capability.authority_binding.transitive_policy_ids, expected)
        self.assertNotIn(
            "source_policy_closure",
            {item.name for item in fields(type(capability.judgment))},
        )

    def test_derived_policy_closure_is_a_set_union(self) -> None:
        binding = family_context()[4].authority_binding
        self.assertEqual(
            model.derive_source_policy_closure((binding,)),
            model.derive_source_policy_closure((binding, binding)),
        )

    def test_policy_closure_is_embedded_as_a_canonical_sequence(self) -> None:
        capability = family_context()[-1]
        judgment = capability.judgment
        bindings = (
            judgment.applicability_authority_binding,
            judgment.source_authority_binding,
            judgment.theorem_truth_authority_binding,
        )
        closure = model.derive_source_policy_closure(bindings)
        operator_binding_ids = tuple(
            model.family_operator_binding_id(binding)
            for binding in judgment.operator_bindings
        )
        self.assertEqual(
            judgment.judgment_id,
            model._family_judgment_id(
                judgment.theorem_schema_id,
                judgment.family_definition_id,
                operator_binding_ids,
                judgment.target_proposition_id,
                judgment.semantic_basis_id,
                capability.checked_result.support_id,
                judgment.validation_basis_id,
                capability.authority_binding.immediate_policy_ids[0],
                judgment.retained_hypotheses,
                closure,
            ),
        )
        self.assertGreater(len(closure), 1)
        with self.assertRaisesRegex(model.AuthorityError, "not canonical"):
            model._family_judgment_id(
                judgment.theorem_schema_id,
                judgment.family_definition_id,
                operator_binding_ids,
                judgment.target_proposition_id,
                judgment.semantic_basis_id,
                capability.checked_result.support_id,
                judgment.validation_basis_id,
                capability.authority_binding.immediate_policy_ids[0],
                judgment.retained_hypotheses,
                tuple(reversed(closure)),
            )
        self.assertNotIn(
            "analysis.source-policy-closure",
            model.ANALYSIS_SUBJECT_KINDS,
        )
        self.assertFalse(hasattr(model, "source_policy_closure_id"))

    def test_analysis_and_external_owner_policies_do_not_collapse(self) -> None:
        port, source = family_context()[4:6]
        analysis_policy = port.authority_binding.immediate_policy_ids[0]
        external_policy = source.authority_binding.immediate_policy_ids[0]
        self.assertEqual(analysis_policy.subject_kind, "analysis.operation-policy")
        self.assertEqual(
            external_policy.subject_kind,
            "k3c.external-owner-operation-policy",
        )
        self.assertEqual(
            analysis_policy,
            model._analysis_operation_policy_id(
                port.checked_result.proposition_id,
                (
                    (
                        "afk-family-property-transport",
                        ("exact-family-applicability",),
                    ),
                ),
                profile=model.K3C_ANALYSIS_TRANSPORT_PROFILE,
            ),
        )
        self.assertEqual(
            external_policy,
            model._assumed_external_operation_policy_id(
                source.external_authority_id,
                "use-assumed-all-n-source-result",
            ),
        )
        self.assertNotEqual(
            external_policy,
            model._analysis_operation_policy_id(
                source.checked_result.proposition_id,
                (
                    (
                        "afk-family-property-transport",
                        ("all-n-two-special-soundness-source",),
                    ),
                ),
                profile=model.K3C_ANALYSIS_TRANSPORT_PROFILE,
            ),
        )
        with self.assertRaisesRegex(
            model.AnalysisError,
            "does not support subject kind",
        ):
            model._analysis_transport_id(
                "analysis.owner-policy-disposition",
                self.probe_policy_body(),
            )

    @staticmethod
    def probe_policy_body() -> object:
        return model.k1.DatumRecord(
            ((0, model.k1.Symbol("forbidden-shadow-policy-kind")),)
        )

    def test_analysis_minted_external_policy_forgery_is_refused(self) -> None:
        family = model.SELECTED_AFK_FAMILY
        source = family_context()[5]
        forged_policy = model._analysis_operation_policy_id(
            source.checked_result.proposition_id,
            (
                (
                    "afk-family-property-transport",
                    ("all-n-two-special-soundness-source",),
                ),
            ),
            profile=model.K3C_ANALYSIS_TRANSPORT_PROFILE,
        )
        forged_binding = replace(
            source.authority_binding,
            immediate_policy_ids=(forged_policy,),
        )
        forged = replace(source, authority_binding=forged_binding)
        with self.assertRaisesRegex(
            model.AuthorityError,
            "identity or support was substituted",
        ):
            model.require_family_source_capability(family, forged)

    def test_analysis_contract_is_wrapped_by_the_single_k1_envelope(self) -> None:
        binding = family_context()[4].authority_binding
        self.assertIs(type(binding), model.AnalysisSourceAuthorityContract)
        envelope = model.k1_portable_source_authority_binding(binding)
        self.assertIs(type(envelope), model.k1.PortableSourceAuthorityBinding)
        self.assertIs(
            type(envelope.capability_requirement),
            model.k1.OwnerCapabilityRequirement,
        )
        self.assertEqual(
            envelope.capability_requirement.owner_requirement,
            model.analysis_capability_requirement_payload_id(
                binding.capability_requirement
            ),
        )
        self.assertEqual(
            model.portable_source_authority_binding_id(binding),
            model._form_analysis_profiled_content_id(
                "analysis.portable-source-authority-binding",
                model.AnalysisPortableSourceAuthorityBindingBodyV0(envelope),
                binding.semantic_profile,
            ),
        )
        self.assertFalse(hasattr(model, "OwnerCapabilityRequirement"))
        self.assertFalse(hasattr(model, "PortableSourceAuthorityBinding"))
        self.assertFalse(
            {item.name for item in fields(type(envelope))}
            & {"live_capability", "_token", "checker", "provider", "occurrence"}
        )

    def test_family_judgment_carries_only_inert_authority_coordinates(self) -> None:
        names = {item.name for item in fields(model.AFKFamilyKnowledgeJudgment)}
        self.assertFalse(
            names
            & {
                "live_capability",
                "applicability_port",
                "source_capability",
                "theorem_truth",
                "_issuer",
                "checker",
                "provider",
                "occurrence",
            }
        )
        self.assertTrue(
            {
                "applicability_checked_result",
                "applicability_authority_binding",
                "source_checked_result",
                "source_authority_binding",
                "theorem_truth_checked_result",
                "theorem_truth_authority_binding",
            }
            <= names
        )

    def test_inert_judgment_revalidation_does_not_issue_live_capabilities(self) -> None:
        judgment = family_context()[-1].judgment
        counts_before = (
            len(model._FAMILY_PORT_TOKENS),
            len(model._EXTERNAL_SOURCE_CAP_TOKENS),
            len(model._TRUTH_TREATMENT_TOKENS),
            len(model._FAMILY_JUDGMENT_TOKENS),
        )
        model.require_family_knowledge_judgment(judgment)
        counts_after = (
            len(model._FAMILY_PORT_TOKENS),
            len(model._EXTERNAL_SOURCE_CAP_TOKENS),
            len(model._TRUTH_TREATMENT_TOKENS),
            len(model._FAMILY_JUDGMENT_TOKENS),
        )
        self.assertEqual(counts_before, counts_after)

    def test_forged_live_applicability_token_is_refused(self) -> None:
        port, source, truth = family_context()[4:7]
        forged = replace(
            port,
            live_capability=replace(port.live_capability, _token=object()),
        )
        result = model.transport_afk_family_knowledge(source, forged, truth)
        self.assertIs(result.kind, model.AttemptKind.REFUSED)

    def test_reconstructed_invocation_capability_is_not_live_authority(self) -> None:
        port, source, truth = family_context()[4:7]
        reconstructed = replace(port.live_capability)
        self.assertEqual(reconstructed, port.live_capability)
        self.assertIsNot(reconstructed, port.live_capability)
        result = model.transport_afk_family_knowledge(
            source,
            replace(port, live_capability=reconstructed),
            truth,
        )
        self.assertIs(result.kind, model.AttemptKind.REFUSED)

    def test_reconstructed_k1_source_binding_is_not_live_authority(self) -> None:
        port, source, truth = family_context()[4:7]
        reconstructed = replace(port.live_capability.source_binding)
        self.assertEqual(reconstructed, port.live_capability.source_binding)
        self.assertIsNot(reconstructed, port.live_capability.source_binding)
        forged = replace(
            port,
            live_capability=replace(
                port.live_capability,
                source_binding=reconstructed,
            ),
        )
        result = model.transport_afk_family_knowledge(source, forged, truth)
        self.assertIs(result.kind, model.AttemptKind.REFUSED)

    def test_cross_family_live_capability_is_refused(self) -> None:
        port, source, truth = family_context()[4:7]
        forged = replace(
            port,
            live_capability=replace(
                port.live_capability,
                capability_family=model.k1.Symbol("different-capability-family"),
            ),
        )
        result = model.transport_afk_family_knowledge(source, forged, truth)
        self.assertIs(result.kind, model.AttemptKind.REFUSED)

    def test_cross_purpose_live_capability_is_refused(self) -> None:
        port, source, truth = family_context()[4:7]
        forged = replace(
            port,
            live_capability=replace(
                port.live_capability,
                typed_purpose_id=model.fixture_ref(
                    "analysis.use-purpose", "different-live-purpose"
                ),
            ),
        )
        result = model.transport_afk_family_knowledge(source, forged, truth)
        self.assertIs(result.kind, model.AttemptKind.REFUSED)

    def test_detached_inert_authority_binding_is_refused(self) -> None:
        port, source, truth = family_context()[4:7]
        forged = replace(
            source,
            authority_binding=replace(
                source.authority_binding,
                owner_id=model.fixture_ref(
                    "k3c.external-proof-authority", "detached-owner"
                ),
            ),
        )
        result = model.transport_afk_family_knowledge(forged, port, truth)
        self.assertIs(result.kind, model.AttemptKind.REFUSED)

    def test_missing_all_n_source_capability_cannot_answer(self) -> None:
        port, truth = family_context()[4], family_context()[6]
        self.assertIs(
            model.transport_afk_family_knowledge(None, port, truth).kind,
            model.AttemptKind.CANNOT_ANSWER,
        )

    def test_fixed_n0_source_judgment_is_refused_for_family_slot(self) -> None:
        port, truth = family_context()[4], family_context()[6]
        result = model.transport_afk_family_knowledge(
            fixed_source_judgment(), port, truth
        )
        self.assertIs(result.kind, model.AttemptKind.REFUSED)

    def test_missing_theorem_truth_cannot_answer(self) -> None:
        port, source_capability = family_context()[4:6]
        result = model.transport_afk_family_knowledge(source_capability, port, None)
        self.assertIs(result.kind, model.AttemptKind.CANNOT_ANSWER)

    def test_source_capability_for_other_family_is_refused(self) -> None:
        port, truth = family_context()[4], family_context()[6]
        other = model.form_afk_asymptotic_family("other-family-N8")
        capability = model.assume_external_family_source_capability_for_fixture(
            other, authority_label="test-other-family-source-authority"
        )
        result = model.transport_afk_family_knowledge(capability, port, truth)
        self.assertIs(result.kind, model.AttemptKind.REFUSED)

    def test_forged_theorem_truth_support_is_refused(self) -> None:
        port, source_capability, truth = family_context()[4:7]
        changed = replace(
            truth,
            checked_result=replace(
                truth.checked_result,
                support_id=model.fixture_ref(
                    "analysis.support-instantiation", "forged-theorem-truth"
                ),
            ),
        )
        result = model.transport_afk_family_knowledge(source_capability, port, changed)
        self.assertIs(result.kind, model.AttemptKind.REFUSED)

    def test_forged_all_n_source_support_is_refused(self) -> None:
        port, source_capability, truth = family_context()[4:7]
        changed = replace(
            source_capability,
            checked_result=replace(
                source_capability.checked_result,
                support_id=model.fixture_ref(
                    "analysis.support-instantiation", "forged-family-source"
                ),
            ),
        )
        result = model.transport_afk_family_knowledge(changed, port, truth)
        self.assertIs(result.kind, model.AttemptKind.REFUSED)

    def test_positive_transport_retains_both_external_assumptions(self) -> None:
        source_capability, truth, capability = family_context()[5:8]
        judgment = capability.judgment
        for source_hypothesis in source_capability.retained_hypotheses:
            self.assertIn(source_hypothesis, judgment.retained_hypotheses)
        self.assertIn(truth.retained_hypothesis_id, judgment.retained_hypotheses)
        model.require_family_knowledge_capability(capability)
        model.require_family_knowledge_judgment(judgment)

    def test_revalidated_judgment_cannot_drop_all_n_source_premise(self) -> None:
        source_capability = family_context()[5]
        judgment = family_context()[-1].judgment
        changed = replace(
            judgment,
            retained_hypotheses=tuple(
                item
                for item in judgment.retained_hypotheses
                if item != source_capability.retained_hypotheses[0]
            ),
        )
        with self.assertRaises(model.TheoremError):
            model.require_family_knowledge_judgment(changed)

    def test_revalidated_judgment_cannot_swap_truth_support(self) -> None:
        judgment = family_context()[-1].judgment
        changed = replace(
            judgment,
            theorem_truth_checked_result=replace(
                judgment.theorem_truth_checked_result,
                support_id=judgment.applicability_checked_result.support_id,
            ),
        )
        with self.assertRaises(model.TheoremError):
            model.require_family_knowledge_judgment(changed)

    def test_revalidated_judgment_cannot_float_to_another_family(self) -> None:
        judgment = family_context()[-1].judgment
        other = model.form_afk_asymptotic_family(
            "floating-N16-family", challenge_cardinality=16
        )
        changed = replace(
            judgment,
            family=other,
            family_definition_id=model.family_definition_id(other),
            target_proposition_id=model.family_target_property_proposition_id(other),
            operator_bindings=model.family_operator_bindings(other),
        )
        with self.assertRaises(model.AuthorityError):
            model.require_family_knowledge_judgment(changed)

    def test_family_judgment_has_no_native_member_coordinates(self) -> None:
        judgment = family_context()[-1].judgment
        names = {item.name for item in fields(type(judgment))}
        self.assertFalse(
            names
            & {
                "source_member_selector_id",
                "target_member_selector_id",
                "native_subject_projection_id",
                "logical_index",
            }
        )

    def test_active_question_goal_proposition_layers_are_distinct(self) -> None:
        proposition = fixed_source_judgment().proposition
        question_id = model.analysis_question_id(proposition.goal.question)
        goal_id = model.analysis_goal_id(proposition.goal)
        proposition_id = model.analysis_proposition_id(proposition)
        extra = model.fixture_hypothesis("question-goal-proposition-split")
        changed = replace(
            proposition,
            hypotheses=model.hypothesis_union(proposition.hypotheses, (extra,)),
        )
        self.assertEqual(question_id, model.analysis_question_id(changed.goal.question))
        self.assertEqual(goal_id, model.analysis_goal_id(changed.goal))
        self.assertNotEqual(proposition_id, model.analysis_proposition_id(changed))
        self.assertNotEqual(
            model.analysis_hypothesis_context_id(proposition.hypotheses),
            model.analysis_hypothesis_context_id(changed.hypotheses),
        )

    def test_goal_identity_is_exactly_its_authenticated_question(self) -> None:
        goal = fixed_source_judgment().proposition.goal
        question_id = model.analysis_question_id(goal.question)
        self.assertEqual(
            model.analysis_goal_id(goal),
            model._analysis_id(
                "analysis.goal",
                model.AnalysisGoalBodyV0(question_id),
            ),
        )

    def test_goal_refuses_conclusion_substitution_after_question_formation(
        self,
    ) -> None:
        goal = fixed_source_judgment().proposition.goal
        changed = replace(
            goal,
            conclusion=replace(
                goal.conclusion,
                extractor_algorithm_id=model.fixture_ref(
                    "analysis.extractor-algorithm", "substituted-goal-conclusion"
                ),
            ),
        )
        self.assertEqual(
            model.analysis_question_id(goal.question),
            model.analysis_question_id(changed.question),
        )
        with self.assertRaises(model.PropertyError):
            model.analysis_goal_id(changed)

    def test_goal_reconstruction_is_pure_and_order_independent(self) -> None:
        goal = fixed_source_judgment().proposition.goal
        self.assertFalse(hasattr(model, "_QUESTION_CONCLUSION_REGISTRY"))
        reconstructed = model.hypothesis_free_conclusion(replace(goal.question))
        self.assertEqual(reconstructed, goal.conclusion)
        self.assertEqual(
            model.analysis_goal_id(replace(goal, question=replace(goal.question))),
            model.analysis_goal_id(goal),
        )

    def test_conflicting_family_payload_changes_question_and_cannot_poison_goal(
        self,
    ) -> None:
        goal = fixed_source_judgment().proposition.goal
        changed_question = replace(
            goal.question,
            family_payload=replace(
                goal.question.family_payload,
                extractor_algorithm_id=model.k1.authenticate_algorithm_identity(
                    model.k1.build_unsupported_algorithm()
                ),
            ),
        )
        self.assertNotEqual(
            model.analysis_question_id(changed_question),
            model.analysis_question_id(goal.question),
        )
        with self.assertRaises(model.PropertyError):
            model.analysis_goal_id(replace(goal, question=changed_question))
        self.assertEqual(
            model.analysis_goal_id(goal), model.analysis_goal_id(replace(goal))
        )

    def test_family_question_goal_proposition_profiles_do_not_collapse(self) -> None:
        family = model.SELECTED_AFK_FAMILY
        candidate = family_context()[2]
        coordinates = {
            model.family_source_property_proposition_id(family),
            model.family_target_property_proposition_id(family),
            model.family_applicability_proposition_id(family, candidate),
        }
        self.assertEqual(len(coordinates), 3)


class PointwiseSpecializationTest(unittest.TestCase):
    def test_fixed_setup_is_paired_owner_view_coordinates_only(self) -> None:
        source, _, _, _, correspondence, *_ = fixed_context()
        setup = correspondence.fixed_public_setup
        names = {item.name for item in fields(model.FixedPublicSetup)}
        self.assertEqual(
            names,
            {
                "core_id",
                "construction_id",
                "fresh_protocol_id",
                "fiat_shamir_protocol_id",
                "fresh_public_setup_view_id",
                "fiat_shamir_public_setup_view_id",
                "relation_definition_id",
                "_source_views",
                "_source",
            },
        )
        self.assertEqual(
            setup.relation_definition_id,
            model.k3.schnorr_relation_definition_id(source.case.definition_sources[0]),
        )
        self.assertEqual(
            setup.relation_definition_id,
            setup._source_views.relation_definition.view.coordinate.definition_id,
        )
        self.assertEqual(
            setup._source_views.fresh_public_setup.view.entries,
            setup._source_views.fiat_shamir_public_setup.view.entries,
        )
        self.assertEqual(setup.core_id, source.protocol_source.core_id)
        self.assertEqual(
            (setup.group_generator, setup.subgroup_order, setup.group_modulus),
            (2, 11, 23),
        )
        self.assertEqual(
            (
                setup.fixed_before_prover_and_oracle,
                setup.adversary_selected,
                setup.oracle_correlated,
                setup.mutable_within_instance,
            ),
            (True, False, False, False),
        )

    def test_reconstructed_public_setup_bearer_is_refused(self) -> None:
        correspondence = fixed_context()[4]
        setup = correspondence.fixed_public_setup
        issued = setup._source_views.fresh_public_setup
        reconstructed = model.k2.IssuedPublicSetupInvocationView(
            issued.view_id,
            issued.view,
            issued.source_binding,
            issued.capability,
            issued._issuer,
        )
        forged_views = replace(
            setup._source_views,
            fresh_public_setup=reconstructed,
        )
        with self.assertRaises(model.AuthorityError):
            model.fixed_public_setup_id(replace(setup, _source_views=forged_views))

    def test_cross_axis_execution_view_is_refused(self) -> None:
        correspondence = fixed_context()[4]
        setup = correspondence.fixed_public_setup
        forged_views = replace(
            setup._source_views,
            fiat_shamir_execution=setup._source_views.fresh_execution,
        )
        with self.assertRaises(model.AuthorityError):
            model.fixed_public_setup_id(replace(setup, _source_views=forged_views))

    def test_unequal_fresh_fs_public_setup_entries_are_refused(self) -> None:
        source, _, _, _, correspondence, *_ = fixed_context()
        setup = correspondence.fixed_public_setup
        values = dict(source.case.invocation.values)
        values["session"] = b"different-public-session"
        outcome = model.k2.issue_public_setup_invocation_view(
            source.case.core,
            source.case.construction,
            model.k2.ChallengeInterpretation.FIAT_SHAMIR,
            model.k2.Invocation(MappingProxyType(values)),
            consumer_id=model._k3c_pir_view_consumer_id(),
            purpose_id=model._k3c_pir_view_purpose_id(
                "fiat-shamir", "public-setup-invocation-view"
            ),
        )
        self.assertIs(
            outcome.kind,
            model.k2.QualifiedViewOutcomeKind.AFFIRMATIVE,
        )
        forged_views = replace(
            setup._source_views,
            fiat_shamir_public_setup=outcome.value,
        )
        with self.assertRaises(model.SourceIngressError):
            model.fixed_public_setup_id(
                replace(
                    setup,
                    fiat_shamir_public_setup_view_id=outcome.value.view_id,
                    _source_views=forged_views,
                )
            )

    def test_reissuance_changes_live_views_not_semantic_identity(self) -> None:
        source, _, source_model, target_model, correspondence, *_ = fixed_context()
        reissued = model.derive_fs_correspondence(
            source,
            source_model,
            target_model,
        )
        self.assertEqual(
            model.fs_correspondence_id(reissued),
            model.fs_correspondence_id(correspondence),
        )
        self.assertIsNot(
            reissued._pir_source_views.fresh_execution,
            correspondence._pir_source_views.fresh_execution,
        )

    def test_fresh_fs_relation_and_plan_axes_are_not_substitutable(self) -> None:
        correspondence = fixed_context()[4]
        substitutions = (
            (
                "fiat_shamir_binding_id",
                model.fixture_ref(
                    "relations.protocol-binding",
                    "substituted-fs-relation-binding",
                ),
            ),
            (
                "fiat_shamir_plan_binding_id",
                model.fixture_ref(
                    "relations.plan-witness-binding",
                    "substituted-fs-plan-binding",
                ),
            ),
            (
                "fiat_shamir_execution_view_binding_id",
                correspondence.fresh_execution_view_binding_id,
            ),
        )
        for field_name, value in substitutions:
            with self.subTest(field_name=field_name):
                with self.assertRaises(model.TheoremError):
                    model.fs_correspondence_id(
                        replace(correspondence, **{field_name: value})
                    )

    def test_exact_correspondence_is_issued(self) -> None:
        capability = fixed_context()[-1]
        model.require_concrete_family_instance_correspondence(capability)
        self.assertEqual(
            (capability.logical_index, capability.native_statement_length), (1, 1)
        )

    def test_correspondence_reissuance_preserves_inert_identity_only(self) -> None:
        source, _, source_model, target_model, corr, assumptions, first = (
            fixed_context()
        )
        second_outcome = model.form_concrete_family_instance_correspondence(
            model.SELECTED_AFK_FAMILY,
            source,
            source_model,
            target_model,
            assumptions,
            correspondence=corr,
        )
        self.assertIs(second_outcome.kind, model.AttemptKind.AFFIRMATIVE)
        second = second_outcome.value
        self.assertEqual(first.judgment, second.judgment)
        self.assertEqual(first.checked_result, second.checked_result)
        self.assertEqual(first.authority_binding, second.authority_binding)
        self.assertIsNot(first.live_capability._token, second.live_capability._token)

    def test_reconstructed_correspondence_capability_is_refused(self) -> None:
        capability = fixed_context()[-1]
        reconstructed = replace(capability.live_capability)
        self.assertEqual(reconstructed, capability.live_capability)
        self.assertIsNot(reconstructed, capability.live_capability)
        changed = replace(capability, live_capability=reconstructed)
        result = model.specialize_afk_family_judgment(family_context()[-1], changed)
        self.assertIs(result.kind, model.AttemptKind.REFUSED)

    def test_specialization_refuses_inert_correspondence_without_live_use(self) -> None:
        result = model.specialize_afk_family_judgment(
            family_context()[-1], fixed_context()[-1].judgment
        )
        self.assertIs(result.kind, model.AttemptKind.REFUSED)

    def test_correspondence_dag_and_source_support_are_exact(self) -> None:
        judgment = fixed_context()[-1].judgment
        self.assertEqual(
            tuple(node.dependency_ordinals for node in judgment.hypothesis_nodes),
            (
                (),
                (0,),
                (),
                (),
                (0, 1),
                (0, 1),
                (0, 1, 2, 3, 4, 5),
                (0, 1, 2, 4, 6),
                (0, 1, 5, 6),
            ),
        )
        coordinates = model._coordinates_from_correspondence_judgment(judgment)
        context_id = model._family_instance_hypothesis_context_id(coordinates)
        context = model._formed_analysis_body(context_id, "analysis.hypothesis-context")
        self.assertEqual(context.roots, (7, 8))
        self.assertEqual(len(judgment.family_support_schema_bindings), 2)
        self.assertEqual(len(judgment.concrete_support_coordinates), 2)
        self.assertEqual(
            len(model._family_instance_source_support_bindings(coordinates).values),
            4,
        )

    def test_all_concrete_selectors_live_in_specialization(self) -> None:
        capability = fixed_context()[-1]
        self.assertEqual(
            capability.source_member_selector_id,
            model.fixed_family_member_selector_id(capability.source, "fresh"),
        )
        self.assertEqual(
            capability.target_member_selector_id,
            model.fixed_family_member_selector_id(capability.source, "fiat-shamir"),
        )

    def test_role_map_is_complete_and_canonical(self) -> None:
        correspondence = fixed_context()[4]
        roles = fixed_context()[-1].role_maps
        self.assertEqual(len(roles), 20)
        self.assertEqual(
            tuple(item.role for item in roles), model.AFK_FAMILY_ROLE_NAMES
        )
        self.assertEqual(tuple(item.ordinal for item in roles), tuple(range(20)))
        expected_native_bodies = tuple(
            model.k1.DatumRecord(
                (
                    (
                        0,
                        model._id_datum(
                            item.native_subject_projection_id,
                            "analysis.native-subject-projection",
                        ),
                    ),
                    (1, model.k1.Nat(item.ordinal)),
                    (2, model.k1.Symbol(item.role)),
                )
            )
            for item in roles
        )
        self.assertEqual(
            tuple(
                model._local_component_body(
                    item.native_coordinate_id,
                    "native-role-coordinate",
                )
                for item in roles
            ),
            expected_native_bodies,
        )
        self.assertEqual(len({item.abstract_resolved_id for item in roles}), 20)
        self.assertEqual(len({item.native_resolved_id for item in roles}), 20)

        def occurrence_payload(name: str) -> object:
            selected = next(
                item for item in correspondence.occurrence_map if item[0] == name
            )
            return model.k1.DatumRecord(
                tuple(
                    (ordinal, model.k1.Symbol(value))
                    for ordinal, value in enumerate(selected)
                )
            )

        for ordinal, occurrence in ((11, "verify"), (12, "terminal")):
            expected = model.k1.DatumRecord(
                (
                    (
                        0,
                        model._id_datum(
                            roles[ordinal].native_coordinate_id,
                            "analysis.native-role-coordinate",
                        ),
                    ),
                    (1, occurrence_payload(occurrence)),
                )
            )
            self.assertEqual(
                model._local_component_body(
                    roles[ordinal].native_resolved_id,
                    "native-resolved-role",
                ),
                expected,
            )

    def test_missing_role_map_is_malformed(self) -> None:
        source, _, source_model, target_model, corr, assumptions, _ = fixed_context()
        roles = model.family_instance_role_maps(model.SELECTED_AFK_FAMILY, source, corr)
        result = model.form_concrete_family_instance_correspondence(
            model.SELECTED_AFK_FAMILY,
            source,
            source_model,
            target_model,
            assumptions,
            correspondence=corr,
            role_maps=roles[:-1],
        )
        self.assertIs(result.kind, model.AttemptKind.MALFORMED)

    def test_changed_role_clause_is_malformed(self) -> None:
        source, _, source_model, target_model, corr, assumptions, _ = fixed_context()
        roles = list(
            model.family_instance_role_maps(model.SELECTED_AFK_FAMILY, source, corr)
        )
        roles[0] = replace(roles[0], map_clause="MerelyInjective")
        result = model.form_concrete_family_instance_correspondence(
            model.SELECTED_AFK_FAMILY,
            source,
            source_model,
            target_model,
            assumptions,
            correspondence=corr,
            role_maps=tuple(roles),
        )
        self.assertIs(result.kind, model.AttemptKind.MALFORMED)

    def test_formula_correspondence_mutation_is_malformed(self) -> None:
        source, _, source_model, target_model, corr, assumptions, _ = fixed_context()
        concrete_subject_id = fixed_context()[-1].concrete_member_subject_id
        formulas = list(
            model.pointwise_formula_correspondences(
                model.SELECTED_AFK_FAMILY, concrete_subject_id
            )
        )
        formulas[1] = replace(
            formulas[1],
            member_formula_id=model.fixture_ref(
                "analysis.quantitative-formula", "wrong-pointwise-formula"
            ),
        )
        result = model.form_concrete_family_instance_correspondence(
            model.SELECTED_AFK_FAMILY,
            source,
            source_model,
            target_model,
            assumptions,
            correspondence=corr,
            formula_correspondences=tuple(formulas),
        )
        self.assertIs(result.kind, model.AttemptKind.MALFORMED)

    def test_same_sort_member_formula_permutation_is_malformed(self) -> None:
        source, _, source_model, target_model, corr, assumptions, _ = fixed_context()
        subject = fixed_context()[-1].concrete_member_subject_id
        formulas = list(
            model.pointwise_formula_correspondences(model.SELECTED_AFK_FAMILY, subject)
        )
        formulas[1] = replace(
            formulas[1], member_formula_id=formulas[2].member_formula_id
        )
        with self.assertRaises(model.TheoremError):
            model._pointwise_formula_correspondence_id(
                formulas[1], model.SELECTED_AFK_FAMILY, subject
            )
        result = model.form_concrete_family_instance_correspondence(
            model.SELECTED_AFK_FAMILY,
            source,
            source_model,
            target_model,
            assumptions,
            correspondence=corr,
            formula_correspondences=tuple(formulas),
        )
        self.assertIs(result.kind, model.AttemptKind.MALFORMED)

    def test_formula_ast_mismatch_is_malformed(self) -> None:
        source, _, source_model, target_model, corr, assumptions, _ = fixed_context()
        concrete_subject_id = fixed_context()[-1].concrete_member_subject_id
        formulas = list(
            model.pointwise_formula_correspondences(
                model.SELECTED_AFK_FAMILY, concrete_subject_id
            )
        )
        formulas[3] = replace(formulas[3], member_normalized_ast="expected-count(Q+1)")
        result = model.form_concrete_family_instance_correspondence(
            model.SELECTED_AFK_FAMILY,
            source,
            source_model,
            target_model,
            assumptions,
            correspondence=corr,
            formula_correspondences=tuple(formulas),
        )
        self.assertIs(result.kind, model.AttemptKind.MALFORMED)

    def test_member_ast_is_rendered_independently_from_family_template(self) -> None:
        transform = model.afk_quantitative_transform(
            k=2,
            challenge_count=8,
            subject_id=fixed_context()[-1].concrete_member_subject_id,
        )
        changed = replace(
            transform,
            expected_adversary_calls=replace(
                transform.expected_adversary_calls, offset=3
            ),
        )
        member_ast = model._member_operator_normal_form(changed, 3)
        family_ast = model._instantiate_local_operator_ast(
            model.AFK_LOCAL_OPERATOR_CATALOG[3], 8
        )
        self.assertEqual(member_ast, "expected-count(Q+3)")
        self.assertNotEqual(member_ast, family_ast)

    def test_setup_timing_is_derived_from_exact_k2_prefix(self) -> None:
        source, _, _, _, correspondence, *_ = fixed_context()
        self.assertEqual(
            model._derive_fixed_setup_provenance(
                source,
                correspondence.fixed_public_setup.challenge_ordinal,
                correspondence.transcript_prefix_map,
            ),
            (True, False, False, False),
        )
        missing_generator = tuple(
            item
            for item in correspondence.transcript_prefix_map
            if item != ("public-parameter", ("root", "g"))
        )
        self.assertFalse(
            model._derive_fixed_setup_provenance(
                source,
                correspondence.fixed_public_setup.challenge_ordinal,
                missing_generator,
            )[0]
        )
        mutable_case = replace(
            source.case,
            invocation=replace(
                source.case.invocation,
                values=dict(source.case.invocation.values),
            ),
        )
        mutable_source = replace(source, case=mutable_case)
        self.assertEqual(
            model._derive_fixed_setup_provenance(
                mutable_source,
                correspondence.fixed_public_setup.challenge_ordinal,
                correspondence.transcript_prefix_map,
            ),
            (False, False, False, True),
        )

    def test_raw_query_index_bound_is_not_bytes_value_payload_capacity(self) -> None:
        correspondence = fixed_context()[4]
        self.assertEqual(
            model.native_raw_query_index_bit_bound(),
            8 * model.k1.MAX_CANONICAL_BYTES,
        )
        payload_bytes = model.k1.MAX_CANONICAL_BYTES - 9
        encoded = model.k1.encode_datum(model.k1.BytesValue(b"x" * payload_bytes))
        self.assertEqual(len(encoded), model.k1.MAX_CANONICAL_BYTES)
        self.assertEqual(
            model.native_raw_query_index_bit_bound() - 8 * payload_bytes,
            72,
        )
        for entry in correspondence.query_encoding_table:
            carrier = entry.k2_challenge_query_carrier
            self.assertLessEqual(len(carrier), model.k1.MAX_CANONICAL_BYTES)
            self.assertEqual(
                model.k1.encode_datum(model.k1.decode_datum(carrier)), carrier
            )

    def test_missing_each_correspondence_premise_cannot_answer(self) -> None:
        source, _, source_model, target_model, corr, assumptions, _ = fixed_context()
        for missing in assumptions:
            with self.subTest(missing=missing.internal_reference().hex()[-8:]):
                result = model.form_concrete_family_instance_correspondence(
                    model.SELECTED_AFK_FAMILY,
                    source,
                    source_model,
                    target_model,
                    tuple(item for item in assumptions if item != missing),
                    correspondence=corr,
                )
                self.assertIs(result.kind, model.AttemptKind.CANNOT_ANSWER)

    def test_pointwise_ro_bound_mismatch_cannot_answer(self) -> None:
        source, _, source_model, target_model, corr, *_ = fixed_context()
        family = model.SELECTED_AFK_FAMILY
        wrong_bound = 8 * model.k1.MAX_CANONICAL_BYTES + 8
        with self.assertRaises(model.TheoremError):
            model.fixed_member_index_bound_hypothesis_id(
                family,
                fixed_context()[-1].concrete_member_subject_id,
                wrong_bound,
                model.native_raw_query_index_bit_bound(),
            )
        result = model.form_concrete_family_instance_correspondence(
            family,
            source,
            source_model,
            target_model,
            (),
            correspondence=corr,
            family_index_bound_at_n0=wrong_bound,
        )
        self.assertIs(result.kind, model.AttemptKind.CANNOT_ANSWER)

    def test_admission_replays_minting_gate_for_small_index_domain(self) -> None:
        source, _, source_model, target_model, corr, *_ = fixed_context()
        family = replace(
            model.SELECTED_AFK_FAMILY,
            ro_index_domain=replace(
                model.SELECTED_AFK_FAMILY.ro_index_domain,
                length_bound_coefficients_low_to_high=(64,),
            ),
        )
        substituted = replace(
            fixed_context()[-1],
            family=family,
            family_definition_id=model.family_definition_id(family),
            family_index_bound_at_n0=64,
        )
        with self.assertRaises(model.AuthorityError):
            model.require_concrete_family_instance_correspondence(substituted)

    def test_family_ro_bound_is_evaluated_from_authenticated_family_data(self) -> None:
        source, _, source_model, target_model, corr, *_ = fixed_context()
        family = replace(
            model.SELECTED_AFK_FAMILY,
            ro_index_domain=replace(
                model.SELECTED_AFK_FAMILY.ro_index_domain,
                length_bound_coefficients_low_to_high=(
                    8 * model.k1.MAX_CANONICAL_BYTES + 8,
                ),
            ),
        )
        result = model.form_concrete_family_instance_correspondence(
            family,
            source,
            source_model,
            target_model,
            (),
            correspondence=corr,
        )
        self.assertIs(result.kind, model.AttemptKind.CANNOT_ANSWER)

    def test_non_N8_family_has_no_selected_concrete_member(self) -> None:
        source, _, source_model, target_model, corr, *_ = fixed_context()
        family = model.form_afk_asymptotic_family(
            "constant-N16-no-native-anchor", challenge_cardinality=16
        )
        result = model.form_concrete_family_instance_correspondence(
            family, source, source_model, target_model, (), correspondence=corr
        )
        self.assertIs(result.kind, model.AttemptKind.CANNOT_ANSWER)

    def test_stock_bounded_rejection_member_is_not_selected(self) -> None:
        source = model.derive_fresh_fs_relation_source(model.k3.schnorr_case())
        source_model = model.fresh_special_soundness_model(k=2, challenge_count=11)
        target_model = model.adaptive_rom_knowledge_model(k=2, challenge_count=8)
        correspondence = model.derive_fs_correspondence(
            source, source_model, target_model
        )
        self.assertFalse(correspondence.sampler_map[0][-1])
        result = model.form_concrete_family_instance_correspondence(
            model.SELECTED_AFK_FAMILY,
            source,
            source_model,
            target_model,
            (),
            correspondence=correspondence,
        )
        self.assertIs(result.kind, model.AttemptKind.CANNOT_ANSWER)

    def test_exact_n8_member_with_non_total_sampler_is_not_selected(self) -> None:
        case = model.total_uniform_schnorr_case()
        construction = replace(
            case.construction,
            application_domain=b"zkc/test/schnorr-n8-bounded-rejection/v0",
            max_attempts=2,
        )
        protocol_id = model.k3.protocol_id(
            case.core,
            construction,
            model.k2.ChallengeInterpretation.FIAT_SHAMIR,
        )
        interface = model.k3.default_interface(
            case.core,
            construction,
            model.k2.ChallengeInterpretation.FIAT_SHAMIR,
            expose_all_transports=True,
        )
        plan = replace(case.plan, protocol_id=protocol_id)
        protocol_binding = replace(case.protocol_binding, protocol_id=protocol_id)
        surface = model.k3.derive_plan_witness_surface(
            case.core,
            construction,
            model.k2.ChallengeInterpretation.FIAT_SHAMIR,
            plan,
        )
        plan_binding = replace(
            case.plan_binding,
            plan_witness_surface_id=model.k3.plan_witness_surface_id(surface),
        )
        source = model.derive_fresh_fs_relation_source(
            replace(
                case,
                construction=construction,
                interface=interface,
                plan=plan,
                protocol_binding=protocol_binding,
                plan_binding=plan_binding,
            )
        )
        result = model.form_concrete_family_instance_correspondence(
            model.SELECTED_AFK_FAMILY,
            source,
            model.fresh_special_soundness_model(k=2, challenge_count=8),
            model.adaptive_rom_knowledge_model(k=2, challenge_count=8),
            (),
        )
        self.assertIs(result.kind, model.AttemptKind.CANNOT_ANSWER)
        self.assertEqual(
            result.detail,
            "concrete sampler is not exact total uniform N=8",
        )

    def test_admission_replays_minting_gate_for_bounded_rejection_member(self) -> None:
        source = model.derive_fresh_fs_relation_source(model.k3.schnorr_case())
        source_model = model.fresh_special_soundness_model(k=2, challenge_count=11)
        target_model = model.adaptive_rom_knowledge_model(k=2, challenge_count=8)
        correspondence = model.derive_fs_correspondence(
            source, source_model, target_model
        )
        substituted = replace(
            fixed_context()[-1],
            source=source,
            source_model=source_model,
            target_model=target_model,
            fs_correspondence=correspondence,
            fs_correspondence_id=model.fs_correspondence_id(correspondence),
        )
        result = model.specialize_afk_family_judgment(family_context()[-1], substituted)
        self.assertIs(result.kind, model.AttemptKind.REFUSED)

    def test_post_authentication_substitution_is_refused(self) -> None:
        capability = fixed_context()[-1]
        changed_judgment = replace(
            capability.judgment,
            judgment_id=model.fixture_ref(
                "analysis.judgment-record",
                "substituted-after-mint",
            ),
        )
        with self.assertRaises(model.AuthorityError):
            model.require_family_instance_correspondence_judgment(changed_judgment)
        changed = replace(capability, judgment=changed_judgment)
        result = model.specialize_afk_family_judgment(family_context()[-1], changed)
        self.assertIs(result.kind, model.AttemptKind.REFUSED)

    def test_member_judgment_revalidates_its_own_identity(self) -> None:
        result = model.specialize_afk_family_judgment(
            family_context()[-1], fixed_context()[-1]
        )
        self.assertIs(result.kind, model.AttemptKind.AFFIRMATIVE)
        model.require_concrete_member_judgment(result.value)
        changed = replace(
            result.value,
            judgment_id=model.fixture_ref(
                "analysis.concrete-member-knowledge-judgment",
                "substituted-after-mint",
            ),
        )
        with self.assertRaises(model.AuthorityError):
            model.require_concrete_member_judgment(changed)

    def test_cold_member_revalidation_does_not_touch_live_registries(self) -> None:
        result = model.specialize_afk_family_judgment(
            family_context()[-1], fixed_context()[-1]
        )
        self.assertIs(result.kind, model.AttemptKind.AFFIRMATIVE)
        registries = (
            model._FAMILY_PORT_TOKENS,
            model._EXTERNAL_SOURCE_CAP_TOKENS,
            model._TRUTH_TREATMENT_TOKENS,
            model._FAMILY_JUDGMENT_TOKENS,
            model._MEMBER_CORRESPONDENCE_TOKENS,
        )
        before = tuple(len(item) for item in registries)
        model.require_family_instance_correspondence_judgment(
            result.value.correspondence_judgment
        )
        model.require_concrete_member_judgment(result.value)
        self.assertEqual(tuple(len(item) for item in registries), before)

    def test_raw_statement_profile_has_fixed_setup(self) -> None:
        correspondence = fixed_context()[4]
        setup = correspondence.fixed_public_setup
        self.assertTrue(setup.fixed_before_prover_and_oracle)
        self.assertFalse(setup.adversary_selected)
        self.assertFalse(setup.oracle_correlated)
        self.assertFalse(setup.mutable_within_instance)
        self.assertEqual(correspondence.query_index_map, ("statement", "commitment"))

    def test_native_statement_length_is_derived_and_retained(self) -> None:
        source, _, source_model, target_model, corr, assumptions, capability = (
            fixed_context()
        )
        self.assertEqual(model.native_statement_octet_length(source), 1)
        self.assertEqual(capability.native_statement_length, 1)
        self.assertIn(
            model.fixed_member_length_embedding_hypothesis_id(
                model.SELECTED_AFK_FAMILY,
                source,
                capability.concrete_member_subject_id,
            ),
            assumptions,
        )
        result = model.form_concrete_family_instance_correspondence(
            model.SELECTED_AFK_FAMILY,
            source,
            source_model,
            target_model,
            assumptions,
            correspondence=corr,
        )
        self.assertIs(result.kind, model.AttemptKind.AFFIRMATIVE)

    def test_query_encoding_is_full_and_injective(self) -> None:
        table = fixed_context()[4].query_encoding_table
        self.assertEqual(len(table), 121)
        self.assertEqual(len({item.k2_challenge_query_carrier for item in table}), 121)

    def test_setup_session_mutation_is_malformed(self) -> None:
        source, _, source_model, target_model, corr, assumptions, _ = fixed_context()
        values = dict(source.case.invocation.values)
        values["session"] = b"different"
        changed_source = replace(
            source,
            case=replace(
                source.case,
                invocation=model.k2.Invocation(MappingProxyType(values)),
            ),
        )
        changed_setup = replace(
            corr.fixed_public_setup,
            _source=changed_source,
        )
        changed = replace(
            corr,
            fixed_public_setup=changed_setup,
        )
        result = model.form_concrete_family_instance_correspondence(
            model.SELECTED_AFK_FAMILY,
            source,
            source_model,
            target_model,
            assumptions,
            correspondence=changed,
        )
        self.assertIs(result.kind, model.AttemptKind.MALFORMED)

    def test_specialization_requires_correspondence(self) -> None:
        result = model.specialize_afk_family_judgment(family_context()[-1], None)
        self.assertIs(result.kind, model.AttemptKind.CANNOT_ANSWER)

    def test_specialization_requires_live_family_capability(self) -> None:
        result = model.specialize_afk_family_judgment(
            family_context()[-1].judgment, fixed_context()[-1]
        )
        self.assertIs(result.kind, model.AttemptKind.REFUSED)

    def test_positive_specialization_is_relation_bound(self) -> None:
        result = model.specialize_afk_family_judgment(
            family_context()[-1], fixed_context()[-1]
        )
        self.assertIs(result.kind, model.AttemptKind.AFFIRMATIVE)
        model.require_concrete_member_judgment(result.value)
        self.assertEqual(
            result.value.target_conclusion.success_event_id,
            model.subject_bound_relation_success_event_id(
                fixed_context()[-1].concrete_member_subject_id
            ),
        )

    def test_concrete_subject_substitution_is_rejected(self) -> None:
        result = model.specialize_afk_family_judgment(
            family_context()[-1], fixed_context()[-1]
        )
        self.assertIs(result.kind, model.AttemptKind.AFFIRMATIVE)
        changed = replace(
            result.value,
            concrete_member_subject_id=model.fixture_ref(
                "analysis.concrete-family-member-subject", "wrong-member"
            ),
        )
        with self.assertRaises(model.AuthorityError):
            model.require_concrete_member_judgment(changed)

    def test_member_judgment_retains_no_live_correspondence_or_issuer(self) -> None:
        result = model.specialize_afk_family_judgment(
            family_context()[-1], fixed_context()[-1]
        )
        self.assertIs(result.kind, model.AttemptKind.AFFIRMATIVE)
        names = {item.name for item in fields(type(result.value))}
        self.assertFalse(
            names
            & {
                "correspondence",
                "correspondence_capability_id",
                "live_capability",
                "family_capability",
                "_token",
                "_issuer",
                "checker",
                "provider",
                "occurrence",
            }
        )
        self.assertTrue(
            {
                "family_judgment",
                "correspondence_judgment",
                "family_checked_result",
                "family_authority_binding",
                "correspondence_checked_result",
                "correspondence_authority_binding",
            }
            <= names
        )
        changed = replace(
            result.value,
            correspondence_checked_result=replace(
                result.value.correspondence_checked_result,
                result_id=model.fixture_ref(
                    "analysis.judgment-record", "detached-correspondence-result"
                ),
            ),
        )
        with self.assertRaises(model.AuthorityError):
            model.require_concrete_member_judgment(changed)

    def test_pointwise_capability_cannot_fill_all_n_source_slot(self) -> None:
        port, truth = family_context()[4], family_context()[6]
        result = model.transport_afk_family_knowledge(fixed_context()[-1], port, truth)
        self.assertIs(result.kind, model.AttemptKind.REFUSED)


class AdaptiveAndQuantitativeBoundaryTest(unittest.TestCase):
    def test_target_prefix_has_native_adaptive_order(self) -> None:
        prefix = model.adaptive_rom_knowledge_model().quantifiers
        self.assertEqual(
            tuple((item.kind, item.binder) for item in prefix),
            (
                (model.QuantifierKind.EXISTS_POSITIVE_POLYNOMIAL, "q_KS"),
                (model.QuantifierKind.EXISTS_UNIFORM_BLACK_BOX_EXTRACTOR, "E"),
                (model.QuantifierKind.FOR_ALL_QUANTITATIVE_VALUE, "n"),
                (model.QuantifierKind.FOR_ALL_QUANTITATIVE_VALUE, "Q"),
                (model.QuantifierKind.FOR_ALL_ADAPTIVE_PROVERS, "Pa"),
            ),
        )

    def test_statement_is_prover_output_not_outer_binder(self) -> None:
        target = model.adaptive_rom_knowledge_model()
        self.assertIs(
            target.statement_timing, model.StatementTiming.ADAPTIVE_PROVER_OUTPUT
        )
        self.assertNotIn("statement", tuple(item.binder for item in target.quantifiers))

    def test_adaptive_prover_is_total_output_and_unbounded_time(self) -> None:
        profile = model.ADAPTIVE_KNOWLEDGE_PROFILE
        self.assertEqual(profile.inputs, ())
        self.assertTrue(profile.total_output_required)
        self.assertEqual(
            profile.efficiency_restriction,
            "no-PPT-restriction-on-adaptive-prover",
        )
        self.assertIn(
            "randomized-adversary-coins-fixed-into-one-deterministic-next-message-strategy-before-extractor-reruns",
            profile.output_constraints,
        )

    def test_extractor_input_excludes_Q_epsilon_code_and_table(self) -> None:
        self.assertEqual(
            model.AFK_EXTRACTOR_PROFILE_BODY.inputs,
            ("security-parameter", "black-box-adaptive-prover"),
        )
        self.assertEqual(
            model.AFK_EXTRACTOR_PROFILE_BODY.forbidden_inputs,
            (
                "query-bound",
                "success-probability",
                "prover-code-as-data",
                "hidden-oracle-table",
            ),
        )
        self.assertEqual(
            model.AFK_EXTRACTOR_PROFILE_BODY.prover_rerun_coin_law,
            "one-fixed-deterministic-prover-strategy-per-extractor-experiment-no-coin-resampling",
        )

    def test_expected_call_bound_refuses_probability_formula(self) -> None:
        transform = model.afk_quantitative_transform(k=2, challenge_count=8)
        formulas = model.afk_quantitative_formula_ids(transform)
        dimension = next(
            item
            for item in model.AFK_RESOURCE_DIMENSIONS
            if item.name == "adversary-running-calls"
        )
        with self.assertRaises(model.QuantitativeError):
            model.expected_invocation_bound_id(
                model.ExpectedInvocationBound(
                    model.subject_bound_experiment_body_id(
                        8, transform.subject_id, "extractor-experiment"
                    ),
                    model.subject_bound_afk_adversary_running_algorithm_id(
                        8, transform.subject_id
                    ),
                    model.resource_dimension_id(dimension),
                    "less-than-or-equal",
                    formulas["knowledge-error"],
                )
            )

    def test_expected_call_bound_binds_actor_resource_and_experiment(self) -> None:
        transform = model.afk_quantitative_transform(k=2, challenge_count=8)
        formulas = model.afk_quantitative_formula_ids(transform)
        with self.assertRaises(model.QuantitativeError):
            model.expected_invocation_bound_id(
                model.ExpectedInvocationBound(
                    model.subject_bound_experiment_body_id(
                        8, transform.subject_id, "extractor-experiment"
                    ),
                    model.subject_bound_afk_adversary_running_algorithm_id(
                        8, transform.subject_id
                    ),
                    model.AFK_ADVERSARY_RO_QUERY_DIMENSION_ID,
                    "less-than-or-equal",
                    formulas["expected-adversary-calls-upper-bound"],
                )
            )

    def test_formula_roles_require_the_authenticated_transform(self) -> None:
        transform = model.afk_quantitative_transform(k=2, challenge_count=8)
        changed = replace(
            transform,
            source_success=transform.knowledge_error,
        )
        with self.assertRaises(model.QuantitativeError):
            model.afk_quantitative_formula_ids(changed)

    def test_conclusion_refuses_same_sort_formula_role_swap(self) -> None:
        transform = model.afk_quantitative_transform(k=2, challenge_count=8)
        formulas = model.afk_quantitative_formula_ids(transform)
        conclusion = model.afk_knowledge_soundness_conclusion(transform)
        changed = replace(
            conclusion,
            success_lower_bound_formula_id=formulas[
                "lemma4-transcript-extraction-lower-bound"
            ],
        )
        with self.assertRaises(model.PropertyError):
            model._property_conclusion_body(changed)

    def test_conclusion_refuses_formulas_from_another_subject(self) -> None:
        first = model.afk_quantitative_transform(k=2, challenge_count=8)
        second = model.afk_quantitative_transform(
            k=2,
            challenge_count=8,
            subject_id=model.fixture_ref(
                "analysis.family-member-subject", "other-formula-subject"
            ),
        )
        first_conclusion = model.afk_knowledge_soundness_conclusion(first)
        second_conclusion = model.afk_knowledge_soundness_conclusion(second)
        changed = replace(
            first_conclusion,
            success_probability_formula_id=(
                second_conclusion.success_probability_formula_id
            ),
            knowledge_error_formula_id=second_conclusion.knowledge_error_formula_id,
            success_lower_bound_formula_id=(
                second_conclusion.success_lower_bound_formula_id
            ),
            expected_invocation_bound_id=(
                second_conclusion.expected_invocation_bound_id
            ),
        )
        with self.assertRaises(model.PropertyError):
            model._property_conclusion_body(changed)

    def test_Q_domain_is_strictly_less_than_N(self) -> None:
        transform = model.afk_quantitative_transform(k=2, challenge_count=8)
        self.assertEqual(
            model.afk_query_bound_domain_id(8),
            model.value_domain_profile_id(
                model.ValueDomainProfile(
                    "QueryCount-AdversaryRO",
                    "zero-less-than-or-equal-Q-strictly-less-than-N",
                    (("N", 8),),
                )
            ),
        )
        self.assertEqual(
            model.instantiate_afk_at_query_bound(transform, 7).knowledge_error,
            Fraction(1, 1),
        )
        for wrong in (-1, 8, 64):
            with self.subTest(Q=wrong), self.assertRaises(model.QuantitativeError):
                model.instantiate_afk_at_query_bound(transform, wrong)

    def test_expected_calls_use_distinct_dimension_and_Q_plus_two(self) -> None:
        transform = model.afk_quantitative_transform(k=2, challenge_count=8)
        self.assertEqual(
            model.instantiate_afk_at_query_bound(transform, 3).expected_adversary_calls,
            5,
        )
        self.assertIs(
            transform.expected_adversary_calls.sort,
            model.QuantitativeSort.EXPECTED_COUNT_ADVERSARY_RUNNING_ALGORITHM,
        )
        self.assertIsNot(
            transform.expected_adversary_calls.sort,
            model.QuantitativeSort.QUERY_COUNT_ADVERSARY_RO,
        )

    def test_lower_bounds_remain_signed_and_unclamped(self) -> None:
        transform = model.afk_quantitative_transform(k=2, challenge_count=8)
        self.assertIs(
            transform.knowledge_success_lower_bound.sort,
            model.QuantitativeSort.SIGNED_PROBABILITY_LOWER_BOUND,
        )
        self.assertIs(
            transform.lemma4_extraction_lower_bound.sort,
            model.QuantitativeSort.SIGNED_PROBABILITY_LOWER_BOUND,
        )

    def test_pointwise_formula_mapping_has_exact_four_outputs(self) -> None:
        correspondences = model.pointwise_formula_correspondences(
            model.SELECTED_AFK_FAMILY,
            fixed_context()[-1].concrete_member_subject_id,
        )
        self.assertEqual(
            tuple(item.local_ordinal for item in correspondences), (0, 1, 2, 3)
        )
        self.assertEqual(len({item.member_formula_id for item in correspondences}), 4)

    def test_lazy_random_function_repeats_return_stored_value(self) -> None:
        result = model.lazy_random_function_trace(
            8, (b"image", b"off-image", b"image"), (3, 6)
        )
        self.assertEqual(result, (3, 6, 3))

    def test_lazy_trace_rejects_missing_or_unused_draws(self) -> None:
        with self.assertRaises(model.ExperimentError):
            model.lazy_random_function_trace(8, (b"a", b"b"), (1,))
        with self.assertRaises(model.ExperimentError):
            model.lazy_random_function_trace(8, (b"a",), (1, 2))
        with self.assertRaises(model.ExperimentError):
            model.lazy_random_function_trace(
                8,
                (b"x" * (model.k1.MAX_CANONICAL_BYTES + 1),),
                (1,),
            )

    def test_two_index_joint_law_is_uniform(self) -> None:
        law = model.two_distinct_lazy_query_joint_law(8)
        self.assertEqual(len(law), 64)
        self.assertEqual({mass for _, mass in law}, {Fraction(1, 64)})
        self.assertEqual(sum((mass for _, mass in law), Fraction()), Fraction(1))


class DirectionalLossDeferralTest(unittest.TestCase):
    @lru_cache(maxsize=1)
    def loss_context(self) -> tuple[object, ...]:
        source = model.derive_relation_property_source(model.lossy_schnorr_case())
        return source, model.derive_loss_uses(source)

    def test_loss_occurrence_is_derived_from_checked_binding(self) -> None:
        _, uses = self.loss_context()
        self.assertEqual(len(uses), 1)
        self.assertTrue(uses[0].coordinate.startswith("plan-witness:"))

    def test_missing_typed_export_rule_cannot_answer(self) -> None:
        source, _ = self.loss_context()
        self.assertIs(
            model.price_loss_uses(source, (), ()).kind,
            model.AttemptKind.CANNOT_ANSWER,
        )

    def test_missing_export_premise_cannot_answer(self) -> None:
        source, uses = self.loss_context()
        rule = model.LossExportRule(
            uses[0].quantitative_export_id, model.fixture_hypothesis("loss-premise")
        )
        self.assertIs(
            model.price_loss_uses(source, (rule,), ()).kind,
            model.AttemptKind.CANNOT_ANSWER,
        )

    def test_complete_fixture_rule_still_defers_owner_semantics(self) -> None:
        source, uses = self.loss_context()
        hypothesis = model.fixture_hypothesis("loss-premise")
        rule = model.LossExportRule(uses[0].quantitative_export_id, hypothesis)
        result = model.price_loss_uses(source, (rule,), (hypothesis,))
        self.assertIs(result.kind, model.AttemptKind.CANNOT_ANSWER)
        self.assertIn("owner-issued Relations semantic rule", result.detail)


if __name__ == "__main__":
    unittest.main()
