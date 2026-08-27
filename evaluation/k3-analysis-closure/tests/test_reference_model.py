from __future__ import annotations

from dataclasses import fields, replace
from fractions import Fraction
from functools import lru_cache
import hashlib
from pathlib import Path
import sys
import unittest
from unittest.mock import patch


PACKAGE_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(PACKAGE_ROOT))

import reference_model as model  # noqa: E402


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


def _legacy_unchecked_index_bound_hypothesis(
    family: model.AFKAsymptoticFamily,
    concrete_subject_id: object,
    family_index_bound_at_n0: int,
    native_index_bound: int,
) -> object:
    """Reproduce the pre-repair hypothesis body for a regression attack."""

    return model._analysis_id(
        "analysis.hypothesis",
        model.k1.DatumRecord(
            (
                (
                    0,
                    model._id_datum(
                        model.family_definition_id(family),
                        "analysis.asymptotic-family-definition",
                    ),
                ),
                (
                    1,
                    model._id_datum(
                        concrete_subject_id,
                        "analysis.concrete-family-member-subject",
                    ),
                ),
                (2, model.k1.Nat(1)),
                (3, model.k1.Nat(family_index_bound_at_n0)),
                (4, model.k1.Nat(native_index_bound)),
                (
                    5,
                    model.k1.Symbol(
                        "checked-numeric-u-at-n0-equality-with-assumed-domain-correspondence"
                    ),
                ),
            )
        ),
    )


def coherently_refield_correspondence(
    family: model.AFKAsymptoticFamily,
    source: object,
    source_model: model.ExperimentModel,
    target_model: model.ExperimentModel,
    correspondence: model.FSCorrespondence,
    family_index_bound_at_n0: int,
    *,
    reproduce_legacy_bound_hypothesis: bool = False,
) -> model.ConcreteFamilyInstanceCorrespondence:
    """Recompute every dependent field around a substituted semantic anchor."""

    legitimate = fixed_context()[-1]
    source_selector = model.fixed_family_member_selector_id(source, "fresh")
    target_selector = model.fixed_family_member_selector_id(source, "fiat-shamir")
    subject_id = model.concrete_member_subject_id(
        family,
        source,
        correspondence,
        source_selector,
        target_selector,
    )
    role_maps = model.family_instance_role_maps(family, source, correspondence)
    formulas = model.pointwise_formula_correspondences(family, subject_id)
    hypothesis_patch = (
        patch.object(
            model,
            "fixed_member_index_bound_hypothesis_id",
            side_effect=_legacy_unchecked_index_bound_hypothesis,
        )
        if reproduce_legacy_bound_hypothesis
        else patch.object(
            model,
            "fixed_member_index_bound_hypothesis_id",
            wraps=model.fixed_member_index_bound_hypothesis_id,
        )
    )
    with hypothesis_patch:
        hypotheses = model.fixed_member_required_hypotheses(
            family,
            source,
            source_model,
            target_model,
            correspondence,
            family_index_bound_at_n0=family_index_bound_at_n0,
        )
    capability_id = model._member_correspondence_id(
        family,
        source,
        source_model,
        target_model,
        correspondence,
        subject_id,
        family_index_bound_at_n0,
        legitimate.native_index_bound,
        source_selector,
        target_selector,
        role_maps,
        formulas,
        hypotheses,
    )
    return replace(
        legitimate,
        correspondence_capability_id=capability_id,
        family=family,
        family_definition_id=model.family_definition_id(family),
        source=source,
        native_subject_projection_id=model.native_subject_projection_id(source),
        concrete_member_subject_id=subject_id,
        family_index_bound_at_n0=family_index_bound_at_n0,
        source_model=source_model,
        target_model=target_model,
        fs_correspondence=correspondence,
        fs_correspondence_id=model.fs_correspondence_id(correspondence),
        source_member_selector_id=source_selector,
        target_member_selector_id=target_selector,
        role_maps=role_maps,
        formula_correspondences=formulas,
        retained_hypotheses=hypotheses,
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
        digest = hashlib.sha256(model.k1.encode_datum(body)).hexdigest()
        self.assertEqual(digest, schema.authority.statement_content_sha256)
        self.assertEqual(
            digest,
            "f449dd9a41b8d4ef6f4ed7794d68398f81d562e31e828252fabd09ca551ae0bc",
        )
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

    def test_pdf_digest_mutation_is_rejected(self) -> None:
        schema = model.afk_v2_theorem_schema()
        changed = replace(
            schema, authority=replace(schema.authority, artifact_sha256="0" * 64)
        )
        with self.assertRaises(model.TheoremError):
            model.fs_theorem_schema_id(changed)

    def test_statement_component_mutation_is_rejected(self) -> None:
        schema = model.afk_v2_theorem_schema()
        changed = replace(
            schema.source_property_template,
            canonical_clauses=("different-source-property",),
        )
        with self.assertRaises(model.TheoremError):
            model.fs_theorem_schema_id(
                replace(schema, source_property_template=changed)
            )

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

    def test_operator_ast_mutation_is_rejected(self) -> None:
        schema = model.afk_v2_theorem_schema()
        operators = list(schema.local_operator_catalog)
        operators[3] = replace(operators[3], template_ast="expected-count(Q+1)")
        with self.assertRaises(model.TheoremError):
            model.fs_theorem_schema_id(
                replace(schema, local_operator_catalog=tuple(operators))
            )

    def test_schema_admission_is_not_theorem_truth(self) -> None:
        schema = model.afk_v2_theorem_schema()
        self.assertNotIn(model.ASSUMED_AFK_V2_THM4, tuple(schema.__dict__.values()))
        self.assertEqual(model.assume_afk_theorem_truth(schema).treatment, "Assumed")


class FamilyApplicabilityTest(unittest.TestCase):
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

    def test_wrong_source_goal_cannot_instantiate_schema(self) -> None:
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
        self.assertIs(result.kind, model.AttemptKind.CANNOT_ANSWER)

    def test_q_equals_two_substitution_is_not_selected(self) -> None:
        schema, family, candidate, premises, *_ = family_context()
        substitution = replace(
            candidate.parameter_substitution,
            positive_polynomial_id=model.fixture_ref(
                "analysis.positive-polynomial-profile", "constant-two"
            ),
        )
        result = model.check_afk_family_applicability(
            schema,
            family,
            premises,
            candidate=replace(candidate, parameter_substitution=substitution),
        )
        self.assertIs(result.kind, model.AttemptKind.CANNOT_ANSWER)

    def test_ro_index_domain_identity_mismatch_cannot_instantiate(self) -> None:
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
        self.assertIs(result.kind, model.AttemptKind.CANNOT_ANSWER)

    def test_formula_binding_mutation_cannot_instantiate(self) -> None:
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
        self.assertIs(result.kind, model.AttemptKind.CANNOT_ANSWER)

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
            support_ref=model.fixture_ref("analysis.theorem-truth-support", "forged"),
        )
        result = model.transport_afk_family_knowledge(source_capability, port, changed)
        self.assertIs(result.kind, model.AttemptKind.REFUSED)

    def test_forged_all_n_source_support_is_refused(self) -> None:
        port, source_capability, truth = family_context()[4:7]
        changed = replace(
            source_capability,
            support_id=model.fixture_ref("analysis.support-instantiation", "forged"),
        )
        result = model.transport_afk_family_knowledge(changed, port, truth)
        self.assertIs(result.kind, model.AttemptKind.REFUSED)

    def test_positive_transport_retains_both_external_assumptions(self) -> None:
        source_capability, truth, judgment = family_context()[5:8]
        self.assertIn(
            source_capability.retained_hypothesis_id, judgment.retained_hypotheses
        )
        self.assertIn(truth.retained_hypothesis_id, judgment.retained_hypotheses)
        model.require_family_knowledge_judgment(judgment)

    def test_revalidated_judgment_cannot_drop_all_n_source_premise(self) -> None:
        source_capability, judgment = family_context()[5], family_context()[-1]
        changed = replace(
            judgment,
            retained_hypotheses=tuple(
                item
                for item in judgment.retained_hypotheses
                if item != source_capability.retained_hypothesis_id
            ),
        )
        with self.assertRaises(model.TheoremError):
            model.require_family_knowledge_judgment(changed)

    def test_revalidated_judgment_cannot_swap_truth_support(self) -> None:
        judgment = family_context()[-1]
        changed = replace(
            judgment,
            theorem_truth_support_ref=model.fixture_ref(
                "analysis.theorem-truth-support", "unrelated-proof"
            ),
        )
        with self.assertRaises(model.TheoremError):
            model.require_family_knowledge_judgment(changed)

    def test_revalidated_judgment_cannot_float_to_another_family(self) -> None:
        judgment = family_context()[-1]
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
        judgment = family_context()[-1]
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


class PointwiseSpecializationTest(unittest.TestCase):
    def test_exact_correspondence_is_issued(self) -> None:
        capability = fixed_context()[-1]
        model.require_concrete_family_instance_correspondence(capability)
        self.assertEqual(
            (capability.logical_index, capability.native_statement_length), (1, 1)
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
        old_shape = tuple(
            model._analysis_id(
                "analysis.native-role-coordinate",
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
                ),
            )
            for item in roles
        )
        self.assertEqual(tuple(item.native_coordinate_id for item in roles), old_shape)
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
            expected = model._analysis_id(
                "analysis.native-resolved-role",
                model.k1.DatumRecord(
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
                ),
            )
            self.assertEqual(roles[ordinal].native_resolved_id, expected)

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
        refielded = coherently_refield_correspondence(
            family,
            source,
            source_model,
            target_model,
            corr,
            64,
            reproduce_legacy_bound_hypothesis=True,
        )
        with self.assertRaises(model.AuthorityError):
            model.require_concrete_family_instance_correspondence(refielded)

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
        target_model = model.adaptive_rom_knowledge_model(k=2, challenge_count=11)
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

    def test_admission_replays_minting_gate_for_bounded_rejection_member(self) -> None:
        source = model.derive_fresh_fs_relation_source(model.k3.schnorr_case())
        source_model = model.fresh_special_soundness_model(k=2, challenge_count=11)
        target_model = model.adaptive_rom_knowledge_model(k=2, challenge_count=11)
        correspondence = model.derive_fs_correspondence(
            source, source_model, target_model
        )
        refielded = coherently_refield_correspondence(
            model.SELECTED_AFK_FAMILY,
            source,
            source_model,
            target_model,
            correspondence,
            model.native_raw_query_index_bit_bound(),
        )
        with self.assertRaises(model.AuthorityError):
            model.require_concrete_family_instance_correspondence(refielded)
        result = model.specialize_afk_family_judgment(family_context()[-1], refielded)
        self.assertIs(result.kind, model.AttemptKind.REFUSED)

    def test_post_authentication_substitution_is_refused(self) -> None:
        capability = fixed_context()[-1]
        changed = replace(
            capability,
            correspondence_capability_id=model.fixture_ref(
                "analysis.family-instance-correspondence-capability",
                "substituted-after-mint",
            ),
        )
        with self.assertRaises(model.AuthorityError):
            model.require_concrete_family_instance_correspondence(changed)
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
        changed_setup = replace(corr.fixed_public_setup, session=b"different")
        changed = replace(
            corr,
            fixed_public_setup=changed_setup,
            fixed_public_setup_id=model.fixed_public_setup_id(changed_setup),
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

    def test_member_judgment_revalidates_its_correspondence_object(self) -> None:
        result = model.specialize_afk_family_judgment(
            family_context()[-1], fixed_context()[-1]
        )
        self.assertIs(result.kind, model.AttemptKind.AFFIRMATIVE)
        changed = replace(
            result.value,
            correspondence=replace(
                result.value.correspondence,
                concrete_member_subject_id=model.fixture_ref(
                    "analysis.concrete-family-member-subject", "detached"
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
