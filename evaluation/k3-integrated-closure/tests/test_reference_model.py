from __future__ import annotations

from dataclasses import fields, replace
from functools import lru_cache
from pathlib import Path
import sys
import unittest
from unittest.mock import patch


PACKAGE_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(PACKAGE_ROOT))

import reference_model as model  # noqa: E402


@lru_cache(maxsize=1)
def baseline() -> model.IntegratedWitness:
    return model.build_integrated_witness()


@lru_cache(maxsize=1)
def changed_construction() -> model.IntegratedWitness:
    case = model.coherent_construction_domain(
        baseline().case,
        b"zkc/k3-e/schnorr-total-uniform/domain-rotation/v0",
    )
    return model.build_integrated_witness(case)


@lru_cache(maxsize=1)
def changed_interface() -> model.IntegratedWitness:
    return model.build_integrated_witness(
        model.coherent_interface_external_rename(baseline().case)
    )


@lru_cache(maxsize=1)
def exported_plan() -> model.IntegratedWitness:
    return model.build_integrated_witness(
        model.with_unused_plan_export(baseline().case)
    )


class CanonicalImportTest(unittest.TestCase):
    def test_analysis_then_oir_share_exact_module_objects(self) -> None:
        self.assertIs(model.analysis.k3, model.oir.k3)
        self.assertIs(model.analysis.k2, model.oir.k2)
        self.assertIs(model.analysis.k1, model.oir.k1)
        self.assertIs(model.model_chain()[0], model.analysis.k3)

    def test_every_module_came_from_the_exact_expected_file(self) -> None:
        expected = tuple(
            item.resolve()
            for item in (
                model.ANALYSIS_PATH,
                model.OIR_PATH,
                model.K3B_PATH,
                model.K2_PATH,
                model.K1_PATH,
            )
        )
        self.assertEqual(model.CANONICAL_IMPORT_FILES, expected)


class PositiveJoinedWitnessTest(unittest.TestCase):
    def test_independent_consumer_records_start_from_one_owner_case(self) -> None:
        witness = baseline()
        case = witness.case
        self.assertIs(witness.analysis_lanes.relation.case, case)
        self.assertIs(witness.analysis_lanes.fresh_fs.case, case)
        self.assertIs(witness.verifier.request.core, case.core)
        self.assertIs(witness.verifier.request.interface, case.interface)
        self.assertIs(witness.prover.request.plan, case.plan)

    def test_cross_consumer_correspondence_contains_only_inert_typed_ids(self) -> None:
        anchors = baseline().anchors
        self.assertTrue(
            all(
                type(getattr(anchors, item.name)) is model.k1.TypedContentId
                for item in fields(anchors)
            )
        )
        self.assertEqual(anchors, model.shared_owner_anchors(baseline().case))

    def test_analysis_sources_and_finite_profile_are_exactly_anchored(self) -> None:
        witness = baseline()
        lanes = witness.analysis_lanes
        model.analysis.require_relation_property_source(lanes.relation)
        model.analysis.require_fresh_fs_relation_source(lanes.fresh_fs)
        model.analysis.require_schnorr_special_soundness_profile(
            lanes.fresh_fs, lanes.finite_profile
        )
        self.assertEqual(
            lanes.relation.protocol_source.core_id,
            witness.anchors.core_id,
        )
        self.assertEqual(
            lanes.finite_profile.relation_interface_id,
            witness.anchors.relation_interface_id,
        )

    def test_endpoint_lanes_are_separately_admitted_and_projection_checked(self) -> None:
        witness = baseline()
        verifier = witness.verifier
        prover = witness.prover
        self.assertIs(verifier.request.role, model.oir.EndpointRole.VERIFIER)
        self.assertIs(prover.request.role, model.oir.EndpointRole.PROVER)
        self.assertNotEqual(verifier.source.view_id, prover.source.view_id)
        self.assertNotEqual(verifier.admitted.oir_id, prover.admitted.oir_id)
        self.assertNotEqual(
            verifier.validation.proposition.proposition_id,
            prover.validation.proposition.proposition_id,
        )
        self.assertEqual(verifier.checked.source_view_id, verifier.source.view_id)
        self.assertEqual(prover.checked.source_view_id, prover.source.view_id)

    def test_checked_graphs_and_validation_source_handles_share_exact_anchors(
        self,
    ) -> None:
        witness = baseline()
        for lane in (witness.verifier, witness.prover):
            self.assertEqual(
                model.oir.canonical_bytes(lane.source.view.semantic_graph),
                model.oir.canonical_bytes(lane.admitted.endpoint.semantic_graph),
            )
            expected_handles = (
                witness.anchors.fiat_shamir_protocol_id.internal_reference().hex(),
                witness.anchors.interface_id.internal_reference().hex(),
            )
            if lane.request.role is model.oir.EndpointRole.PROVER:
                expected_handles += (
                    witness.anchors.plan_id.internal_reference().hex(),
                )
            self.assertEqual(lane.validation.source_handles, expected_handles)

    def test_checked_adapters_are_purpose_bound_and_retain_residuals(self) -> None:
        verifier_lane = baseline().verifier
        prover_lane = baseline().prover
        verifier = verifier_lane.adapter
        prover = prover_lane.adapter
        self.assertIs(verifier_lane.basis.adapter, verifier)
        self.assertIs(prover_lane.basis.adapter, prover)
        self.assertIs(verifier_lane.source.basis, verifier_lane.basis)
        self.assertIs(prover_lane.source.basis, prover_lane.basis)
        self.assertIs(verifier_lane.source.adapter, verifier)
        self.assertIs(prover_lane.source.adapter, prover)
        self.assertIs(verifier_lane.validation.basis, verifier_lane.basis)
        self.assertIs(prover_lane.validation.basis, prover_lane.basis)
        self.assertIs(verifier_lane.validation.adapter, verifier)
        self.assertIs(prover_lane.validation.adapter, prover)
        self.assertIs(verifier.purpose, model.oir.ProjectionPurpose.FS_VERIFIER)
        self.assertIs(prover.purpose, model.oir.ProjectionPurpose.FS_PLAN_PROVER)
        self.assertIs(
            verifier.supplement,
            baseline().verifier.request.supplement_authority,
        )
        self.assertIs(
            prover.supplement,
            baseline().prover.request.supplement_authority,
        )
        self.assertIs(
            verifier.supplement.supplement,
            baseline().verifier.request.future_owner,
        )
        self.assertIs(
            prover.supplement.supplement,
            baseline().prover.request.future_owner,
        )
        self.assertEqual(len(verifier.k2_static_views), 7)
        self.assertEqual(len(prover.k2_static_views), 8)
        self.assertIsNone(verifier.checked_plan)
        self.assertEqual(prover.checked_plan.plan_id, baseline().anchors.plan_id)
        self.assertEqual(
            verifier.supplement_only_paths,
            model.oir.FUTURE_OWNER_SUPPLEMENT_ONLY_PATHS,
        )
        self.assertEqual(
            prover.supplement_only_paths,
            model.oir.FUTURE_OWNER_SUPPLEMENT_ONLY_PATHS,
        )
        self.assertEqual(
            verifier.interface_view.view.protocol_interface_id,
            baseline().anchors.interface_id,
        )
        self.assertEqual(
            prover.interface_view.view.protocol_interface_id,
            baseline().anchors.interface_id,
        )

    def test_missing_supplement_is_missing_dependency_for_each_role(self) -> None:
        for role in (model.oir.EndpointRole.VERIFIER, model.oir.EndpointRole.PROVER):
            request = model.projection_request(
                baseline().case, role, include_supplement=False
            )
            adapter = model.oir.check_projection_owner_adapter(request)
            source = model.oir.derive_source_view(request)
            target = model.oir.project(request)
            self.assertIs(adapter.kind, model.oir.OutcomeKind.MISSING_DEPENDENCY)
            self.assertIs(source.kind, model.oir.OutcomeKind.MISSING_DEPENDENCY)
            self.assertIs(target.kind, model.oir.OutcomeKind.MISSING_DEPENDENCY)

    def test_portable_binding_does_not_replace_live_supplement_authority(self) -> None:
        request = baseline().verifier.request
        authority = request.supplement_authority
        self.assertIs(type(authority), model.oir.IssuedFutureOwnerSupplement)
        context = model.k1.authenticate_profiled_semantic_content(
            authority.authority_binding_id,
            model.oir.SOURCE_PROFILE,
            authority.authority_binding.body(),
            model.oir.K3D_SEMANTIC_PROFILES.source_view_bundle,
            supported_profiles=(model.oir.SOURCE_PROFILE,),
        )
        self.assertEqual(len(context.authenticated_profiles), 5)

        unbound = replace(request, supplement_authority=None)
        self.assertIs(
            model.oir.check_projection_owner_adapter(unbound).kind,
            model.oir.OutcomeKind.MISSING_DEPENDENCY,
        )
        portable_only = replace(
            request,
            supplement_authority=authority.authority_binding,
        )
        self.assertIs(
            model.oir.check_projection_owner_adapter(portable_only).kind,
            model.oir.OutcomeKind.REFUSED,
        )
        self.assertIs(
            model.oir.check_projection_owner_adapter(request).kind,
            model.oir.OutcomeKind.AFFIRMATIVE,
        )

    def test_equal_supplement_reconstruction_requires_fresh_owner_issuance(
        self,
    ) -> None:
        request = baseline().verifier.request
        reconstructed = replace(request.future_owner)
        stale = replace(request, future_owner=reconstructed)
        refused = model.oir.check_projection_owner_adapter(stale)
        self.assertIs(refused.kind, model.oir.OutcomeKind.REFUSED)
        rebound = model.oir.bind_future_owner_supplement(
            replace(stale, supplement_authority=None)
        )
        self.assertIs(rebound.kind, model.oir.OutcomeKind.AFFIRMATIVE)
        checked = model.oir.check_projection_owner_adapter(rebound.value)
        self.assertIs(checked.kind, model.oir.OutcomeKind.AFFIRMATIVE)

    def test_supported_projection_rejects_reconstructed_and_wrong_bases(self) -> None:
        basis = baseline().verifier.basis
        reconstructed = replace(basis)
        self.assertIs(
            model.oir.project_supported_endpoint(reconstructed).kind,
            model.oir.OutcomeKind.REFUSED,
        )
        self.assertIs(
            model.oir.extract_endpoint_source_view(reconstructed).kind,
            model.oir.OutcomeKind.REFUSED,
        )
        self.assertIs(
            model.oir.project_supported_endpoint(object()).kind,
            model.oir.OutcomeKind.MALFORMED,
        )


class CrossBoundaryMutationTest(unittest.TestCase):
    def test_coherent_construction_domain_rotates_only_dependent_roots(self) -> None:
        old = model.identity_snapshot(baseline())
        new = model.identity_snapshot(changed_construction())
        self.assertEqual(old.anchors.core_id, new.anchors.core_id)
        self.assertEqual(old.anchors.fresh_protocol_id, new.anchors.fresh_protocol_id)
        self.assertEqual(
            old.anchors.relation_interface_id,
            new.anchors.relation_interface_id,
        )
        self.assertNotEqual(old.anchors.construction_id, new.anchors.construction_id)
        self.assertNotEqual(
            old.anchors.fiat_shamir_protocol_id,
            new.anchors.fiat_shamir_protocol_id,
        )
        self.assertNotEqual(old.pair_manifest_id, new.pair_manifest_id)
        self.assertEqual(old.finite_profile_id, new.finite_profile_id)
        self.assertNotEqual(old.verifier_source_id, new.verifier_source_id)
        self.assertNotEqual(old.prover_oir_id, new.prover_oir_id)

    def test_stale_core_challenge_dependents_are_rejected_in_both_consumers(
        self,
    ) -> None:
        stale = model.stale_challenge_domain(baseline().case)
        with self.assertRaises((model.analysis.AnalysisError, model.k3.K3Error)):
            model.derive_analysis_lanes(stale)
        for role in (model.oir.EndpointRole.VERIFIER, model.oir.EndpointRole.PROVER):
            request = model.projection_request(stale, role, admit_supplement=False)
            answer = model.oir.bind_future_owner_supplement(request)
            self.assertIs(answer.kind, model.oir.OutcomeKind.REFUSED)

    def test_relations_only_witness_rename_is_refused_only_by_analysis(self) -> None:
        old = baseline()
        changed_case = model.coherent_relation_witness_rename(old.case)
        with self.assertRaisesRegex(
            model.analysis.SourceIngressError,
            "closed K3-C slot catalog",
        ):
            model.derive_analysis_lanes(
                changed_case,
                require_finite_profile=False,
                relation_witness_slot="secret-renamed",
            )
        changed_verifier = model.derive_endpoint_lane(
            model.projection_request(changed_case, model.oir.EndpointRole.VERIFIER)
        )
        changed_prover = model.derive_endpoint_lane(
            model.projection_request(changed_case, model.oir.EndpointRole.PROVER)
        )
        self.assertEqual(old.verifier.source.view_id, changed_verifier.source.view_id)
        self.assertEqual(old.verifier.admitted.oir_id, changed_verifier.admitted.oir_id)
        self.assertEqual(old.prover.source.view_id, changed_prover.source.view_id)
        self.assertEqual(old.prover.admitted.oir_id, changed_prover.admitted.oir_id)

    def test_interface_external_coordinate_rotates_endpoint_semantics_only(
        self,
    ) -> None:
        old = model.identity_snapshot(baseline())
        new = model.identity_snapshot(changed_interface())
        self.assertEqual(old.pair_manifest_id, new.pair_manifest_id)
        self.assertEqual(old.finite_profile_id, new.finite_profile_id)
        self.assertNotEqual(old.anchors.interface_id, new.anchors.interface_id)
        self.assertNotEqual(old.verifier_source_id, new.verifier_source_id)
        self.assertNotEqual(old.verifier_oir_id, new.verifier_oir_id)
        self.assertNotEqual(old.verifier_proposition_id, new.verifier_proposition_id)
        self.assertNotEqual(old.prover_source_id, new.prover_source_id)
        self.assertNotEqual(old.prover_oir_id, new.prover_oir_id)

    def test_unused_valid_plan_export_rotates_plan_handle_not_endpoint_graph(
        self,
    ) -> None:
        old = model.identity_snapshot(baseline())
        new = model.identity_snapshot(exported_plan())
        self.assertNotEqual(old.anchors.plan_id, new.anchors.plan_id)
        self.assertNotEqual(old.anchors.plan_binding_id, new.anchors.plan_binding_id)
        self.assertEqual(old.prover_source_id, new.prover_source_id)
        self.assertEqual(old.prover_oir_id, new.prover_oir_id)
        self.assertEqual(old.prover_proposition_id, new.prover_proposition_id)
        self.assertNotEqual(old.prover_validation_id, new.prover_validation_id)

    def test_provenance_and_source_label_rotate_validation_only(self) -> None:
        old = baseline().verifier
        changed_request = replace(
            old.request,
            provenance="k3e:independent-validation-run",
            source_label="same-source-different-label",
        )
        new = model.derive_endpoint_lane(changed_request)
        self.assertEqual(old.source.view_id, new.source.view_id)
        self.assertEqual(old.admitted.oir_id, new.admitted.oir_id)
        self.assertEqual(
            old.validation.proposition.proposition_id,
            new.validation.proposition.proposition_id,
        )
        self.assertNotEqual(
            old.checked.validation_request_id,
            new.checked.validation_request_id,
        )

    def test_downstream_oir_change_is_negative_and_leaves_upstream_fixed(self) -> None:
        lane = baseline().verifier
        result = model.downstream_oir_mismatch(lane)
        self.assertIs(result.kind, model.oir.OutcomeKind.NEGATIVE)
        self.assertEqual(
            tuple(item.path for item in result.mismatches),
            ("semantic_graph.role_abi_graph",),
        )
        self.assertEqual(
            lane.source.view_id,
            model.identity_snapshot(baseline()).verifier_source_id,
        )


class IndependentBranchLocalityTest(unittest.TestCase):
    def test_rederiving_analysis_records_preserves_semantic_ids(self) -> None:
        case = baseline().case
        first = model.derive_analysis_lanes(case)
        second = model.derive_analysis_lanes(case)
        self.assertIsNot(first.relation, second.relation)
        self.assertIsNot(first.fresh_fs, second.fresh_fs)
        self.assertIsNot(first.finite_profile, second.finite_profile)
        self.assertEqual(first.relation, second.relation)
        self.assertEqual(first.fresh_fs, second.fresh_fs)
        self.assertEqual(
            model.analysis.source_manifest_id(first.fresh_fs.fresh_manifest),
            model.analysis.source_manifest_id(second.fresh_fs.fresh_manifest),
        )
        self.assertEqual(
            model.analysis.source_manifest_id(first.fresh_fs.pair_manifest),
            model.analysis.source_manifest_id(second.fresh_fs.pair_manifest),
        )
        self.assertEqual(
            first.finite_profile.profile_id, second.finite_profile.profile_id
        )

    def test_analysis_hypothesis_changes_only_the_analysis_proposition(self) -> None:
        lanes = baseline().analysis_lanes
        source = lanes.fresh_fs
        profile = lanes.finite_profile
        source_model = model.analysis.fresh_special_soundness_model(
            k=2, challenge_count=8
        )
        required = (
            model.analysis.schnorr_relation_correspondence_hypothesis_id(profile),
            model.analysis.k2_static_view_support_hypothesis_id(source),
        )
        original = model.analysis.form_special_soundness_proposition(
            source, source_model, profile, required
        )
        changed = model.analysis.form_special_soundness_proposition(
            source,
            source_model,
            profile,
            required + (model.analysis.fixture_hypothesis("k3e-extra-premise"),),
        )
        self.assertNotEqual(
            model.analysis.analysis_proposition_id(original),
            model.analysis.analysis_proposition_id(changed),
        )


class SemanticLanguageProfileIdentityLocalityTest(unittest.TestCase):
    @staticmethod
    def _analysis_profiles(profiles):
        return (
            profiles.kernel,
            profiles.property,
            profiles.transport,
            profiles.theorem_source_validation,
        )

    @staticmethod
    def _oir_profiles(profiles):
        return (
            profiles.endpoint_graph,
            profiles.source_view,
            profiles.projection,
            profiles.validation,
        )

    def assert_exact_rotations(self, original, changed, rotated) -> None:
        for ordinal, (left, right) in enumerate(zip(original, changed, strict=True)):
            with self.subTest(ordinal=ordinal):
                if ordinal in rotated:
                    self.assertNotEqual(left.identity, right.identity)
                else:
                    self.assertEqual(left.identity, right.identity)

    def test_imported_root_contexts_are_exact_and_have_no_cross_branch_import(self) -> None:
        analysis_profiles = model.analysis.K3C_ANALYSIS_SEMANTIC_PROFILES
        oir_profiles = model.oir.K3D_SEMANTIC_PROFILES
        self.assertIs(
            analysis_profiles.k3b_profiles,
            model.k3.K3B_SEMANTIC_PROFILES,
        )
        self.assertIs(oir_profiles.k3b_profiles, model.k3.K3B_SEMANTIC_PROFILES)
        self.assertIs(
            model.k3.K3B_SEMANTIC_PROFILES.k2_profiles,
            model.k2.K2_SEMANTIC_PROFILES,
        )
        roots = (
            (analysis_profiles.kernel, analysis_profiles.kernel_bundle, 1),
            (analysis_profiles.property, analysis_profiles.property_bundle, 6),
            (analysis_profiles.transport, analysis_profiles.transport_bundle, 7),
            (
                analysis_profiles.theorem_source_validation,
                analysis_profiles.theorem_source_validation_bundle,
                8,
            ),
            (oir_profiles.endpoint_graph, oir_profiles.endpoint_graph_bundle, 4),
            (oir_profiles.source_view, oir_profiles.source_view_bundle, 5),
            (oir_profiles.projection, oir_profiles.projection_bundle, 6),
            (oir_profiles.validation, oir_profiles.validation_bundle, 7),
        )
        for profile, bundle, expected_count in roots:
            with self.subTest(profile=profile.profile_family.value):
                context = model.k1.effective_semantic_context(
                    profile.identity,
                    bundle,
                    semantic_regime=model.k1.SEMANTIC_REGIME_ID,
                )
                self.assertEqual(len(context.authenticated_profiles), expected_count)
                self.assertEqual(
                    {item for item, _ in context.authenticated_profiles},
                    set(bundle),
                )

        shared = set(analysis_profiles.property_bundle) & set(
            oir_profiles.validation_bundle
        )
        self.assertEqual(
            shared,
            {
                model.k2.K2_SEMANTIC_PROFILES.interaction.identity,
                model.k2.K2_SEMANTIC_PROFILES.transcript_fs.identity,
                model.k3.K3B_SEMANTIC_PROFILES.interface_plan.identity,
            },
        )
        for profile_id in shared:
            self.assertIs(
                analysis_profiles.property_bundle[profile_id],
                oir_profiles.validation_bundle[profile_id],
            )
        for profile in self._analysis_profiles(analysis_profiles):
            self.assertNotIn(profile.identity, oir_profiles.validation_bundle)
        for profile in self._oir_profiles(oir_profiles):
            self.assertNotIn(
                profile.identity,
                analysis_profiles.theorem_source_validation_bundle,
            )

        cross_branch_bundles = (
            (
                analysis_profiles.property.identity,
                {
                    **analysis_profiles.property_bundle,
                    **oir_profiles.validation_bundle,
                },
            ),
            (
                oir_profiles.validation.identity,
                {
                    **oir_profiles.validation_bundle,
                    **analysis_profiles.theorem_source_validation_bundle,
                },
            ),
        )
        for selected_profile, overcomplete in cross_branch_bundles:
            with self.subTest(selected_profile=selected_profile.subject_kind):
                with self.assertRaises(model.k1._Control) as caught:
                    model.k1.effective_semantic_context(
                        selected_profile,
                        overcomplete,
                        semantic_regime=model.k1.SEMANTIC_REGIME_ID,
                    )
                self.assertIs(caught.exception.outcome, model.k1.Outcome.REFUSED)
                self.assertEqual(
                    caught.exception.code,
                    "K1-REFUSED-EXTRA-PROFILE",
                )

    def test_actual_branch_subjects_authenticate_in_branch_local_contexts(self) -> None:
        authenticator = model.k1.authenticate_profiled_semantic_content
        with patch.object(
            model.k1,
            "authenticate_profiled_semantic_content",
            wraps=authenticator,
        ) as authenticated:
            witness = model.build_integrated_witness()

        expected = {
            witness.analysis_lanes.finite_profile.profile_id: (
                model.analysis.K3C_ANALYSIS_PROPERTY_PROFILE_ID,
                6,
            )
        }
        for lane in (witness.verifier, witness.prover):
            authority = lane.request.supplement_authority
            self.assertIs(type(authority), model.oir.IssuedFutureOwnerSupplement)
            expected.update(
                {
                    authority.authority_binding_id: (model.oir.SOURCE_PROFILE, 5),
                    lane.source.view_id: (model.oir.SOURCE_PROFILE, 5),
                    lane.admitted.oir_id: (model.oir.OIR_PROFILE, 4),
                    lane.validation.proposition.proposition_id: (
                        model.oir.RELATION_PROFILE,
                        6,
                    ),
                    lane.checked.validation_request_id: (
                        model.oir.VALIDATION_PROFILE,
                        7,
                    ),
                }
            )

        seen = set()
        for call in authenticated.call_args_list:
            if not call.args or call.args[0] not in expected:
                continue
            identifier, selected_profile, _domain_body, supplied_profiles = call.args
            expected_profile, expected_count = expected[identifier]
            with self.subTest(subject_kind=identifier.subject_kind):
                self.assertEqual(selected_profile, expected_profile)
                self.assertEqual(
                    call.kwargs,
                    {"supported_profiles": (expected_profile,)},
                )
                context = model.k1.effective_semantic_context(
                    selected_profile,
                    supplied_profiles,
                    semantic_regime=model.k1.SEMANTIC_REGIME_ID,
                )
                self.assertEqual(len(context.authenticated_profiles), expected_count)
            seen.add(identifier)
        self.assertEqual(seen, set(expected))

    def test_analysis_law_identity_rotations_follow_exact_descendants(self) -> None:
        original = model.analysis.K3C_ANALYSIS_SEMANTIC_PROFILES
        original_profiles = self._analysis_profiles(original)
        cases = (
            ("kernel_law", {0, 1, 2, 3}),
            ("property_law", {1, 2, 3}),
            ("transport_law", {2, 3}),
            ("theorem_source_validation_law", {3}),
        )
        for argument, rotated in cases:
            with self.subTest(argument=argument):
                changed = model.analysis.make_k3c_analysis_semantic_profiles(
                    **{argument: f"zkc-k3e-mutated-{argument}".encode("ascii")}
                )
                self.assert_exact_rotations(
                    original_profiles,
                    self._analysis_profiles(changed),
                    rotated,
                )
        self.assertEqual(
            model.oir.K3D_SEMANTIC_PROFILES,
            model.oir.make_k3d_semantic_profiles(),
        )

    def test_oir_law_identity_rotations_follow_exact_descendants(self) -> None:
        original = model.oir.K3D_SEMANTIC_PROFILES
        original_profiles = self._oir_profiles(original)
        cases = (
            ("endpoint_graph_law", {0, 1, 2, 3}),
            ("source_view_law", {1, 2, 3}),
            ("projection_law", {2, 3}),
            ("validation_law", {3}),
        )
        for argument, rotated in cases:
            with self.subTest(argument=argument):
                changed = model.oir.make_k3d_semantic_profiles(
                    **{argument: f"zkc-k3e-mutated-{argument}".encode("ascii")}
                )
                self.assert_exact_rotations(
                    original_profiles,
                    self._oir_profiles(changed),
                    rotated,
                )
        self.assertEqual(
            model.analysis.K3C_ANALYSIS_SEMANTIC_PROFILES,
            model.analysis.make_k3c_analysis_semantic_profiles(),
        )

    def test_relations_law_rotates_analysis_descendants_but_not_k3d(self) -> None:
        changed_k3b = model.k3.make_k3b_semantic_profiles(
            relations_law=b"zkc-k3e-mutated-relations-law"
        )
        changed_analysis = model.analysis.make_k3c_analysis_semantic_profiles(
            k3b_profiles=changed_k3b
        )
        changed_oir = model.oir.make_k3d_semantic_profiles(k3b_profiles=changed_k3b)
        self.assertEqual(
            model.k3.K3B_SEMANTIC_PROFILES.interface_plan.identity,
            changed_k3b.interface_plan.identity,
        )
        self.assertNotEqual(
            model.k3.K3B_SEMANTIC_PROFILES.relations_correspondence.identity,
            changed_k3b.relations_correspondence.identity,
        )
        self.assert_exact_rotations(
            self._analysis_profiles(model.analysis.K3C_ANALYSIS_SEMANTIC_PROFILES),
            self._analysis_profiles(changed_analysis),
            {1, 2, 3},
        )
        self.assert_exact_rotations(
            self._oir_profiles(model.oir.K3D_SEMANTIC_PROFILES),
            self._oir_profiles(changed_oir),
            set(),
        )

    def test_interface_plan_law_rotates_both_consumer_profile_trees(self) -> None:
        changed_k3b = model.k3.make_k3b_semantic_profiles(
            interface_plan_law=b"zkc-k3e-mutated-interface-plan-law"
        )
        changed_analysis = model.analysis.make_k3c_analysis_semantic_profiles(
            k3b_profiles=changed_k3b
        )
        changed_oir = model.oir.make_k3d_semantic_profiles(k3b_profiles=changed_k3b)
        self.assertNotEqual(
            model.k3.K3B_SEMANTIC_PROFILES.interface_plan.identity,
            changed_k3b.interface_plan.identity,
        )
        self.assertNotEqual(
            model.k3.K3B_SEMANTIC_PROFILES.relations_correspondence.identity,
            changed_k3b.relations_correspondence.identity,
        )
        self.assert_exact_rotations(
            self._analysis_profiles(model.analysis.K3C_ANALYSIS_SEMANTIC_PROFILES),
            self._analysis_profiles(changed_analysis),
            {1, 2, 3},
        )
        self.assert_exact_rotations(
            self._oir_profiles(model.oir.K3D_SEMANTIC_PROFILES),
            self._oir_profiles(changed_oir),
            {0, 1, 2, 3},
        )


if __name__ == "__main__":
    unittest.main()
