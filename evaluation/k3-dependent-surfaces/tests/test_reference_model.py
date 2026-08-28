from __future__ import annotations

import copy
from dataclasses import FrozenInstanceError, fields, replace
from pathlib import Path
import pickle
import sys
import unittest
from types import MappingProxyType


PACKAGE_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(PACKAGE_ROOT))

import reference_model as model  # noqa: E402


def axes(case: model.DependentSurfaceCase) -> tuple[object | None, object]:
    if case.name == "verifier-private":
        return None, model.k2.ChallengeInterpretation.FRESH
    return case.construction, model.k2.ChallengeInterpretation.FIAT_SHAMIR


def protocol_check(
    case: model.DependentSurfaceCase,
    binding: model.ProtocolRelationBinding | None = None,
) -> model.CheckedProtocolRelationBinding:
    construction, interpretation = axes(case)
    return model.check_protocol_relation_binding(
        case.core,
        construction,
        interpretation,
        case.relation_interfaces,
        case.bridges,
        case.protocol_binding if binding is None else binding,
    )


def plan_check(
    case: model.DependentSurfaceCase,
    binding: model.PlanWitnessBinding | None = None,
) -> model.CheckedPlanWitnessBinding:
    construction, interpretation = axes(case)
    model.check_plan_realizes(
        case.core, construction, interpretation, case.plan
    )
    surface = model.derive_plan_witness_surface(
        case.core, construction, interpretation, case.plan
    )
    if len(case.relation_interfaces) != 1:
        raise AssertionError("bounded fixtures select exactly one relation Interface")
    return model.check_plan_witness_binding(
        surface,
        case.relation_interfaces[0],
        case.bridges,
        case.plan_binding if binding is None else binding,
    )


def coordinate(source: object) -> model.RelationRunCoordinate:
    return model.RelationRunCoordinate(
        model.RunCoordinateKind.STATEMENT
        if type(source) is model.BindingRef
        else model.RunCoordinateKind.PUBLIC_OCCURRENCE,
        source,
    )


def binding_manifest(
    binding: model.ProtocolRelationBinding,
) -> tuple[model.RelationRunCoordinate, ...]:
    requested = tuple(
        [coordinate(edge.source) for edge in binding.public_edges]
        + [coordinate(edge.source) for edge in binding.phase_edges]
        + [
            coordinate(source)
            for edge in binding.oracle_edges
            for source in (edge.query, edge.answer)
        ]
    )
    return tuple(dict.fromkeys(requested))


def completed(result: object) -> object:
    if type(result) is not model.k2.Completed:
        raise AssertionError(result)
    return result.record


def issue_case_view(case: model.DependentSurfaceCase) -> model.RelationRunView:
    record = completed(
        model.k2.generate(
            case.core,
            case.construction,
            axes(case)[1],
            case.invocation,
            case.strategy,
        )
    )
    return model.issue_relation_run_view(
        case.core,
        case.construction,
        case.invocation,
        record,
        binding_manifest(case.protocol_binding),
    )


class SemanticProfileIdentityTest(unittest.TestCase):
    @staticmethod
    def body() -> object:
        return model.k1.DatumRecord(
            ((0, model.k1.Symbol("profile-locality-probe")),)
        )

    def identity(
        self,
        subject_kind: str,
        profiles: model.K3BSemanticProfiles,
    ) -> object:
        return model._semantic_id(
            subject_kind,
            self.body(),
            profiles=profiles,
        )

    def test_each_k3b_profile_root_has_its_exact_no_extra_closure(self) -> None:
        expected_sizes = {
            model.PIR_INTERFACE_PLAN_PROFILE_ID: 3,
            model.RELATIONS_PROFILE_ID: 4,
        }
        for root_id, expected_size in expected_sizes.items():
            preimages = model.K3B_ROOT_PROFILE_PREIMAGES[root_id]
            self.assertIs(type(preimages), dict)
            context = model.k1.effective_semantic_context(
                root_id,
                preimages,
                semantic_regime=model.k1.SEMANTIC_REGIME_ID,
            )
            self.assertEqual(len(context.authenticated_profiles), expected_size)
        self.assertEqual(
            set(model.K3B_PROFILE_PREIMAGES),
            {
                model.k2.PIR_INTERACTION_PROFILE_ID,
                model.k2.PIR_TRANSCRIPT_PROFILE_ID,
                model.k2.PIR_PUBLIC_SETUP_PROFILE_ID,
                model.PIR_INTERFACE_PLAN_PROFILE_ID,
                model.RELATIONS_PROFILE_ID,
            },
        )
        interface_with_unrelated_public_view = {
            **model.PIR_INTERFACE_PLAN_PROFILE_PREIMAGES,
            model.k2.PIR_PUBLIC_SETUP_PROFILE_ID: model.k2.PIR_PUBLIC_SETUP_PROFILE,
        }
        with self.assertRaises(model.k1._Control) as caught:
            model.k1.effective_semantic_context(
                model.PIR_INTERFACE_PLAN_PROFILE_ID,
                interface_with_unrelated_public_view,
                semantic_regime=model.k1.SEMANTIC_REGIME_ID,
            )
        self.assertIs(caught.exception.outcome, model.k1.Outcome.REFUSED)
        self.assertEqual(caught.exception.code, "K1-REFUSED-EXTRA-PROFILE")
        with self.assertRaisesRegex(model.K3Error, "outside its exact profile catalog"):
            model._semantic_id("pir.protocol", self.body())

    def test_interface_only_support_does_not_backflow_from_relations(self) -> None:
        case = model.schnorr_case()
        manifest = model.external_statement_read_manifest(
            case.interface,
            ("statement.statement",),
        )
        issued = model.issue_protocol_interface_correspondence_view(
            case.core,
            case.construction,
            model.k2.ChallengeInterpretation.FIAT_SHAMIR,
            case.interface,
            manifest,
            profile_support=model.K3B_INTERFACE_PROFILE_SUPPORT,
        )
        self.assertIs(issued.kind, model.k2.QualifiedViewOutcomeKind.AFFIRMATIVE)
        relation_id = model.relation_interface_id(case.relation_interfaces[0])
        transform = model.RelationTransform(
            "profile-support-probe",
            (relation_id,),
            (relation_id,),
            model.IDENTITY_CODEC,
        )
        relation_manifest = model.claim_reduction_transform_read_manifest(
            (model.relation_transform_id(transform),)
        )
        refused = model.issue_relations_correspondence_view(
            (transform,),
            relation_manifest,
            profile_support=model.K3B_INTERFACE_PROFILE_SUPPORT,
        )
        self.assertIs(refused.kind, model.k2.QualifiedViewOutcomeKind.UNSUPPORTED)

    def test_real_owner_views_enforce_support_and_profile_locality(self) -> None:
        case = model.schnorr_case()
        interpretation = model.k2.ChallengeInterpretation.FIAT_SHAMIR
        baseline_manifest = model.external_statement_read_manifest(
            case.interface,
            ("statement.statement",),
        )
        baseline = model.issue_protocol_interface_correspondence_view(
            case.core,
            case.construction,
            interpretation,
            case.interface,
            baseline_manifest,
        )
        self.assertIs(baseline.kind, model.k2.QualifiedViewOutcomeKind.AFFIRMATIVE)

        changed = model.make_k3b_semantic_profiles(
            interface_plan_law=b"zkc-k3b-real-interface-plan-law-v1",
        )
        changed_interface = model.default_interface(
            case.core,
            case.construction,
            interpretation,
            expose_all_transports=True,
            profiles=changed,
        )
        changed_manifest = model.external_statement_read_manifest(
            changed_interface,
            ("statement.statement",),
        )
        unsupported = model.issue_protocol_interface_correspondence_view(
            case.core,
            case.construction,
            interpretation,
            changed_interface,
            changed_manifest,
            profiles=changed,
        )
        self.assertIs(
            unsupported.kind,
            model.k2.QualifiedViewOutcomeKind.UNSUPPORTED,
        )
        supported = model.issue_protocol_interface_correspondence_view(
            case.core,
            case.construction,
            interpretation,
            changed_interface,
            changed_manifest,
            profiles=changed,
            profile_support=model.make_k3b_profile_support(changed),
        )
        self.assertIs(supported.kind, model.k2.QualifiedViewOutcomeKind.AFFIRMATIVE)
        assert type(baseline.value) is model.IssuedProtocolInterfaceCorrespondenceView
        assert type(supported.value) is model.IssuedProtocolInterfaceCorrespondenceView
        self.assertNotEqual(
            baseline.value.view.protocol_interface_id,
            supported.value.view.protocol_interface_id,
        )
        self.assertNotEqual(
            baseline.value.source_binding.owner_binding_payload,
            supported.value.source_binding.owner_binding_payload,
        )

        relations_only = model.make_k3b_semantic_profiles(
            relations_law=b"zkc-k3b-real-relations-law-v1",
        )
        same_interface = model.default_interface(
            case.core,
            case.construction,
            interpretation,
            expose_all_transports=True,
            profiles=relations_only,
        )
        same_manifest = model.external_statement_read_manifest(
            same_interface,
            ("statement.statement",),
        )
        unaffected = model.issue_protocol_interface_correspondence_view(
            case.core,
            case.construction,
            interpretation,
            same_interface,
            same_manifest,
            profiles=relations_only,
            profile_support=model.make_k3b_profile_support(relations_only),
        )
        self.assertIs(unaffected.kind, model.k2.QualifiedViewOutcomeKind.AFFIRMATIVE)
        assert type(unaffected.value) is model.IssuedProtocolInterfaceCorrespondenceView
        self.assertEqual(
            baseline.value.view.protocol_interface_id,
            unaffected.value.view.protocol_interface_id,
        )
        self.assertEqual(
            baseline.value.source_binding.owner_binding_payload,
            unaffected.value.source_binding.owner_binding_payload,
        )

    def test_real_relations_view_rotates_only_under_supported_profile(self) -> None:
        case = model.schnorr_case()
        relation_id = model.relation_interface_id(case.relation_interfaces[0])
        transform = model.RelationTransform(
            "real-relations-profile-probe",
            (relation_id,),
            (relation_id,),
            model.IDENTITY_CODEC,
        )
        baseline_id = model.relation_transform_id(transform)
        baseline_manifest = model.claim_reduction_transform_read_manifest(
            (baseline_id,)
        )
        baseline = model.issue_relations_correspondence_view(
            (transform,),
            baseline_manifest,
        )
        self.assertIs(baseline.kind, model.k2.QualifiedViewOutcomeKind.AFFIRMATIVE)

        changed = model.make_k3b_semantic_profiles(
            relations_law=b"zkc-k3b-real-relations-view-law-v1",
        )
        changed_id = model.relation_transform_id(transform, profiles=changed)
        changed_manifest = model.claim_reduction_transform_read_manifest(
            (changed_id,)
        )
        unsupported = model.issue_relations_correspondence_view(
            (transform,),
            changed_manifest,
            profiles=changed,
        )
        self.assertIs(
            unsupported.kind,
            model.k2.QualifiedViewOutcomeKind.UNSUPPORTED,
        )
        supported = model.issue_relations_correspondence_view(
            (transform,),
            changed_manifest,
            profiles=changed,
            profile_support=model.make_k3b_profile_support(changed),
        )
        self.assertIs(supported.kind, model.k2.QualifiedViewOutcomeKind.AFFIRMATIVE)
        assert type(baseline.value) is model.IssuedRelationsCorrespondenceView
        assert type(supported.value) is model.IssuedRelationsCorrespondenceView
        self.assertNotEqual(baseline_id, changed_id)
        self.assertNotEqual(
            baseline.value.source_binding.owner_binding_payload,
            supported.value.source_binding.owner_binding_payload,
        )

    def test_supported_profiles_refuse_undeclared_real_owner_subject_kinds(self) -> None:
        case = model.schnorr_case()
        interpretation = model.k2.ChallengeInterpretation.FIAT_SHAMIR
        baseline = model.K3B_SEMANTIC_PROFILES
        relation_id = model.relation_interface_id(case.relation_interfaces[0])
        transform = model.RelationTransform(
            "undeclared-transform-probe",
            (relation_id,),
            (relation_id,),
            model.IDENTITY_CODEC,
        )
        interface_required = model._PIR_SOURCE_AUTHORITY_SUBJECT_KINDS | {
            "pir.protocol-interface"
        }
        for omitted_kind in sorted(interface_required):
            with self.subTest(interface_omitted_kind=omitted_kind):
                interface_profile = replace(
                    baseline.interface_plan,
                    supported_subject_kinds=tuple(
                        item
                        for item in baseline.interface_plan.supported_subject_kinds
                        if item.value != omitted_kind
                    ),
                )
                relations_profile = replace(
                    baseline.relations_correspondence,
                    profile_imports=model._profile_imports(interface_profile),
                )
                interface_bundle = model.K3BSemanticProfiles(
                    baseline.k2_profiles,
                    interface_profile,
                    relations_profile,
                )
                interface = model.default_interface(
                    case.core,
                    case.construction,
                    interpretation,
                    expose_all_transports=True,
                    profiles=interface_bundle,
                )
                manifest = model.external_statement_read_manifest(
                    interface,
                    ("statement.statement",),
                )
                refused_interface = (
                    model.issue_protocol_interface_correspondence_view(
                        case.core,
                        case.construction,
                        interpretation,
                        interface,
                        manifest,
                        profiles=interface_bundle,
                        profile_support=model.make_k3b_profile_support(
                            interface_bundle
                        ),
                    )
                )
                self.assertIs(
                    refused_interface.kind,
                    model.k2.QualifiedViewOutcomeKind.REFUSED,
                )

        relations_required = model._RELATIONS_SOURCE_AUTHORITY_SUBJECT_KINDS | {
            "relations.transform"
        }
        for omitted_kind in sorted(relations_required):
            with self.subTest(relations_omitted_kind=omitted_kind):
                relations_profile = replace(
                    baseline.relations_correspondence,
                    supported_subject_kinds=tuple(
                        item
                        for item in baseline.relations_correspondence.supported_subject_kinds
                        if item.value != omitted_kind
                    ),
                )
                relations_bundle = model.K3BSemanticProfiles(
                    baseline.k2_profiles,
                    baseline.interface_plan,
                    relations_profile,
                )
                relation_manifest = model.claim_reduction_transform_read_manifest(
                    (
                        model.relation_transform_id(
                            transform,
                            profiles=relations_bundle,
                        ),
                    )
                )
                refused_relations = model.issue_relations_correspondence_view(
                    (transform,),
                    relation_manifest,
                    profiles=relations_bundle,
                    profile_support=model.make_k3b_profile_support(
                        relations_bundle
                    ),
                )
                self.assertIs(
                    refused_relations.kind,
                    model.k2.QualifiedViewOutcomeKind.REFUSED,
                )

    def test_upstream_interaction_change_rotates_both_k3b_languages(self) -> None:
        changed_k2 = model.k2.make_k2_semantic_profiles(
            interaction_law=b"zkc-k2-interaction-core-fresh-law-v1",
        )
        changed = model.make_k3b_semantic_profiles(k2_profiles=changed_k2)
        baseline = model.K3B_SEMANTIC_PROFILES
        self.assertNotEqual(
            self.identity("pir.protocol-interface", baseline),
            self.identity("pir.protocol-interface", changed),
        )
        self.assertNotEqual(
            self.identity("relations.protocol-binding", baseline),
            self.identity("relations.protocol-binding", changed),
        )
        self.assertEqual(
            model.fixture_semantic_ref(
                "foundation.canonical-algorithm",
                "profile-independent-fixture",
                profiles=baseline,
            ),
            model.fixture_semantic_ref(
                "foundation.canonical-algorithm",
                "profile-independent-fixture",
                profiles=changed,
            ),
        )

    def test_public_setup_law_is_local_but_transcript_rotates_k3b(self) -> None:
        baseline = model.K3B_SEMANTIC_PROFILES
        changed_public = model.make_k3b_semantic_profiles(
            k2_profiles=model.k2.make_k2_semantic_profiles(
                public_view_law=b"zkc-k2-unrelated-public-view-law-v1",
            )
        )
        changed_transcript = model.make_k3b_semantic_profiles(
            k2_profiles=model.k2.make_k2_semantic_profiles(
                transcript_fs_law=b"zkc-k2-used-transcript-fs-law-v1",
            )
        )
        for subject_kind in ("pir.prover-plan", "relations.interface"):
            with self.subTest(subject_kind=subject_kind):
                baseline_id = self.identity(subject_kind, baseline)
                self.assertEqual(
                    baseline_id,
                    self.identity(subject_kind, changed_public),
                )
                self.assertNotEqual(
                    baseline_id,
                    self.identity(subject_kind, changed_transcript),
                )
        self.assertEqual(
            baseline.interface_plan.identity,
            changed_public.interface_plan.identity,
        )
        self.assertEqual(
            baseline.relations_correspondence.identity,
            changed_public.relations_correspondence.identity,
        )
        self.assertNotEqual(
            baseline.interface_plan.identity,
            changed_transcript.interface_plan.identity,
        )
        self.assertNotEqual(
            baseline.relations_correspondence.identity,
            changed_transcript.relations_correspondence.identity,
        )

    def test_real_public_id_constructors_and_checks_use_selected_profiles(self) -> None:
        baseline = model.K3B_SEMANTIC_PROFILES
        changed_public = model.make_k3b_semantic_profiles(
            k2_profiles=model.k2.make_k2_semantic_profiles(
                public_view_law=b"zkc-k2-real-id-public-view-law-v1",
            )
        )
        changed_transcript = model.make_k3b_semantic_profiles(
            k2_profiles=model.k2.make_k2_semantic_profiles(
                transcript_fs_law=b"zkc-k2-real-id-transcript-fs-law-v1",
            )
        )
        case = model.verifier_private_case()
        construction, interpretation = axes(case)

        def relation(profiles: model.K3BSemanticProfiles) -> model.RelationInterface:
            return replace(
                case.relation_interfaces[0],
                definition_id=model.fixture_semantic_ref(
                    "relations.definition",
                    "fresh-statement",
                    profiles=profiles,
                ),
            )

        baseline_relation = relation(baseline)
        public_relation = relation(changed_public)
        transcript_relation = relation(changed_transcript)
        baseline_relation_id = model.relation_interface_id(
            baseline_relation,
            profiles=baseline,
        )
        public_relation_id = model.relation_interface_id(
            public_relation,
            profiles=changed_public,
        )
        transcript_relation_id = model.relation_interface_id(
            transcript_relation,
            profiles=changed_transcript,
        )
        self.assertEqual(baseline_relation_id, public_relation_id)
        self.assertNotEqual(baseline_relation_id, transcript_relation_id)

        baseline_plan_id = model.plan_id(
            case.core,
            construction,
            interpretation,
            case.plan,
            profiles=baseline,
        )
        self.assertEqual(
            baseline_plan_id,
            model.plan_id(
                case.core,
                construction,
                interpretation,
                case.plan,
                profiles=changed_public,
            ),
        )
        self.assertNotEqual(
            baseline_plan_id,
            model.plan_id(
                case.core,
                construction,
                interpretation,
                case.plan,
                profiles=changed_transcript,
            ),
        )
        surface = model.derive_plan_witness_surface(
            case.core,
            construction,
            interpretation,
            case.plan,
            profiles=changed_transcript,
        )
        surface_id = model.plan_witness_surface_id(
            surface,
            profiles=changed_transcript,
        )

        instances = tuple(
            replace(item, relation_interface_id=transcript_relation_id)
            for item in case.protocol_binding.instances
        )
        protocol_binding = replace(
            case.protocol_binding,
            relation_interface_ids=(transcript_relation_id,),
            instances=instances,
        )
        checked_protocol = model.check_protocol_relation_binding(
            case.core,
            construction,
            interpretation,
            (transcript_relation,),
            (),
            protocol_binding,
            profiles=changed_transcript,
        )
        model.require_whole_protocol_binding(checked_protocol)
        self.assertNotEqual(
            checked_protocol.binding_id,
            model.protocol_relation_binding_id(protocol_binding),
        )
        with self.assertRaisesRegex(model.RelationError, "unavailable"):
            model.check_protocol_relation_binding(
                case.core,
                construction,
                interpretation,
                (transcript_relation,),
                (),
                protocol_binding,
            )

        plan_binding = replace(
            case.plan_binding,
            plan_witness_surface_id=surface_id,
            relation_interface_id=transcript_relation_id,
        )
        checked_plan = model.check_plan_witness_binding(
            surface,
            transcript_relation,
            (),
            plan_binding,
            profiles=changed_transcript,
        )
        model.require_whole_plan_binding(checked_plan)
        self.assertNotEqual(
            checked_plan.binding_id,
            model.plan_witness_binding_id(plan_binding),
        )
        with self.assertRaisesRegex(model.RelationError, "wrong witness surface"):
            model.check_plan_witness_binding(
                surface,
                transcript_relation,
                (),
                plan_binding,
            )

        bridge = model.three_bridge_fixtures()[0]
        equation = model.r1cs_grounding_equation()
        coordinate = model.RelationRunCoordinate(
            model.RunCoordinateKind.STATEMENT,
            model.BindingRef("root", "statement"),
        )
        locality_subjects = (
            (
                model.value_bridge_id(bridge, profiles=baseline),
                model.value_bridge_id(bridge, profiles=changed_public),
                model.value_bridge_id(bridge, profiles=changed_transcript),
            ),
            (
                model.grounding_equation_id(equation, profiles=baseline),
                model.grounding_equation_id(equation, profiles=changed_public),
                model.grounding_equation_id(
                    equation,
                    profiles=changed_transcript,
                ),
            ),
            (
                model._grounded_value_id(coordinate, b"x", profiles=baseline),
                model._grounded_value_id(
                    coordinate,
                    b"x",
                    profiles=changed_public,
                ),
                model._grounded_value_id(
                    coordinate,
                    b"x",
                    profiles=changed_transcript,
                ),
            ),
        )
        for baseline_id, public_id, transcript_id in locality_subjects:
            self.assertEqual(baseline_id, public_id)
            self.assertNotEqual(baseline_id, transcript_id)

    def test_carrier_and_run_view_do_not_relabel_baseline_execution(self) -> None:
        changed = model.make_k3b_semantic_profiles(
            k2_profiles=model.k2.make_k2_semantic_profiles(
                transcript_fs_law=b"zkc-k2-carrier-runtime-transcript-law-v1",
            )
        )
        core, construction, invocation, strategy = model.k2.schnorr_fixture()
        interpretation = model.k2.ChallengeInterpretation.FIAT_SHAMIR
        graph = model.carrier_graph_for(
            core,
            interpretation,
            construction,
            profiles=changed,
        )
        carrier = model.lower_carrier(graph, profiles=changed)
        dependencies = model.CarrierDependencyEnvironment(construction)
        self.assertEqual(model.read_carrier(carrier, profiles=changed), graph)
        self.assertEqual(
            model.authenticate_carrier(
                carrier,
                dependencies,
                profiles=changed,
            ),
            graph,
        )
        with self.assertRaisesRegex(model.CarrierError, "asserted Protocol ID"):
            model.read_carrier(carrier)

        record = completed(
            model.k2.generate(
                core,
                construction,
                interpretation,
                invocation,
                strategy,
                profiles=changed.k2_profiles,
            )
        )
        manifest = (
            model.RelationRunCoordinate(
                model.RunCoordinateKind.STATEMENT,
                model.BindingRef("root", "statement"),
            ),
        )
        view = model.issue_relation_run_view(
            core,
            construction,
            invocation,
            record,
            manifest,
            profiles=changed,
        )
        self.assertEqual(
            view.protocol_id,
            model.protocol_id(
                core,
                construction,
                interpretation,
                profiles=changed,
            ),
        )
        with self.assertRaisesRegex(model.k2.ReplayError, "identity axes"):
            model.issue_relation_run_view(
                core,
                construction,
                invocation,
                record,
                manifest,
            )

    def test_local_profile_changes_rotate_only_their_dependency_cone(self) -> None:
        baseline = model.K3B_SEMANTIC_PROFILES
        changed_interface = model.make_k3b_semantic_profiles(
            interface_plan_law=b"zkc-k3b-interface-plan-law-v1",
        )
        changed_relations = model.make_k3b_semantic_profiles(
            relations_law=b"zkc-k3b-relations-correspondence-law-v1",
        )
        baseline_interface = self.identity("pir.prover-plan", baseline)
        baseline_relations = self.identity("relations.interface", baseline)
        self.assertNotEqual(
            baseline_interface,
            self.identity("pir.prover-plan", changed_interface),
        )
        self.assertNotEqual(
            baseline_relations,
            self.identity("relations.interface", changed_interface),
        )
        self.assertEqual(
            baseline_interface,
            self.identity("pir.prover-plan", changed_relations),
        )
        self.assertNotEqual(
            baseline_relations,
            self.identity("relations.interface", changed_relations),
        )
        self.assertEqual(
            baseline.k2_profiles.bundle,
            changed_interface.k2_profiles.bundle,
        )
        self.assertEqual(
            baseline.k2_profiles.bundle,
            changed_relations.k2_profiles.bundle,
        )


class InterfaceAndPlanTest(unittest.TestCase):
    def test_interface_separates_private_assignment_and_statement_coverage(self) -> None:
        case = model.verifier_private_case()
        private = next(
            item for item in case.interface.inputs if item.core_input == "verifier-secret"
        )
        self.assertIs(
            private.visibility, model.ExternalVisibility.VERIFIER_CONFIDENTIAL
        )
        with self.assertRaisesRegex(model.InterfaceError, "Statement coverage"):
            model.admit_interface(
                case.core,
                None,
                model.k2.ChallengeInterpretation.FRESH,
                replace(case.interface, statements=()),
            )

    def test_interface_checks_codec_kind_and_transport_occurrence(self) -> None:
        case = model.fri_oracle_case()
        with self.assertRaises(model.K3Error):
            model.admit_interface(
                case.core,
                case.construction,
                model.k2.ChallengeInterpretation.FIAT_SHAMIR,
                replace(
                    case.interface,
                    inputs=(
                        replace(
                            case.interface.inputs[0],
                            codec_id=model.fixture_semantic_ref(
                                "relations.definition", "not-codec"
                            ),
                        ),
                    )
                    + case.interface.inputs[1:],
                ),
            )
        exposure = case.interface.transports[0]
        with self.assertRaisesRegex(model.InterfaceError, "role disagrees"):
            model.admit_interface(
                case.core,
                case.construction,
                model.k2.ChallengeInterpretation.FIAT_SHAMIR,
                replace(
                    case.interface,
                    transports=(
                        replace(exposure, role=model.TransportRole.ORACLE_ANSWER),
                    )
                    + case.interface.transports[1:],
                ),
            )
        for forbidden_kind in (
            model.k2.OccurrenceKind.CHECK,
            model.k2.OccurrenceKind.TERMINAL,
        ):
            with self.subTest(forbidden_kind=forbidden_kind):
                occurrence = next(
                    item
                    for item in case.core.schedule
                    if item.kind is forbidden_kind
                )
                with self.assertRaisesRegex(model.InterfaceError, "role disagrees"):
                    model.admit_interface(
                        case.core,
                        case.construction,
                        model.k2.ChallengeInterpretation.FIAT_SHAMIR,
                        replace(
                            case.interface,
                            transports=case.interface.transports
                            + (
                                model.TransportExposure(
                                    f"effect.invalid-{forbidden_kind.value}",
                                    occurrence.name,
                                    model.TransportRole.ORACLE_ANSWER,
                                ),
                            ),
                        ),
                    )
        exposed = {
            item.kind
            for item in case.core.schedule
            if item.name in {x.occurrence for x in case.interface.transports}
        }
        self.assertNotIn(model.k2.OccurrenceKind.CHECK, exposed)
        self.assertNotIn(model.k2.OccurrenceKind.TERMINAL, exposed)

    def test_plan_requires_all_decisions_and_prior_only_reads(self) -> None:
        case = model.schnorr_case()
        missing = replace(case.plan, decision_routes=case.plan.decision_routes[1:])
        model.admit_plan(
            case.core,
            case.construction,
            model.k2.ChallengeInterpretation.FIAT_SHAMIR,
            missing,
        )
        with self.assertRaisesRegex(model.PlanError, "exactly every"):
            model.check_plan_realizes(
                case.core,
                case.construction,
                model.k2.ChallengeInterpretation.FIAT_SHAMIR,
                missing,
            )
        first = case.plan.decision_routes[0]
        future = replace(
            first,
            reads=first.reads
            + (
                model.PlanRead(
                    model.PlanReadKind.PRIOR_OCCURRENCE_VIEW, "response"
                ),
            ),
        )
        future_plan = replace(
            case.plan,
            decision_routes=(future,) + case.plan.decision_routes[1:],
        )
        model.admit_plan(
            case.core,
            case.construction,
            model.k2.ChallengeInterpretation.FIAT_SHAMIR,
            future_plan,
        )
        with self.assertRaisesRegex(model.PlanError, "all-path K2 guaranteed read"):
            model.check_plan_realizes(
                case.core,
                case.construction,
                model.k2.ChallengeInterpretation.FIAT_SHAMIR,
                future_plan,
            )

    def test_plan_realizes_refuses_prior_conditionally_skipped_read(self) -> None:
        core = model.k2.Core(
            inputs=(
                model.k2.InputDecl(
                    "flag",
                    model.k2.InputRole.PUBLIC_CONTEXT,
                    value_sort=model.k2.ValueSort.BOOL,
                ),
            ),
            scopes=(model.k2.ScopeDecl("root", None, None),),
            schedule=(
                model.k2.Occurrence(
                    "conditional",
                    model.k2.OccurrenceKind.VERIFIER_MESSAGE,
                    guard=model.k2.Predicate(
                        model.k2.PredicateKind.BOOL,
                        (model.k2.ValueRef.input("flag"),),
                    ),
                    verifier_rule=model.k2.VerifierRule(
                        model.k2.VerifierRuleKind.CONSTANT_INT, (7,)
                    ),
                ),
                model.k2.Occurrence("move", model.k2.OccurrenceKind.PROVER_MESSAGE),
                model.k2.Occurrence("terminal", model.k2.OccurrenceKind.TERMINAL),
            ),
        )
        interpretation = model.k2.ChallengeInterpretation.FRESH
        plan = model.ProverPlan(
            model.protocol_id(core, None, interpretation),
            (),
            (),
            (),
            (
                model.DecisionRoute(
                    "move",
                    model.MoveKind.MESSAGE_VALUE,
                    (
                        model.PlanRead(
                            model.PlanReadKind.PRIOR_OCCURRENCE_VIEW,
                            "conditional",
                        ),
                    ),
                    (),
                    model._algorithm("conditional-read"),
                ),
            ),
            (),
        )
        model.admit_plan(core, None, interpretation, plan)
        with self.assertRaisesRegex(model.PlanError, "all-path K2 guaranteed read"):
            model.check_plan_realizes(core, None, interpretation, plan)

    def test_plan_read_visibility_is_distinct_from_public_exportability(self) -> None:
        core = model.k2.Core(
            inputs=(
                model.k2.InputDecl(
                    "verifier-secret", model.k2.InputRole.VERIFIER_PRIVATE
                ),
            ),
            scopes=(model.k2.ScopeDecl("root", None, None),),
            schedule=(
                model.k2.Occurrence(
                    "disclosed",
                    model.k2.OccurrenceKind.VERIFIER_MESSAGE,
                    dependencies=(model.k2.ValueRef.input("verifier-secret"),),
                    verifier_rule=model.k2.VerifierRule(
                        model.k2.VerifierRuleKind.COPY
                    ),
                ),
                model.k2.Occurrence("move", model.k2.OccurrenceKind.PROVER_MESSAGE),
                model.k2.Occurrence("terminal", model.k2.OccurrenceKind.TERMINAL),
            ),
        )
        interpretation = model.k2.ChallengeInterpretation.FRESH
        plan = model.ProverPlan(
            model.protocol_id(core, None, interpretation),
            (),
            (),
            (),
            (
                model.DecisionRoute(
                    "move",
                    model.MoveKind.MESSAGE_VALUE,
                    (
                        model.PlanRead(
                            model.PlanReadKind.PRIOR_OCCURRENCE_VIEW, "disclosed"
                        ),
                    ),
                    (),
                    model._algorithm("use-disclosed-value"),
                ),
            ),
            (),
        )
        model.check_plan_realizes(core, None, interpretation, plan)
        self.assertNotIn("disclosed", model._public_occurrence_names(core))

    def test_plan_realizes_scope_gates_public_input_reads(self) -> None:
        core = model.k2.Core(
            inputs=(
                model.k2.InputDecl(
                    "late-public",
                    model.k2.InputRole.PUBLIC_CONTEXT,
                    scope="child",
                ),
            ),
            scopes=(
                model.k2.ScopeDecl("root", None, None),
                model.k2.ScopeDecl("child", "root", "open-child"),
            ),
            schedule=(
                model.k2.Occurrence("early", model.k2.OccurrenceKind.PROVER_MESSAGE),
                model.k2.Occurrence(
                    "open-child",
                    model.k2.OccurrenceKind.VERIFIER_MESSAGE,
                    verifier_rule=model.k2.VerifierRule(
                        model.k2.VerifierRuleKind.CONSTANT_INT, (1,)
                    ),
                ),
                model.k2.Occurrence("late", model.k2.OccurrenceKind.PROVER_MESSAGE),
                model.k2.Occurrence("terminal", model.k2.OccurrenceKind.TERMINAL),
            ),
        )
        interpretation = model.k2.ChallengeInterpretation.FRESH
        public_read = model.PlanRead(
            model.PlanReadKind.PUBLIC_INPUT_VIEW, "late-public"
        )
        early = model.DecisionRoute(
            "early",
            model.MoveKind.MESSAGE_VALUE,
            (public_read,),
            (),
            model._algorithm("early-public-read"),
        )
        late = model.DecisionRoute(
            "late",
            model.MoveKind.MESSAGE_VALUE,
            (),
            (),
            model._algorithm("late-public-read"),
        )
        plan = model.ProverPlan(
            model.protocol_id(core, None, interpretation),
            (),
            (),
            (),
            (early, late),
            (),
        )
        model.admit_plan(core, None, interpretation, plan)
        with self.assertRaisesRegex(model.PlanError, "before its K2 scope opens"):
            model.check_plan_realizes(core, None, interpretation, plan)

        after_open = replace(
            plan,
            decision_routes=(
                replace(early, reads=()),
                replace(late, reads=(public_read,)),
            ),
        )
        model.check_plan_realizes(core, None, interpretation, after_open)

    def test_state_and_derived_export_types_are_checked(self) -> None:
        case = model.nova_case()
        route = replace(case.plan.decision_routes[0], state_after=())
        with self.assertRaisesRegex(model.PlanError, "total state-after"):
            model.admit_plan(
                case.core,
                case.construction,
                model.k2.ChallengeInterpretation.FIAT_SHAMIR,
                replace(
                    case.plan,
                    decision_routes=(route,) + case.plan.decision_routes[1:],
                ),
            )
        with self.assertRaisesRegex(model.PlanError, "source output"):
            model.admit_plan(
                case.core,
                case.construction,
                model.k2.ChallengeInterpretation.FIAT_SHAMIR,
                replace(
                    case.plan,
                    exports=(replace(case.plan.exports[0], value_type=model.NAT),),
                ),
            )

    def test_witness_surface_identity_excludes_plan_algorithm(self) -> None:
        case = model.nova_case()
        changed_route = replace(
            case.plan.decision_routes[0],
            implementation_algorithm_id=model._algorithm("alternate-left"),
        )
        changed = replace(
            case.plan,
            decision_routes=(changed_route,) + case.plan.decision_routes[1:],
        )
        surface = model.derive_plan_witness_surface(
            case.core,
            case.construction,
            model.k2.ChallengeInterpretation.FIAT_SHAMIR,
            case.plan,
        )
        changed_surface = model.derive_plan_witness_surface(
            case.core,
            case.construction,
            model.k2.ChallengeInterpretation.FIAT_SHAMIR,
            changed,
        )
        self.assertEqual(
            model.plan_witness_surface_id(surface),
            model.plan_witness_surface_id(changed_surface),
        )
        self.assertNotEqual(
            model.plan_id(
                case.core,
                case.construction,
                model.k2.ChallengeInterpretation.FIAT_SHAMIR,
                case.plan,
            ),
            model.plan_id(
                case.core,
                case.construction,
                model.k2.ChallengeInterpretation.FIAT_SHAMIR,
                changed,
            ),
        )
        self.assertTrue(model.plan_is_relation_free_by_construction())
        self.assertNotIn("source_kind", {item.name for item in fields(model.PlanExport)})


class CorrespondenceOwnerViewTest(unittest.TestCase):
    def test_interface_manifest_closes_over_assignments_slots_and_codecs(self) -> None:
        case = model.schnorr_case()
        requested = (
            model.ProtocolInterfaceRead(
                model.ProtocolInterfaceReadKind.STATEMENT_MEMBER,
                "statement.statement",
            ),
            model.ProtocolInterfaceRead(
                model.ProtocolInterfaceReadKind.TRANSPORT_ENTRY,
                "commitment",
            ),
        )
        closed = model.required_protocol_interface_read_closure(
            case.interface,
            requested,
        )
        self.assertEqual(
            {item.kind for item in closed},
            set(model.ProtocolInterfaceReadKind),
        )
        manifest = model.CorrespondenceReadManifest(closed)
        outcome = model.issue_protocol_interface_correspondence_view(
            case.core,
            case.construction,
            model.k2.ChallengeInterpretation.FIAT_SHAMIR,
            case.interface,
            manifest,
        )
        self.assertIs(outcome.kind, model.k2.QualifiedViewOutcomeKind.AFFIRMATIVE)
        self.assertIs(type(outcome.value), model.IssuedProtocolInterfaceCorrespondenceView)
        issued = outcome.value
        assert type(issued) is model.IssuedProtocolInterfaceCorrespondenceView
        self.assertEqual(issued.view.requested_reads, closed)
        self.assertIs(issued.source_binding.owner_local_coordinate, issued.view)
        self.assertIs(issued.capability.view, issued.view)
        self.assertIs(issued.capability.source_binding, issued.source_binding)
        self.assertTrue(
            model.validate_issued_protocol_interface_correspondence_view(issued)
        )

    def test_interface_view_refuses_incomplete_and_aliased_source_reads(self) -> None:
        case = model.schnorr_case()
        complete = model.external_statement_read_manifest(
            case.interface,
            ("statement.statement",),
        )
        incomplete = model.CorrespondenceReadManifest(
            tuple(
                item
                for item in complete.protocol_interface
                if item.kind is not model.ProtocolInterfaceReadKind.INTERFACE_CODEC
            )
        )
        outcome = model.issue_protocol_interface_correspondence_view(
            case.core,
            case.construction,
            model.k2.ChallengeInterpretation.FIAT_SHAMIR,
            case.interface,
            incomplete,
        )
        self.assertIs(
            outcome.kind,
            model.k2.QualifiedViewOutcomeKind.MISSING_DEPENDENCY,
        )

        colliding_transport = replace(
            case.interface.transports[0],
            external_coordinate=case.interface.inputs[0].external_coordinate,
        )
        aliased = replace(
            case.interface,
            transports=(colliding_transport,) + case.interface.transports[1:],
        )
        slot_read = model.CorrespondenceReadManifest(
            (
                model.ProtocolInterfaceRead(
                    model.ProtocolInterfaceReadKind.EXTERNAL_SLOT,
                    case.interface.inputs[0].external_coordinate,
                ),
            )
        )
        aliased_outcome = model.issue_protocol_interface_correspondence_view(
            case.core,
            case.construction,
            model.k2.ChallengeInterpretation.FIAT_SHAMIR,
            aliased,
            slot_read,
        )
        self.assertIs(
            aliased_outcome.kind,
            model.k2.QualifiedViewOutcomeKind.MALFORMED,
        )

    def test_relation_transform_read_is_owner_issued_and_exact(self) -> None:
        case = model.schnorr_case()
        relation_id = model.relation_interface_id(case.relation_interfaces[0])
        transform = model.RelationTransform(
            "schnorr-self-reduction",
            (relation_id,),
            (relation_id,),
            model.IDENTITY_CODEC,
        )
        transform_id = model.relation_transform_id(transform)
        manifest = model.claim_reduction_transform_read_manifest((transform_id,))
        outcome = model.issue_relations_correspondence_view(
            (transform,),
            manifest,
        )
        self.assertIs(outcome.kind, model.k2.QualifiedViewOutcomeKind.AFFIRMATIVE)
        self.assertIs(type(outcome.value), model.IssuedRelationsCorrespondenceView)
        issued = outcome.value
        assert type(issued) is model.IssuedRelationsCorrespondenceView
        self.assertEqual(issued.view.requested_reads, manifest.relations)
        self.assertEqual(issued.view.entries[0].value, transform)
        self.assertIs(issued.source_binding.owner_local_coordinate, issued.view)
        self.assertIs(issued.capability.view, issued.view)
        self.assertIs(issued.capability.source_binding, issued.source_binding)
        self.assertTrue(model.validate_issued_relations_correspondence_view(issued))

        missing = model.issue_relations_correspondence_view((), manifest)
        self.assertIs(
            missing.kind,
            model.k2.QualifiedViewOutcomeKind.MISSING_DEPENDENCY,
        )

        extra = model.RelationTransform(
            "unrequested-extra-transform",
            (relation_id,),
            (relation_id,),
            model.IDENTITY_CODEC,
        )
        extra_outcome = model.issue_relations_correspondence_view(
            (transform, extra),
            manifest,
        )
        self.assertIs(
            extra_outcome.kind,
            model.k2.QualifiedViewOutcomeKind.MALFORMED,
        )

    def test_correspondence_views_cannot_be_self_authored(self) -> None:
        with self.assertRaises(model.InterfaceError):
            model.ProtocolInterfaceCorrespondenceView(
                model.IDENTITY_CODEC,
                (),
                (),
                object(),
            )
        with self.assertRaises(model.RelationError):
            model.RelationsCorrespondenceView((), (), object())

    def test_interface_authority_refuses_copy_reconstruction_and_wrong_purpose(self) -> None:
        case = model.schnorr_case()
        manifest = model.external_statement_read_manifest(
            case.interface,
            ("statement.statement",),
        )
        issued = model.issue_protocol_interface_correspondence_view(
            case.core,
            case.construction,
            model.k2.ChallengeInterpretation.FIAT_SHAMIR,
            case.interface,
            manifest,
        ).value
        alternate = model.issue_protocol_interface_correspondence_view(
            case.core,
            case.construction,
            model.k2.ChallengeInterpretation.FIAT_SHAMIR,
            case.interface,
            manifest,
            purpose_id=model._source_authority_id(
                model.PIR_INTERFACE_PLAN_PROFILE,
                "pir.source-purpose",
                model.k1.DatumRecord(
                    ((0, model.k1.Symbol("alternate-interface-purpose")),)
                ),
            ),
        ).value
        assert type(issued) is model.IssuedProtocolInterfaceCorrespondenceView
        assert type(alternate) is model.IssuedProtocolInterfaceCorrespondenceView
        self.assertFalse(
            model.validate_issued_protocol_interface_correspondence_view(
                issued,
                expected_purpose_id=alternate.capability.purpose_id,
            )
        )
        for live in (issued.source_binding, issued.capability, issued):
            with self.assertRaises((model.K3Error, model.k1.ModelError)):
                copy.copy(live)
            with self.assertRaises((model.K3Error, model.k1.ModelError)):
                copy.deepcopy(live)
            with self.assertRaises((model.K3Error, model.k1.ModelError)):
                pickle.dumps(live)
        binding = issued.source_binding
        reconstructed_binding = model.k1.OwnerLocalSourceAuthorityBinding(
            binding.owner_domain,
            binding.capability_family,
            binding.owner_local_coordinate,
            binding.owner_binding_payload,
            binding.operation_policy,
            binding.owner_policy_closure,
            binding.capability_requirement,
        )
        forged = replace(issued, source_binding=reconstructed_binding)
        self.assertFalse(
            model.validate_issued_protocol_interface_correspondence_view(forged)
        )
        with self.assertRaises(model.InterfaceError):
            model.ProtocolInterfaceViewCapability(
                issued.view,
                issued.source_binding,
                issued.capability.consumer_id,
                issued.capability.purpose_id,
                case.interface,
                object(),
            )

    def test_relations_authority_refuses_cross_family_and_reconstruction(self) -> None:
        case = model.schnorr_case()
        relation_id = model.relation_interface_id(case.relation_interfaces[0])
        transform = model.RelationTransform(
            "schnorr-authority-transform",
            (relation_id,),
            (relation_id,),
            model.IDENTITY_CODEC,
        )
        manifest = model.claim_reduction_transform_read_manifest(
            (model.relation_transform_id(transform),)
        )
        issued = model.issue_relations_correspondence_view(
            (transform,),
            manifest,
        ).value
        assert type(issued) is model.IssuedRelationsCorrespondenceView
        self.assertTrue(model.validate_issued_relations_correspondence_view(issued))
        for live in (issued.source_binding, issued.capability, issued):
            with self.assertRaises((model.K3Error, model.k1.ModelError)):
                copy.copy(live)
            with self.assertRaises((model.K3Error, model.k1.ModelError)):
                pickle.dumps(live)
        binding = issued.source_binding
        reconstructed_binding = model.k1.OwnerLocalSourceAuthorityBinding(
            binding.owner_domain,
            binding.capability_family,
            binding.owner_local_coordinate,
            binding.owner_binding_payload,
            binding.operation_policy,
            binding.owner_policy_closure,
            binding.capability_requirement,
        )
        forged = replace(issued, source_binding=reconstructed_binding)
        self.assertFalse(
            model.validate_issued_relations_correspondence_view(forged)
        )
        interface_manifest = model.external_statement_read_manifest(
            case.interface,
            ("statement.statement",),
        )
        interface_issued = model.issue_protocol_interface_correspondence_view(
            case.core,
            case.construction,
            model.k2.ChallengeInterpretation.FIAT_SHAMIR,
            case.interface,
            interface_manifest,
        ).value
        assert type(interface_issued) is model.IssuedProtocolInterfaceCorrespondenceView
        cross_family = replace(
            issued,
            source_binding=interface_issued.source_binding,
        )
        self.assertFalse(
            model.validate_issued_relations_correspondence_view(cross_family)
        )


class RelationDefinitionOwnerViewTest(unittest.TestCase):
    def test_schnorr_definition_is_profiled_and_exports_exact_fixed_setup(self) -> None:
        case = model.schnorr_case()
        definition = case.definition_sources[0]
        self.assertEqual(
            case.definitions[0].definition_id,
            model.schnorr_relation_definition_id(definition),
        )
        manifest = model.schnorr_fixed_setup_manifest(definition)
        outcome = model.issue_relation_definition_view(definition, manifest)
        self.assertIs(outcome.kind, model.k2.QualifiedViewOutcomeKind.AFFIRMATIVE)
        issued = outcome.value
        assert type(issued) is model.IssuedRelationDefinitionView
        self.assertTrue(model.validate_issued_relation_definition_view(issued))
        self.assertEqual(
            {entry.coordinate.field: entry.value for entry in issued.view.entries},
            {
                model.RelationDefinitionField.GENERATOR: 2,
                model.RelationDefinitionField.SCALAR_MODULUS: 11,
                model.RelationDefinitionField.GROUP_MODULUS: 23,
            },
        )
        assert case.invocation is not None
        self.assertEqual(
            tuple(case.invocation.values[name] for name in ("g", "q", "p")),
            (definition.generator, definition.scalar_modulus, definition.group_modulus),
        )

    def test_definition_view_refuses_substitution_wrong_profile_and_reconstruction(
        self,
    ) -> None:
        definition = model.selected_schnorr_relation_definition()
        manifest = model.schnorr_fixed_setup_manifest(definition)
        substituted = replace(definition, generator=3)
        substitution = model.issue_relation_definition_view(substituted, manifest)
        self.assertIs(
            substitution.kind,
            model.k2.QualifiedViewOutcomeKind.MALFORMED,
        )

        changed = model.make_k3b_semantic_profiles(
            relations_law=b"relations-definition-owner-view-profile-locality-v1"
        )
        changed_manifest = model.schnorr_fixed_setup_manifest(
            definition,
            profiles=changed,
        )
        changed_outcome = model.issue_relation_definition_view(
            definition,
            changed_manifest,
            profiles=changed,
            profile_support=model.make_k3b_profile_support(changed),
        )
        self.assertIs(
            changed_outcome.kind,
            model.k2.QualifiedViewOutcomeKind.AFFIRMATIVE,
        )
        issued = changed_outcome.value
        assert type(issued) is model.IssuedRelationDefinitionView
        self.assertFalse(model.validate_issued_relation_definition_view(issued))
        self.assertTrue(
            model.validate_issued_relation_definition_view(
                issued,
                profiles=changed,
                profile_support=model.make_k3b_profile_support(changed),
            )
        )
        self.assertFalse(
            model.validate_issued_relation_definition_view(
                issued,
                profiles=changed,
                profile_support=model.make_k3b_profile_support(changed),
                expected_purpose_id=model._algorithm("wrong-definition-view-purpose"),
            )
        )
        for live in (issued.source_binding, issued.capability, issued):
            with self.assertRaises((model.K3Error, model.k1.ModelError)):
                copy.copy(live)
            with self.assertRaises((model.K3Error, model.k1.ModelError)):
                pickle.dumps(live)
        binding = issued.source_binding
        reconstructed_binding = model.k1.OwnerLocalSourceAuthorityBinding(
            binding.owner_domain,
            binding.capability_family,
            binding.owner_local_coordinate,
            binding.owner_binding_payload,
            binding.operation_policy,
            binding.owner_policy_closure,
            binding.capability_requirement,
        )
        forged = replace(issued, source_binding=reconstructed_binding)
        self.assertFalse(
            model.validate_issued_relation_definition_view(
                forged,
                profiles=changed,
                profile_support=model.make_k3b_profile_support(changed),
            )
        )


class RelationBindingTest(unittest.TestCase):
    def test_cases_pass_independent_protocol_and_plan_binding_checks(self) -> None:
        for builder in (
            model.schnorr_case,
            model.verifier_private_case,
            model.fri_oracle_case,
            model.r1cs_case,
            model.nova_case,
        ):
            with self.subTest(case=builder.__name__):
                case = builder()
                protocol = protocol_check(case)
                plan = plan_check(case)
                model.require_whole_protocol_binding(protocol)
                model.require_whole_plan_binding(plan)

    def test_relation_has_four_roles_and_bindings_are_split(self) -> None:
        relation = model.fri_oracle_case().relation_interfaces[0]
        self.assertTrue(relation.public_instance)
        self.assertTrue(relation.private_witness)
        self.assertTrue(relation.oracle_statements)
        self.assertTrue(relation.phase_inputs)
        self.assertNotIn(
            "plan", {item.name for item in fields(model.ProtocolRelationBinding)}
        )
        self.assertNotIn(
            "protocol_id", {item.name for item in fields(model.PlanWitnessBinding)}
        )
        self.assertEqual(
            {item.name for item in fields(model.PlanWitnessBinding)},
            {
                "plan_witness_surface_id",
                "relation_interface_id",
                "witness_edges",
            },
        )
        self.assertEqual(
            {item.name for item in fields(model.WitnessSlotEdge)},
            {"slot", "witness_surface_key", "value_relation"},
        )

    def test_missing_oracle_and_witness_edges_are_not_whole(self) -> None:
        fri = model.fri_oracle_case()
        protocol = protocol_check(fri, replace(fri.protocol_binding, oracle_edges=()))
        self.assertEqual(protocol.missing_oracle, (("fri-instance", "oracle"),))
        with self.assertRaises(model.RelationError):
            model.require_whole_protocol_binding(protocol)
        schnorr = model.schnorr_case()
        plan = plan_check(
            schnorr, replace(schnorr.plan_binding, witness_edges=())
        )
        self.assertEqual(plan.missing_witness, ("secret",))

    def test_checked_result_refuses_post_check_binding_substitution(self) -> None:
        case = model.schnorr_case()
        checked = protocol_check(case)
        altered = replace(
            case.protocol_binding,
            public_edges=(
                replace(
                    case.protocol_binding.public_edges[0],
                    source=model.k2.ValueRef.input("statement"),
                ),
            ),
        )
        with self.assertRaises(model.RelationError):
            model.require_whole_protocol_binding(replace(checked, binding=altered))

    def test_relation_semantic_reference_subject_kinds_are_checked(self) -> None:
        with self.assertRaises(model.K3Error):
            model.admit_relation_definition_ref(
                model.RelationDefinitionRef(
                    model.fixture_semantic_ref(
                        "foundation.canonical-algorithm", "not-a-definition"
                    )
                )
            )
        case = model.fri_oracle_case()
        oracle = case.relation_interfaces[0].oracle_statements[0]
        with self.assertRaises(model.K3Error):
            model.relation_interface_id(
                replace(
                    case.relation_interfaces[0],
                    oracle_statements=(
                        replace(
                            oracle,
                            access_law_id=model._algorithm("wrong-access-law"),
                        ),
                    ),
                )
            )
        definition = model.fixture_relation_definition_ref("semantic-relation")
        self.assertEqual(
            {item.name for item in fields(model.RelationDefinitionRef)},
            {"definition_id"},
        )
        evaluator_a = model._algorithm("evaluator-a")
        evaluator_b = model._algorithm("evaluator-b")
        self.assertNotEqual(evaluator_a, evaluator_b)
        self.assertEqual(
            definition.definition_id,
            model.fixture_relation_definition_ref(
                "semantic-relation"
            ).definition_id,
        )


class BridgeAndArtifactTest(unittest.TestCase):
    def test_three_bridge_lanes_are_typed_and_non_substitutable(self) -> None:
        equivalence, embedding, lossy = model.three_bridge_fixtures()
        for bridge in (equivalence, embedding, lossy):
            model.admit_value_bridge(bridge)
        with self.assertRaises(model.BridgeError):
            model.admit_value_bridge(replace(equivalence, inverse_algorithm_id=None))
        with self.assertRaises(model.BridgeError):
            model.admit_value_bridge(
                replace(embedding, collision_relation_id=lossy.collision_relation_id)
            )

    def test_validation_basis_is_external_to_bridge_meaning_and_identity(self) -> None:
        _, _, lossy = model.three_bridge_fixtures()
        self.assertNotIn(
            "law_basis_id", {item.name for item in fields(model.ValueBridge)}
        )
        basis_a = model.fixture_semantic_ref(
            "relations.value-bridge-law", "external-basis-a"
        )
        basis_b = model.fixture_semantic_ref(
            "relations.value-bridge-law", "external-basis-b"
        )
        self.assertNotEqual(basis_a, basis_b)
        bridge_id = model.value_bridge_id(lossy)
        for external_basis in (basis_a, basis_b):
            with self.subTest(external_basis=external_basis):
                self.assertEqual(bridge_id, model.value_bridge_id(lossy))

    def test_bridge_is_resolved_typed_and_directed_on_witness_edge(self) -> None:
        case = model.schnorr_case()
        bridge = model.ValueBridge(
            "nat-to-bytes",
            model.ValueBridgeLane.DIRECTIONAL_LOSSY,
            model.NAT,
            model.BYTES,
            model._algorithm("nat-to-bytes"),
            collision_relation_id=model.fixture_semantic_ref(
                "relations.definition", "nat-collision"
            ),
            source_premise_id=model.fixture_semantic_ref(
                "relations.loss-source-premise", "nat-premise"
            ),
            quantitative_export_id=model.fixture_semantic_ref(
                "relations.loss-export", "nat-loss-export"
            ),
        )
        interface = replace(
            case.relation_interfaces[0],
            private_witness=(model.RelationSlot("secret", model.BYTES),),
        )
        relation_id = model.relation_interface_id(interface)
        binding = replace(
            case.plan_binding,
            relation_interface_id=relation_id,
            witness_edges=(
                replace(
                    case.plan_binding.witness_edges[0],
                    value_relation=model.ValueRelation(
                        model.value_bridge_id(bridge), model.BridgeDirection.FORWARD
                    ),
                ),
            ),
        )
        surface = model.derive_plan_witness_surface(
            case.core,
            case.construction,
            model.k2.ChallengeInterpretation.FIAT_SHAMIR,
            case.plan,
        )
        checked = model.check_plan_witness_binding(
            surface, interface, (bridge,), binding
        )
        model.require_whole_plan_binding(checked)
        backward = replace(
            binding.witness_edges[0],
            value_relation=model.ValueRelation(
                model.value_bridge_id(bridge), model.BridgeDirection.BACKWARD
            ),
        )
        with self.assertRaises(model.BridgeError):
            model.check_plan_witness_binding(
                surface,
                interface,
                (bridge,),
                replace(binding, witness_edges=(backward,)),
            )

    def test_equation_identity_binds_constant_and_typed_algorithm_abi(self) -> None:
        equation = model.r1cs_grounding_equation()
        replacement = model.k1.admit_value(
            model.BYTES32, model.k1.BytesValue(b"e" * 32)
        )
        changed = replace(
            equation,
            nodes=tuple(
                replace(node, reference=replacement)
                if node.name == "declared"
                else node
                for node in equation.nodes
            ),
        )
        self.assertNotEqual(
            model.grounding_equation_id(equation),
            model.grounding_equation_id(changed),
        )
        digest = model.FactType(model.FactKind.VALUE, model.BYTES32)
        typed = model.TypedAlgorithmRef(
            model._algorithm("digest-normalize"),
            model.fixture_semantic_ref(
                "foundation.evaluation-contract", "digest-contract"
            ),
            (digest,),
            digest,
        )
        apply = model.EquationNode(
            "normalized", model.EquationOp.APPLY, digest, ("observed",), typed
        )
        nodes = (equation.nodes[0], apply, equation.nodes[1]) + (
            replace(equation.nodes[2], dependencies=("normalized", "declared")),
        )
        model.admit_grounding_equation(replace(equation, nodes=nodes))
        with self.assertRaises(model.K3Error):
            model.admit_grounding_equation(
                replace(
                    equation,
                    nodes=(
                        equation.nodes[0],
                        replace(
                            apply,
                            reference=replace(
                                typed,
                                evaluation_contract_id=model._algorithm(
                                    "not-evaluation-contract"
                                ),
                            ),
                        ),
                        equation.nodes[1],
                        replace(
                            equation.nodes[2],
                            dependencies=("normalized", "declared"),
                        ),
                    ),
                )
            )

    def test_observation_state_and_selector_bounds_are_real(self) -> None:
        equation = model.r1cs_grounding_equation()
        unread = model.ArtifactObservation(
            equation.schema,
            tuple(
                model.ArtifactFactObservation(
                    fact.name, model.ObservationState.UNREAD
                )
                for fact in equation.schema.facts
            ),
        )
        observed = replace(
            unread,
            facts=tuple(
                replace(item, state=model.ObservationState.OBSERVED)
                for item in unread.facts
            ),
        )
        model.admit_artifact_observation(unread)
        model.admit_artifact_observation(observed)
        self.assertNotEqual(unread, observed)
        with self.assertRaises(model.ArtifactError):
            model.admit_grounding_equation(
                replace(
                    equation,
                    selectors=(
                        replace(
                            equation.selectors[0], index=model.MAX_SELECTOR_INDEX + 1
                        ),
                    ),
                )
            )

    def test_equation_cycle_and_unread_value_are_refused(self) -> None:
        equation = model.r1cs_grounding_equation()
        cyclic = replace(equation.nodes[0], dependencies=("matches",))
        with self.assertRaisesRegex(model.ArtifactError, "cyclic"):
            model.admit_grounding_equation(
                replace(equation, nodes=(cyclic,) + equation.nodes[1:])
            )
        schema = equation.schema
        observations = tuple(
            model.ArtifactFactObservation(fact.name, model.ObservationState.UNREAD)
            for fact in schema.facts
        )
        with self.assertRaisesRegex(model.ArtifactError, "Unread"):
            model.admit_artifact_observation(
                model.ArtifactObservation(
                    schema,
                    (replace(observations[0], values=(1,)),) + observations[1:],
                )
            )


class RunGroundingTest(unittest.TestCase):
    def test_schnorr_executes_via_k2_and_view_is_exact_and_immutable(self) -> None:
        case = model.schnorr_case()
        view = issue_case_view(case)
        result = model.ground_whole_correspondence(protocol_check(case), view)
        self.assertEqual(len(result.public_slots), 1)
        self.assertEqual(view.manifest, binding_manifest(case.protocol_binding))
        self.assertNotIn(
            "completed_record", {item.name for item in fields(model.RelationRunView)}
        )
        self.assertNotIn(
            "invocation_id", {item.name for item in fields(model.RelationRunView)}
        )
        with self.assertRaises((FrozenInstanceError, AttributeError)):
            view.entries = ()  # type: ignore[misc]

    def test_oracle_executes_but_publication_material_is_not_exported(self) -> None:
        case = model.fri_oracle_case()
        view = issue_case_view(case)
        result = model.ground_whole_correspondence(protocol_check(case), view)
        self.assertEqual(
            (
                len(result.public_slots),
                len(result.phase_slots),
                len(result.oracle_observations),
            ),
            (1, 1, 2),
        )
        self.assertNotIn(
            model.k2.ValueRef.occurrence("oracle"),
            tuple(item.source for item in view.manifest),
        )

    def test_verifier_private_dependency_is_refused_by_manifest(self) -> None:
        case = model.verifier_private_case()
        record = completed(
            model.k2.generate(
                case.core,
                case.construction,
                model.k2.ChallengeInterpretation.FRESH,
                case.invocation,
                case.strategy,
            )
        )
        private = model.RelationRunCoordinate(
            model.RunCoordinateKind.PUBLIC_OCCURRENCE,
            model.k2.ValueRef.occurrence("private-derived"),
        )
        with self.assertRaisesRegex(model.GroundingError, "private or nonpublic"):
            model.issue_relation_run_view(
                case.core,
                case.construction,
                case.invocation,
                record,
                (private,),
            )
        view = model.issue_relation_run_view(
            case.core,
            case.construction,
            case.invocation,
            record,
            binding_manifest(case.protocol_binding),
        )
        self.assertNotIn(b"secret", tuple(item.value for item in view.entries))

    def test_private_check_influence_closes_over_terminal_result(self) -> None:
        core = model.k2.Core(
            inputs=(
                model.k2.InputDecl(
                    "verifier-flag",
                    model.k2.InputRole.VERIFIER_PRIVATE,
                    value_sort=model.k2.ValueSort.BOOL,
                ),
            ),
            scopes=(model.k2.ScopeDecl("root", None, None),),
            schedule=(
                model.k2.Occurrence(
                    "private-check",
                    model.k2.OccurrenceKind.CHECK,
                    dependencies=(model.k2.ValueRef.input("verifier-flag"),),
                    check_predicate=model.k2.Predicate(
                        model.k2.PredicateKind.BOOL,
                        (model.k2.ValueRef.input("verifier-flag"),),
                    ),
                ),
                model.k2.Occurrence("terminal", model.k2.OccurrenceKind.TERMINAL),
            ),
        )
        construction = model.k2.TranscriptConstruction(
            b"zkc/k3/private-terminal/v0"
        )
        invocation = model.k2.Invocation(MappingProxyType({"verifier-flag": True}))
        record = completed(
            model.k2.generate(
                core,
                construction,
                model.k2.ChallengeInterpretation.FRESH,
                invocation,
                model.k2.ScriptedStrategy({}),
            )
        )
        terminal = model.RelationRunCoordinate(
            model.RunCoordinateKind.PUBLIC_OCCURRENCE,
            model.k2.ValueRef.occurrence("terminal"),
        )
        with self.assertRaisesRegex(model.GroundingError, "private or nonpublic"):
            model.issue_relation_run_view(
                core, construction, invocation, record, (terminal,)
            )

    def test_equal_values_keep_two_source_occurrences(self) -> None:
        core = model.k2.Core(
            inputs=(
                model.k2.InputDecl("left", model.k2.InputRole.STATEMENT),
                model.k2.InputDecl("right", model.k2.InputRole.STATEMENT),
            ),
            scopes=(model.k2.ScopeDecl("root", None, None),),
            schedule=(
                model.k2.Occurrence("terminal", model.k2.OccurrenceKind.TERMINAL),
            ),
        )
        interpretation = model.k2.ChallengeInterpretation.FRESH
        _, relation = model._simple_relation(
            "equal-values", public=(model.RelationSlot("value", model.BYTES),)
        )
        relation = replace(relation, requires_claim=False)
        relation_id = model.relation_interface_id(relation)
        instances = (
            model.RelationInstanceOccurrence("left-instance", relation_id),
            model.RelationInstanceOccurrence("right-instance", relation_id),
        )
        binding = model.ProtocolRelationBinding(
            model.protocol_id(core, None, interpretation),
            (relation_id,),
            instances,
            (
                model.PublicSlotEdge(
                    "left-instance", "value", model.BindingRef("root", "left")
                ),
                model.PublicSlotEdge(
                    "right-instance", "value", model.BindingRef("root", "right")
                ),
            ),
            (),
            (),
            (),
        )
        checked = model.check_protocol_relation_binding(
            core, None, interpretation, (relation,), (), binding
        )
        invocation = model.k2.Invocation(
            MappingProxyType({"left": b"same", "right": b"same"})
        )
        construction = model.k2.TranscriptConstruction(b"unused-fresh")
        record = completed(
            model.k2.generate(
                core,
                construction,
                interpretation,
                invocation,
                model.k2.ScriptedStrategy({}),
            )
        )
        view = model.issue_relation_run_view(
            core,
            construction,
            invocation,
            record,
            binding_manifest(binding),
        )
        grounded = model.ground_whole_correspondence(checked, view)
        self.assertEqual(tuple(item.value for item in view.entries), (b"same", b"same"))
        self.assertNotEqual(
            grounded.public_slots[0].value_id, grounded.public_slots[1].value_id
        )

    def test_grounding_refuses_binding_and_manifest_substitution(self) -> None:
        case = model.schnorr_case()
        checked = protocol_check(case)
        view = issue_case_view(case)
        forged_binding = replace(
            case.protocol_binding,
            public_edges=(
                replace(
                    case.protocol_binding.public_edges[0], slot="substituted-slot"
                ),
            ),
        )
        with self.assertRaises(model.RelationError):
            model.ground_whole_correspondence(
                replace(checked, binding=forged_binding), view
            )
        record = completed(
            model.k2.generate(
                case.core,
                case.construction,
                model.k2.ChallengeInterpretation.FIAT_SHAMIR,
                case.invocation,
                case.strategy,
            )
        )
        empty_view = model.issue_relation_run_view(
            case.core,
            case.construction,
            case.invocation,
            record,
            (),
        )
        with self.assertRaisesRegex(model.GroundingError, "exact binding read set"):
            model.ground_whole_correspondence(checked, empty_view)


class CarrierTest(unittest.TestCase):
    def source(
        self,
    ) -> tuple[model.CarrierGraph, model.CarrierDependencyEnvironment]:
        case = model.schnorr_case()
        return (
            model.carrier_graph_for(
                case.core,
                model.k2.ChallengeInterpretation.FIAT_SHAMIR,
                case.construction,
            ),
            model.CarrierDependencyEnvironment(case.construction),
        )

    def test_exact_protocol_carrier_round_trips_fresh_and_fs(self) -> None:
        self.assertTrue(model.carrier_disposition_is_complete())
        drifted = dict(model.FROZEN_CARRIER_FIELD_DISPOSITION)
        drifted["Core.unreviewed_field"] = model.FieldDisposition.GRAPH_CARRIED
        self.assertFalse(model.carrier_disposition_is_complete(drifted))
        fresh = model.verifier_private_case()
        for graph, dependencies in (
            self.source(),
            (
                model.carrier_graph_for(
                    fresh.core,
                    model.k2.ChallengeInterpretation.FRESH,
                    None,
                ),
                model.CarrierDependencyEnvironment(None),
            ),
        ):
            carrier = model.lower_carrier(graph)
            self.assertEqual(model.read_carrier(carrier), graph)
            self.assertEqual(model.authenticate_carrier(carrier, dependencies), graph)
            self.assertNotIn("TranscriptConstruction", repr(carrier))
            with self.assertRaises(model.UnsupportedCarrierFeature):
                model._lower_carrier_value(dependencies)

    def test_carrier_refuses_ineligible_fs_and_imported_satellite(self) -> None:
        case = model.verifier_private_case()
        graph = model.carrier_graph_for(
            case.core,
            model.k2.ChallengeInterpretation.FIAT_SHAMIR,
            case.construction,
        )
        with self.assertRaises(model.CarrierError):
            model.admit_carrier_graph(
                graph,
                model.CarrierDependencyEnvironment(case.construction),
            )
        with self.assertRaises(model.UnsupportedCarrierFeature):
            model.require_imported_verification_carrier_support()

    def test_carrier_distinguishes_missing_unknown_and_unsupported(self) -> None:
        graph, _ = self.source()
        carrier = model.lower_carrier(graph)
        unknown = copy.deepcopy(carrier)
        unknown["mystery"] = 1
        with self.assertRaises(model.UnknownCarrierField):
            model.read_carrier(unknown)
        missing = copy.deepcopy(carrier)
        del missing["graph"]
        with self.assertRaises(model.MissingCarrierField):
            model.read_carrier(missing)
        unsupported = copy.deepcopy(carrier)
        unsupported["profile"] = "formed-but-unsupported-v9"
        with self.assertRaises(model.UnsupportedCarrierFeature):
            model.read_carrier(unsupported)

    def test_carrier_identity_binds_transcript_construction(self) -> None:
        graph, dependencies = self.source()
        changed_construction = model.k2.TranscriptConstruction(
            b"zkc/k3/changed-construction/v0"
        )
        changed_graph = model.carrier_graph_for(
            graph.core,
            graph.interpretation,
            changed_construction,
        )
        self.assertNotEqual(
            model.carrier_protocol_id(graph),
            model.carrier_protocol_id(changed_graph),
        )
        carrier = model.lower_carrier(graph)
        self.assertEqual(model.authenticate_carrier(carrier, dependencies), graph)
        for wrong_environment in (
            model.CarrierDependencyEnvironment(None),
            model.CarrierDependencyEnvironment(changed_construction),
        ):
            with self.assertRaises(model.CarrierError):
                model.authenticate_carrier(carrier, wrong_environment)


if __name__ == "__main__":
    unittest.main()
