from __future__ import annotations

from copy import copy, deepcopy
from dataclasses import fields, replace
import importlib.util
from pathlib import Path
import sys
import unittest
from unittest.mock import patch


NAME = "_zkc_k3_oir_projection"
PATH = Path(__file__).resolve().parents[1] / "reference_model.py"
if NAME in sys.modules:
    m = sys.modules[NAME]
else:
    spec = importlib.util.spec_from_file_location(NAME, PATH)
    assert spec is not None and spec.loader is not None
    m = importlib.util.module_from_spec(spec)
    sys.modules[NAME] = m
    spec.loader.exec_module(m)


GRAPH_FIELDS = (
    "role",
    "exact_used_dependencies",
    "value_types",
    "constants",
    "pure_nodes",
    "role_abi_graph",
    "endpoint_spine",
    "static_fs_semantics",
    "claims",
    "anchored_obligations",
    "optional_plan_graph",
)

FROZEN_P01_SPINE = (
    ("fs-initialization", None, None, None),
    ("scope-opening", None, None, None),
    ("public-binding", None, 0, None),
    ("public-binding", None, 1, None),
    ("public-binding", None, 2, None),
    ("public-binding", None, 3, None),
    ("public-binding", None, 4, None),
    ("core-occurrence", "ProverMessageAction", None, 0),
    ("core-occurrence", "ChallengeAction", None, 1),
    ("core-occurrence", "ProverMessageAction", None, 2),
    ("core-occurrence", "CheckAction", None, 3),
    ("core-occurrence", "ReductionAction", None, None),
    ("core-occurrence", "TerminalAction", None, 4),
)

FROZEN_P01_FRAMES = (
    ("core-header", (), None, None, None, None, ""),
    ("construction-header", (), None, None, None, None, ""),
    ("application-domain", (), None, None, None, None, ""),
    ("scope-open", (0,), None, None, None, None, ""),
    ("public-binding", (), 0, None, None, None, "public-parameter"),
    ("public-binding", (), 1, None, None, None, "public-parameter"),
    ("public-binding", (), 2, None, None, None, "public-parameter"),
    ("public-binding", (), 3, None, None, None, "statement"),
    ("public-binding", (), 4, None, None, None, "public-context"),
    ("message", (), None, 0, None, None, ""),
    ("challenge-condition", (), None, 1, 1, 0, ""),
    ("message", (), None, 2, None, None, ""),
)

FROZEN_VERIFIER_NONFRAME_OBLIGATIONS = (
    ("presentation", 0, None, "external-supply", "decode"),
    ("presentation", 0, None, "transport", "decode"),
    ("presentation", 1, None, "external-supply", "decode"),
    ("presentation", 1, None, "transport", "decode"),
    ("presentation", 2, None, "external-supply", "decode"),
    ("presentation", 3, None, "external-supply", "decode"),
    ("presentation", 4, None, "external-supply", "decode"),
    ("presentation", 0, None, "completion-tag", "encode"),
    ("presentation", 1, 0, "completion-payload", "encode"),
    ("presentation", 1, 1, "completion-payload", "encode"),
    ("presentation", 1, 2, "completion-payload", "encode"),
    ("presentation", 1, 3, "completion-payload", "encode"),
    ("presentation", 1, 4, "completion-payload", "encode"),
    ("presentation", 1, 5, "completion-payload", "encode"),
    ("presentation", 1, None, "completion-tag", "encode"),
    ("challenge-interpret", 8, 0, None, None),
    ("local-occurrence", 10, None, None, None),
    ("local-occurrence", 11, None, None, None),
    ("local-occurrence", 12, None, None, None),
    ("slot-ingress", 0, None, None, None),
    ("slot-ingress", 1, None, None, None),
    ("slot-ingress", 2, None, None, None),
    ("slot-ingress", 3, None, None, None),
    ("slot-ingress", 4, None, None, None),
)

FROZEN_PROVER_NONFRAME_OBLIGATIONS = (
    ("presentation", 0, None, "external-supply", "decode"),
    ("presentation", 1, None, "external-supply", "decode"),
    ("presentation", 2, None, "external-supply", "decode"),
    ("presentation", 3, None, "external-supply", "decode"),
    ("presentation", 4, None, "external-supply", "decode"),
    ("presentation", 0, None, "transport", "encode"),
    ("presentation", 1, None, "transport", "encode"),
    ("challenge-interpret", 8, 0, None, None),
    ("local-occurrence", 7, None, None, None),
    ("local-occurrence", 9, None, None, None),
    ("plan-decision", 7, None, None, None),
    ("plan-decision", 9, None, None, None),
    ("slot-ingress", 0, None, None, None),
    ("slot-ingress", 1, None, None, None),
    ("slot-ingress", 2, None, None, None),
    ("slot-ingress", 3, None, None, None),
    ("slot-ingress", 4, None, None, None),
)


def p01(role=m.EndpointRole.VERIFIER):
    return m.p01_request(role)


def bind_supplement(request):
    answer = m.bind_future_owner_supplement(request)
    if answer.kind is not m.OutcomeKind.AFFIRMATIVE:
        raise AssertionError(answer)
    return answer.value


def target(request):
    answer = m.project(request)
    if answer.kind is not m.OutcomeKind.AFFIRMATIVE:
        raise AssertionError(answer)
    return answer.value


def admit(endpoint, **kwargs):
    answer = m.local_admit(endpoint, **kwargs)
    if answer.kind is not m.OutcomeKind.AFFIRMATIVE:
        raise AssertionError(answer)
    return answer.value


def source(request):
    answer = m.derive_source_view(request)
    if answer.kind is not m.OutcomeKind.AFFIRMATIVE:
        raise AssertionError(answer)
    return answer.value


def validation(request, endpoint, *, work_limit=m.MAX_WORK):
    answer = m.form_projection_validation_request(
        source(request), admit(endpoint), work_limit=work_limit
    )
    if answer.kind is not m.OutcomeKind.AFFIRMATIVE:
        raise AssertionError(answer)
    return answer.value


def checked_projection(request, endpoint=None):
    endpoint = target(request) if endpoint is None else endpoint
    answer = m.check_projection(validation(request, endpoint))
    if answer.kind is not m.OutcomeKind.AFFIRMATIVE:
        raise AssertionError(answer)
    return answer.value


def pair_pressure_probe(
    verifier,
    prover,
):
    return m.pressure_probe_p01_endpoint_pair(
        admit(verifier),
        admit(prover),
    )


def remint_graph(endpoint, graph):
    return m.remint(replace(endpoint, semantic_graph=graph))


def graph_with(endpoint, **changes):
    return remint_graph(endpoint, replace(endpoint.semantic_graph, **changes))


def frame_signature(item):
    return (
        item.family,
        item.original_scope_path,
        item.original_binding_ordinal,
        item.original_occurrence_ordinal,
        item.original_challenge_ordinal,
        item.challenge_input_ordinal,
        item.binding_class,
    )


def obligation_signature(item):
    return (
        item.kind.value,
        item.owner_ref,
        item.secondary_ref,
        None if item.presentation_kind is None else item.presentation_kind.value,
        None if item.codec_direction is None else item.codec_direction.value,
    )


class GraphAndPositiveTests(unittest.TestCase):
    def test_exact_graph_has_eleven_identity_fields(self):
        self.assertEqual(
            tuple(item.name for item in fields(m.EndpointSemanticGraph)), GRAPH_FIELDS
        )
        self.assertNotIn("requirements", GRAPH_FIELDS)
        self.assertNotIn("completion_interface", GRAPH_FIELDS)

    def test_contract_accessor_is_static_and_nonidentity(self):
        self.assertEqual(m.ENDPOINT_CONTRACT_LAW, "EndpointContractLawV0")
        self.assertEqual(
            tuple(item.name for item in fields(m.DerivedEndpointContract)),
            (
                "static_obligations",
                "requirements",
                "completion_interface",
            ),
        )
        self.assertFalse(hasattr(m, "scripted_challenge"))
        self.assertFalse(hasattr(m, "DrawStep"))

    def test_verifier_source_and_target_are_independently_equal(self):
        request = p01()
        self.assertEqual(
            source(request).view.semantic_graph, target(request).semantic_graph
        )

    def test_prover_source_and_target_are_independently_equal(self):
        request = p01(m.EndpointRole.PROVER)
        self.assertEqual(
            source(request).view.semantic_graph, target(request).semantic_graph
        )

    def test_verifier_projects_admits_and_checks(self):
        answers = m.project_admit_check(p01())
        self.assertEqual(
            tuple(item.kind for item in answers),
            (m.OutcomeKind.AFFIRMATIVE,) * 3,
        )

    def test_prover_projects_admits_and_checks(self):
        answers = m.project_admit_check(p01(m.EndpointRole.PROVER))
        self.assertEqual(
            tuple(item.kind for item in answers),
            (m.OutcomeKind.AFFIRMATIVE,) * 3,
        )

    def test_independent_trivial_pair_pressure_probe_matches(self):
        verifier, prover = m.trivial_requests()
        for request in (verifier, prover):
            answers = m.project_admit_check(request)
            self.assertTrue(
                all(item.kind is m.OutcomeKind.AFFIRMATIVE for item in answers)
            )
        answer = pair_pressure_probe(target(verifier), target(prover))
        self.assertEqual(answer, ())

    def test_verifier_message_and_inactive_guarded_message_are_supported(self):
        for guarded in (False, True):
            for request in m.verifier_message_requests(guarded=guarded):
                answers = m.project_admit_check(request)
                self.assertTrue(
                    all(item.kind is m.OutcomeKind.AFFIRMATIVE for item in answers)
                )

    def test_nested_scope_is_supported(self):
        for request in m.nested_scope_requests():
            answers = m.project_admit_check(request)
            self.assertTrue(
                all(item.kind is m.OutcomeKind.AFFIRMATIVE for item in answers)
            )
            self.assertGreater(len(target(request).semantic_graph.endpoint_spine), 13)

    def test_zero_one_and_two_public_derivations(self):
        for count in (0, 1, 2):
            verifier, prover = m.public_derivation_requests(count)
            for request in (verifier, prover):
                answers = m.project_admit_check(request)
                self.assertTrue(
                    all(item.kind is m.OutcomeKind.AFFIRMATIVE for item in answers)
                )
            verifier_edges = target(
                verifier
            ).semantic_graph.role_abi_graph.transport_edges
            prover_edges = target(prover).semantic_graph.role_abi_graph.transport_edges
            self.assertEqual(
                sum(
                    item.source is m.TransportActor.PUBLIC_DERIVATION
                    for item in verifier_edges
                ),
                count,
            )
            self.assertFalse(
                any(
                    item.source is m.TransportActor.PUBLIC_DERIVATION
                    for item in prover_edges
                )
            )

    def test_p01_endpoint_value_access_routes_are_role_exact(self):
        verifier = m.derive_endpoint_value_access(target(p01()).semantic_graph)
        prover = m.derive_endpoint_value_access(
            target(p01(m.EndpointRole.PROVER)).semantic_graph
        )

        def signature(item):
            return (
                item.value.kind.value,
                item.value.ref,
                item.route.kind.value,
                item.route.owner_ref,
                item.route.secondary_ref,
            )

        self.assertEqual(
            tuple(map(signature, verifier)),
            (
                ("occurrence-output", 8, "challenge-interpret", 8, 0),
                ("occurrence-output", 7, "inbound-transport", 0, None),
                ("occurrence-output", 9, "inbound-transport", 1, None),
                ("invocation-target", 0, "invocation-decode", 0, 0),
                ("invocation-target", 1, "invocation-decode", 1, 1),
                ("invocation-target", 2, "invocation-decode", 2, 2),
                ("invocation-target", 3, "invocation-decode", 3, 3),
                ("invocation-target", 4, "invocation-decode", 4, 4),
            ),
        )
        self.assertEqual(
            tuple(map(signature, prover)),
            (
                ("occurrence-output", 8, "challenge-interpret", 8, 0),
                ("invocation-target", 0, "invocation-decode", 0, 0),
                ("invocation-target", 1, "invocation-decode", 1, 1),
                ("invocation-target", 2, "invocation-decode", 2, 2),
                ("invocation-target", 3, "invocation-decode", 3, 3),
                ("invocation-target", 4, "invocation-decode", 4, 4),
                ("occurrence-output", 7, "plan-move", 7, None),
                ("occurrence-output", 9, "plan-move", 9, None),
            ),
        )

    def test_value_access_closes_constant_and_pure_predecessors(self):
        access = m.derive_endpoint_value_access(
            m.constant_pure_control().semantic_graph
        )
        routes = {item.route.kind for item in access}
        self.assertIn(m.EndpointValueAccessRouteKind.CONSTANT, routes)
        self.assertIn(m.EndpointValueAccessRouteKind.PURE_EVAL, routes)

    def test_public_check_reconstruction_does_not_replace_counterparty_action(self):
        baseline = target(p01(m.EndpointRole.PROVER)).semantic_graph
        reconstructed = m.public_reconstruction_control().semantic_graph
        access = m.derive_endpoint_value_access(reconstructed)
        self.assertIn(
            m.EndpointValueAccessRouteKind.RECONSTRUCT_CHECK,
            {item.route.kind for item in access},
        )

        def counterparty_actions(graph):
            return tuple(
                (
                    type(graph.endpoint_spine[item.spine_event_ref].action).__name__,
                    item.counterparty,
                )
                for item in m.derive_endpoint_contract(graph).requirements
                if item.family is m.RequirementFamily.COUNTERPARTY
                and item.use_site.startswith("counterparty-action:")
            )

        self.assertEqual(
            counterparty_actions(reconstructed), counterparty_actions(baseline)
        )


class FrozenContractTests(unittest.TestCase):
    def test_p01_spine_is_literal_and_includes_reduction(self):
        graph = target(p01()).semantic_graph
        actual = tuple(
            (
                event.kind.value,
                None if event.action is None else type(event.action).__name__,
                event.original_binding_ordinal,
                event.original_occurrence_ordinal,
            )
            for event in graph.endpoint_spine
        )
        self.assertEqual(actual, FROZEN_P01_SPINE)

    def test_every_p01_k2_frame_coordinate_is_literal(self):
        graph = target(p01()).semantic_graph
        self.assertEqual(
            tuple(map(frame_signature, m.derive_frame_recipes(graph))),
            FROZEN_P01_FRAMES,
        )

    def test_verifier_static_obligations_are_frozen(self):
        contract = m.derive_endpoint_contract(target(p01()).semantic_graph)
        nonframes = tuple(
            obligation_signature(item)
            for item in contract.static_obligations
            if item.kind is not m.StaticObligationKind.K2_FRAME
        )
        frames = tuple(
            frame_signature(item.frame_recipe)
            for item in contract.static_obligations
            if item.kind is m.StaticObligationKind.K2_FRAME
        )
        expected_frames = (
            FROZEN_P01_FRAMES[4:9]
            + FROZEN_P01_FRAMES[9:12]
            + (
                FROZEN_P01_FRAMES[1],
                FROZEN_P01_FRAMES[0],
                FROZEN_P01_FRAMES[3],
                FROZEN_P01_FRAMES[2],
            )
        )
        self.assertEqual(nonframes, FROZEN_VERIFIER_NONFRAME_OBLIGATIONS)
        self.assertEqual(frames, expected_frames)

    def test_prover_static_obligations_are_frozen(self):
        contract = m.derive_endpoint_contract(
            target(p01(m.EndpointRole.PROVER)).semantic_graph
        )
        nonframes = tuple(
            obligation_signature(item)
            for item in contract.static_obligations
            if item.kind is not m.StaticObligationKind.K2_FRAME
        )
        self.assertEqual(nonframes, FROZEN_PROVER_NONFRAME_OBLIGATIONS)

    def test_reduction_row_and_terminal_closure_are_frozen(self):
        graph = target(p01()).semantic_graph
        reduction, terminal = graph.anchored_obligations
        self.assertEqual(
            reduction.output_claims,
            (m.ReductionOutputRow(0, "claim-contract:checked", (1,)),),
        )
        self.assertEqual(reduction.required_challenge_law_refs, (0,))
        self.assertEqual(
            tuple(
                (item.publication_spine_ref, item.next_challenge_law_ref)
                for item in reduction.publications
            ),
            ((7, 0), (9, None)),
        )
        self.assertEqual(
            (terminal.terminal_spine_ref, terminal.required_check_spine_refs),
            (12, (10,)),
        )

    def test_completion_tag_is_present_even_with_zero_payload(self):
        graph = target(p01()).semantic_graph
        self.assertEqual(
            graph.role_abi_graph.completion_variants[0].payload_bindings, ()
        )
        contract = m.derive_endpoint_contract(graph)
        tags = [
            item
            for item in contract.static_obligations
            if item.presentation_kind is m.PresentationKind.COMPLETION_TAG
        ]
        self.assertEqual([item.owner_ref for item in tags], [0, 1])


class SupportAndManifestTests(unittest.TestCase):
    def test_owner_schema_is_exact_and_reflected(self):
        self.assertEqual(len(m.OWNER_SCHEMA_PATHS), 190)
        self.assertEqual(m.OWNER_SCHEMA_PATHS, m.reflected_owner_schema_paths())
        self.assertIs(m.audit_owner_schema().kind, m.OutcomeKind.AFFIRMATIVE)

    def test_unknown_owner_field_fails_closed(self):
        answer = m.audit_owner_schema(additions=("Core.future_field",))
        self.assertIs(answer.kind, m.OutcomeKind.UNSUPPORTED)

    def test_multisink_and_plan_material_dispositions_are_exact(self):
        schedule = m.owner_field_disposition(
            "Core.schedule", m.ProjectionPurpose.FS_PLAN_PROVER
        )
        self.assertEqual(
            schedule.prover_sinks,
            (m.ViewSink.ANCHOR, m.ViewSink.PLAN, m.ViewSink.SPINE),
        )
        key = m.owner_field_disposition(
            "PrivateMaterialDecl.key", m.ProjectionPurpose.FS_PLAN_PROVER
        )
        kind = m.owner_field_disposition(
            "PrivateMaterialDecl.kind", m.ProjectionPurpose.FS_PLAN_PROVER
        )
        value_type = m.owner_field_disposition(
            "PrivateMaterialDecl.value_type", m.ProjectionPurpose.FS_PLAN_PROVER
        )
        self.assertIs(key.prover_kind, m.FieldDispositionKind.INERT)
        self.assertEqual(kind.prover_sinks, (m.ViewSink.PLAN,))
        self.assertEqual(value_type.prover_sinks, (m.ViewSink.PLAN, m.ViewSink.TYPE))

    def test_manifest_is_purpose_specific_but_schema_is_shared(self):
        verifier = m.classify_support(p01()).value
        prover = m.classify_support(p01(m.EndpointRole.PROVER)).value
        self.assertEqual(verifier.schema_set_id, prover.schema_set_id)
        self.assertNotEqual(verifier.manifest_id, prover.manifest_id)

    def test_live_k3b_implementation_carrier_gap_is_typed(self):
        answer = m.project(m.live_p01_request())
        self.assertIs(answer.kind, m.OutcomeKind.MISSING_DEPENDENCY)
        self.assertEqual(answer.unsupported_reasons, ())
        self.assertIsNone(answer.value)

    def test_durable_support_reason_universe_is_exact(self):
        self.assertEqual(
            tuple(m.SupportReason),
            (
                m.SupportReason.FRESH_ENDPOINT,
                m.SupportReason.GENERIC_PROVER_ENDPOINT,
                m.SupportReason.STANDARD_ORACLE_ENDPOINT,
                m.SupportReason.MODULE_EFFECT_ENDPOINT,
            ),
        )

    def test_unsupported_reasons_are_complete_nonempty_and_sorted(self):
        prover = p01(m.EndpointRole.PROVER)
        request = replace(
            prover,
            interpretation=m.k2.ChallengeInterpretation.FRESH,
            plan=None,
            future_owner=replace(prover.future_owner, plan=None),
            admitted_module_effect=True,
        )
        answer = m.classify_support(request)
        self.assertIs(answer.kind, m.OutcomeKind.UNSUPPORTED)
        self.assertEqual(
            answer.unsupported_reasons,
            (
                m.SupportReason.FRESH_ENDPOINT,
                m.SupportReason.GENERIC_PROVER_ENDPOINT,
                m.SupportReason.MODULE_EFFECT_ENDPOINT,
            ),
        )
        self.assertIsNone(answer.value)

    def test_fresh_generic_and_module_reasons_are_typed(self):
        prover = p01(m.EndpointRole.PROVER)
        cases = (
            (
                replace(p01(), interpretation=m.k2.ChallengeInterpretation.FRESH),
                m.SupportReason.FRESH_ENDPOINT,
            ),
            (
                replace(
                    prover,
                    plan=None,
                    future_owner=replace(prover.future_owner, plan=None),
                ),
                m.SupportReason.GENERIC_PROVER_ENDPOINT,
            ),
            (
                replace(p01(), admitted_module_effect=True),
                m.SupportReason.MODULE_EFFECT_ENDPOINT,
            ),
        )
        for request, reason in cases:
            with self.subTest(reason=reason):
                answer = m.project(request)
                self.assertIs(answer.kind, m.OutcomeKind.UNSUPPORTED)
                self.assertIn(reason, answer.unsupported_reasons)

    def test_plan_module_is_owner_profile_kind_mismatch(self):
        prover = p01(m.EndpointRole.PROVER)
        request = replace(
            prover,
            future_owner=replace(
                prover.future_owner,
                plan=replace(prover.future_owner.plan, has_module_recipe=True),
            ),
        )
        answer = m.project(request)
        self.assertIs(answer.kind, m.OutcomeKind.KIND_MISMATCH)
        self.assertEqual(answer.unsupported_reasons, ())

    def test_oracle_is_typed_unsupported(self):
        case = m.k3.fri_oracle_case()
        request = m.ProjectionRequest(
            case.core,
            case.construction,
            m.k2.ChallengeInterpretation.FIAT_SHAMIR,
            case.interface,
            m.EndpointRole.VERIFIER,
            None,
            None,
        )
        answer = m.classify_support(request)
        self.assertIs(answer.kind, m.OutcomeKind.UNSUPPORTED)
        self.assertIn(
            m.SupportReason.STANDARD_ORACLE_ENDPOINT,
            answer.unsupported_reasons,
        )

    def test_k3c_is_not_an_import_dependency(self):
        self.assertEqual(m._K3_PATH.parent.name, "k3-dependent-surfaces")
        self.assertFalse(any("k3-analysis" in name for name in sys.modules))


class StaticFsAndAdmissionTests(unittest.TestCase):
    def test_fs_has_one_construction_global_failure_only(self):
        graph = target(p01()).semantic_graph
        self.assertEqual(
            graph.static_fs_semantics.sampling_exhausted_failure,
            "sampling-exhausted-v0",
        )
        law_fields = {item.name for item in fields(m.ChallengeLaw)}
        self.assertNotIn("failure", law_fields)
        self.assertNotIn("namespace", law_fields)
        self.assertNotIn("modulus", law_fields)

    def test_namespace_recipe_is_derived_from_static_coordinates(self):
        graph = target(p01()).semantic_graph
        recipe = m.derive_namespace_recipe(graph, 0)
        law = graph.static_fs_semantics.challenge_laws[0]
        self.assertEqual(recipe.original_scope_path, (0,))
        self.assertEqual(recipe.original_challenge_ordinal, 1)
        self.assertEqual(
            (recipe.domain_ref, recipe.correlation),
            (law.domain_ref, law.correlation),
        )

    def test_static_fs_application_domain_rotates_oir(self):
        endpoint = target(p01())
        fs = replace(
            endpoint.semantic_graph.static_fs_semantics,
            application_domain=b"other-domain",
        )
        changed = graph_with(endpoint, static_fs_semantics=fs)
        self.assertIs(m.local_admit(changed).kind, m.OutcomeKind.AFFIRMATIVE)
        self.assertNotEqual(endpoint.asserted_id, changed.asserted_id)

    def test_challenge_law_omission_and_duplication_are_malformed(self):
        endpoint = target(p01())
        fs = endpoint.semantic_graph.static_fs_semantics
        for laws in ((), fs.challenge_laws + fs.challenge_laws):
            with self.subTest(size=len(laws)):
                changed = graph_with(
                    endpoint,
                    static_fs_semantics=replace(fs, challenge_laws=laws),
                )
                self.assertIs(m.local_admit(changed).kind, m.OutcomeKind.MALFORMED)

    def test_orphan_challenge_action_is_malformed(self):
        endpoint = target(p01())
        spine = list(endpoint.semantic_graph.endpoint_spine)
        spine[8] = replace(spine[8], action=m.ChallengeAction(1))
        changed = graph_with(endpoint, endpoint_spine=tuple(spine))
        self.assertIs(m.local_admit(changed).kind, m.OutcomeKind.MALFORMED)

    def test_terminal_must_be_one_final_closure(self):
        endpoint = target(p01())
        spine = endpoint.semantic_graph.endpoint_spine + (
            m.SpineEvent(
                m.SpineEventKind.CORE_OCCURRENCE,
                scope_event_ref=1,
                action=m.TerminalAction(),
            ),
        )
        changed = graph_with(endpoint, endpoint_spine=spine)
        self.assertIs(m.local_admit(changed).kind, m.OutcomeKind.MALFORMED)

    def test_completion_payload_duplicate_and_reorder_are_malformed(self):
        endpoint = target(p01())
        abi = endpoint.semantic_graph.role_abi_graph
        failure = abi.completion_variants[1]
        mutations = (
            failure.payload_bindings + (failure.payload_bindings[0],),
            tuple(reversed(failure.payload_bindings)),
        )
        for bindings in mutations:
            variants = list(abi.completion_variants)
            variants[1] = replace(failure, payload_bindings=bindings)
            changed = graph_with(
                endpoint,
                role_abi_graph=replace(abi, completion_variants=tuple(variants)),
            )
            self.assertIs(m.local_admit(changed).kind, m.OutcomeKind.MALFORMED)

    def test_wrong_transport_role_is_malformed(self):
        endpoint = target(p01())
        abi = endpoint.semantic_graph.role_abi_graph
        edges = list(abi.transport_edges)
        edges[0] = replace(edges[0], source=m.TransportActor.VERIFIER)
        changed = graph_with(
            endpoint,
            role_abi_graph=replace(abi, transport_edges=tuple(edges)),
        )
        self.assertIs(m.local_admit(changed).kind, m.OutcomeKind.MALFORMED)

    def test_constant_and_pure_node_control_is_admitted(self):
        endpoint = m.constant_pure_control()
        self.assertIs(m.local_admit(endpoint).kind, m.OutcomeKind.AFFIRMATIVE)
        uses = {
            item.use_site
            for item in m.derive_endpoint_contract(endpoint.semantic_graph).requirements
        }
        self.assertIn("pure-node:0", uses)

    def test_phantom_pure_node_is_malformed(self):
        endpoint = m.constant_pure_control()
        node = endpoint.semantic_graph.pure_nodes[0]
        changed = graph_with(
            endpoint, pure_nodes=endpoint.semantic_graph.pure_nodes + (node,)
        )
        self.assertIs(m.local_admit(changed).kind, m.OutcomeKind.MALFORMED)

    def test_general_codec_certificate_is_admission_only(self):
        endpoint = target(p01())
        graph = endpoint.semantic_graph
        codecs = list(graph.role_abi_graph.codec_nodes)
        codecs[0] = m.CodecNode(
            m.CodecKind.GENERAL,
            general_law_dependency=0,
            interface_codec_id=codecs[0].interface_codec_id,
        )
        changed = graph_with(
            endpoint,
            role_abi_graph=replace(graph.role_abi_graph, codec_nodes=tuple(codecs)),
        )
        self.assertIs(
            m.local_admit(changed).kind,
            m.OutcomeKind.MISSING_DEPENDENCY,
        )
        admitted = m.local_admit(changed, general_codec_evidence={0: True})
        self.assertIs(admitted.kind, m.OutcomeKind.AFFIRMATIVE)
        contract = m.derive_endpoint_contract(changed.semantic_graph)
        self.assertFalse(
            any("certificate" in item.use_site for item in contract.requirements)
        )


class PlanAndPublicClosureTests(unittest.TestCase):
    def test_plan_decisions_are_prover_message_spine_refs(self):
        plan = target(p01(m.EndpointRole.PROVER)).semantic_graph.optional_plan_graph
        self.assertEqual(tuple(item.decision_ref for item in plan.moves), (7, 9))
        self.assertEqual(tuple(item.decision_ref for item in plan.recipe_nodes), (7, 9))

    def test_private_material_and_randomness_requirements_are_exact(self):
        graph = target(p01(m.EndpointRole.PROVER)).semantic_graph
        requirements = m.derive_endpoint_contract(graph).requirements
        private = next(
            item
            for item in requirements
            if item.family is m.RequirementFamily.PRIVATE_MATERIAL_INGRESS
        )
        randomness = next(
            item
            for item in requirements
            if item.family is m.RequirementFamily.PRIVATE_RANDOMNESS_INGRESS
        )
        self.assertEqual(
            (private.plan_ref, private.kind, private.type_ref),
            (0, "witness-ingress", 1),
        )
        self.assertEqual(
            (
                randomness.plan_ref,
                randomness.type_ref,
                randomness.first_available_decision_spine_ref,
            ),
            (0, 1, 7),
        )

    def test_state_requirement_preserves_initializer_and_total_updates(self):
        request = m.stateful_p01_request()
        endpoint = target(request)
        self.assertIs(m.local_admit(endpoint).kind, m.OutcomeKind.AFFIRMATIVE)
        requirement = next(
            item
            for item in m.derive_endpoint_contract(endpoint.semantic_graph).requirements
            if item.family is m.RequirementFamily.STATE_STORAGE
        )
        self.assertEqual(
            requirement.initializer.kind, m.PlanOperandKind.PRIVATE_MATERIAL
        )
        self.assertEqual(
            tuple(item.decision_ref for item in requirement.updates), (7, 9)
        )

    def test_cross_decision_recipe_node_reference_is_malformed(self):
        endpoint = target(p01(m.EndpointRole.PROVER))
        plan = endpoint.semantic_graph.optional_plan_graph
        nodes = list(plan.recipe_nodes)
        nodes[1] = replace(nodes[1], decision_ref=7)
        changed = graph_with(
            endpoint,
            optional_plan_graph=replace(plan, recipe_nodes=tuple(nodes)),
        )
        self.assertIs(m.local_admit(changed).kind, m.OutcomeKind.MALFORMED)

    def test_dead_plan_material_and_exports_are_quotiented(self):
        request = p01(m.EndpointRole.PROVER)
        plan = request.plan
        extra = m.k3.PrivateMaterialDecl(
            "unused", m.k3.PrivateMaterialKind.ADVICE, m.k3.NAT
        )
        dead_plan = replace(plan, private_material=plan.private_material + (extra,))
        dead = bind_supplement(
            replace(
                request,
                plan=dead_plan,
                future_owner=m.future_owner_supplement(
                    request.core,
                    request.construction,
                    request.interface,
                    dead_plan,
                ),
                supplement_authority=None,
            )
        )
        export = m.k3.PlanExport("copy", "response", m.k3.NAT)
        exported_plan = replace(plan, exports=(export,))
        exported = bind_supplement(
            replace(
                request,
                plan=exported_plan,
                future_owner=m.future_owner_supplement(
                    request.core,
                    request.construction,
                    request.interface,
                    exported_plan,
                ),
                supplement_authority=None,
            )
        )
        self.assertEqual(target(request).asserted_id, target(dead).asserted_id)
        self.assertEqual(target(request).asserted_id, target(exported).asserted_id)

    def test_reachable_plan_algorithm_rotates_identity(self):
        request = p01(m.EndpointRole.PROVER)
        routes = list(request.plan.decision_routes)
        routes[0] = replace(
            routes[0], implementation_algorithm_id=m._algorithm("changed-route")
        )
        plan = replace(request.plan, decision_routes=tuple(routes))
        changed = bind_supplement(
            replace(
                request,
                plan=plan,
                future_owner=m.future_owner_supplement(
                    request.core,
                    request.construction,
                    request.interface,
                    plan,
                ),
                supplement_authority=None,
            )
        )
        self.assertNotEqual(target(request).asserted_id, target(changed).asserted_id)

    def test_public_check_reconstruction_is_demand_driven(self):
        endpoint = m.public_reconstruction_control()
        self.assertIs(m.local_admit(endpoint).kind, m.OutcomeKind.AFFIRMATIVE)
        uses = {
            item.use_site
            for item in m.derive_endpoint_contract(endpoint.semantic_graph).requirements
        }
        self.assertIn("public-reconstruction:10", uses)
        ordinary = m.derive_endpoint_contract(
            target(p01(m.EndpointRole.PROVER)).semantic_graph
        )
        self.assertNotIn(
            "public-reconstruction:10",
            {item.use_site for item in ordinary.requirements},
        )

    def test_prover_verifier_private_leaf_is_rejected(self):
        endpoint = m.public_reconstruction_control()
        graph = endpoint.semantic_graph
        targets = list(graph.role_abi_graph.invocation_targets)
        targets[0] = replace(
            targets[0], invocation_class=m.InvocationClass.VERIFIER_PRIVATE
        )
        changed = graph_with(
            endpoint,
            role_abi_graph=replace(
                graph.role_abi_graph, invocation_targets=tuple(targets)
            ),
        )
        answer = m.local_admit(changed)
        self.assertIs(answer.kind, m.OutcomeKind.MALFORMED)
        self.assertIn("verifier-private", answer.reason)

    def test_prover_has_no_completion_or_accept_outcome(self):
        graph = target(p01(m.EndpointRole.PROVER)).semantic_graph
        contract = m.derive_endpoint_contract(graph)
        self.assertEqual(graph.role_abi_graph.completion_variants, ())
        self.assertIs(
            contract.completion_interface.kind,
            m.CompletionInterfaceKind.NO_SOURCE_SEMANTIC_COMPLETION,
        )
        self.assertFalse(hasattr(contract, "outcome"))


class ProjectionRelationTests(unittest.TestCase):
    def assert_projection_negative(self, request, endpoint, *paths):
        admitted = m.local_admit(endpoint)
        self.assertIs(admitted.kind, m.OutcomeKind.AFFIRMATIVE, admitted.reason)
        answer = m.check_projection(validation(request, endpoint))
        self.assertIs(answer.kind, m.OutcomeKind.NEGATIVE)
        self.assertEqual({item.path for item in answer.mismatches}, set(paths))

    def test_exact_mismatch_reports_top_level_field_set(self):
        request = p01()
        endpoint = target(request)
        fs = replace(
            endpoint.semantic_graph.static_fs_semantics,
            application_domain=b"changed",
        )
        abi = endpoint.semantic_graph.role_abi_graph
        slots = list(abi.slots)
        slots[5] = replace(slots[5], external_key="changed.commitment")
        changed = graph_with(
            endpoint,
            static_fs_semantics=fs,
            role_abi_graph=replace(abi, slots=tuple(slots)),
        )
        self.assert_projection_negative(
            request,
            changed,
            "semantic_graph.role_abi_graph",
            "semantic_graph.static_fs_semantics",
        )

    def test_required_check_erasure_is_local_but_projection_negative(self):
        request = p01()
        endpoint = target(request)
        anchors = list(endpoint.semantic_graph.anchored_obligations)
        anchors[1] = replace(anchors[1], required_check_spine_refs=())
        changed = graph_with(endpoint, anchored_obligations=tuple(anchors))
        self.assert_projection_negative(
            request, changed, "semantic_graph.anchored_obligations"
        )

    def test_phantom_reduction_output_is_local_but_projection_negative(self):
        request = p01()
        endpoint = target(request)
        anchors = list(endpoint.semantic_graph.anchored_obligations)
        anchors[0] = replace(
            anchors[0],
            output_claims=anchors[0].output_claims
            + (m.ReductionOutputRow(1, "empty-contract", ()),),
        )
        changed = graph_with(endpoint, anchored_obligations=tuple(anchors))
        self.assert_projection_negative(
            request, changed, "semantic_graph.anchored_obligations"
        )

    def test_reduction_claim_row_mutations_are_malformed(self):
        endpoint = target(p01())
        graph = endpoint.semantic_graph
        claims = graph.claims + (replace(graph.claims[1]),)
        anchors = list(graph.anchored_obligations)
        row = replace(anchors[0].output_claims[0], claim_refs=(1, 2))
        anchors[0] = replace(anchors[0], output_claims=(row,))
        valid = graph_with(endpoint, claims=claims, anchored_obligations=tuple(anchors))
        self.assertIs(m.local_admit(valid).kind, m.OutcomeKind.AFFIRMATIVE)
        for refs in ((1,), (1, 1), (2, 1)):
            bad_anchors = list(valid.semantic_graph.anchored_obligations)
            bad_anchors[0] = replace(
                bad_anchors[0], output_claims=(replace(row, claim_refs=refs),)
            )
            bad = graph_with(valid, anchored_obligations=tuple(bad_anchors))
            self.assertIs(m.local_admit(bad).kind, m.OutcomeKind.MALFORMED)

    def test_publication_next_challenge_mutation_is_negative(self):
        request = p01()
        endpoint = target(request)
        anchors = list(endpoint.semantic_graph.anchored_obligations)
        publications = list(anchors[0].publications)
        publications[0] = replace(publications[0], next_challenge_law_ref=None)
        anchors[0] = replace(anchors[0], publications=tuple(publications))
        changed = graph_with(endpoint, anchored_obligations=tuple(anchors))
        self.assert_projection_negative(
            request, changed, "semantic_graph.anchored_obligations"
        )

    def test_terminal_verdict_mutation_is_negative(self):
        request = p01()
        endpoint = target(request)
        anchors = list(endpoint.semantic_graph.anchored_obligations)
        anchors[1] = replace(anchors[1], verdict="different-verdict")
        changed = graph_with(endpoint, anchored_obligations=tuple(anchors))
        self.assert_projection_negative(
            request, changed, "semantic_graph.anchored_obligations"
        )

    def test_message_condition_and_guard_mutations_are_detected(self):
        request = p01()
        endpoint = target(request)
        spine = list(endpoint.semantic_graph.endpoint_spine)
        spine[7] = replace(
            spine[7], action=replace(spine[7].action, channel_ref="other-channel")
        )
        self.assert_projection_negative(
            request,
            graph_with(endpoint, endpoint_spine=tuple(spine)),
            "semantic_graph.endpoint_spine",
        )

        endpoint = target(request)
        fs = endpoint.semantic_graph.static_fs_semantics
        laws = list(fs.challenge_laws)
        laws[0] = replace(
            laws[0],
            conditions=(m.GraphValueRef(m.ValueRefKind.INVOCATION, 0),),
        )
        self.assert_projection_negative(
            request,
            graph_with(
                endpoint,
                static_fs_semantics=replace(fs, challenge_laws=tuple(laws)),
            ),
            "semantic_graph.static_fs_semantics",
        )

        guarded_request = m.verifier_message_requests(guarded=True)[0]
        guarded = target(guarded_request)
        guarded_spine = list(guarded.semantic_graph.endpoint_spine)
        guard_ref = next(
            index
            for index, item in enumerate(guarded_spine)
            if item.activity.algorithm_dependency is not None
        )
        guarded_spine[guard_ref] = replace(
            guarded_spine[guard_ref],
            activity=replace(
                guarded_spine[guard_ref].activity,
                inputs=(m.GraphValueRef(m.ValueRefKind.INVOCATION, 0),),
            ),
        )
        self.assert_projection_negative(
            guarded_request,
            graph_with(guarded, endpoint_spine=tuple(guarded_spine)),
            "semantic_graph.endpoint_spine",
        )

    def test_provenance_and_source_label_do_not_rotate_semantic_ids(self):
        first = p01()
        second = replace(
            first, provenance="other-provenance", source_label="other-label"
        )
        self.assertEqual(target(first).asserted_id, target(second).asserted_id)
        self.assertEqual(source(first).view_id, source(second).view_id)
        left = checked_projection(first)
        right = checked_projection(second)
        self.assertEqual(
            left.proposition.proposition_id, right.proposition.proposition_id
        )
        self.assertNotEqual(
            left.validation_request_fingerprint,
            right.validation_request_fingerprint,
        )

    def test_runtime_receipt_is_inert(self):
        first = p01()
        second = replace(first, runtime_receipt={"draws": 7, "result": 3})
        self.assertEqual(target(first).asserted_id, target(second).asserted_id)
        self.assertEqual(source(first).view_id, source(second).view_id)
        self.assertEqual(
            checked_projection(first).validation_request_fingerprint,
            checked_projection(second).validation_request_fingerprint,
        )


class NonAuthoritativePairPressureProbeTests(unittest.TestCase):
    def setUp(self):
        self.verifier = target(p01())
        self.prover = target(p01(m.EndpointRole.PROVER))

    def assert_pair_observes(self, verifier, prover, path):
        observations = pair_pressure_probe(verifier, prover)
        self.assertIn(path, {item.path for item in observations})

    def test_probe_has_no_authoritative_pair_artifacts(self):
        self.assertFalse(hasattr(m, "EndpointPairProposition"))
        self.assertFalse(hasattr(m, "EndpointPairValidationRequest"))
        self.assertFalse(hasattr(m, "CheckedEndpointPair"))
        self.assertFalse(hasattr(m, "PAIR_PROFILE"))

    def test_p01_pair_pressure_probe_matches(self):
        self.assertEqual(pair_pressure_probe(self.verifier, self.prover), ())

    def test_noncomplementary_roles_and_forged_capability_are_rejected(self):
        verifier = admit(self.verifier)
        with self.assertRaises(ValueError):
            m.pressure_probe_p01_endpoint_pair(verifier, verifier)
        forged = replace(admit(self.prover))
        with self.assertRaises(TypeError):
            m.pressure_probe_p01_endpoint_pair(verifier, forged)

    def test_static_fs_mismatch_is_observed(self):
        fs = replace(
            self.prover.semantic_graph.static_fs_semantics,
            application_domain=b"pair-other",
        )
        self.assert_pair_observes(
            self.verifier,
            graph_with(self.prover, static_fs_semantics=fs),
            "static-fs",
        )

    def test_spine_stream_mismatch_is_observed(self):
        spine = list(self.prover.semantic_graph.endpoint_spine)
        spine[7] = replace(
            spine[7], action=replace(spine[7].action, channel_ref="pair-other")
        )
        self.assert_pair_observes(
            self.verifier,
            graph_with(self.prover, endpoint_spine=tuple(spine)),
            "endpoint-spine",
        )

    def test_abi_codec_mismatch_is_observed(self):
        abi = self.prover.semantic_graph.role_abi_graph
        slots = list(abi.slots)
        slots[5] = replace(slots[5], external_key="pair.other")
        self.assert_pair_observes(
            self.verifier,
            graph_with(
                self.prover,
                role_abi_graph=replace(abi, slots=tuple(slots)),
            ),
            "role-abi",
        )

    def test_claim_and_anchor_mismatch_is_observed(self):
        graph = self.prover.semantic_graph
        claims = list(graph.claims)
        claims[1] = replace(claims[1], contract_ref="other-claim-contract")
        anchors = list(graph.anchored_obligations)
        row = anchors[0].output_claims[0]
        anchors[0] = replace(
            anchors[0],
            output_claims=(replace(row, contract_ref="other-claim-contract"),),
        )
        changed = graph_with(
            self.prover,
            claims=tuple(claims),
            anchored_obligations=tuple(anchors),
        )
        self.assert_pair_observes(self.verifier, changed, "claims")
        self.assert_pair_observes(self.verifier, changed, "anchors")

    def test_completion_closure_mismatch_is_observed(self):
        abi = self.verifier.semantic_graph.role_abi_graph
        phantom = m.CompletionVariant(
            m.CompletionTargetKind.CORE_TERMINAL,
            12,
            "phantom-terminal",
            (),
        )
        changed = graph_with(
            self.verifier,
            role_abi_graph=replace(
                abi,
                completion_variants=abi.completion_variants + (phantom,),
            ),
        )
        self.assert_pair_observes(changed, self.prover, "verifier-completion-closure")

    def test_pair_claims_no_liveness_or_acceptance(self):
        observations = pair_pressure_probe(self.verifier, self.prover)
        self.assertIs(type(observations), tuple)
        self.assertFalse(hasattr(observations, "capability"))


class OwnerAdapterAndProfileTests(unittest.TestCase):
    def _with_interface(self, request, interface):
        raw = m.future_owner_supplement(
            request.core,
            request.construction,
            interface,
            request.plan,
        )
        return bind_supplement(
            replace(
                request,
                interface=interface,
                future_owner=raw,
                supplement_authority=None,
            )
        )

    def test_checked_adapter_exposes_exact_live_authorities_and_residuals(self):
        verifier = p01()
        result = m.check_projection_owner_adapter(verifier)
        self.assertIs(result.kind, m.OutcomeKind.AFFIRMATIVE)
        adapter = result.value
        self.assertIs(adapter.request, verifier)
        self.assertIs(adapter.supplement, verifier.supplement_authority)
        self.assertEqual(
            adapter.supplement_only_paths,
            m.FUTURE_OWNER_SUPPLEMENT_ONLY_PATHS,
        )
        consumer_id = adapter.supplement.capability.consumer_id
        purpose_id = adapter.supplement.capability.purpose_id
        for issued in (*adapter.k2_static_views, adapter.fs_construction_view):
            self.assertTrue(
                m.k2.validate_issued_pir_static_view(
                    issued,
                    expected_consumer_id=consumer_id,
                    expected_purpose_id=purpose_id,
                )
            )
        self.assertEqual(
            adapter.checked_fs_construction.capability.consumer_id,
            consumer_id,
        )
        self.assertEqual(
            adapter.checked_fs_construction.capability.purpose_id,
            purpose_id,
        )
        self.assertTrue(
            m.k3.validate_issued_protocol_interface_correspondence_view(
                adapter.interface_view,
                expected_consumer_id=consumer_id,
                expected_purpose_id=purpose_id,
            )
        )
        self.assertEqual(len(adapter.k2_static_views), 7)
        self.assertIsNone(adapter.checked_plan)
        prover = m.check_projection_owner_adapter(p01(m.EndpointRole.PROVER)).value
        self.assertEqual(len(prover.k2_static_views), 8)
        self.assertIs(type(prover.checked_plan), m.k3.CheckedPlanRealizes)

    def test_raw_stale_and_reconstructed_supplements_cannot_be_consumed(self):
        request = p01()
        raw = replace(request, supplement_authority=None)
        self.assertIs(
            m.check_projection_owner_adapter(raw).kind,
            m.OutcomeKind.MISSING_DEPENDENCY,
        )
        self.assertIs(m.project(raw).kind, m.OutcomeKind.MISSING_DEPENDENCY)

        reconstructed = replace(request.supplement_authority)
        forged_request = replace(request, supplement_authority=reconstructed)
        self.assertIs(
            m.check_projection_owner_adapter(forged_request).kind,
            m.OutcomeKind.REFUSED,
        )
        with self.assertRaises(ValueError):
            copy(request.supplement_authority)
        with self.assertRaises(ValueError):
            deepcopy(request.supplement_authority)
        with self.assertRaises(ValueError):
            copy(request.supplement_authority.capability)
        with self.assertRaises(ValueError):
            deepcopy(request.supplement_authority.capability)

        reconstructed_capability = replace(
            request.supplement_authority.capability
        )
        reconstructed_with_capability = replace(
            request.supplement_authority,
            capability=reconstructed_capability,
        )
        with patch.dict(
            m._LIVE_SUPPLEMENT_AUTHORITIES,
            {id(reconstructed_with_capability): reconstructed_with_capability},
        ):
            self.assertIs(
                m.check_projection_owner_adapter(
                    replace(
                        request,
                        supplement_authority=reconstructed_with_capability,
                    )
                ).kind,
                m.OutcomeKind.REFUSED,
            )

        owner = request.future_owner
        stale_owner = replace(
            owner,
            core=replace(
                owner.core,
                terminal=replace(owner.core.terminal, verdict="changed"),
            ),
        )
        stale = replace(request, future_owner=stale_owner)
        self.assertIs(
            m.check_projection_owner_adapter(stale).kind,
            m.OutcomeKind.REFUSED,
        )

    def test_external_coordinate_rotates_source_oir_and_proposition(self):
        request = p01()
        assignments = list(request.interface.inputs)
        assignments[0] = replace(
            assignments[0],
            external_coordinate=assignments[0].external_coordinate + ".v2",
        )
        changed = self._with_interface(
            request,
            replace(request.interface, inputs=tuple(assignments)),
        )
        original_source = source(request)
        changed_source = source(changed)
        original_target = target(request)
        changed_target = target(changed)
        self.assertNotEqual(original_source.view_id, changed_source.view_id)
        self.assertNotEqual(original_target.asserted_id, changed_target.asserted_id)
        original = m.form_projection_proposition(
            original_source,
            admit(original_target),
        ).value
        rotated = m.form_projection_proposition(
            changed_source,
            admit(changed_target),
        ).value
        self.assertNotEqual(original.proposition_id, rotated.proposition_id)

        transports = list(request.interface.transports)
        transports[0] = replace(
            transports[0],
            external_coordinate=transports[0].external_coordinate + ".v2",
        )
        transported = self._with_interface(
            request,
            replace(request.interface, transports=tuple(transports)),
        )
        self.assertNotEqual(source(request).view_id, source(transported).view_id)
        self.assertNotEqual(target(request).asserted_id, target(transported).asserted_id)

    def test_statement_name_and_codec_identity_are_not_erased(self):
        request = p01()
        statements = list(request.interface.statements)
        statements[0] = replace(
            statements[0],
            external_statement=statements[0].external_statement + ".v2",
        )
        renamed = self._with_interface(
            request,
            replace(request.interface, statements=tuple(statements)),
        )
        self.assertNotEqual(source(request).view_id, source(renamed).view_id)
        self.assertNotEqual(target(request).asserted_id, target(renamed).asserted_id)

        assignments = list(request.interface.inputs)
        assignments[0] = replace(
            assignments[0],
            codec_id=m._algorithm("alternate-interface-codec"),
        )
        recoded = self._with_interface(
            request,
            replace(request.interface, inputs=tuple(assignments)),
        )
        recoded_graph = target(recoded).semantic_graph
        self.assertNotEqual(target(request).asserted_id, target(recoded).asserted_id)
        self.assertIn(
            assignments[0].codec_id,
            tuple(
                item.interface_codec_id
                for item in recoded_graph.role_abi_graph.codec_nodes
            ),
        )

    def test_profile_mutation_locality_is_exact(self):
        baseline = m.K3D_SEMANTIC_PROFILES
        relation_changed = m.make_k3d_semantic_profiles(
            projection_law=b"changed-projection-and-validation-operation-law"
        )
        self.assertEqual(relation_changed.endpoint_graph, baseline.endpoint_graph)
        self.assertEqual(relation_changed.source_view, baseline.source_view)
        self.assertNotEqual(relation_changed.projection, baseline.projection)

        relations_only = m.k3.make_k3b_semantic_profiles(
            relations_law=b"changed-relations-law"
        )
        downstream = m.make_k3d_semantic_profiles(k3b_profiles=relations_only)
        self.assertEqual(downstream, baseline)
        self.assertNotIn(
            relations_only.relations_correspondence.identity,
            downstream.bundle,
        )

        interface_changed = m.k3.make_k3b_semantic_profiles(
            interface_plan_law=b"changed-interface-plan-law"
        )
        rotated = m.make_k3d_semantic_profiles(k3b_profiles=interface_changed)
        self.assertNotEqual(rotated.endpoint_graph, baseline.endpoint_graph)
        self.assertNotEqual(rotated.source_view, baseline.source_view)
        self.assertNotEqual(rotated.projection, baseline.projection)

    def test_every_k3d_root_uses_its_exact_no_extra_import_closure(self):
        profiles = m.K3D_SEMANTIC_PROFILES
        roots = (
            (profiles.endpoint_graph, profiles.endpoint_graph_bundle, 4),
            (profiles.source_view, profiles.source_view_bundle, 5),
            (profiles.projection, profiles.projection_bundle, 6),
        )
        for profile, bundle, expected_count in roots:
            with self.subTest(profile=profile.profile_family.value):
                context = m.k1.effective_semantic_context(
                    profile.identity,
                    bundle,
                    semantic_regime=m.k1.SEMANTIC_REGIME_ID,
                )
                self.assertEqual(
                    len(context.authenticated_profiles),
                    expected_count,
                )
                self.assertEqual(
                    {item for item, _ in context.authenticated_profiles},
                    set(bundle),
                )

        self.assertNotIn(
            profiles.k3b_profiles.relations_correspondence.identity,
            profiles.projection_bundle,
        )
        self.assertNotIn(
            profiles.k3b_profiles.k2_profiles.public_view.identity,
            profiles.projection_bundle,
        )


class SupplementClosureTests(unittest.TestCase):
    def _issue_with_owner(self, request, owner):
        return m.issue_future_owner_supplement(
            replace(
                request,
                future_owner=owner,
                supplement_authority=None,
            )
        )

    def _authority_binding(self):
        authority = p01().supplement_authority
        self.assertIs(type(authority), m.IssuedFutureOwnerSupplement)
        return authority

    def test_authority_binding_formation_authenticates_the_exact_source_context(self):
        authenticator = m.k1.authenticate_profiled_semantic_content
        with patch.object(
            m.k1,
            "authenticate_profiled_semantic_content",
            wraps=authenticator,
        ) as authenticated:
            authority = self._authority_binding()

        matching_calls = tuple(
            call
            for call in authenticated.call_args_list
            if call.args and call.args[0] == authority.authority_binding_id
        )
        self.assertEqual(len(matching_calls), 1)
        formation_call = matching_calls[0]
        self.assertEqual(formation_call.args[1], m.SOURCE_PROFILE)
        self.assertEqual(formation_call.args[2], authority.authority_binding.body())
        self.assertEqual(
            formation_call.args[3],
            m.K3D_SEMANTIC_PROFILES.source_view_bundle,
        )
        self.assertEqual(
            formation_call.kwargs,
            {"supported_profiles": (m.SOURCE_PROFILE,)},
        )

    def test_authority_binding_authenticates_exactly_five_profiles(self):
        authority = self._authority_binding()
        bundle = m.K3D_SEMANTIC_PROFILES.source_view_bundle
        context = m.k1.authenticate_profiled_semantic_content(
            authority.authority_binding_id,
            m.SOURCE_PROFILE,
            authority.authority_binding.body(),
            bundle,
            supported_profiles=(m.SOURCE_PROFILE,),
        )
        self.assertEqual(context.selected_profile, m.SOURCE_PROFILE)
        self.assertEqual(len(context.authenticated_profiles), 5)
        self.assertEqual(
            {profile_id for profile_id, _ in context.authenticated_profiles},
            set(bundle),
        )

    def test_authority_binding_refuses_a_missing_source_profile_preimage(self):
        authority = self._authority_binding()
        incomplete = dict(m.K3D_SEMANTIC_PROFILES.source_view_bundle)
        incomplete.pop(m.K3D_SEMANTIC_PROFILES.endpoint_graph.identity)
        with self.assertRaises(m.k1._Control) as caught:
            m.k1.authenticate_profiled_semantic_content(
                authority.authority_binding_id,
                m.SOURCE_PROFILE,
                authority.authority_binding.body(),
                incomplete,
                supported_profiles=(m.SOURCE_PROFILE,),
            )
        self.assertIs(caught.exception.outcome, m.k1.Outcome.MISSING_DEPENDENCY)
        self.assertEqual(caught.exception.code, "K1-MISSING-PROFILE")

    def test_authority_binding_refuses_an_extra_source_profile_preimage(self):
        authority = self._authority_binding()
        overcomplete = dict(m.K3D_SEMANTIC_PROFILES.source_view_bundle)
        projection = m.K3D_SEMANTIC_PROFILES.projection
        self.assertNotIn(projection.identity, overcomplete)
        overcomplete[projection.identity] = projection
        with self.assertRaises(m.k1._Control) as caught:
            m.k1.authenticate_profiled_semantic_content(
                authority.authority_binding_id,
                m.SOURCE_PROFILE,
                authority.authority_binding.body(),
                overcomplete,
                supported_profiles=(m.SOURCE_PROFILE,),
            )
        self.assertIs(caught.exception.outcome, m.k1.Outcome.REFUSED)
        self.assertEqual(caught.exception.code, "K1-REFUSED-EXTRA-PROFILE")

    def test_authority_binding_has_no_generic_json_identity_route(self):
        with self.assertRaisesRegex(TypeError, "has no language profile"):
            m._semantic_id(
                "pir.endpoint-owner-supplement-authority-binding",
                m.k1.BytesValue(b"alternate-body"),
            )

    def test_provisional_supplement_activates_only_after_the_live_owner_join(self):
        request = p01()
        authority = request.supplement_authority
        self.assertIs(
            m._PROVISIONAL_SUPPLEMENT_AUTHORITIES.get(id(authority)), authority
        )
        self.assertNotIn(id(authority), m._LIVE_SUPPLEMENT_AUTHORITIES)
        checked = m.check_projection_owner_adapter(request)
        self.assertIs(checked.kind, m.OutcomeKind.AFFIRMATIVE)
        self.assertIs(checked.value.supplement, authority)
        self.assertNotIn(id(authority), m._PROVISIONAL_SUPPLEMENT_AUTHORITIES)
        self.assertIs(m._LIVE_SUPPLEMENT_AUTHORITIES.get(id(authority)), authority)

    def test_every_closed_supplement_table_rejects_duplicate_keys(self):
        verifier = p01()
        owner = verifier.future_owner
        assert owner is not None
        mutations = {
            "claims": replace(
                owner,
                core=replace(
                    owner.core,
                    claims=owner.core.claims + (owner.core.claims[0],),
                ),
            ),
            "reductions": replace(
                owner,
                core=replace(
                    owner.core,
                    reductions=owner.core.reductions + (owner.core.reductions[0],),
                ),
            ),
            "challenges": replace(
                owner,
                fs=replace(
                    owner.fs,
                    challenges=owner.fs.challenges + (owner.fs.challenges[0],),
                ),
            ),
            "statement-aliases": replace(
                owner,
                interface=replace(
                    owner.interface,
                    statement_aliases=(
                        owner.interface.statement_aliases
                        + (owner.interface.statement_aliases[0],)
                    ),
                ),
            ),
            "transports": replace(
                owner,
                interface=replace(
                    owner.interface,
                    transports=(
                        owner.interface.transports
                        + (owner.interface.transports[0],)
                    ),
                ),
            ),
            "completions": replace(
                owner,
                interface=replace(
                    owner.interface,
                    completions=(
                        owner.interface.completions
                        + (owner.interface.completions[0],)
                    ),
                ),
            ),
        }
        for label, changed in mutations.items():
            with self.subTest(label=label):
                self.assertIs(
                    self._issue_with_owner(verifier, changed).kind,
                    m.OutcomeKind.REFUSED,
                )

        prover = p01(m.EndpointRole.PROVER)
        prover_owner = prover.future_owner
        assert prover_owner is not None and prover_owner.plan is not None
        duplicate_recipe = replace(
            prover_owner,
            plan=replace(
                prover_owner.plan,
                recipes=prover_owner.plan.recipes + (prover_owner.plan.recipes[0],),
            ),
        )
        self.assertIs(
            self._issue_with_owner(prover, duplicate_recipe).kind,
            m.OutcomeKind.REFUSED,
        )

        exported_plan = replace(
            prover.plan,
            exports=(m.k3.PlanExport("copy", "response", m.k3.NAT),),
        )
        exported_owner = m.future_owner_supplement(
            prover.core,
            prover.construction,
            prover.interface,
            exported_plan,
        )
        assert exported_owner.plan is not None
        duplicate_export = replace(
            exported_owner,
            plan=replace(
                exported_owner.plan,
                derived_exports=(
                    exported_owner.plan.derived_exports
                    + (exported_owner.plan.derived_exports[0],)
                ),
            ),
        )
        exported_request = replace(
            prover,
            plan=exported_plan,
            future_owner=duplicate_export,
            supplement_authority=None,
        )
        self.assertIs(
            m.issue_future_owner_supplement(exported_request).kind,
            m.OutcomeKind.REFUSED,
        )

    def test_claim_origins_are_exact_owner_overlap_not_just_name_and_arity(self):
        request = p01()
        owner = request.future_owner
        assert owner is not None
        initial = owner.core.claims[0]
        reanchored = replace(initial, source_name="g")
        changed = replace(
            owner,
            core=replace(
                owner.core,
                claims=(reanchored,) + owner.core.claims[1:],
            ),
        )
        answer = self._issue_with_owner(request, changed)
        self.assertIs(answer.kind, m.OutcomeKind.REFUSED)
        self.assertIn("claim origin", answer.reason)

    def test_unique_rows_outside_each_closed_owner_set_are_refused(self):
        verifier = p01()
        owner = verifier.future_owner
        assert owner is not None
        extra_claim = replace(owner.core.claims[0], claim_key="phantom-claim")
        extra_reduction = replace(
            owner.core.reductions[0], reduction_name="phantom-reduction"
        )
        extra_challenge = replace(
            owner.fs.challenges[0], occurrence="terminal"
        )
        extra_statement = replace(
            owner.interface.statement_aliases[0],
            external_statement="phantom-statement",
            binding_input="g",
            slot_key="input:g",
            invocation_input="g",
        )
        extra_transport = replace(
            owner.interface.transports[0],
            occurrence="terminal",
            source=m.TransportActor.PUBLIC_DERIVATION,
            destination=m.TransportDestination.EXTERNAL_APPLICATION,
        )
        extra_completion = replace(
            owner.interface.completions[0],
            target="phantom-completion",
            external_tag="phantom-completion",
        )
        mutations = {
            "claim": replace(
                owner,
                core=replace(
                    owner.core,
                    claims=owner.core.claims + (extra_claim,),
                ),
            ),
            "reduction": replace(
                owner,
                core=replace(
                    owner.core,
                    reductions=owner.core.reductions + (extra_reduction,),
                ),
            ),
            "challenge": replace(
                owner,
                fs=replace(
                    owner.fs,
                    challenges=owner.fs.challenges + (extra_challenge,),
                ),
            ),
            "statement": replace(
                owner,
                interface=replace(
                    owner.interface,
                    statement_aliases=(
                        owner.interface.statement_aliases + (extra_statement,)
                    ),
                ),
            ),
            "transport": replace(
                owner,
                interface=replace(
                    owner.interface,
                    transports=owner.interface.transports + (extra_transport,),
                ),
            ),
            "completion": replace(
                owner,
                interface=replace(
                    owner.interface,
                    completions=owner.interface.completions + (extra_completion,),
                ),
            ),
        }
        for label, changed in mutations.items():
            with self.subTest(label=label):
                self.assertIs(
                    self._issue_with_owner(verifier, changed).kind,
                    m.OutcomeKind.REFUSED,
                )

        prover = p01(m.EndpointRole.PROVER)
        prover_owner = prover.future_owner
        assert prover_owner is not None and prover_owner.plan is not None
        extra_recipe = replace(
            prover_owner.plan.recipes[0],
            decision="challenge",
        )
        with_extra_recipe = replace(
            prover_owner,
            plan=replace(
                prover_owner.plan,
                recipes=prover_owner.plan.recipes + (extra_recipe,),
            ),
        )
        self.assertIs(
            self._issue_with_owner(prover, with_extra_recipe).kind,
            m.OutcomeKind.REFUSED,
        )
        extra_export = (
            "phantom-export",
            "response",
            m.OwnerPlanOperand(m.PlanOperandKind.NODE_OUTPUT, node_ordinal=0),
            m.k3.NAT,
        )
        with_extra_export = replace(
            prover_owner,
            plan=replace(
                prover_owner.plan,
                derived_exports=prover_owner.plan.derived_exports + (extra_export,),
            ),
        )
        self.assertIs(
            self._issue_with_owner(prover, with_extra_export).kind,
            m.OutcomeKind.REFUSED,
        )

    def test_generic_prover_is_unsupported_before_supplement_admission(self):
        request = replace(
            p01(m.EndpointRole.PROVER),
            plan=None,
            future_owner=None,
            supplement_authority=None,
        )
        answer = m.classify_support(request)
        self.assertIs(answer.kind, m.OutcomeKind.UNSUPPORTED)
        self.assertEqual(
            answer.unsupported_reasons,
            (m.SupportReason.GENERIC_PROVER_ENDPOINT,),
        )


class AuthoritySealingTests(unittest.TestCase):
    def setUp(self):
        self.request = p01()
        support = m.classify_support(self.request)
        self.assertIs(support.kind, m.OutcomeKind.AFFIRMATIVE)
        self.basis = support.value
        extracted = m.extract_endpoint_source_view(self.basis)
        self.assertIs(extracted.kind, m.OutcomeKind.AFFIRMATIVE)
        self.source = extracted.value
        projected = m.project_supported_endpoint(self.basis)
        self.assertIs(projected.kind, m.OutcomeKind.AFFIRMATIVE)
        self.endpoint = projected.value
        self.admitted = admit(self.endpoint)
        formed = m.form_projection_proposition(self.source, self.admitted)
        self.assertIs(formed.kind, m.OutcomeKind.AFFIRMATIVE)
        self.formed = formed.value
        validation_answer = m.form_projection_validation_request(
            self.source,
            self.admitted,
        )
        self.assertIs(validation_answer.kind, m.OutcomeKind.AFFIRMATIVE)
        self.validation = validation_answer.value
        checked = m.check_projection(self.validation)
        self.assertIs(checked.kind, m.OutcomeKind.AFFIRMATIVE)
        self.checked = checked.value

    def test_exact_basis_and_adapter_chain_is_retained_through_validation(self):
        self.assertIs(self.source.basis, self.basis)
        self.assertIs(self.source.adapter, self.basis.adapter)
        self.assertIs(self.validation.basis, self.basis)
        self.assertIs(self.validation.adapter, self.basis.adapter)
        self.assertIs(self.checked.validation, self.validation)
        self.assertTrue(m._is_live_checked_projection(self.checked))
        self.assertIs(
            m.project_supported_endpoint(replace(self.basis)).kind,
            m.OutcomeKind.REFUSED,
        )

    def test_copy_and_replace_reconstruction_fails_at_every_consumed_boundary(self):
        carriers = (
            self.basis,
            self.source,
            self.admitted,
            self.formed,
            self.validation,
            self.checked,
        )
        for carrier in carriers:
            with self.subTest(copy=type(carrier).__name__):
                with self.assertRaises(ValueError):
                    copy(carrier)
                with self.assertRaises(ValueError):
                    deepcopy(carrier)

        self.assertIs(
            m.extract_endpoint_source_view(replace(self.basis)).kind,
            m.OutcomeKind.REFUSED,
        )
        self.assertIs(
            m.form_projection_proposition(replace(self.source), self.admitted).kind,
            m.OutcomeKind.REFUSED,
        )
        self.assertIs(
            m.form_projection_proposition(self.source, replace(self.admitted)).kind,
            m.OutcomeKind.REFUSED,
        )
        forged_formed = replace(self.formed)
        forged_validation = replace(self.validation, proposition=forged_formed)
        with patch.dict(
            m._LIVE_VALIDATION_REQUESTS,
            {id(forged_validation): forged_validation},
        ):
            self.assertIs(
                m.check_projection(forged_validation).kind,
                m.OutcomeKind.REFUSED,
            )
        self.assertIs(
            m.check_projection(replace(self.validation)).kind,
            m.OutcomeKind.REFUSED,
        )
        self.assertFalse(m._is_live_checked_projection(replace(self.checked)))

    def test_coherent_graph_mutations_cannot_reconstruct_source_or_admission(self):
        changed_endpoint = graph_with(
            self.endpoint,
            static_fs_semantics=replace(
                self.endpoint.semantic_graph.static_fs_semantics,
                application_domain=b"coherent-authority-forgery",
            ),
        )
        changed_admitted = admit(changed_endpoint)
        changed_view = replace(
            self.source.view,
            semantic_graph=changed_endpoint.semantic_graph,
        )
        reconstructed_source = replace(
            self.source,
            view=changed_view,
            view_id=m.endpoint_source_view_id(changed_view),
        )
        self.assertIs(
            m.form_projection_proposition(
                reconstructed_source,
                changed_admitted,
            ).kind,
            m.OutcomeKind.REFUSED,
        )

        reconstructed_admission = replace(
            self.admitted,
            endpoint=changed_endpoint,
            oir_id=changed_endpoint.asserted_id,
        )
        self.assertIs(
            m.form_projection_proposition(self.source, reconstructed_admission).kind,
            m.OutcomeKind.REFUSED,
        )

    def test_validation_request_recomputes_every_derived_audit_field(self):
        mutations = {
            "source-handles": {
                "source_handles": self.validation.source_handles + ("forged",)
            },
            "schema-set": {"schema_set_id": object()},
            "manifest": {"manifest_id": object()},
            "provenance": {"provenance": "forged-provenance"},
            "source-label": {"source_label": "forged-source"},
        }
        for label, change in mutations.items():
            forged = replace(self.validation, **change)
            with self.subTest(label=label), patch.dict(
                m._LIVE_VALIDATION_REQUESTS,
                {id(forged): forged},
            ):
                self.assertIs(
                    m.check_projection(forged).kind,
                    m.OutcomeKind.REFUSED,
                )


class QualifiedOutcomeTests(unittest.TestCase):
    def test_pipeline_records_unattempted_stages_without_fake_refusals(self):
        run = m.project_admit_check(m.live_p01_request())
        self.assertIs(run.produced.kind, m.OutcomeKind.MISSING_DEPENDENCY)
        self.assertIsNone(run.admitted)
        self.assertIsNone(run.checked)

    def test_invalid_owner_is_refused_before_proposition_formation(self):
        request = p01()
        owner = request.future_owner
        assert owner is not None
        bad_interface = replace(
            owner.interface,
            codecs=owner.interface.codecs + (owner.interface.codecs[0],),
        )
        answer = m.project(
            replace(request, future_owner=replace(owner, interface=bad_interface))
        )
        self.assertIs(answer.kind, m.OutcomeKind.REFUSED)
        self.assertNotEqual(answer.kind, m.OutcomeKind.NEGATIVE)

    def test_extractor_and_target_faults_are_checker_failures_not_negatives(self):
        request = p01()
        support = m.classify_support(request)
        self.assertIs(support.kind, m.OutcomeKind.AFFIRMATIVE)
        with patch.object(
            m, "_extract_source_graph", side_effect=ValueError("injected extractor fault")
        ):
            extracted = m.extract_endpoint_source_view(support.value)
        self.assertIs(extracted.kind, m.OutcomeKind.CHECKER_FAILURE)

        with patch.object(
            m, "_construct_target_graph", side_effect=ValueError("injected target fault")
        ):
            produced = m.project(request)
        self.assertIs(produced.kind, m.OutcomeKind.CHECKER_FAILURE)

    def test_unexpected_owner_checker_faults_are_not_semantic_failures(self):
        interface_request = p01()
        owner_plan_request = p01(m.EndpointRole.PROVER)
        core_request = p01()
        protocol_request = p01()
        interface_admission_request = p01()
        plan_request = p01(m.EndpointRole.PROVER)

        with patch.object(
            m.k3,
            "required_protocol_interface_read_closure",
            side_effect=RuntimeError("injected checker fault"),
        ):
            interface_closure = m.classify_support(interface_request)
        self.assertIs(interface_closure.kind, m.OutcomeKind.CHECKER_FAILURE)

        with patch.object(
            m.k3,
            "check_plan_realizes",
            side_effect=RuntimeError("injected checker fault"),
        ):
            owner_plan = m.check_projection_owner_adapter(
                owner_plan_request
            )
        self.assertIs(owner_plan.kind, m.OutcomeKind.CHECKER_FAILURE)

        with patch.object(
            m.k2,
            "admit_core",
            side_effect=RuntimeError("injected checker fault"),
        ):
            core_admission = m.classify_support(core_request)
        self.assertIs(core_admission.kind, m.OutcomeKind.CHECKER_FAILURE)

        with patch.object(
            m.k3,
            "protocol_id",
            side_effect=RuntimeError("injected checker fault"),
        ):
            protocol_admission = m.classify_support(protocol_request)
        self.assertIs(protocol_admission.kind, m.OutcomeKind.CHECKER_FAILURE)

        with patch.object(
            m.k3,
            "admit_interface",
            side_effect=RuntimeError("injected checker fault"),
        ):
            interface_admission = m.classify_support(interface_admission_request)
        self.assertIs(interface_admission.kind, m.OutcomeKind.CHECKER_FAILURE)

        with patch.object(
            m.k3,
            "check_plan_realizes",
            side_effect=RuntimeError("injected checker fault"),
        ):
            plan_realizes = m.classify_support(plan_request)
        self.assertIs(plan_realizes.kind, m.OutcomeKind.CHECKER_FAILURE)

    def test_all_declared_outcomes_are_exercised(self):
        observed = {m.OutcomeKind.AFFIRMATIVE}
        request = p01()
        endpoint = target(request)
        changed = graph_with(
            endpoint,
            static_fs_semantics=replace(
                endpoint.semantic_graph.static_fs_semantics,
                application_domain=b"negative",
            ),
        )
        observed.add(m.check_projection(validation(request, changed)).kind)
        observed.add(m.project(m.live_p01_request()).kind)
        observed.add(
            m.project(
                replace(
                    request,
                    interpretation=m.k2.ChallengeInterpretation.FRESH,
                )
            ).kind
        )
        observed.add(m.project(replace(request, construction=None)).kind)
        observed.add(
            m.local_admit(replace(endpoint, semantic_profile="wrong-profile")).kind
        )
        observed.add(
            m.local_admit(
                replace(
                    endpoint,
                    asserted_id=m._fixed_ref("oir.endpoint", "false"),
                )
            ).kind
        )
        forged = replace(admit(endpoint))
        observed.add(m.form_projection_proposition(source(request), forged).kind)
        limited = m.form_projection_validation_request(
            source(request), admit(endpoint), work_limit=1
        ).value
        observed.add(m.check_projection(limited).kind)
        ordinary = validation(request, endpoint)
        observed.add(m.check_projection(ordinary, simulate_checker_failure=True).kind)
        self.assertEqual(observed, set(m.OutcomeKind))

    def test_json_identity_is_explicitly_a_probe_surrogate(self):
        encoded = m.canonical_bytes(target(p01()).semantic_graph)
        self.assertTrue(encoded.startswith(b"{"))
        self.assertIn(b'"role"', encoded)
        self.assertNotEqual(encoded, m.k1.encode_datum(m.k1.BytesValue(encoded)))


if __name__ == "__main__":
    unittest.main()
