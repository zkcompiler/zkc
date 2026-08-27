from __future__ import annotations

from dataclasses import fields, replace
import importlib.util
from pathlib import Path
import sys
import unittest


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
        self.assertEqual(len(m.OWNER_SCHEMA_PATHS), 188)
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
        codecs[0] = m.CodecNode(m.CodecKind.GENERAL, general_law_dependency=0)
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
        dead = replace(
            request,
            plan=replace(plan, private_material=plan.private_material + (extra,)),
        )
        export = m.k3.PlanExport("copy", "response", m.k3.NAT)
        exported_plan = replace(plan, exports=(export,))
        exported = replace(
            request,
            plan=exported_plan,
            future_owner=m._future_owner(
                request.core, request.construction, exported_plan
            ),
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
        changed = replace(
            request,
            plan=plan,
            future_owner=m._future_owner(request.core, request.construction, plan),
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
        self.assertNotEqual(left.validation_request_id, right.validation_request_id)

    def test_runtime_receipt_is_inert(self):
        first = p01()
        second = replace(first, runtime_receipt={"draws": 7, "result": 3})
        self.assertEqual(target(first).asserted_id, target(second).asserted_id)
        self.assertEqual(source(first).view_id, source(second).view_id)
        self.assertEqual(
            checked_projection(first).validation_request_id,
            checked_projection(second).validation_request_id,
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
        forged = m.AdmittedOir(object(), self.prover, self.prover.asserted_id)
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


class QualifiedOutcomeTests(unittest.TestCase):
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
        forged = m.AdmittedOir(object(), endpoint, endpoint.asserted_id)
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
