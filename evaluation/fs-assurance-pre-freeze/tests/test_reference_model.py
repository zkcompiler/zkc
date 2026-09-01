from __future__ import annotations

from dataclasses import replace
from pathlib import Path
import json
import sys
import unittest


ROOT = Path(__file__).resolve().parents[1]
REPOSITORY = ROOT.parents[1]
sys.path.insert(0, str(ROOT))

import reference_model as m  # noqa: E402


def base_frames() -> tuple[m.Frame, ...]:
    return (
        m.Frame("core-header", "core", b"core-v1"),
        m.Frame("construction-header", "construction", b"fs-v1"),
        m.Frame("application-domain", "application", b"zkc/test"),
        m.Frame("statement", "binding:statement", b"Y"),
        m.Frame("prover-message", "commitment", b"A"),
    )


def base_prefix() -> m.ChallengePrefix:
    return m.ChallengePrefix("challenge:0", base_frames())


def contract() -> m.FSStaticContract:
    return m.FSStaticContract(
        "construction:canonical-fs-v1",
        "law:typed-frames-v1",
        "law:derived-prefix-v1",
        "law:namespace-v1",
        "algorithm:absorb-v1",
        "algorithm:squeeze-v1",
        "algorithm:advance-v1",
        "law:sampler-v1",
        "failure:sampling-exhausted-v1",
    )


def logical_query(*, session: bytes = b"session", instance: bytes = b"Y") -> m.LogicalQuery:
    return m.LogicalQuery(
        session,
        instance,
        (m.Frame("prover-message", "commitment", b"A"),),
        b"challenge:0/draw:0",
    )


class StructuralAndStatementTest(unittest.TestCase):
    def test_exact_prefix_positive_control(self) -> None:
        self.assertIs(
            m.check_exact_prefix(base_prefix(), base_prefix()).outcome,
            m.Outcome.AFFIRMATIVE,
        )

    def test_missing_statement_is_detected(self) -> None:
        actual = m.ChallengePrefix(
            "challenge:0",
            tuple(frame for frame in base_frames() if frame.tag != "statement"),
        )
        answer = m.check_exact_prefix(base_prefix(), actual)
        self.assertIs(answer.outcome, m.Outcome.NEGATIVE)
        self.assertIn("omitted-or-substituted-frame", answer.reasons)

    def test_missing_last_challenge_material_is_detected(self) -> None:
        expected = m.ChallengePrefix(
            "challenge:batch",
            base_frames()
            + (
                m.Frame("prover-message", "opening-proof:w1", b"W1"),
                m.Frame("prover-message", "opening-proof:w2", b"W2"),
            ),
        )
        actual = replace(expected, frames=expected.frames[:-2])
        self.assertIs(
            m.check_exact_prefix(expected, actual).outcome,
            m.Outcome.NEGATIVE,
        )

    def test_reordering_is_detected_even_with_same_multiset(self) -> None:
        frames = list(base_frames())
        frames[-1], frames[-2] = frames[-2], frames[-1]
        answer = m.check_exact_prefix(
            base_prefix(), m.ChallengePrefix("challenge:0", tuple(frames))
        )
        self.assertEqual(answer.reasons, ("reordered-frame",))

    def test_duplicate_is_detected(self) -> None:
        frames = base_frames() + (base_frames()[-1],)
        answer = m.check_exact_prefix(
            base_prefix(), m.ChallengePrefix("challenge:0", frames)
        )
        self.assertIn("injected-or-duplicated-frame", answer.reasons)

    def test_weak_authored_schedule_can_pass_structure_but_fail_manifest(self) -> None:
        weak = m.ChallengePrefix(
            "challenge:0",
            tuple(frame for frame in base_frames() if frame.tag != "statement"),
        )
        self.assertIs(m.check_exact_prefix(weak, weak).outcome, m.Outcome.AFFIRMATIVE)
        manifest = m.ClosedStatementManifest(
            (m.StatementRoute("external:Y", "binding:statement"),)
        )
        answer = m.check_closed_statement_correspondence(manifest, (), weak)
        self.assertIs(answer.outcome, m.Outcome.NEGATIVE)
        self.assertIn("missing-external-statement-route", answer.reasons)

    def test_closed_statement_correspondence_positive_control(self) -> None:
        route = m.StatementRoute("external:Y", "binding:statement")
        answer = m.check_closed_statement_correspondence(
            m.ClosedStatementManifest((route,)), (route,), base_prefix()
        )
        self.assertIs(answer.outcome, m.Outcome.AFFIRMATIVE)

    def test_substituted_external_statement_route_is_detected(self) -> None:
        expected = m.StatementRoute("external:Y", "binding:statement")
        supplied = m.StatementRoute("external:other", "binding:statement")
        answer = m.check_closed_statement_correspondence(
            m.ClosedStatementManifest((expected,)), (supplied,), base_prefix()
        )
        self.assertIs(answer.outcome, m.Outcome.NEGATIVE)
        self.assertIn("extra-or-substituted-statement-route", answer.reasons)


class EncodingAndTransitionTest(unittest.TestCase):
    def test_typed_length_delimited_control_has_no_selected_alias(self) -> None:
        domain = (
            (m.Frame("message", "0", b"a"), m.Frame("message", "1", b"bc")),
            (m.Frame("message", "0", b"ab"), m.Frame("message", "1", b"c")),
            (m.Frame("statement", "0", b"a"), m.Frame("message", "1", b"bc")),
        )
        self.assertEqual(m.find_aliases(domain, m.canonical_frame_encoding), ())

    def test_unframed_concatenation_has_boundary_alias(self) -> None:
        domain = (
            (m.Frame("message", "0", b"a"), m.Frame("message", "1", b"bc")),
            (m.Frame("message", "0", b"ab"), m.Frame("message", "1", b"c")),
        )
        aliases = m.find_aliases(domain, m.unframed_payload_encoding)
        self.assertEqual(len(aliases), 1)
        self.assertEqual(aliases[0].image, b"abc")

    def test_missing_length_marker_makes_trailing_zero_free(self) -> None:
        domain = ((7,), (7, 0), (7, 0, 0))
        self.assertEqual(
            len(m.find_aliases(domain, m.trailing_zero_aliased_projection)), 2
        )

    def test_length_marker_separates_trailing_zero_streams(self) -> None:
        domain = ((7,), (7, 0), (7, 0, 0))
        self.assertEqual(m.find_aliases(domain, m.complete_limb_projection), ())

    def test_floor_sized_projection_drops_high_bits(self) -> None:
        domain = (1, 257, 513)
        aliases = m.find_aliases(domain, m.high_bit_truncated_projection)
        self.assertEqual(len(aliases), 2)

    def test_full_width_projection_keeps_selected_high_bits(self) -> None:
        self.assertEqual(
            m.find_aliases((1, 257, 513), m.full_width_field_projection), ()
        )

    def test_structural_exactness_does_not_imply_concrete_binding(self) -> None:
        self.assertIs(
            m.check_exact_prefix(base_prefix(), base_prefix()).outcome,
            m.Outcome.AFFIRMATIVE,
        )
        aliases = m.find_aliases(
            ((7,), (7, 0)), m.trailing_zero_aliased_projection
        )
        self.assertTrue(aliases)


class SamplerTest(unittest.TestCase):
    def test_total_power_of_two_sampler_is_exact_uniform(self) -> None:
        report = m.analyze_sampler(range(256), range(8), lambda draw: draw % 8)
        self.assertIs(
            m.qualify_sampler(
                report, m.SamplerExpectation.TOTAL_EXACT_UNIFORM
            ).outcome,
            m.Outcome.AFFIRMATIVE,
        )

    def test_modulo_three_sampler_is_biased(self) -> None:
        report = m.analyze_sampler(range(256), range(3), lambda draw: draw % 3)
        answer = m.qualify_sampler(
            report, m.SamplerExpectation.TOTAL_EXACT_UNIFORM
        )
        self.assertIs(answer.outcome, m.Outcome.NEGATIVE)
        self.assertIn("biased-challenge-distribution", answer.reasons)

    def test_rejection_sampler_is_not_total_uniform(self) -> None:
        report = m.analyze_sampler(
            range(4), range(3), lambda draw: draw if draw < 3 else None
        )
        self.assertIs(
            m.qualify_sampler(
                report, m.SamplerExpectation.TOTAL_EXACT_UNIFORM
            ).outcome,
            m.Outcome.NEGATIVE,
        )

    def test_rejection_sampler_requires_explicit_failure_accounting(self) -> None:
        report = m.analyze_sampler(
            range(4), range(3), lambda draw: draw if draw < 3 else None
        )
        unmodeled = m.qualify_sampler(
            report,
            m.SamplerExpectation.CONDITIONAL_UNIFORM_WITH_FAILURE_TERM,
        )
        modeled = m.qualify_sampler(
            report,
            m.SamplerExpectation.CONDITIONAL_UNIFORM_WITH_FAILURE_TERM,
            explicit_failure_term=True,
        )
        self.assertIs(unmodeled.outcome, m.Outcome.CANNOT_ANSWER)
        self.assertIs(modeled.outcome, m.Outcome.AFFIRMATIVE)


class QueryProjectionAndRealizationTest(unittest.TestCase):
    def test_canonical_query_binds_session_instance_and_namespace(self) -> None:
        queries = (
            logical_query(),
            logical_query(session=b"other-session"),
            logical_query(instance=b"other-instance"),
            replace(logical_query(), namespace=b"challenge:0/draw:1"),
        )
        self.assertEqual(m.find_aliases(queries, m.canonical_query_index), ())

    def test_weak_query_index_aliases_sessions_and_statements(self) -> None:
        queries = (
            logical_query(),
            logical_query(session=b"other-session"),
            logical_query(instance=b"other-instance"),
        )
        self.assertEqual(len(m.find_aliases(queries, m.weak_query_index)), 2)

    def test_static_projection_positive_control(self) -> None:
        source = contract()
        projection = m.exact_oir_projection(source)
        self.assertIs(
            m.check_projection(source, projection).outcome,
            m.Outcome.AFFIRMATIVE,
        )

    def test_static_projection_cannot_drop_prefix_law(self) -> None:
        source = contract()
        projection = replace(
            m.exact_oir_projection(source),
            derived_prefix_law_id="law:manual-prefix-v1",
        )
        answer = m.check_projection(source, projection)
        self.assertEqual(answer.reasons, ("projection:derived_prefix_law_id",))

    def test_bounded_realization_vectors_positive_control(self) -> None:
        source = contract()
        query = logical_query()
        index = m.canonical_query_index(query)
        candidate = m.RealizationCandidate(
            source.construction_id,
            (
                source.absorb_algorithm_id,
                source.squeeze_algorithm_id,
                source.advance_algorithm_id,
            ),
            m.canonical_query_index,
            m.byte_challenge,
            True,
        )
        answer = m.check_realization(
            source,
            candidate,
            (m.ConformanceVector(query, m.byte_challenge(index)),),
        )
        self.assertIs(answer.outcome, m.Outcome.AFFIRMATIVE)

    def test_realization_using_weak_query_index_is_rejected(self) -> None:
        source = contract()
        query = logical_query()
        candidate = m.RealizationCandidate(
            source.construction_id,
            (
                source.absorb_algorithm_id,
                source.squeeze_algorithm_id,
                source.advance_algorithm_id,
            ),
            m.weak_query_index,
            m.byte_challenge,
            True,
        )
        answer = m.check_realization(
            source,
            candidate,
            (
                m.ConformanceVector(
                    query, m.byte_challenge(m.canonical_query_index(query))
                ),
            ),
        )
        self.assertIn("logical-query-index-mismatch", answer.reasons)

    def test_parser_must_consume_entire_proof(self) -> None:
        source = contract()
        query = logical_query()
        candidate = m.RealizationCandidate(
            source.construction_id,
            (
                source.absorb_algorithm_id,
                source.squeeze_algorithm_id,
                source.advance_algorithm_id,
            ),
            m.canonical_query_index,
            m.byte_challenge,
            False,
        )
        answer = m.check_realization(
            source,
            candidate,
            (
                m.ConformanceVector(
                    query, m.byte_challenge(m.canonical_query_index(query))
                ),
            ),
        )
        self.assertIn("parser-did-not-reach-end-of-input", answer.reasons)


class ClaimQualificationTest(unittest.TestCase):
    def test_formally_verified_verifier_does_not_supply_security_theorem(self) -> None:
        supplied = m.evidence(
            (
                "structural-prefix-completeness",
                "closed-statement-correspondence",
                "encoding-adequacy",
                "oir-projection-preservation",
                "realization-conformance",
            ),
            kind="verified-refinement-or-translation-validation",
        )
        answer = m.qualify_claim(m.CLASSICAL_FS_ACTIVATION_PREMISES, supplied)
        self.assertIs(answer.outcome, m.Outcome.MISSING_DEPENDENCY)
        self.assertIn("missing:theorem-applicability", answer.reasons)
        self.assertIn("missing:interactive-source-property", answer.reasons)

    def test_bcs_label_does_not_supply_state_restoration_premise(self) -> None:
        supplied = m.evidence(m.CLASSICAL_FS_ACTIVATION_PREMISES)
        del supplied["interactive-source-property"]
        supplied["bcs-transform-selected"] = m.PremiseEvidence(
            "bcs-transform-selected", True, "construction-label"
        )
        answer = m.qualify_claim(m.CLASSICAL_FS_ACTIVATION_PREMISES, supplied)
        self.assertIn("missing:interactive-source-property", answer.reasons)

    def test_classical_rom_result_does_not_upgrade_to_qrom(self) -> None:
        supplied = m.evidence(m.CLASSICAL_FS_ACTIVATION_PREMISES)
        required = m.CLASSICAL_FS_ACTIVATION_PREMISES + m.QROM_ADDITIONAL_PREMISES
        answer = m.qualify_claim(required, supplied)
        self.assertIs(answer.outcome, m.Outcome.MISSING_DEPENDENCY)
        self.assertIn("missing:qrom-theorem-applicability", answer.reasons)

    def test_false_premise_produces_negative_not_success(self) -> None:
        supplied = m.evidence(m.CLASSICAL_FS_ACTIVATION_PREMISES)
        supplied["encoding-adequacy"] = m.PremiseEvidence(
            "encoding-adequacy", False, "counterexample"
        )
        answer = m.qualify_claim(m.CLASSICAL_FS_ACTIVATION_PREMISES, supplied)
        self.assertEqual(answer.reasons, ("falsified:encoding-adequacy",))

    def test_complete_finite_chain_is_only_a_bounded_control(self) -> None:
        supplied = m.evidence(m.CLASSICAL_FS_ACTIVATION_PREMISES)
        answer = m.qualify_claim(m.CLASSICAL_FS_ACTIVATION_PREMISES, supplied)
        self.assertIs(answer.outcome, m.Outcome.AFFIRMATIVE)
        self.assertTrue(
            all(item.evidence_kind == "bounded-control" for item in answer.value)
        )


class PackageIntegrityTest(unittest.TestCase):
    def test_attack_matrix_has_unique_cases_and_known_layers(self) -> None:
        matrix = json.loads(
            (ROOT / "cases" / "attack-matrix.json").read_text(encoding="utf-8")
        )
        cases = matrix["cases"]
        ids = tuple(item["id"] for item in cases)
        self.assertEqual(len(ids), len(set(ids)))
        known_layers = set(matrix["assurance_layers"])
        self.assertTrue(cases)
        for item in cases:
            self.assertTrue(set(item["detection_layers"]).issubset(known_layers))
            self.assertTrue(item["positive_control"])

    def test_runner_is_listed_in_semantic_aggregate(self) -> None:
        aggregate = (REPOSITORY / "evaluation" / "semantic_checks.py").read_text(
            encoding="utf-8"
        )
        self.assertIn("evaluation/fs-assurance-pre-freeze/run.py", aggregate)


if __name__ == "__main__":
    unittest.main()
