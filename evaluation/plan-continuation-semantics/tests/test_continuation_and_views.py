from __future__ import annotations

from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

import fixtures  # noqa: E402
import reference_model as m  # noqa: E402


TEST_CONSUMER = m.DownstreamConsumerId("tests.continuation-view")
TEST_PURPOSE = m.DownstreamPurposeId("tests.confidential-inspection")


def execute(case: m.FamilyCase):
    checked = m.admit_plan(case.core, case.plan)
    prepared = m.prepare_plan_execution(
        case.core, case.construction, case.invocation, case.plan, checked,
        case.private_values, case.randomness_values,
    ).value
    generated = m.generate_plan_run(prepared[0], prepared[1], case.fresh_values).value
    completed, continuation_cap = m.complete_accepted_plan_continuation(
        generated, generated.plan_capability, generated.continuation_right
    ).value
    return generated, completed, continuation_cap


class ContinuationViewTests(unittest.TestCase):
    def test_source_requirements_match_occurrence_classes(self) -> None:
        for case in fixtures.family_cases():
            with self.subTest(case=case.name):
                surface = m.plan_witness_surface(case.plan)
                arm = {
                    item.key
                    for item in m.continuation_arm(case.core, case.plan, "terminal")
                }
                terminal = {
                    item.key for item in surface.entries
                    if item.key in arm and item.occurrence_class is m.OccurrenceClass.TERMINAL
                }
                actual = m.SourceRequirement.FINALIZED if terminal else m.SourceRequirement.GENERATED
                self.assertIs(actual, case.expected_requirement)

    def test_generated_source_cannot_disclose_terminal_output(self) -> None:
        case = fixtures.family_cases()[0]
        generated, _, _ = execute(case)
        surface = m.plan_witness_surface(case.plan)
        result = m.issue_confidential_plan_witness_view(
            generated,
            generated.plan_capability,
            surface,
            ("folded",),
            TEST_CONSUMER,
            TEST_PURPOSE,
        )
        self.assertIs(result.outcome, m.Outcome.REFUSED)

    def test_finalized_source_discloses_terminal_output(self) -> None:
        case = fixtures.family_cases()[0]
        _, completed, cap = execute(case)
        surface = m.plan_witness_surface(case.plan)
        result = m.issue_confidential_plan_witness_view(
            completed,
            cap,
            surface,
            ("folded",),
            TEST_CONSUMER,
            TEST_PURPOSE,
        )
        self.assertIs(result.outcome, m.Outcome.AFFIRMATIVE)
        self.assertEqual(result.value[0].source_tag, "Finalized")

    def test_cyclefold_generated_primary_but_not_mixed_manifest(self) -> None:
        case = fixtures.family_cases()[2]
        generated, _, _ = execute(case)
        surface = m.plan_witness_surface(case.plan)
        primary = m.issue_confidential_plan_witness_view(
            generated,
            generated.plan_capability,
            surface,
            ("primary_out",),
            TEST_CONSUMER,
            TEST_PURPOSE,
        )
        mixed = m.issue_confidential_plan_witness_view(
            generated, generated.plan_capability, surface,
            ("companion_out", "primary_out"), TEST_CONSUMER, TEST_PURPOSE,
        )
        self.assertIs(primary.outcome, m.Outcome.AFFIRMATIVE)
        self.assertIs(mixed.outcome, m.Outcome.REFUSED)

    def test_decision_only_family_uses_generated_source(self) -> None:
        case = fixtures.family_cases()[3]
        generated, _, _ = execute(case)
        surface = m.plan_witness_surface(case.plan)
        result = m.issue_confidential_plan_witness_view(
            generated, generated.plan_capability, surface,
            ("accumulator_witness",), TEST_CONSUMER, TEST_PURPOSE,
        )
        self.assertIs(result.outcome, m.Outcome.AFFIRMATIVE)

    def test_manifest_must_be_nonempty_sorted_unique(self) -> None:
        case = fixtures.family_cases()[4]
        generated, _, _ = execute(case)
        surface = m.plan_witness_surface(case.plan)
        for manifest in ((), ("decomposition_1", "decomposition_0"), ("decomposition_0", "decomposition_0")):
            with self.subTest(manifest=manifest):
                result = m.issue_confidential_plan_witness_view(
                    generated,
                    generated.plan_capability,
                    surface,
                    manifest,
                    TEST_CONSUMER,
                    TEST_PURPOSE,
                )
                self.assertIs(result.outcome, m.Outcome.MALFORMED)

    def test_consumer_and_purpose_are_nonempty_nominal_ids(self) -> None:
        case = fixtures.family_cases()[3]
        generated, _, _ = execute(case)
        surface = m.plan_witness_surface(case.plan)
        manifest = ("accumulator_witness",)

        for consumer, purpose, expected in (
            (m.DownstreamConsumerId(""), TEST_PURPOSE, m.Outcome.MALFORMED),
            (TEST_CONSUMER, m.DownstreamPurposeId(""), m.Outcome.MALFORMED),
            (TEST_PURPOSE, TEST_PURPOSE, m.Outcome.KIND_MISMATCH),
            (TEST_CONSUMER, TEST_CONSUMER, m.Outcome.KIND_MISMATCH),
        ):
            with self.subTest(consumer=consumer, purpose=purpose):
                result = m.issue_confidential_plan_witness_view(
                    generated,
                    generated.plan_capability,
                    surface,
                    manifest,
                    consumer,
                    purpose,
                )
                self.assertIs(result.outcome, expected)

    def test_equal_values_keep_distinct_latticefold_occurrences(self) -> None:
        case = fixtures.family_cases()[4]
        generated, completed, cap = execute(case)
        self.assertEqual(tuple(completed.outputs), ("decomposition_0", "decomposition_1"))
        self.assertIsNot(completed.outputs["decomposition_0"], completed.outputs["decomposition_1"])
        graph = m.derive_endpoint_graph(
            case.core,
            case.plan,
            m.EndpointPurpose.PLAN_CONTINUATION,
        )
        self.assertEqual(tuple(item.output_ref for item in graph.exports), (0, 1))


if __name__ == "__main__":
    unittest.main()
