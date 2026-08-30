from __future__ import annotations

from dataclasses import replace
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

import fixtures  # noqa: E402
import reference_model as m  # noqa: E402


def prepare(case: m.FamilyCase, plan: m.ProverPlan | None = None):
    plan = case.plan if plan is None else plan
    checked = m.admit_plan(case.core, plan)
    answer = m.prepare_plan_execution(
        case.core, case.construction, case.invocation, plan, checked,
        case.private_values, case.randomness_values,
    )
    assert answer.outcome is m.Outcome.AFFIRMATIVE
    return answer.value


class AdapterLifecycleTests(unittest.TestCase):
    def test_all_families_execute_through_plan_adapter(self) -> None:
        for case in fixtures.family_cases():
            with self.subTest(case=case.name):
                generated, completed = m.execute_case(case)
                self.assertEqual(generated.terminal, "terminal")
                self.assertEqual(tuple(completed.outputs), case.expected_arm)

    def test_ready_capability_is_one_use(self) -> None:
        case = fixtures.family_cases()[0]
        session, ready = prepare(case)
        first = m.generate_plan_run(session, ready, case.fresh_values)
        self.assertIs(first.outcome, m.Outcome.AFFIRMATIVE)
        second = m.generate_plan_run(session, ready, case.fresh_values)
        self.assertIs(second.outcome, m.Outcome.REFUSED)

    def test_randomness_is_consumed_once_at_actual_demand(self) -> None:
        case = fixtures.family_cases()[0]
        session, ready = prepare(case)
        result = m.generate_plan_run(session, ready, case.fresh_values)
        self.assertIs(result.outcome, m.Outcome.AFFIRMATIVE)
        self.assertEqual(session.random_used, {"blind"})

    def test_plan_algorithm_failure_stops_without_generation_authority(self) -> None:
        case = fixtures.family_cases()[3]
        first = case.plan.decision_recipes[0]
        failed_node = replace(first.nodes[0], algorithm=m.Algorithm.FAIL)
        bad_plan = replace(case.plan, decision_recipes=(replace(first, nodes=(failed_node,)), case.plan.decision_recipes[1]))
        session, ready = prepare(case, bad_plan)
        result = m.generate_plan_run(session, ready, case.fresh_values)
        self.assertIs(result.outcome, m.Outcome.CANNOT_ANSWER)
        self.assertTrue(session.closed)
        self.assertEqual(session.trace, {})
        self.assertEqual(session.decision_exports, {})

    def test_continuation_is_atomic_and_one_use(self) -> None:
        case = fixtures.family_cases()[0]
        session, ready = prepare(case)
        generated = m.generate_plan_run(session, ready, case.fresh_values).value
        right = generated.continuation_right
        first = m.complete_accepted_plan_continuation(generated, generated.plan_capability, right)
        self.assertIs(first.outcome, m.Outcome.AFFIRMATIVE)
        second = m.complete_accepted_plan_continuation(generated, generated.plan_capability, right)
        self.assertIs(second.outcome, m.Outcome.REFUSED)

    def test_terminal_failure_does_not_rewrite_core_accept_or_emit_prefix(self) -> None:
        case = fixtures.family_cases()[0]
        terminal = case.plan.terminal_recipes[0]
        failed = replace(terminal.nodes[-1], algorithm=m.Algorithm.FAIL)
        bad_plan = replace(case.plan, terminal_recipes=(replace(terminal, nodes=terminal.nodes[:-1] + (failed,)),))
        session, ready = prepare(case, bad_plan)
        generated = m.generate_plan_run(session, ready, case.fresh_values).value
        result = m.complete_accepted_plan_continuation(generated, generated.plan_capability, generated.continuation_right)
        self.assertIs(result.outcome, m.Outcome.CANNOT_ANSWER)
        self.assertEqual(generated.terminal, "terminal")
        self.assertIs(generated.record.entries[-1].value, True)

    def test_protocol_replay_returns_no_plan_capability(self) -> None:
        case = fixtures.family_cases()[0]
        generated, _ = m.execute_case(case)
        replayed = m.protocol.replay(case.core, case.construction, case.invocation, generated.record)
        self.assertEqual(replayed, generated.record)
        self.assertFalse(hasattr(replayed, "plan_capability"))


if __name__ == "__main__":
    unittest.main()
