from __future__ import annotations

from dataclasses import replace
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

import fixtures  # noqa: E402
import reference_model as m  # noqa: E402


class PlanFormationTests(unittest.TestCase):
    def test_declared_depths_remain_metadata_while_plans_admit(self) -> None:
        cases = fixtures.family_cases()
        self.assertEqual([case.evidence_depth for case in cases], ["T2", "T1", "T1", "T1", "T1"])
        for case in cases:
            with self.subTest(case=case.name):
                checked = m.admit_plan(case.core, case.plan)
                self.assertEqual(checked.plan_id, case.plan.identity)

    def test_private_values_do_not_enter_plan_identity(self) -> None:
        case = fixtures.family_cases()[0]
        changed = dict(case.private_values)
        changed["w1"] += 100
        changed_case = replace(case, private_values=changed)
        _, baseline = m.execute_case(case)
        _, mutated = m.execute_case(changed_case)
        baseline_oir = m.derive_endpoint_graph(
            case.core,
            case.plan,
            m.EndpointPurpose.PLAN_CONTINUATION,
        )
        mutated_oir = m.derive_endpoint_graph(
            changed_case.core,
            changed_case.plan,
            m.EndpointPurpose.PLAN_CONTINUATION,
        )
        self.assertNotEqual(
            baseline.outputs["folded"].value,
            mutated.outputs["folded"].value,
        )
        self.assertEqual(case.plan.identity, changed_case.plan.identity)
        self.assertEqual(baseline_oir.identity, mutated_oir.identity)

    def test_missing_decision_recipe_is_rejected(self) -> None:
        case = fixtures.family_cases()[1]
        bad = replace(case.plan, decision_recipes=case.plan.decision_recipes[:-1])
        with self.assertRaisesRegex(m.PlanError, "cover every and only"):
            m.admit_plan(case.core, bad)

    def test_terminal_direct_randomness_is_rejected(self) -> None:
        case = fixtures.family_cases()[0]
        terminal = case.plan.terminal_recipes[0]
        bad_node = replace(terminal.nodes[-1], operands=(m.Operand.randomness("blind"), m.Operand.node("scaled")))
        bad = replace(case.plan, terminal_recipes=(replace(terminal, nodes=terminal.nodes[:-1] + (bad_node,)),))
        with self.assertRaisesRegex(m.PlanError, "cannot directly read randomness"):
            m.admit_plan(case.core, bad)

    def test_cross_site_node_capture_is_rejected(self) -> None:
        case = fixtures.family_cases()[3]
        second = case.plan.decision_recipes[1]
        bad_node = replace(second.nodes[0], operands=(m.Operand.node("corr"), m.Operand.occurrence("alpha")))
        bad = replace(case.plan, decision_recipes=(case.plan.decision_recipes[0], replace(second, nodes=(bad_node,))))
        with self.assertRaisesRegex(m.PlanError, "crosses recipe sites"):
            m.admit_plan(case.core, bad)

    def test_export_dead_node_is_rejected(self) -> None:
        case = fixtures.family_cases()[3]
        first = case.plan.decision_recipes[0]
        dead = m.RecipeNode("dead", m.Algorithm.IDENTITY, (m.Operand.constant(1),))
        bad = replace(case.plan, decision_recipes=(replace(first, nodes=first.nodes + (dead,)), case.plan.decision_recipes[1]))
        with self.assertRaisesRegex(m.PlanError, "export-dead"):
            m.admit_plan(case.core, bad)

    def test_static_recipe_mutation_rotates_plan_not_core(self) -> None:
        case = fixtures.family_cases()[0]
        terminal = case.plan.terminal_recipes[0]
        changed_node = replace(terminal.nodes[-1], algorithm=m.Algorithm.MUL)
        changed = replace(case.plan, terminal_recipes=(replace(terminal, nodes=terminal.nodes[:-1] + (changed_node,)),))
        self.assertNotEqual(case.plan.identity, changed.identity)
        self.assertEqual(m.protocol.core_id(case.core), m.protocol.core_id(case.core))


if __name__ == "__main__":
    unittest.main()
