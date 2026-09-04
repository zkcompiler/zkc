from __future__ import annotations

from dataclasses import replace
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

import fixtures  # noqa: E402
import independent_oir  # noqa: E402
import reference_model as m  # noqa: E402


class EndpointProjectionTests(unittest.TestCase):
    def test_primary_and_independent_derivations_agree(self) -> None:
        for case in fixtures.family_cases():
            for purpose in m.EndpointPurpose:
                with self.subTest(case=case.name, purpose=purpose.value):
                    primary = m.derive_endpoint_graph(case.core, case.plan, purpose)
                    independent = independent_oir.derive(case.core, case.plan, purpose)
                    self.assertEqual(primary, independent)
                    self.assertIs(m.locally_admit_oir(primary).outcome, m.Outcome.AFFIRMATIVE)

    def test_ordinary_endpoint_excludes_private_continuation(self) -> None:
        case = fixtures.family_cases()[0]
        ordinary = m.derive_endpoint_graph(
            case.core, case.plan, m.EndpointPurpose.PLAN_PROVER
        )
        continuation = m.derive_endpoint_graph(
            case.core, case.plan, m.EndpointPurpose.PLAN_CONTINUATION
        )
        self.assertEqual(ordinary.exports, ())
        self.assertEqual(ordinary.arms, ())
        self.assertTrue(continuation.exports)
        self.assertTrue(continuation.arms)
        self.assertEqual(ordinary.completion, "NoSourceSemanticCompletion")
        self.assertEqual(continuation.completion, "NoSourceSemanticCompletion")

    def test_cyclefold_arm_preserves_decision_and_terminal_sites(self) -> None:
        case = fixtures.family_cases()[2]
        graph = m.derive_endpoint_graph(
            case.core, case.plan, m.EndpointPurpose.PLAN_CONTINUATION
        )
        by_key = {item.key: item for item in graph.exports}
        self.assertIs(by_key["primary_out"].site.kind, m.SiteKind.DECISION)
        self.assertIs(by_key["companion_out"].site.kind, m.SiteKind.ACCEPTED_TERMINAL)
        self.assertEqual(graph.arms[0].output_refs, (0, 1))

    def test_proto_star_decision_only_arm_needs_no_terminal_recipe(self) -> None:
        case = fixtures.family_cases()[3]
        graph = m.derive_endpoint_graph(
            case.core, case.plan, m.EndpointPurpose.PLAN_CONTINUATION
        )
        self.assertEqual(case.plan.terminal_recipes, ())
        self.assertEqual(tuple(item.key for item in graph.exports), ("accumulator_witness",))
        self.assertTrue(all(item.site.kind is m.SiteKind.DECISION for item in graph.exports))

    def test_local_admission_rejects_sparse_or_dangling_refs(self) -> None:
        case = fixtures.family_cases()[4]
        graph = m.derive_endpoint_graph(
            case.core, case.plan, m.EndpointPurpose.PLAN_CONTINUATION
        )
        sparse = replace(graph, exports=(replace(graph.exports[0], output_ref=2),) + graph.exports[1:])
        dangling = replace(graph, arms=(replace(graph.arms[0], output_refs=(0, 3)),))
        self.assertIs(m.locally_admit_oir(sparse).outcome, m.Outcome.MALFORMED)
        self.assertIs(m.locally_admit_oir(dangling).outcome, m.Outcome.MALFORMED)

    def test_ordinary_purpose_cannot_carry_private_outputs(self) -> None:
        case = fixtures.family_cases()[0]
        continuation = m.derive_endpoint_graph(
            case.core, case.plan, m.EndpointPurpose.PLAN_CONTINUATION
        )
        wrong = replace(continuation, purpose=m.EndpointPurpose.PLAN_PROVER)
        self.assertIs(m.locally_admit_oir(wrong).outcome, m.Outcome.MALFORMED)

    def test_static_plan_change_rotates_continuation_graph(self) -> None:
        case = fixtures.family_cases()[0]
        baseline = m.derive_endpoint_graph(
            case.core, case.plan, m.EndpointPurpose.PLAN_CONTINUATION
        )
        export = replace(case.plan.exports[0], key="renamed_folded")
        changed = replace(case.plan, exports=(export,))
        rotated = m.derive_endpoint_graph(
            case.core, changed, m.EndpointPurpose.PLAN_CONTINUATION
        )
        self.assertNotEqual(baseline.identity, rotated.identity)

    def test_retained_recipe_operand_rotates_plan_and_endpoint_identity(self) -> None:
        case = fixtures.family_cases()[0]
        baseline = m.derive_endpoint_graph(
            case.core, case.plan, m.EndpointPurpose.PLAN_CONTINUATION
        )
        terminal = case.plan.terminal_recipes[0]
        folded = terminal.nodes[-1]
        changed_folded = replace(
            folded,
            operands=(m.Operand.private("w2"), folded.operands[1]),
        )
        changed = replace(
            case.plan,
            terminal_recipes=(
                replace(
                    terminal,
                    nodes=terminal.nodes[:-1] + (changed_folded,),
                ),
            ),
        )
        self.assertEqual(m.admit_plan(case.core, changed).plan_id, changed.identity)
        projected = m.derive_endpoint_graph(
            case.core, changed, m.EndpointPurpose.PLAN_CONTINUATION
        )
        independently_projected = independent_oir.derive(
            case.core, changed, m.EndpointPurpose.PLAN_CONTINUATION
        )
        self.assertNotEqual(case.plan.identity, changed.identity)
        self.assertNotEqual(baseline.identity, projected.identity)
        self.assertEqual(projected, independently_projected)
        self.assertIs(
            m.locally_admit_oir(projected).outcome,
            m.Outcome.AFFIRMATIVE,
        )

    def test_authored_empty_continuation_graph_is_malformed(self) -> None:
        case = fixtures.family_cases()[0]
        ordinary = m.derive_endpoint_graph(
            case.core, case.plan, m.EndpointPurpose.PLAN_PROVER
        )
        authored_empty = replace(
            ordinary,
            purpose=m.EndpointPurpose.PLAN_CONTINUATION,
        )
        self.assertIs(
            m.locally_admit_oir(authored_empty).outcome,
            m.Outcome.MALFORMED,
        )

    def test_unguaranteed_decision_yields_no_continuation_arm(self) -> None:
        case = fixtures.family_cases()[3]
        schedule = tuple(
            replace(
                item,
                guard=m.protocol.Predicate(m.protocol.PredicateKind.NEVER),
            )
            if item.name == "accumulator_publication"
            else item
            for item in case.core.schedule
        )
        core = replace(case.core, schedule=schedule)
        plan = replace(
            case.plan,
            protocol_id=m.protocol.protocol_id(
                core,
                None,
                m.protocol.ChallengeInterpretation.FRESH,
            ),
        )
        self.assertEqual(m.continuation_arm(core, plan, "terminal"), ())
        support = m.endpoint_projection_support(
            core, plan, m.EndpointPurpose.PLAN_CONTINUATION
        )
        self.assertIs(support.outcome, m.Outcome.UNSUPPORTED)
        with self.assertRaisesRegex(m.PlanError, "NoPlanContinuationArm"):
            m.derive_endpoint_graph(
                core, plan, m.EndpointPurpose.PLAN_CONTINUATION
            )
        checked = m.admit_plan(core, plan)
        prepared = m.prepare_plan_execution(
            core,
            case.construction,
            case.invocation,
            plan,
            checked,
            case.private_values,
            case.randomness_values,
        )
        self.assertIs(prepared.outcome, m.Outcome.AFFIRMATIVE)
        session, ready = prepared.value
        generated = m.generate_plan_run(
            session, ready, case.fresh_values
        ).value
        self.assertEqual(generated.terminal, "terminal")
        self.assertIsNone(generated.continuation_right)

    def test_equal_conditional_guards_satisfy_closed_guard_implication(self) -> None:
        guard = m.protocol.Predicate(
            m.protocol.PredicateKind.BOOL,
            (m.protocol.ValueRef.input("enabled"),),
        )
        other = m.protocol.Predicate(
            m.protocol.PredicateKind.BOOL,
            (m.protocol.ValueRef.input("other"),),
        )
        self.assertTrue(m.guard_implies(guard, guard))
        self.assertTrue(
            m.guard_implies(
                guard,
                m.protocol.Predicate(m.protocol.PredicateKind.ALWAYS),
            )
        )
        self.assertFalse(m.guard_implies(guard, other))


if __name__ == "__main__":
    unittest.main()
