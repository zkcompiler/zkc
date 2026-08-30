from __future__ import annotations

from dataclasses import replace
from pathlib import Path
import sys
from types import MappingProxyType
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

import fixtures  # noqa: E402
import reference_model as m  # noqa: E402


def execute(case: m.FamilyCase):
    checked = m.admit_plan(case.core, case.plan)
    session, ready = m.prepare_plan_execution(
        case.core, case.construction, case.invocation, case.plan, checked,
        case.private_values, case.randomness_values,
    ).value
    generated = m.generate_plan_run(session, ready, case.fresh_values).value
    completed, cap = m.complete_accepted_plan_continuation(
        generated, generated.plan_capability, generated.continuation_right
    ).value
    return generated, completed, cap


def ground(
    generated: m.CompletedPlanRun,
    source: object,
    source_cap: object,
    surface: m.PlanWitnessSurface,
    keys: tuple[str, ...],
    instance: m.RelationInstance,
    assignment: dict[str, object],
):
    binding = m.PlanWitnessBinding(
        surface.identity,
        tuple(m.WitnessBindingEdge(key, f"relation_{key}") for key in keys),
    )
    consumer, purpose = m.plan_witness_grounding_roles(instance, binding)
    view, view_cap = m.issue_confidential_plan_witness_view(
        source, source_cap, surface, keys, consumer, purpose
    ).value
    return m.check_plan_witness_grounding_for_run(
        instance, binding, assignment, view, view_cap, generated
    )


def with_statement(case: m.FamilyCase, value: object) -> m.FamilyCase:
    values = dict(case.invocation.values)
    values["statement"] = value
    return replace(
        case,
        invocation=m.protocol.Invocation(MappingProxyType(values)),
    )


def recurrence_legs() -> tuple[m.PublicRecurrenceLeg, ...]:
    source_output = m.PublicRecurrenceCoordinate(
        m.PublicCoordinateRole.SOURCE_RUN_OUTPUT, "cross_commit"
    )
    source_slot = m.PublicRecurrenceCoordinate(
        m.PublicCoordinateRole.SOURCE_INSTANCE_SLOT, "accumulator"
    )
    target_slot = m.PublicRecurrenceCoordinate(
        m.PublicCoordinateRole.TARGET_INSTANCE_SLOT, "accumulator"
    )
    target_statement = m.PublicRecurrenceCoordinate(
        m.PublicCoordinateRole.TARGET_STATEMENT_INPUT, "statement"
    )
    return (
        m.PublicRecurrenceLeg(source_output, source_slot),
        m.PublicRecurrenceLeg(source_slot, target_slot),
        m.PublicRecurrenceLeg(target_slot, target_statement),
    )


class RelationsAndHandoffTests(unittest.TestCase):
    def test_grounding_distinguishes_agreement_from_value_disagreement(self) -> None:
        case = fixtures.family_cases()[0]
        generated, completed, cap = execute(case)
        surface = m.plan_witness_surface(case.plan)
        instance = m.RelationInstance("nova-output")
        value = completed.outputs["folded"].value
        yes = ground(generated, completed, cap, surface, ("folded",), instance, {"relation_folded": value})
        no = ground(generated, completed, cap, surface, ("folded",), instance, {"relation_folded": value + 1})
        self.assertIs(yes.outcome, m.Outcome.AFFIRMATIVE)
        self.assertIs(no.outcome, m.Outcome.NEGATIVE)

    def test_same_run_join_refuses_byte_equal_distinct_generation(self) -> None:
        case = fixtures.family_cases()[0]
        generated, completed, cap = execute(case)
        generated2, _, _ = execute(case)
        surface = m.plan_witness_surface(case.plan)
        instance = m.RelationInstance("same-run")
        value = completed.outputs["folded"].value
        private = ground(generated, completed, cap, surface, ("folded",), instance, {"relation_folded": value}).value
        self.assertIs(m.join_same_run_grounding(private, m.PublicRunGrounding(instance, generated, True)).outcome, m.Outcome.AFFIRMATIVE)
        self.assertIs(m.join_same_run_grounding(private, m.PublicRunGrounding(instance, generated2, True)).outcome, m.Outcome.REFUSED)
        self.assertIs(m.join_same_run_grounding(private, m.PublicRunGrounding(instance, generated, False)).outcome, m.Outcome.UNSUPPORTED)

    def test_one_use_handoff_creates_fresh_target_ingress_and_causal_join(self) -> None:
        source_case = fixtures.family_cases()[0]
        source_generated, source_completed, source_cap = execute(source_case)
        target_case = with_statement(fixtures.family_cases()[0], 17)
        issued = m.issue_accepted_plan_witness_ingress_supply(
            source_completed, source_cap, "folded", target_case.core,
            target_case.plan, "w1"
        )
        self.assertIs(issued.outcome, m.Outcome.AFFIRMATIVE)
        supply, supply_capability = issued.value
        checked = m.admit_plan(target_case.core, target_case.plan)
        prepared = m.prepare_plan_execution(
            target_case.core, target_case.construction, target_case.invocation,
            target_case.plan, checked, {"w2": target_case.private_values["w2"]},
            target_case.randomness_values, ((supply, supply_capability),),
        )
        self.assertIs(prepared.outcome, m.Outcome.AFFIRMATIVE)
        target_session, ready = prepared.value
        handoff = target_session.handoff_capabilities[0]
        target_generated = m.generate_plan_run(target_session, ready, target_case.fresh_values).value
        source_surface = m.plan_witness_surface(source_case.plan)
        target_surface = m.plan_witness_surface(target_case.plan)
        source_instance = m.RelationInstance(
            "source-output", MappingProxyType({"accumulator": 17})
        )
        target_instance = m.RelationInstance(
            "target-input", MappingProxyType({"accumulator": 17})
        )
        source_grounding = ground(
            source_generated, source_completed, source_cap, source_surface,
            ("folded",), source_instance,
            {"relation_folded": source_completed.outputs["folded"].value},
        ).value
        target_grounding = ground(
            target_generated, target_generated, target_generated.plan_capability,
            target_surface, ("w1",), target_instance,
            {"relation_w1": source_completed.outputs["folded"].value},
        ).value
        joined = m.join_causal_plan_witness_handoff(source_grounding, target_grounding, handoff)
        self.assertIs(joined.outcome, m.Outcome.AFFIRMATIVE)
        self.assertIs(target_session.ingress_occurrences["w1"].handoff_capability, handoff)
        public = m.check_public_recurrence_grounding(
            source_generated,
            target_generated,
            source_instance,
            target_instance,
            recurrence_legs(),
        )
        self.assertEqual(public.value.anchor_values, (17, 17, 17, 17))
        self.assertEqual(public.value.leg_agreements, (True, True, True))
        recurrence = m.join_causal_plan_step_recurrence(joined.value, public.value)
        self.assertIs(recurrence.outcome, m.Outcome.AFFIRMATIVE)

    def test_equal_public_recurrence_cannot_replace_causal_handoff(self) -> None:
        source_case = fixtures.family_cases()[0]
        source_generated, _, _ = execute(source_case)
        target_generated, _, _ = execute(with_statement(source_case, 17))
        public = m.check_public_recurrence_grounding(
            source_generated,
            target_generated,
            m.RelationInstance("source", MappingProxyType({"accumulator": 17})),
            m.RelationInstance("target", MappingProxyType({"accumulator": 17})),
            recurrence_legs(),
        )
        self.assertIs(public.outcome, m.Outcome.AFFIRMATIVE)
        result = m.join_causal_plan_step_recurrence(public.value, public.value)
        self.assertIs(result.outcome, m.Outcome.KIND_MISMATCH)

    def test_equal_public_recurrence_with_unrelated_instance_cannot_join(self) -> None:
        case = fixtures.family_cases()[0]
        source_generated, source_completed, source_cap = execute(case)
        supply, supply_capability = m.issue_accepted_plan_witness_ingress_supply(
            source_completed, source_cap, "folded", case.core, case.plan, "w1"
        ).value
        checked = m.admit_plan(case.core, case.plan)
        target_case = with_statement(case, 17)
        target_session, ready = m.prepare_plan_execution(
            target_case.core, target_case.construction, target_case.invocation, target_case.plan, checked,
            {"w2": case.private_values["w2"]}, case.randomness_values,
            ((supply, supply_capability),),
        ).value
        target_generated = m.generate_plan_run(target_session, ready, case.fresh_values).value
        handoff = target_session.handoff_capabilities[0]
        surface = m.plan_witness_surface(case.plan)
        source_instance = m.RelationInstance(
            "source-role", MappingProxyType({"accumulator": 17})
        )
        target_instance = m.RelationInstance(
            "target-role", MappingProxyType({"accumulator": 17})
        )
        source_grounding = ground(
            source_generated, source_completed, source_cap, surface, ("folded",),
            source_instance, {"relation_folded": source_completed.outputs["folded"].value},
        ).value
        target_grounding = ground(
            target_generated, target_generated, target_generated.plan_capability, surface,
            ("w1",), target_instance,
            {"relation_w1": source_completed.outputs["folded"].value},
        ).value
        private = m.join_causal_plan_witness_handoff(
            source_grounding, target_grounding, handoff
        ).value
        unrelated = m.check_public_recurrence_grounding(
            source_generated,
            target_generated,
            m.RelationInstance(
                "equal-content-but-new-source",
                MappingProxyType({"accumulator": 17}),
            ),
            target_instance,
            recurrence_legs(),
        )
        self.assertIs(unrelated.outcome, m.Outcome.AFFIRMATIVE)
        self.assertIs(
            m.join_causal_plan_step_recurrence(private, unrelated.value).outcome,
            m.Outcome.REFUSED,
        )

    def test_public_recurrence_rejects_missing_extra_self_and_unrelated_legs(self) -> None:
        case = fixtures.family_cases()[0]
        source_generated, _, _ = execute(case)
        target_generated, _, _ = execute(with_statement(case, 17))
        source_instance = m.RelationInstance(
            "source", MappingProxyType({"accumulator": 17})
        )
        target_instance = m.RelationInstance(
            "target", MappingProxyType({"accumulator": 17})
        )
        legs = recurrence_legs()
        missing = m.check_public_recurrence_grounding(
            source_generated, target_generated, source_instance, target_instance,
            legs[:2],
        )
        extra = m.check_public_recurrence_grounding(
            source_generated, target_generated, source_instance, target_instance,
            legs + (legs[-1],),
        )
        self_role = m.check_public_recurrence_grounding(
            source_generated, source_generated, source_instance, target_instance,
            legs,
        )
        unrelated_middle = replace(
            legs[1],
            left=m.PublicRecurrenceCoordinate(
                m.PublicCoordinateRole.SOURCE_INSTANCE_SLOT, "other"
            ),
        )
        unrelated = m.check_public_recurrence_grounding(
            source_generated, target_generated, source_instance, target_instance,
            (legs[0], unrelated_middle, legs[2]),
        )
        self.assertEqual(
            [missing.outcome, extra.outcome, self_role.outcome, unrelated.outcome],
            [m.Outcome.MALFORMED] * 4,
        )

    def test_each_public_recurrence_leg_is_checked_from_its_owner(self) -> None:
        case = fixtures.family_cases()[0]
        source_generated, _, _ = execute(case)
        legs = recurrence_legs()
        cases = (
            (18, 18, 18, (False, True, True)),
            (17, 18, 18, (True, False, True)),
            (17, 17, 18, (True, True, False)),
        )
        for source_slot, target_slot, target_statement, expected in cases:
            with self.subTest(expected=expected):
                target_generated, _, _ = execute(with_statement(case, target_statement))
                checked = m.check_public_recurrence_grounding(
                    source_generated,
                    target_generated,
                    m.RelationInstance(
                        "source", MappingProxyType({"accumulator": source_slot})
                    ),
                    m.RelationInstance(
                        "target", MappingProxyType({"accumulator": target_slot})
                    ),
                    legs,
                )
                self.assertIs(checked.outcome, m.Outcome.NEGATIVE)
                self.assertEqual(checked.value.leg_agreements, expected)

    def test_handoff_supply_is_one_use(self) -> None:
        case = fixtures.family_cases()[0]
        generated, completed, cap = execute(case)
        supply, supply_capability = m.issue_accepted_plan_witness_ingress_supply(
            completed, cap, "folded", case.core, case.plan, "w1"
        ).value
        checked = m.admit_plan(case.core, case.plan)
        args = (case.core, case.construction, case.invocation, case.plan, checked,
                {"w2": case.private_values["w2"]}, case.randomness_values,
                ((supply, supply_capability),))
        self.assertIs(m.prepare_plan_execution(*args).outcome, m.Outcome.AFFIRMATIVE)
        self.assertIs(m.prepare_plan_execution(*args).outcome, m.Outcome.REFUSED)

    def test_reconstructed_continuation_capability_has_no_authority(self) -> None:
        case = fixtures.family_cases()[0]
        generated, completed, authentic = execute(case)
        forged = m.CausalPlanContinuationCapability(
            completed,
            generated.plan_capability,
        )
        refused = m.issue_accepted_plan_witness_ingress_supply(
            completed, forged, "folded", case.core, case.plan, "w1"
        )
        accepted = m.issue_accepted_plan_witness_ingress_supply(
            completed, authentic, "folded", case.core, case.plan, "w1"
        )
        self.assertIs(refused.outcome, m.Outcome.REFUSED)
        self.assertIs(accepted.outcome, m.Outcome.AFFIRMATIVE)

    def test_handoff_requires_witness_ingress_of_identical_type(self) -> None:
        case = fixtures.family_cases()[0]
        _, completed, cap = execute(case)
        w1 = case.plan.private_material[0]
        for changed, expected in (
            (
                replace(w1, kind=m.PrivateMaterialKind.ADVICE),
                m.Outcome.KIND_MISMATCH,
            ),
            (
                replace(w1, value_type=m.ValueType.BYTES),
                m.Outcome.KIND_MISMATCH,
            ),
        ):
            with self.subTest(changed=changed):
                target_plan = replace(
                    case.plan,
                    private_material=(changed,) + case.plan.private_material[1:],
                )
                self.assertEqual(
                    m.admit_plan(case.core, target_plan).plan_id,
                    target_plan.identity,
                )
                result = m.issue_accepted_plan_witness_ingress_supply(
                    completed, cap, "folded", case.core, target_plan, "w1"
                )
                self.assertIs(result.outcome, expected)

    def test_handoff_supply_is_bound_to_exact_target_core_and_plan(self) -> None:
        case = fixtures.family_cases()[0]
        _, completed, cap = execute(case)
        supply, supply_capability = m.issue_accepted_plan_witness_ingress_supply(
            completed, cap, "folded", case.core, case.plan, "w1"
        ).value
        other_schedule = tuple(
            replace(
                item,
                challenge_domain=m.protocol.ChallengeDomain(101),
            )
            if item.name == "fold_coin"
            else item
            for item in case.core.schedule
        )
        other_core = replace(case.core, schedule=other_schedule)
        other_plan = replace(
            case.plan,
            protocol_id=m.protocol.protocol_id(
                other_core,
                None,
                m.protocol.ChallengeInterpretation.FRESH,
            ),
        )
        other_checked = m.admit_plan(other_core, other_plan)
        refused = m.prepare_plan_execution(
            other_core,
            case.construction,
            case.invocation,
            other_plan,
            other_checked,
            {"w2": case.private_values["w2"]},
            case.randomness_values,
            ((supply, supply_capability),),
        )
        self.assertIs(refused.outcome, m.Outcome.REFUSED)
        self.assertTrue(supply_capability.active)
        self.assertFalse(supply_capability.used)
        accepted = m.prepare_plan_execution(
            case.core,
            case.construction,
            case.invocation,
            case.plan,
            m.admit_plan(case.core, case.plan),
            {"w2": case.private_values["w2"]},
            case.randomness_values,
            ((supply, supply_capability),),
        )
        self.assertIs(accepted.outcome, m.Outcome.AFFIRMATIVE)

    def test_grounding_roles_are_question_derived_and_nominal(self) -> None:
        case = fixtures.family_cases()[0]
        generated, completed, cap = execute(case)
        surface = m.plan_witness_surface(case.plan)
        instance = m.RelationInstance("question-bound")
        binding = m.PlanWitnessBinding(
            surface.identity,
            (m.WitnessBindingEdge("folded", "relation_folded"),),
        )
        consumer, purpose = m.plan_witness_grounding_roles(instance, binding)
        value = completed.outputs["folded"].value
        for wrong_consumer, wrong_purpose in (
            (m.DownstreamConsumerId("wrong"), purpose),
            (consumer, m.DownstreamPurposeId("wrong")),
        ):
            with self.subTest(
                consumer=wrong_consumer,
                purpose=wrong_purpose,
            ):
                view, view_cap = m.issue_confidential_plan_witness_view(
                    completed,
                    cap,
                    surface,
                    ("folded",),
                    wrong_consumer,
                    wrong_purpose,
                ).value
                checked = m.check_plan_witness_grounding_for_run(
                    instance,
                    binding,
                    {"relation_folded": value},
                    view,
                    view_cap,
                    generated,
                )
                self.assertIs(checked.outcome, m.Outcome.REFUSED)
        swapped = m.issue_confidential_plan_witness_view(
            completed,
            cap,
            surface,
            ("folded",),
            purpose,
            consumer,
        )
        self.assertIs(swapped.outcome, m.Outcome.KIND_MISMATCH)

    def test_challenge_and_raw_terminal_are_not_public_recurrence_outputs(self) -> None:
        case = fixtures.family_cases()[0]
        source_generated, _, _ = execute(case)
        target_generated, _, _ = execute(with_statement(case, 17))
        source_instance = m.RelationInstance(
            "source", MappingProxyType({"accumulator": 17})
        )
        target_instance = m.RelationInstance(
            "target", MappingProxyType({"accumulator": 17})
        )
        ordinary = recurrence_legs()
        for source_key in ("fold_coin", "terminal"):
            with self.subTest(source_key=source_key):
                unsupported = (
                    replace(
                        ordinary[0],
                        left=m.PublicRecurrenceCoordinate(
                            m.PublicCoordinateRole.SOURCE_RUN_OUTPUT,
                            source_key,
                        ),
                    ),
                    ordinary[1],
                    ordinary[2],
                )
                result = m.check_public_recurrence_grounding(
                    source_generated,
                    target_generated,
                    source_instance,
                    target_instance,
                    unsupported,
                )
                self.assertIs(result.outcome, m.Outcome.UNSUPPORTED)

    def test_invalid_batch_does_not_consume_valid_supply(self) -> None:
        case = fixtures.family_cases()[0]
        _, completed, cap = execute(case)
        supply, supply_capability = m.issue_accepted_plan_witness_ingress_supply(
            completed, cap, "folded", case.core, case.plan, "w1"
        ).value
        bad_supply = replace(supply, target_key="not-a-target")
        bad_capability = m.ReadyPlanWitnessIngressSupplyCapability(bad_supply)
        checked = m.admit_plan(case.core, case.plan)
        result = m.prepare_plan_execution(
            case.core, case.construction, case.invocation, case.plan, checked,
            {"w2": case.private_values["w2"]}, case.randomness_values,
            ((supply, supply_capability), (bad_supply, bad_capability)),
        )
        self.assertIs(result.outcome, m.Outcome.MALFORMED)
        self.assertTrue(supply_capability.active)
        self.assertFalse(supply_capability.used)


if __name__ == "__main__":
    unittest.main()
