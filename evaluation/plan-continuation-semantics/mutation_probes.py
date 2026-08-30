"""Executable one-mutation/one-outcome probes for the finite evaluator."""

from __future__ import annotations

from dataclasses import replace
from types import MappingProxyType
from typing import Callable

import fixtures
import reference_model as m


def _execute(case: m.FamilyCase):
    checked = m.admit_plan(case.core, case.plan)
    session, ready = m.prepare_plan_execution(
        case.core,
        case.construction,
        case.invocation,
        case.plan,
        checked,
        case.private_values,
        case.randomness_values,
    ).value
    generated = m.generate_plan_run(
        session, ready, case.fresh_values
    ).value
    completed, continuation_capability = m.complete_accepted_plan_continuation(
        generated,
        generated.plan_capability,
        generated.continuation_right,
    ).value
    return generated, completed, continuation_capability


def _malformed_plan(plan: m.ProverPlan, core: object) -> m.Outcome:
    try:
        m.admit_plan(core, plan)
    except (m.PlanError, m.protocol.ModelError):
        return m.Outcome.MALFORMED
    return m.Outcome.CHECKER_FAILURE


def cross_site_node_capture() -> m.Outcome:
    case = fixtures.family_cases()[3]
    second = case.plan.decision_recipes[1]
    bad_node = replace(
        second.nodes[0],
        operands=(m.Operand.node("corr"), m.Operand.occurrence("alpha")),
    )
    bad = replace(
        case.plan,
        decision_recipes=(
            case.plan.decision_recipes[0],
            replace(second, nodes=(bad_node,)),
        ),
    )
    return _malformed_plan(bad, case.core)


def missing_decision_recipe() -> m.Outcome:
    case = fixtures.family_cases()[1]
    return _malformed_plan(
        replace(case.plan, decision_recipes=case.plan.decision_recipes[:-1]),
        case.core,
    )


def terminal_randomness_read() -> m.Outcome:
    case = fixtures.family_cases()[0]
    terminal = case.plan.terminal_recipes[0]
    bad_node = replace(
        terminal.nodes[-1],
        operands=(m.Operand.randomness("blind"), m.Operand.node("scaled")),
    )
    bad = replace(
        case.plan,
        terminal_recipes=(
            replace(
                terminal,
                nodes=terminal.nodes[:-1] + (bad_node,),
            ),
        ),
    )
    return _malformed_plan(bad, case.core)


def ready_capability_reuse() -> m.Outcome:
    case = fixtures.family_cases()[0]
    checked = m.admit_plan(case.core, case.plan)
    session, ready = m.prepare_plan_execution(
        case.core,
        case.construction,
        case.invocation,
        case.plan,
        checked,
        case.private_values,
        case.randomness_values,
    ).value
    first = m.generate_plan_run(session, ready, case.fresh_values)
    if first.outcome is not m.Outcome.AFFIRMATIVE:
        return m.Outcome.CHECKER_FAILURE
    return m.generate_plan_run(session, ready, case.fresh_values).outcome


def adapter_failure() -> m.Outcome:
    case = fixtures.family_cases()[3]
    first = case.plan.decision_recipes[0]
    failed_node = replace(first.nodes[0], algorithm=m.Algorithm.FAIL)
    bad_plan = replace(
        case.plan,
        decision_recipes=(
            replace(first, nodes=(failed_node,)),
            case.plan.decision_recipes[1],
        ),
    )
    checked = m.admit_plan(case.core, bad_plan)
    session, ready = m.prepare_plan_execution(
        case.core,
        case.construction,
        case.invocation,
        bad_plan,
        checked,
        case.private_values,
        case.randomness_values,
    ).value
    return m.generate_plan_run(session, ready, case.fresh_values).outcome


def generated_terminal_disclosure() -> m.Outcome:
    case = fixtures.family_cases()[0]
    generated, _, _ = _execute(case)
    return m.issue_confidential_plan_witness_view(
        generated,
        generated.plan_capability,
        m.plan_witness_surface(case.plan),
        ("folded",),
        m.DownstreamConsumerId("mutation.consumer"),
        m.DownstreamPurposeId("mutation.purpose"),
    ).outcome


def malformed_confidential_manifest() -> m.Outcome:
    case = fixtures.family_cases()[4]
    generated, _, _ = _execute(case)
    return m.issue_confidential_plan_witness_view(
        generated,
        generated.plan_capability,
        m.plan_witness_surface(case.plan),
        ("decomposition_1", "decomposition_0"),
        m.DownstreamConsumerId("mutation.consumer"),
        m.DownstreamPurposeId("mutation.purpose"),
    ).outcome


def reconstructed_continuation_capability() -> m.Outcome:
    case = fixtures.family_cases()[0]
    generated, completed, _ = _execute(case)
    forged = m.CausalPlanContinuationCapability(
        completed,
        generated.plan_capability,
    )
    return m.issue_accepted_plan_witness_ingress_supply(
        completed,
        forged,
        "folded",
        case.core,
        case.plan,
        "w1",
    ).outcome


def wrong_handoff_material_kind() -> m.Outcome:
    case = fixtures.family_cases()[0]
    _, completed, capability = _execute(case)
    changed = replace(
        case.plan.private_material[0],
        kind=m.PrivateMaterialKind.ADVICE,
    )
    target = replace(
        case.plan,
        private_material=(changed,) + case.plan.private_material[1:],
    )
    return m.issue_accepted_plan_witness_ingress_supply(
        completed,
        capability,
        "folded",
        case.core,
        target,
        "w1",
    ).outcome


def wrong_handoff_value_type() -> m.Outcome:
    case = fixtures.family_cases()[0]
    _, completed, capability = _execute(case)
    changed = replace(
        case.plan.private_material[0],
        value_type=m.ValueType.BYTES,
    )
    target = replace(
        case.plan,
        private_material=(changed,) + case.plan.private_material[1:],
    )
    return m.issue_accepted_plan_witness_ingress_supply(
        completed,
        capability,
        "folded",
        case.core,
        target,
        "w1",
    ).outcome


def exact_target_core_binding() -> m.Outcome:
    case = fixtures.family_cases()[0]
    _, completed, capability = _execute(case)
    supply, supply_capability = m.issue_accepted_plan_witness_ingress_supply(
        completed,
        capability,
        "folded",
        case.core,
        case.plan,
        "w1",
    ).value
    other_schedule = tuple(
        replace(item, challenge_domain=m.protocol.ChallengeDomain(101))
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
    return m.prepare_plan_execution(
        other_core,
        case.construction,
        case.invocation,
        other_plan,
        m.admit_plan(other_core, other_plan),
        {"w2": case.private_values["w2"]},
        case.randomness_values,
        ((supply, supply_capability),),
    ).outcome


def wrong_grounding_consumer() -> m.Outcome:
    case = fixtures.family_cases()[0]
    generated, completed, capability = _execute(case)
    surface = m.plan_witness_surface(case.plan)
    instance = m.RelationInstance("mutation-grounding")
    binding = m.PlanWitnessBinding(
        surface.identity,
        (m.WitnessBindingEdge("folded", "relation_folded"),),
    )
    _, purpose = m.plan_witness_grounding_roles(instance, binding)
    view, view_capability = m.issue_confidential_plan_witness_view(
        completed,
        capability,
        surface,
        ("folded",),
        m.DownstreamConsumerId("wrong"),
        purpose,
    ).value
    return m.check_plan_witness_grounding_for_run(
        instance,
        binding,
        {"relation_folded": completed.outputs["folded"].value},
        view,
        view_capability,
        generated,
    ).outcome


def _recurrence_inputs():
    case = fixtures.family_cases()[0]
    source, _, _ = _execute(case)
    invocation_values = dict(case.invocation.values)
    invocation_values["statement"] = 17
    target_case = replace(
        case,
        invocation=m.protocol.Invocation(MappingProxyType(invocation_values)),
    )
    target, _, _ = _execute(target_case)
    source_instance = m.RelationInstance(
        "source",
        MappingProxyType({"accumulator": 17}),
    )
    target_instance = m.RelationInstance(
        "target",
        MappingProxyType({"accumulator": 17}),
    )
    source_output = m.PublicRecurrenceCoordinate(
        m.PublicCoordinateRole.SOURCE_RUN_OUTPUT,
        "cross_commit",
    )
    source_slot = m.PublicRecurrenceCoordinate(
        m.PublicCoordinateRole.SOURCE_INSTANCE_SLOT,
        "accumulator",
    )
    target_slot = m.PublicRecurrenceCoordinate(
        m.PublicCoordinateRole.TARGET_INSTANCE_SLOT,
        "accumulator",
    )
    statement = m.PublicRecurrenceCoordinate(
        m.PublicCoordinateRole.TARGET_STATEMENT_INPUT,
        "statement",
    )
    legs = (
        m.PublicRecurrenceLeg(source_output, source_slot),
        m.PublicRecurrenceLeg(source_slot, target_slot),
        m.PublicRecurrenceLeg(target_slot, statement),
    )
    return source, target, source_instance, target_instance, legs


def incomplete_public_recurrence() -> m.Outcome:
    source, target, source_instance, target_instance, legs = _recurrence_inputs()
    return m.check_public_recurrence_grounding(
        source,
        target,
        source_instance,
        target_instance,
        legs[:2],
    ).outcome


def challenge_as_public_recurrence_output() -> m.Outcome:
    source, target, source_instance, target_instance, legs = _recurrence_inputs()
    bad_first = replace(
        legs[0],
        left=m.PublicRecurrenceCoordinate(
            m.PublicCoordinateRole.SOURCE_RUN_OUTPUT,
            "fold_coin",
        ),
    )
    return m.check_public_recurrence_grounding(
        source,
        target,
        source_instance,
        target_instance,
        (bad_first, legs[1], legs[2]),
    ).outcome


def unequal_public_recurrence_leg() -> m.Outcome:
    source, target, _, target_instance, legs = _recurrence_inputs()
    unequal_source = m.RelationInstance(
        "source",
        MappingProxyType({"accumulator": 18}),
    )
    return m.check_public_recurrence_grounding(
        source,
        target,
        unequal_source,
        target_instance,
        legs,
    ).outcome


def empty_continuation_graph() -> m.Outcome:
    case = fixtures.family_cases()[0]
    ordinary = m.derive_endpoint_graph(
        case.core,
        case.plan,
        m.EndpointPurpose.PLAN_PROVER,
    )
    return m.locally_admit_oir(
        replace(ordinary, purpose=m.EndpointPurpose.PLAN_CONTINUATION)
    ).outcome


def ordinary_graph_with_continuation() -> m.Outcome:
    case = fixtures.family_cases()[0]
    continuation = m.derive_endpoint_graph(
        case.core,
        case.plan,
        m.EndpointPurpose.PLAN_CONTINUATION,
    )
    return m.locally_admit_oir(
        replace(continuation, purpose=m.EndpointPurpose.PLAN_PROVER)
    ).outcome


def no_plan_continuation_arm() -> m.Outcome:
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
    return m.endpoint_projection_support(
        core,
        plan,
        m.EndpointPurpose.PLAN_CONTINUATION,
    ).outcome


PROBES: dict[str, Callable[[], m.Outcome]] = {
    "cross_site_node_capture": cross_site_node_capture,
    "missing_decision_recipe": missing_decision_recipe,
    "terminal_randomness_read": terminal_randomness_read,
    "ready_capability_reuse": ready_capability_reuse,
    "adapter_failure": adapter_failure,
    "generated_terminal_disclosure": generated_terminal_disclosure,
    "malformed_confidential_manifest": malformed_confidential_manifest,
    "reconstructed_continuation_capability": reconstructed_continuation_capability,
    "wrong_handoff_material_kind": wrong_handoff_material_kind,
    "wrong_handoff_value_type": wrong_handoff_value_type,
    "exact_target_core_binding": exact_target_core_binding,
    "wrong_grounding_consumer": wrong_grounding_consumer,
    "incomplete_public_recurrence": incomplete_public_recurrence,
    "challenge_as_public_recurrence_output": challenge_as_public_recurrence_output,
    "unequal_public_recurrence_leg": unequal_public_recurrence_leg,
    "empty_continuation_graph": empty_continuation_graph,
    "ordinary_graph_with_continuation": ordinary_graph_with_continuation,
    "no_plan_continuation_arm": no_plan_continuation_arm,
}
