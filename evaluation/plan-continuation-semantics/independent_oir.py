"""Independent literal derivation of the static continuation contract."""

from __future__ import annotations

import reference_model as m


def _guaranteed_decisions(core: object, terminal: str) -> tuple[str, ...]:
    """Independently apply the finite profile's closed GuardImplies rule."""

    declarations = tuple(core.schedule)
    terminal_matches = tuple(
        (index, item)
        for index, item in enumerate(declarations)
        if item.name == terminal
    )
    if len(terminal_matches) != 1:
        raise m.PlanError("accepted terminal is absent or ambiguous")
    terminal_index, terminal_decl = terminal_matches[0]
    if terminal_decl.kind is not m.protocol.OccurrenceKind.TERMINAL:
        raise m.PlanError("accepted terminal coordinate has the wrong kind")
    return tuple(
        item.name
        for item in declarations[:terminal_index]
        if item.kind
        in {
            m.protocol.OccurrenceKind.PROVER_MESSAGE,
            m.protocol.OccurrenceKind.ORACLE_PUBLISH,
        }
        and (
            item.guard.kind is m.protocol.PredicateKind.ALWAYS
            or item.guard == terminal_decl.guard
        )
    )


def _nodes(plan_graph: m.ProjectedPlanGraph) -> tuple[m.ProjectedNode, ...]:
    return tuple(
        m.ProjectedNode(
            m.RecipeSite.decision(recipe.occurrence),
            item.name,
            item.algorithm,
            item.operands,
        )
        for recipe in plan_graph.decision_recipes
        for item in recipe.nodes
    ) + tuple(
        m.ProjectedNode(
            m.RecipeSite.terminal(recipe.terminal),
            item.name,
            item.algorithm,
            item.operands,
        )
        for recipe in plan_graph.terminal_recipes
        for item in recipe.nodes
    )


def derive(
    core: object,
    plan: m.ProverPlan,
    purpose: m.EndpointPurpose,
) -> m.EndpointGraph:
    """Derive the endpoint graph without calling the primary projector."""

    if type(purpose) is not m.EndpointPurpose:
        raise m.PlanError("KindMismatch: endpoint purpose has the wrong kind")
    m.admit_plan(core, plan)
    if purpose is m.EndpointPurpose.PLAN_PROVER:
        plan_graph = m.ProjectedPlanGraph(
            plan.protocol_id,
            plan.private_material,
            plan.randomness,
            plan.state_initializers,
            plan.decision_recipes,
            (),
            (),
        )
        return m.EndpointGraph(
            purpose,
            plan.protocol_id,
            m.protocol.core_id(core),
            plan_graph,
            _nodes(plan_graph),
            (),
            (),
        )

    derived_arms: list[tuple[str, tuple[m.DerivedWitnessExport, ...]]] = []
    for terminal in plan.accepted_terminals:
        guaranteed = set(_guaranteed_decisions(core, terminal))
        arm = tuple(sorted(
            (
                item
                for item in plan.exports
                if item.site == m.RecipeSite.terminal(terminal)
                or (
                    item.site.kind is m.SiteKind.DECISION
                    and item.site.ref in guaranteed
                )
            ),
            key=lambda item: item.key,
        ))
        if arm:
            derived_arms.append((terminal, arm))
    if not derived_arms:
        raise m.PlanError("Unsupported: NoPlanContinuationArm")

    by_key = {
        item.key: item
        for _, arm in derived_arms
        for item in arm
    }
    selected = tuple(by_key[key] for key in sorted(by_key))
    retained_terminal_names = {
        item.site.ref
        for item in selected
        if item.site.kind is m.SiteKind.ACCEPTED_TERMINAL
    }
    retained_terminal_recipes = tuple(
        recipe
        for recipe in plan.terminal_recipes
        if recipe.terminal in retained_terminal_names
    )
    plan_graph = m.ProjectedPlanGraph(
        plan.protocol_id,
        plan.private_material,
        plan.randomness,
        plan.state_initializers,
        plan.decision_recipes,
        selected,
        retained_terminal_recipes,
    )
    exports = tuple(
        m.ProjectedExport(index, item.key, item.site, item.value_type)
        for index, item in enumerate(selected)
    )
    output_ref = {item.key: item.output_ref for item in exports}
    arms = tuple(
        m.ContinuationArmDecl(
            terminal,
            tuple(sorted(output_ref[item.key] for item in arm)),
        )
        for terminal, arm in derived_arms
    )
    return m.EndpointGraph(
        purpose,
        plan.protocol_id,
        m.protocol.core_id(core),
        plan_graph,
        _nodes(plan_graph),
        exports,
        arms,
    )
