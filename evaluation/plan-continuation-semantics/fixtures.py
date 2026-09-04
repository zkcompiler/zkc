"""Source-shaped finite fixtures for the Plan continuation evaluator."""

from __future__ import annotations

import json
from pathlib import Path
from types import MappingProxyType

import reference_model as m


ROOT = Path(__file__).resolve().parent


def _load(name: str) -> object:
    return json.loads((ROOT / "cases" / name).read_text(encoding="utf-8"))


def _core(
    name: str,
    schedule: tuple[object, ...],
    public: dict[str, object],
) -> tuple[object, object, object]:
    core = m.protocol.Core(
        inputs=(
            m.protocol.InputDecl("statement", m.protocol.InputRole.STATEMENT, value_sort=m.protocol.ValueSort.NAT),
            m.protocol.InputDecl("session", m.protocol.InputRole.PUBLIC_CONTEXT),
        ),
        scopes=(m.protocol.ScopeDecl("root", None, None),),
        schedule=schedule,
    )
    return (
        core,
        m.protocol.TranscriptConstruction(f"zkc/plan-continuation/{name}".encode()),
        m.protocol.Invocation(MappingProxyType({
            "statement": public[name]["statement"],
            "session": public[name]["session"].encode(),
        })),
    )


def msg(name: str) -> object:
    return m.protocol.Occurrence(name, m.protocol.OccurrenceKind.PROVER_MESSAGE, prover_value_sort=m.protocol.ValueSort.NAT)


def coin(name: str) -> object:
    return m.protocol.Occurrence(name, m.protocol.OccurrenceKind.CHALLENGE, challenge_domain=m.protocol.ChallengeDomain(97))


def terminal() -> object:
    return m.protocol.Occurrence("terminal", m.protocol.OccurrenceKind.TERMINAL)


def node(name: str, algorithm: m.Algorithm, *operands: m.Operand) -> m.RecipeNode:
    return m.RecipeNode(name, algorithm, operands)


def state(*items: tuple[str, m.Operand]) -> tuple[m.StateAssignment, ...]:
    return tuple(m.StateAssignment(key, value) for key, value in items)


def private_material(*keys: str) -> tuple[m.PrivateMaterialDecl, ...]:
    return tuple(
        m.PrivateMaterialDecl(
            key,
            m.PrivateMaterialKind.WITNESS_INGRESS,
            m.ValueType.NAT,
        )
        for key in keys
    )


def fresh_protocol_id(core: object) -> object:
    return m.protocol.protocol_id(
        core,
        None,
        m.protocol.ChallengeInterpretation.FRESH,
    )


def _nova(private: dict[str, object], public: dict[str, object]) -> m.FamilyCase:
    core, construction, invocation = _core("nova", (msg("cross_commit"), coin("fold_coin"), terminal()), public)
    plan = m.ProverPlan(
        fresh_protocol_id(core), private_material("w1", "w2"),
        (m.RandomnessRequirement("blind", m.ValueType.NAT, "cross_commit"),),
        state(("cross", m.Operand.constant(0)), ("blind_state", m.Operand.constant(0))),
        (m.DecisionRecipe(
            "cross_commit",
            (node("cross", m.Algorithm.ADD, m.Operand.private("w1"), m.Operand.private("w2")),
             node("commit", m.Algorithm.ADD, m.Operand.node("cross"), m.Operand.randomness("blind"))),
            m.Operand.node("commit"),
            state(("cross", m.Operand.node("cross")), ("blind_state", m.Operand.randomness("blind"))),
        ),),
        (m.DerivedWitnessExport("folded", m.RecipeSite.terminal("terminal"), m.Operand.node("folded")),),
        (m.TerminalRecipe("terminal", (
            node("scaled", m.Algorithm.MUL, m.Operand.occurrence("fold_coin"), m.Operand.state("cross")),
            node("folded", m.Algorithm.ADD, m.Operand.private("w1"), m.Operand.node("scaled")),
        )),),
    )
    return m.FamilyCase("Nova", "T2", core, construction, invocation, plan,
                        MappingProxyType(private["nova"]["private"]),
                        MappingProxyType(private["nova"]["randomness"]),
                        MappingProxyType(public["nova"]["fresh"]), ("folded",), m.SourceRequirement.FINALIZED)


def _hypernova(private: dict[str, object], public: dict[str, object]) -> m.FamilyCase:
    core, construction, invocation = _core(
        "hypernova", (coin("gamma_beta"), msg("sumcheck_poly"), coin("round_coin"), msg("sigma_theta"), coin("rho"), terminal()), public
    )
    plan = m.ProverPlan(
        fresh_protocol_id(core), private_material("witness"), (), state(("sigma", m.Operand.constant(0)),),
        (
            m.DecisionRecipe("sumcheck_poly", (node("poly", m.Algorithm.ADD, m.Operand.private("witness"), m.Operand.occurrence("gamma_beta")),), m.Operand.node("poly"), state(("sigma", m.Operand.node("poly")),)),
            m.DecisionRecipe("sigma_theta", (node("sigma", m.Algorithm.ADD, m.Operand.state("sigma"), m.Operand.occurrence("round_coin")),), m.Operand.node("sigma"), state(("sigma", m.Operand.node("sigma")),)),
        ),
        (m.DerivedWitnessExport("folded_lcccs", m.RecipeSite.terminal("terminal"), m.Operand.node("folded")),),
        (m.TerminalRecipe("terminal", (node("folded", m.Algorithm.ADD, m.Operand.state("sigma"), m.Operand.occurrence("rho")),)),),
    )
    return m.FamilyCase("HyperNova", "T1", core, construction, invocation, plan,
                        MappingProxyType(private["hypernova"]["private"]), MappingProxyType({}),
                        MappingProxyType(public["hypernova"]["fresh"]),
                        ("folded_lcccs",), m.SourceRequirement.FINALIZED)


def _cyclefold(private: dict[str, object], public: dict[str, object]) -> m.FamilyCase:
    core, construction, invocation = _core(
        "cyclefold", (msg("primary_commit"), coin("rho"), msg("primary_followup"), msg("companion_commit"), coin("rho_star"), terminal()), public
    )
    plan = m.ProverPlan(
        fresh_protocol_id(core), private_material("primary_in", "companion_in"), (), state(("companion_cross", m.Operand.constant(0)),),
        (
            m.DecisionRecipe("primary_commit", (node("p0", m.Algorithm.IDENTITY, m.Operand.private("primary_in")),), m.Operand.node("p0"), state(("companion_cross", m.Operand.state("companion_cross")),)),
            m.DecisionRecipe("primary_followup", (node("primary_out", m.Algorithm.ADD, m.Operand.private("primary_in"), m.Operand.occurrence("rho")),), m.Operand.node("primary_out"), state(("companion_cross", m.Operand.state("companion_cross")),)),
            m.DecisionRecipe("companion_commit", (node("cross", m.Algorithm.ADD, m.Operand.private("companion_in"), m.Operand.occurrence("rho")),), m.Operand.node("cross"), state(("companion_cross", m.Operand.node("cross")),)),
        ),
        (
            m.DerivedWitnessExport("primary_out", m.RecipeSite.decision("primary_followup"), m.Operand.node("primary_out")),
            m.DerivedWitnessExport("companion_out", m.RecipeSite.terminal("terminal"), m.Operand.node("companion_out")),
        ),
        (m.TerminalRecipe("terminal", (node("companion_out", m.Algorithm.ADD, m.Operand.state("companion_cross"), m.Operand.occurrence("rho_star")),)),),
    )
    return m.FamilyCase("CycleFold", "T1", core, construction, invocation, plan,
                        MappingProxyType(private["cyclefold"]["private"]), MappingProxyType({}),
                        MappingProxyType(public["cyclefold"]["fresh"]),
                        ("companion_out", "primary_out"), m.SourceRequirement.FINALIZED)


def _protostar(private: dict[str, object], public: dict[str, object]) -> m.FamilyCase:
    core, construction, invocation = _core("protostar", (msg("corrections"), coin("alpha"), msg("accumulator_publication"), terminal()), public)
    plan = m.ProverPlan(
        fresh_protocol_id(core), private_material("old_acc", "nark_witness"), (), state(("correction", m.Operand.constant(0)),),
        (
            m.DecisionRecipe("corrections", (node("corr", m.Algorithm.ADD, m.Operand.private("old_acc"), m.Operand.private("nark_witness")),), m.Operand.node("corr"), state(("correction", m.Operand.node("corr")),)),
            m.DecisionRecipe("accumulator_publication", (node("new_acc", m.Algorithm.ADD, m.Operand.state("correction"), m.Operand.occurrence("alpha")),), m.Operand.node("new_acc"), state(("correction", m.Operand.node("new_acc")),)),
        ),
        (m.DerivedWitnessExport("accumulator_witness", m.RecipeSite.decision("accumulator_publication"), m.Operand.node("new_acc")),),
        (),
    )
    return m.FamilyCase("ProtoStar", "T1", core, construction, invocation, plan,
                        MappingProxyType(private["protostar"]["private"]), MappingProxyType({}),
                        MappingProxyType(public["protostar"]["fresh"]), ("accumulator_witness",), m.SourceRequirement.GENERATED)


def _latticefold(private: dict[str, object], public: dict[str, object]) -> m.FamilyCase:
    core, construction, invocation = _core("latticefold_plus", (msg("helpers"), coin("batch_coin"), msg("decomposition"), terminal()), public)
    plan = m.ProverPlan(
        fresh_protocol_id(core), private_material("f0", "f1", "f2"), (), state(("wide", m.Operand.constant(0)),),
        (
            m.DecisionRecipe("helpers", (node("wide", m.Algorithm.ADD, m.Operand.private("f0"), m.Operand.private("f1")),), m.Operand.node("wide"), state(("wide", m.Operand.node("wide")),)),
            m.DecisionRecipe("decomposition", (
                node("combined", m.Algorithm.ADD, m.Operand.state("wide"), m.Operand.occurrence("batch_coin")),
                node("pair", m.Algorithm.PAIR, m.Operand.node("combined"), m.Operand.private("f2")),
                node("out0", m.Algorithm.FIRST, m.Operand.node("pair")),
                node("out1", m.Algorithm.SECOND, m.Operand.node("pair")),
            ), m.Operand.node("combined"), state(("wide", m.Operand.node("combined")),)),
        ),
        (
            m.DerivedWitnessExport("decomposition_0", m.RecipeSite.decision("decomposition"), m.Operand.node("out0")),
            m.DerivedWitnessExport("decomposition_1", m.RecipeSite.decision("decomposition"), m.Operand.node("out1")),
        ),
        (),
    )
    return m.FamilyCase("LatticeFold+", "T1", core, construction, invocation, plan,
                        MappingProxyType(private["latticefold_plus"]["private"]), MappingProxyType({}),
                        MappingProxyType(public["latticefold_plus"]["fresh"]), ("decomposition_0", "decomposition_1"), m.SourceRequirement.GENERATED)


def family_cases() -> tuple[m.FamilyCase, ...]:
    declared = _load("family-shapes.json")
    private = _load("private-generation.json")
    public = _load("public-inputs.json")
    assert isinstance(declared, dict) and isinstance(private, dict) and isinstance(public, dict)
    cases = (
        _nova(private, public),
        _hypernova(private, public),
        _cyclefold(private, public),
        _protostar(private, public),
        _latticefold(private, public),
    )
    assert tuple(item.name for item in cases) == tuple(item["name"] for item in declared["families"])
    assert tuple(item.evidence_depth for item in cases) == tuple(item["depth"] for item in declared["families"])
    return cases
