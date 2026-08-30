"""Finite executable model of causal Plan continuation semantics.

The existing Protocol reference executor remains the only Core executor.  This
module adds a narrow Plan-owned strategy adapter, accepted-terminal private
continuations, confidential witness views, causal Relations checks, and a
one-use output-to-ingress handoff.  It is an evaluation instrument, not a
cryptographic implementation or normative semantic authority.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
from types import MappingProxyType
from typing import Mapping


_PROTOCOL_EXECUTOR_PATH = (
    Path(__file__).resolve().parents[1]
    / "k2-protocol-fiat-shamir"
    / "reference_model.py"
)
_PROTOCOL_EXECUTOR_NAME = "_zkc_protocol_executor_for_plan_continuation"
if _PROTOCOL_EXECUTOR_NAME in sys.modules:
    protocol = sys.modules[_PROTOCOL_EXECUTOR_NAME]
else:
    _spec = importlib.util.spec_from_file_location(_PROTOCOL_EXECUTOR_NAME, _PROTOCOL_EXECUTOR_PATH)
    if _spec is None or _spec.loader is None:  # pragma: no cover - host failure
        raise ImportError(f"cannot load Protocol executor from {_PROTOCOL_EXECUTOR_PATH}")
    protocol = importlib.util.module_from_spec(_spec)
    sys.modules[_PROTOCOL_EXECUTOR_NAME] = protocol
    _spec.loader.exec_module(protocol)


class Outcome(str, Enum):
    AFFIRMATIVE = "Affirmative"
    NEGATIVE = "Negative"
    UNSUPPORTED = "Unsupported"
    MISSING_DEPENDENCY = "MissingDependency"
    CANNOT_ANSWER = "CannotAnswer"
    KIND_MISMATCH = "KindMismatch"
    MALFORMED = "Malformed"
    REFUSED = "Refused"
    LIMIT = "DeterministicLimitExceeded"
    CHECKER_FAILURE = "CheckerFailure"


@dataclass(frozen=True)
class Answer:
    outcome: Outcome
    value: object | None = None
    reason: str = ""


def affirmative(value: object) -> Answer:
    return Answer(Outcome.AFFIRMATIVE, value)


def _canonical(value: object) -> object:
    if isinstance(value, Enum):
        return value.value
    if hasattr(value, "__dataclass_fields__"):
        return {
            name: _canonical(getattr(value, name))
            for name in value.__dataclass_fields__
            if not name.startswith("_")
        }
    if isinstance(value, Mapping):
        return {str(key): _canonical(value[key]) for key in sorted(value, key=str)}
    if isinstance(value, tuple):
        return [_canonical(item) for item in value]
    if isinstance(value, bytes):
        return {"bytes": value.hex()}
    return value


def semantic_id(domain: str, value: object) -> str:
    payload = json.dumps(
        {"domain": domain, "body": _canonical(value)},
        sort_keys=True,
        separators=(",", ":"),
    ).encode()
    return hashlib.sha256(payload).hexdigest()


class SiteKind(str, Enum):
    DECISION = "DecisionSite"
    ACCEPTED_TERMINAL = "AcceptedTerminalSite"


@dataclass(frozen=True, order=True)
class RecipeSite:
    kind: SiteKind
    ref: str

    @staticmethod
    def decision(ref: str) -> "RecipeSite":
        return RecipeSite(SiteKind.DECISION, ref)

    @staticmethod
    def terminal(ref: str) -> "RecipeSite":
        return RecipeSite(SiteKind.ACCEPTED_TERMINAL, ref)


class OperandKind(str, Enum):
    PUBLIC_INPUT = "PublicInput"
    OCCURRENCE = "ObservedOccurrence"
    PRIVATE = "PrivateMaterial"
    RANDOMNESS = "PrivateRandomness"
    STATE = "StateBefore"
    CONSTANT = "Constant"
    NODE = "NodeOutput"
    TERMINAL_OUTPUT = "AcceptedTerminalPublicOutput"


@dataclass(frozen=True)
class Operand:
    kind: OperandKind
    ref: str = ""
    value: object | None = None

    @staticmethod
    def input(ref: str) -> "Operand": return Operand(OperandKind.PUBLIC_INPUT, ref)
    @staticmethod
    def occurrence(ref: str) -> "Operand": return Operand(OperandKind.OCCURRENCE, ref)
    @staticmethod
    def private(ref: str) -> "Operand": return Operand(OperandKind.PRIVATE, ref)
    @staticmethod
    def randomness(ref: str) -> "Operand": return Operand(OperandKind.RANDOMNESS, ref)
    @staticmethod
    def state(ref: str) -> "Operand": return Operand(OperandKind.STATE, ref)
    @staticmethod
    def constant(value: object) -> "Operand": return Operand(OperandKind.CONSTANT, value=value)
    @staticmethod
    def node(ref: str) -> "Operand": return Operand(OperandKind.NODE, ref)
    @staticmethod
    def terminal_output(ref: str) -> "Operand": return Operand(OperandKind.TERMINAL_OUTPUT, ref)


class Algorithm(str, Enum):
    IDENTITY = "Identity"
    ADD = "Add"
    MUL = "Multiply"
    PAIR = "Pair"
    FIRST = "First"
    SECOND = "Second"
    FAIL = "AlwaysFail"


class ValueType(str, Enum):
    """Small exact type universe used by this finite evaluator."""

    NAT = "Nat"
    BYTES = "Bytes"


def _value_has_type(value: object, value_type: ValueType) -> bool:
    if value_type is ValueType.NAT:
        return type(value) is int and value >= 0
    if value_type is ValueType.BYTES:
        return type(value) is bytes
    return False


class PrivateMaterialKind(str, Enum):
    WITNESS_INGRESS = "WitnessIngress"
    ADVICE = "Advice"
    CONFIDENTIAL_CONTEXT = "ConfidentialContext"


@dataclass(frozen=True)
class PrivateMaterialDecl:
    key: str
    kind: PrivateMaterialKind
    value_type: ValueType


@dataclass(frozen=True)
class RecipeNode:
    name: str
    algorithm: Algorithm
    operands: tuple[Operand, ...]


@dataclass(frozen=True)
class StateAssignment:
    slot: str
    value: Operand


@dataclass(frozen=True)
class DecisionRecipe:
    occurrence: str
    nodes: tuple[RecipeNode, ...]
    move: Operand
    state_after: tuple[StateAssignment, ...]


@dataclass(frozen=True)
class TerminalRecipe:
    terminal: str
    nodes: tuple[RecipeNode, ...]


@dataclass(frozen=True)
class RandomnessRequirement:
    key: str
    value_type: ValueType
    first_available_at: str


@dataclass(frozen=True)
class DerivedWitnessExport:
    key: str
    site: RecipeSite
    value: Operand
    value_type: ValueType = ValueType.NAT


@dataclass(frozen=True)
class ProverPlan:
    protocol_id: object
    private_material: tuple[PrivateMaterialDecl, ...]
    randomness: tuple[RandomnessRequirement, ...]
    state_initializers: tuple[StateAssignment, ...]
    decision_recipes: tuple[DecisionRecipe, ...]
    exports: tuple[DerivedWitnessExport, ...]
    terminal_recipes: tuple[TerminalRecipe, ...]
    accepted_terminals: tuple[str, ...] = ("terminal",)

    @property
    def identity(self) -> str:
        return semantic_id("pir.prover-plan", self)


@dataclass(frozen=True)
class CheckedPlanRealizes:
    plan_id: str
    core_id: object


class PlanError(ValueError):
    pass


def _decision_names(core: object) -> tuple[str, ...]:
    return tuple(
        item.name
        for item in core.schedule
        if item.kind in {protocol.OccurrenceKind.PROVER_MESSAGE, protocol.OccurrenceKind.ORACLE_PUBLISH}
    )


def _terminal_names(core: object) -> tuple[str, ...]:
    return tuple(item.name for item in core.schedule if item.kind is protocol.OccurrenceKind.TERMINAL)


def _fresh_protocol_id(core: object) -> object:
    return protocol.protocol_id(
        core,
        None,
        protocol.ChallengeInterpretation.FRESH,
    )


def _private_material_by_key(plan: ProverPlan) -> dict[str, PrivateMaterialDecl]:
    return {item.key: item for item in plan.private_material}


def guard_implies(
    use_guard: object,
    source_guard: object,
) -> bool:
    """The exact closed syntactic implication law imported from Protocol."""

    return (
        type(use_guard) is protocol.Predicate
        and type(source_guard) is protocol.Predicate
        and (
            source_guard.kind is protocol.PredicateKind.ALWAYS
            or use_guard == source_guard
        )
    )


def _validate_operand(
    operand: Operand,
    *,
    site: RecipeSite,
    prior_nodes: set[str],
    plan: ProverPlan,
    core: object,
) -> None:
    if type(operand) is not Operand:
        raise PlanError("operand has the wrong exact shape")
    if operand.kind is OperandKind.NODE and operand.ref not in prior_nodes:
        raise PlanError("node operand is future, absent, or crosses recipe sites")
    if operand.kind is OperandKind.PRIVATE and operand.ref not in _private_material_by_key(plan):
        raise PlanError("private operand is undeclared")
    if operand.kind is OperandKind.RANDOMNESS:
        if site.kind is SiteKind.ACCEPTED_TERMINAL:
            raise PlanError("accepted-terminal recipes cannot directly read randomness")
        if operand.ref not in {item.key for item in plan.randomness}:
            raise PlanError("randomness operand is undeclared")
    if operand.kind is OperandKind.STATE and operand.ref not in {
        item.slot for item in plan.state_initializers
    }:
        raise PlanError("state operand is undeclared")
    if operand.kind is OperandKind.PUBLIC_INPUT and operand.ref not in {
        item.name for item in core.inputs
    }:
        raise PlanError("public input operand is unknown")
    if operand.kind is OperandKind.OCCURRENCE:
        order = {item.name: index for index, item in enumerate(core.schedule)}
        if operand.ref not in order or site.ref not in order or order[operand.ref] >= order[site.ref]:
            raise PlanError("observed occurrence is not in the exact prior prefix")
    if operand.kind is OperandKind.TERMINAL_OUTPUT and site.kind is not SiteKind.ACCEPTED_TERMINAL:
        raise PlanError("terminal output is legal only at its accepted terminal")


def admit_plan(core: object, plan: ProverPlan) -> CheckedPlanRealizes:
    protocol.admit_core(core)
    if type(plan) is not ProverPlan:
        raise PlanError("Plan has the wrong exact carrier")
    if plan.protocol_id != _fresh_protocol_id(core):
        raise PlanError("Plan names a different exact Protocol")
    decisions = _decision_names(core)
    if tuple(item.occurrence for item in plan.decision_recipes) != decisions:
        raise PlanError("decision recipes must cover every and only prover decisions in order")
    terminals = _terminal_names(core)
    if any(item not in terminals for item in plan.accepted_terminals):
        raise PlanError("accepted terminal is absent from the Core")
    terminal_map = {item.terminal: item for item in plan.terminal_recipes}
    if len(terminal_map) != len(plan.terminal_recipes):
        raise PlanError("terminal recipes must have unique sites")
    if any(item not in plan.accepted_terminals for item in terminal_map):
        raise PlanError("terminal recipe is not attached to an accepted terminal")
    if any(
        type(item) is not PrivateMaterialDecl
        or type(item.kind) is not PrivateMaterialKind
        or type(item.value_type) is not ValueType
        or not item.key
        for item in plan.private_material
    ):
        raise PlanError("private material declarations have the wrong exact shape")
    if len({item.key for item in plan.private_material}) != len(plan.private_material):
        raise PlanError("private material keys must be unique")
    if any(
        type(item) is not RandomnessRequirement
        or type(item.value_type) is not ValueType
        or not item.key
        for item in plan.randomness
    ):
        raise PlanError("randomness declarations have the wrong exact shape")
    if len({item.key for item in plan.randomness}) != len(plan.randomness):
        raise PlanError("randomness keys must be unique")
    state_slots = tuple(item.slot for item in plan.state_initializers)
    if len(set(state_slots)) != len(state_slots):
        raise PlanError("state slots must be unique")
    order = {name: index for index, name in enumerate(decisions)}
    for requirement in plan.randomness:
        if requirement.first_available_at not in order:
            raise PlanError("randomness availability must name a decision")
    recipes: list[tuple[RecipeSite, tuple[RecipeNode, ...], tuple[Operand, ...]]] = []
    for recipe in plan.decision_recipes:
        site = RecipeSite.decision(recipe.occurrence)
        export_roots = tuple(item.value for item in plan.exports if item.site == site)
        recipes.append((site, recipe.nodes,
                        (recipe.move,) + tuple(item.value for item in recipe.state_after) + export_roots))
        if tuple(item.slot for item in recipe.state_after) != state_slots:
            raise PlanError("every decision state map must be total and ordered")
    for recipe in plan.terminal_recipes:
        roots = tuple(item.value for item in plan.exports if item.site == RecipeSite.terminal(recipe.terminal))
        if not roots:
            raise PlanError("every terminal recipe needs at least one export")
        recipes.append((RecipeSite.terminal(recipe.terminal), recipe.nodes, roots))
    for site, nodes, roots in recipes:
        prior: set[str] = set()
        for node in nodes:
            if node.name in prior:
                raise PlanError("recipe node names must be unique within a site")
            for operand in node.operands:
                _validate_operand(operand, site=site, prior_nodes=prior, plan=plan, core=core)
            prior.add(node.name)
        for root in roots:
            _validate_operand(root, site=site, prior_nodes=prior, plan=plan, core=core)
        used = {operand.ref for node in nodes for operand in node.operands if operand.kind is OperandKind.NODE}
        used.update(root.ref for root in roots if root.kind is OperandKind.NODE)
        if set(prior) - used:
            raise PlanError("recipe contains an export-dead node")
    export_keys = tuple(item.key for item in plan.exports)
    if len(set(export_keys)) != len(export_keys):
        raise PlanError("derived witness export keys must be unique")
    valid_sites = {RecipeSite.decision(name) for name in decisions} | {
        RecipeSite.terminal(name) for name in terminal_map
    }
    if any(item.site not in valid_sites for item in plan.exports):
        raise PlanError("derived witness export has no exact recipe site")
    return CheckedPlanRealizes(plan.identity, protocol.core_id(core))


def guaranteed_decisions_for_terminal(core: object, terminal: str) -> tuple[str, ...]:
    """Derive a conservative all-path guarantee from the exact finite Core.

    The reused executor has one total schedule with per-occurrence guards.  A
    prover decision is therefore guaranteed on every path to a later terminal
    exactly when it precedes that terminal and the closed Protocol `GuardImplies`
    rule holds: the source guard is `Always`, or it is exactly the terminal
    guard.  Caller-authored path claims are deliberately absent.
    """

    protocol.admit_core(core)
    order = {item.name: index for index, item in enumerate(core.schedule)}
    if terminal not in order:
        raise PlanError("accepted terminal is absent from the Core")
    terminal_decl = core.schedule[order[terminal]]
    if terminal_decl.kind is not protocol.OccurrenceKind.TERMINAL:
        raise PlanError("accepted terminal coordinate has the wrong kind")
    return tuple(
        item.name
        for item in core.schedule[: order[terminal]]
        if item.kind
        in {
            protocol.OccurrenceKind.PROVER_MESSAGE,
            protocol.OccurrenceKind.ORACLE_PUBLISH,
        }
        and guard_implies(terminal_decl.guard, item.guard)
    )


def continuation_arm(
    core: object,
    plan: ProverPlan,
    terminal: str,
) -> tuple[DerivedWitnessExport, ...]:
    guaranteed = set(guaranteed_decisions_for_terminal(core, terminal))
    selected = tuple(
        item for item in plan.exports
        if item.site == RecipeSite.terminal(terminal)
        or (item.site.kind is SiteKind.DECISION and item.site.ref in guaranteed)
    )
    return tuple(sorted(selected, key=lambda item: item.key))


class LiveCapability:
    __slots__ = ("owner", "active", "used")

    def __init__(self, owner: object) -> None:
        self.owner = owner
        self.active = True
        self.used = False

    def __copy__(self) -> object: raise TypeError("live capabilities cannot be copied")
    def __deepcopy__(self, memo: object) -> object: raise TypeError("live capabilities cannot be copied")


@dataclass
class WitnessIngressOccurrence:
    protocol_id: object
    plan_id: str
    key: str
    value_type: ValueType
    value: object
    handoff_capability: "CausalPlanWitnessHandoffCapability | None" = None


@dataclass
class PreparedPlanExecution:
    core: object
    construction: object
    invocation: object
    plan: ProverPlan
    checked: CheckedPlanRealizes
    private_values: Mapping[str, object]
    randomness_values: Mapping[str, object]
    state: dict[str, object]
    ingress_occurrences: Mapping[str, WitnessIngressOccurrence]
    handoff_capabilities: tuple["CausalPlanWitnessHandoffCapability", ...]
    random_used: set[str] = field(default_factory=set)
    trace: dict[str, dict[str, object]] = field(default_factory=dict)
    decision_exports: dict[str, "PlanWitnessOccurrence"] = field(default_factory=dict)
    running: bool = False
    closed: bool = False


@dataclass(frozen=True)
class PlanWitnessOccurrence:
    key: str
    value_type: ValueType
    value: object
    site: RecipeSite
    source_run: object


@dataclass(frozen=True)
class CausalCoreGenerationCapability:
    run: object


@dataclass(frozen=True)
class CausalPlanGenerationCapability:
    session: PreparedPlanExecution
    run: object
    core_capability: CausalCoreGenerationCapability
    handoff_capabilities: tuple["CausalPlanWitnessHandoffCapability", ...]


@dataclass
class AcceptedPlanContinuationRight(LiveCapability):
    terminal: str = ""

    def __init__(self, owner: object, terminal: str) -> None:
        LiveCapability.__init__(self, owner)
        self.terminal = terminal


@dataclass(frozen=True)
class CompletedPlanRun:
    record: object
    session: PreparedPlanExecution
    core_capability: CausalCoreGenerationCapability
    plan_capability: CausalPlanGenerationCapability
    terminal: str | None
    continuation_right: AcceptedPlanContinuationRight | None


@dataclass(frozen=True)
class CompletedPlanContinuation:
    generated: CompletedPlanRun
    terminal: str
    outputs: Mapping[str, PlanWitnessOccurrence]
    _issued_capability: object | None = field(
        default=None,
        init=False,
        compare=False,
        repr=False,
    )


@dataclass(frozen=True)
class CausalPlanContinuationCapability:
    continuation: CompletedPlanContinuation
    generation_capability: CausalPlanGenerationCapability


class ReadyPlanWitnessIngressSupplyCapability(LiveCapability):
    """One-use right consumed only by atomic target preparation."""


@dataclass(frozen=True)
class ReadyPlanWitnessIngressSupply:
    source_occurrence: PlanWitnessOccurrence
    source_continuation_capability: CausalPlanContinuationCapability
    target_protocol_id: object
    target_core_id: object
    target_plan_id: str
    target_key: str
    value_type: ValueType
    value: object


@dataclass
class CausalPlanWitnessHandoffCapability:
    supply: ReadyPlanWitnessIngressSupply
    consumed_supply_capability: ReadyPlanWitnessIngressSupplyCapability
    source_occurrence: PlanWitnessOccurrence
    target_protocol_id: object
    target_core_id: object
    target_plan_id: str
    target_key: str
    value_type: ValueType
    target_occurrence: WitnessIngressOccurrence


def issue_accepted_plan_witness_ingress_supply(
    continuation: CompletedPlanContinuation,
    capability: CausalPlanContinuationCapability,
    output_key: str,
    target_core: object,
    target_plan: ProverPlan,
    target_key: str,
) -> Answer:
    if (
        capability is not continuation._issued_capability
        or capability.continuation is not continuation
        or capability.generation_capability is not continuation.generated.plan_capability
    ):
        return Answer(Outcome.REFUSED, reason="continuation capability is not identical")
    try:
        target_protocol_id = _fresh_protocol_id(target_core)
    except protocol.ModelError as error:
        return Answer(Outcome.MALFORMED, reason=str(error))
    if target_plan.protocol_id != target_protocol_id:
        return Answer(Outcome.REFUSED, reason="target Plan names a different Protocol")
    try:
        admit_plan(target_core, target_plan)
    except (PlanError, protocol.ModelError) as error:
        return Answer(Outcome.MALFORMED, reason=str(error))
    target_decl = _private_material_by_key(target_plan).get(target_key)
    if target_decl is None:
        return Answer(Outcome.MALFORMED, reason="target WitnessIngress key is absent")
    if target_decl.kind is not PrivateMaterialKind.WITNESS_INGRESS:
        return Answer(Outcome.KIND_MISMATCH, reason="handoff target is not WitnessIngress")
    occurrence = continuation.outputs.get(output_key)
    if occurrence is None:
        return Answer(Outcome.CANNOT_ANSWER, reason="source output is absent")
    if occurrence.value_type is not target_decl.value_type:
        return Answer(Outcome.KIND_MISMATCH, reason="source and target ValueTypes differ")
    provisional = object()
    right = ReadyPlanWitnessIngressSupplyCapability(provisional)
    supply = ReadyPlanWitnessIngressSupply(
        occurrence,
        capability,
        target_protocol_id,
        protocol.core_id(target_core),
        target_plan.identity,
        target_key,
        occurrence.value_type,
        occurrence.value,
    )
    right.owner = supply
    return affirmative((supply, right))


def _eval_algorithm(algorithm: Algorithm, values: tuple[object, ...]) -> object:
    if algorithm is Algorithm.IDENTITY and len(values) == 1:
        return values[0]
    if (
        algorithm is Algorithm.ADD
        and len(values) == 2
        and all(type(x) is int for x in values)
    ):
        return values[0] + values[1]
    if (
        algorithm is Algorithm.MUL
        and len(values) == 2
        and all(type(x) is int for x in values)
    ):
        return values[0] * values[1]
    if algorithm is Algorithm.PAIR and len(values) == 2:
        return values
    if (
        algorithm is Algorithm.FIRST
        and len(values) == 1
        and type(values[0]) is tuple
    ):
        return values[0][0]
    if (
        algorithm is Algorithm.SECOND
        and len(values) == 1
        and type(values[0]) is tuple
    ):
        return values[0][1]
    if algorithm is Algorithm.FAIL:
        raise PlanError("closed fixture algorithm refused")
    raise PlanError("algorithm ABI or operand type mismatch")


class PlanStrategyAdapter:
    def __init__(self, session: PreparedPlanExecution) -> None:
        self.session = session

    def _operand(
        self,
        operand: Operand,
        view: object | None,
        nodes: Mapping[str, object],
        before: Mapping[str, object],
        random_pending: dict[str, object],
        record_values: Mapping[str, object] | None = None,
    ) -> object:
        if operand.kind is OperandKind.PUBLIC_INPUT:
            if view is not None:
                return view.public_input(operand.ref)
            return self.session.invocation.values[operand.ref]
        if operand.kind is OperandKind.OCCURRENCE:
            if view is not None:
                return view.read_occurrence(operand.ref)
            assert record_values is not None
            return record_values[operand.ref]
        if operand.kind is OperandKind.PRIVATE:
            return self.session.private_values[operand.ref]
        if operand.kind is OperandKind.STATE:
            return before[operand.ref]
        if operand.kind is OperandKind.CONSTANT:
            return operand.value
        if operand.kind is OperandKind.NODE:
            return nodes[operand.ref]
        if operand.kind is OperandKind.TERMINAL_OUTPUT:
            assert record_values is not None
            return record_values[operand.ref]
        if operand.kind is OperandKind.RANDOMNESS:
            if operand.ref in self.session.random_used:
                raise PlanError("randomness bearer is exhausted")
            if operand.ref not in random_pending:
                random_pending[operand.ref] = self.session.randomness_values[operand.ref]
            return random_pending[operand.ref]
        raise PlanError("unknown operand")

    def _evaluate_nodes(
        self,
        nodes_decl: tuple[RecipeNode, ...],
        view: object | None,
        before: Mapping[str, object],
        random_pending: dict[str, object],
        record_values: Mapping[str, object] | None = None,
    ) -> dict[str, object]:
        values: dict[str, object] = {}
        for node in nodes_decl:
            inputs = tuple(
                self._operand(item, view, values, before, random_pending, record_values)
                for item in node.operands
            )
            values[node.name] = _eval_algorithm(node.algorithm, inputs)
        return values

    def move(self, occurrence: object, view: object) -> object:
        if not self.session.running or self.session.closed:
            raise protocol.StrategyStopped("Plan adapter is not running")
        recipe = next(
            (item for item in self.session.plan.decision_recipes if item.occurrence == occurrence.name),
            None,
        )
        if recipe is None:
            raise protocol.StrategyStopped("no admitted Plan recipe for decision")
        before = dict(self.session.state)
        random_pending: dict[str, object] = {}
        try:
            nodes = self._evaluate_nodes(recipe.nodes, view, before, random_pending)
            move = self._operand(recipe.move, view, nodes, before, random_pending)
            after = {
                item.slot: self._operand(item.value, view, nodes, before, random_pending)
                for item in recipe.state_after
            }
            local_exports = {
                item.key: self._operand(item.value, view, nodes, before, random_pending)
                for item in self.session.plan.exports
                if item.site == RecipeSite.decision(occurrence.name)
            }
            export_types = {
                item.key: item.value_type
                for item in self.session.plan.exports
                if item.site == RecipeSite.decision(occurrence.name)
            }
            if any(
                not _value_has_type(value, export_types[key])
                for key, value in local_exports.items()
            ):
                raise PlanError("decision export value has the wrong exact type")
            requirement_order = {
                item.key: _decision_names(self.session.core).index(item.first_available_at)
                for item in self.session.plan.randomness
            }
            current = _decision_names(self.session.core).index(occurrence.name)
            if any(current < requirement_order[key] for key in random_pending):
                raise PlanError("randomness was demanded before its availability boundary")
        except (KeyError, PlanError, TypeError) as error:
            self.session.closed = True
            raise protocol.StrategyStopped(str(error)) from error
        self.session.state = after
        self.session.random_used.update(random_pending)
        self.session.trace[occurrence.name] = dict(nodes)
        for item in self.session.plan.exports:
            if item.key in local_exports:
                self.session.decision_exports[item.key] = PlanWitnessOccurrence(
                    item.key,
                    item.value_type,
                    local_exports[item.key],
                    item.site,
                    self.session,
                )
        return move


def prepare_plan_execution(
    core: object,
    construction: object,
    invocation: object,
    plan: ProverPlan,
    checked: CheckedPlanRealizes,
    private_values: Mapping[str, object],
    randomness_values: Mapping[str, object],
    supplies: tuple[tuple[ReadyPlanWitnessIngressSupply, ReadyPlanWitnessIngressSupplyCapability], ...] = (),
) -> Answer:
    try:
        expected = admit_plan(core, plan)
    except (PlanError, protocol.ModelError) as error:
        return Answer(Outcome.MALFORMED, reason=str(error))
    if checked != expected:
        return Answer(Outcome.REFUSED, reason="CheckedPlanRealizes is not exact")
    private_decls = _private_material_by_key(plan)
    exact_protocol_id = _fresh_protocol_id(core)
    exact_core_id = protocol.core_id(core)
    supplied_by_key: dict[str, tuple[ReadyPlanWitnessIngressSupply, ReadyPlanWitnessIngressSupplyCapability]] = {}
    for supply, supply_capability in supplies:
        if (
            type(supply) is not ReadyPlanWitnessIngressSupply
            or type(supply_capability) is not ReadyPlanWitnessIngressSupplyCapability
        ):
            return Answer(Outcome.KIND_MISMATCH, reason="handoff supply has the wrong exact carrier")
        target_decl = private_decls.get(supply.target_key)
        if target_decl is None:
            return Answer(Outcome.MALFORMED, reason="handoff target coordinate is absent")
        if target_decl.kind is not PrivateMaterialKind.WITNESS_INGRESS:
            return Answer(Outcome.KIND_MISMATCH, reason="handoff target is not WitnessIngress")
        if type(supply.source_continuation_capability) is not CausalPlanContinuationCapability:
            return Answer(Outcome.KIND_MISMATCH, reason="source capability has the wrong exact carrier")
        source_continuation = supply.source_continuation_capability.continuation
        if (
            supply_capability.owner is not supply
            or supply_capability.used
            or not supply_capability.active
            or supply.source_continuation_capability
               is not source_continuation._issued_capability
            or supply.target_protocol_id != exact_protocol_id
            or supply.target_core_id != exact_core_id
            or supply.target_plan_id != plan.identity
            or supply.source_continuation_capability.continuation.outputs.get(supply.source_occurrence.key)
               is not supply.source_occurrence
        ):
            return Answer(Outcome.REFUSED, reason="handoff supply is stale or not exact")
        if (
            supply.value_type is not target_decl.value_type
            or supply.source_occurrence.value_type is not target_decl.value_type
        ):
            return Answer(Outcome.KIND_MISMATCH, reason="handoff ValueType differs")
        if supply.value != supply.source_occurrence.value:
            return Answer(Outcome.REFUSED, reason="handoff value is not the exact source value")
        if supply.target_key in supplied_by_key:
            return Answer(Outcome.MALFORMED, reason="duplicate handoff target")
        supplied_by_key[supply.target_key] = (supply, supply_capability)
    if set(private_values) | set(supplied_by_key) != set(private_decls):
        return Answer(Outcome.MISSING_DEPENDENCY, reason="private material is not exact")
    if set(private_values) & set(supplied_by_key):
        return Answer(Outcome.MALFORMED, reason="direct and causal ingress overlap")
    if any(
        not _value_has_type(value, private_decls[key].value_type)
        for key, value in private_values.items()
    ):
        return Answer(Outcome.KIND_MISMATCH, reason="private material has the wrong exact type")
    if set(randomness_values) != {item.key for item in plan.randomness}:
        return Answer(Outcome.MISSING_DEPENDENCY, reason="randomness supply is not exact")
    randomness_types = {item.key: item.value_type for item in plan.randomness}
    if any(
        not _value_has_type(value, randomness_types[key])
        for key, value in randomness_values.items()
    ):
        return Answer(Outcome.KIND_MISMATCH, reason="randomness has the wrong exact type")
    # Validate the whole batch before consuming any one-use supply.
    merged = dict(private_values)
    occurrences: dict[str, WitnessIngressOccurrence] = {
        key: WitnessIngressOccurrence(
            exact_protocol_id,
            plan.identity,
            key,
            private_decls[key].value_type,
            value,
        )
        for key, value in private_values.items()
    }
    handoffs: list[CausalPlanWitnessHandoffCapability] = []
    pending_handoffs: list[tuple[ReadyPlanWitnessIngressSupply, ReadyPlanWitnessIngressSupplyCapability, WitnessIngressOccurrence]] = []
    for key, (supply, supply_capability) in supplied_by_key.items():
        merged[key] = supply.value
        occurrence = WitnessIngressOccurrence(
            exact_protocol_id,
            plan.identity,
            key,
            private_decls[key].value_type,
            supply.value,
        )
        occurrences[key] = occurrence
        pending_handoffs.append((supply, supply_capability, occurrence))
    try:
        state = {
            item.slot: (
                item.value.value
                if item.value.kind is OperandKind.CONSTANT
                else merged[item.value.ref]
                if item.value.kind is OperandKind.PRIVATE
                else (_ for _ in ()).throw(PlanError("unsupported state initializer"))
            )
            for item in plan.state_initializers
        }
    except (KeyError, PlanError) as error:
        return Answer(Outcome.MALFORMED, reason=str(error))
    # Successful preparation is the single atomic consumption point.  No
    # refusal above spends one supply or leaves a partially prepared target.
    for supply, supply_capability, occurrence in pending_handoffs:
        supply_capability.used = True
        supply_capability.active = False
        handoff = CausalPlanWitnessHandoffCapability(
            supply,
            supply_capability,
            supply.source_occurrence,
            exact_protocol_id,
            exact_core_id,
            plan.identity,
            supply.target_key,
            supply.value_type,
            occurrence,
        )
        occurrence.handoff_capability = handoff
        handoffs.append(handoff)
    session = PreparedPlanExecution(
        core, construction, invocation, plan, checked,
        MappingProxyType(merged), MappingProxyType(dict(randomness_values)), state,
        MappingProxyType(occurrences), tuple(handoffs),
    )
    return affirmative((session, LiveCapability(session)))


def generate_plan_run(
    session: PreparedPlanExecution,
    ready: LiveCapability,
    fresh_values: Mapping[str, int],
) -> Answer:
    if ready.owner is not session or ready.used or not ready.active or session.closed:
        return Answer(Outcome.REFUSED, reason="ready capability is stale or wrong")
    ready.used = True
    ready.active = False
    session.running = True
    result = protocol.generate(
        session.core,
        session.construction,
        protocol.ChallengeInterpretation.FRESH,
        session.invocation,
        PlanStrategyAdapter(session),
        fresh_resolver=protocol.ScriptedFreshResolver(fresh_values),
    )
    session.running = False
    session.closed = True
    if type(result) is not protocol.Completed:
        return Answer(Outcome.CANNOT_ANSWER, value=result, reason="Plan strategy did not complete")
    record = result.record
    terminal_entries = [
        item for item in record.entries
        if item.kind is protocol.OccurrenceKind.TERMINAL and item.status is protocol.EntryStatus.EXECUTED
    ]
    terminal = next((item.occurrence for item in terminal_entries if item.value is True), None)
    core_cap = CausalCoreGenerationCapability(record)
    plan_cap = CausalPlanGenerationCapability(
        session, record, core_cap, session.handoff_capabilities
    )
    arm = () if terminal is None else continuation_arm(session.core, session.plan, terminal)
    right = AcceptedPlanContinuationRight(record, terminal) if terminal is not None and arm else None
    return affirmative(CompletedPlanRun(record, session, core_cap, plan_cap, terminal, right))


def complete_accepted_plan_continuation(
    generated: CompletedPlanRun,
    capability: CausalPlanGenerationCapability,
    right: AcceptedPlanContinuationRight,
) -> Answer:
    if (
        capability is not generated.plan_capability
        or right is not generated.continuation_right
        or right.owner is not generated.record
        or right.used
        or not right.active
        or generated.terminal is None
    ):
        return Answer(Outcome.REFUSED, reason="continuation authority is stale or wrong")
    right.used = True
    right.active = False
    terminal = generated.terminal
    recipe = next((item for item in generated.session.plan.terminal_recipes if item.terminal == terminal), None)
    record_values = {
        item.occurrence: item.value for item in generated.record.entries if item.value is not None
    }
    nodes: dict[str, object] = {}
    adapter = PlanStrategyAdapter(generated.session)
    try:
        if recipe is not None:
            nodes = adapter._evaluate_nodes(
                recipe.nodes, None, generated.session.state, {}, record_values
            )
        outputs: dict[str, PlanWitnessOccurrence] = {}
        for export in continuation_arm(
            generated.session.core,
            generated.session.plan,
            terminal,
        ):
            if export.site.kind is SiteKind.DECISION:
                prior = generated.session.decision_exports.get(export.key)
                if prior is None:
                    raise PlanError("guaranteed decision export was not produced")
                value = prior.value
            else:
                value = adapter._operand(
                    export.value, None, nodes, generated.session.state, {}, record_values
                )
            if not _value_has_type(value, export.value_type):
                raise PlanError("continuation export value has the wrong exact type")
            outputs[export.key] = PlanWitnessOccurrence(
                export.key,
                export.value_type,
                value,
                export.site,
                generated.record,
            )
    except (KeyError, PlanError, TypeError) as error:
        return Answer(Outcome.CANNOT_ANSWER, reason=str(error))
    completed = CompletedPlanContinuation(generated, terminal, MappingProxyType(outputs))
    continuation_capability = CausalPlanContinuationCapability(completed, capability)
    object.__setattr__(completed, "_issued_capability", continuation_capability)
    return affirmative((completed, continuation_capability))


class WitnessRole(str, Enum):
    INGRESS = "WitnessIngress"
    EXPORT = "DerivedWitnessExport"


class OccurrenceClass(str, Enum):
    SUPPLIED = "SuppliedForGeneration"
    DECISION = "ProducedWhenSourceDecisionActive"
    TERMINAL = "ProducedWhenAcceptedTerminalReached"


@dataclass(frozen=True)
class SurfaceEntry:
    key: str
    role: WitnessRole
    occurrence_class: OccurrenceClass
    value_type: ValueType


@dataclass(frozen=True)
class PlanWitnessSurface:
    protocol_id: object
    entries: tuple[SurfaceEntry, ...]

    @property
    def identity(self) -> str:
        return semantic_id(
            "pir.plan-witness-surface",
            (self.protocol_id, self.entries),
        )


def plan_witness_surface(plan: ProverPlan) -> PlanWitnessSurface:
    entries = [
        SurfaceEntry(
            item.key,
            WitnessRole.INGRESS,
            OccurrenceClass.SUPPLIED,
            item.value_type,
        )
        for item in plan.private_material
        if item.kind is PrivateMaterialKind.WITNESS_INGRESS
    ]
    entries.extend(
        SurfaceEntry(
            item.key,
            WitnessRole.EXPORT,
            OccurrenceClass.DECISION if item.site.kind is SiteKind.DECISION else OccurrenceClass.TERMINAL,
            item.value_type,
        )
        for item in plan.exports
    )
    return PlanWitnessSurface(
        plan.protocol_id,
        tuple(sorted(entries, key=lambda item: item.key)),
    )


class SourceRequirement(str, Enum):
    GENERATED = "GeneratedSufficient"
    FINALIZED = "FinalizedRequired"


@dataclass(frozen=True)
class ConfidentialEntry:
    surface: SurfaceEntry
    value: object
    occurrence: object


@dataclass(frozen=True)
class DownstreamConsumerId:
    value: str


@dataclass(frozen=True)
class DownstreamPurposeId:
    value: str


@dataclass(frozen=True)
class ConfidentialPlanWitnessView:
    surface_id: str
    source_tag: str
    consumer: DownstreamConsumerId
    purpose: DownstreamPurposeId
    entries: tuple[ConfidentialEntry, ...]


@dataclass(frozen=True)
class ConfidentialViewCapability:
    view: ConfidentialPlanWitnessView
    source_capability: object


def issue_confidential_plan_witness_view(
    source: CompletedPlanRun | CompletedPlanContinuation,
    source_capability: CausalPlanGenerationCapability | CausalPlanContinuationCapability,
    surface: PlanWitnessSurface,
    manifest: tuple[str, ...],
    consumer: DownstreamConsumerId,
    purpose: DownstreamPurposeId,
) -> Answer:
    if (
        type(consumer) is not DownstreamConsumerId
        or type(purpose) is not DownstreamPurposeId
    ):
        return Answer(Outcome.KIND_MISMATCH, reason="consumer or purpose has the wrong nominal kind")
    if not consumer.value or not purpose.value:
        return Answer(Outcome.MALFORMED, reason="consumer and purpose must be exact nonempty identifiers")
    if not manifest or tuple(sorted(set(manifest))) != manifest:
        return Answer(Outcome.MALFORMED, reason="manifest must be nonempty sorted unique")
    by_key = {item.key: item for item in surface.entries}
    if any(key not in by_key for key in manifest):
        return Answer(Outcome.MALFORMED, reason="manifest has an unknown key")
    terminal_needed = any(by_key[key].occurrence_class is OccurrenceClass.TERMINAL for key in manifest)
    if type(source) is CompletedPlanRun:
        if source_capability is not source.plan_capability:
            return Answer(Outcome.REFUSED, reason="generation capability is not identical")
        if terminal_needed:
            return Answer(Outcome.REFUSED, reason="terminal output requires finalized source")
        session = source.session
        final_outputs: Mapping[str, PlanWitnessOccurrence] = {}
        tag = "Generated"
    elif type(source) is CompletedPlanContinuation:
        if (
            type(source_capability) is not CausalPlanContinuationCapability
            or source_capability is not source._issued_capability
            or source_capability.continuation is not source
            or source_capability.generation_capability
               is not source.generated.plan_capability
        ):
            return Answer(Outcome.REFUSED, reason="continuation capability is not identical")
        session = source.generated.session
        final_outputs = source.outputs
        tag = "Finalized"
    else:
        return Answer(Outcome.KIND_MISMATCH, reason="unknown confidential source")
    values: list[ConfidentialEntry] = []
    for key in manifest:
        entry = by_key[key]
        if entry.occurrence_class is OccurrenceClass.SUPPLIED:
            occurrence = session.ingress_occurrences[key]
            value = occurrence.value
        elif entry.occurrence_class is OccurrenceClass.DECISION:
            occurrence = session.decision_exports.get(key)
            if occurrence is None:
                return Answer(Outcome.CANNOT_ANSWER, reason="decision export was inactive")
            value = occurrence.value
        else:
            occurrence = final_outputs.get(key)
            if occurrence is None:
                return Answer(Outcome.CANNOT_ANSWER, reason="terminal export is absent")
            value = occurrence.value
        values.append(ConfidentialEntry(entry, value, occurrence))
    view = ConfidentialPlanWitnessView(surface.identity, tag, consumer, purpose, tuple(values))
    return affirmative((view, ConfidentialViewCapability(view, source_capability)))


@dataclass(frozen=True)
class RelationInstance:
    name: str
    public_slots: Mapping[str, object] = field(
        default_factory=lambda: MappingProxyType({})
    )


@dataclass(frozen=True)
class WitnessBindingEdge:
    surface_key: str
    relation_key: str


@dataclass(frozen=True)
class PlanWitnessBinding:
    surface_id: str
    edges: tuple[WitnessBindingEdge, ...]


def plan_witness_grounding_roles(
    instance: RelationInstance,
    binding: PlanWitnessBinding,
) -> tuple[DownstreamConsumerId, DownstreamPurposeId]:
    """Derive nominal downstream roles from the exact grounding question.

    The caller cannot author or override either expected role.  The two
    identifiers share one exact question basis but remain nominally distinct.
    """

    question_id = semantic_id(
        "relations.plan-witness-run-grounding-question",
        (instance, binding),
    )
    return (
        DownstreamConsumerId(
            semantic_id("pir.downstream-consumer.plan-witness-grounding", question_id)
        ),
        DownstreamPurposeId(
            semantic_id("pir.downstream-purpose.plan-witness-grounding", question_id)
        ),
    )


@dataclass(frozen=True)
class CheckedPlanWitnessGrounding:
    instance: RelationInstance
    run: CompletedPlanRun
    entries: tuple[ConfidentialEntry, ...]
    agreements: tuple[bool, ...]


def check_plan_witness_grounding_for_run(
    instance: RelationInstance,
    binding: PlanWitnessBinding,
    assignment: Mapping[str, object],
    view: ConfidentialPlanWitnessView,
    capability: ConfidentialViewCapability,
    generated: CompletedPlanRun,
) -> Answer:
    if capability.view is not view:
        return Answer(Outcome.REFUSED, reason="view capability is not exact")
    source = capability.source_capability
    source_generation = source if type(source) is CausalPlanGenerationCapability else source.generation_capability
    if source_generation is not generated.plan_capability:
        return Answer(Outcome.REFUSED, reason="view and run are not causally identical")
    expected_consumer, expected_purpose = plan_witness_grounding_roles(
        instance,
        binding,
    )
    if view.consumer != expected_consumer or view.purpose != expected_purpose:
        return Answer(Outcome.REFUSED, reason="view consumer or purpose differs")
    if binding.surface_id != view.surface_id:
        return Answer(Outcome.REFUSED, reason="surface differs")
    by_key = {item.surface.key: item for item in view.entries}
    if {item.surface_key for item in binding.edges} != set(by_key) or {item.relation_key for item in binding.edges} != set(assignment):
        return Answer(Outcome.MALFORMED, reason="grounding manifest is not exact")
    agreements = tuple(by_key[e.surface_key].value == assignment[e.relation_key] for e in binding.edges)
    result = CheckedPlanWitnessGrounding(instance, generated, tuple(by_key[e.surface_key] for e in binding.edges), agreements)
    return Answer(Outcome.AFFIRMATIVE if all(agreements) else Outcome.NEGATIVE, result)


@dataclass(frozen=True)
class PublicRunGrounding:
    instance: RelationInstance
    generated: CompletedPlanRun
    causal: bool


def join_same_run_grounding(private: CheckedPlanWitnessGrounding, public: PublicRunGrounding) -> Answer:
    if not all(private.agreements):
        return Answer(Outcome.REFUSED, reason="private grounding is not affirmative")
    if not public.causal:
        return Answer(Outcome.UNSUPPORTED, reason="replay-qualified public grounding cannot join")
    if private.instance is not public.instance or private.run is not public.generated:
        return Answer(Outcome.REFUSED, reason="public and private grounding are not the same run")
    return affirmative((private, public))


@dataclass(frozen=True)
class CheckedPlanWitnessHandoff:
    source: CheckedPlanWitnessGrounding
    target: CheckedPlanWitnessGrounding
    capability: CausalPlanWitnessHandoffCapability


def join_causal_plan_witness_handoff(
    source: CheckedPlanWitnessGrounding,
    target: CheckedPlanWitnessGrounding,
    capability: CausalPlanWitnessHandoffCapability,
) -> Answer:
    if not all(source.agreements) or not all(target.agreements):
        return Answer(Outcome.REFUSED, reason="handoff join requires affirmative grounding")
    source_generated = capability.supply.source_continuation_capability.continuation.generated
    if (
        source.run is not source_generated
        or not any(
            retained is capability
            for retained in target.run.plan_capability.handoff_capabilities
        )
        or capability.target_protocol_id != target.run.session.plan.protocol_id
        or capability.target_core_id != protocol.core_id(target.run.session.core)
        or capability.target_plan_id != target.run.session.plan.identity
        or capability.value_type is not capability.source_occurrence.value_type
        or capability.target_occurrence.value_type is not capability.value_type
    ):
        return Answer(Outcome.REFUSED, reason="handoff capability has the wrong causal runs")
    source_occurrences = tuple(
        item.occurrence for item in source.entries
        if isinstance(item.occurrence, PlanWitnessOccurrence)
    )
    target_occurrences = [item.occurrence for item in target.entries if isinstance(item.occurrence, WitnessIngressOccurrence)]
    if not any(item is capability.source_occurrence for item in source_occurrences):
        return Answer(Outcome.REFUSED, reason="source grounding omits the exact handoff output")
    if not any(
        item is capability.target_occurrence and item.handoff_capability is capability
        for item in target_occurrences
    ):
        return Answer(Outcome.REFUSED, reason="target grounding omits the propagated handoff capability")
    return affirmative(CheckedPlanWitnessHandoff(source, target, capability))


class PublicCoordinateRole(str, Enum):
    SOURCE_RUN_OUTPUT = "SourceRunPublicOutput"
    SOURCE_INSTANCE_SLOT = "SourceInstancePublicSlot"
    TARGET_INSTANCE_SLOT = "TargetInstancePublicSlot"
    TARGET_STATEMENT_INPUT = "TargetRunStatementBinding"


@dataclass(frozen=True)
class PublicRecurrenceCoordinate:
    role: PublicCoordinateRole
    key: str


@dataclass(frozen=True)
class PublicRecurrenceLeg:
    left: PublicRecurrenceCoordinate
    right: PublicRecurrenceCoordinate


@dataclass(frozen=True)
class PublicRecurrenceGrounding:
    source_run: CompletedPlanRun
    target_run: CompletedPlanRun
    source_instance: RelationInstance
    target_instance: RelationInstance
    legs: tuple[PublicRecurrenceLeg, ...]
    anchor_values: tuple[object, object, object, object]
    leg_agreements: tuple[bool, bool, bool]

    @property
    def agrees(self) -> bool:
        return all(self.leg_agreements)


class UnsupportedPublicRecurrenceCoordinate(ValueError):
    pass


def _public_recurrence_anchor_value(
    coordinate: PublicRecurrenceCoordinate,
    source_run: CompletedPlanRun,
    target_run: CompletedPlanRun,
    source_instance: RelationInstance,
    target_instance: RelationInstance,
) -> object:
    if coordinate.role is PublicCoordinateRole.SOURCE_RUN_OUTPUT:
        declarations = [
            item
            for item in source_run.session.core.schedule
            if item.name == coordinate.key
        ]
        if len(declarations) != 1:
            raise KeyError("source-run output declaration is absent or ambiguous")
        if declarations[0].kind not in {
            protocol.OccurrenceKind.PROVER_MESSAGE,
            protocol.OccurrenceKind.VERIFIER_MESSAGE,
            protocol.OccurrenceKind.ORACLE_PUBLISH,
        }:
            raise UnsupportedPublicRecurrenceCoordinate(
                "source coordinate is not an owner-classified public output"
            )
        matches = [
            entry.value
            for entry in source_run.record.entries
            if entry.occurrence == coordinate.key
            and entry.status is protocol.EntryStatus.EXECUTED
            and entry.value is not None
        ]
        if len(matches) != 1:
            raise KeyError("source-run public output anchor is absent or ambiguous")
        return matches[0]
    if coordinate.role is PublicCoordinateRole.SOURCE_INSTANCE_SLOT:
        return source_instance.public_slots[coordinate.key]
    if coordinate.role is PublicCoordinateRole.TARGET_INSTANCE_SLOT:
        return target_instance.public_slots[coordinate.key]
    if coordinate.role is PublicCoordinateRole.TARGET_STATEMENT_INPUT:
        declarations = {
            item.name: item
            for item in target_run.session.core.inputs
            if item.role is protocol.InputRole.STATEMENT
        }
        if coordinate.key not in declarations:
            raise KeyError("target Statement binding anchor is absent")
        return target_run.session.invocation.values[coordinate.key]
    raise KeyError("unknown public recurrence anchor role")


def check_public_recurrence_grounding(
    source_run: CompletedPlanRun,
    target_run: CompletedPlanRun,
    source_instance: RelationInstance,
    target_instance: RelationInstance,
    legs: tuple[PublicRecurrenceLeg, ...],
) -> Answer:
    if source_run is target_run or source_instance is target_instance:
        return Answer(Outcome.MALFORMED, reason="recurrence roles require distinct occurrences")
    expected_roles = (
        (PublicCoordinateRole.SOURCE_RUN_OUTPUT, PublicCoordinateRole.SOURCE_INSTANCE_SLOT),
        (PublicCoordinateRole.SOURCE_INSTANCE_SLOT, PublicCoordinateRole.TARGET_INSTANCE_SLOT),
        (PublicCoordinateRole.TARGET_INSTANCE_SLOT, PublicCoordinateRole.TARGET_STATEMENT_INPUT),
    )
    if len(legs) != 3 or tuple((leg.left.role, leg.right.role) for leg in legs) != expected_roles:
        return Answer(Outcome.MALFORMED, reason="public recurrence requires exactly three role-correct legs")
    if legs[0].right != legs[1].left or legs[1].right != legs[2].left:
        return Answer(Outcome.MALFORMED, reason="public recurrence legs do not share exact intermediate anchors")
    coordinates = (legs[0].left, legs[0].right, legs[1].right, legs[2].right)
    if any(not item.key for item in coordinates):
        return Answer(Outcome.MALFORMED, reason="public recurrence anchor key is empty")
    try:
        values = tuple(
            _public_recurrence_anchor_value(
                item, source_run, target_run, source_instance, target_instance
            )
            for item in coordinates
        )
    except UnsupportedPublicRecurrenceCoordinate as error:
        return Answer(Outcome.UNSUPPORTED, reason=str(error))
    except KeyError as error:
        return Answer(Outcome.MISSING_DEPENDENCY, reason=str(error))
    agreements = (
        values[0] == values[1],
        values[1] == values[2],
        values[2] == values[3],
    )
    result = PublicRecurrenceGrounding(
        source_run,
        target_run,
        source_instance,
        target_instance,
        legs,
        values,
        agreements,
    )
    return Answer(Outcome.AFFIRMATIVE if result.agrees else Outcome.NEGATIVE, result)


@dataclass(frozen=True)
class CheckedCausalPlanStepRecurrence:
    handoff: CheckedPlanWitnessHandoff
    public_recurrence: PublicRecurrenceGrounding


def join_causal_plan_step_recurrence(
    handoff: CheckedPlanWitnessHandoff,
    public_recurrence: PublicRecurrenceGrounding,
) -> Answer:
    if type(handoff) is not CheckedPlanWitnessHandoff:
        return Answer(Outcome.KIND_MISMATCH, reason="causal witness handoff is absent")
    if type(public_recurrence) is not PublicRecurrenceGrounding:
        return Answer(Outcome.KIND_MISMATCH, reason="public recurrence result is absent")
    if not public_recurrence.agrees:
        return Answer(Outcome.REFUSED, reason="public recurrence is not affirmative")
    if (
        public_recurrence.source_run is not handoff.source.run
        or public_recurrence.target_run is not handoff.target.run
        or public_recurrence.source_instance is not handoff.source.instance
        or public_recurrence.target_instance is not handoff.target.instance
    ):
        return Answer(Outcome.REFUSED, reason="public recurrence roles do not match private handoff")
    return affirmative(CheckedCausalPlanStepRecurrence(handoff, public_recurrence))


class EndpointPurpose(str, Enum):
    PLAN_PROVER = "PlanSpecializedProverEndpoint"
    PLAN_CONTINUATION = "PlanContinuationProverEndpoint"


@dataclass(frozen=True)
class ProjectedNode:
    site: RecipeSite
    name: str
    algorithm: Algorithm
    operands: tuple[Operand, ...]


@dataclass(frozen=True)
class ProjectedExport:
    output_ref: int
    key: str
    site: RecipeSite
    value_type: ValueType


@dataclass(frozen=True)
class ContinuationArmDecl:
    terminal: str
    output_refs: tuple[int, ...]


@dataclass(frozen=True)
class ProjectedPlanGraph:
    """The complete retained finite Plan graph for this evaluator profile.

    This bounded evaluator deliberately retains the full decision-side graph.
    The ordinary purpose erases every derived export and accepted-terminal
    recipe.  The continuation purpose adds every and only export selected by
    an owner-derived nonempty arm and the terminal recipes those exports use.
    Keeping the complete carrier here makes every retained operand, move,
    state update, type, and material declaration identity-bearing.
    """

    protocol_id: object
    private_material: tuple[PrivateMaterialDecl, ...]
    randomness: tuple[RandomnessRequirement, ...]
    state_initializers: tuple[StateAssignment, ...]
    decision_recipes: tuple[DecisionRecipe, ...]
    retained_exports: tuple[DerivedWitnessExport, ...]
    terminal_recipes: tuple[TerminalRecipe, ...]


@dataclass(frozen=True)
class EndpointGraph:
    purpose: EndpointPurpose
    protocol_id: object
    core_id: object
    plan_graph: ProjectedPlanGraph
    nodes: tuple[ProjectedNode, ...]
    exports: tuple[ProjectedExport, ...]
    arms: tuple[ContinuationArmDecl, ...]
    completion: str = "NoSourceSemanticCompletion"

    @property
    def identity(self) -> str: return semantic_id("oir.endpoint", self)


def _projected_nodes(
    plan_graph: ProjectedPlanGraph,
) -> tuple[ProjectedNode, ...]:
    decision_nodes = tuple(
        ProjectedNode(
            RecipeSite.decision(recipe.occurrence),
            node.name,
            node.algorithm,
            node.operands,
        )
        for recipe in plan_graph.decision_recipes
        for node in recipe.nodes
    )
    terminal_nodes = tuple(
        ProjectedNode(
            RecipeSite.terminal(recipe.terminal),
            node.name,
            node.algorithm,
            node.operands,
        )
        for recipe in plan_graph.terminal_recipes
        for node in recipe.nodes
    )
    return decision_nodes + terminal_nodes


def _derived_continuation_arms(
    core: object,
    plan: ProverPlan,
) -> tuple[tuple[str, tuple[DerivedWitnessExport, ...]], ...]:
    return tuple(
        (terminal, arm)
        for terminal in plan.accepted_terminals
        if (arm := continuation_arm(core, plan, terminal))
    )


def endpoint_projection_support(
    core: object,
    plan: ProverPlan,
    purpose: EndpointPurpose,
) -> Answer:
    if type(purpose) is not EndpointPurpose:
        return Answer(Outcome.KIND_MISMATCH, reason="endpoint purpose has the wrong kind")
    try:
        admit_plan(core, plan)
    except (PlanError, protocol.ModelError) as error:
        return Answer(Outcome.MALFORMED, reason=str(error))
    if (
        purpose is EndpointPurpose.PLAN_CONTINUATION
        and not _derived_continuation_arms(core, plan)
    ):
        return Answer(Outcome.UNSUPPORTED, reason="NoPlanContinuationArm")
    return affirmative((protocol.core_id(core), plan.identity, purpose))


def derive_endpoint_graph(
    core: object,
    plan: ProverPlan,
    purpose: EndpointPurpose,
) -> EndpointGraph:
    support = endpoint_projection_support(core, plan, purpose)
    if support.outcome is not Outcome.AFFIRMATIVE:
        raise PlanError(f"{support.outcome.value}: {support.reason}")
    if purpose is EndpointPurpose.PLAN_PROVER:
        plan_graph = ProjectedPlanGraph(
            plan.protocol_id,
            plan.private_material,
            plan.randomness,
            plan.state_initializers,
            plan.decision_recipes,
            (),
            (),
        )
        return EndpointGraph(
            purpose,
            plan.protocol_id,
            protocol.core_id(core),
            plan_graph,
            _projected_nodes(plan_graph),
            (),
            (),
        )

    derived_arms = _derived_continuation_arms(core, plan)
    selected_by_key = {
        item.key: item
        for _, arm in derived_arms
        for item in arm
    }
    selected = tuple(selected_by_key[key] for key in sorted(selected_by_key))
    retained_terminals = {
        item.site.ref
        for item in selected
        if item.site.kind is SiteKind.ACCEPTED_TERMINAL
    }
    retained_terminal_recipes = tuple(
        recipe
        for recipe in plan.terminal_recipes
        if recipe.terminal in retained_terminals
    )
    plan_graph = ProjectedPlanGraph(
        plan.protocol_id,
        plan.private_material,
        plan.randomness,
        plan.state_initializers,
        plan.decision_recipes,
        selected,
        retained_terminal_recipes,
    )
    exports = tuple(
        ProjectedExport(index, item.key, item.site, item.value_type)
        for index, item in enumerate(selected)
    )
    ref_by_key = {item.key: item.output_ref for item in exports}
    arms = tuple(
        ContinuationArmDecl(
            terminal,
            tuple(sorted(ref_by_key[item.key] for item in arm)),
        )
        for terminal, arm in derived_arms
    )
    return EndpointGraph(
        purpose,
        plan.protocol_id,
        protocol.core_id(core),
        plan_graph,
        _projected_nodes(plan_graph),
        exports,
        arms,
    )


def _locally_validate_projected_plan_graph(
    plan_graph: ProjectedPlanGraph,
) -> str | None:
    if type(plan_graph) is not ProjectedPlanGraph:
        return "projected Plan graph has the wrong exact carrier"
    if (
        any(type(item) is not PrivateMaterialDecl for item in plan_graph.private_material)
        or any(type(item) is not RandomnessRequirement for item in plan_graph.randomness)
        or any(type(item) is not StateAssignment for item in plan_graph.state_initializers)
        or any(type(item) is not DecisionRecipe for item in plan_graph.decision_recipes)
        or any(type(item) is not DerivedWitnessExport for item in plan_graph.retained_exports)
        or any(type(item) is not TerminalRecipe for item in plan_graph.terminal_recipes)
    ):
        return "projected Plan table has the wrong exact member kind"
    private_keys = tuple(item.key for item in plan_graph.private_material)
    random_keys = tuple(item.key for item in plan_graph.randomness)
    state_slots = tuple(item.slot for item in plan_graph.state_initializers)
    decisions = tuple(item.occurrence for item in plan_graph.decision_recipes)
    terminals = tuple(item.terminal for item in plan_graph.terminal_recipes)
    if (
        any(not key for key in private_keys + random_keys + state_slots + decisions + terminals)
        or len(set(private_keys)) != len(private_keys)
        or len(set(random_keys)) != len(random_keys)
        or len(set(state_slots)) != len(state_slots)
        or len(set(decisions)) != len(decisions)
        or len(set(terminals)) != len(terminals)
    ):
        return "projected Plan coordinate table is empty or nonunique"
    if any(
        type(item.kind) is not PrivateMaterialKind
        or type(item.value_type) is not ValueType
        for item in plan_graph.private_material
    ) or any(
        type(item.value_type) is not ValueType
        or item.first_available_at not in decisions
        for item in plan_graph.randomness
    ):
        return "projected material declaration kind or type is invalid"
    if any(
        type(item.value) is not Operand
        or item.value.kind not in {OperandKind.CONSTANT, OperandKind.PRIVATE}
        or (
            item.value.kind is OperandKind.PRIVATE
            and item.value.ref not in private_keys
        )
        for item in plan_graph.state_initializers
    ):
        return "projected state initializer is outside the retained graph"

    nodes_by_site: dict[RecipeSite, set[str]] = {}
    recipes: list[tuple[RecipeSite, tuple[RecipeNode, ...], tuple[Operand, ...]]] = []
    for recipe in plan_graph.decision_recipes:
        if tuple(item.slot for item in recipe.state_after) != state_slots:
            return "projected decision state update is not total and ordered"
        if type(recipe.move) is not Operand or any(
            type(item.value) is not Operand for item in recipe.state_after
        ):
            return "projected decision root has the wrong exact carrier"
        recipes.append(
            (
                RecipeSite.decision(recipe.occurrence),
                recipe.nodes,
                (recipe.move,) + tuple(item.value for item in recipe.state_after),
            )
        )
    for recipe in plan_graph.terminal_recipes:
        recipes.append((RecipeSite.terminal(recipe.terminal), recipe.nodes, ()))
    for site, nodes, roots in recipes:
        prior: set[str] = set()
        for node in nodes:
            if type(node) is not RecipeNode or not node.name or node.name in prior:
                return "projected recipe node is malformed or nonunique"
            for operand in node.operands:
                if type(operand) is not Operand:
                    return "projected recipe operand has the wrong exact carrier"
                if operand.kind is OperandKind.NODE and operand.ref not in prior:
                    return "projected node reference is forward or cross-site"
                if operand.kind is OperandKind.PRIVATE and operand.ref not in private_keys:
                    return "projected private read is undeclared"
                if operand.kind is OperandKind.RANDOMNESS:
                    if site.kind is SiteKind.ACCEPTED_TERMINAL:
                        return "projected terminal recipe reads randomness"
                    if operand.ref not in random_keys:
                        return "projected randomness read is undeclared"
                if operand.kind is OperandKind.STATE and operand.ref not in state_slots:
                    return "projected state read is undeclared"
                if (
                    operand.kind is OperandKind.TERMINAL_OUTPUT
                    and site.kind is not SiteKind.ACCEPTED_TERMINAL
                ):
                    return "projected decision reads terminal output"
            prior.add(node.name)
        if any(
            root.kind is OperandKind.NODE and root.ref not in prior
            for root in roots
        ):
            return "projected decision root is outside its recipe site"
        nodes_by_site[site] = prior

    export_keys = tuple(item.key for item in plan_graph.retained_exports)
    if (
        tuple(sorted(export_keys)) != export_keys
        or len(set(export_keys)) != len(export_keys)
        or any(
            type(item.value) is not Operand
            or type(item.value_type) is not ValueType
            for item in plan_graph.retained_exports
        )
    ):
        return "projected export table is noncanonical"
    for export in plan_graph.retained_exports:
        if export.site not in nodes_by_site:
            return "projected export site is absent"
        if (
            export.value.kind is OperandKind.NODE
            and export.value.ref not in nodes_by_site[export.site]
        ):
            return "projected export root is outside its recipe site"
    return None


def locally_admit_oir(graph: EndpointGraph) -> Answer:
    if type(graph) is not EndpointGraph or type(graph.purpose) is not EndpointPurpose:
        return Answer(Outcome.KIND_MISMATCH, reason="endpoint graph has the wrong exact carrier")
    if graph.completion != "NoSourceSemanticCompletion":
        return Answer(Outcome.MALFORMED, reason="private continuation is not external completion")
    plan_graph_error = _locally_validate_projected_plan_graph(graph.plan_graph)
    if plan_graph_error is not None:
        return Answer(Outcome.MALFORMED, reason=plan_graph_error)
    if graph.protocol_id != graph.plan_graph.protocol_id:
        return Answer(Outcome.MALFORMED, reason="Plan graph names a different Protocol")
    if graph.nodes != _projected_nodes(graph.plan_graph):
        return Answer(Outcome.MALFORMED, reason="projected recipe nodes are incomplete or phantom")
    expected_exports = tuple(
        ProjectedExport(index, item.key, item.site, item.value_type)
        for index, item in enumerate(graph.plan_graph.retained_exports)
    )
    if graph.exports != expected_exports:
        return Answer(Outcome.MALFORMED, reason="projected exports differ from the retained Plan graph")
    if graph.purpose is EndpointPurpose.PLAN_PROVER:
        if (
            graph.plan_graph.retained_exports
            or graph.plan_graph.terminal_recipes
            or graph.exports
            or graph.arms
        ):
            return Answer(Outcome.MALFORMED, reason="ordinary endpoint carries private continuation")
        return affirmative(graph.identity)
    if not graph.plan_graph.retained_exports or not graph.exports or not graph.arms:
        return Answer(Outcome.MALFORMED, reason="continuation endpoint has no nonempty arm")
    if tuple(item.output_ref for item in graph.exports) != tuple(range(len(graph.exports))):
        return Answer(Outcome.MALFORMED, reason="continuation output refs are not dense")
    refs = {item.output_ref for item in graph.exports}
    if (
        len({arm.terminal for arm in graph.arms}) != len(graph.arms)
        or any(
            not arm.output_refs
            or tuple(sorted(set(arm.output_refs))) != arm.output_refs
            or set(arm.output_refs) - refs
            for arm in graph.arms
        )
    ):
        return Answer(Outcome.MALFORMED, reason="continuation arm is noncanonical or dangling")
    used_refs = {ref for arm in graph.arms for ref in arm.output_refs}
    if used_refs != refs:
        return Answer(Outcome.MALFORMED, reason="continuation output is absent from every arm")
    exports_by_ref = {item.output_ref: item for item in graph.exports}
    for arm in graph.arms:
        if any(
            exports_by_ref[ref].site.kind is SiteKind.ACCEPTED_TERMINAL
            and exports_by_ref[ref].site.ref != arm.terminal
            for ref in arm.output_refs
        ):
            return Answer(Outcome.MALFORMED, reason="terminal export appears in another terminal arm")
    recipe_terminals = {item.terminal for item in graph.plan_graph.terminal_recipes}
    required_terminal_recipes = {
        item.site.ref
        for item in graph.exports
        if item.site.kind is SiteKind.ACCEPTED_TERMINAL
    }
    if recipe_terminals != required_terminal_recipes:
        return Answer(Outcome.MALFORMED, reason="terminal recipe closure differs from selected exports")
    return affirmative(graph.identity)


@dataclass(frozen=True)
class FamilyCase:
    name: str
    evidence_depth: str
    core: object
    construction: object
    invocation: object
    plan: ProverPlan
    private_values: Mapping[str, object]
    randomness_values: Mapping[str, object]
    fresh_values: Mapping[str, int]
    expected_arm: tuple[str, ...]
    expected_requirement: SourceRequirement


def execute_case(case: FamilyCase) -> tuple[CompletedPlanRun, CompletedPlanContinuation]:
    checked = admit_plan(case.core, case.plan)
    prepared_answer = prepare_plan_execution(
        case.core, case.construction, case.invocation, case.plan, checked,
        case.private_values, case.randomness_values,
    )
    assert prepared_answer.outcome is Outcome.AFFIRMATIVE
    session, ready = prepared_answer.value
    generated_answer = generate_plan_run(session, ready, case.fresh_values)
    assert generated_answer.outcome is Outcome.AFFIRMATIVE
    generated = generated_answer.value
    assert generated.continuation_right is not None
    completed_answer = complete_accepted_plan_continuation(
        generated, generated.plan_capability, generated.continuation_right
    )
    assert completed_answer.outcome is Outcome.AFFIRMATIVE
    completed, _ = completed_answer.value
    return generated, completed
