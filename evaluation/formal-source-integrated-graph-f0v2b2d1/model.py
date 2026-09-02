"""Bounded integrated PublicCoin owner evaluator for F0-V2B2D1.

This pre-publication falsifier composes every InteractiveCore constructor family
needed by the B2D graph obligation into one exact canonical-byte carrier.  It
derives the complete PublicCoinView but deliberately does not implement runtime
generation or replay; those remain the separately named F0-V2B2D2 obligation.
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from enum import Enum
import hashlib
import heapq
import importlib.util
from pathlib import Path
import sys
from types import MappingProxyType, ModuleType
from typing import Any, Mapping


ROOT = Path(__file__).resolve().parents[2]
B5_MODEL = (
    ROOT
    / "evaluation"
    / "formal-source-terminal-owner-projections-f0v2b2c1b5b2"
    / "model.py"
)


def _load(name: str, path: Path) -> ModuleType:
    if name in sys.modules:
        return sys.modules[name]
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:  # pragma: no cover - host failure
        raise ImportError(f"cannot load module at {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


b5 = _load("_zkc_f0v2b2d1_b5", B5_MODEL)
b3 = b5.b3
oracle = b3.prior
foundation = b5.foundation
base = b5.base
b2c0 = b5.b2c0
codec = b5.codec
k1 = b5.k1
VIEW_SCHEMAS = b5.VIEW_SCHEMAS
VIEW_OWNERS = b5.VIEW_OWNERS
VIEW_SCHEMA_STATS = b5.VIEW_SCHEMA_STATS

EVALUATOR_FINGERPRINT = hashlib.sha256(
    b"zkc-f0-v2b2d1-integrated-public-coin-owner-v0"
).digest()
MODULE_DECLARATION_MAGIC = "f0v2b2d1.module-effect.v0"
SCENARIOS = (
    "integrated-baseline",
    "private-verifier-output-sink",
    "invalid-module-control-sink",
    "history-challenge-condition",
    "logical-reject-preemption",
)


class IntegratedFailure(ValueError):
    """One stable fail-closed result from the bounded D1 evaluator."""

    def __init__(self, outcome: str, code: str, detail: str) -> None:
        super().__init__(detail)
        self.outcome = outcome
        self.code = code
        self.detail = detail


@dataclass(frozen=True)
class AdmissionResult:
    outcome: str
    code: str
    detail: str
    handle: object | None = None


class ModuleDecisionClass(Enum):
    NO_PROVER_DECISION = 0
    PROVER_DECISION = 1
    PROVER_PUBLICATION = 2


class ModuleVisibility(Enum):
    INTERNAL = 0
    PROVER_ONLY = 1
    VERIFIER_ONLY = 2
    PUBLIC = 3


class ModuleOutputTransfer(Enum):
    DETERMINISTIC = 0
    PROVER_PUBLICATION = 1
    PROVER_INTERNAL = 2


class ModuleDependencyKind(Enum):
    ACTIVITY = 0
    EFFECT = 1
    PAYLOAD_INPUT = 2
    PRIOR_OUTPUT = 3


@dataclass(frozen=True)
class ModuleDependency:
    kind: ModuleDependencyKind
    ordinal: int | None = None


@dataclass(frozen=True)
class ModuleOutputSpec:
    value_type: object
    visibility: ModuleVisibility
    transfer: ModuleOutputTransfer
    dependencies: tuple[ModuleDependency, ...]
    reconstruction_algorithm: object | None
    reconstruction_contract: object | None
    acceptance_relevant: bool


@dataclass(frozen=True)
class ModuleControlSpec:
    dependencies: tuple[ModuleDependency, ...]
    acceptance_relevant: bool


@dataclass(frozen=True)
class ModuleSemantics:
    name: str
    payload_input_types: tuple[object, ...]
    decision_class: ModuleDecisionClass
    move_type: object | None
    outputs: tuple[ModuleOutputSpec, ...]
    controls: tuple[ModuleControlSpec, ...]
    influence_output: int | None
    guard_behavior: str
    replay_rule: str
    terminal_interaction: str
    work_bound: int


@dataclass(frozen=True)
class ModulePayload:
    inputs: tuple[object, ...]


@dataclass(frozen=True)
class ModuleEffectRef:
    module: object
    declaration: object
    payload: ModulePayload


@dataclass(frozen=True)
class Fixture:
    name: str
    environment: object
    core: object
    candidate: object
    protocol_candidate: object
    modules: tuple[object, ...]
    algorithms: tuple[object, ...]


@dataclass(frozen=True)
class GraphEvidence:
    nodes: tuple[tuple[int, ...], ...]
    edges: tuple[tuple[tuple[int, ...], tuple[int, ...]], ...]
    topological: tuple[tuple[int, ...], ...]
    classes: Mapping[tuple[int, ...], int]
    sinks: tuple[tuple[int, ...], ...]
    acceptance_sinks: tuple[tuple[int, ...], ...]
    private_predecessors: tuple[tuple[int, ...], ...]
    logical_cones: Mapping[int, tuple[tuple[int, ...], ...]]
    logical_intersections: Mapping[int, tuple[tuple[int, ...], ...]]
    challenge_validity: Mapping[int, bool]
    challenge_observation_order: Mapping[int, bool]
    eligible: bool


def _fail(outcome: str, code: str, detail: str) -> None:
    raise IntegratedFailure(outcome, code, detail)


def _record(*values: object) -> object:
    return k1.DatumRecord(tuple((index, value) for index, value in enumerate(values)))


def _seq(values: tuple[object, ...]) -> object:
    return k1.DatumSeq(values)


def _variant(case: int, payload: object = k1.UNIT) -> object:
    return k1.DatumVariant(case, payload)


def _bool_datum(value: bool) -> object:
    return _variant(1 if value else 0)


def candidate_profile_artifact() -> object:
    return b5.candidate_profile_artifact()


def profile_evidence() -> dict[str, Any]:
    return b5.profile_evidence()


def candidate_schema_source() -> dict[str, Any]:
    return b5.candidate_schema_source()


_PC_GRAPH_SCHEMA = codec.record_field(VIEW_SCHEMAS["PublicCoinView"], 1)
_PC_NODE_SCHEMA = codec.record_field(_PC_GRAPH_SCHEMA, 0)["element"]
_PC_EDGE_SCHEMA = codec.record_field(_PC_GRAPH_SCHEMA, 1)["element"]


def z3_identity_algorithm() -> object:
    return k1.CanonicalAlgorithm(
        k1.Symbol("F0V2B2D1Z3Identity"), (base.Z3,), k1.Variable(0, base.Z3)
    )


def bool_identity_algorithm() -> object:
    return k1.CanonicalAlgorithm(
        k1.Symbol("F0V2B2D1BoolIdentity"), (k1.BOOL,), k1.Variable(0, k1.BOOL)
    )


def bool_conjunction_algorithm() -> object:
    return k1.CanonicalAlgorithm(
        k1.Symbol("F0V2B2D1BoolConjunction"),
        (k1.BOOL, k1.BOOL),
        k1.Conditional(
            k1.Variable(0, k1.BOOL),
            k1.Variable(1, k1.BOOL),
            k1.Literal(k1.admit_value(k1.BOOL, False)),
        ),
    )


def module_reconstruction_algorithm() -> object:
    return k1.CanonicalAlgorithm(
        k1.Symbol("F0V2B2D1ModuleReconstructZ3"),
        (base.Z3,),
        k1.Variable(0, base.Z3),
    )


def _dependency_datum(dependency: ModuleDependency) -> object:
    if dependency.kind in (
        ModuleDependencyKind.ACTIVITY,
        ModuleDependencyKind.EFFECT,
    ):
        if dependency.ordinal is not None:
            raise k1.ModelError("node-local module dependency carries an ordinal")
        return _variant(dependency.kind.value)
    if type(dependency.ordinal) is not int or dependency.ordinal < 0:
        raise k1.ModelError("indexed module dependency lacks an ordinal")
    return _variant(dependency.kind.value, k1.Nat(dependency.ordinal))


def _output_spec_datum(output: ModuleOutputSpec) -> object:
    if output.transfer is ModuleOutputTransfer.DETERMINISTIC:
        if (
            output.reconstruction_algorithm is None
            or output.reconstruction_contract is None
        ):
            raise k1.ModelError("deterministic module output lacks reconstruction")
        transfer = _variant(
            0,
            _record(
                k1.BytesValue(output.reconstruction_algorithm.internal_reference()),
                k1.BytesValue(output.reconstruction_contract.internal_reference()),
            ),
        )
    else:
        if (
            output.reconstruction_algorithm is not None
            or output.reconstruction_contract is not None
        ):
            raise k1.ModelError("nondeterministic module output carries reconstruction")
        transfer = _variant(output.transfer.value)
    return _record(
        k1.value_type_datum(output.value_type),
        _variant(output.visibility.value),
        transfer,
        _seq(tuple(_dependency_datum(item) for item in output.dependencies)),
        _bool_datum(output.acceptance_relevant),
    )


def _control_spec_datum(control: ModuleControlSpec) -> object:
    return _record(
        _seq(tuple(_dependency_datum(item) for item in control.dependencies)),
        _bool_datum(control.acceptance_relevant),
    )


def _semantics_datum(semantics: ModuleSemantics) -> object:
    if semantics.decision_class is ModuleDecisionClass.NO_PROVER_DECISION:
        decision = _variant(0)
    else:
        if semantics.move_type is None:
            raise k1.ModelError("module decision lacks its move type")
        decision = _variant(
            semantics.decision_class.value, k1.value_type_datum(semantics.move_type)
        )
    return _record(
        k1.Symbol(MODULE_DECLARATION_MAGIC),
        k1.Symbol(semantics.name),
        decision,
        _seq(
            tuple(k1.value_type_datum(item) for item in semantics.payload_input_types)
        ),
        _seq(tuple(_output_spec_datum(item) for item in semantics.outputs)),
        _seq(tuple(_control_spec_datum(item) for item in semantics.controls)),
        _variant(0)
        if semantics.influence_output is None
        else _variant(1, k1.Nat(semantics.influence_output)),
        k1.Symbol(semantics.guard_behavior),
        k1.Symbol(semantics.replay_rule),
        k1.Symbol(semantics.terminal_interaction),
        k1.Nat(semantics.work_bound),
    )


def module_semantics(private_sink: bool = False) -> tuple[ModuleSemantics, ...]:
    activity = ModuleDependency(ModuleDependencyKind.ACTIVITY)
    effect = ModuleDependency(ModuleDependencyKind.EFFECT)
    payload = ModuleDependency(ModuleDependencyKind.PAYLOAD_INPUT, 0)
    output = ModuleDependency(ModuleDependencyKind.PRIOR_OUTPUT, 0)
    reconstruction = module_reconstruction_algorithm()
    contract = k1.DEFAULT_EVALUATION_CONTRACT.identity
    lifecycle = (
        "inherit-exact-occurrence-guard",
        "exact-module-event-replay",
        "nonterminating",
        8,
    )
    return (
        ModuleSemantics(
            "integrated-deterministic-public",
            (base.Z3,),
            ModuleDecisionClass.NO_PROVER_DECISION,
            None,
            (
                ModuleOutputSpec(
                    base.Z3,
                    ModuleVisibility.PUBLIC,
                    ModuleOutputTransfer.DETERMINISTIC,
                    (activity, effect, payload),
                    reconstruction.identity,
                    contract,
                    True,
                ),
            ),
            (ModuleControlSpec((activity, effect, output), True),),
            None,
            *lifecycle,
        ),
        ModuleSemantics(
            "integrated-prover-private",
            (base.Z3,),
            ModuleDecisionClass.PROVER_DECISION,
            base.Z3,
            (
                ModuleOutputSpec(
                    base.Z3,
                    ModuleVisibility.PROVER_ONLY,
                    ModuleOutputTransfer.PROVER_INTERNAL,
                    (activity, effect, payload),
                    None,
                    None,
                    False,
                ),
            ),
            (ModuleControlSpec((activity, effect, output), private_sink),),
            None,
            *lifecycle,
        ),
        ModuleSemantics(
            "integrated-prover-publication",
            (base.Z3,),
            ModuleDecisionClass.PROVER_PUBLICATION,
            base.Z3,
            (
                ModuleOutputSpec(
                    base.Z3,
                    ModuleVisibility.PUBLIC,
                    ModuleOutputTransfer.PROVER_PUBLICATION,
                    (activity, effect, payload),
                    None,
                    None,
                    True,
                ),
            ),
            (ModuleControlSpec((activity, effect, output), True),),
            0,
            *lifecycle,
        ),
    )


def _catalog(kind: str, values: tuple[object, ...]) -> object:
    return _record(k1.Symbol(kind), _seq(values))


def extension_module(private_sink: bool = False) -> object:
    return k1.SemanticModuleCandidate(
        k1.Symbol(
            "f0v2b2d1.integrated-module-private-sink"
            if private_sink
            else "f0v2b2d1.integrated-module-baseline"
        ),
        (),
        _seq(
            (
                _catalog(
                    "pir.core-effect",
                    tuple(
                        _semantics_datum(item)
                        for item in module_semantics(private_sink)
                    ),
                ),
            )
        ),
    )


def _module_payload_datum(payload: ModulePayload) -> object:
    if type(payload) is not ModulePayload:
        raise k1.ModelError("module payload has another exact carrier")
    return _record(_seq(tuple(base.value_ref_datum(item) for item in payload.inputs)))


def _module_effect_datum(effect: ModuleEffectRef) -> object:
    if type(effect) is not ModuleEffectRef:
        raise k1.ModelError("module effect has another exact carrier")
    return _record(
        k1.BytesValue(effect.module.internal_reference()),
        base.module_declaration_ref_datum(effect.declaration),
        _module_payload_datum(effect.payload),
    )


def _effect_datum(effect: object) -> object:
    if type(effect) is base.ProverMessageEffect:
        return base._effect_datum(effect)
    if type(effect) is foundation.VerifierMessageEffect:
        return foundation._effect_datum(effect)
    if type(effect) is base.ChallengeEffect:
        return _variant(2, k1.Nat(effect.challenge))
    if type(effect) is base.CheckEffect:
        return _variant(3, k1.Nat(effect.check))
    if type(effect) is b3.ApplyReductionEffect:
        return _variant(4, k1.Nat(effect.reduction))
    if type(effect) is base.TerminalEffect:
        return _variant(5, k1.Nat(effect.terminal))
    if type(effect) in (
        oracle.PublishOracleEffect,
        oracle.QueryOracleEffect,
        oracle.AnswerOracleEffect,
    ):
        return oracle._oracle_effect_datum(effect)
    if type(effect) is ModuleEffectRef:
        return _variant(7, _module_effect_datum(effect))
    raise k1.ModelError("unknown integrated Core effect carrier")


def core_domain_datum(core: object) -> object:
    if type(core) is not base.InteractiveCore:
        raise k1.ModelError("integrated Core has another exact carrier")
    return _record(
        _seq(
            tuple(
                k1.BytesValue(item.internal_reference()) for item in core.used_modules
            )
        ),
        _seq(tuple(base._input_datum(item) for item in core.public_inputs)),
        _seq(tuple(base._input_datum(item) for item in core.verifier_private_inputs)),
        _seq(tuple(base._constant_datum(item) for item in core.constants)),
        _seq(tuple(base._derived_datum(item) for item in core.derived_values)),
        _seq(tuple(base._scope_datum(item) for item in core.scopes)),
        _seq(tuple(base._binding_datum(item) for item in core.public_bindings)),
        _seq(tuple(base._challenge_datum(item) for item in core.challenges)),
        _seq(tuple(oracle._oracle_datum(item) for item in core.oracles)),
        _seq(tuple(base._check_datum(item) for item in core.checks)),
        _seq(tuple(b3._claim_datum(item) for item in core.claims)),
        _seq(tuple(b3._reduction_datum(item) for item in core.reductions)),
        _seq(tuple(b5._terminal_datum(item) for item in core.terminals)),
        _seq(
            tuple(
                _record(
                    k1.Nat(item.scope),
                    base._guard_datum(item.guard),
                    _effect_datum(item.effect),
                )
                for item in core.occurrences
            )
        ),
    )


def core_profiled_body(core: object, profile_id: object) -> bytes:
    return k1.encode_datum(
        k1.profiled_semantic_body(profile_id, core_domain_datum(core))
    )


def core_id(core: object, profile_id: object) -> object:
    return k1.profiled_content_id(
        base.TARGET_CORE_KIND,
        profile_id,
        core_domain_datum(core),
        semantic_regime=k1.SEMANTIC_REGIME_ID,
    )


def make_candidate(core: object, profile_id: object) -> object:
    return b2c0.CanonicalCoreCandidate(
        core_id(core, profile_id), profile_id, core_profiled_body(core, profile_id)
    )


def _decode_module_payload(value: object) -> ModulePayload:
    (inputs,) = b2c0._record(value, (0,), "module payload")
    return ModulePayload(
        tuple(
            b2c0._decode_value_ref(item)
            for item in b2c0._sequence(inputs, "module payload inputs")
        )
    )


def _decode_effect(value: object) -> object:
    case, payload = b2c0._variant(value, tuple(range(8)), "Core effect")
    if case == 0:
        channel, payload_type = b2c0._record(payload, (0, 1), "Prover message")
        return base.ProverMessageEffect(
            b2c0._decode_module_ref(channel), b2c0._decode_value_type(payload_type)
        )
    if case == 1:
        channel, algorithm, contract, inputs, payload_type = b2c0._record(
            payload, (0, 1, 2, 3, 4), "Verifier message"
        )
        return foundation.VerifierMessageEffect(
            b2c0._decode_module_ref(channel),
            b2c0._content_ref(algorithm, "Verifier-message algorithm"),
            b2c0._content_ref(contract, "Verifier-message contract"),
            tuple(
                b2c0._decode_value_ref(item)
                for item in b2c0._sequence(inputs, "Verifier-message inputs")
            ),
            b2c0._decode_value_type(payload_type),
        )
    if case == 2:
        return base.ChallengeEffect(b2c0._nat(payload, "Challenge backlink"))
    if case == 3:
        return base.CheckEffect(b2c0._nat(payload, "Check backlink"))
    if case == 4:
        return b3.ApplyReductionEffect(b2c0._nat(payload, "Reduction backlink"))
    if case == 5:
        return base.TerminalEffect(b2c0._nat(payload, "Terminal backlink"))
    if case == 6:
        oracle_case, oracle_payload = b2c0._variant(payload, (0, 1, 2), "Oracle effect")
        if oracle_case == 0:
            return oracle.PublishOracleEffect(
                b2c0._nat(oracle_payload, "publication Oracle")
            )
        if oracle_case == 1:
            oracle_ref, index, visibility = b2c0._record(
                oracle_payload, (0, 1, 2), "Oracle query"
            )
            visibility_case, visibility_payload = b2c0._variant(
                visibility, (0, 1), "Oracle visibility"
            )
            b2c0._unit(visibility_payload, "Oracle visibility payload")
            return oracle.QueryOracleEffect(
                b2c0._nat(oracle_ref, "query Oracle"),
                b2c0._decode_value_ref(index),
                oracle.OracleVisibility(visibility_case),
            )
        return oracle.AnswerOracleEffect(
            b2c0._nat(oracle_payload, "answer Query backlink")
        )
    module, declaration, module_payload = b2c0._record(
        payload, (0, 1, 2), "module effect"
    )
    return ModuleEffectRef(
        b2c0._content_ref(module, "module-effect owner"),
        b2c0._decode_module_ref(declaration),
        _decode_module_payload(module_payload),
    )


def decode_core(domain: object) -> object:
    """Strictly decode every table of the integrated candidate Core."""

    fields = b2c0._record(domain, tuple(range(14)), "InteractiveCore")
    tables = tuple(
        b2c0._sequence(value, f"InteractiveCore field {ordinal}")
        for ordinal, value in enumerate(fields)
    )
    used_modules = tuple(b2c0._content_ref(item, "used module") for item in tables[0])
    public_inputs = tuple(
        base.InputDecl(
            b2c0._decode_value_type(b2c0._record(item, (0,), "public input")[0])
        )
        for item in tables[1]
    )
    private_inputs = tuple(
        base.InputDecl(
            b2c0._decode_value_type(
                b2c0._record(item, (0,), "verifier-private input")[0]
            )
        )
        for item in tables[2]
    )
    constants: list[object] = []
    for item in tables[3]:
        value_type, datum = b2c0._record(item, (0, 1), "typed constant")
        decoded_type = b2c0._decode_value_type(value_type)
        try:
            admitted = k1.admit_value(decoded_type, datum)
        except Exception as error:
            _fail("Refused", "F0V2B2D1-R-CONSTANT", str(error))
        constants.append(base.TypedConstantDecl(decoded_type, admitted))
    derived_values: list[object] = []
    for item in tables[4]:
        algorithm, contract, inputs, result_type = b2c0._record(
            item, (0, 1, 2, 3), "derived value"
        )
        derived_values.append(
            base.DerivedValueDecl(
                b2c0._content_ref(algorithm, "derived algorithm"),
                b2c0._content_ref(contract, "derived contract"),
                tuple(
                    b2c0._decode_value_ref(value)
                    for value in b2c0._sequence(inputs, "derived inputs")
                ),
                b2c0._decode_value_type(result_type),
            )
        )
    scopes: list[object] = []
    for item in tables[5]:
        parent, opening = b2c0._record(item, (0, 1), "scope")
        parent_case, parent_payload = b2c0._variant(parent, (0, 1), "scope parent")
        opening_case, opening_payload = b2c0._variant(opening, (0, 1), "scope opening")
        if parent_case == 0:
            b2c0._unit(parent_payload, "absent scope parent")
        if opening_case == 0:
            b2c0._unit(opening_payload, "initial scope opening")
        scopes.append(
            base.ScopeDecl(
                None if parent_case == 0 else b2c0._nat(parent_payload, "scope parent"),
                None
                if opening_case == 0
                else b2c0._nat(opening_payload, "scope opening"),
            )
        )
    bindings: list[object] = []
    for item in tables[6]:
        scope, binding_class, reference = b2c0._record(
            item, (0, 1, 2), "public binding"
        )
        class_case, class_payload = b2c0._variant(
            binding_class, (0, 1, 2), "binding class"
        )
        b2c0._unit(class_payload, "binding-class payload")
        bindings.append(
            base.PublicBindingDecl(
                b2c0._nat(scope, "binding scope"),
                base.BindingClass(class_case),
                b2c0._decode_value_ref(reference),
            )
        )
    checks: list[object] = []
    for item in tables[9]:
        algorithm, contract, inputs = b2c0._record(item, (0, 1, 2), "Check")
        checks.append(
            base.CheckDecl(
                b2c0._content_ref(algorithm, "Check algorithm"),
                b2c0._content_ref(contract, "Check contract"),
                tuple(
                    b2c0._decode_value_ref(value)
                    for value in b2c0._sequence(inputs, "Check inputs")
                ),
            )
        )
    occurrences: list[object] = []
    for item in tables[13]:
        scope, guard, effect = b2c0._record(item, (0, 1, 2), "occurrence")
        occurrences.append(
            base.OccurrenceDecl(
                b2c0._nat(scope, "occurrence scope"),
                b2c0._decode_guard(guard),
                _decode_effect(effect),
            )
        )
    return base.InteractiveCore(
        used_modules,
        public_inputs,
        private_inputs,
        tuple(constants),
        tuple(derived_values),
        tuple(scopes),
        tuple(bindings),
        tuple(b3._decode_challenge(item) for item in tables[7]),
        tuple(oracle._decode_oracle(item) for item in tables[8]),
        tuple(checks),
        tuple(b3._decode_claim(item) for item in tables[10]),
        tuple(b3._decode_reduction(item) for item in tables[11]),
        tuple(b5._decode_terminal(item) for item in tables[12]),
        tuple(occurrences),
    )


def _module_references(core: object) -> tuple[object, ...]:
    references: list[object] = []
    for challenge in core.challenges:
        references.extend((challenge.domain, challenge.fresh_law))
        if type(challenge.correlation) is base.JointCorrelation:
            references.append(challenge.correlation.group)
        if type(challenge.reduction_use) is base.SharedReductionUse:
            references.append(challenge.reduction_use.contract)
    for item in core.oracles:
        mode = item.publication_mode
        if type(mode) is oracle.PublicBindingOracle:
            references.append(mode.binding_contract)
        elif type(mode) is oracle.LogicalAccessOracle:
            references.append(mode.domain_law)
    references.extend(item.contract for item in core.claims)
    for item in core.reductions:
        references.append(item.contract)
        references.extend(item.output_contracts)
    for occurrence in core.occurrences:
        effect = occurrence.effect
        if type(effect) in (base.ProverMessageEffect, foundation.VerifierMessageEffect):
            references.append(effect.channel)
        elif type(effect) is ModuleEffectRef:
            references.append(effect.declaration)
    return tuple(references)


def _ordinary_references(
    core: object,
) -> tuple[tuple[object, ...], tuple[object, ...]]:
    algorithms: set[object] = set()
    contracts: set[object] = set()
    for item in core.derived_values:
        algorithms.add(item.algorithm)
        contracts.add(item.evaluation_contract)
    for item in core.oracles:
        mode = item.publication_mode
        if type(mode) is oracle.PublicBindingOracle:
            algorithms.add(mode.binding_algorithm)
            contracts.add(mode.evaluation_contract)
    for item in core.checks:
        algorithms.add(item.algorithm)
        contracts.add(item.evaluation_contract)
    for occurrence in core.occurrences:
        guard = occurrence.guard
        if type(guard) is base.EvaluateGuard:
            algorithms.add(guard.algorithm)
            contracts.add(guard.evaluation_contract)
        effect = occurrence.effect
        if type(effect) is foundation.VerifierMessageEffect:
            algorithms.add(effect.algorithm)
            contracts.add(effect.evaluation_contract)
    for semantics in module_semantics(False):
        for output in semantics.outputs:
            if output.reconstruction_algorithm is not None:
                algorithms.add(output.reconstruction_algorithm)
                contracts.add(output.reconstruction_contract)

    def reference_key(item: object) -> bytes:
        return item.internal_reference()

    return (
        tuple(sorted(algorithms, key=reference_key)),
        tuple(sorted(contracts, key=reference_key)),
    )


def _build_core(
    scenario: str,
) -> tuple[object, tuple[object, ...], tuple[object, ...]]:
    if scenario not in SCENARIOS:
        raise KeyError(scenario)
    private_sink = scenario == "invalid-module-control-sink"
    protocol_module = b3.protocol_module()
    oracle_module = oracle.oracle_module(base.Z3)
    effect_module = extension_module(private_sink)
    modules = (protocol_module, oracle_module, effect_module)

    protocol_id = protocol_module.identity
    oracle_id = oracle_module.identity
    effect_id = effect_module.identity
    channel = base.ModuleDeclarationRef(protocol_id, "pir.message-channel", 0)
    challenge_domain = base.ModuleDeclarationRef(protocol_id, "pir.challenge-domain", 0)
    fresh_law = base.ModuleDeclarationRef(protocol_id, "pir.public-coin-law", 0)
    joint_group = base.ModuleDeclarationRef(
        protocol_id, "pir.coin-correlation-group", 0
    )
    sharing = base.ModuleDeclarationRef(
        protocol_id, "pir.challenge-sharing-contract", 0
    )
    claim_input = base.ModuleDeclarationRef(protocol_id, "pir.claim-contract", 0)
    claim_output = base.ModuleDeclarationRef(protocol_id, "pir.claim-contract", 1)
    reduction_a = base.ModuleDeclarationRef(protocol_id, "pir.reduction-contract", 0)
    reduction_b = base.ModuleDeclarationRef(protocol_id, "pir.reduction-contract", 1)
    binding_contract = base.ModuleDeclarationRef(
        oracle_id, "pir.oracle-binding-contract", 0
    )
    domain_law = base.ModuleDeclarationRef(oracle_id, "pir.oracle-domain-law", 0)

    z3_identity = z3_identity_algorithm()
    bool_identity = bool_identity_algorithm()
    conjunction = bool_conjunction_algorithm()
    reconstruction = module_reconstruction_algorithm()
    provisional_binding_oracle = oracle.OracleDecl(
        1,
        oracle.OracleOrigin.PROVER,
        base.Z3,
        base.Z3,
        2,
        oracle.FullCanonicalOracle(),
    )
    binding_algorithm = oracle.binding_algorithm(provisional_binding_oracle, base.Z3)
    algorithms = (
        z3_identity,
        bool_identity,
        conjunction,
        reconstruction,
        binding_algorithm,
    )
    contract = k1.DEFAULT_EVALUATION_CONTRACT.identity

    public_inputs = (
        base.InputDecl(base.Z3),
        base.InputDecl(k1.BOOL),
        base.InputDecl(k1.BOOL),
        base.InputDecl(k1.BOOL),
    )
    private_inputs = (base.InputDecl(base.Z3),)
    constants = (
        base.TypedConstantDecl(base.Z3, k1.admit_value(base.Z3, k1.Nat(1))),
        base.TypedConstantDecl(k1.BOOL, k1.admit_value(k1.BOOL, True)),
    )
    derived_values = (
        base.DerivedValueDecl(
            z3_identity.identity,
            contract,
            (base.ConstantRef(0),),
            base.Z3,
        ),
        base.DerivedValueDecl(
            z3_identity.identity,
            contract,
            (base.VerifierPrivateInputRef(0),),
            base.Z3,
        ),
        base.DerivedValueDecl(
            bool_identity.identity,
            contract,
            (base.PublicInputRef(3),),
            k1.BOOL,
        ),
    )
    scopes = (base.ScopeDecl(None, None), base.ScopeDecl(0, 0))
    bindings = (
        base.PublicBindingDecl(0, base.BindingClass.STATEMENT, base.PublicInputRef(0)),
        base.PublicBindingDecl(
            0, base.BindingClass.SESSION_CONTEXT, base.PublicInputRef(1)
        ),
        base.PublicBindingDecl(
            0, base.BindingClass.SESSION_CONTEXT, base.PublicInputRef(2)
        ),
        base.PublicBindingDecl(
            0, base.BindingClass.PUBLIC_PARAMETER, base.PublicInputRef(3)
        ),
        base.PublicBindingDecl(
            1, base.BindingClass.SESSION_CONTEXT, base.DerivedValueRef(0)
        ),
    )

    challenge_one_condition: object = base.PublicInputRef(3)
    if scenario == "history-challenge-condition":
        challenge_one_condition = base.OccurrenceOutputRef(1, 0)
    challenges = (
        base.ChallengeDecl(
            1,
            base.Z3,
            challenge_domain,
            fresh_law,
            base.IndependentCorrelation(),
            base.SharedReductionUse(sharing),
            (base.DerivedValueRef(2),),
        ),
        base.ChallengeDecl(
            1,
            base.Z3,
            challenge_domain,
            fresh_law,
            base.JointCorrelation(joint_group, 0, ()),
            base.ExclusiveReductionUse(),
            (challenge_one_condition,),
        ),
        base.ChallengeDecl(
            1,
            base.Z3,
            challenge_domain,
            fresh_law,
            base.JointCorrelation(joint_group, 1, (1,)),
            base.ExclusiveReductionUse(),
            (base.PublicInputRef(3),),
        ),
    )
    full_oracle = oracle.OracleDecl(
        1,
        oracle.OracleOrigin.INITIAL,
        base.Z3,
        base.Z3,
        2,
        oracle.FullCanonicalOracle(),
    )
    binding_oracle = replace(
        provisional_binding_oracle,
        publication_mode=oracle.PublicBindingOracle(
            base.Z3,
            binding_contract,
            binding_algorithm.identity,
            contract,
        ),
    )
    logical_oracle = oracle.OracleDecl(
        1,
        oracle.OracleOrigin.INITIAL,
        base.Z3,
        k1.BOOL,
        2,
        oracle.LogicalAccessOracle(domain_law),
    )
    oracles = (full_oracle, binding_oracle, logical_oracle)
    checks = (
        base.CheckDecl(bool_identity.identity, contract, (base.PublicInputRef(3),)),
    )
    claims = (
        b3.ClaimDecl(
            claim_input,
            0,
            base.ClaimUsage.REUSABLE,
            b3.InitialClaimSource(0),
        ),
        b3.ClaimDecl(
            claim_output,
            1,
            base.ClaimUsage.REUSABLE,
            b3.ReductionOutputClaimSource(0, 0),
        ),
        b3.ClaimDecl(
            claim_output,
            1,
            base.ClaimUsage.REUSABLE,
            b3.ReductionOutputClaimSource(1, 0),
        ),
    )
    reductions = (
        b3.ReductionDecl(
            reduction_a,
            1,
            (0,),
            (base.OccurrenceOutputRef(1, 0), base.OccurrenceOutputRef(7, 0)),
            (0, 1),
            (b3.ReductionPublicationRequirement(1, 0),),
            (claim_output,),
        ),
        b3.ReductionDecl(
            reduction_b,
            1,
            (0,),
            (base.OccurrenceOutputRef(2, 0),),
            (0, 2),
            (b3.ReductionPublicationRequirement(4, 0),),
            (claim_output,),
        ),
    )

    verifier_input = (
        base.DerivedValueRef(1)
        if scenario == "private-verifier-output-sink"
        else base.DerivedValueRef(0)
    )
    guarded_verifier = foundation.VerifierMessageEffect(
        channel,
        z3_identity.identity,
        contract,
        (verifier_input,),
        base.Z3,
    )
    semantics = module_semantics(private_sink)

    def module_effect(ordinal: int, value: object) -> ModuleEffectRef:
        return ModuleEffectRef(
            effect_id,
            base.ModuleDeclarationRef(effect_id, "pir.core-effect", ordinal),
            ModulePayload((value,)),
        )

    occurrences: list[object] = [
        base.OccurrenceDecl(
            1,
            base.EvaluateGuard(
                bool_identity.identity,
                contract,
                (base.PublicInputRef(3),),
            ),
            guarded_verifier,
        ),
        base.OccurrenceDecl(
            1, base.AlwaysGuard(), base.ProverMessageEffect(channel, base.Z3)
        ),
        base.OccurrenceDecl(
            1, base.AlwaysGuard(), module_effect(0, base.DerivedValueRef(0))
        ),
        base.OccurrenceDecl(
            1, base.AlwaysGuard(), module_effect(1, base.DerivedValueRef(1))
        ),
        base.OccurrenceDecl(
            1, base.AlwaysGuard(), module_effect(2, base.DerivedValueRef(0))
        ),
        base.OccurrenceDecl(1, base.AlwaysGuard(), oracle.PublishOracleEffect(0)),
        base.OccurrenceDecl(
            1,
            base.AlwaysGuard(),
            oracle.QueryOracleEffect(
                0, base.DerivedValueRef(0), oracle.OracleVisibility.PUBLIC
            ),
        ),
        base.OccurrenceDecl(1, base.AlwaysGuard(), oracle.AnswerOracleEffect(6)),
        base.OccurrenceDecl(1, base.AlwaysGuard(), oracle.PublishOracleEffect(1)),
        base.OccurrenceDecl(
            1,
            base.AlwaysGuard(),
            oracle.QueryOracleEffect(
                1, base.ConstantRef(0), oracle.OracleVisibility.VERIFIER_ONLY
            ),
        ),
        base.OccurrenceDecl(1, base.AlwaysGuard(), oracle.AnswerOracleEffect(9)),
        base.OccurrenceDecl(1, base.AlwaysGuard(), oracle.PublishOracleEffect(2)),
        base.OccurrenceDecl(
            1,
            base.AlwaysGuard(),
            oracle.QueryOracleEffect(
                2, base.ConstantRef(0), oracle.OracleVisibility.PUBLIC
            ),
        ),
        base.OccurrenceDecl(1, base.AlwaysGuard(), oracle.AnswerOracleEffect(12)),
        base.OccurrenceDecl(1, base.AlwaysGuard(), base.ChallengeEffect(0)),
        base.OccurrenceDecl(1, base.AlwaysGuard(), base.ChallengeEffect(1)),
        base.OccurrenceDecl(1, base.AlwaysGuard(), base.ChallengeEffect(2)),
        base.OccurrenceDecl(1, base.AlwaysGuard(), base.CheckEffect(0)),
        base.OccurrenceDecl(1, base.AlwaysGuard(), b3.ApplyReductionEffect(0)),
        base.OccurrenceDecl(1, base.AlwaysGuard(), b3.ApplyReductionEffect(1)),
    ]

    if scenario == "logical-reject-preemption":
        terminals = (
            b5.TerminalDecl(base.TerminalVerdict.REJECT, (), (), (), ()),
            b5.TerminalDecl(
                base.TerminalVerdict.ABORT,
                (base.PublicInputRef(2),),
                (),
                (1,),
                (2,),
            ),
            b5.TerminalDecl(
                base.TerminalVerdict.ACCEPT,
                (base.OccurrenceOutputRef(4, 0),),
                (),
                (0, 1),
                (1, 2),
            ),
        )
        terminal_guards = (
            base.EvaluateGuard(
                bool_identity.identity,
                contract,
                (base.OccurrenceOutputRef(13, 0),),
            ),
            base.EvaluateGuard(
                bool_identity.identity, contract, (base.PublicInputRef(2),)
            ),
            base.AlwaysGuard(),
        )
    else:
        terminals = (
            b5.TerminalDecl(
                base.TerminalVerdict.ACCEPT,
                (base.OccurrenceOutputRef(4, 0),),
                (0,),
                (0, 1),
                (1, 2),
            ),
            b5.TerminalDecl(
                base.TerminalVerdict.ABORT,
                (base.PublicInputRef(2),),
                (),
                (1,),
                (2,),
            ),
            b5.TerminalDecl(
                base.TerminalVerdict.REJECT,
                (base.PublicInputRef(0),),
                (),
                (1,),
                (2,),
            ),
        )
        terminal_guards = (
            base.EvaluateGuard(
                conjunction.identity,
                contract,
                (base.OccurrenceOutputRef(17, 0), base.PublicInputRef(1)),
            ),
            base.EvaluateGuard(
                bool_identity.identity, contract, (base.PublicInputRef(2),)
            ),
            base.AlwaysGuard(),
        )
    occurrences.extend(
        base.OccurrenceDecl(1, terminal_guards[index], base.TerminalEffect(index))
        for index in range(3)
    )

    provisional = base.InteractiveCore(
        (),
        public_inputs,
        private_inputs,
        constants,
        derived_values,
        scopes,
        bindings,
        challenges,
        oracles,
        checks,
        claims,
        reductions,
        terminals,
        tuple(occurrences),
    )
    used_modules = tuple(
        sorted(
            {reference.module for reference in _module_references(provisional)},
            key=lambda item: item.internal_reference(),
        )
    )
    if set(used_modules) != {item.identity for item in modules}:
        raise AssertionError("integrated fixture module closure differs")
    core = replace(provisional, used_modules=used_modules)
    algorithm_refs, _contract_refs = _ordinary_references(core)
    algorithms = tuple(
        item for item in algorithms if item.identity in set(algorithm_refs)
    )
    if semantics != module_semantics(private_sink):
        raise AssertionError("module semantics construction drifted")
    return core, modules, algorithms


def _environment(
    core: object, modules: tuple[object, ...], algorithms: tuple[object, ...]
) -> object:
    profile = candidate_profile_artifact()
    algorithm_map = {
        item.identity: item
        for item in sorted(
            algorithms, key=lambda value: value.identity.internal_reference()
        )
    }
    algorithm_refs, contract_refs = _ordinary_references(core)
    if set(algorithm_map) != set(algorithm_refs):
        raise AssertionError("integrated fixture algorithm closure differs")
    contract = k1.DEFAULT_EVALUATION_CONTRACT
    if set(contract_refs) != {contract.identity}:
        raise AssertionError("integrated fixture contract closure differs")
    module_map = {
        item.identity: item
        for item in sorted(
            modules, key=lambda value: value.identity.internal_reference()
        )
    }
    if set(module_map) != set(core.used_modules):
        raise AssertionError("integrated fixture module preimages differ")
    return base.Environment(
        profile.profile_id,
        MappingProxyType({profile.profile_id: profile.profile}),
        MappingProxyType(module_map),
        MappingProxyType(algorithm_map),
        MappingProxyType(
            {identifier: MappingProxyType({}) for identifier in algorithm_map}
        ),
        MappingProxyType({contract.identity: contract}),
    )


_FIXTURE_CACHE: dict[str, Fixture] = {}


def fixture(name: str = "integrated-baseline") -> Fixture:
    if name in _FIXTURE_CACHE:
        return _FIXTURE_CACHE[name]
    core, modules, algorithms = _build_core(name)
    environment = _environment(core, modules, algorithms)
    candidate = make_candidate(core, environment.profile_id)
    protocol_candidate = b2c0.make_protocol_candidate(
        candidate.asserted_id, environment.profile_id
    )
    result = Fixture(
        name,
        environment,
        core,
        candidate,
        protocol_candidate,
        modules,
        algorithms,
    )
    _FIXTURE_CACHE[name] = result
    return result


def fixtures() -> dict[str, Fixture]:
    return {name: fixture(name) for name in SCENARIOS}


def _positions(core: object) -> dict[str, dict[int, int]]:
    rows: dict[str, dict[int, int]] = {
        "challenge": {},
        "check": {},
        "reduction": {},
        "terminal": {},
        "publication": {},
    }
    for occurrence_ref, occurrence in enumerate(core.occurrences):
        effect = occurrence.effect
        if type(effect) is base.ChallengeEffect:
            table, ordinal = "challenge", effect.challenge
        elif type(effect) is base.CheckEffect:
            table, ordinal = "check", effect.check
        elif type(effect) is b3.ApplyReductionEffect:
            table, ordinal = "reduction", effect.reduction
        elif type(effect) is base.TerminalEffect:
            table, ordinal = "terminal", effect.terminal
        elif type(effect) is oracle.PublishOracleEffect:
            table, ordinal = "publication", effect.oracle
        else:
            continue
        if ordinal in rows[table]:
            _fail(
                "Refused",
                "F0V2B2D1-R-BACKLINK",
                f"{table} {ordinal} has more than one occurrence",
            )
        rows[table][ordinal] = occurrence_ref
    expected = {
        "challenge": len(core.challenges),
        "check": len(core.checks),
        "reduction": len(core.reductions),
        "terminal": len(core.terminals),
        "publication": len(core.oracles),
    }
    if any(set(rows[name]) != set(range(count)) for name, count in expected.items()):
        _fail(
            "Refused",
            "F0V2B2D1-R-BACKLINK",
            "declaration-to-occurrence backlinks are not exact and total",
        )
    return rows


def _module_occurrence_semantics(
    core: object, private_sink: bool
) -> Mapping[int, ModuleSemantics]:
    supported = module_semantics(private_sink)
    result: dict[int, ModuleSemantics] = {}
    for occurrence_ref, occurrence in enumerate(core.occurrences):
        effect = occurrence.effect
        if type(effect) is not ModuleEffectRef:
            continue
        ordinal = effect.declaration.local_ordinal
        if (
            effect.module != effect.declaration.module
            or effect.declaration.declaration_kind != "pir.core-effect"
            or not 0 <= ordinal < len(supported)
        ):
            _fail(
                "Refused",
                "F0V2B2D1-R-MODULE-COORDINATE",
                "module occurrence names another owner or declaration",
            )
        semantics = supported[ordinal]
        if len(effect.payload.inputs) != len(semantics.payload_input_types):
            _fail(
                "KindMismatch",
                "F0V2B2D1-K-MODULE-PAYLOAD",
                "module payload arity differs from its owner declaration",
            )
        result[occurrence_ref] = semantics
    return MappingProxyType(result)


def _output_types(
    core: object, module_occurrences: Mapping[int, ModuleSemantics]
) -> tuple[tuple[object, ...], ...]:
    rows: list[tuple[object, ...]] = []
    for occurrence_ref, occurrence in enumerate(core.occurrences):
        effect = occurrence.effect
        if type(effect) in (
            base.ProverMessageEffect,
            foundation.VerifierMessageEffect,
        ):
            rows.append((effect.payload_type,))
        elif type(effect) is base.ChallengeEffect:
            rows.append((core.challenges[effect.challenge].value_type,))
        elif type(effect) is base.CheckEffect:
            rows.append((k1.BOOL,))
        elif type(effect) in (b3.ApplyReductionEffect, base.TerminalEffect):
            rows.append(())
        elif type(effect) is oracle.PublishOracleEffect:
            rows.append(oracle.oracle_publication_types(core.oracles[effect.oracle]))
        elif type(effect) is oracle.QueryOracleEffect:
            rows.append(())
        elif type(effect) is oracle.AnswerOracleEffect:
            if not 0 <= effect.query < occurrence_ref:
                _fail(
                    "Refused",
                    "F0V2B2D1-R-ANSWER-BACKLINK",
                    "Oracle Answer does not name an earlier Query",
                )
            query = core.occurrences[effect.query].effect
            if type(query) is not oracle.QueryOracleEffect:
                _fail(
                    "Refused",
                    "F0V2B2D1-R-ANSWER-BACKLINK",
                    "Oracle Answer backlink does not name a Query",
                )
            rows.append((oracle.oracle_answer_type(core.oracles[query.oracle]),))
        elif type(effect) is ModuleEffectRef:
            rows.append(
                tuple(
                    item.value_type
                    for item in module_occurrences[occurrence_ref].outputs
                )
            )
        else:
            _fail(
                "Unsupported",
                "F0V2B2D1-U-EFFECT",
                "effect lies outside the integrated bounded carrier",
            )
    return tuple(rows)


def _producer_node(reference: object) -> tuple[int, ...]:
    if type(reference) is base.PublicInputRef:
        return 0, reference.ordinal
    if type(reference) is base.VerifierPrivateInputRef:
        return 1, reference.ordinal
    if type(reference) is base.ConstantRef:
        return 2, reference.ordinal
    if type(reference) is base.DerivedValueRef:
        return 3, reference.ordinal
    if type(reference) is base.OccurrenceOutputRef:
        return 8, reference.occurrence, reference.output_ordinal
    _fail("Malformed", "F0V2B2D1-M-VALUE-REF", "ValueRef carrier differs")
    raise AssertionError("unreachable")


def _pc_value(node: tuple[int, ...]) -> dict[str, Any]:
    tag, *arguments = node
    if tag in (8, 12, 13):
        if len(arguments) != 2:
            _fail("CheckerFailure", "F0V2B2D1-C-PCNODE", "PCNode arity differs")
        return foundation._v(
            tag,
            {
                0: foundation._ordinal("occurrence-ref-body-v0", arguments[0]),
                1: arguments[1],
            },
        )
    compiler = {
        0: "public-input-ref-body-v0",
        1: "verifier-private-input-ref-body-v0",
        2: "constant-ref-body-v0",
        3: "derived-value-ref-body-v0",
        4: "scope-ref-body-v0",
        5: "binding-ref-body-v0",
        6: "occurrence-ref-body-v0",
        7: "occurrence-ref-body-v0",
        9: "claim-ref-body-v0",
        10: "reduction-ref-body-v0",
        11: "terminal-ref-body-v0",
    }.get(tag)
    if compiler is None or len(arguments) != 1:
        _fail("CheckerFailure", "F0V2B2D1-C-PCNODE", "PCNode tag or arity differs")
    return foundation._v(tag, foundation._ordinal(compiler, arguments[0]))


def _pc_key(node: tuple[int, ...]) -> bytes:
    return codec.encode_value(_PC_NODE_SCHEMA, _pc_value(node))


def _edge_value(
    edge: tuple[tuple[int, ...], tuple[int, ...]],
) -> dict[int, Any]:
    return {0: _pc_value(edge[0]), 1: _pc_value(edge[1])}


def _edge_key(edge: tuple[tuple[int, ...], tuple[int, ...]]) -> bytes:
    return codec.encode_value(_PC_EDGE_SCHEMA, _edge_value(edge))


def _join(values: list[int]) -> int:
    for value in (3, 2, 1):
        if value in values:
            return value
    return 0


def _publish(value: int) -> int:
    return 1 if value in (0, 1) else value


def _module_dependency_node(
    effect: ModuleEffectRef,
    dependency: ModuleDependency,
    occurrence_ref: int,
) -> tuple[int, ...]:
    if dependency.kind is ModuleDependencyKind.ACTIVITY:
        return 6, occurrence_ref
    if dependency.kind is ModuleDependencyKind.EFFECT:
        return 7, occurrence_ref
    if dependency.ordinal is None:
        _fail(
            "CheckerFailure",
            "F0V2B2D1-C-MODULE-DEPENDENCY",
            "indexed module dependency has no ordinal",
        )
    if dependency.kind is ModuleDependencyKind.PAYLOAD_INPUT:
        if not 0 <= dependency.ordinal < len(effect.payload.inputs):
            _fail(
                "Refused",
                "F0V2B2D1-R-MODULE-DEPENDENCY",
                "module dependency names an absent payload input",
            )
        return _producer_node(effect.payload.inputs[dependency.ordinal])
    return 13, occurrence_ref, dependency.ordinal


def _descendants(
    source: tuple[int, ...],
    outgoing: Mapping[tuple[int, ...], set[tuple[int, ...]]],
) -> set[tuple[int, ...]]:
    seen = {source}
    pending = [source]
    while pending:
        current = pending.pop()
        for child in outgoing[current]:
            if child not in seen:
                seen.add(child)
                pending.append(child)
    return seen


def derive_graph(core: object, scenario: str) -> tuple[dict[int, Any], GraphEvidence]:
    """Derive the exact complete PCGraph and all eligibility side tables."""

    private_sink = scenario == "invalid-module-control-sink"
    module_occurrences = _module_occurrence_semantics(core, private_sink)
    outputs = _output_types(core, module_occurrences)
    positions = _positions(core)
    incoming: dict[tuple[int, ...], set[tuple[int, ...]]] = {}
    outgoing: dict[tuple[int, ...], set[tuple[int, ...]]] = {}

    def node(value: tuple[int, ...]) -> tuple[int, ...]:
        incoming.setdefault(value, set())
        outgoing.setdefault(value, set())
        return value

    def edge(source: tuple[int, ...], target: tuple[int, ...]) -> None:
        source, target = node(source), node(target)
        incoming[target].add(source)
        outgoing[source].add(target)

    for ordinal in range(len(core.public_inputs)):
        node((0, ordinal))
    for ordinal in range(len(core.verifier_private_inputs)):
        node((1, ordinal))
    for ordinal in range(len(core.constants)):
        node((2, ordinal))
    for ordinal, derived in enumerate(core.derived_values):
        target = node((3, ordinal))
        for reference in derived.inputs:
            edge(_producer_node(reference), target)
    for ordinal, scope in enumerate(core.scopes):
        target = node((4, ordinal))
        if scope.parent is not None:
            edge((4, scope.parent), target)
    for ordinal, binding in enumerate(core.public_bindings):
        edge((4, binding.scope), (5, ordinal))
        edge(_producer_node(binding.value), (5, ordinal))

    module_outputs: dict[tuple[int, ...], ModuleOutputSpec] = {}
    module_controls: dict[tuple[int, ...], ModuleControlSpec] = {}
    earlier_terminals: list[tuple[int, ...]] = []
    for occurrence_ref, occurrence in enumerate(core.occurrences):
        activity = node((6, occurrence_ref))
        effect_node = node((7, occurrence_ref))
        edge((4, occurrence.scope), activity)
        if type(occurrence.guard) is base.EvaluateGuard:
            for reference in occurrence.guard.inputs:
                edge(_producer_node(reference), activity)
        for terminal in earlier_terminals:
            edge(terminal, activity)
        edge(activity, effect_node)
        effect = occurrence.effect
        if type(effect) is foundation.VerifierMessageEffect:
            for reference in effect.inputs:
                edge(_producer_node(reference), effect_node)
        elif type(effect) is base.ChallengeEffect:
            challenge = core.challenges[effect.challenge]
            for condition in challenge.public_conditions:
                edge(_producer_node(condition), effect_node)
            if type(challenge.correlation) is base.JointCorrelation:
                for prior_member in challenge.correlation.prior_members:
                    edge((8, positions["challenge"][prior_member], 0), effect_node)
        elif type(effect) is base.CheckEffect:
            for reference in core.checks[effect.check].inputs:
                edge(_producer_node(reference), effect_node)
        elif type(effect) is b3.ApplyReductionEffect:
            reduction = core.reductions[effect.reduction]
            for claim_ref in reduction.input_claims:
                edge((9, claim_ref), effect_node)
            for reference in reduction.side_inputs:
                edge(_producer_node(reference), effect_node)
            for challenge_ref in reduction.required_challenges:
                edge((8, positions["challenge"][challenge_ref], 0), effect_node)
            for requirement in reduction.required_publications:
                edge((7, requirement.publication), effect_node)
            edge(effect_node, (10, effect.reduction))
        elif type(effect) is base.TerminalEffect:
            terminal = core.terminals[effect.terminal]
            for reference in terminal.public_outputs:
                edge(_producer_node(reference), effect_node)
            for check_ref in terminal.required_true_checks:
                edge((8, positions["check"][check_ref], 0), effect_node)
            for reduction_ref in terminal.required_applied_reductions:
                edge((10, reduction_ref), effect_node)
            for claim_ref in terminal.terminal_claims:
                edge((9, claim_ref), effect_node)
            terminal_node = node((11, effect.terminal))
            edge(effect_node, terminal_node)
            earlier_terminals.append(terminal_node)
        elif type(effect) is oracle.QueryOracleEffect:
            edge((7, positions["publication"][effect.oracle]), effect_node)
            edge(_producer_node(effect.index), effect_node)
        elif type(effect) is oracle.AnswerOracleEffect:
            query = core.occurrences[effect.query].effect
            if type(query) is not oracle.QueryOracleEffect:
                _fail(
                    "Refused",
                    "F0V2B2D1-R-ANSWER-BACKLINK",
                    "Oracle Answer backlink does not name a Query",
                )
            edge((7, effect.query), effect_node)
            edge((7, positions["publication"][query.oracle]), effect_node)
        elif type(effect) is ModuleEffectRef:
            semantics = module_occurrences[occurrence_ref]
            for control_ordinal, control in enumerate(semantics.controls):
                control_node = node((12, occurrence_ref, control_ordinal))
                module_controls[control_node] = control
                for dependency in control.dependencies:
                    edge(
                        _module_dependency_node(effect, dependency, occurrence_ref),
                        control_node,
                    )
            for output_ordinal, output in enumerate(semantics.outputs):
                output_node = node((13, occurrence_ref, output_ordinal))
                module_outputs[output_node] = output
                for dependency in output.dependencies:
                    edge(
                        _module_dependency_node(effect, dependency, occurrence_ref),
                        output_node,
                    )
                edge(output_node, (8, occurrence_ref, output_ordinal))
        for output_ordinal in range(len(outputs[occurrence_ref])):
            edge(effect_node, (8, occurrence_ref, output_ordinal))

    for claim_ref, claim in enumerate(core.claims):
        if type(claim.source) is b3.InitialClaimSource:
            edge((5, claim.source.binding), (9, claim_ref))
        else:
            edge((10, claim.source.reduction), (9, claim_ref))

    indegree = {item: len(parents) for item, parents in incoming.items()}
    heap = [(_pc_key(item), item) for item, count in indegree.items() if count == 0]
    heapq.heapify(heap)
    topological: list[tuple[int, ...]] = []
    while heap:
        _encoded, current = heapq.heappop(heap)
        topological.append(current)
        for child in outgoing[current]:
            indegree[child] -= 1
            if indegree[child] == 0:
                heapq.heappush(heap, (_pc_key(child), child))
    if len(topological) != len(incoming):
        _fail("Refused", "F0V2B2D1-R-PCGRAPH-CYCLE", "integrated PCGraph is cyclic")

    classes: dict[tuple[int, ...], int] = {}
    challenge_validity: dict[int, bool] = {}
    for current in topological:
        tag = current[0]
        joined = _join([classes[item] for item in incoming[current]])
        if tag in (0, 2):
            value = 0
        elif tag == 1:
            value = 2
        elif current in module_outputs:
            transfer = module_outputs[current].transfer
            if transfer is ModuleOutputTransfer.DETERMINISTIC:
                value = joined
            elif transfer is ModuleOutputTransfer.PROVER_PUBLICATION:
                value = _publish(joined)
            else:
                value = 3
        elif tag == 7:
            effect = core.occurrences[current[1]].effect
            if (
                type(effect) is oracle.PublishOracleEffect
                and type(core.oracles[effect.oracle].publication_mode)
                is oracle.LogicalAccessOracle
            ):
                value = _publish(classes[(6, current[1])])
            elif type(effect) is oracle.QueryOracleEffect:
                value = (
                    2
                    if effect.visibility is oracle.OracleVisibility.VERIFIER_ONLY
                    else _join(
                        [
                            classes[(6, current[1])],
                            classes[_producer_node(effect.index)],
                        ]
                    )
                )
            elif type(effect) is oracle.AnswerOracleEffect:
                query = core.occurrences[effect.query].effect
                value = (
                    2
                    if query.visibility is oracle.OracleVisibility.VERIFIER_ONLY
                    else joined
                )
            else:
                value = joined
        elif tag == 8:
            effect = core.occurrences[current[1]].effect
            activity_class = classes[(6, current[1])]
            if type(effect) is base.ProverMessageEffect:
                value = _publish(activity_class)
            elif type(effect) is foundation.VerifierMessageEffect:
                value = _join(
                    [activity_class]
                    + [classes[_producer_node(item)] for item in effect.inputs]
                )
            elif type(effect) is base.ChallengeEffect:
                challenge = core.challenges[effect.challenge]
                condition_classes = [
                    classes[_producer_node(item)]
                    for item in challenge.public_conditions
                ]
                prior_classes = (
                    [
                        classes[(8, positions["challenge"][item], 0)]
                        for item in challenge.correlation.prior_members
                    ]
                    if type(challenge.correlation) is base.JointCorrelation
                    else []
                )
                dependencies = [activity_class, *condition_classes, *prior_classes]
                if 3 in dependencies:
                    value = 3
                elif 2 in dependencies:
                    value = 2
                elif any(item != 0 for item in condition_classes) or any(
                    item != 1 for item in prior_classes
                ):
                    value = 3
                elif activity_class in (0, 1):
                    value = 1
                else:  # pragma: no cover - lattice is closed above
                    value = 3
                challenge_validity[effect.challenge] = value == 1
            elif type(effect) is oracle.PublishOracleEffect:
                value = _publish(activity_class)
            elif type(effect) is oracle.AnswerOracleEffect:
                query = core.occurrences[effect.query].effect
                value = (
                    2
                    if query.visibility is oracle.OracleVisibility.VERIFIER_ONLY
                    else _publish(activity_class)
                )
            else:
                value = joined
        else:
            value = joined
        classes[current] = value

    binding_sinks = {(5, index) for index in range(len(core.public_bindings))}
    public_observations: set[tuple[int, ...]] = set(binding_sinks)
    observation_activities: set[tuple[int, ...]] = set()
    challenge_condition_sinks: set[tuple[int, ...]] = set()
    challenge_sinks: set[tuple[int, ...]] = set()
    check_sinks: set[tuple[int, ...]] = set()
    for occurrence_ref, occurrence in enumerate(core.occurrences):
        effect = occurrence.effect
        observed: set[tuple[int, ...]] = set()
        if type(effect) in (
            base.ProverMessageEffect,
            foundation.VerifierMessageEffect,
        ):
            observed.update(
                (8, occurrence_ref, output)
                for output in range(len(outputs[occurrence_ref]))
            )
        elif type(effect) is base.ChallengeEffect:
            observed.add((8, occurrence_ref, 0))
            challenge_sinks.add((8, occurrence_ref, 0))
            challenge_condition_sinks.update(
                _producer_node(item)
                for item in core.challenges[effect.challenge].public_conditions
            )
        elif type(effect) is base.CheckEffect:
            check_sinks.add((7, occurrence_ref))
        elif type(effect) is oracle.PublishOracleEffect:
            mode = core.oracles[effect.oracle].publication_mode
            if type(mode) is oracle.LogicalAccessOracle:
                observed.add((7, occurrence_ref))
            else:
                observed.update(
                    (8, occurrence_ref, output)
                    for output in range(len(outputs[occurrence_ref]))
                )
        elif type(effect) is oracle.QueryOracleEffect:
            if effect.visibility is oracle.OracleVisibility.PUBLIC:
                observed.add((7, occurrence_ref))
                public_observations.add(_producer_node(effect.index))
        elif type(effect) is oracle.AnswerOracleEffect:
            query = core.occurrences[effect.query].effect
            if query.visibility is oracle.OracleVisibility.PUBLIC:
                observed.add((8, occurrence_ref, 0))
        elif type(effect) is ModuleEffectRef:
            semantics = module_occurrences[occurrence_ref]
            for output_ordinal, output in enumerate(semantics.outputs):
                if output.visibility is ModuleVisibility.PUBLIC:
                    observed.update(
                        (
                            (13, occurrence_ref, output_ordinal),
                            (8, occurrence_ref, output_ordinal),
                        )
                    )
        if observed:
            public_observations.update(observed)
            observation_activities.add((6, occurrence_ref))

    reduction_sinks = {(10, index) for index in range(len(core.reductions))}
    terminal_sinks = {(11, index) for index in range(len(core.terminals))}
    terminal_outputs = {
        _producer_node(reference)
        for terminal in core.terminals
        for reference in terminal.public_outputs
    }
    acceptance_module = {
        node
        for node, spec in (*module_outputs.items(), *module_controls.items())
        if spec.acceptance_relevant
    }
    sinks = (
        public_observations
        | observation_activities
        | challenge_condition_sinks
        | challenge_sinks
        | check_sinks
        | reduction_sinks
        | terminal_sinks
        | terminal_outputs
        | acceptance_module
    )
    accepting_terminals = {
        (11, index)
        for index, terminal in enumerate(core.terminals)
        if terminal.verdict is base.TerminalVerdict.ACCEPT
    }
    accepting_outputs = {
        _producer_node(reference)
        for index, terminal in enumerate(core.terminals)
        if (11, index) in accepting_terminals
        for reference in terminal.public_outputs
    }
    acceptance = (
        check_sinks
        | reduction_sinks
        | accepting_terminals
        | accepting_outputs
        | acceptance_module
    )

    private_predecessors = tuple(
        sorted(
            (
                source
                for source in (
                    (1, index) for index in range(len(core.verifier_private_inputs))
                )
                if _descendants(source, outgoing) & sinks
            ),
            key=_pc_key,
        )
    )
    logical_cones: dict[int, tuple[tuple[int, ...], ...]] = {}
    logical_intersections: dict[int, tuple[tuple[int, ...], ...]] = {}
    for oracle_ref, declaration in enumerate(core.oracles):
        if type(declaration.publication_mode) is not oracle.LogicalAccessOracle:
            continue
        cone = _descendants((7, positions["publication"][oracle_ref]), outgoing)
        intersection = cone & acceptance
        logical_cones[oracle_ref] = tuple(sorted(cone, key=_pc_key))
        logical_intersections[oracle_ref] = tuple(sorted(intersection, key=_pc_key))

    decision_occurrences = {
        index
        for index, occurrence in enumerate(core.occurrences)
        if type(occurrence.effect) is base.ProverMessageEffect
        or (
            type(occurrence.effect) is oracle.PublishOracleEffect
            and core.oracles[occurrence.effect.oracle].origin
            is oracle.OracleOrigin.PROVER
        )
        or (
            index in module_occurrences
            and module_occurrences[index].decision_class
            is not ModuleDecisionClass.NO_PROVER_DECISION
        )
    }
    challenge_order: dict[int, bool] = {}
    for challenge_ref, occurrence_ref in positions["challenge"].items():
        output_node = (8, occurrence_ref, 0)
        dependent_decisions = {
            decision
            for decision in decision_occurrences
            if (6, decision) in _descendants(output_node, outgoing)
            or (7, decision) in _descendants(output_node, outgoing)
        }
        challenge_order[challenge_ref] = all(
            occurrence_ref < decision for decision in dependent_decisions
        )

    ordered_nodes = tuple(sorted(incoming, key=_pc_key))
    ordered_edges = tuple(
        sorted(
            (
                (source, target)
                for target, parents in incoming.items()
                for source in parents
            ),
            key=_edge_key,
        )
    )
    ordered_sinks = tuple(sorted(sinks, key=_pc_key))
    ordered_acceptance = tuple(sorted(acceptance, key=_pc_key))
    eligible = (
        all(classes[item] in (0, 1) for item in ordered_sinks)
        and all(
            challenge_validity.get(index, False)
            for index in range(len(core.challenges))
        )
        and all(challenge_order.values())
        and not any(logical_intersections.values())
    )
    graph = {
        0: [_pc_value(item) for item in ordered_nodes],
        1: [_edge_value(item) for item in ordered_edges],
        2: [_pc_value(item) for item in topological],
        3: [
            {0: _pc_value(item), 1: foundation._v(classes[item])}
            for item in ordered_nodes
        ],
        4: [_pc_value(item) for item in ordered_sinks],
        5: [_pc_value(item) for item in ordered_acceptance],
        6: [
            {
                0: foundation._ordinal("oracle-ref-body-v0", oracle_ref),
                1: [_pc_value(item) for item in logical_cones[oracle_ref]],
                2: [_pc_value(item) for item in logical_intersections[oracle_ref]],
            }
            for oracle_ref in sorted(logical_cones)
        ],
    }
    evidence = GraphEvidence(
        ordered_nodes,
        ordered_edges,
        tuple(topological),
        MappingProxyType(classes),
        ordered_sinks,
        ordered_acceptance,
        private_predecessors,
        MappingProxyType(logical_cones),
        MappingProxyType(logical_intersections),
        MappingProxyType(challenge_validity),
        MappingProxyType(challenge_order),
        eligible,
    )
    return graph, evidence


def _scenario_for_domain(domain_body: bytes) -> str:
    matches = [
        name
        for name in SCENARIOS
        if k1.encode_datum(core_domain_datum(fixture(name).core)) == domain_body
    ]
    if len(matches) != 1:
        _fail(
            "Refused",
            "F0V2B2D1-R-BOUNDED-CARRIER",
            "Core is outside the five exact integrated D1 carriers",
        )
    return matches[0]


def _authenticate_environment(core: object, scenario: str, environment: object) -> None:
    expected = fixture(scenario)
    if environment.profile_id != candidate_profile_artifact().profile_id:
        _fail(
            "KindMismatch",
            "F0V2B2D1-K-TARGET-PROFILE",
            "evaluator accepts only the exact synthetic Interaction revision 2",
        )
    if set(environment.profile_preimages) != {environment.profile_id}:
        _fail(
            "Refused",
            "F0V2B2D1-R-PROFILE-CLOSURE",
            "profile preimage closure is not exact",
        )
    if set(environment.module_preimages) != set(core.used_modules):
        _fail(
            "Refused",
            "F0V2B2D1-R-MODULE-CLOSURE",
            "module preimage closure differs from exact used_modules",
        )
    for identifier, module in environment.module_preimages.items():
        if module.identity != identifier:
            _fail(
                "Refused",
                "F0V2B2D1-R-MODULE-ID",
                "semantic module body differs from its content reference",
            )
    expected_modules = {item.identity: item.body() for item in expected.modules}
    observed_modules = {
        identifier: module.body()
        for identifier, module in environment.module_preimages.items()
    }
    if observed_modules != expected_modules:
        _fail(
            "Unsupported",
            "F0V2B2D1-U-MODULE-SUPPORT",
            "module declaration closure lies outside bounded D1 support",
        )
    algorithm_refs, contract_refs = _ordinary_references(core)
    if (
        set(environment.algorithm_preimages) != set(algorithm_refs)
        or set(environment.algorithm_modules) != set(algorithm_refs)
        or set(environment.contract_preimages) != set(contract_refs)
    ):
        _fail(
            "Refused",
            "F0V2B2D1-R-ALGORITHM-CLOSURE",
            "algorithm or evaluation-contract closure is not exact",
        )
    ledger = k1.AuthenticationLedger()
    try:
        for identifier in algorithm_refs:
            algorithm = environment.algorithm_preimages[identifier]
            if (
                k1.authenticate_algorithm_identity(algorithm, ledger=ledger)
                != identifier
            ):
                _fail(
                    "Refused",
                    "F0V2B2D1-R-ALGORITHM-ID",
                    "algorithm preimage differs from its exact reference",
                )
            modules = environment.algorithm_modules[identifier]
            k1.authenticate_module_closure(
                k1.direct_module_dependencies(algorithm, ledger=ledger),
                dict(modules),
                semantic_regime=k1.SEMANTIC_REGIME_ID,
                ledger=ledger,
            )
            k1.authenticate_algorithm_declaration_references(
                algorithm, dict(modules), ledger=ledger
            )
        for identifier in contract_refs:
            contract = environment.contract_preimages[identifier]
            if contract.identity != identifier:
                _fail(
                    "Refused",
                    "F0V2B2D1-R-CONTRACT-ID",
                    "evaluation contract differs from its exact reference",
                )
            k1.authenticate_content_id(
                identifier,
                contract.body(),
                environment.prior_meta_preimages,
                ledger=ledger,
            )
    except IntegratedFailure:
        raise
    except Exception as error:
        outcome = getattr(getattr(error, "outcome", None), "value", None)
        _fail(outcome or "Refused", "F0V2B2D1-R-DEPENDENCY", str(error))


def _validate_integrated_shape(core: object, scenario: str) -> GraphEvidence:
    expected = fixture(scenario).core
    if core != expected:
        _fail(
            "Refused",
            "F0V2B2D1-R-BOUNDED-CARRIER",
            "decoded Core differs from its exact admitted D1 carrier",
        )
    if (
        len(core.public_inputs) != 4
        or len(core.verifier_private_inputs) != 1
        or len(core.constants) != 2
        or len(core.derived_values) != 3
        or len(core.scopes) != 2
        or len(core.public_bindings) != 5
        or len(core.challenges) != 3
        or len(core.oracles) != 3
        or len(core.checks) != 1
        or len(core.claims) != 3
        or len(core.reductions) != 2
        or len(core.terminals) != 3
        or len(core.occurrences) != 23
    ):
        _fail(
            "CheckerFailure",
            "F0V2B2D1-C-CARRIER-CENSUS",
            "recognized integrated carrier has an impossible table census",
        )
    _graph, evidence = derive_graph(core, scenario)
    if {node[0] for node in evidence.nodes} != set(range(14)):
        _fail(
            "CheckerFailure",
            "F0V2B2D1-C-PCNODE-COVERAGE",
            "integrated graph does not inhabit all fourteen PCNode cases",
        )
    if set(evidence.classes.values()) != {0, 1, 2, 3}:
        _fail(
            "CheckerFailure",
            "F0V2B2D1-C-PCCLASS-COVERAGE",
            "integrated graph does not inhabit all four PCClass cases",
        )
    return evidence


def admit_core(candidate: object, environment: object) -> AdmissionResult:
    try:
        if type(candidate) is not b2c0.CanonicalCoreCandidate:
            _fail("Malformed", "F0V2B2D1-M-REQUEST", "Core request is malformed")
        if type(environment) is not base.Environment:
            _fail("Malformed", "F0V2B2D1-M-ENVIRONMENT", "environment is malformed")
        if candidate.profile_id != environment.profile_id:
            _fail(
                "KindMismatch",
                "F0V2B2D1-K-REQUEST-PROFILE",
                "candidate and environment profile coordinates differ",
            )
        profile, domain, domain_body = b2c0._strict_profiled_body(
            candidate.profiled_body, "F0-V2B2D1 integrated Core"
        )
        if profile != candidate.profile_id:
            _fail(
                "KindMismatch",
                "F0V2B2D1-K-BODY-PROFILE",
                "Core body and request profile coordinates differ",
            )
        if (
            type(candidate.asserted_id) is not k1.TypedContentId
            or candidate.asserted_id.subject_kind != base.TARGET_CORE_KIND
        ):
            _fail("KindMismatch", "F0V2B2D1-K-CORE-ID", "Core ID kind differs")
        try:
            k1.authenticate_content_id(
                candidate.asserted_id,
                candidate.profiled_body,
                environment.prior_meta_preimages,
            )
        except Exception as error:
            _fail("Malformed", "F0V2B2D1-M-CORE-ID", str(error))
        scenario = _scenario_for_domain(domain_body)
        core = decode_core(domain)
        if k1.encode_datum(core_domain_datum(core)) != domain_body:
            _fail(
                "Malformed",
                "F0V2B2D1-M-CORE-ROUNDTRIP",
                "decoded Core does not round-trip to exact canonical bytes",
            )
        _authenticate_environment(core, scenario, environment)
        evidence = _validate_integrated_shape(core, scenario)
        closure = b2c0.snapshot_environment(environment)
        summary = (
            ("stage", "F0-V2B2D1"),
            ("scenario", scenario),
            ("nodes", len(evidence.nodes)),
            ("edges", len(evidence.edges)),
            ("eligible", evidence.eligible),
        )
        handle = b2c0.AdmittedCoreSnapshot(
            candidate.asserted_id.internal_reference(),
            candidate.profile_id.internal_reference(),
            bytes(candidate.profiled_body),
            bytes(domain_body),
            closure,
            summary,
            EVALUATOR_FINGERPRINT,
            tuple(range(1, 11)),
            b2c0._CORE_ISSUER,
        )
        return AdmissionResult(
            "Affirmative",
            "F0V2B2D1-A-CORE-ADMITTED",
            "exact bytes passed the finite integrated D1 carrier gate",
            handle,
        )
    except IntegratedFailure as error:
        return AdmissionResult(error.outcome, error.code, error.detail)
    except b2c0.SnapshotFailure as error:
        return AdmissionResult(error.outcome, error.code, error.detail)
    except Exception as error:  # pragma: no cover - fail-closed defect lane
        return AdmissionResult("CheckerFailure", "F0V2B2D1-CHECKER", str(error))


def admit_fresh_protocol(
    core_handle: object, candidate: object, environment: object
) -> AdmissionResult:
    try:
        if (
            type(core_handle) is not b2c0.AdmittedCoreSnapshot
            or not core_handle._issued_by(b2c0._CORE_ISSUER)
            or core_handle.evaluator_fingerprint != EVALUATOR_FINGERPRINT
        ):
            _fail(
                "Refused",
                "F0V2B2D1-R-CORE-AUTHORITY",
                "Fresh Protocol request has no exact D1 Core authority",
            )
        if type(candidate) is not b2c0.CanonicalFreshProtocolCandidate:
            _fail(
                "Malformed",
                "F0V2B2D1-M-PROTOCOL-REQUEST",
                "Fresh Protocol request is malformed",
            )
        if type(environment) is not base.Environment:
            _fail("Malformed", "F0V2B2D1-M-ENVIRONMENT", "environment is malformed")
        if (
            candidate.profile_id != environment.profile_id
            or candidate.profile_id.internal_reference()
            != core_handle.profile_reference
        ):
            _fail(
                "KindMismatch",
                "F0V2B2D1-K-PROTOCOL-PROFILE",
                "Fresh Protocol and Core profiles differ",
            )
        profile, domain, _domain_body = b2c0._strict_profiled_body(
            candidate.profiled_body, "F0-V2B2D1 Fresh Protocol"
        )
        if profile != candidate.profile_id:
            _fail(
                "KindMismatch",
                "F0V2B2D1-K-PROTOCOL-BODY-PROFILE",
                "Fresh Protocol body profile differs",
            )
        fields = b2c0._record(domain, (0, 1), "Fresh Protocol")
        core_reference = b2c0._content_ref(fields[0], "Fresh Protocol Core")
        interpretation, payload = b2c0._variant(fields[1], (0,), "Fresh interpretation")
        if interpretation != 0:
            _fail(
                "KindMismatch",
                "F0V2B2D1-K-INTERPRETATION",
                "Protocol does not select Fresh interpretation",
            )
        b2c0._unit(payload, "Fresh interpretation payload")
        if core_reference.internal_reference() != core_handle.core_reference:
            _fail(
                "Refused",
                "F0V2B2D1-R-PROTOCOL-CORE",
                "Fresh Protocol names another Core",
            )
        if (
            type(candidate.asserted_id) is not k1.TypedContentId
            or candidate.asserted_id.subject_kind != base.TARGET_PROTOCOL_KIND
        ):
            _fail(
                "KindMismatch",
                "F0V2B2D1-K-PROTOCOL-ID",
                "Fresh Protocol ID kind differs",
            )
        try:
            k1.authenticate_content_id(
                candidate.asserted_id,
                candidate.profiled_body,
                environment.prior_meta_preimages,
            )
        except Exception as error:
            _fail("Malformed", "F0V2B2D1-M-PROTOCOL-ID", str(error))
        closure = b2c0.snapshot_environment(environment)
        if closure.fingerprint != core_handle.closure.fingerprint:
            _fail(
                "Refused",
                "F0V2B2D1-R-PROTOCOL-CLOSURE",
                "Fresh Protocol closure differs from admitted Core closure",
            )
        handle = b2c0.AdmittedFreshProtocolSnapshot(
            candidate.asserted_id.internal_reference(),
            candidate.profile_id.internal_reference(),
            bytes(candidate.profiled_body),
            core_handle,
            closure.fingerprint,
            EVALUATOR_FINGERPRINT,
            b2c0._PROTOCOL_ISSUER,
        )
        return AdmissionResult(
            "Affirmative",
            "F0V2B2D1-A-FRESH-ADMITTED",
            "Fresh Protocol is paired to the exact integrated Core authority",
            handle,
        )
    except IntegratedFailure as error:
        return AdmissionResult(error.outcome, error.code, error.detail)
    except b2c0.SnapshotFailure as error:
        return AdmissionResult(error.outcome, error.code, error.detail)
    except Exception as error:  # pragma: no cover - fail-closed defect lane
        return AdmissionResult("CheckerFailure", "F0V2B2D1-CHECKER", str(error))


def _retained_core(handle: object) -> tuple[object, str]:
    if (
        type(handle) is not b2c0.AdmittedCoreSnapshot
        or not handle._issued_by(b2c0._CORE_ISSUER)
        or handle.evaluator_fingerprint != EVALUATOR_FINGERPRINT
        or handle.profile_reference
        != candidate_profile_artifact().profile_id.internal_reference()
        or handle.admission_steps != tuple(range(1, 11))
    ):
        _fail(
            "Refused",
            "F0V2B2D1-R-CORE-AUTHORITY",
            "Core authority is absent, stale, or from another evaluator",
        )
    try:
        domain = k1.decode_datum(handle.domain_body)
    except Exception as error:
        _fail("Malformed", "F0V2B2D1-M-RETAINED-CORE", str(error))
    scenario = _scenario_for_domain(handle.domain_body)
    core = decode_core(domain)
    _validate_integrated_shape(core, scenario)
    return core, scenario


def _correlation_value(value: object) -> dict[str, Any]:
    if type(value) is base.IndependentCorrelation:
        return foundation._v(0)
    return foundation._v(
        1,
        {
            0: foundation._module_ref(value.group),
            1: value.index,
            2: [
                foundation._ordinal("challenge-ref-body-v0", item)
                for item in value.prior_members
            ],
        },
    )


def _reduction_use_value(value: object) -> dict[str, Any]:
    if type(value) is base.ExclusiveReductionUse:
        return foundation._v(0)
    return foundation._v(1, foundation._module_ref(value.contract))


def _backward_closure(
    source: tuple[int, ...],
    edges: tuple[tuple[tuple[int, ...], tuple[int, ...]], ...],
) -> set[tuple[int, ...]]:
    incoming: dict[tuple[int, ...], set[tuple[int, ...]]] = {}
    for parent, child in edges:
        incoming.setdefault(child, set()).add(parent)
        incoming.setdefault(parent, set())
    seen = {source}
    pending = [source]
    while pending:
        current = pending.pop()
        for parent in incoming.get(current, set()):
            if parent not in seen:
                seen.add(parent)
                pending.append(parent)
    return seen


def project_public_coin(handle: object) -> tuple[dict[int, Any], GraphEvidence]:
    core, scenario = _retained_core(handle)
    graph, evidence = derive_graph(core, scenario)
    identifier = k1.decode_content_reference(handle.core_reference)
    positions = _positions(core)
    consumers: dict[int, list[int]] = {
        index: [] for index in range(len(core.challenges))
    }
    for reduction_ref, reduction in enumerate(core.reductions):
        for challenge_ref in reduction.required_challenges:
            consumers[challenge_ref].append(reduction_ref)
    challenge_rows: list[dict[int, Any]] = []
    for challenge_ref, challenge in enumerate(core.challenges):
        closure = {
            node
            for condition in challenge.public_conditions
            for node in _backward_closure(_producer_node(condition), evidence.edges)
        }
        challenge_rows.append(
            {
                0: foundation._ordinal("challenge-ref-body-v0", challenge_ref),
                1: foundation._ordinal(
                    "occurrence-ref-body-v0", positions["challenge"][challenge_ref]
                ),
                2: foundation._ordinal("scope-ref-body-v0", challenge.scope),
                3: foundation._value_type_body(challenge.value_type),
                4: foundation._module_ref(challenge.domain),
                5: foundation._module_ref(challenge.fresh_law),
                6: _correlation_value(challenge.correlation),
                7: _reduction_use_value(challenge.reduction_use),
                8: [
                    foundation._value_ref(item) for item in challenge.public_conditions
                ],
                9: [_pc_value(item) for item in sorted(closure, key=_pc_key)],
                10: [
                    {
                        0: foundation._ordinal("reduction-ref-body-v0", reduction_ref),
                        1: foundation._ordinal("challenge-ref-body-v0", challenge_ref),
                    }
                    for reduction_ref in consumers[challenge_ref]
                ],
            }
        )
    value = {
        0: foundation._identifier("core-id-body-v0", identifier),
        1: graph,
        2: evidence.eligible,
        3: [_pc_value(item) for item in evidence.private_predecessors],
        4: challenge_rows,
    }
    codec.encode_value(VIEW_SCHEMAS["PublicCoinView"], value)
    return value, evidence


def public_coin_body(handle: object) -> bytes:
    value, _evidence = project_public_coin(handle)
    return codec.encode_value(VIEW_SCHEMAS["PublicCoinView"], value)


def admit_public_coin_claim(handle: object, claimed_body: bytes) -> AdmissionResult:
    try:
        if type(claimed_body) is not bytes:
            _fail(
                "Malformed",
                "F0V2B2D1-M-PUBLIC-COIN-CLAIM",
                "claimed PublicCoinView body is not exact bytes",
            )
        expected = public_coin_body(handle)
        if claimed_body != expected:
            _fail(
                "Refused",
                "F0V2B2D1-R-PUBLIC-COIN-SUBSTITUTION",
                "claimed graph differs from the exact owner-derived view",
            )
        return AdmissionResult(
            "Affirmative",
            "F0V2B2D1-A-PUBLIC-COIN-CLAIM",
            "claimed PublicCoinView is the exact owner-derived body",
        )
    except IntegratedFailure as error:
        return AdmissionResult(error.outcome, error.code, error.detail)
    except Exception as error:  # pragma: no cover - fail-closed defect lane
        return AdmissionResult("CheckerFailure", "F0V2B2D1-CHECKER", str(error))


def admit_fiat_shamir(handle: object) -> AdmissionResult:
    try:
        _value, evidence = project_public_coin(handle)
        if any(evidence.logical_intersections.values()):
            _fail(
                "Refused",
                "F0V2B2D1-R-LOGICAL-INTERSECTION",
                "logical-access influence reaches an acceptance sink",
            )
        if not evidence.eligible:
            _fail(
                "Refused",
                "F0V2B2D1-R-PUBLIC-COIN",
                "a public-coin sink or Challenge transfer is not public",
            )
        return AdmissionResult(
            "Affirmative",
            "F0V2B2D1-A-FS-STRUCTURAL",
            "bounded Core passes structural public-coin eligibility only",
        )
    except IntegratedFailure as error:
        return AdmissionResult(error.outcome, error.code, error.detail)
    except Exception as error:  # pragma: no cover - fail-closed defect lane
        return AdmissionResult("CheckerFailure", "F0V2B2D1-CHECKER", str(error))


def raw_module_sources(environment: object) -> tuple[tuple[bytes, bytes], ...]:
    return tuple(
        sorted(
            (
                (identifier.internal_reference(), module.body())
                for identifier, module in environment.module_preimages.items()
            ),
            key=lambda item: item[0],
        )
    )


def rebuild(core: object, environment: object) -> object:
    return make_candidate(core, environment.profile_id)
