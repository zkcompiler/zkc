"""Typed owner evaluator for the F0-V2B2C1B4 module-effect slice.

This temporary research model extends the canonical-byte owner substrate over
one exact supported semantic module.  The module preimage, rather than an
ambient callback or asserted classification, fixes payload decoding, decision
class, outputs, observations, dependency edges, reconstruction, influence,
replay, terminal interaction, and work bounds.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
import hashlib
import heapq
import importlib.util
from pathlib import Path
import sys
from types import MappingProxyType, ModuleType
from typing import Any, Mapping


ROOT = Path(__file__).resolve().parents[2]
PREDECESSOR_MODEL = (
    ROOT
    / "evaluation"
    / "formal-source-claim-reduction-owner-projections-f0v2b2c1b3"
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


prior = _load("_zkc_f0v2b2c1b4_predecessor", PREDECESSOR_MODEL)
foundation = prior.foundation
base = prior.base
b2c0 = prior.b2c0
b2b = prior.b2b
codec = prior.codec
k1 = prior.k1
VIEW_SCHEMAS = prior.VIEW_SCHEMAS
_PC_GRAPH_SCHEMA = prior._PC_GRAPH_SCHEMA
_PC_NODE_SCHEMA = prior._PC_NODE_SCHEMA
_PC_EDGE_SCHEMA = prior._PC_EDGE_SCHEMA

EVALUATOR_FINGERPRINT = hashlib.sha256(
    b"zkc-f0-v2b2c1b4-module-owner-evaluator-v0"
).digest()
MAX_LOCAL_ITEMS = 1 << 14
MODULE_DECLARATION_MAGIC = "f0v2b2c1b4.module-effect.v0"


class FamilyFailure(ValueError):
    """Stable fail-closed result from the bounded module evaluator."""

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
class ValidationEvidence:
    outputs: tuple[tuple[object, ...], ...]
    paths: tuple[tuple[int, ...], ...]
    terminal_positions: Mapping[int, int]
    module_semantics: Mapping[int, ModuleSemantics]


def _fail(outcome: str, code: str, detail: str) -> None:
    raise FamilyFailure(outcome, code, detail)


def _record(*values: object) -> object:
    return k1.DatumRecord(tuple((index, value) for index, value in enumerate(values)))


def _seq(values: tuple[object, ...]) -> object:
    return k1.DatumSeq(values)


def _variant(case: int, payload: object = k1.UNIT) -> object:
    return k1.DatumVariant(case, payload)


def _bool_datum(value: bool) -> object:
    return _variant(1 if value else 0)


def _dependency_datum(dependency: ModuleDependency) -> object:
    if dependency.kind in (
        ModuleDependencyKind.ACTIVITY,
        ModuleDependencyKind.EFFECT,
    ):
        if dependency.ordinal is not None:
            raise k1.ModelError("node-local dependency unexpectedly has an ordinal")
        return _variant(dependency.kind.value)
    if type(dependency.ordinal) is not int or dependency.ordinal < 0:
        raise k1.ModelError("indexed module dependency lacks a natural ordinal")
    return _variant(dependency.kind.value, k1.Nat(dependency.ordinal))


def _output_spec_datum(output: ModuleOutputSpec) -> object:
    if output.transfer is ModuleOutputTransfer.DETERMINISTIC:
        if (
            output.reconstruction_algorithm is None
            or output.reconstruction_contract is None
        ):
            raise k1.ModelError("deterministic output lacks reconstruction authority")
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
            raise k1.ModelError(
                "nondeterministic output carries reconstruction authority"
            )
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
        if semantics.move_type is not None:
            raise k1.ModelError("NoProverDecision declaration carries a move type")
        decision = _variant(0)
    else:
        if semantics.move_type is None:
            raise k1.ModelError("module decision declaration lacks a move type")
        decision = _variant(
            semantics.decision_class.value,
            k1.value_type_datum(semantics.move_type),
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
    if type(effect) is ModuleEffectRef:
        return _variant(7, _module_effect_datum(effect))
    if type(effect) is base.TerminalEffect:
        return _variant(5, k1.Nat(effect.terminal))
    raise k1.ModelError("effect belongs to another constructor slice")


def core_domain_datum(core: object) -> object:
    if type(core) is not base.InteractiveCore:
        raise k1.ModelError("Core has another carrier")
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
        _seq(tuple(core.oracles)),
        _seq(tuple(base._check_datum(item) for item in core.checks)),
        _seq(tuple(prior._claim_datum(item) for item in core.claims)),
        _seq(tuple(prior._reduction_datum(item) for item in core.reductions)),
        _seq(tuple(base._terminal_datum(item) for item in core.terminals)),
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
        core_id(core, profile_id),
        profile_id,
        core_profiled_body(core, profile_id),
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
    if case == 5:
        return base.TerminalEffect(b2c0._nat(payload, "terminal backlink"))
    if case == 7:
        module, declaration, effect_payload = b2c0._record(
            payload, (0, 1, 2), "module effect"
        )
        return ModuleEffectRef(
            b2c0._content_ref(module, "module-effect owner"),
            b2c0._decode_module_ref(declaration),
            _decode_module_payload(effect_payload),
        )
    _fail(
        "Unsupported",
        "F0V2B2C1B4-U-EFFECT",
        f"effect tag {case} belongs to another isolation slice",
    )
    raise AssertionError("unreachable")


def _decode_terminal(value: object) -> object:
    verdict, outputs, checks, dispositions = b2c0._record(
        value, (0, 1, 2, 3), "terminal"
    )
    verdict_case, verdict_payload = b2c0._variant(
        verdict, (0, 1, 2), "terminal verdict"
    )
    b2c0._unit(verdict_payload, "terminal verdict payload")
    decoded_outputs = tuple(
        b2c0._decode_value_ref(item)
        for item in b2c0._sequence(outputs, "terminal outputs")
    )
    decoded_checks = b2c0._sequence(checks, "terminal checks")
    decoded_dispositions = b2c0._sequence(dispositions, "terminal dispositions")
    if decoded_checks or decoded_dispositions:
        _fail(
            "Unsupported",
            "F0V2B2C1B4-U-TERMINAL-SLICE",
            "terminal checks and claim dispositions belong to earlier owner slices",
        )
    return base.TerminalDecl(
        base.TerminalVerdict(verdict_case),
        decoded_outputs,
        (),
        (),
    )


def decode_core(domain: object) -> object:
    """Strictly decode the bounded module-effect Core from canonical bytes."""

    fields = b2c0._record(domain, tuple(range(14)), "InteractiveCore")
    tables = tuple(
        b2c0._sequence(value, f"InteractiveCore field {index}")
        for index, value in enumerate(fields)
    )
    if any(tables[index] for index in (2, 3, 4, 7, 8, 9, 10, 11)):
        _fail(
            "Unsupported",
            "F0V2B2C1B4-U-OTHER-SLICE",
            "private, constant, derived, Challenge, Oracle, Check, Claim, and Reduction constructors are outside B2C1B4",
        )
    public_inputs = tuple(
        base.InputDecl(
            b2c0._decode_value_type(b2c0._record(item, (0,), "public input")[0])
        )
        for item in tables[1]
    )
    scopes: list[object] = []
    for item in tables[5]:
        parent, opening = b2c0._record(item, (0, 1), "scope")
        parent_case, parent_payload = b2c0._variant(parent, (0, 1), "scope parent")
        opening_case, opening_payload = b2c0._variant(opening, (0, 1), "scope opening")
        if parent_case == 0:
            b2c0._unit(parent_payload, "absent parent")
        if opening_case == 0:
            b2c0._unit(opening_payload, "initial opening")
        scopes.append(
            base.ScopeDecl(
                None if parent_case == 0 else b2c0._nat(parent_payload, "parent"),
                None
                if opening_case == 0
                else b2c0._nat(opening_payload, "opening occurrence"),
            )
        )
    bindings: list[object] = []
    for item in tables[6]:
        scope, binding_class, value = b2c0._record(item, (0, 1, 2), "binding")
        class_case, class_payload = b2c0._variant(
            binding_class, (0, 1, 2), "binding class"
        )
        b2c0._unit(class_payload, "binding class payload")
        bindings.append(
            base.PublicBindingDecl(
                b2c0._nat(scope, "binding scope"),
                base.BindingClass(class_case),
                b2c0._decode_value_ref(value),
            )
        )
    occurrences = tuple(
        base.OccurrenceDecl(
            b2c0._nat(
                b2c0._record(item, (0, 1, 2), "occurrence")[0],
                "occurrence scope",
            ),
            b2c0._decode_guard(b2c0._record(item, (0, 1, 2), "occurrence")[1]),
            _decode_effect(b2c0._record(item, (0, 1, 2), "occurrence")[2]),
        )
        for item in tables[13]
    )
    return base.InteractiveCore(
        tuple(b2c0._content_ref(item, "used module") for item in tables[0]),
        public_inputs,
        (),
        (),
        (),
        tuple(scopes),
        tuple(bindings),
        (),
        (),
        (),
        (),
        (),
        tuple(_decode_terminal(item) for item in tables[12]),
        occurrences,
    )


def _symbol(value: object, label: str) -> str:
    if type(value) is not k1.Symbol:
        _fail("Malformed", "F0V2B2C1B4-M-MODULE-DECL", f"{label} is not a symbol")
    return value.value


def _decode_bool(value: object, label: str) -> bool:
    case, payload = b2c0._variant(value, (0, 1), label)
    b2c0._unit(payload, f"{label} payload")
    return bool(case)


def _decode_dependency(value: object) -> ModuleDependency:
    case, payload = b2c0._variant(value, tuple(range(4)), "module dependency")
    kind = ModuleDependencyKind(case)
    if kind in (ModuleDependencyKind.ACTIVITY, ModuleDependencyKind.EFFECT):
        b2c0._unit(payload, "node-local dependency payload")
        return ModuleDependency(kind)
    return ModuleDependency(kind, b2c0._nat(payload, "module dependency ordinal"))


def _decode_output(value: object) -> ModuleOutputSpec:
    value_type, visibility, transfer, dependencies, sink = b2c0._record(
        value, (0, 1, 2, 3, 4), "module output"
    )
    visibility_case, visibility_payload = b2c0._variant(
        visibility, tuple(range(4)), "module visibility"
    )
    b2c0._unit(visibility_payload, "module visibility payload")
    transfer_case, transfer_payload = b2c0._variant(
        transfer, tuple(range(3)), "module output transfer"
    )
    algorithm: object | None = None
    contract: object | None = None
    if transfer_case == 0:
        algorithm_value, contract_value = b2c0._record(
            transfer_payload, (0, 1), "module reconstruction"
        )
        algorithm = b2c0._content_ref(algorithm_value, "reconstruction algorithm")
        contract = b2c0._content_ref(contract_value, "reconstruction contract")
    else:
        b2c0._unit(transfer_payload, "nondeterministic transfer payload")
    return ModuleOutputSpec(
        b2c0._decode_value_type(value_type),
        ModuleVisibility(visibility_case),
        ModuleOutputTransfer(transfer_case),
        tuple(
            _decode_dependency(item)
            for item in b2c0._sequence(dependencies, "module output dependencies")
        ),
        algorithm,
        contract,
        _decode_bool(sink, "module output sink"),
    )


def _decode_control(value: object) -> ModuleControlSpec:
    dependencies, sink = b2c0._record(value, (0, 1), "module control")
    return ModuleControlSpec(
        tuple(
            _decode_dependency(item)
            for item in b2c0._sequence(dependencies, "module control dependencies")
        ),
        _decode_bool(sink, "module control sink"),
    )


def decode_semantics(value: object) -> ModuleSemantics:
    fields = b2c0._record(value, tuple(range(11)), "module declaration")
    if _symbol(fields[0], "module declaration magic") != MODULE_DECLARATION_MAGIC:
        _fail(
            "Unsupported",
            "F0V2B2C1B4-U-MODULE-SCHEMA",
            "module declaration selects another supported schema",
        )
    decision_case, decision_payload = b2c0._variant(
        fields[2], tuple(range(3)), "module decision class"
    )
    if decision_case == 0:
        b2c0._unit(decision_payload, "NoProverDecision payload")
        move_type = None
    else:
        move_type = b2c0._decode_value_type(decision_payload)
    influence_case, influence_payload = b2c0._variant(
        fields[6], (0, 1), "module influence output"
    )
    if influence_case == 0:
        b2c0._unit(influence_payload, "absent influence output")
    return ModuleSemantics(
        _symbol(fields[1], "module declaration name"),
        tuple(
            b2c0._decode_value_type(item)
            for item in b2c0._sequence(fields[3], "module payload ABI")
        ),
        ModuleDecisionClass(decision_case),
        move_type,
        tuple(
            _decode_output(item) for item in b2c0._sequence(fields[4], "module outputs")
        ),
        tuple(
            _decode_control(item)
            for item in b2c0._sequence(fields[5], "module controls")
        ),
        None
        if influence_case == 0
        else b2c0._nat(influence_payload, "module influence output"),
        _symbol(fields[7], "module guard behavior"),
        _symbol(fields[8], "module replay rule"),
        _symbol(fields[9], "module terminal interaction"),
        b2c0._nat(fields[10], "module work bound"),
    )


def identity_algorithm() -> object:
    return k1.CanonicalAlgorithm(
        k1.Symbol("f0v2b2c1b4.reconstruct-identity-z3"),
        (base.Z3,),
        k1.Variable(0, base.Z3),
    )


def supported_semantics() -> tuple[ModuleSemantics, ...]:
    activity = ModuleDependency(ModuleDependencyKind.ACTIVITY)
    effect = ModuleDependency(ModuleDependencyKind.EFFECT)
    input_zero = ModuleDependency(ModuleDependencyKind.PAYLOAD_INPUT, 0)
    output_zero = ModuleDependency(ModuleDependencyKind.PRIOR_OUTPUT, 0)
    algorithm = identity_algorithm()
    contract = k1.DEFAULT_EVALUATION_CONTRACT
    return (
        ModuleSemantics(
            "bounded-deterministic-public",
            (base.Z3,),
            ModuleDecisionClass.NO_PROVER_DECISION,
            None,
            (
                ModuleOutputSpec(
                    base.Z3,
                    ModuleVisibility.PUBLIC,
                    ModuleOutputTransfer.DETERMINISTIC,
                    (activity, effect, input_zero),
                    algorithm.identity,
                    contract.identity,
                    True,
                ),
            ),
            (ModuleControlSpec((activity, effect, output_zero), True),),
            None,
            "inherit-exact-occurrence-guard",
            "exact-module-event-replay",
            "nonterminating",
            8,
        ),
        ModuleSemantics(
            "bounded-prover-decision",
            (base.Z3,),
            ModuleDecisionClass.PROVER_DECISION,
            base.Z3,
            (
                ModuleOutputSpec(
                    base.Z3,
                    ModuleVisibility.PROVER_ONLY,
                    ModuleOutputTransfer.PROVER_INTERNAL,
                    (activity, effect, input_zero),
                    None,
                    None,
                    True,
                ),
            ),
            (ModuleControlSpec((activity, effect, output_zero), True),),
            None,
            "inherit-exact-occurrence-guard",
            "exact-module-event-replay",
            "nonterminating",
            8,
        ),
        ModuleSemantics(
            "bounded-prover-publication",
            (base.Z3,),
            ModuleDecisionClass.PROVER_PUBLICATION,
            base.Z3,
            (
                ModuleOutputSpec(
                    base.Z3,
                    ModuleVisibility.PUBLIC,
                    ModuleOutputTransfer.PROVER_PUBLICATION,
                    (activity, effect, input_zero),
                    None,
                    None,
                    True,
                ),
            ),
            (ModuleControlSpec((activity, effect, output_zero), True),),
            0,
            "inherit-exact-occurrence-guard",
            "exact-module-event-replay",
            "nonterminating",
            8,
        ),
    )


def _catalog(kind: str, values: tuple[object, ...]) -> object:
    return _record(k1.Symbol(kind), _seq(values))


def extension_module(
    semantics: tuple[ModuleSemantics, ...] | None = None,
) -> object:
    selected = supported_semantics() if semantics is None else semantics
    return k1.SemanticModuleCandidate(
        k1.Symbol("f0v2b2c1b4.module-owner-fixture"),
        (),
        _seq(
            (
                _catalog(
                    "pir.core-effect",
                    tuple(_semantics_datum(item) for item in selected),
                ),
            )
        ),
    )


def _validate_dependencies(
    dependencies: tuple[ModuleDependency, ...],
    semantics: ModuleSemantics,
    output_ordinal: int | None,
) -> None:
    if len(dependencies) != len(set(dependencies)):
        _fail(
            "Refused",
            "F0V2B2C1B4-R-MODULE-EDGE-UNIQUE",
            "module dependency edge list contains a duplicate",
        )
    if (
        ModuleDependency(ModuleDependencyKind.ACTIVITY) not in dependencies
        or ModuleDependency(ModuleDependencyKind.EFFECT) not in dependencies
    ):
        _fail(
            "Refused",
            "F0V2B2C1B4-R-MODULE-EDGE-CLOSURE",
            "module result omits its activity or effect dependency",
        )
    for dependency in dependencies:
        if dependency.kind is ModuleDependencyKind.PAYLOAD_INPUT:
            if dependency.ordinal is None or not 0 <= dependency.ordinal < len(
                semantics.payload_input_types
            ):
                _fail(
                    "Refused",
                    "F0V2B2C1B4-R-MODULE-EDGE-REF",
                    "module dependency names an absent payload input",
                )
        elif dependency.kind is ModuleDependencyKind.PRIOR_OUTPUT:
            limit = len(semantics.outputs) if output_ordinal is None else output_ordinal
            if dependency.ordinal is None or not 0 <= dependency.ordinal < limit:
                _fail(
                    "Refused",
                    "F0V2B2C1B4-R-MODULE-EDGE-REF",
                    "module dependency names a non-prior output",
                )


def _validate_semantics(semantics: ModuleSemantics) -> None:
    if (
        semantics.guard_behavior != "inherit-exact-occurrence-guard"
        or semantics.replay_rule != "exact-module-event-replay"
        or semantics.terminal_interaction != "nonterminating"
        or not 0 < semantics.work_bound <= MAX_LOCAL_ITEMS
    ):
        _fail(
            "Refused",
            "F0V2B2C1B4-R-MODULE-LIFECYCLE",
            "module guard, replay, terminal, or work-bound law differs",
        )
    if semantics.decision_class is ModuleDecisionClass.NO_PROVER_DECISION:
        if semantics.move_type is not None:
            _fail(
                "Refused",
                "F0V2B2C1B4-R-MODULE-DECISION",
                "NoProverDecision carries a move type",
            )
    elif semantics.move_type is None:
        _fail(
            "Refused",
            "F0V2B2C1B4-R-MODULE-DECISION",
            "module prover decision lacks a move type",
        )
    publication_outputs: list[int] = []
    for output_ordinal, output in enumerate(semantics.outputs):
        _validate_dependencies(output.dependencies, semantics, output_ordinal)
        if output.transfer is ModuleOutputTransfer.DETERMINISTIC:
            if (
                output.visibility is not ModuleVisibility.PUBLIC
                or output.reconstruction_algorithm is None
                or output.reconstruction_contract is None
            ):
                _fail(
                    "Refused",
                    "F0V2B2C1B4-R-MODULE-RECONSTRUCTION",
                    "deterministic public output lacks exact reconstruction",
                )
        elif output.transfer is ModuleOutputTransfer.PROVER_PUBLICATION:
            publication_outputs.append(output_ordinal)
            if (
                semantics.decision_class is not ModuleDecisionClass.PROVER_PUBLICATION
                or output.visibility is not ModuleVisibility.PUBLIC
                or output.reconstruction_algorithm is not None
                or output.reconstruction_contract is not None
            ):
                _fail(
                    "Refused",
                    "F0V2B2C1B4-R-MODULE-PUBLICATION",
                    "publication transfer, decision class, or visibility differs",
                )
        elif (
            output.transfer is not ModuleOutputTransfer.PROVER_INTERNAL
            or semantics.decision_class is not ModuleDecisionClass.PROVER_DECISION
            or output.visibility is not ModuleVisibility.PROVER_ONLY
            or output.reconstruction_algorithm is not None
            or output.reconstruction_contract is not None
        ):
            _fail(
                "Refused",
                "F0V2B2C1B4-R-MODULE-INTERNAL-OUTPUT",
                "private module move output has another transfer or visibility",
            )
    for control in semantics.controls:
        _validate_dependencies(control.dependencies, semantics, None)
    public_outputs = [
        index
        for index, output in enumerate(semantics.outputs)
        if output.visibility is ModuleVisibility.PUBLIC
    ]
    if semantics.decision_class is ModuleDecisionClass.PROVER_PUBLICATION:
        if (
            publication_outputs != [semantics.influence_output]
            or public_outputs != publication_outputs
        ):
            _fail(
                "Refused",
                "F0V2B2C1B4-R-MODULE-PUBLICATION",
                "ProverPublication lacks its unique public observation and influence output",
            )
    elif publication_outputs or semantics.influence_output is not None:
        _fail(
            "Refused",
            "F0V2B2C1B4-R-MODULE-INFLUENCE",
            "nonpublication module declaration asserts publication influence",
        )
    if semantics.decision_class is ModuleDecisionClass.NO_PROVER_DECISION and any(
        output.transfer is not ModuleOutputTransfer.DETERMINISTIC
        for output in semantics.outputs
    ):
        _fail(
            "Refused",
            "F0V2B2C1B4-R-MODULE-NONDETERMINISM",
            "NoProverDecision exposes a nondeterministic output",
        )


def _resolve_supported_semantics(
    effect: ModuleEffectRef, environment: object
) -> ModuleSemantics:
    if (
        type(effect.declaration) is not base.ModuleDeclarationRef
        or effect.declaration.declaration_kind != "pir.core-effect"
    ):
        _fail(
            "KindMismatch",
            "F0V2B2C1B4-K-MODULE-DECLARATION",
            "module effect declaration has another kind",
        )
    if effect.module != effect.declaration.module:
        _fail(
            "Refused",
            "F0V2B2C1B4-R-MODULE-OWNER",
            "module effect owner and declaration owner differ",
        )
    if (
        type(effect.module) is not k1.TypedContentId
        or effect.module.subject_kind != k1.SEMANTIC_MODULE_KIND
    ):
        _fail(
            "KindMismatch",
            "F0V2B2C1B4-K-MODULE-OWNER",
            "module effect owner has another subject kind",
        )
    module = environment.module_preimages.get(effect.module)
    if module is None:
        _fail(
            "MissingDependency",
            "F0V2B2C1B4-D-MODULE-PREIMAGE",
            "module effect owner preimage is absent",
        )
    try:
        if module.identity != effect.module:
            _fail(
                "Refused",
                "F0V2B2C1B4-R-MODULE-ID",
                "module effect owner body does not authenticate",
            )
        declaration = k1.resolve_module_declaration(
            module,
            effect.declaration.declaration_kind,
            effect.declaration.local_ordinal,
        )
    except FamilyFailure:
        raise
    except Exception as error:
        _fail(
            "Refused",
            "F0V2B2C1B4-R-MODULE-COORDINATE",
            str(error),
        )
    semantics = decode_semantics(declaration)
    _validate_semantics(semantics)
    expected = extension_module()
    supported = supported_semantics()
    if (
        module.body() != expected.body()
        or effect.module != expected.identity
        or not 0 <= effect.declaration.local_ordinal < len(supported)
        or semantics != supported[effect.declaration.local_ordinal]
    ):
        _fail(
            "Unsupported",
            "F0V2B2C1B4-U-MODULE-DECLARATION",
            "this evaluator does not advertise the exact module declaration",
        )
    return semantics


def _value_type(
    core: object,
    outputs: tuple[tuple[object, ...], ...],
    reference: object,
) -> object:
    if type(reference) is base.PublicInputRef:
        if not 0 <= reference.ordinal < len(core.public_inputs):
            _fail("Refused", "F0V2B2C1B4-R-VALUE-REF", "public input is absent")
        return core.public_inputs[reference.ordinal].value_type
    if type(reference) is base.OccurrenceOutputRef:
        if not 0 <= reference.occurrence < len(outputs):
            _fail("Refused", "F0V2B2C1B4-R-VALUE-REF", "occurrence is absent")
        row = outputs[reference.occurrence]
        if not 0 <= reference.output_ordinal < len(row):
            _fail("Refused", "F0V2B2C1B4-R-VALUE-REF", "output is absent")
        return row[reference.output_ordinal]
    _fail(
        "Malformed",
        "F0V2B2C1B4-M-VALUE-REF",
        "ValueRef belongs to another isolation slice",
    )
    raise AssertionError("unreachable")


def _producer_node(reference: object) -> tuple[int, ...]:
    if type(reference) is base.PublicInputRef:
        return 0, reference.ordinal
    if type(reference) is base.OccurrenceOutputRef:
        return 8, reference.occurrence, reference.output_ordinal
    _fail(
        "Malformed",
        "F0V2B2C1B4-M-VALUE-REF",
        "producer belongs to another isolation slice",
    )
    raise AssertionError("unreachable")


def _value_dependencies(
    effect: ModuleEffectRef,
    dependencies: tuple[ModuleDependency, ...],
    occurrence_ref: int,
) -> tuple[object, ...]:
    result: list[object] = []
    for dependency in dependencies:
        if dependency.kind is ModuleDependencyKind.PAYLOAD_INPUT:
            if dependency.ordinal is None:
                raise AssertionError("validated payload dependency lacks ordinal")
            result.append(effect.payload.inputs[dependency.ordinal])
        elif dependency.kind is ModuleDependencyKind.PRIOR_OUTPUT:
            if dependency.ordinal is None:
                raise AssertionError("validated output dependency lacks ordinal")
            result.append(base.OccurrenceOutputRef(occurrence_ref, dependency.ordinal))
    return tuple(result)


def _authenticate_reconstruction(
    core: object,
    environment: object,
    semantics_by_occurrence: Mapping[int, ModuleSemantics],
    effects: Mapping[int, ModuleEffectRef],
) -> None:
    required_algorithms: dict[object, tuple[tuple[object, ...], object]] = {}
    required_contracts: set[object] = set()
    for occurrence_ref, semantics in semantics_by_occurrence.items():
        effect = effects[occurrence_ref]
        for output in semantics.outputs:
            if output.transfer is not ModuleOutputTransfer.DETERMINISTIC:
                continue
            if (
                output.reconstruction_algorithm is None
                or output.reconstruction_contract is None
            ):
                raise AssertionError("validated deterministic output lacks authority")
            inputs = tuple(
                _value_type(core, (), reference)
                if type(reference) is base.PublicInputRef
                else semantics.outputs[reference.output_ordinal].value_type
                for reference in _value_dependencies(
                    effect, output.dependencies, occurrence_ref
                )
            )
            signature = (inputs, output.value_type)
            prior_signature = required_algorithms.get(output.reconstruction_algorithm)
            if prior_signature is not None and prior_signature != signature:
                _fail(
                    "KindMismatch",
                    "F0V2B2C1B4-K-MODULE-RECONSTRUCTION-ABI",
                    "one reconstruction algorithm is used at two ABIs",
                )
            required_algorithms[output.reconstruction_algorithm] = signature
            required_contracts.add(output.reconstruction_contract)
    if set(environment.algorithm_preimages) != set(required_algorithms):
        missing = set(required_algorithms) - set(environment.algorithm_preimages)
        _fail(
            "MissingDependency" if missing else "Refused",
            "F0V2B2C1B4-D-RECONSTRUCTION-ALGORITHM"
            if missing
            else "F0V2B2C1B4-R-EXACT-ALGORITHMS",
            "reconstruction algorithm closure differs",
        )
    if set(environment.contract_preimages) != required_contracts:
        missing = required_contracts - set(environment.contract_preimages)
        _fail(
            "MissingDependency" if missing else "Refused",
            "F0V2B2C1B4-D-RECONSTRUCTION-CONTRACT"
            if missing
            else "F0V2B2C1B4-R-EXACT-CONTRACTS",
            "reconstruction contract closure differs",
        )
    ledger = k1.AuthenticationLedger()
    try:
        for identifier, (inputs, output) in required_algorithms.items():
            algorithm = environment.algorithm_preimages[identifier]
            if (
                k1.authenticate_algorithm_identity(algorithm, ledger=ledger)
                != identifier
            ):
                _fail(
                    "Refused",
                    "F0V2B2C1B4-R-RECONSTRUCTION-ID",
                    "reconstruction algorithm identity differs",
                )
            modules = environment.algorithm_modules.get(identifier)
            if modules is None:
                _fail(
                    "MissingDependency",
                    "F0V2B2C1B4-D-RECONSTRUCTION-MODULES",
                    "reconstruction module closure is absent",
                )
            dependencies = k1.direct_module_dependencies(algorithm, ledger=ledger)
            k1.authenticate_module_closure(
                dependencies,
                dict(modules),
                semantic_regime=k1.SEMANTIC_REGIME_ID,
                ledger=ledger,
            )
            k1.authenticate_algorithm_declaration_references(
                algorithm, dict(modules), ledger=ledger
            )
            function = algorithm.function_type
            if (
                function.inputs != inputs
                or function.output != output
                or function.failures
            ):
                _fail(
                    "KindMismatch",
                    "F0V2B2C1B4-K-MODULE-RECONSTRUCTION-ABI",
                    "reconstruction algorithm ABI is not exact and total",
                )
        for identifier in required_contracts:
            contract = environment.contract_preimages[identifier]
            if contract.identity != identifier:
                _fail(
                    "Refused",
                    "F0V2B2C1B4-R-RECONSTRUCTION-CONTRACT-ID",
                    "reconstruction contract identity differs",
                )
            k1.authenticate_content_id(
                identifier,
                contract.body(),
                environment.prior_meta_preimages,
                ledger=ledger,
            )
    except FamilyFailure:
        raise
    except Exception as error:
        _fail("Refused", "F0V2B2C1B4-R-RECONSTRUCTION", str(error))


def _validate_core(core: object, environment: object) -> ValidationEvidence:
    if (
        type(environment) is not base.Environment
        or len(core.scopes) != 1
        or core.scopes[0] != base.ScopeDecl(None, None)
        or len(core.public_inputs) != 1
        or not core.occurrences
        or len(core.terminals) != 1
    ):
        _fail(
            "Refused",
            "F0V2B2C1B4-R-ISOLATION-SHAPE",
            "bounded module carrier has another root/input/terminal shape",
        )
    if len(core.occurrences) > MAX_LOCAL_ITEMS:
        _fail(
            "DeterministicLimitExceeded",
            "F0V2B2C1B4-L-OCCURRENCES",
            "occurrence table crosses the local bound",
        )
    if any(
        type(item) is not base.AlwaysGuard
        for item in (o.guard for o in core.occurrences)
    ):
        _fail(
            "Unsupported",
            "F0V2B2C1B4-U-GUARD",
            "guarded module behavior remains outside this isolation slice",
        )
    if any(item.scope != 0 for item in core.occurrences) or any(
        item.scope != 0 for item in core.public_bindings
    ):
        _fail(
            "Refused",
            "F0V2B2C1B4-R-SCOPE",
            "bounded module carrier leaves the root scope",
        )
    if len(core.public_bindings) != 1 or core.public_bindings[
        0
    ] != base.PublicBindingDecl(0, base.BindingClass.STATEMENT, base.PublicInputRef(0)):
        _fail(
            "Refused",
            "F0V2B2C1B4-R-BINDING",
            "public input lacks its exact root Statement binding",
        )
    try:
        core.public_inputs[0].value_type.__post_init__()
        k1.authenticate_value_type_reference(
            core.public_inputs[0].value_type,
            dict(environment.module_preimages),
            semantic_regime=k1.SEMANTIC_REGIME_ID,
        )
    except Exception as error:
        _fail("KindMismatch", "F0V2B2C1B4-K-VALUE-TYPE", str(error))

    module_effects = {
        occurrence_ref: occurrence.effect
        for occurrence_ref, occurrence in enumerate(core.occurrences)
        if type(occurrence.effect) is ModuleEffectRef
    }
    direct_modules = tuple(
        sorted(
            {
                owner
                for effect in module_effects.values()
                for owner in (effect.module, effect.declaration.module)
            },
            key=lambda item: item.internal_reference(),
        )
    )
    if core.used_modules != direct_modules:
        _fail(
            "Refused",
            "F0V2B2C1B4-R-EXACT-USED-MODULES",
            "used_modules differs from exact module-effect owners",
        )
    if set(environment.module_preimages) != set(core.used_modules):
        missing = set(core.used_modules) - set(environment.module_preimages)
        _fail(
            "MissingDependency" if missing else "Refused",
            "F0V2B2C1B4-D-MODULE-PREIMAGE"
            if missing
            else "F0V2B2C1B4-R-EXACT-MODULE-PREIMAGES",
            "module preimage closure differs",
        )
    semantics_by_occurrence: dict[int, ModuleSemantics] = {}
    for occurrence_ref, effect in module_effects.items():
        semantics_by_occurrence[occurrence_ref] = _resolve_supported_semantics(
            effect, environment
        )
    if not semantics_by_occurrence:
        _fail(
            "Refused",
            "F0V2B2C1B4-R-MODULE-NONEMPTY",
            "module isolation carrier contains no ModuleEffect",
        )

    outputs = tuple(
        tuple(item.value_type for item in semantics_by_occurrence[index].outputs)
        if index in semantics_by_occurrence
        else ()
        for index in range(len(core.occurrences))
    )
    available: set[object] = {base.PublicInputRef(0)}
    for occurrence_ref, occurrence in enumerate(core.occurrences):
        if type(occurrence.effect) is ModuleEffectRef:
            effect = occurrence.effect
            semantics = semantics_by_occurrence[occurrence_ref]
            if len(effect.payload.inputs) != len(semantics.payload_input_types):
                _fail(
                    "Malformed",
                    "F0V2B2C1B4-M-MODULE-PAYLOAD-ARITY",
                    "module payload input count differs from its exact schema",
                )
            for reference, expected_type in zip(
                effect.payload.inputs,
                semantics.payload_input_types,
                strict=True,
            ):
                if reference not in available:
                    _fail(
                        "Refused",
                        "F0V2B2C1B4-R-MODULE-PAYLOAD-AVAILABILITY",
                        "module payload names a future or absent value",
                    )
                if _value_type(core, outputs, reference) != expected_type:
                    _fail(
                        "KindMismatch",
                        "F0V2B2C1B4-K-MODULE-PAYLOAD-ABI",
                        "module payload input type differs",
                    )
            for output_ordinal in range(len(outputs[occurrence_ref])):
                available.add(base.OccurrenceOutputRef(occurrence_ref, output_ordinal))
        elif type(occurrence.effect) is not base.TerminalEffect:
            _fail(
                "Unsupported",
                "F0V2B2C1B4-U-EFFECT",
                "occurrence belongs to another effect slice",
            )

    terminal_positions = [
        index
        for index, occurrence in enumerate(core.occurrences)
        if type(occurrence.effect) is base.TerminalEffect
        and occurrence.effect.terminal == 0
    ]
    terminal = core.terminals[0]
    if (
        terminal_positions != [len(core.occurrences) - 1]
        or type(core.occurrences[-1].guard) is not base.AlwaysGuard
        or terminal.verdict is not base.TerminalVerdict.ACCEPT
        or terminal.public_outputs
        or terminal.required_true_checks
        or terminal.claim_dispositions
    ):
        _fail(
            "Refused",
            "F0V2B2C1B4-R-TERMINAL-FALLBACK",
            "module isolation carrier lacks its exact unconditional Accept fallback",
        )
    if any(
        type(occurrence.effect) is base.TerminalEffect
        and occurrence.effect.terminal != 0
        for occurrence in core.occurrences
    ):
        _fail(
            "Refused",
            "F0V2B2C1B4-R-TERMINAL-BACKLINK",
            "terminal occurrence names an absent declaration",
        )
    _authenticate_reconstruction(
        core,
        environment,
        MappingProxyType(semantics_by_occurrence),
        MappingProxyType(module_effects),
    )
    return ValidationEvidence(
        outputs,
        ((0,),),
        MappingProxyType({0: terminal_positions[0]}),
        MappingProxyType(semantics_by_occurrence),
    )


def _pc_value(node: tuple[int, ...]) -> dict[str, Any]:
    return prior._pc_value(node)


def _pc_key(node: tuple[int, ...]) -> bytes:
    return codec.encode_value(prior._PC_NODE_SCHEMA, _pc_value(node))


def _edge_value(
    pair: tuple[tuple[int, ...], tuple[int, ...]],
) -> dict[int, Any]:
    return {0: _pc_value(pair[0]), 1: _pc_value(pair[1])}


def _edge_key(pair: tuple[tuple[int, ...], tuple[int, ...]]) -> bytes:
    return codec.encode_value(prior._PC_EDGE_SCHEMA, _edge_value(pair))


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
        raise AssertionError("validated indexed dependency lacks ordinal")
    if dependency.kind is ModuleDependencyKind.PAYLOAD_INPUT:
        return _producer_node(effect.payload.inputs[dependency.ordinal])
    return 13, occurrence_ref, dependency.ordinal


def _join(values: list[int]) -> int:
    if 3 in values:
        return 3
    if 2 in values:
        return 2
    if 1 in values:
        return 1
    return 0


def _publish(value: int) -> int:
    return 1 if value in (0, 1) else value


def _graph(
    core: object, validation: ValidationEvidence
) -> tuple[dict[int, Any], dict[str, Any]]:
    nodes: set[tuple[int, ...]] = {(0, 0), (4, 0), (5, 0)}
    edges: set[tuple[tuple[int, ...], tuple[int, ...]]] = {
        ((0, 0), (5, 0)),
        ((4, 0), (5, 0)),
    }
    output_specs: dict[tuple[int, ...], ModuleOutputSpec] = {}
    public_observations: set[tuple[int, ...]] = set()
    acceptance_module: set[tuple[int, ...]] = set()
    for occurrence_ref, occurrence in enumerate(core.occurrences):
        activity = (6, occurrence_ref)
        effect_node = (7, occurrence_ref)
        nodes.update((activity, effect_node))
        edges.add(((4, occurrence.scope), activity))
        edges.add((activity, effect_node))
        if type(occurrence.effect) is ModuleEffectRef:
            effect = occurrence.effect
            semantics = validation.module_semantics[occurrence_ref]
            for control_ordinal, control in enumerate(semantics.controls):
                node = (12, occurrence_ref, control_ordinal)
                nodes.add(node)
                for dependency in control.dependencies:
                    source = _module_dependency_node(effect, dependency, occurrence_ref)
                    nodes.add(source)
                    edges.add((source, node))
                if control.acceptance_relevant:
                    acceptance_module.add(node)
            for output_ordinal, output in enumerate(semantics.outputs):
                module_output = (13, occurrence_ref, output_ordinal)
                occurrence_output = (8, occurrence_ref, output_ordinal)
                nodes.update((module_output, occurrence_output))
                output_specs[module_output] = output
                for dependency in output.dependencies:
                    source = _module_dependency_node(effect, dependency, occurrence_ref)
                    nodes.add(source)
                    edges.add((source, module_output))
                edges.add((effect_node, occurrence_output))
                edges.add((module_output, occurrence_output))
                if output.visibility is ModuleVisibility.PUBLIC:
                    public_observations.update((module_output, occurrence_output))
                if output.acceptance_relevant:
                    acceptance_module.add(module_output)
        else:
            terminal = (11, occurrence.effect.terminal)
            nodes.add(terminal)
            edges.add((effect_node, terminal))

    incoming: dict[tuple[int, ...], set[tuple[int, ...]]] = {
        node: set() for node in nodes
    }
    outgoing: dict[tuple[int, ...], set[tuple[int, ...]]] = {
        node: set() for node in nodes
    }
    for source, target in edges:
        incoming[target].add(source)
        outgoing[source].add(target)
    heap = [(_pc_key(node), node) for node in nodes if not incoming[node]]
    heapq.heapify(heap)
    indegree = {node: len(incoming[node]) for node in nodes}
    topological: list[tuple[int, ...]] = []
    while heap:
        _key, node = heapq.heappop(heap)
        topological.append(node)
        for target in outgoing[node]:
            indegree[target] -= 1
            if indegree[target] == 0:
                heapq.heappush(heap, (_pc_key(target), target))
    if len(topological) != len(nodes):
        _fail("Refused", "F0V2B2C1B4-R-PCGRAPH-CYCLE", "module PCGraph is cyclic")

    classes: dict[tuple[int, ...], int] = {}
    for node in topological:
        if node[0] in (0, 4):
            value = 0
        elif node in output_specs:
            joined = _join([classes[item] for item in incoming[node]])
            transfer = output_specs[node].transfer
            if transfer is ModuleOutputTransfer.DETERMINISTIC:
                value = joined
            elif transfer is ModuleOutputTransfer.PROVER_PUBLICATION:
                value = _publish(joined)
            else:
                value = 3
        else:
            value = _join([classes[item] for item in incoming[node]])
        classes[node] = value

    terminal_ref = validation.terminal_positions[0]
    terminal_nodes = {(6, terminal_ref), (7, terminal_ref), (11, 0)}
    observation_activities = {
        (6, occurrence_ref)
        for occurrence_ref, semantics in validation.module_semantics.items()
        if any(
            output.visibility is ModuleVisibility.PUBLIC for output in semantics.outputs
        )
    }
    sinks = (
        terminal_nodes
        | public_observations
        | observation_activities
        | acceptance_module
    )
    acceptance = {(11, 0)} | acceptance_module
    eligible = all(classes[node] in (0, 1) for node in sinks)
    ordered_nodes = sorted(nodes, key=_pc_key)
    graph = {
        0: [_pc_value(node) for node in ordered_nodes],
        1: [_edge_value(edge) for edge in sorted(edges, key=_edge_key)],
        2: [_pc_value(node) for node in topological],
        3: [
            {0: _pc_value(node), 1: foundation._v(classes[node])}
            for node in ordered_nodes
        ],
        4: [_pc_value(node) for node in sorted(sinks, key=_pc_key)],
        5: [_pc_value(node) for node in sorted(acceptance, key=_pc_key)],
        6: [],
    }
    return graph, {
        "nodes": len(nodes),
        "edges": len(edges),
        "eligible": eligible,
        "classes": classes,
        "public_observations": len(public_observations),
        "acceptance_sinks": len(acceptance),
    }


def admit_core(candidate: object, environment: object) -> AdmissionResult:
    try:
        if type(candidate) is not b2c0.CanonicalCoreCandidate:
            _fail("Malformed", "F0V2B2C1B4-M-REQUEST", "Core request is malformed")
        if type(environment) is not base.Environment:
            _fail(
                "Malformed",
                "F0V2B2C1B4-M-ENVIRONMENT",
                "environment has another carrier",
            )
        if candidate.profile_id != environment.profile_id:
            _fail("KindMismatch", "F0V2B2C1B4-K-REQUEST-PROFILE", "profiles differ")
        if environment.profile_id != base.target_profile_id():
            _fail(
                "KindMismatch",
                "F0V2B2C1B4-K-TARGET-PROFILE",
                "owner profile is unsupported",
            )
        profile, domain, domain_body = b2c0._strict_profiled_body(
            candidate.profiled_body, "B2C1B4 module Core"
        )
        if profile != candidate.profile_id:
            _fail("KindMismatch", "F0V2B2C1B4-K-BODY-PROFILE", "body profile differs")
        if (
            type(candidate.asserted_id) is not k1.TypedContentId
            or candidate.asserted_id.subject_kind != base.TARGET_CORE_KIND
        ):
            _fail("KindMismatch", "F0V2B2C1B4-K-CORE-ID", "Core ID kind differs")
        try:
            k1.authenticate_content_id(
                candidate.asserted_id,
                candidate.profiled_body,
                environment.prior_meta_preimages,
            )
        except Exception as error:
            _fail("Malformed", "F0V2B2C1B4-M-CORE-ID", str(error))
        core = decode_core(domain)
        validation = _validate_core(core, environment)
        closure = b2c0.snapshot_environment(environment)
        _graph_value, graph_evidence = _graph(core, validation)
        handle = b2c0.AdmittedCoreSnapshot(
            candidate.asserted_id.internal_reference(),
            candidate.profile_id.internal_reference(),
            bytes(candidate.profiled_body),
            bytes(domain_body),
            closure,
            (
                ("slice", "F0-V2B2C1B4"),
                ("core", core),
                ("validation", validation),
                ("graph_evidence", graph_evidence),
            ),
            EVALUATOR_FINGERPRINT,
            tuple(range(1, 16)),
            b2c0._CORE_ISSUER,
        )
        return AdmissionResult(
            "Affirmative",
            "F0V2B2C1B4-A-CORE-ADMITTED",
            "exact bytes passed the bounded module owner evaluator",
            handle,
        )
    except FamilyFailure as error:
        return AdmissionResult(error.outcome, error.code, error.detail)
    except b2c0.SnapshotFailure as error:
        return AdmissionResult(error.outcome, error.code, error.detail)
    except Exception as error:  # pragma: no cover - fail-closed defect lane
        return AdmissionResult("CheckerFailure", "F0V2B2C1B4-CHECKER", str(error))


def _retained_core(handle: object) -> tuple[object, ValidationEvidence]:
    if (
        type(handle) is not b2c0.AdmittedCoreSnapshot
        or not handle._issued_by(b2c0._CORE_ISSUER)
        or handle.evaluator_fingerprint != EVALUATOR_FINGERPRINT
    ):
        _fail("Refused", "F0V2B2C1B4-R-CORE-AUTHORITY", "Core authority differs")
    summary = dict(handle.structural_summary)
    if (
        summary.get("slice") != "F0-V2B2C1B4"
        or type(summary.get("core")) is not base.InteractiveCore
        or type(summary.get("validation")) is not ValidationEvidence
    ):
        _fail(
            "Refused",
            "F0V2B2C1B4-R-RETAINED-FACTS",
            "retained owner facts differ",
        )
    core = summary["core"]
    profile = k1.decode_content_reference(handle.profile_reference)
    if core_profiled_body(core, profile) != handle.profiled_body:
        _fail("Refused", "F0V2B2C1B4-R-RETAINED-BODY", "retained body differs")
    return core, summary["validation"]


def admit_fresh_protocol(
    core_handle: object, candidate: object, environment: object
) -> AdmissionResult:
    try:
        _retained_core(core_handle)
        if type(candidate) is not b2c0.CanonicalFreshProtocolCandidate:
            _fail(
                "Malformed",
                "F0V2B2C1B4-M-PROTOCOL-REQUEST",
                "Protocol request differs",
            )
        profile, domain, _domain_body = b2c0._strict_profiled_body(
            candidate.profiled_body, "B2C1B4 Fresh Protocol"
        )
        if (
            profile.internal_reference() != core_handle.profile_reference
            or candidate.profile_id.internal_reference()
            != core_handle.profile_reference
        ):
            _fail(
                "KindMismatch",
                "F0V2B2C1B4-K-PROTOCOL-PROFILE",
                "Protocol profile differs",
            )
        core_ref, interpretation = b2c0._record(domain, (0, 1), "Fresh Protocol")
        referenced_core = b2c0._content_ref(core_ref, "Protocol Core")
        if referenced_core.internal_reference() != core_handle.core_reference:
            _fail(
                "Refused",
                "F0V2B2C1B4-R-PROTOCOL-CORE",
                "Protocol names another Core",
            )
        interpretation_case, payload = b2c0._variant(
            interpretation, (0,), "Fresh interpretation"
        )
        if interpretation_case != 0:  # pragma: no cover - parser set closes this
            _fail("Refused", "F0V2B2C1B4-R-INTERPRETATION", "Protocol is not Fresh")
        b2c0._unit(payload, "Fresh payload")
        if (
            type(candidate.asserted_id) is not k1.TypedContentId
            or candidate.asserted_id.subject_kind != base.TARGET_PROTOCOL_KIND
        ):
            _fail(
                "KindMismatch",
                "F0V2B2C1B4-K-PROTOCOL-ID",
                "Protocol ID kind differs",
            )
        try:
            k1.authenticate_content_id(
                candidate.asserted_id,
                candidate.profiled_body,
                environment.prior_meta_preimages,
            )
        except Exception as error:
            _fail("Malformed", "F0V2B2C1B4-M-PROTOCOL-ID", str(error))
        closure = b2c0.snapshot_environment(environment)
        if closure.fingerprint != core_handle.closure.fingerprint:
            _fail("Refused", "F0V2B2C1B4-R-CLOSURE-PAIR", "closure differs")
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
            "F0V2B2C1B4-A-FRESH-ADMITTED",
            "Fresh Protocol is paired to this evaluator and exact Core",
            handle,
        )
    except FamilyFailure as error:
        return AdmissionResult(error.outcome, error.code, error.detail)
    except b2c0.SnapshotFailure as error:
        return AdmissionResult(error.outcome, error.code, error.detail)
    except Exception as error:  # pragma: no cover - fail-closed defect lane
        return AdmissionResult("CheckerFailure", "F0V2B2C1B4-CHECKER", str(error))


def _admitted_effect_value(effect: ModuleEffectRef) -> dict[str, str]:
    return {
        "module_body": k1.encode_datum(
            k1.BytesValue(effect.module.internal_reference())
        ).hex(),
        "declaration_body": k1.encode_datum(
            base.module_declaration_ref_datum(effect.declaration)
        ).hex(),
        "payload_body": k1.encode_datum(_module_payload_datum(effect.payload)).hex(),
    }


def _effect_value(effect: object) -> dict[str, Any]:
    if type(effect) is ModuleEffectRef:
        return foundation._v(7, _admitted_effect_value(effect))
    if type(effect) is base.TerminalEffect:
        return foundation._v(
            5, foundation._ordinal("terminal-ref-body-v0", effect.terminal)
        )
    _fail("Unsupported", "F0V2B2C1B4-U-EFFECT", "effect differs")
    raise AssertionError("unreachable")


def _module_move_value(
    effect: ModuleEffectRef, semantics: ModuleSemantics
) -> dict[str, Any]:
    if semantics.move_type is None:
        raise AssertionError("NoProverDecision has no legal move value")
    return foundation._v(
        2,
        {
            0: _admitted_effect_value(effect),
            1: foundation._value_type_body(semantics.move_type),
        },
    )


def project_views(core_handle: object, protocol_handle: object) -> dict[str, Any]:
    core, validation = _retained_core(core_handle)
    if (
        type(protocol_handle) is not b2c0.AdmittedFreshProtocolSnapshot
        or not protocol_handle._issued_by(b2c0._PROTOCOL_ISSUER)
        or protocol_handle.core_handle is not core_handle
        or protocol_handle.profile_reference != core_handle.profile_reference
        or protocol_handle.closure_fingerprint != core_handle.closure.fingerprint
        or protocol_handle.evaluator_fingerprint != EVALUATOR_FINGERPRINT
    ):
        _fail(
            "Refused",
            "F0V2B2C1B4-R-PROTOCOL-AUTHORITY",
            "Protocol authority differs",
        )
    core_id_value = k1.decode_content_reference(core_handle.core_reference)
    protocol_id_value = k1.decode_content_reference(protocol_handle.protocol_reference)
    core_atom = foundation._identifier("core-id-body-v0", core_id_value)
    protocol_atom = foundation._identifier("protocol-id-body-v0", protocol_id_value)
    graph, graph_evidence = _graph(core, validation)

    public_binding = {
        0: core_atom,
        1: [
            {
                0: foundation._ordinal("scope-ref-body-v0", 0),
                1: foundation._v(0),
                2: foundation._v(0),
                3: [foundation._ordinal("scope-ref-body-v0", 0)],
            }
        ],
        2: [
            {
                0: foundation._ordinal("binding-ref-body-v0", 0),
                1: foundation._ordinal("scope-ref-body-v0", 0),
                2: foundation._v(base.BindingClass.STATEMENT.value),
                3: foundation._value_ref(base.PublicInputRef(0)),
                4: foundation._value_type_body(core.public_inputs[0].value_type),
            }
        ],
    }

    decisions = [
        (occurrence_ref, occurrence, validation.module_semantics[occurrence_ref])
        for occurrence_ref, occurrence in enumerate(core.occurrences)
        if occurrence_ref in validation.module_semantics
        and validation.module_semantics[occurrence_ref].decision_class
        is not ModuleDecisionClass.NO_PROVER_DECISION
    ]
    decision_rows: list[dict[int, Any]] = []
    read_rows: list[dict[int, Any]] = []
    legal_rows: list[dict[int, Any]] = []
    for occurrence_ref, occurrence, semantics in decisions:
        move = _module_move_value(occurrence.effect, semantics)
        prior_decisions = [item for item in decisions if item[0] < occurrence_ref]
        decision_rows.append(
            {
                0: foundation._ordinal("decision-ref-body-v0", occurrence_ref),
                1: foundation._ordinal("occurrence-ref-body-v0", occurrence_ref),
                2: [foundation._ordinal("scope-ref-body-v0", 0)],
                3: foundation._guard_body(occurrence.guard),
                4: move,
                5: [
                    foundation._ordinal("decision-ref-body-v0", prior_ref)
                    for prior_ref, _prior_occurrence, _prior_semantics in prior_decisions
                ],
            }
        )
        read_rows.extend(
            (
                {
                    0: foundation._ordinal("decision-ref-body-v0", occurrence_ref),
                    1: foundation._v(
                        1, foundation._ordinal("public-input-ref-body-v0", 0)
                    ),
                    2: foundation._value_type_body(core.public_inputs[0].value_type),
                },
                {
                    0: foundation._ordinal("decision-ref-body-v0", occurrence_ref),
                    1: foundation._v(2, foundation._ordinal("binding-ref-body-v0", 0)),
                    2: foundation._value_type_body(core.public_inputs[0].value_type),
                },
            )
        )
        for prior_ref in range(occurrence_ref):
            prior_semantics = validation.module_semantics.get(prior_ref)
            if prior_semantics is None:
                continue
            for output_ordinal, output in enumerate(prior_semantics.outputs):
                if output.visibility in (
                    ModuleVisibility.PROVER_ONLY,
                    ModuleVisibility.PUBLIC,
                ):
                    read_rows.append(
                        {
                            0: foundation._ordinal(
                                "decision-ref-body-v0", occurrence_ref
                            ),
                            1: foundation._v(
                                8,
                                {
                                    0: foundation._ordinal(
                                        "occurrence-ref-body-v0", prior_ref
                                    ),
                                    1: output_ordinal,
                                },
                            ),
                            2: foundation._value_type_body(output.value_type),
                        }
                    )
        for prior_ref, _prior_occurrence, prior_semantics in prior_decisions:
            if prior_semantics.move_type is None:
                raise AssertionError("prior decision lacks move type")
            read_rows.append(
                {
                    0: foundation._ordinal("decision-ref-body-v0", occurrence_ref),
                    1: foundation._v(
                        9, foundation._ordinal("decision-ref-body-v0", prior_ref)
                    ),
                    2: foundation._value_type_body(prior_semantics.move_type),
                }
            )
        legal_rows.append(
            {0: foundation._ordinal("decision-ref-body-v0", occurrence_ref), 1: move}
        )
    read_rows.sort(key=lambda item: codec.encode_value(prior._READ_SCHEMA, item))
    strategy = {
        0: core_atom,
        1: decision_rows,
        2: foundation._law("core-admission-v0"),
        3: read_rows,
        4: legal_rows,
    }

    public_coin = {
        0: core_atom,
        1: graph,
        2: graph_evidence["eligible"],
        3: [],
        4: [],
    }

    value_rows: list[dict[int, Any]] = [
        {
            0: foundation._value_ref(base.PublicInputRef(0)),
            1: foundation._value_type_body(core.public_inputs[0].value_type),
            2: [],
        }
    ]
    occurrence_rows: list[dict[int, Any]] = []
    extension_rows: list[dict[int, Any]] = []
    for occurrence_ref, occurrence in enumerate(core.occurrences):
        occurrence_rows.append(
            {
                0: foundation._ordinal("occurrence-ref-body-v0", occurrence_ref),
                1: [foundation._ordinal("scope-ref-body-v0", 0)],
                2: foundation._guard_body(occurrence.guard),
                3: _effect_value(occurrence.effect),
                4: [
                    foundation._value_type_body(item)
                    for item in validation.outputs[occurrence_ref]
                ],
            }
        )
        if type(occurrence.effect) is ModuleEffectRef:
            semantics = validation.module_semantics[occurrence_ref]
            extension_rows.append(
                {
                    0: foundation._ordinal("occurrence-ref-body-v0", occurrence_ref),
                    1: _admitted_effect_value(occurrence.effect),
                }
            )
            for output_ordinal, output in enumerate(semantics.outputs):
                value_rows.append(
                    {
                        0: foundation._value_ref(
                            base.OccurrenceOutputRef(occurrence_ref, output_ordinal)
                        ),
                        1: foundation._value_type_body(output.value_type),
                        2: [
                            foundation._value_ref(item)
                            for item in _value_dependencies(
                                occurrence.effect,
                                output.dependencies,
                                occurrence_ref,
                            )
                        ],
                    }
                )
    terminal = core.terminals[0]
    terminal_rows = [
        {
            0: foundation._ordinal("terminal-ref-body-v0", 0),
            1: foundation._v(terminal.verdict.value),
            2: [],
            3: [],
            4: [],
            5: foundation._ordinal(
                "occurrence-ref-body-v0", validation.terminal_positions[0]
            ),
        }
    ]
    effect_view = {
        0: core_atom,
        1: occurrence_rows,
        2: value_rows,
        3: [],
        4: [],
        5: [],
        6: terminal_rows,
        7: extension_rows,
    }

    claim_reduction = {0: core_atom, 1: [], 2: [], 3: []}
    runtime = {
        0: [
            {
                0: foundation._ordinal("occurrence-ref-body-v0", occurrence_ref),
                1: [
                    foundation._value_type_body(item)
                    for item in validation.outputs[occurrence_ref]
                ],
            }
            for occurrence_ref in range(len(core.occurrences))
        ],
        1: [],
        2: [],
        3: [
            {
                0: foundation._ordinal("terminal-ref-body-v0", 0),
                1: foundation._ordinal(
                    "occurrence-ref-body-v0", validation.terminal_positions[0]
                ),
                2: foundation._v(terminal.verdict.value),
                3: [],
            }
        ],
    }
    execution = {
        0: protocol_atom,
        1: core_atom,
        2: foundation._v(0),
        3: foundation._law("core-admission-v0"),
        4: [],
        5: foundation._law("execution-and-replay-v0"),
        6: runtime,
        7: foundation._v(0),
        8: foundation._law("execution-and-replay-v0"),
        9: foundation._law("run-view-issuance-v0"),
    }
    return {
        "PublicBindingView": public_binding,
        "StrategyDecisionView": strategy,
        "PublicCoinView": public_coin,
        "EffectView": effect_view,
        "ClaimReductionView": claim_reduction,
        "ExecutionView": execution,
    }


def _environment(
    module: object,
    *,
    needs_reconstruction: bool,
) -> object:
    fixture = base.make_fixture()
    algorithm = identity_algorithm()
    contract = k1.DEFAULT_EVALUATION_CONTRACT
    return base.Environment(
        fixture.environment.profile_id,
        MappingProxyType(dict(fixture.environment.profile_preimages)),
        MappingProxyType({module.identity: module}),
        MappingProxyType(
            {algorithm.identity: algorithm} if needs_reconstruction else {}
        ),
        MappingProxyType(
            {algorithm.identity: MappingProxyType({})} if needs_reconstruction else {}
        ),
        MappingProxyType({contract.identity: contract} if needs_reconstruction else {}),
    )


def _assemble(
    module: object,
    declarations: tuple[int, ...],
    payloads: tuple[tuple[object, ...], ...],
    *,
    needs_reconstruction: bool,
) -> tuple[object, object]:
    if len(declarations) != len(payloads):
        raise AssertionError("fixture declaration and payload sequences differ")
    effects = tuple(
        base.OccurrenceDecl(
            0,
            base.AlwaysGuard(),
            ModuleEffectRef(
                module.identity,
                base.ModuleDeclarationRef(
                    module.identity, "pir.core-effect", declaration
                ),
                ModulePayload(payload),
            ),
        )
        for declaration, payload in zip(declarations, payloads, strict=True)
    )
    terminal = base.TerminalDecl(base.TerminalVerdict.ACCEPT, (), (), ())
    occurrences = (
        *effects,
        base.OccurrenceDecl(
            0,
            base.AlwaysGuard(),
            base.TerminalEffect(0),
        ),
    )
    core = base.InteractiveCore(
        (module.identity,),
        (base.InputDecl(base.Z3),),
        (),
        (),
        (),
        (base.ScopeDecl(None, None),),
        (
            base.PublicBindingDecl(
                0,
                base.BindingClass.STATEMENT,
                base.PublicInputRef(0),
            ),
        ),
        (),
        (),
        (),
        (),
        (),
        (terminal,),
        occurrences,
    )
    environment = _environment(module, needs_reconstruction=needs_reconstruction)
    return environment, make_candidate(core, environment.profile_id)


def fixtures() -> dict[str, tuple[object, object]]:
    module = extension_module()
    return {
        "module-no-decision": _assemble(
            module,
            (0,),
            ((base.PublicInputRef(0),),),
            needs_reconstruction=True,
        ),
        "module-prover-decision": _assemble(
            module,
            (1, 1),
            (
                (base.PublicInputRef(0),),
                (base.OccurrenceOutputRef(0, 0),),
            ),
            needs_reconstruction=False,
        ),
        "module-prover-publication": _assemble(
            module,
            (2,),
            ((base.PublicInputRef(0),),),
            needs_reconstruction=False,
        ),
    }


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


def retained_core(handle: object) -> object:
    return _retained_core(handle)[0]
