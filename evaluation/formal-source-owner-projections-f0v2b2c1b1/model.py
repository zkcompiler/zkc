#!/usr/bin/env python3
"""Reference owner evaluator and projector for the B2C1B1 foundation slice.

The slice covers four constructor-isolation families: verifier-private
dependency, constants and derived values, child scopes with nontrivial guards,
and deterministic Verifier messages.  It extends the B2C0 canonical-byte
admission substrate without defining a new semantic owner or target stage.
"""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import importlib.util
from pathlib import Path
import sys
from types import MappingProxyType, ModuleType
from typing import Any, Mapping


ROOT = Path(__file__).resolve().parents[2]
B2C0_MODEL = ROOT / "evaluation/formal-source-owner-admission-f0v2b2c0/model.py"
B2B_MODEL = ROOT / "evaluation/formal-source-view-schema-f0v2b2b/model.py"
B2C1A_MODEL = ROOT / "evaluation/formal-source-view-codec-f0v2b2c1a/model.py"
EVALUATOR_FINGERPRINT = hashlib.sha256(
    b"zkc.f0v2b2c1b1.foundation-owner-evaluator.v0"
).digest()


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


b2c0 = _load("_zkc_f0v2b2c1b1_b2c0", B2C0_MODEL)
b2b = _load("_zkc_f0v2b2c1b1_b2b", B2B_MODEL)
codec = _load("_zkc_f0v2b2c1b1_codec", B2C1A_MODEL)
base = b2c0.base
k1 = b2c0.k1
VIEW_SCHEMAS, _VIEW_OWNERS, _VIEW_SCHEMA_STATS = b2b.compile_current()
_PUBLIC_COIN_SCHEMA = VIEW_SCHEMAS["PublicCoinView"]
_PC_GRAPH_SCHEMA = codec.record_field(_PUBLIC_COIN_SCHEMA, 1)
_PC_NODE_SCHEMA = codec.record_field(_PC_GRAPH_SCHEMA, 0)["element"]
_PC_EDGE_SCHEMA = codec.record_field(_PC_GRAPH_SCHEMA, 1)["element"]


class FamilyFailure(ValueError):
    """One classified failure in the bounded B2C1B1 owner evaluator."""

    def __init__(self, outcome: str, code: str, detail: str) -> None:
        super().__init__(detail)
        self.outcome = outcome
        self.code = code
        self.detail = detail


@dataclass(frozen=True, slots=True)
class FamilyAdmissionResult:
    outcome: str
    code: str
    detail: str
    handle: object | None = None


@dataclass(frozen=True, slots=True)
class VerifierMessageEffect:
    channel: object
    algorithm: object
    evaluation_contract: object
    inputs: tuple[object, ...]
    payload_type: object


def _fail(outcome: str, code: str, detail: str) -> None:
    raise FamilyFailure(outcome, code, detail)


def _record(*values: object) -> object:
    return k1.DatumRecord(
        tuple((ordinal, value) for ordinal, value in enumerate(values))
    )


def _seq(values: tuple[object, ...]) -> object:
    return k1.DatumSeq(values)


def _variant(case: int, payload: object = k1.UNIT) -> object:
    return k1.DatumVariant(case, payload)


def _effect_datum(effect: object) -> object:
    if type(effect) is VerifierMessageEffect:
        return _variant(
            1,
            _record(
                base.module_declaration_ref_datum(effect.channel),
                k1.BytesValue(effect.algorithm.internal_reference()),
                k1.BytesValue(effect.evaluation_contract.internal_reference()),
                _seq(tuple(base.value_ref_datum(value) for value in effect.inputs)),
                k1.value_type_datum(effect.payload_type),
            ),
        )
    return base._effect_datum(effect)


def core_domain_datum(core: object) -> object:
    """Encode the exact Appendix-A Core body for the supported foundation slice."""

    if type(core) is not base.InteractiveCore:
        raise k1.ModelError("foundation Core has another carrier")
    return _record(
        _seq(
            tuple(
                k1.BytesValue(module.internal_reference())
                for module in core.used_modules
            )
        ),
        _seq(tuple(base._input_datum(item) for item in core.public_inputs)),
        _seq(tuple(base._input_datum(item) for item in core.verifier_private_inputs)),
        _seq(tuple(base._constant_datum(item) for item in core.constants)),
        _seq(tuple(base._derived_datum(item) for item in core.derived_values)),
        _seq(tuple(base._scope_datum(item) for item in core.scopes)),
        _seq(tuple(base._binding_datum(item) for item in core.public_bindings)),
        _seq(tuple(base._challenge_datum(item) for item in core.challenges)),
        _seq(tuple(item for item in core.oracles)),
        _seq(tuple(base._check_datum(item) for item in core.checks)),
        _seq(tuple(base._claim_datum(item) for item in core.claims)),
        _seq(tuple(item for item in core.reductions)),
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
        return VerifierMessageEffect(
            b2c0._decode_module_ref(channel),
            b2c0._content_ref(algorithm, "Verifier-message algorithm"),
            b2c0._content_ref(contract, "Verifier-message contract"),
            tuple(
                b2c0._decode_value_ref(item)
                for item in b2c0._sequence(inputs, "Verifier-message inputs")
            ),
            b2c0._decode_value_type(payload_type),
        )
    if case == 5:
        return base.TerminalEffect(b2c0._nat(payload, "terminal backlink"))
    _fail(
        "Unsupported",
        "F0V2B2C1B1-U-EFFECT",
        f"Core effect tag {case} belongs to another B2C1B slice",
    )
    raise AssertionError("unreachable")


def decode_core(domain: object) -> object:
    """Strictly decode supported exact Core bytes to an alias-free frozen carrier."""

    fields = b2c0._record(domain, tuple(range(14)), "InteractiveCore")
    sequences = tuple(
        b2c0._sequence(value, f"InteractiveCore field {ordinal}")
        for ordinal, value in enumerate(fields)
    )
    if any(sequences[index] for index in (7, 8, 9, 10, 11)):
        _fail(
            "Unsupported",
            "F0V2B2C1B1-U-OTHER-SLICE",
            "challenge, Oracle, check, claim, and reduction families are outside B2C1B1",
        )
    used_modules = tuple(
        b2c0._content_ref(item, "used module") for item in sequences[0]
    )
    public_inputs = tuple(
        base.InputDecl(
            b2c0._decode_value_type(b2c0._record(item, (0,), "public input")[0])
        )
        for item in sequences[1]
    )
    private_inputs = tuple(
        base.InputDecl(
            b2c0._decode_value_type(
                b2c0._record(item, (0,), "verifier-private input")[0]
            )
        )
        for item in sequences[2]
    )
    constants: list[object] = []
    for item in sequences[3]:
        value_type, datum = b2c0._record(item, (0, 1), "typed constant")
        decoded_type = b2c0._decode_value_type(value_type)
        try:
            admitted = k1.admit_value(decoded_type, datum)
        except Exception as error:
            _fail("Refused", "F0V2B2C1B1-R-CONSTANT", str(error))
        constants.append(base.TypedConstantDecl(decoded_type, admitted))
    derived_values: list[object] = []
    for item in sequences[4]:
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
    for item in sequences[5]:
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
                else b2c0._nat(opening_payload, "scope opening occurrence"),
            )
        )
    bindings: list[object] = []
    for item in sequences[6]:
        scope, binding_class, value = b2c0._record(item, (0, 1, 2), "public binding")
        class_case, class_payload = b2c0._variant(
            binding_class, (0, 1, 2), "binding class"
        )
        b2c0._unit(class_payload, "binding-class payload")
        bindings.append(
            base.PublicBindingDecl(
                b2c0._nat(scope, "binding scope"),
                base.BindingClass(class_case),
                b2c0._decode_value_ref(value),
            )
        )
    terminals: list[object] = []
    for item in sequences[12]:
        verdict, outputs, checks, dispositions = b2c0._record(
            item, (0, 1, 2, 3), "terminal"
        )
        verdict_case, verdict_payload = b2c0._variant(
            verdict, (0, 1, 2), "terminal verdict"
        )
        b2c0._unit(verdict_payload, "terminal-verdict payload")
        if b2c0._sequence(checks, "terminal checks") or b2c0._sequence(
            dispositions, "terminal dispositions"
        ):
            _fail(
                "Unsupported",
                "F0V2B2C1B1-U-TERMINAL-CLOSURE",
                "checks and claim dispositions belong to later B2C1B slices",
            )
        terminals.append(
            base.TerminalDecl(
                base.TerminalVerdict(verdict_case),
                tuple(
                    b2c0._decode_value_ref(value)
                    for value in b2c0._sequence(outputs, "terminal outputs")
                ),
                (),
                (),
            )
        )
    occurrences: list[object] = []
    for item in sequences[13]:
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
        (),
        (),
        (),
        (),
        (),
        tuple(terminals),
        tuple(occurrences),
    )


def _ordinary_references(core: object) -> tuple[tuple[object, ...], tuple[object, ...]]:
    algorithms: set[object] = set()
    contracts: set[object] = set()
    for item in core.derived_values:
        algorithms.add(item.algorithm)
        contracts.add(item.evaluation_contract)
    for occurrence in core.occurrences:
        if type(occurrence.guard) is base.EvaluateGuard:
            algorithms.add(occurrence.guard.algorithm)
            contracts.add(occurrence.guard.evaluation_contract)
        if type(occurrence.effect) is VerifierMessageEffect:
            algorithms.add(occurrence.effect.algorithm)
            contracts.add(occurrence.effect.evaluation_contract)

    def key(item: object) -> bytes:
        return item.internal_reference()

    return tuple(sorted(algorithms, key=key)), tuple(sorted(contracts, key=key))


def _module_references(core: object) -> tuple[object, ...]:
    return tuple(
        occurrence.effect.channel
        for occurrence in core.occurrences
        if type(occurrence.effect) in (base.ProverMessageEffect, VerifierMessageEffect)
    )


def _authenticate_algorithms(
    core: object, environment: object
) -> Mapping[object, object]:
    algorithm_ids, contract_ids = _ordinary_references(core)
    if set(environment.algorithm_preimages) != set(algorithm_ids):
        _fail(
            "Refused",
            "F0V2B2C1B1-R-EXACT-ALGORITHMS",
            "algorithm closure is missing or contains unused preimages",
        )
    if set(environment.contract_preimages) != set(contract_ids):
        _fail(
            "Refused",
            "F0V2B2C1B1-R-EXACT-CONTRACTS",
            "contract closure is missing or contains unused preimages",
        )
    function_types: dict[object, object] = {}
    ledger = k1.AuthenticationLedger()
    try:
        for identifier in algorithm_ids:
            algorithm = environment.algorithm_preimages[identifier]
            if (
                k1.authenticate_algorithm_identity(algorithm, ledger=ledger)
                != identifier
            ):
                _fail(
                    "Refused",
                    "F0V2B2C1B1-R-ALGORITHM-ID",
                    "algorithm identity differs from its reference",
                )
            modules = environment.algorithm_modules.get(identifier)
            if modules is None:
                _fail(
                    "MissingDependency",
                    "F0V2B2C1B1-D-ALGORITHM-MODULES",
                    "algorithm module closure is missing",
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
            function_types[identifier] = algorithm.function_type
        for identifier in contract_ids:
            contract = environment.contract_preimages[identifier]
            if contract.identity != identifier:
                _fail(
                    "Refused",
                    "F0V2B2C1B1-R-CONTRACT-ID",
                    "evaluation-contract identity differs from its reference",
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
        outcome = getattr(getattr(error, "outcome", None), "value", None)
        _fail(outcome or "Refused", "F0V2B2C1B1-R-DEPENDENCY", str(error))
    return MappingProxyType(function_types)


def _value_output_types(core: object) -> tuple[tuple[object, ...], ...]:
    result: list[tuple[object, ...]] = []
    for occurrence in core.occurrences:
        effect = occurrence.effect
        if type(effect) is base.ProverMessageEffect:
            result.append((effect.payload_type,))
        elif type(effect) is VerifierMessageEffect:
            result.append((effect.payload_type,))
        elif type(effect) is base.TerminalEffect:
            result.append(())
        else:
            _fail(
                "Unsupported",
                "F0V2B2C1B1-U-EFFECT",
                "occurrence effect belongs to another isolation slice",
            )
    return tuple(result)


def _value_type(
    core: object, outputs: tuple[tuple[object, ...], ...], ref: object
) -> object:
    if type(ref) is base.PublicInputRef:
        table = core.public_inputs
        ordinal = ref.ordinal
    elif type(ref) is base.VerifierPrivateInputRef:
        table = core.verifier_private_inputs
        ordinal = ref.ordinal
    elif type(ref) is base.ConstantRef:
        table = core.constants
        ordinal = ref.ordinal
    elif type(ref) is base.DerivedValueRef:
        table = core.derived_values
        ordinal = ref.ordinal
    elif type(ref) is base.OccurrenceOutputRef:
        if not 0 <= ref.occurrence < len(outputs):
            _fail("Refused", "F0V2B2C1B1-R-VALUE-REF", "occurrence is absent")
        values = outputs[ref.occurrence]
        if not 0 <= ref.output_ordinal < len(values):
            _fail("Refused", "F0V2B2C1B1-R-VALUE-REF", "output is absent")
        return values[ref.output_ordinal]
    else:
        _fail("Malformed", "F0V2B2C1B1-M-VALUE-REF", "unknown ValueRef carrier")
    if not 0 <= ordinal < len(table):
        _fail("Refused", "F0V2B2C1B1-R-VALUE-REF", "value ordinal is absent")
    item = table[ordinal]
    return item.result_type if type(ref) is base.DerivedValueRef else item.value_type


def _guard_implies(use: object, source: object) -> bool:
    return type(source) is base.AlwaysGuard or use == source


def _validate_core(
    core: object, environment: object, function_types: Mapping[object, object]
) -> tuple[tuple[object, ...], ...]:
    if not core.scopes or not core.occurrences or not core.terminals:
        _fail(
            "Refused",
            "F0V2B2C1B1-R-NONEMPTY",
            "scopes, occurrences, and terminals must be nonempty",
        )
    module_refs = _module_references(core)
    direct = tuple(
        sorted(
            {item.module for item in module_refs},
            key=lambda item: item.internal_reference(),
        )
    )
    if core.used_modules != direct:
        _fail(
            "Refused",
            "F0V2B2C1B1-R-EXACT-USED-MODULES",
            "used_modules differs from the direct owner-module set",
        )
    for reference in module_refs:
        try:
            base._validate_nominal(reference, "pir.message-channel", environment)
        except base.AdmissionFailure as error:
            _fail(error.outcome, error.code, error.detail)

    all_types = [
        *(item.value_type for item in core.public_inputs),
        *(item.value_type for item in core.verifier_private_inputs),
        *(item.value_type for item in core.constants),
        *(item.result_type for item in core.derived_values),
        *(
            occurrence.effect.payload_type
            for occurrence in core.occurrences
            if type(occurrence.effect)
            in (base.ProverMessageEffect, VerifierMessageEffect)
        ),
    ]
    try:
        for value_type in all_types:
            value_type.__post_init__()
            k1.authenticate_value_type_reference(
                value_type,
                dict(environment.module_preimages),
                semantic_regime=k1.SEMANTIC_REGIME_ID,
            )
    except Exception as error:
        _fail("KindMismatch", "F0V2B2C1B1-K-VALUE-TYPE", str(error))

    outputs = _value_output_types(core)
    available: set[object] = {
        *(base.PublicInputRef(index) for index in range(len(core.public_inputs))),
        *(
            base.VerifierPrivateInputRef(index)
            for index in range(len(core.verifier_private_inputs))
        ),
        *(base.ConstantRef(index) for index in range(len(core.constants))),
    }
    for ordinal, derived in enumerate(core.derived_values):
        if any(item not in available for item in derived.inputs):
            _fail(
                "Refused",
                "F0V2B2C1B1-R-DERIVED-ORDER",
                "derived value reads a future or absent predecessor",
            )
        observed = tuple(_value_type(core, outputs, ref) for ref in derived.inputs)
        function_type = function_types[derived.algorithm]
        if (
            observed != function_type.inputs
            or derived.result_type != function_type.output
            or function_type.failures
        ):
            _fail(
                "KindMismatch",
                "F0V2B2C1B1-K-DERIVED-ABI",
                "derived algorithm ABI is not exact, total, and failure-free",
            )
        available.add(base.DerivedValueRef(ordinal))

    if core.scopes[0] != base.ScopeDecl(None, None):
        _fail(
            "Refused",
            "F0V2B2C1B1-R-ROOT-SCOPE",
            "scope zero is not the unique initial root",
        )
    opening_positions = [-1]
    depths = [0]
    for ordinal, scope in enumerate(core.scopes[1:], start=1):
        if scope.parent is None or not 0 <= scope.parent < ordinal:
            _fail(
                "Refused",
                "F0V2B2C1B1-R-SCOPE-PARENT",
                "scope parent does not precede its child",
            )
        if scope.opening is None or not 0 <= scope.opening < len(core.occurrences):
            _fail(
                "Refused",
                "F0V2B2C1B1-R-SCOPE-OPENING",
                "child scope has no exact opening boundary",
            )
        depth = depths[scope.parent] + 1
        if depth > 384:
            _fail(
                "DeterministicLimitExceeded",
                "F0V2B2C1B1-L-SCOPE-DEPTH",
                "scope depth exceeds the target bound",
            )
        if scope.opening < opening_positions[scope.parent]:
            _fail(
                "Refused",
                "F0V2B2C1B1-R-SCOPE-OPENING",
                "child scope opens before its parent",
            )
        opening_positions.append(scope.opening)
        depths.append(depth)
        members = [
            index
            for index, occurrence in enumerate(core.occurrences)
            if occurrence.scope == ordinal
        ]
        if not members or scope.opening > members[0]:
            _fail(
                "Refused",
                "F0V2B2C1B1-R-SCOPE-OPENING",
                "child scope opens after its first member",
            )

    bound_public: set[int] = set()
    triples: set[tuple[object, ...]] = set()
    for binding in core.public_bindings:
        if not 0 <= binding.scope < len(core.scopes):
            _fail("Refused", "F0V2B2C1B1-R-SCOPE-REF", "binding scope is absent")
        _value_type(core, outputs, binding.value)
        if type(binding.value) is base.VerifierPrivateInputRef:
            _fail(
                "Refused",
                "F0V2B2C1B1-R-PRIVATE-BINDING",
                "verifier-private input cannot be publicly bound",
            )
        if type(binding.value) is base.OccurrenceOutputRef:
            opening = opening_positions[binding.scope]
            source = binding.value.occurrence
            if (
                opening < 0
                or source >= opening
                or type(core.occurrences[source].guard) is not base.AlwaysGuard
            ):
                _fail(
                    "Refused",
                    "F0V2B2C1B1-R-BINDING-AVAILABILITY",
                    "scope binding is not unconditionally available before opening",
                )
        if type(binding.value) is base.PublicInputRef:
            bound_public.add(binding.value.ordinal)
        triple = (binding.scope, binding.binding_class, binding.value)
        if triple in triples:
            _fail(
                "Refused",
                "F0V2B2C1B1-R-DUPLICATE-BINDING",
                "public binding triple is duplicated",
            )
        triples.add(triple)
    if bound_public != set(range(len(core.public_inputs))):
        _fail(
            "Refused",
            "F0V2B2C1B1-R-BINDING-COMPLETENESS",
            "public inputs do not have complete binding coverage",
        )

    terminal_positions: dict[int, list[int]] = {
        index: [] for index in range(len(core.terminals))
    }
    source_guards: dict[object, object] = {}
    for index, occurrence in enumerate(core.occurrences):
        if not 0 <= occurrence.scope < len(core.scopes):
            _fail("Refused", "F0V2B2C1B1-R-SCOPE-REF", "occurrence scope is absent")
        if opening_positions[occurrence.scope] > index:
            _fail(
                "Refused",
                "F0V2B2C1B1-R-SCOPE-OPENING",
                "occurrence precedes its active scope",
            )
        reads: tuple[object, ...] = ()
        if type(occurrence.guard) is base.EvaluateGuard:
            reads += occurrence.guard.inputs
            observed = tuple(_value_type(core, outputs, ref) for ref in reads)
            function_type = function_types[occurrence.guard.algorithm]
            if (
                observed != function_type.inputs
                or function_type.output != k1.BOOL
                or function_type.failures
            ):
                _fail(
                    "KindMismatch",
                    "F0V2B2C1B1-K-GUARD-ABI",
                    "guard ABI is not exact total Boolean",
                )
        elif type(occurrence.guard) is not base.AlwaysGuard:
            _fail("Malformed", "F0V2B2C1B1-M-GUARD", "unknown guard carrier")
        effect = occurrence.effect
        if type(effect) is VerifierMessageEffect:
            reads += effect.inputs
            observed = tuple(_value_type(core, outputs, ref) for ref in effect.inputs)
            function_type = function_types[effect.algorithm]
            if (
                observed != function_type.inputs
                or effect.payload_type != function_type.output
                or function_type.failures
            ):
                _fail(
                    "KindMismatch",
                    "F0V2B2C1B1-K-VERIFIER-MESSAGE-ABI",
                    "Verifier message ABI is not exact, total, and failure-free",
                )
        elif type(effect) is base.TerminalEffect:
            if not 0 <= effect.terminal < len(core.terminals):
                _fail(
                    "Refused",
                    "F0V2B2C1B1-R-TERMINAL-REF",
                    "terminal backlink is absent",
                )
            terminal_positions[effect.terminal].append(index)
            reads += core.terminals[effect.terminal].public_outputs
        elif type(effect) is not base.ProverMessageEffect:
            _fail("Unsupported", "F0V2B2C1B1-U-EFFECT", "unsupported effect")
        if any(ref not in available for ref in reads):
            _fail(
                "Refused",
                "F0V2B2C1B1-R-VALUE-AVAILABILITY",
                "occurrence reads a future or absent value",
            )
        for ref in reads:
            source = source_guards.get(ref)
            if source is not None and not _guard_implies(occurrence.guard, source):
                _fail(
                    "Refused",
                    "F0V2B2C1B1-R-GUARD-IMPLIES",
                    "a conditional value use does not imply its source guard",
                )
        for output in range(len(outputs[index])):
            ref = base.OccurrenceOutputRef(index, output)
            available.add(ref)
            source_guards[ref] = occurrence.guard
    if any(len(positions) != 1 for positions in terminal_positions.values()):
        _fail(
            "Refused",
            "F0V2B2C1B1-R-TERMINAL-BACKLINK",
            "terminal occurrence backlinks are not one-to-one",
        )
    final = core.occurrences[-1]
    if (
        type(final.guard) is not base.AlwaysGuard
        or type(final.effect) is not base.TerminalEffect
    ):
        _fail(
            "Refused",
            "F0V2B2C1B1-R-FINAL-FALLBACK",
            "final occurrence is not an unconditional terminal",
        )
    return outputs


def admit_core(candidate: object, environment: object) -> FamilyAdmissionResult:
    try:
        if type(candidate) is not b2c0.CanonicalCoreCandidate:
            _fail("Malformed", "F0V2B2C1B1-M-REQUEST", "Core request is malformed")
        if type(environment) is not base.Environment:
            _fail("Malformed", "F0V2B2C1B1-M-ENVIRONMENT", "environment is malformed")
        if candidate.profile_id != environment.profile_id:
            _fail(
                "KindMismatch",
                "F0V2B2C1B1-K-REQUEST-PROFILE",
                "candidate and environment profiles differ",
            )
        if environment.profile_id != base.target_profile_id():
            _fail(
                "KindMismatch",
                "F0V2B2C1B1-K-TARGET-PROFILE",
                "evaluator accepts only Interaction revision 0",
            )
        profile, domain, domain_body = b2c0._strict_profiled_body(
            candidate.profiled_body, "B2C1B1 Core"
        )
        if profile != candidate.profile_id:
            _fail(
                "KindMismatch",
                "F0V2B2C1B1-K-BODY-PROFILE",
                "Core body and request profiles differ",
            )
        if (
            type(candidate.asserted_id) is not k1.TypedContentId
            or candidate.asserted_id.subject_kind != base.TARGET_CORE_KIND
        ):
            _fail("KindMismatch", "F0V2B2C1B1-K-CORE-ID", "Core ID kind differs")
        try:
            k1.authenticate_content_id(
                candidate.asserted_id,
                candidate.profiled_body,
                environment.prior_meta_preimages,
            )
        except Exception as error:
            _fail("Malformed", "F0V2B2C1B1-M-CORE-ID", str(error))
        core = decode_core(domain)
        closure = b2c0.snapshot_environment(environment)
        function_types = _authenticate_algorithms(core, environment)
        outputs = _validate_core(core, environment, function_types)
        _graph_value, graph_evidence = _graph(core, outputs)
        if any(
            graph_evidence["classes"][(5, ordinal)] not in (0, 1)
            for ordinal in range(len(core.public_bindings))
        ):
            _fail(
                "Refused",
                "F0V2B2C1B1-R-PRIVATE-BINDING",
                "a public binding depends on verifier-private or invalid data",
            )
        summary = (
            ("slice", "F0-V2B2C1B1"),
            ("core", core),
            ("output_types", outputs),
            ("occurrences", len(core.occurrences)),
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
        return FamilyAdmissionResult(
            "Affirmative",
            "F0V2B2C1B1-A-CORE-ADMITTED",
            "exact bytes passed the supported ten-stage foundation slice",
            handle,
        )
    except FamilyFailure as error:
        return FamilyAdmissionResult(error.outcome, error.code, error.detail)
    except b2c0.SnapshotFailure as error:
        return FamilyAdmissionResult(error.outcome, error.code, error.detail)
    except Exception as error:  # pragma: no cover - fail-closed defect lane
        return FamilyAdmissionResult("CheckerFailure", "F0V2B2C1B1-CHECKER", str(error))


def admit_fresh_protocol(
    core_handle: object, candidate: object, environment: object
) -> FamilyAdmissionResult:
    """Form Fresh Protocol authority under this extended owner evaluator."""

    try:
        _retained_core(core_handle)
        if type(candidate) is not b2c0.CanonicalFreshProtocolCandidate:
            _fail(
                "Malformed",
                "F0V2B2C1B1-M-PROTOCOL-REQUEST",
                "Protocol request has another carrier",
            )
        if type(environment) is not base.Environment:
            _fail(
                "Malformed",
                "F0V2B2C1B1-M-ENVIRONMENT",
                "environment is malformed",
            )
        if candidate.profile_id != environment.profile_id:
            _fail(
                "KindMismatch",
                "F0V2B2C1B1-K-PROTOCOL-PROFILE",
                "Protocol request and environment profiles differ",
            )
        profile, domain, _domain_body = b2c0._strict_profiled_body(
            candidate.profiled_body, "B2C1B1 Protocol"
        )
        if (
            profile.internal_reference() != core_handle.profile_reference
            or candidate.profile_id.internal_reference()
            != core_handle.profile_reference
        ):
            _fail(
                "KindMismatch",
                "F0V2B2C1B1-K-PROTOCOL-PROFILE",
                "Fresh Protocol and admitted Core profiles differ",
            )
        core_ref, interpretation = b2c0._record(domain, (0, 1), "B2C1B1 Fresh Protocol")
        referenced_core = b2c0._content_ref(core_ref, "Protocol Core")
        if referenced_core.internal_reference() != core_handle.core_reference:
            _fail(
                "Refused",
                "F0V2B2C1B1-R-PROTOCOL-CORE",
                "Fresh Protocol cites another admitted Core",
            )
        tag, payload = b2c0._variant(interpretation, (0,), "Fresh interpretation")
        assert tag == 0
        b2c0._unit(payload, "Fresh interpretation payload")
        if (
            type(candidate.asserted_id) is not k1.TypedContentId
            or candidate.asserted_id.subject_kind != base.TARGET_PROTOCOL_KIND
        ):
            _fail(
                "KindMismatch",
                "F0V2B2C1B1-K-PROTOCOL-ID",
                "Protocol ID has another kind",
            )
        try:
            k1.authenticate_content_id(
                candidate.asserted_id,
                candidate.profiled_body,
                environment.prior_meta_preimages,
            )
        except Exception as error:
            _fail("Malformed", "F0V2B2C1B1-M-PROTOCOL-ID", str(error))
        closure = b2c0.snapshot_environment(environment)
        if closure.fingerprint != core_handle.closure.fingerprint:
            _fail(
                "Refused",
                "F0V2B2C1B1-R-CLOSURE-PAIR",
                "Fresh formation closure differs from the admitted Core closure",
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
        return FamilyAdmissionResult(
            "Affirmative",
            "F0V2B2C1B1-A-FRESH-ADMITTED",
            "Fresh Protocol formed over this evaluator's exact Core and closure",
            handle,
        )
    except FamilyFailure as error:
        return FamilyAdmissionResult(error.outcome, error.code, error.detail)
    except b2c0.SnapshotFailure as error:
        return FamilyAdmissionResult(error.outcome, error.code, error.detail)
    except Exception as error:  # pragma: no cover - fail-closed defect lane
        return FamilyAdmissionResult("CheckerFailure", "F0V2B2C1B1-CHECKER", str(error))


def _retained_core(handle: object) -> tuple[object, tuple[tuple[object, ...], ...]]:
    if (
        type(handle) is not b2c0.AdmittedCoreSnapshot
        or not handle._issued_by(b2c0._CORE_ISSUER)
        or handle.evaluator_fingerprint != EVALUATOR_FINGERPRINT
    ):
        _fail(
            "Refused",
            "F0V2B2C1B1-R-CORE-AUTHORITY",
            "projection requires this evaluator's exact live Core snapshot",
        )
    summary = dict(handle.structural_summary)
    if (
        summary.get("slice") != "F0-V2B2C1B1"
        or type(summary.get("core")) is not base.InteractiveCore
    ):
        _fail(
            "Refused",
            "F0V2B2C1B1-R-RETAINED-FACTS",
            "admitted snapshot lacks the exact retained foundation facts",
        )
    core = summary["core"]
    profile = k1.decode_content_reference(handle.profile_reference)
    if core_profiled_body(core, profile) != handle.profiled_body:
        _fail(
            "Refused",
            "F0V2B2C1B1-R-RETAINED-BODY",
            "retained facts do not reproduce the admitted canonical body",
        )
    outputs = summary["output_types"]
    return core, outputs


def _body(compiler_name: str, datum: object) -> dict[str, str]:
    return {"compiler": compiler_name, "body": k1.encode_datum(datum).hex()}


def _ordinal(compiler_name: str, value: int) -> dict[str, str]:
    return _body(compiler_name, k1.Nat(value))


def _identifier(compiler_name: str, value: object) -> dict[str, str]:
    return _body(compiler_name, k1.BytesValue(value.internal_reference()))


def _value_ref(value: object) -> dict[str, str]:
    return _body("value-ref-body-v0", base.value_ref_datum(value))


def _value_type_body(value: object) -> dict[str, str]:
    return _body("value-type-body-v0", k1.value_type_datum(value))


def _module_ref(value: object) -> dict[str, str]:
    return _body(
        "module-declaration-ref-body-v0", base.module_declaration_ref_datum(value)
    )


def _guard_body(value: object) -> dict[str, str]:
    return _body("guard-body-v0", base._guard_datum(value))


def _law(name: str) -> dict[str, str]:
    return {
        "profile": b2b.PROFILE["profile_digest"],
        "kind": "pir.semantic-law",
        "name": name,
    }


def _v(case: int, value: Any = None) -> dict[str, Any]:
    return {"case": case, "value": value}


def _scope_paths(core: object) -> tuple[tuple[int, ...], ...]:
    paths: list[tuple[int, ...]] = []
    for ordinal, scope in enumerate(core.scopes):
        trail: list[int] = []
        current: int | None = ordinal
        while current is not None:
            trail.append(current)
            current = core.scopes[current].parent
        paths.append(tuple(reversed(trail)))
    return tuple(paths)


def _producer_node(ref: object) -> tuple[int, ...]:
    if type(ref) is base.PublicInputRef:
        return (0, ref.ordinal)
    if type(ref) is base.VerifierPrivateInputRef:
        return (1, ref.ordinal)
    if type(ref) is base.ConstantRef:
        return (2, ref.ordinal)
    if type(ref) is base.DerivedValueRef:
        return (3, ref.ordinal)
    if type(ref) is base.OccurrenceOutputRef:
        return (8, ref.occurrence, ref.output_ordinal)
    raise FamilyFailure("Malformed", "F0V2B2C1B1-M-VALUE-REF", "unknown producer")


def _pc_value(node: tuple[int, ...]) -> dict[str, Any]:
    tag, *arguments = node
    if tag in (8, 12, 13):
        return _v(
            tag,
            {
                0: _ordinal("occurrence-ref-body-v0", arguments[0]),
                1: arguments[1],
            },
        )
    compiler_name = {
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
    if compiler_name is None or len(arguments) != 1:
        raise FamilyFailure("Malformed", "F0V2B2C1B1-M-PCNODE", "unknown PCNode")
    return _v(tag, _ordinal(compiler_name, arguments[0]))


def _pc_key(node: tuple[int, ...]) -> bytes:
    return codec.encode_value(_PC_NODE_SCHEMA, _pc_value(node))


def _edge_value(pair: tuple[tuple[int, ...], tuple[int, ...]]) -> dict[int, Any]:
    return {0: _pc_value(pair[0]), 1: _pc_value(pair[1])}


def _edge_key(pair: tuple[tuple[int, ...], tuple[int, ...]]) -> bytes:
    return codec.encode_value(_PC_EDGE_SCHEMA, _edge_value(pair))


def _graph(
    core: object, outputs: tuple[tuple[object, ...], ...]
) -> tuple[dict[int, Any], dict[str, Any]]:
    nodes: set[tuple[int, ...]] = set()
    edges: set[tuple[tuple[int, ...], tuple[int, ...]]] = set()

    def add(node: tuple[int, ...]) -> tuple[int, ...]:
        nodes.add(node)
        return node

    def edge(source: tuple[int, ...], target: tuple[int, ...]) -> None:
        add(source)
        add(target)
        edges.add((source, target))

    for ordinal in range(len(core.public_inputs)):
        add((0, ordinal))
    for ordinal in range(len(core.verifier_private_inputs)):
        add((1, ordinal))
    for ordinal in range(len(core.constants)):
        add((2, ordinal))
    for ordinal, item in enumerate(core.derived_values):
        target = add((3, ordinal))
        for source in item.inputs:
            edge(_producer_node(source), target)
    for ordinal, scope in enumerate(core.scopes):
        target = add((4, ordinal))
        if scope.parent is not None:
            edge((4, scope.parent), target)
    for ordinal, binding in enumerate(core.public_bindings):
        target = add((5, ordinal))
        edge((4, binding.scope), target)
        edge(_producer_node(binding.value), target)

    terminal_positions: dict[int, int] = {}
    prior_terminals: list[tuple[int, ...]] = []
    for occurrence_ref, occurrence in enumerate(core.occurrences):
        activity = add((6, occurrence_ref))
        effect_node = add((7, occurrence_ref))
        edge((4, occurrence.scope), activity)
        if type(occurrence.guard) is base.EvaluateGuard:
            for value in occurrence.guard.inputs:
                edge(_producer_node(value), activity)
        for terminal in prior_terminals:
            edge(terminal, activity)
        edge(activity, effect_node)
        effect = occurrence.effect
        if type(effect) is VerifierMessageEffect:
            for value in effect.inputs:
                edge(_producer_node(value), effect_node)
        elif type(effect) is base.TerminalEffect:
            for value in core.terminals[effect.terminal].public_outputs:
                edge(_producer_node(value), effect_node)
            terminal = add((11, effect.terminal))
            edge(effect_node, terminal)
            terminal_positions[effect.terminal] = occurrence_ref
            prior_terminals.append(terminal)
        for output in range(len(outputs[occurrence_ref])):
            edge(effect_node, (8, occurrence_ref, output))

    incoming = {node: set() for node in nodes}
    outgoing = {node: set() for node in nodes}
    for source, target in edges:
        incoming[target].add(source)
        outgoing[source].add(target)
    remaining = {node: set(values) for node, values in incoming.items()}
    available = sorted((node for node in nodes if not remaining[node]), key=_pc_key)
    topological: list[tuple[int, ...]] = []
    while available:
        node = available.pop(0)
        topological.append(node)
        for target in outgoing[node]:
            remaining[target].remove(node)
            if (
                not remaining[target]
                and target not in topological
                and target not in available
            ):
                available.append(target)
        available.sort(key=_pc_key)
    if len(topological) != len(nodes):
        _fail("Refused", "F0V2B2C1B1-R-PCGRAPH-CYCLE", "PCGraph is cyclic")

    classes: dict[tuple[int, ...], int] = {}
    for node in topological:
        joined = max((classes[parent] for parent in incoming[node]), default=0)
        if node[0] == 1:
            value = 2
        elif node[0] in (0, 2):
            value = 0
        elif node[0] == 7:
            effect = core.occurrences[node[1]].effect
            value = (
                1
                if type(effect) is base.ProverMessageEffect and joined <= 1
                else joined
            )
        else:
            value = joined
        classes[node] = value

    activities = {(6, index) for index in range(len(core.occurrences))}
    deterministic_message_outputs = {
        (8, index, output)
        for index, occurrence in enumerate(core.occurrences)
        if type(occurrence.effect) is VerifierMessageEffect
        for output in range(len(outputs[index]))
    }
    binding_observations = {(5, index) for index in range(len(core.public_bindings))}
    terminals = {(11, index) for index in range(len(core.terminals))}
    terminal_public_outputs = {
        _producer_node(reference)
        for terminal in core.terminals
        for reference in terminal.public_outputs
    }
    sinks = (
        activities
        | binding_observations
        | deterministic_message_outputs
        | terminals
        | terminal_public_outputs
    )
    accepting_terminals = {
        (11, index)
        for index, terminal in enumerate(core.terminals)
        if terminal.verdict is base.TerminalVerdict.ACCEPT
    }
    acceptance = accepting_terminals | {
        _producer_node(reference)
        for index, terminal in enumerate(core.terminals)
        if (11, index) in accepting_terminals
        for reference in terminal.public_outputs
    }
    eligible = all(classes[node] in (0, 1) for node in sinks)
    private_predecessors: list[tuple[int, ...]] = []
    for ordinal in range(len(core.verifier_private_inputs)):
        source = (1, ordinal)
        seen = {source}
        pending = [source]
        reaches_sink = False
        while pending:
            current = pending.pop()
            reaches_sink = reaches_sink or current in sinks
            for child in outgoing[current]:
                if child not in seen:
                    seen.add(child)
                    pending.append(child)
        if reaches_sink:
            private_predecessors.append(source)
    private_predecessors.sort(key=_pc_key)

    ordered_nodes = sorted(nodes, key=_pc_key)
    ordered_edges = sorted(edges, key=_edge_key)
    graph = {
        0: [_pc_value(node) for node in ordered_nodes],
        1: [_edge_value(pair) for pair in ordered_edges],
        2: [_pc_value(node) for node in topological],
        3: [{0: _pc_value(node), 1: _v(classes[node])} for node in ordered_nodes],
        4: [_pc_value(node) for node in sorted(sinks, key=_pc_key)],
        5: [_pc_value(node) for node in sorted(acceptance, key=_pc_key)],
        6: [],
    }
    return graph, {
        "eligible": eligible,
        "private_predecessors": tuple(private_predecessors),
        "terminal_positions": terminal_positions,
        "classes": classes,
        "nodes": len(nodes),
        "edges": len(edges),
    }


def _effect_value(effect: object) -> dict[str, Any]:
    if type(effect) is base.ProverMessageEffect:
        return _v(
            0,
            {0: _module_ref(effect.channel), 1: _value_type_body(effect.payload_type)},
        )
    if type(effect) is VerifierMessageEffect:
        return _v(
            1,
            {
                0: _module_ref(effect.channel),
                1: _identifier("algorithm-ref-body-v0", effect.algorithm),
                2: _identifier(
                    "evaluation-contract-id-body-v0", effect.evaluation_contract
                ),
                3: [_value_ref(item) for item in effect.inputs],
                4: _value_type_body(effect.payload_type),
            },
        )
    if type(effect) is base.TerminalEffect:
        return _v(5, _ordinal("terminal-ref-body-v0", effect.terminal))
    raise FamilyFailure("Unsupported", "F0V2B2C1B1-U-EFFECT", "unsupported effect")


def project_views(core_handle: object, protocol_handle: object) -> dict[str, Any]:
    """Derive all six candidate static bodies from retained admitted facts."""

    core, outputs = _retained_core(core_handle)
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
            "F0V2B2C1B1-R-PROTOCOL-AUTHORITY",
            "ExecutionView requires the paired Fresh Protocol snapshot",
        )
    core_identifier = k1.decode_content_reference(core_handle.core_reference)
    protocol_identifier = k1.decode_content_reference(
        protocol_handle.protocol_reference
    )
    paths = _scope_paths(core)
    graph, graph_evidence = _graph(core, outputs)
    core_atom = _identifier("core-id-body-v0", core_identifier)
    protocol_atom = _identifier("protocol-id-body-v0", protocol_identifier)

    public_binding = {
        0: core_atom,
        1: [
            {
                0: _ordinal("scope-ref-body-v0", ordinal),
                1: _v(0)
                if scope.parent is None
                else _v(1, _ordinal("scope-ref-body-v0", scope.parent)),
                2: _v(0)
                if scope.opening is None
                else _v(1, _ordinal("occurrence-ref-body-v0", scope.opening)),
                3: [_ordinal("scope-ref-body-v0", item) for item in paths[ordinal]],
            }
            for ordinal, scope in enumerate(core.scopes)
        ],
        2: [
            {
                0: _ordinal("binding-ref-body-v0", ordinal),
                1: _ordinal("scope-ref-body-v0", binding.scope),
                2: _v(binding.binding_class.value),
                3: _value_ref(binding.value),
                4: _value_type_body(_value_type(core, outputs, binding.value)),
            }
            for ordinal, binding in enumerate(core.public_bindings)
        ],
    }

    decisions = [
        (index, occurrence)
        for index, occurrence in enumerate(core.occurrences)
        if type(occurrence.effect) is base.ProverMessageEffect
    ]
    decision_rows: list[dict[int, Any]] = []
    read_rows: list[dict[int, Any]] = []
    legal_rows: list[dict[int, Any]] = []
    opening_positions = [
        -1 if scope.opening is None else scope.opening for scope in core.scopes
    ]
    for occurrence_ref, occurrence in decisions:
        move = _v(0, _value_type_body(occurrence.effect.payload_type))
        prior = [index for index, _item in decisions if index < occurrence_ref]
        decision_rows.append(
            {
                0: _ordinal("decision-ref-body-v0", occurrence_ref),
                1: _ordinal("occurrence-ref-body-v0", occurrence_ref),
                2: [
                    _ordinal("scope-ref-body-v0", item)
                    for item in paths[occurrence.scope]
                ],
                3: _guard_body(occurrence.guard),
                4: move,
                5: [_ordinal("decision-ref-body-v0", item) for item in prior],
            }
        )
        for ordinal, constant in enumerate(core.constants):
            read_rows.append(
                {
                    0: _ordinal("decision-ref-body-v0", occurrence_ref),
                    1: _v(0, _ordinal("constant-ref-body-v0", ordinal)),
                    2: _value_type_body(constant.value_type),
                }
            )
        for ordinal, item in enumerate(core.public_inputs):
            boundaries = [
                opening_positions[binding.scope]
                for binding in core.public_bindings
                if binding.value == base.PublicInputRef(ordinal)
            ]
            if boundaries and min(boundaries) <= occurrence_ref:
                read_rows.append(
                    {
                        0: _ordinal("decision-ref-body-v0", occurrence_ref),
                        1: _v(1, _ordinal("public-input-ref-body-v0", ordinal)),
                        2: _value_type_body(item.value_type),
                    }
                )
        for binding_ref, binding in enumerate(core.public_bindings):
            if opening_positions[binding.scope] <= occurrence_ref:
                read_rows.append(
                    {
                        0: _ordinal("decision-ref-body-v0", occurrence_ref),
                        1: _v(2, _ordinal("binding-ref-body-v0", binding_ref)),
                        2: _value_type_body(_value_type(core, outputs, binding.value)),
                    }
                )
        for prior_ref, prior_occurrence in enumerate(core.occurrences[:occurrence_ref]):
            prior_effect = prior_occurrence.effect
            if type(prior_effect) in (
                base.ProverMessageEffect,
                VerifierMessageEffect,
            ) and _guard_implies(occurrence.guard, prior_occurrence.guard):
                read_rows.append(
                    {
                        0: _ordinal("decision-ref-body-v0", occurrence_ref),
                        1: _v(
                            3,
                            _ordinal("occurrence-ref-body-v0", prior_ref),
                        ),
                        2: _value_type_body(prior_effect.payload_type),
                    }
                )
                if type(prior_effect) is base.ProverMessageEffect:
                    read_rows.append(
                        {
                            0: _ordinal("decision-ref-body-v0", occurrence_ref),
                            1: _v(
                                9,
                                _ordinal("decision-ref-body-v0", prior_ref),
                            ),
                            2: _value_type_body(prior_effect.payload_type),
                        }
                    )
        legal_rows.append(
            {0: _ordinal("decision-ref-body-v0", occurrence_ref), 1: move}
        )
    strategy = {
        0: core_atom,
        1: decision_rows,
        2: _law("core-admission-v0"),
        3: read_rows,
        4: legal_rows,
    }

    public_coin = {
        0: core_atom,
        1: graph,
        2: graph_evidence["eligible"],
        3: [_pc_value(item) for item in graph_evidence["private_predecessors"]],
        4: [],
    }

    occurrence_rows: list[dict[int, Any]] = []
    value_rows: list[dict[int, Any]] = []
    for ordinal, item in enumerate(core.public_inputs):
        value_rows.append(
            {
                0: _value_ref(base.PublicInputRef(ordinal)),
                1: _value_type_body(item.value_type),
                2: [],
            }
        )
    for ordinal, item in enumerate(core.verifier_private_inputs):
        value_rows.append(
            {
                0: _value_ref(base.VerifierPrivateInputRef(ordinal)),
                1: _value_type_body(item.value_type),
                2: [],
            }
        )
    for ordinal, item in enumerate(core.constants):
        value_rows.append(
            {
                0: _value_ref(base.ConstantRef(ordinal)),
                1: _value_type_body(item.value_type),
                2: [],
            }
        )
    for ordinal, item in enumerate(core.derived_values):
        value_rows.append(
            {
                0: _value_ref(base.DerivedValueRef(ordinal)),
                1: _value_type_body(item.result_type),
                2: [_value_ref(value) for value in item.inputs],
            }
        )
    messages: list[dict[int, Any]] = []
    for occurrence_ref, occurrence in enumerate(core.occurrences):
        occurrence_rows.append(
            {
                0: _ordinal("occurrence-ref-body-v0", occurrence_ref),
                1: [
                    _ordinal("scope-ref-body-v0", item)
                    for item in paths[occurrence.scope]
                ],
                2: _guard_body(occurrence.guard),
                3: _effect_value(occurrence.effect),
                4: [_value_type_body(item) for item in outputs[occurrence_ref]],
            }
        )
        effect = occurrence.effect
        if type(effect) is base.ProverMessageEffect:
            messages.append(
                {
                    0: _ordinal("occurrence-ref-body-v0", occurrence_ref),
                    1: _v(0),
                    2: _v(
                        0,
                        {
                            0: _module_ref(effect.channel),
                            1: _value_type_body(effect.payload_type),
                        },
                    ),
                }
            )
        elif type(effect) is VerifierMessageEffect:
            messages.append(
                {
                    0: _ordinal("occurrence-ref-body-v0", occurrence_ref),
                    1: _v(1),
                    2: _v(
                        1,
                        {
                            0: _module_ref(effect.channel),
                            1: _identifier("algorithm-ref-body-v0", effect.algorithm),
                            2: _identifier(
                                "evaluation-contract-id-body-v0",
                                effect.evaluation_contract,
                            ),
                            3: [_value_ref(item) for item in effect.inputs],
                            4: _value_type_body(effect.payload_type),
                        },
                    ),
                }
            )
        for output_ordinal, output_type in enumerate(outputs[occurrence_ref]):
            predecessors: tuple[object, ...] = ()
            if type(effect) is VerifierMessageEffect:
                predecessors = effect.inputs
            value_rows.append(
                {
                    0: _value_ref(
                        base.OccurrenceOutputRef(occurrence_ref, output_ordinal)
                    ),
                    1: _value_type_body(output_type),
                    2: [_value_ref(item) for item in predecessors],
                }
            )
    terminals = [
        {
            0: _ordinal("terminal-ref-body-v0", terminal_ref),
            1: _v(terminal.verdict.value),
            2: [_value_ref(item) for item in terminal.public_outputs],
            3: [],
            4: [],
            5: _ordinal(
                "occurrence-ref-body-v0",
                graph_evidence["terminal_positions"][terminal_ref],
            ),
        }
        for terminal_ref, terminal in enumerate(core.terminals)
    ]
    effect_view = {
        0: core_atom,
        1: occurrence_rows,
        2: value_rows,
        3: messages,
        4: [],
        5: [],
        6: terminals,
        7: [],
    }

    runtime = {
        0: [
            {
                0: _ordinal("occurrence-ref-body-v0", index),
                1: [_value_type_body(item) for item in outputs[index]],
            }
            for index in range(len(core.occurrences))
        ],
        1: [],
        2: [],
        3: [
            {
                0: _ordinal("terminal-ref-body-v0", index),
                1: _ordinal(
                    "occurrence-ref-body-v0",
                    graph_evidence["terminal_positions"][index],
                ),
                2: _v(terminal.verdict.value),
                3: [
                    _value_type_body(_value_type(core, outputs, ref))
                    for ref in terminal.public_outputs
                ],
            }
            for index, terminal in enumerate(core.terminals)
        ],
    }
    execution = {
        0: protocol_atom,
        1: core_atom,
        2: _v(0),
        3: _law("core-admission-v0"),
        4: [],
        5: _law("execution-and-replay-v0"),
        6: runtime,
        7: _v(0),
        8: _law("execution-and-replay-v0"),
        9: _law("run-view-issuance-v0"),
    }
    return {
        "PublicBindingView": public_binding,
        "StrategyDecisionView": strategy,
        "PublicCoinView": public_coin,
        "EffectView": effect_view,
        "ClaimReductionView": {0: core_atom, 1: [], 2: [], 3: []},
        "ExecutionView": execution,
    }


def identity_algorithm(name: str, value_type: object) -> object:
    return k1.CanonicalAlgorithm(
        k1.Symbol(name), (value_type,), k1.Variable(0, value_type)
    )


def _fixture_environment(core: object, algorithms: tuple[object, ...]) -> object:
    base_fixture = base.make_fixture()
    module_ids = set(core.used_modules)
    algorithm_map = {item.identity: item for item in algorithms}
    _algorithm_ids, contracts = _ordinary_references(core)
    contract_ids = set(contracts)
    contract = k1.DEFAULT_EVALUATION_CONTRACT
    if contract_ids - {contract.identity}:
        raise AssertionError("fixture uses an unexpected evaluation contract")
    return base.Environment(
        base_fixture.environment.profile_id,
        MappingProxyType(dict(base_fixture.environment.profile_preimages)),
        MappingProxyType(
            {
                identifier: base_fixture.environment.module_preimages[identifier]
                for identifier in module_ids
            }
        ),
        MappingProxyType(algorithm_map),
        MappingProxyType(
            {identifier: MappingProxyType({}) for identifier in algorithm_map}
        ),
        MappingProxyType({contract.identity: contract} if contract_ids else {}),
    )


def _fixture_cases() -> dict[str, tuple[object, object]]:
    """Build the positive carriers and the private-binding negative."""

    base_fixture = base.make_fixture()
    module_id = base_fixture.module.identity
    channel = base.ModuleDeclarationRef(module_id, "pir.message-channel", 0)
    contract_id = k1.DEFAULT_EVALUATION_CONTRACT.identity
    z3_identity = identity_algorithm("B2C1B1Z3Identity", base.Z3)
    bool_identity = identity_algorithm("B2C1B1BoolIdentity", k1.BOOL)

    def assemble(
        *,
        public_inputs: tuple[object, ...],
        private_inputs: tuple[object, ...] = (),
        constants: tuple[object, ...] = (),
        derived: tuple[object, ...] = (),
        scopes: tuple[object, ...] = (base.ScopeDecl(None, None),),
        bindings: tuple[object, ...],
        terminals: tuple[object, ...],
        occurrences: tuple[object, ...],
        algorithms: tuple[object, ...] = (),
    ) -> tuple[object, object]:
        used = tuple(
            sorted(
                {
                    effect.channel.module
                    for effect in (item.effect for item in occurrences)
                    if type(effect) in (base.ProverMessageEffect, VerifierMessageEffect)
                },
                key=lambda item: item.internal_reference(),
            )
        )
        core = base.InteractiveCore(
            used,
            public_inputs,
            private_inputs,
            constants,
            derived,
            scopes,
            bindings,
            (),
            (),
            (),
            (),
            (),
            terminals,
            occurrences,
        )
        environment = _fixture_environment(core, algorithms)
        return environment, make_candidate(core, environment.profile_id)

    public_z3 = (base.InputDecl(base.Z3),)
    statement_z3 = (
        base.PublicBindingDecl(0, base.BindingClass.STATEMENT, base.PublicInputRef(0)),
    )
    dead_terminal = (base.TerminalDecl(base.TerminalVerdict.ACCEPT, (), (), ()),)
    dead_occurrence = (
        base.OccurrenceDecl(0, base.AlwaysGuard(), base.TerminalEffect(0)),
    )
    private_dead = assemble(
        public_inputs=public_z3,
        private_inputs=(base.InputDecl(k1.BOOL),),
        bindings=statement_z3,
        terminals=dead_terminal,
        occurrences=dead_occurrence,
    )
    private_sink_terminal = (
        base.TerminalDecl(
            base.TerminalVerdict.ACCEPT,
            (base.VerifierPrivateInputRef(0),),
            (),
            (),
        ),
    )
    private_sink = assemble(
        public_inputs=public_z3,
        private_inputs=(base.InputDecl(k1.BOOL),),
        bindings=statement_z3,
        terminals=private_sink_terminal,
        occurrences=dead_occurrence,
    )

    private_binding_derived = base.DerivedValueDecl(
        z3_identity.identity,
        contract_id,
        (base.VerifierPrivateInputRef(0),),
        base.Z3,
    )
    private_binding = assemble(
        public_inputs=public_z3,
        private_inputs=(base.InputDecl(base.Z3),),
        derived=(private_binding_derived,),
        bindings=(
            *statement_z3,
            base.PublicBindingDecl(
                0,
                base.BindingClass.SESSION_CONTEXT,
                base.DerivedValueRef(0),
            ),
        ),
        terminals=dead_terminal,
        occurrences=dead_occurrence,
        algorithms=(z3_identity,),
    )

    public_history_binding = assemble(
        public_inputs=public_z3,
        scopes=(base.ScopeDecl(None, None), base.ScopeDecl(0, 1)),
        bindings=(
            *statement_z3,
            base.PublicBindingDecl(
                1,
                base.BindingClass.SESSION_CONTEXT,
                base.OccurrenceOutputRef(0, 0),
            ),
        ),
        terminals=dead_terminal,
        occurrences=(
            base.OccurrenceDecl(
                0, base.AlwaysGuard(), base.ProverMessageEffect(channel, base.Z3)
            ),
            base.OccurrenceDecl(1, base.AlwaysGuard(), base.TerminalEffect(0)),
        ),
    )

    constant = base.TypedConstantDecl(base.Z3, k1.admit_value(base.Z3, k1.Nat(1)))
    derived_decl = base.DerivedValueDecl(
        z3_identity.identity,
        contract_id,
        (base.ConstantRef(0),),
        base.Z3,
    )
    value_terminals = (
        base.TerminalDecl(
            base.TerminalVerdict.ACCEPT, (base.DerivedValueRef(0),), (), ()
        ),
    )
    constant_derived = assemble(
        public_inputs=public_z3,
        constants=(constant,),
        derived=(derived_decl,),
        bindings=statement_z3,
        terminals=value_terminals,
        occurrences=(
            base.OccurrenceDecl(
                0, base.AlwaysGuard(), base.ProverMessageEffect(channel, base.Z3)
            ),
            base.OccurrenceDecl(0, base.AlwaysGuard(), base.TerminalEffect(0)),
        ),
        algorithms=(z3_identity,),
    )

    guard = base.EvaluateGuard(
        bool_identity.identity,
        contract_id,
        (base.PublicInputRef(0),),
    )
    child_scopes = (base.ScopeDecl(None, None), base.ScopeDecl(0, 0))
    child_terminals = (
        base.TerminalDecl(
            base.TerminalVerdict.ACCEPT,
            (base.OccurrenceOutputRef(0, 0),),
            (),
            (),
        ),
        base.TerminalDecl(base.TerminalVerdict.REJECT, (), (), ()),
    )
    child_guard = assemble(
        public_inputs=(base.InputDecl(k1.BOOL),),
        scopes=child_scopes,
        bindings=(
            base.PublicBindingDecl(
                1, base.BindingClass.STATEMENT, base.PublicInputRef(0)
            ),
        ),
        terminals=child_terminals,
        occurrences=(
            base.OccurrenceDecl(1, guard, base.ProverMessageEffect(channel, k1.BOOL)),
            base.OccurrenceDecl(1, guard, base.TerminalEffect(0)),
            base.OccurrenceDecl(0, base.AlwaysGuard(), base.TerminalEffect(1)),
        ),
        algorithms=(bool_identity,),
    )

    verifier_message = assemble(
        public_inputs=public_z3,
        bindings=statement_z3,
        terminals=(
            base.TerminalDecl(
                base.TerminalVerdict.ACCEPT,
                (base.OccurrenceOutputRef(0, 0),),
                (),
                (),
            ),
        ),
        occurrences=(
            base.OccurrenceDecl(
                0,
                base.AlwaysGuard(),
                VerifierMessageEffect(
                    channel,
                    z3_identity.identity,
                    contract_id,
                    (base.PublicInputRef(0),),
                    base.Z3,
                ),
            ),
            base.OccurrenceDecl(
                0, base.AlwaysGuard(), base.ProverMessageEffect(channel, base.Z3)
            ),
            base.OccurrenceDecl(0, base.AlwaysGuard(), base.TerminalEffect(0)),
        ),
        algorithms=(z3_identity,),
    )
    return {
        "verifier-private-dead": private_dead,
        "verifier-private-sink": private_sink,
        "public-history-binding-observation": public_history_binding,
        "constant-and-derived-value": constant_derived,
        "child-scope-and-nontrivial-guard": child_guard,
        "deterministic-verifier-message": verifier_message,
        "verifier-private-derived-binding": private_binding,
    }


def fixtures() -> dict[str, tuple[object, object]]:
    """Return the six exact positive foundation carriers."""

    cases = _fixture_cases()
    del cases["verifier-private-derived-binding"]
    return cases


def private_binding_mutation() -> tuple[object, object]:
    """Return an authenticated binding with verifier-private ancestry."""

    return _fixture_cases()["verifier-private-derived-binding"]


def mutated_fixture(name: str) -> tuple[object, object]:
    """Construct a semantic mutation with a freshly authenticated candidate ID."""

    environment, candidate = fixtures()[name]
    _profile, domain, _domain_body = b2c0._strict_profiled_body(
        candidate.profiled_body, "mutation source"
    )
    core = decode_core(domain)
    if name == "constant-and-derived-value":
        item = core.derived_values[0]
        core = base.InteractiveCore(
            core.used_modules,
            core.public_inputs,
            core.verifier_private_inputs,
            core.constants,
            (
                base.DerivedValueDecl(
                    item.algorithm,
                    item.evaluation_contract,
                    item.inputs,
                    k1.BOOL,
                ),
            ),
            core.scopes,
            core.public_bindings,
            core.challenges,
            core.oracles,
            core.checks,
            core.claims,
            core.reductions,
            core.terminals,
            core.occurrences,
        )
    elif name == "child-scope-and-nontrivial-guard":
        occurrences = list(core.occurrences)
        occurrences[1] = base.OccurrenceDecl(
            occurrences[1].scope, base.AlwaysGuard(), occurrences[1].effect
        )
        core = base.InteractiveCore(
            core.used_modules,
            core.public_inputs,
            core.verifier_private_inputs,
            core.constants,
            core.derived_values,
            core.scopes,
            core.public_bindings,
            core.challenges,
            core.oracles,
            core.checks,
            core.claims,
            core.reductions,
            core.terminals,
            tuple(occurrences),
        )
    elif name == "deterministic-verifier-message":
        occurrences = list(core.occurrences)
        effect = occurrences[0].effect
        assert type(effect) is VerifierMessageEffect
        occurrences[0] = base.OccurrenceDecl(
            occurrences[0].scope,
            occurrences[0].guard,
            VerifierMessageEffect(
                effect.channel,
                effect.algorithm,
                effect.evaluation_contract,
                effect.inputs,
                k1.BOOL,
            ),
        )
        core = base.InteractiveCore(
            core.used_modules,
            core.public_inputs,
            core.verifier_private_inputs,
            core.constants,
            core.derived_values,
            core.scopes,
            core.public_bindings,
            core.challenges,
            core.oracles,
            core.checks,
            core.claims,
            core.reductions,
            core.terminals,
            tuple(occurrences),
        )
    else:
        raise KeyError(name)
    return _fixture_environment(
        core, tuple(environment.algorithm_preimages.values())
    ), make_candidate(core, environment.profile_id)
