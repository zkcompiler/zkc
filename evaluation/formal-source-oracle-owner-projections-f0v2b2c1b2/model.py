"""Typed owner evaluator for the F0-V2B2C1B2 Oracle isolation slice.

This is temporary research code.  It extends the B2C1B1 canonical-byte owner
substrate for the standard immutable-Oracle constructors only; it is not the
published PIR evaluator and it does not execute an Oracle.
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from enum import Enum
import hashlib
import importlib.util
from pathlib import Path
import sys
from types import MappingProxyType, ModuleType
from typing import Any, Mapping


ROOT = Path(__file__).resolve().parents[2]
FOUNDATION_MODEL = (
    ROOT / "evaluation" / "formal-source-owner-projections-f0v2b2c1b1" / "model.py"
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


foundation = _load("_zkc_f0v2b2c1b2_foundation", FOUNDATION_MODEL)
base = foundation.base
b2c0 = foundation.b2c0
b2b = foundation.b2b
codec = foundation.codec
k1 = foundation.k1
VIEW_SCHEMAS = foundation.VIEW_SCHEMAS

EVALUATOR_FINGERPRINT = hashlib.sha256(
    b"zkc-f0-v2b2c1b2-oracle-owner-evaluator-v0"
).digest()
MAX_ORACLE_ENTRIES = 1 << 14


class OracleFailure(ValueError):
    """Stable fail-closed outcome from the bounded Oracle owner evaluator."""

    def __init__(self, outcome: str, code: str, detail: str) -> None:
        super().__init__(detail)
        self.outcome = outcome
        self.code = code
        self.detail = detail


@dataclass(frozen=True)
class OracleAdmissionResult:
    outcome: str
    code: str
    detail: str
    handle: object | None = None


class OracleOrigin(Enum):
    INITIAL = 0
    PROVER = 1


class OracleVisibility(Enum):
    PUBLIC = 0
    VERIFIER_ONLY = 1


@dataclass(frozen=True)
class FullCanonicalOracle:
    pass


@dataclass(frozen=True)
class PublicBindingOracle:
    binding_type: object
    binding_contract: object
    binding_algorithm: object
    evaluation_contract: object


@dataclass(frozen=True)
class LogicalAccessOracle:
    domain_law: object


@dataclass(frozen=True)
class OracleDecl:
    scope: int
    origin: OracleOrigin
    index_type: object
    element_type: object
    maximum_entries: int
    publication_mode: object


@dataclass(frozen=True)
class PublishOracleEffect:
    oracle: int


@dataclass(frozen=True)
class QueryOracleEffect:
    oracle: int
    index: object
    visibility: OracleVisibility


@dataclass(frozen=True)
class AnswerOracleEffect:
    query: int


def _fail(outcome: str, code: str, detail: str) -> None:
    raise OracleFailure(outcome, code, detail)


def _record(*values: object) -> object:
    return k1.DatumRecord(tuple((index, value) for index, value in enumerate(values)))


def _seq(values: tuple[object, ...]) -> object:
    return k1.DatumSeq(values)


def _variant(case: int, payload: object = k1.UNIT) -> object:
    return k1.DatumVariant(case, payload)


def oracle_entry_type(oracle: OracleDecl) -> object:
    entry = k1.ValueType(
        k1.RECORD_DOMAIN,
        k1.RecordSchema(((0, oracle.index_type), (1, oracle.element_type))),
    )
    return entry


def oracle_carrier_type(oracle: OracleDecl) -> object:
    return k1.ValueType(
        k1.SEQUENCE_DOMAIN,
        k1.SeqSchema(oracle_entry_type(oracle), oracle.maximum_entries),
    )


def oracle_lookup_type(oracle: OracleDecl) -> object:
    return k1.ValueType(
        k1.VARIANT_DOMAIN,
        k1.VariantSchema(((0, k1.UNIT_VALUE), (1, oracle.element_type))),
    )


def oracle_publication_types(oracle: OracleDecl) -> tuple[object, ...]:
    mode = oracle.publication_mode
    if type(mode) is FullCanonicalOracle:
        return (oracle_carrier_type(oracle),)
    if type(mode) is PublicBindingOracle:
        return (mode.binding_type,)
    if type(mode) is LogicalAccessOracle:
        return ()
    _fail("Malformed", "F0V2B2C1B2-M-ORACLE-MODE", "unknown Oracle mode")
    raise AssertionError("unreachable")


def oracle_answer_type(oracle: OracleDecl) -> object:
    if type(oracle.publication_mode) is LogicalAccessOracle:
        return oracle.element_type
    return oracle_lookup_type(oracle)


def _mode_datum(mode: object) -> object:
    if type(mode) is FullCanonicalOracle:
        return _variant(0)
    if type(mode) is PublicBindingOracle:
        return _variant(
            1,
            _record(
                k1.value_type_datum(mode.binding_type),
                base.module_declaration_ref_datum(mode.binding_contract),
                k1.BytesValue(mode.binding_algorithm.internal_reference()),
                k1.BytesValue(mode.evaluation_contract.internal_reference()),
            ),
        )
    if type(mode) is LogicalAccessOracle:
        return _variant(2, base.module_declaration_ref_datum(mode.domain_law))
    raise k1.ModelError("unknown Oracle publication mode")


def _oracle_datum(oracle: object) -> object:
    if type(oracle) is not OracleDecl:
        raise k1.ModelError("Oracle declaration has another carrier")
    return _record(
        k1.Nat(oracle.scope),
        _variant(oracle.origin.value),
        k1.value_type_datum(oracle.index_type),
        k1.value_type_datum(oracle.element_type),
        k1.Nat(oracle.maximum_entries),
        _mode_datum(oracle.publication_mode),
    )


def _oracle_effect_datum(effect: object) -> object:
    if type(effect) is PublishOracleEffect:
        payload = _variant(0, k1.Nat(effect.oracle))
    elif type(effect) is QueryOracleEffect:
        payload = _variant(
            1,
            _record(
                k1.Nat(effect.oracle),
                base.value_ref_datum(effect.index),
                _variant(effect.visibility.value),
            ),
        )
    elif type(effect) is AnswerOracleEffect:
        payload = _variant(2, k1.Nat(effect.query))
    else:
        raise k1.ModelError("unknown Oracle effect")
    return _variant(6, payload)


def _effect_datum(effect: object) -> object:
    if type(effect) in (PublishOracleEffect, QueryOracleEffect, AnswerOracleEffect):
        return _oracle_effect_datum(effect)
    return foundation._effect_datum(effect)


def core_domain_datum(core: object) -> object:
    if type(core) is not base.InteractiveCore:
        raise k1.ModelError("Oracle Core has another carrier")
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
        _seq(tuple(_oracle_datum(item) for item in core.oracles)),
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


def _decode_mode(value: object) -> object:
    case, payload = b2c0._variant(value, (0, 1, 2), "Oracle publication mode")
    if case == 0:
        b2c0._unit(payload, "FullCanonicalOracle payload")
        return FullCanonicalOracle()
    if case == 1:
        value_type, contract, algorithm, evaluation = b2c0._record(
            payload, (0, 1, 2, 3), "PublicBinding Oracle mode"
        )
        return PublicBindingOracle(
            b2c0._decode_value_type(value_type),
            b2c0._decode_module_ref(contract),
            b2c0._content_ref(algorithm, "binding algorithm"),
            b2c0._content_ref(evaluation, "binding evaluation contract"),
        )
    return LogicalAccessOracle(b2c0._decode_module_ref(payload))


def _decode_oracle(value: object) -> OracleDecl:
    scope, origin, index_type, element_type, maximum, mode = b2c0._record(
        value, tuple(range(6)), "Oracle declaration"
    )
    origin_case, origin_payload = b2c0._variant(origin, (0, 1), "Oracle origin")
    b2c0._unit(origin_payload, "Oracle-origin payload")
    return OracleDecl(
        b2c0._nat(scope, "Oracle scope"),
        OracleOrigin(origin_case),
        b2c0._decode_value_type(index_type),
        b2c0._decode_value_type(element_type),
        b2c0._nat(maximum, "Oracle maximum entries"),
        _decode_mode(mode),
    )


def _decode_effect(value: object) -> object:
    case, payload = b2c0._variant(value, tuple(range(8)), "Core effect")
    if case == 0:
        channel, payload_type = b2c0._record(payload, (0, 1), "Prover message")
        return base.ProverMessageEffect(
            b2c0._decode_module_ref(channel), b2c0._decode_value_type(payload_type)
        )
    if case == 5:
        return base.TerminalEffect(b2c0._nat(payload, "terminal backlink"))
    if case != 6:
        _fail(
            "Unsupported",
            "F0V2B2C1B2-U-EFFECT",
            f"effect tag {case} belongs to another isolation slice",
        )
    oracle_case, oracle_payload = b2c0._variant(payload, (0, 1, 2), "Oracle effect")
    if oracle_case == 0:
        return PublishOracleEffect(b2c0._nat(oracle_payload, "publication Oracle"))
    if oracle_case == 1:
        oracle, index, visibility = b2c0._record(
            oracle_payload, (0, 1, 2), "Oracle query"
        )
        visibility_case, visibility_payload = b2c0._variant(
            visibility, (0, 1), "Oracle visibility"
        )
        b2c0._unit(visibility_payload, "Oracle-visibility payload")
        return QueryOracleEffect(
            b2c0._nat(oracle, "query Oracle"),
            b2c0._decode_value_ref(index),
            OracleVisibility(visibility_case),
        )
    return AnswerOracleEffect(b2c0._nat(oracle_payload, "answer query"))


def decode_core(domain: object) -> object:
    """Strictly decode the exact bounded Oracle Core from canonical bytes."""

    fields = b2c0._record(domain, tuple(range(14)), "InteractiveCore")
    sequences = tuple(
        b2c0._sequence(value, f"InteractiveCore field {ordinal}")
        for ordinal, value in enumerate(fields)
    )
    if any(sequences[index] for index in (2, 4, 7, 9, 10, 11)):
        _fail(
            "Unsupported",
            "F0V2B2C1B2-U-OTHER-SLICE",
            "private, derived, challenge, check, claim, or reduction constructors are outside B2C1B2",
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
    constants: list[object] = []
    for item in sequences[3]:
        value_type, datum = b2c0._record(item, (0, 1), "typed constant")
        decoded_type = b2c0._decode_value_type(value_type)
        try:
            admitted = k1.admit_value(decoded_type, datum)
        except Exception as error:
            _fail("Refused", "F0V2B2C1B2-R-CONSTANT", str(error))
        constants.append(base.TypedConstantDecl(decoded_type, admitted))
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
                None if parent_case == 0 else b2c0._nat(parent_payload, "parent"),
                None if opening_case == 0 else b2c0._nat(opening_payload, "opening"),
            )
        )
    bindings: list[object] = []
    for item in sequences[6]:
        scope, binding_class, value = b2c0._record(item, (0, 1, 2), "binding")
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
    oracles = tuple(_decode_oracle(item) for item in sequences[8])
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
                "F0V2B2C1B2-U-TERMINAL-CLOSURE",
                "checks and claim dispositions belong to later slices",
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
        (),
        tuple(constants),
        (),
        tuple(scopes),
        tuple(bindings),
        (),
        oracles,
        (),
        (),
        (),
        tuple(terminals),
        tuple(occurrences),
    )


def _mode_module_refs(mode: object) -> tuple[object, ...]:
    if type(mode) is PublicBindingOracle:
        return (mode.binding_contract,)
    if type(mode) is LogicalAccessOracle:
        return (mode.domain_law,)
    return ()


def _module_references(core: object) -> tuple[object, ...]:
    refs = [
        ref
        for oracle in core.oracles
        for ref in _mode_module_refs(oracle.publication_mode)
    ]
    refs.extend(
        occurrence.effect.channel
        for occurrence in core.occurrences
        if type(occurrence.effect) is base.ProverMessageEffect
    )
    return tuple(refs)


def _ordinary_references(core: object) -> tuple[tuple[object, ...], tuple[object, ...]]:
    algorithms: set[object] = set()
    contracts: set[object] = set()
    for oracle in core.oracles:
        mode = oracle.publication_mode
        if type(mode) is PublicBindingOracle:
            algorithms.add(mode.binding_algorithm)
            contracts.add(mode.evaluation_contract)

    def key(item: object) -> bytes:
        return item.internal_reference()

    return tuple(sorted(algorithms, key=key)), tuple(sorted(contracts, key=key))


def _authenticate_algorithms(
    core: object, environment: object
) -> Mapping[object, object]:
    algorithms, contracts = _ordinary_references(core)
    if set(environment.algorithm_preimages) != set(algorithms):
        _fail(
            "Refused",
            "F0V2B2C1B2-R-EXACT-ALGORITHMS",
            "binding-algorithm closure is missing or has unused entries",
        )
    if set(environment.contract_preimages) != set(contracts):
        _fail(
            "Refused",
            "F0V2B2C1B2-R-EXACT-CONTRACTS",
            "binding-contract evaluator closure is missing or has unused entries",
        )
    result: dict[object, object] = {}
    ledger = k1.AuthenticationLedger()
    try:
        for identifier in algorithms:
            algorithm = environment.algorithm_preimages[identifier]
            if (
                k1.authenticate_algorithm_identity(algorithm, ledger=ledger)
                != identifier
            ):
                _fail(
                    "Refused",
                    "F0V2B2C1B2-R-ALGORITHM-ID",
                    "binding algorithm identity differs",
                )
            modules = environment.algorithm_modules.get(identifier)
            if modules is None:
                _fail(
                    "MissingDependency",
                    "F0V2B2C1B2-D-ALGORITHM-MODULES",
                    "binding algorithm module closure is missing",
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
            result[identifier] = algorithm.function_type
        for identifier in contracts:
            contract = environment.contract_preimages[identifier]
            if contract.identity != identifier:
                _fail(
                    "Refused",
                    "F0V2B2C1B2-R-CONTRACT-ID",
                    "evaluation contract identity differs",
                )
            k1.authenticate_content_id(
                identifier,
                contract.body(),
                environment.prior_meta_preimages,
                ledger=ledger,
            )
    except OracleFailure:
        raise
    except Exception as error:
        outcome = getattr(getattr(error, "outcome", None), "value", None)
        _fail(outcome or "Refused", "F0V2B2C1B2-R-DEPENDENCY", str(error))
    return MappingProxyType(result)


def _resolve_declaration(
    reference: object, expected: str, environment: object
) -> object:
    if type(reference) is not base.ModuleDeclarationRef:
        _fail(
            "Malformed",
            "F0V2B2C1B2-M-MODULE-REF",
            "module declaration reference has another carrier",
        )
    if reference.declaration_kind != expected:
        _fail(
            "KindMismatch",
            "F0V2B2C1B2-K-DECLARATION",
            f"expected declaration kind {expected}",
        )
    module = environment.module_preimages.get(reference.module)
    if module is None:
        _fail(
            "MissingDependency",
            "F0V2B2C1B2-D-MODULE-PREIMAGE",
            "declaration owner is missing",
        )
    try:
        return k1.resolve_module_declaration(
            module, reference.declaration_kind, reference.local_ordinal
        )
    except Exception as error:
        _fail("Refused", "F0V2B2C1B2-R-DECLARATION-COORDINATE", str(error))
    raise AssertionError("unreachable")


def _validate_nominal(reference: object, expected: str, environment: object) -> None:
    body = _resolve_declaration(reference, expected, environment)
    if (
        type(body) is not k1.DatumRecord
        or tuple(index for index, _ in body.fields) != (0,)
        or type(body.fields[0][1]) is not k1.Symbol
    ):
        _fail(
            "Refused",
            "F0V2B2C1B2-R-NOMINAL-BODY",
            f"{expected} declaration has another exact body",
        )


def _validate_domain_law(
    oracle: OracleDecl, reference: object, environment: object
) -> None:
    body = _resolve_declaration(reference, "pir.oracle-domain-law", environment)
    value_type, values = b2c0._record(body, (0, 1), "Oracle domain law")
    decoded_type = b2c0._decode_value_type(value_type)
    if decoded_type != oracle.index_type:
        _fail(
            "KindMismatch",
            "F0V2B2C1B2-K-DOMAIN-LAW-TYPE",
            "domain-law index type differs from the Oracle index type",
        )
    items = b2c0._sequence(values, "Oracle exact indices")
    if len(items) > oracle.maximum_entries:
        _fail(
            "Refused",
            "F0V2B2C1B2-R-DOMAIN-LAW-BOUND",
            "domain law exceeds maximum_entries",
        )
    encoded: list[bytes] = []
    try:
        for item in items:
            encoded.append(k1.admit_value(decoded_type, item).bytes())
    except Exception as error:
        _fail("Refused", "F0V2B2C1B2-R-DOMAIN-LAW-VALUE", str(error))
    if encoded != sorted(set(encoded)):
        _fail(
            "Refused",
            "F0V2B2C1B2-R-DOMAIN-LAW-ORDER",
            "domain-law indices are not canonical strictly ascending unique",
        )


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


def _output_types(core: object) -> tuple[tuple[object, ...], ...]:
    result: list[tuple[object, ...]] = []
    for index, occurrence in enumerate(core.occurrences):
        effect = occurrence.effect
        if type(effect) is base.ProverMessageEffect:
            result.append((effect.payload_type,))
        elif type(effect) is PublishOracleEffect:
            if not 0 <= effect.oracle < len(core.oracles):
                _fail(
                    "Refused", "F0V2B2C1B2-R-ORACLE-REF", "publication Oracle is absent"
                )
            result.append(oracle_publication_types(core.oracles[effect.oracle]))
        elif type(effect) is QueryOracleEffect:
            result.append(())
        elif type(effect) is AnswerOracleEffect:
            if not 0 <= effect.query < index:
                _fail(
                    "Refused",
                    "F0V2B2C1B2-R-ANSWER-BACKLINK",
                    "answer query is not earlier",
                )
            query = core.occurrences[effect.query].effect
            if type(query) is not QueryOracleEffect or not 0 <= query.oracle < len(
                core.oracles
            ):
                _fail(
                    "Refused",
                    "F0V2B2C1B2-R-ANSWER-BACKLINK",
                    "answer does not name a query",
                )
            result.append((oracle_answer_type(core.oracles[query.oracle]),))
        elif type(effect) is base.TerminalEffect:
            result.append(())
        else:
            _fail("Unsupported", "F0V2B2C1B2-U-EFFECT", "unsupported effect")
    return tuple(result)


def _value_type(
    core: object, outputs: tuple[tuple[object, ...], ...], reference: object
) -> object:
    if type(reference) is base.PublicInputRef:
        table = core.public_inputs
        ordinal = reference.ordinal
    elif type(reference) is base.ConstantRef:
        table = core.constants
        ordinal = reference.ordinal
    elif type(reference) is base.OccurrenceOutputRef:
        if not 0 <= reference.occurrence < len(outputs):
            _fail("Refused", "F0V2B2C1B2-R-VALUE-REF", "occurrence is absent")
        values = outputs[reference.occurrence]
        if not 0 <= reference.output_ordinal < len(values):
            _fail("Refused", "F0V2B2C1B2-R-VALUE-REF", "output is absent")
        return values[reference.output_ordinal]
    else:
        _fail("Malformed", "F0V2B2C1B2-M-VALUE-REF", "unsupported ValueRef")
    if not 0 <= ordinal < len(table):
        _fail("Refused", "F0V2B2C1B2-R-VALUE-REF", "value ordinal is absent")
    return table[ordinal].value_type


def _guard_implies(use: object, source: object) -> bool:
    return type(source) is base.AlwaysGuard or use == source


def _validate_core(
    core: object, environment: object, function_types: Mapping[object, object]
) -> tuple[tuple[object, ...], ...]:
    if (
        not core.scopes
        or not core.oracles
        or not core.occurrences
        or not core.terminals
    ):
        _fail(
            "Refused",
            "F0V2B2C1B2-R-NONEMPTY",
            "scope, Oracle, occurrence, and terminal tables must be nonempty",
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
            "F0V2B2C1B2-R-EXACT-USED-MODULES",
            "used_modules differs from the exact Oracle declaration owners",
        )
    for occurrence in core.occurrences:
        if type(occurrence.effect) is base.ProverMessageEffect:
            _validate_nominal(
                occurrence.effect.channel, "pir.message-channel", environment
            )
    for oracle in core.oracles:
        if type(oracle) is not OracleDecl:
            _fail("Malformed", "F0V2B2C1B2-M-ORACLE", "Oracle carrier differs")
        if not 0 <= oracle.scope < len(core.scopes):
            _fail("Refused", "F0V2B2C1B2-R-ORACLE-SCOPE", "Oracle scope is absent")
        if not 0 <= oracle.maximum_entries <= MAX_ORACLE_ENTRIES:
            _fail("Refused", "F0V2B2C1B2-R-ORACLE-BOUND", "Oracle bound is outside v0")
        mode = oracle.publication_mode
        if type(mode) is PublicBindingOracle:
            _validate_nominal(
                mode.binding_contract, "pir.oracle-binding-contract", environment
            )
            function = function_types[mode.binding_algorithm]
            if (
                function.inputs != (oracle_carrier_type(oracle),)
                or function.output != mode.binding_type
                or function.failures
            ):
                _fail(
                    "KindMismatch",
                    "F0V2B2C1B2-K-BINDING-ABI",
                    "Oracle binding algorithm is not exact, total, and failure-free",
                )
        elif type(mode) is LogicalAccessOracle:
            _validate_domain_law(oracle, mode.domain_law, environment)
        elif type(mode) is not FullCanonicalOracle:
            _fail("Malformed", "F0V2B2C1B2-M-ORACLE-MODE", "Oracle mode differs")

    all_types = [
        *(item.value_type for item in core.public_inputs),
        *(item.value_type for item in core.constants),
        *(oracle.index_type for oracle in core.oracles),
        *(oracle.element_type for oracle in core.oracles),
        *(
            oracle.publication_mode.binding_type
            for oracle in core.oracles
            if type(oracle.publication_mode) is PublicBindingOracle
        ),
        *(
            occurrence.effect.payload_type
            for occurrence in core.occurrences
            if type(occurrence.effect) is base.ProverMessageEffect
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
        for oracle in core.oracles:
            oracle_carrier_type(oracle).__post_init__()
            oracle_lookup_type(oracle).__post_init__()
    except Exception as error:
        _fail("KindMismatch", "F0V2B2C1B2-K-VALUE-TYPE", str(error))

    if core.scopes[0] != base.ScopeDecl(None, None):
        _fail("Refused", "F0V2B2C1B2-R-ROOT-SCOPE", "scope zero is not initial")
    opening_positions = [-1]
    depths = [0]
    for ordinal, scope in enumerate(core.scopes[1:], start=1):
        if scope.parent is None or not 0 <= scope.parent < ordinal:
            _fail("Refused", "F0V2B2C1B2-R-SCOPE-PARENT", "scope parent is not earlier")
        if scope.opening is None or not 0 <= scope.opening < len(core.occurrences):
            _fail("Refused", "F0V2B2C1B2-R-SCOPE-OPENING", "scope opening is absent")
        depth = depths[scope.parent] + 1
        if depth > 384:
            _fail(
                "DeterministicLimitExceeded",
                "F0V2B2C1B2-L-SCOPE-DEPTH",
                "scope depth exceeds the target bound",
            )
        if scope.opening < opening_positions[scope.parent]:
            _fail("Refused", "F0V2B2C1B2-R-SCOPE-OPENING", "scope opens before parent")
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
                "F0V2B2C1B2-R-SCOPE-OPENING",
                "child scope opens after its first member or has no member",
            )

    outputs = _output_types(core)
    available: set[object] = {
        *(base.PublicInputRef(index) for index in range(len(core.public_inputs))),
        *(base.ConstantRef(index) for index in range(len(core.constants))),
    }
    bound_public: set[int] = set()
    binding_triples: set[tuple[object, ...]] = set()
    for binding in core.public_bindings:
        if not 0 <= binding.scope < len(core.scopes):
            _fail("Refused", "F0V2B2C1B2-R-SCOPE-REF", "binding scope is absent")
        _value_type(core, outputs, binding.value)
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
                    "F0V2B2C1B2-R-BINDING-AVAILABILITY",
                    "scope binding is not unconditionally available before opening",
                )
        if type(binding.value) is base.PublicInputRef:
            bound_public.add(binding.value.ordinal)
        triple = (binding.scope, binding.binding_class, binding.value)
        if triple in binding_triples:
            _fail(
                "Refused",
                "F0V2B2C1B2-R-DUPLICATE-BINDING",
                "public binding triple is duplicated",
            )
        binding_triples.add(triple)
    if bound_public != set(range(len(core.public_inputs))):
        _fail(
            "Refused",
            "F0V2B2C1B2-R-BINDING-COMPLETENESS",
            "public inputs lack complete binding coverage",
        )
    paths = _scope_paths(core)
    publications: dict[int, int] = {}
    queries: dict[int, QueryOracleEffect] = {}
    answers: dict[int, int] = {}
    terminals: dict[int, list[int]] = {
        index: [] for index in range(len(core.terminals))
    }
    seen_terminal_positions: list[int] = []
    source_guards: dict[object, object] = {}
    for index, occurrence in enumerate(core.occurrences):
        if not 0 <= occurrence.scope < len(core.scopes):
            _fail("Refused", "F0V2B2C1B2-R-SCOPE-REF", "occurrence scope is absent")
        if opening_positions[occurrence.scope] > index:
            _fail("Refused", "F0V2B2C1B2-R-SCOPE-OPENING", "occurrence precedes scope")
        if type(occurrence.guard) is not base.AlwaysGuard:
            _fail(
                "Unsupported",
                "F0V2B2C1B2-U-GUARD",
                "this Oracle slice admits only unconditional lifecycle fixtures",
            )
        effect = occurrence.effect
        reads: tuple[object, ...] = ()
        if type(effect) is PublishOracleEffect:
            if not 0 <= effect.oracle < len(core.oracles):
                _fail(
                    "Refused", "F0V2B2C1B2-R-ORACLE-REF", "publication Oracle is absent"
                )
            oracle = core.oracles[effect.oracle]
            if effect.oracle in publications or occurrence.scope != oracle.scope:
                _fail(
                    "Refused",
                    "F0V2B2C1B2-R-PUBLICATION-BACKLINK",
                    "Oracle publication is duplicate or in another scope",
                )
            publications[effect.oracle] = index
        elif type(effect) is QueryOracleEffect:
            if not 0 <= effect.oracle < len(core.oracles):
                _fail("Refused", "F0V2B2C1B2-R-ORACLE-REF", "query Oracle is absent")
            publication = publications.get(effect.oracle)
            oracle = core.oracles[effect.oracle]
            if publication is None or oracle.scope not in paths[occurrence.scope]:
                _fail(
                    "Refused",
                    "F0V2B2C1B2-R-QUERY-LIFECYCLE",
                    "query precedes publication or leaves the Oracle scope",
                )
            if not _guard_implies(
                occurrence.guard, core.occurrences[publication].guard
            ):
                _fail(
                    "Refused",
                    "F0V2B2C1B2-R-GUARD-IMPLIES",
                    "query guard does not imply its publication guard",
                )
            reads = (effect.index,)
            if _value_type(core, outputs, effect.index) != oracle.index_type:
                _fail(
                    "KindMismatch",
                    "F0V2B2C1B2-K-QUERY-INDEX",
                    "query index type differs from its Oracle",
                )
            queries[index] = effect
        elif type(effect) is AnswerOracleEffect:
            query = queries.get(effect.query)
            if query is None:
                _fail(
                    "Refused",
                    "F0V2B2C1B2-R-ANSWER-BACKLINK",
                    "answer does not name an earlier unmatched query",
                )
            query_occurrence = core.occurrences[effect.query]
            if effect.query in answers or occurrence.scope != query_occurrence.scope:
                _fail(
                    "Refused",
                    "F0V2B2C1B2-R-ANSWER-MATCH",
                    "answer is duplicate or differs from the Query scope",
                )
            if not _guard_implies(occurrence.guard, query_occurrence.guard):
                _fail(
                    "Refused",
                    "F0V2B2C1B2-R-GUARD-IMPLIES",
                    "answer guard does not imply its Query guard",
                )
            if any(
                effect.query < terminal < index for terminal in seen_terminal_positions
            ):
                _fail(
                    "Refused",
                    "F0V2B2C1B2-R-ANSWER-TERMINAL-ORDER",
                    "an active terminal occurs between Query and Answer",
                )
            answers[effect.query] = index
        elif type(effect) is base.TerminalEffect:
            if not 0 <= effect.terminal < len(core.terminals):
                _fail("Refused", "F0V2B2C1B2-R-TERMINAL-REF", "terminal is absent")
            terminals[effect.terminal].append(index)
            seen_terminal_positions.append(index)
            reads = core.terminals[effect.terminal].public_outputs
        elif type(effect) is not base.ProverMessageEffect:
            _fail("Unsupported", "F0V2B2C1B2-U-EFFECT", "unsupported effect")
        if any(reference not in available for reference in reads):
            _fail(
                "Refused",
                "F0V2B2C1B2-R-VALUE-AVAILABILITY",
                "occurrence reads a future or absent value",
            )
        for reference in reads:
            source = source_guards.get(reference)
            if source is not None and not _guard_implies(occurrence.guard, source):
                _fail(
                    "Refused", "F0V2B2C1B2-R-GUARD-IMPLIES", "guard implication fails"
                )
        for output in range(len(outputs[index])):
            reference = base.OccurrenceOutputRef(index, output)
            available.add(reference)
            source_guards[reference] = occurrence.guard
    if set(publications) != set(range(len(core.oracles))):
        _fail(
            "Refused",
            "F0V2B2C1B2-R-PUBLICATION-BACKLINK",
            "every Oracle does not have exactly one publication",
        )
    if set(queries) != set(answers):
        _fail(
            "Refused",
            "F0V2B2C1B2-R-ANSWER-TOTALITY",
            "every query does not have exactly one answer",
        )
    if any(len(items) != 1 for items in terminals.values()):
        _fail(
            "Refused",
            "F0V2B2C1B2-R-TERMINAL-BACKLINK",
            "terminal backlinks are not one-to-one",
        )
    final = core.occurrences[-1]
    if (
        type(final.guard) is not base.AlwaysGuard
        or type(final.effect) is not base.TerminalEffect
    ):
        _fail("Refused", "F0V2B2C1B2-R-FINAL-FALLBACK", "final fallback differs")
    return outputs


def _producer_node(reference: object) -> tuple[int, ...]:
    if type(reference) is base.PublicInputRef:
        return (0, reference.ordinal)
    if type(reference) is base.ConstantRef:
        return (2, reference.ordinal)
    if type(reference) is base.OccurrenceOutputRef:
        return (8, reference.occurrence, reference.output_ordinal)
    _fail("Malformed", "F0V2B2C1B2-M-VALUE-REF", "producer is outside the slice")
    raise AssertionError("unreachable")


def _pc_value(node: tuple[int, ...]) -> dict[str, Any]:
    tag, *args = node
    if tag == 8:
        return foundation._v(
            8,
            {
                0: foundation._ordinal("occurrence-ref-body-v0", args[0]),
                1: args[1],
            },
        )
    compiler = {
        0: "public-input-ref-body-v0",
        2: "constant-ref-body-v0",
        4: "scope-ref-body-v0",
        5: "binding-ref-body-v0",
        6: "occurrence-ref-body-v0",
        7: "occurrence-ref-body-v0",
        11: "terminal-ref-body-v0",
    }.get(tag)
    if compiler is None or len(args) != 1:
        raise OracleFailure("CheckerFailure", "F0V2B2C1B2-CHECKER", "bad PCNode")
    return foundation._v(tag, foundation._ordinal(compiler, args[0]))


_PC_GRAPH_SCHEMA = codec.record_field(VIEW_SCHEMAS["PublicCoinView"], 1)
_PC_NODE_SCHEMA = codec.record_field(_PC_GRAPH_SCHEMA, 0)["element"]
_PC_EDGE_SCHEMA = codec.record_field(_PC_GRAPH_SCHEMA, 1)["element"]


def _pc_key(node: tuple[int, ...]) -> bytes:
    return codec.encode_value(_PC_NODE_SCHEMA, _pc_value(node))


def _edge_value(pair: tuple[tuple[int, ...], tuple[int, ...]]) -> dict[int, Any]:
    return {0: _pc_value(pair[0]), 1: _pc_value(pair[1])}


def _edge_key(pair: tuple[tuple[int, ...], tuple[int, ...]]) -> bytes:
    return codec.encode_value(_PC_EDGE_SCHEMA, _edge_value(pair))


def _oracle_lifecycle(
    core: object,
) -> tuple[dict[int, int], dict[int, tuple[int, ...]], dict[int, tuple[int, ...]]]:
    publications: dict[int, int] = {}
    queries: dict[int, list[int]] = {index: [] for index in range(len(core.oracles))}
    answers: dict[int, list[int]] = {index: [] for index in range(len(core.oracles))}
    for occurrence_ref, occurrence in enumerate(core.occurrences):
        effect = occurrence.effect
        if type(effect) is PublishOracleEffect:
            publications[effect.oracle] = occurrence_ref
        elif type(effect) is QueryOracleEffect:
            queries[effect.oracle].append(occurrence_ref)
        elif type(effect) is AnswerOracleEffect:
            query = core.occurrences[effect.query].effect
            answers[query.oracle].append(occurrence_ref)
    return (
        publications,
        {key: tuple(value) for key, value in queries.items()},
        {key: tuple(value) for key, value in answers.items()},
    )


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
    for ordinal in range(len(core.constants)):
        add((2, ordinal))
    for ordinal, scope in enumerate(core.scopes):
        add((4, ordinal))
        if scope.parent is not None:
            edge((4, scope.parent), (4, ordinal))
    for ordinal, binding in enumerate(core.public_bindings):
        edge((4, binding.scope), (5, ordinal))
        edge(_producer_node(binding.value), (5, ordinal))

    publications, _queries, _answers = _oracle_lifecycle(core)
    terminal_positions: dict[int, int] = {}
    earlier_terminals: list[tuple[int, ...]] = []
    for occurrence_ref, occurrence in enumerate(core.occurrences):
        activity = add((6, occurrence_ref))
        effect_node = add((7, occurrence_ref))
        edge((4, occurrence.scope), activity)
        for terminal in earlier_terminals:
            edge(terminal, activity)
        edge(activity, effect_node)
        effect = occurrence.effect
        if type(effect) is QueryOracleEffect:
            edge((7, publications[effect.oracle]), effect_node)
            edge(_producer_node(effect.index), effect_node)
        elif type(effect) is AnswerOracleEffect:
            query = core.occurrences[effect.query].effect
            edge((7, effect.query), effect_node)
            edge((7, publications[query.oracle]), effect_node)
        elif type(effect) is base.TerminalEffect:
            for reference in core.terminals[effect.terminal].public_outputs:
                edge(_producer_node(reference), effect_node)
            terminal = add((11, effect.terminal))
            edge(effect_node, terminal)
            terminal_positions[effect.terminal] = occurrence_ref
            earlier_terminals.append(terminal)
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
        current = available.pop(0)
        topological.append(current)
        for target in outgoing[current]:
            remaining[target].remove(current)
            if (
                not remaining[target]
                and target not in topological
                and target not in available
            ):
                available.append(target)
        available.sort(key=_pc_key)
    if len(topological) != len(nodes):
        _fail("Refused", "F0V2B2C1B2-R-PCGRAPH-CYCLE", "Oracle PCGraph is cyclic")

    classes: dict[tuple[int, ...], int] = {}
    for node in topological:
        joined = max((classes[parent] for parent in incoming[node]), default=0)
        if node[0] in (0, 2):
            value = 0
        elif node[0] == 7:
            effect = core.occurrences[node[1]].effect
            if type(effect) in (base.ProverMessageEffect, PublishOracleEffect):
                value = 1 if joined <= 1 else joined
            elif type(effect) is QueryOracleEffect:
                if effect.visibility is OracleVisibility.VERIFIER_ONLY:
                    value = 2
                else:
                    value = max(
                        classes[(6, node[1])],
                        classes[_producer_node(effect.index)],
                    )
            elif type(effect) is AnswerOracleEffect:
                query = core.occurrences[effect.query].effect
                value = (
                    2
                    if query.visibility is OracleVisibility.VERIFIER_ONLY
                    else (1 if classes[(6, node[1])] <= 1 else classes[(6, node[1])])
                )
            else:
                value = joined
        else:
            value = joined
        classes[node] = value

    activities = {(6, index) for index in range(len(core.occurrences))}
    terminal_nodes = {(11, index) for index in range(len(core.terminals))}
    terminal_outputs = {
        _producer_node(reference)
        for terminal in core.terminals
        for reference in terminal.public_outputs
    }
    public_observations: set[tuple[int, ...]] = set()
    for index, occurrence in enumerate(core.occurrences):
        effect = occurrence.effect
        if type(effect) is PublishOracleEffect:
            oracle = core.oracles[effect.oracle]
            if type(oracle.publication_mode) is LogicalAccessOracle:
                public_observations.add((7, index))
            else:
                public_observations.update(
                    (8, index, output) for output in range(len(outputs[index]))
                )
        elif (
            type(effect) is QueryOracleEffect
            and effect.visibility is OracleVisibility.PUBLIC
        ):
            public_observations.add((7, index))
        elif type(effect) is AnswerOracleEffect:
            query = core.occurrences[effect.query].effect
            if query.visibility is OracleVisibility.PUBLIC:
                public_observations.add((8, index, 0))
        elif type(effect) is base.ProverMessageEffect:
            public_observations.add((8, index, 0))
    sinks = activities | terminal_nodes | terminal_outputs | public_observations
    accepting = {
        (11, index)
        for index, terminal in enumerate(core.terminals)
        if terminal.verdict is base.TerminalVerdict.ACCEPT
    }
    acceptance = accepting | {
        _producer_node(reference)
        for index, terminal in enumerate(core.terminals)
        if (11, index) in accepting
        for reference in terminal.public_outputs
    }
    logical_entries: list[dict[int, Any]] = []
    logical_intersections: list[tuple[int, ...]] = []
    for oracle_ref, oracle in enumerate(core.oracles):
        if type(oracle.publication_mode) is not LogicalAccessOracle:
            continue
        source = (7, publications[oracle_ref])
        seen = {source}
        pending = [source]
        while pending:
            current = pending.pop()
            for child in outgoing[current]:
                if child not in seen:
                    seen.add(child)
                    pending.append(child)
        intersection = seen & acceptance
        logical_intersections.extend(intersection)
        logical_entries.append(
            {
                0: foundation._ordinal("oracle-ref-body-v0", oracle_ref),
                1: [_pc_value(item) for item in sorted(seen, key=_pc_key)],
                2: [_pc_value(item) for item in sorted(intersection, key=_pc_key)],
            }
        )
    eligible = (
        all(classes[node] in (0, 1) for node in sinks) and not logical_intersections
    )
    ordered_nodes = sorted(nodes, key=_pc_key)
    ordered_edges = sorted(edges, key=_edge_key)
    graph = {
        0: [_pc_value(node) for node in ordered_nodes],
        1: [_edge_value(pair) for pair in ordered_edges],
        2: [_pc_value(node) for node in topological],
        3: [
            {0: _pc_value(node), 1: foundation._v(classes[node])}
            for node in ordered_nodes
        ],
        4: [_pc_value(node) for node in sorted(sinks, key=_pc_key)],
        5: [_pc_value(node) for node in sorted(acceptance, key=_pc_key)],
        6: logical_entries,
    }
    return graph, {
        "eligible": eligible,
        "classes": classes,
        "terminal_positions": terminal_positions,
        "nodes": len(nodes),
        "edges": len(edges),
        "logical_intersections": len(logical_intersections),
    }


def admit_core(candidate: object, environment: object) -> OracleAdmissionResult:
    try:
        if type(candidate) is not b2c0.CanonicalCoreCandidate:
            _fail("Malformed", "F0V2B2C1B2-M-REQUEST", "Core request is malformed")
        if type(environment) is not base.Environment:
            _fail("Malformed", "F0V2B2C1B2-M-ENVIRONMENT", "environment is malformed")
        if candidate.profile_id != environment.profile_id:
            _fail("KindMismatch", "F0V2B2C1B2-K-REQUEST-PROFILE", "profiles differ")
        if environment.profile_id != base.target_profile_id():
            _fail(
                "KindMismatch", "F0V2B2C1B2-K-TARGET-PROFILE", "profile is unsupported"
            )
        profile, domain, domain_body = b2c0._strict_profiled_body(
            candidate.profiled_body, "B2C1B2 Oracle Core"
        )
        if profile != candidate.profile_id:
            _fail("KindMismatch", "F0V2B2C1B2-K-BODY-PROFILE", "body profile differs")
        if (
            type(candidate.asserted_id) is not k1.TypedContentId
            or candidate.asserted_id.subject_kind != base.TARGET_CORE_KIND
        ):
            _fail("KindMismatch", "F0V2B2C1B2-K-CORE-ID", "Core ID kind differs")
        try:
            k1.authenticate_content_id(
                candidate.asserted_id,
                candidate.profiled_body,
                environment.prior_meta_preimages,
            )
        except Exception as error:
            _fail("Malformed", "F0V2B2C1B2-M-CORE-ID", str(error))
        core = decode_core(domain)
        closure = b2c0.snapshot_environment(environment)
        functions = _authenticate_algorithms(core, environment)
        outputs = _validate_core(core, environment, functions)
        _graph_value, graph_evidence = _graph(core, outputs)
        if any(
            graph_evidence["classes"][(5, ordinal)] not in (0, 1)
            for ordinal in range(len(core.public_bindings))
        ):
            _fail(
                "Refused",
                "F0V2B2C1B2-R-PRIVATE-BINDING",
                "a public binding depends on verifier-private or invalid data",
            )
        summary = (
            ("slice", "F0-V2B2C1B2"),
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
            tuple(range(1, 13)),
            b2c0._CORE_ISSUER,
        )
        return OracleAdmissionResult(
            "Affirmative",
            "F0V2B2C1B2-A-CORE-ADMITTED",
            "exact bytes passed the bounded Oracle owner evaluator",
            handle,
        )
    except OracleFailure as error:
        return OracleAdmissionResult(error.outcome, error.code, error.detail)
    except b2c0.SnapshotFailure as error:
        return OracleAdmissionResult(error.outcome, error.code, error.detail)
    except Exception as error:  # pragma: no cover - fail-closed defect lane
        return OracleAdmissionResult("CheckerFailure", "F0V2B2C1B2-CHECKER", str(error))


def _retained_core(handle: object) -> tuple[object, tuple[tuple[object, ...], ...]]:
    if (
        type(handle) is not b2c0.AdmittedCoreSnapshot
        or not handle._issued_by(b2c0._CORE_ISSUER)
        or handle.evaluator_fingerprint != EVALUATOR_FINGERPRINT
    ):
        _fail("Refused", "F0V2B2C1B2-R-CORE-AUTHORITY", "Core authority differs")
    summary = dict(handle.structural_summary)
    if (
        summary.get("slice") != "F0-V2B2C1B2"
        or type(summary.get("core")) is not base.InteractiveCore
    ):
        _fail("Refused", "F0V2B2C1B2-R-RETAINED-FACTS", "retained facts differ")
    core = summary["core"]
    profile = k1.decode_content_reference(handle.profile_reference)
    if core_profiled_body(core, profile) != handle.profiled_body:
        _fail("Refused", "F0V2B2C1B2-R-RETAINED-BODY", "retained body differs")
    return core, summary["output_types"]


def admit_fresh_protocol(
    core_handle: object, candidate: object, environment: object
) -> OracleAdmissionResult:
    try:
        _retained_core(core_handle)
        if type(candidate) is not b2c0.CanonicalFreshProtocolCandidate:
            _fail(
                "Malformed", "F0V2B2C1B2-M-PROTOCOL-REQUEST", "Protocol request differs"
            )
        profile, domain, _domain_body = b2c0._strict_profiled_body(
            candidate.profiled_body, "B2C1B2 Fresh Protocol"
        )
        if (
            profile.internal_reference() != core_handle.profile_reference
            or candidate.profile_id.internal_reference()
            != core_handle.profile_reference
        ):
            _fail(
                "KindMismatch",
                "F0V2B2C1B2-K-PROTOCOL-PROFILE",
                "Protocol profile differs",
            )
        core_ref, interpretation = b2c0._record(domain, (0, 1), "Fresh Protocol")
        referenced_core = b2c0._content_ref(core_ref, "Protocol Core")
        if referenced_core.internal_reference() != core_handle.core_reference:
            _fail(
                "Refused", "F0V2B2C1B2-R-PROTOCOL-CORE", "Protocol names another Core"
            )
        interpretation_case, payload = b2c0._variant(
            interpretation, (0,), "Fresh interpretation"
        )
        if interpretation_case != 0:
            _fail("Refused", "F0V2B2C1B2-R-INTERPRETATION", "Protocol is not Fresh")
        b2c0._unit(payload, "Fresh payload")
        if (
            type(candidate.asserted_id) is not k1.TypedContentId
            or candidate.asserted_id.subject_kind != base.TARGET_PROTOCOL_KIND
        ):
            _fail(
                "KindMismatch", "F0V2B2C1B2-K-PROTOCOL-ID", "Protocol ID kind differs"
            )
        try:
            k1.authenticate_content_id(
                candidate.asserted_id,
                candidate.profiled_body,
                environment.prior_meta_preimages,
            )
        except Exception as error:
            _fail("Malformed", "F0V2B2C1B2-M-PROTOCOL-ID", str(error))
        closure = b2c0.snapshot_environment(environment)
        if closure.fingerprint != core_handle.closure.fingerprint:
            _fail("Refused", "F0V2B2C1B2-R-CLOSURE-PAIR", "closure differs")
        handle = b2c0.AdmittedFreshProtocolSnapshot(
            candidate.asserted_id.internal_reference(),
            candidate.profile_id.internal_reference(),
            bytes(candidate.profiled_body),
            core_handle,
            closure.fingerprint,
            EVALUATOR_FINGERPRINT,
            b2c0._PROTOCOL_ISSUER,
        )
        return OracleAdmissionResult(
            "Affirmative",
            "F0V2B2C1B2-A-FRESH-ADMITTED",
            "Fresh Protocol is paired to this Oracle evaluator and exact Core",
            handle,
        )
    except OracleFailure as error:
        return OracleAdmissionResult(error.outcome, error.code, error.detail)
    except b2c0.SnapshotFailure as error:
        return OracleAdmissionResult(error.outcome, error.code, error.detail)
    except Exception as error:  # pragma: no cover
        return OracleAdmissionResult("CheckerFailure", "F0V2B2C1B2-CHECKER", str(error))


def _oracle_carrier_value(oracle: OracleDecl) -> dict[int, Any]:
    return {
        0: foundation._value_type_body(oracle.index_type),
        1: foundation._value_type_body(oracle.element_type),
        2: oracle.maximum_entries,
    }


def _mode_value(mode: object) -> dict[str, Any]:
    if type(mode) is FullCanonicalOracle:
        return foundation._v(0)
    if type(mode) is PublicBindingOracle:
        return foundation._v(
            1,
            {
                0: foundation._value_type_body(mode.binding_type),
                1: foundation._module_ref(mode.binding_contract),
                2: foundation._identifier(
                    "algorithm-ref-body-v0", mode.binding_algorithm
                ),
                3: foundation._identifier(
                    "evaluation-contract-id-body-v0", mode.evaluation_contract
                ),
            },
        )
    return foundation._v(2, foundation._module_ref(mode.domain_law))


def _oracle_value(oracle: OracleDecl) -> dict[int, Any]:
    return {
        0: foundation._ordinal("scope-ref-body-v0", oracle.scope),
        1: foundation._v(oracle.origin.value),
        2: foundation._value_type_body(oracle.index_type),
        3: foundation._value_type_body(oracle.element_type),
        4: oracle.maximum_entries,
        5: _mode_value(oracle.publication_mode),
    }


def _effect_value(effect: object) -> dict[str, Any]:
    if type(effect) is base.ProverMessageEffect:
        return foundation._v(
            0,
            {
                0: foundation._module_ref(effect.channel),
                1: foundation._value_type_body(effect.payload_type),
            },
        )
    if type(effect) is PublishOracleEffect:
        oracle_effect = foundation._v(
            0, foundation._ordinal("oracle-ref-body-v0", effect.oracle)
        )
        return foundation._v(6, oracle_effect)
    if type(effect) is QueryOracleEffect:
        oracle_effect = foundation._v(
            1,
            {
                0: foundation._ordinal("oracle-ref-body-v0", effect.oracle),
                1: foundation._value_ref(effect.index),
                2: foundation._v(effect.visibility.value),
            },
        )
        return foundation._v(6, oracle_effect)
    if type(effect) is AnswerOracleEffect:
        oracle_effect = foundation._v(
            2, foundation._ordinal("occurrence-ref-body-v0", effect.query)
        )
        return foundation._v(6, oracle_effect)
    if type(effect) is base.TerminalEffect:
        return foundation._v(
            5, foundation._ordinal("terminal-ref-body-v0", effect.terminal)
        )
    _fail("Unsupported", "F0V2B2C1B2-U-EFFECT", "unsupported effect")
    raise AssertionError("unreachable")


def _decision_move(core: object, effect: object) -> dict[str, Any] | None:
    if type(effect) is base.ProverMessageEffect:
        return foundation._v(0, foundation._value_type_body(effect.payload_type))
    if type(effect) is PublishOracleEffect:
        oracle = core.oracles[effect.oracle]
        if oracle.origin is OracleOrigin.PROVER:
            return foundation._v(
                1,
                {
                    0: foundation._ordinal("oracle-ref-body-v0", effect.oracle),
                    1: _oracle_carrier_value(oracle),
                    2: _mode_value(oracle.publication_mode),
                },
            )
    return None


def project_views(core_handle: object, protocol_handle: object) -> dict[str, Any]:
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
            "Refused", "F0V2B2C1B2-R-PROTOCOL-AUTHORITY", "Protocol authority differs"
        )
    core_id_value = k1.decode_content_reference(core_handle.core_reference)
    protocol_id_value = k1.decode_content_reference(protocol_handle.protocol_reference)
    core_atom = foundation._identifier("core-id-body-v0", core_id_value)
    protocol_atom = foundation._identifier("protocol-id-body-v0", protocol_id_value)
    paths = _scope_paths(core)
    graph, graph_evidence = _graph(core, outputs)
    publications, queries, answers = _oracle_lifecycle(core)

    public_binding = {
        0: core_atom,
        1: [
            {
                0: foundation._ordinal("scope-ref-body-v0", index),
                1: foundation._v(0)
                if scope.parent is None
                else foundation._v(
                    1, foundation._ordinal("scope-ref-body-v0", scope.parent)
                ),
                2: foundation._v(0)
                if scope.opening is None
                else foundation._v(
                    1,
                    foundation._ordinal("occurrence-ref-body-v0", scope.opening),
                ),
                3: [
                    foundation._ordinal("scope-ref-body-v0", item)
                    for item in paths[index]
                ],
            }
            for index, scope in enumerate(core.scopes)
        ],
        2: [
            {
                0: foundation._ordinal("binding-ref-body-v0", index),
                1: foundation._ordinal("scope-ref-body-v0", binding.scope),
                2: foundation._v(binding.binding_class.value),
                3: foundation._value_ref(binding.value),
                4: foundation._value_type_body(
                    _value_type(core, outputs, binding.value)
                ),
            }
            for index, binding in enumerate(core.public_bindings)
        ],
    }

    decisions = [
        (index, occurrence, move)
        for index, occurrence in enumerate(core.occurrences)
        if (move := _decision_move(core, occurrence.effect)) is not None
    ]
    decision_rows: list[dict[int, Any]] = []
    read_rows: list[dict[int, Any]] = []
    legal_rows: list[dict[int, Any]] = []
    for occurrence_ref, occurrence, move in decisions:
        decision_rows.append(
            {
                0: foundation._ordinal("decision-ref-body-v0", occurrence_ref),
                1: foundation._ordinal("occurrence-ref-body-v0", occurrence_ref),
                2: [
                    foundation._ordinal("scope-ref-body-v0", item)
                    for item in paths[occurrence.scope]
                ],
                3: foundation._guard_body(occurrence.guard),
                4: move,
                5: [
                    foundation._ordinal("decision-ref-body-v0", prior)
                    for prior, _item, _prior_move in decisions
                    if prior < occurrence_ref
                ],
            }
        )
        for index, constant in enumerate(core.constants):
            read_rows.append(
                {
                    0: foundation._ordinal("decision-ref-body-v0", occurrence_ref),
                    1: foundation._v(
                        0, foundation._ordinal("constant-ref-body-v0", index)
                    ),
                    2: foundation._value_type_body(constant.value_type),
                }
            )
        for prior_ref, prior_occurrence in enumerate(core.occurrences[:occurrence_ref]):
            prior_effect = prior_occurrence.effect
            read_case: int | None = None
            read_type: object | None = None
            visible = True
            if type(prior_effect) is base.ProverMessageEffect:
                read_case, read_type = 3, prior_effect.payload_type
            elif type(prior_effect) is PublishOracleEffect:
                read_case = 5
                publication_types = oracle_publication_types(
                    core.oracles[prior_effect.oracle]
                )
                read_type = publication_types[0] if publication_types else k1.UNIT_VALUE
            elif type(prior_effect) is QueryOracleEffect:
                read_case, read_type = 6, core.oracles[prior_effect.oracle].index_type
                visible = prior_effect.visibility is OracleVisibility.PUBLIC
            elif type(prior_effect) is AnswerOracleEffect:
                query = core.occurrences[prior_effect.query].effect
                read_case = 7
                read_type = oracle_answer_type(core.oracles[query.oracle])
                visible = query.visibility is OracleVisibility.PUBLIC
            if (
                read_case is not None
                and visible
                and _guard_implies(occurrence.guard, prior_occurrence.guard)
            ):
                read_rows.append(
                    {
                        0: foundation._ordinal("decision-ref-body-v0", occurrence_ref),
                        1: foundation._v(
                            read_case,
                            foundation._ordinal("occurrence-ref-body-v0", prior_ref),
                        ),
                        2: foundation._value_type_body(read_type),
                    }
                )
            if _decision_move(core, prior_effect) is not None:
                read_rows.append(
                    {
                        0: foundation._ordinal("decision-ref-body-v0", occurrence_ref),
                        1: foundation._v(
                            9, foundation._ordinal("decision-ref-body-v0", prior_ref)
                        ),
                        2: foundation._value_type_body(
                            prior_effect.payload_type
                            if type(prior_effect) is base.ProverMessageEffect
                            else oracle_carrier_type(core.oracles[prior_effect.oracle])
                        ),
                    }
                )
        legal_rows.append(
            {0: foundation._ordinal("decision-ref-body-v0", occurrence_ref), 1: move}
        )
    strategy = {
        0: core_atom,
        1: decision_rows,
        2: foundation._law("core-admission-v0"),
        3: read_rows,
        4: legal_rows,
    }

    public_coin = {0: core_atom, 1: graph, 2: graph_evidence["eligible"], 3: [], 4: []}

    value_rows: list[dict[int, Any]] = []
    for index, declaration in enumerate(core.public_inputs):
        value_rows.append(
            {
                0: foundation._value_ref(base.PublicInputRef(index)),
                1: foundation._value_type_body(declaration.value_type),
                2: [],
            }
        )
    for index, declaration in enumerate(core.constants):
        value_rows.append(
            {
                0: foundation._value_ref(base.ConstantRef(index)),
                1: foundation._value_type_body(declaration.value_type),
                2: [],
            }
        )
    occurrence_rows: list[dict[int, Any]] = []
    message_rows: list[dict[int, Any]] = []
    for occurrence_ref, occurrence in enumerate(core.occurrences):
        occurrence_rows.append(
            {
                0: foundation._ordinal("occurrence-ref-body-v0", occurrence_ref),
                1: [
                    foundation._ordinal("scope-ref-body-v0", item)
                    for item in paths[occurrence.scope]
                ],
                2: foundation._guard_body(occurrence.guard),
                3: _effect_value(occurrence.effect),
                4: [
                    foundation._value_type_body(item)
                    for item in outputs[occurrence_ref]
                ],
            }
        )
        if type(occurrence.effect) is base.ProverMessageEffect:
            message_rows.append(
                {
                    0: foundation._ordinal("occurrence-ref-body-v0", occurrence_ref),
                    1: foundation._v(0),
                    2: foundation._v(
                        0,
                        {
                            0: foundation._module_ref(occurrence.effect.channel),
                            1: foundation._value_type_body(
                                occurrence.effect.payload_type
                            ),
                        },
                    ),
                }
            )
        for output, output_type in enumerate(outputs[occurrence_ref]):
            predecessors: list[dict[str, str]] = []
            if type(occurrence.effect) is AnswerOracleEffect:
                query = core.occurrences[occurrence.effect.query].effect
                predecessors.append(foundation._value_ref(query.index))
            value_rows.append(
                {
                    0: foundation._value_ref(
                        base.OccurrenceOutputRef(occurrence_ref, output)
                    ),
                    1: foundation._value_type_body(output_type),
                    2: predecessors,
                }
            )
    oracle_rows = [
        {
            0: foundation._ordinal("oracle-ref-body-v0", oracle_ref),
            1: _oracle_value(oracle),
            2: foundation._ordinal("occurrence-ref-body-v0", publications[oracle_ref]),
            3: [
                foundation._ordinal("occurrence-ref-body-v0", item)
                for item in queries[oracle_ref]
            ],
            4: [
                foundation._ordinal("occurrence-ref-body-v0", item)
                for item in answers[oracle_ref]
            ],
        }
        for oracle_ref, oracle in enumerate(core.oracles)
    ]
    terminal_rows = [
        {
            0: foundation._ordinal("terminal-ref-body-v0", index),
            1: foundation._v(terminal.verdict.value),
            2: [foundation._value_ref(item) for item in terminal.public_outputs],
            3: [],
            4: [],
            5: foundation._ordinal(
                "occurrence-ref-body-v0", graph_evidence["terminal_positions"][index]
            ),
        }
        for index, terminal in enumerate(core.terminals)
    ]
    effect = {
        0: core_atom,
        1: occurrence_rows,
        2: value_rows,
        3: message_rows,
        4: oracle_rows,
        5: [],
        6: terminal_rows,
        7: [],
    }

    oracle_receipts: list[dict[str, Any]] = []
    for occurrence_ref, occurrence in enumerate(core.occurrences):
        item = occurrence.effect
        if type(item) is PublishOracleEffect:
            oracle_receipts.append(
                foundation._v(
                    0,
                    {
                        0: foundation._ordinal(
                            "occurrence-ref-body-v0", occurrence_ref
                        ),
                        1: foundation._ordinal("oracle-ref-body-v0", item.oracle),
                        2: [
                            foundation._value_type_body(value_type)
                            for value_type in outputs[occurrence_ref]
                        ],
                    },
                )
            )
        elif type(item) is QueryOracleEffect:
            oracle_receipts.append(
                foundation._v(
                    1,
                    {
                        0: foundation._ordinal(
                            "occurrence-ref-body-v0", occurrence_ref
                        ),
                        1: foundation._ordinal("oracle-ref-body-v0", item.oracle),
                        2: foundation._value_type_body(
                            core.oracles[item.oracle].index_type
                        ),
                        3: foundation._v(item.visibility.value),
                    },
                )
            )
        elif type(item) is AnswerOracleEffect:
            query = core.occurrences[item.query].effect
            oracle_receipts.append(
                foundation._v(
                    2,
                    {
                        0: foundation._ordinal(
                            "occurrence-ref-body-v0", occurrence_ref
                        ),
                        1: foundation._ordinal("oracle-ref-body-v0", query.oracle),
                        2: foundation._value_type_body(
                            oracle_answer_type(core.oracles[query.oracle])
                        ),
                        3: foundation._v(query.visibility.value),
                    },
                )
            )
    runtime = {
        0: [
            {
                0: foundation._ordinal("occurrence-ref-body-v0", index),
                1: [foundation._value_type_body(item) for item in outputs[index]],
            }
            for index in range(len(core.occurrences))
        ],
        1: [],
        2: oracle_receipts,
        3: [
            {
                0: foundation._ordinal("terminal-ref-body-v0", index),
                1: foundation._ordinal(
                    "occurrence-ref-body-v0",
                    graph_evidence["terminal_positions"][index],
                ),
                2: foundation._v(terminal.verdict.value),
                3: [
                    foundation._value_type_body(_value_type(core, outputs, item))
                    for item in terminal.public_outputs
                ],
            }
            for index, terminal in enumerate(core.terminals)
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
        "EffectView": effect,
        "ClaimReductionView": {0: core_atom, 1: [], 2: [], 3: []},
        "ExecutionView": execution,
    }


def _nominal(symbol: str) -> object:
    return _record(k1.Symbol(symbol))


def _catalog(kind: str, values: tuple[object, ...]) -> object:
    return _record(k1.Symbol(kind), _seq(values))


def oracle_module(
    index_type: object, exact_indices: tuple[object, ...] | None = None
) -> object:
    if exact_indices is None:
        exact_indices = (k1.Nat(0), k1.Nat(1))
    domain_law = _record(
        k1.value_type_datum(index_type),
        _seq(exact_indices),
    )
    return k1.SemanticModuleCandidate(
        k1.Symbol("f0v2b2c1b2.oracle-fixture"),
        (),
        _seq(
            (
                _catalog("pir.message-channel", (_nominal("oracle-observer"),)),
                _catalog("pir.oracle-binding-contract", (_nominal("fixture-binding"),)),
                _catalog("pir.oracle-domain-law", (domain_law,)),
            )
        ),
    )


def binding_algorithm(oracle: OracleDecl, output_type: object) -> object:
    return k1.CanonicalAlgorithm(
        k1.Symbol("F0V2B2C1B2OracleBinding"),
        (oracle_carrier_type(oracle),),
        k1.Literal(k1.admit_value(output_type, k1.Nat(1))),
    )


def _environment(
    core: object,
    module: object | None,
    algorithms: tuple[object, ...],
) -> object:
    base_environment = base.make_fixture().environment
    contract = k1.DEFAULT_EVALUATION_CONTRACT
    contracts = (
        {contract.identity: contract}
        if any(
            type(oracle.publication_mode) is PublicBindingOracle
            for oracle in core.oracles
        )
        else {}
    )
    module_map = {} if module is None else {module.identity: module}
    return base.Environment(
        base_environment.profile_id,
        base_environment.profile_preimages,
        MappingProxyType(module_map),
        MappingProxyType({item.identity: item for item in algorithms}),
        MappingProxyType({item.identity: MappingProxyType({}) for item in algorithms}),
        MappingProxyType(contracts),
    )


def _fixture(
    origin: OracleOrigin,
    mode_name: str,
    visibility: OracleVisibility = OracleVisibility.PUBLIC,
    *,
    observed: bool = False,
    verifier_sink: bool = False,
) -> tuple[object, object]:
    module = oracle_module(base.Z3)
    module_id = module.identity
    binding_contract = base.ModuleDeclarationRef(
        module_id, "pir.oracle-binding-contract", 0
    )
    domain_law = base.ModuleDeclarationRef(module_id, "pir.oracle-domain-law", 0)
    message_channel = base.ModuleDeclarationRef(module_id, "pir.message-channel", 0)
    provisional = OracleDecl(0, origin, base.Z3, base.Z3, 2, FullCanonicalOracle())
    algorithms: tuple[object, ...] = ()
    if mode_name == "full":
        mode: object = FullCanonicalOracle()
    elif mode_name == "binding":
        algorithm = binding_algorithm(provisional, base.Z3)
        algorithms = (algorithm,)
        mode = PublicBindingOracle(
            base.Z3,
            binding_contract,
            algorithm.identity,
            k1.DEFAULT_EVALUATION_CONTRACT.identity,
        )
    elif mode_name == "logical":
        mode = LogicalAccessOracle(domain_law)
    else:
        raise ValueError(mode_name)
    oracle = replace(provisional, publication_mode=mode)
    scopes = (
        (base.ScopeDecl(None, None), base.ScopeDecl(0, 0))
        if observed
        else (base.ScopeDecl(None, None),)
    )
    query_scope = 1 if observed else 0
    occurrences: list[object] = [
        base.OccurrenceDecl(0, base.AlwaysGuard(), PublishOracleEffect(0)),
        base.OccurrenceDecl(
            query_scope,
            base.AlwaysGuard(),
            QueryOracleEffect(0, base.ConstantRef(0), visibility),
        ),
        base.OccurrenceDecl(query_scope, base.AlwaysGuard(), AnswerOracleEffect(1)),
    ]
    if observed:
        occurrences.append(
            base.OccurrenceDecl(
                query_scope,
                base.AlwaysGuard(),
                base.ProverMessageEffect(message_channel, base.Z3),
            )
        )
    terminal_output: tuple[object, ...] = ()
    if mode_name != "logical" or verifier_sink:
        terminal_output = (base.OccurrenceOutputRef(2, 0),)
    terminals = (
        base.TerminalDecl(base.TerminalVerdict.ACCEPT, terminal_output, (), ()),
    )
    occurrences.append(
        base.OccurrenceDecl(0, base.AlwaysGuard(), base.TerminalEffect(0))
    )
    refs = list(_mode_module_refs(mode))
    if observed:
        refs.append(message_channel)
    used_modules = tuple(
        sorted(
            {item.module for item in refs}, key=lambda item: item.internal_reference()
        )
    )
    core = base.InteractiveCore(
        used_modules,
        (),
        (),
        (base.TypedConstantDecl(base.Z3, k1.admit_value(base.Z3, k1.Nat(1))),),
        (),
        scopes,
        (),
        (),
        (oracle,),
        (),
        (),
        (),
        terminals,
        tuple(occurrences),
    )
    environment = _environment(core, module if used_modules else None, algorithms)
    return environment, make_candidate(core, environment.profile_id)


def fixtures() -> dict[str, tuple[object, object]]:
    return {
        "oracle-initial-full": _fixture(OracleOrigin.INITIAL, "full"),
        "oracle-initial-binding": _fixture(OracleOrigin.INITIAL, "binding"),
        "oracle-initial-logical": _fixture(OracleOrigin.INITIAL, "logical"),
        "oracle-prover-full": _fixture(OracleOrigin.PROVER, "full"),
        "oracle-prover-binding": _fixture(OracleOrigin.PROVER, "binding"),
        "oracle-prover-logical": _fixture(OracleOrigin.PROVER, "logical"),
        "oracle-query-public": _fixture(OracleOrigin.INITIAL, "full", observed=True),
        "oracle-query-verifier-only": _fixture(
            OracleOrigin.INITIAL,
            "full",
            OracleVisibility.VERIFIER_ONLY,
            verifier_sink=True,
        ),
    }


def logical_acceptance_fixture() -> tuple[object, object]:
    """Return an admitted Core with a valid Fresh pairing and logical acceptance use."""

    return _fixture(OracleOrigin.INITIAL, "logical", verifier_sink=True)


def mutate_core(name: str, mutation: str) -> tuple[object, object]:
    environment, candidate = fixtures()[name]
    core = decode_core(k1.decode_datum(candidate.profiled_body).fields[1][1])
    occurrences = list(core.occurrences)
    oracles = list(core.oracles)
    if mutation == "duplicate-answer":
        occurrences.insert(-1, occurrences[2])
    elif mutation == "duplicate-publication":
        occurrences.insert(1, occurrences[0])
        answer = occurrences[3]
        occurrences[3] = base.OccurrenceDecl(
            answer.scope, answer.guard, AnswerOracleEffect(2)
        )
        terminal = core.terminals[0]
        core = replace(
            core,
            terminals=(
                replace(
                    terminal,
                    public_outputs=(base.OccurrenceOutputRef(3, 0),),
                ),
            ),
        )
    elif mutation == "answer-scope":
        if len(core.scopes) == 1:
            raise ValueError("answer-scope mutation requires a child scope fixture")
        item = occurrences[2]
        occurrences[2] = base.OccurrenceDecl(0, item.guard, item.effect)
    elif mutation == "binding-abi":
        oracle = oracles[0]
        mode = oracle.publication_mode
        if type(mode) is not PublicBindingOracle:
            raise ValueError("binding-abi mutation requires binding mode")
        wrong = k1.CanonicalAlgorithm(
            k1.Symbol("F0V2B2C1B2WrongBinding"),
            (base.Z3,),
            k1.Literal(k1.admit_value(base.Z3, k1.Nat(1))),
        )
        mode = replace(mode, binding_algorithm=wrong.identity)
        oracles[0] = replace(oracle, publication_mode=mode)
        environment = replace(
            environment,
            algorithm_preimages=MappingProxyType({wrong.identity: wrong}),
            algorithm_modules=MappingProxyType({wrong.identity: MappingProxyType({})}),
        )
    elif mutation == "domain-law-kind":
        oracle = oracles[0]
        mode = oracle.publication_mode
        if type(mode) is not LogicalAccessOracle:
            raise ValueError("domain mutation requires logical mode")
        wrong = replace(mode.domain_law, declaration_kind="pir.message-channel")
        oracles[0] = replace(oracle, publication_mode=replace(mode, domain_law=wrong))
    elif mutation == "domain-law-order":
        oracle = oracles[0]
        mode = oracle.publication_mode
        if type(mode) is not LogicalAccessOracle:
            raise ValueError("domain mutation requires logical mode")
        wrong_module = oracle_module(base.Z3, (k1.Nat(1), k1.Nat(0)))
        wrong_ref = base.ModuleDeclarationRef(
            wrong_module.identity, "pir.oracle-domain-law", 0
        )
        oracles[0] = replace(
            oracle, publication_mode=replace(mode, domain_law=wrong_ref)
        )
        core = replace(core, used_modules=(wrong_module.identity,))
        environment = replace(
            environment,
            module_preimages=MappingProxyType({wrong_module.identity: wrong_module}),
        )
    elif mutation == "answer-after-terminal":
        answer = occurrences[2]
        terminal = core.terminals[0]
        occurrences = [
            occurrences[0],
            occurrences[1],
            base.OccurrenceDecl(0, base.AlwaysGuard(), base.TerminalEffect(0)),
            answer,
            base.OccurrenceDecl(0, base.AlwaysGuard(), base.TerminalEffect(1)),
        ]
        core = replace(
            core,
            terminals=(
                base.TerminalDecl(base.TerminalVerdict.REJECT, (), (), ()),
                replace(
                    terminal,
                    public_outputs=(base.OccurrenceOutputRef(3, 0),),
                ),
            ),
        )
    else:
        raise ValueError(mutation)
    core = replace(core, oracles=tuple(oracles), occurrences=tuple(occurrences))
    if mutation == "duplicate-answer":
        # The inserted answer moves the terminal backlink but intentionally
        # leaves the second Answer naming the same Query.
        terminal = occurrences[-1]
        occurrences[-1] = base.OccurrenceDecl(
            terminal.scope, terminal.guard, base.TerminalEffect(0)
        )
        core = replace(core, occurrences=tuple(occurrences))
    return environment, make_candidate(core, environment.profile_id)
