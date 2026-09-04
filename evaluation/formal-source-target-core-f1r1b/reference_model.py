#!/usr/bin/env python3
"""Bounded exact-target InteractiveCore carrier and admission witness.

This module is a research falsifier.  It implements the complete Appendix-A
carrier and the applicable admission laws for one deliberately small target
slice.  Unsupported target families fail closed; this is not a production PIR
owner or a general implementation of ``core-admission-v0``.
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from enum import Enum
import importlib.util
from pathlib import Path
import sys
from types import MappingProxyType, ModuleType
from typing import Mapping, TypeAlias


ROOT = Path(__file__).resolve().parents[2]
PUBLICATION_MODEL = (
    ROOT / "evaluation" / "semantic-profile-publication" / "reference_model.py"
)


def _load_module(name: str, path: Path) -> ModuleType:
    if name in sys.modules:
        return sys.modules[name]
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:  # pragma: no cover - host failure
        raise ImportError(f"cannot load module at {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


publication = _load_module("_zkc_f1r1b_publication", PUBLICATION_MODEL)
k1 = publication.k1

MAX_LOCAL_ITEMS = 1 << 14
TARGET_PROFILE_KEY = "interaction"
TARGET_CORE_KIND = "pir.interactive-core"
TARGET_PROTOCOL_KIND = "pir.protocol"


class AdmissionFailure(ValueError):
    """One stable, classified refusal at the bounded owner boundary."""

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


class BindingClass(Enum):
    STATEMENT = 0
    SESSION_CONTEXT = 1
    PUBLIC_PARAMETER = 2


class TerminalVerdict(Enum):
    ACCEPT = 0
    REJECT = 1
    ABORT = 2


class ClaimUsage(Enum):
    LINEAR = 0
    REUSABLE = 1


class ClaimDisposition(Enum):
    CONSUME = 0
    DISCHARGE = 1


@dataclass(frozen=True)
class ModuleDeclarationRef:
    module: object
    declaration_kind: str
    local_ordinal: int


@dataclass(frozen=True)
class PublicInputRef:
    ordinal: int


@dataclass(frozen=True)
class VerifierPrivateInputRef:
    ordinal: int


@dataclass(frozen=True)
class ConstantRef:
    ordinal: int


@dataclass(frozen=True)
class DerivedValueRef:
    ordinal: int


@dataclass(frozen=True)
class OccurrenceOutputRef:
    occurrence: int
    output_ordinal: int


ValueRef: TypeAlias = (
    PublicInputRef
    | VerifierPrivateInputRef
    | ConstantRef
    | DerivedValueRef
    | OccurrenceOutputRef
)


@dataclass(frozen=True)
class InputDecl:
    value_type: object


@dataclass(frozen=True)
class TypedConstantDecl:
    value_type: object
    value: object


@dataclass(frozen=True)
class DerivedValueDecl:
    algorithm: object
    evaluation_contract: object
    inputs: tuple[ValueRef, ...]
    result_type: object


@dataclass(frozen=True)
class ScopeDecl:
    parent: int | None
    opening: int | None


@dataclass(frozen=True)
class PublicBindingDecl:
    scope: int
    binding_class: BindingClass
    value: ValueRef


@dataclass(frozen=True)
class IndependentCorrelation:
    pass


@dataclass(frozen=True)
class JointCorrelation:
    group: ModuleDeclarationRef
    index: int
    prior_members: tuple[int, ...]


CoinCorrelation: TypeAlias = IndependentCorrelation | JointCorrelation


@dataclass(frozen=True)
class ExclusiveReductionUse:
    pass


@dataclass(frozen=True)
class SharedReductionUse:
    contract: ModuleDeclarationRef


ReductionUse: TypeAlias = ExclusiveReductionUse | SharedReductionUse


@dataclass(frozen=True)
class ChallengeDecl:
    scope: int
    value_type: object
    domain: ModuleDeclarationRef
    fresh_law: ModuleDeclarationRef
    correlation: CoinCorrelation
    reduction_use: ReductionUse
    public_conditions: tuple[ValueRef, ...]


@dataclass(frozen=True)
class CheckDecl:
    algorithm: object
    evaluation_contract: object
    inputs: tuple[ValueRef, ...]


@dataclass(frozen=True)
class ClaimDecl:
    contract: ModuleDeclarationRef
    scope: int
    usage: ClaimUsage
    source_binding: int


@dataclass(frozen=True)
class ClaimDispositionEntry:
    claim: int
    disposition: ClaimDisposition


@dataclass(frozen=True)
class TerminalDecl:
    verdict: TerminalVerdict
    public_outputs: tuple[ValueRef, ...]
    required_true_checks: tuple[int, ...]
    claim_dispositions: tuple[ClaimDispositionEntry, ...]


@dataclass(frozen=True)
class AlwaysGuard:
    pass


@dataclass(frozen=True)
class EvaluateGuard:
    algorithm: object
    evaluation_contract: object
    inputs: tuple[ValueRef, ...]


Guard: TypeAlias = AlwaysGuard | EvaluateGuard


@dataclass(frozen=True)
class ProverMessageEffect:
    channel: ModuleDeclarationRef
    payload_type: object


@dataclass(frozen=True)
class ChallengeEffect:
    challenge: int


@dataclass(frozen=True)
class CheckEffect:
    check: int


@dataclass(frozen=True)
class TerminalEffect:
    terminal: int


Effect: TypeAlias = ProverMessageEffect | ChallengeEffect | CheckEffect | TerminalEffect


@dataclass(frozen=True)
class OccurrenceDecl:
    scope: int
    guard: Guard
    effect: Effect


@dataclass(frozen=True)
class InteractiveCore:
    used_modules: tuple[object, ...]
    public_inputs: tuple[InputDecl, ...]
    verifier_private_inputs: tuple[InputDecl, ...]
    constants: tuple[TypedConstantDecl, ...]
    derived_values: tuple[DerivedValueDecl, ...]
    scopes: tuple[ScopeDecl, ...]
    public_bindings: tuple[PublicBindingDecl, ...]
    challenges: tuple[ChallengeDecl, ...]
    oracles: tuple[object, ...]
    checks: tuple[CheckDecl, ...]
    claims: tuple[ClaimDecl, ...]
    reductions: tuple[object, ...]
    terminals: tuple[TerminalDecl, ...]
    occurrences: tuple[OccurrenceDecl, ...]


@dataclass(frozen=True)
class CoreCandidate:
    asserted_id: object
    core: InteractiveCore


@dataclass(frozen=True)
class FreshProtocolCandidate:
    asserted_id: object
    core_id: object


@dataclass(frozen=True)
class Environment:
    profile_id: object
    profile_preimages: Mapping[object, object]
    module_preimages: Mapping[object, object]
    algorithm_preimages: Mapping[object, object]
    algorithm_modules: Mapping[object, Mapping[object, object]]
    contract_preimages: Mapping[object, object]
    prior_meta_preimages: object = k1.FOUNDATION_PRIOR_META_PREIMAGES


_CORE_ISSUER = object()
_PROTOCOL_ISSUER = object()


class AdmittedCore:
    """Process-local research handle; serialization carries no authority."""

    __slots__ = (
        "_issuer",
        "core_id",
        "core",
        "profile_id",
        "environment",
        "steps",
    )

    def __init__(
        self,
        core_id: object,
        core: InteractiveCore,
        profile_id: object,
        environment: Environment,
        mint: object,
    ) -> None:
        if mint is not _CORE_ISSUER:
            raise TypeError("only the admission evaluator may mint a Core handle")
        self._issuer = _CORE_ISSUER
        self.core_id = core_id
        self.core = core
        self.profile_id = profile_id
        self.environment = environment
        self.steps = tuple(range(1, 11))

    def __reduce_ex__(self, _protocol: int) -> object:
        raise TypeError("an admitted Core handle is process-local")


class AdmittedFreshProtocol:
    __slots__ = ("_issuer", "protocol_id", "core_handle", "profile_id")

    def __init__(
        self, protocol_id: object, core_handle: AdmittedCore, mint: object
    ) -> None:
        if mint is not _PROTOCOL_ISSUER:
            raise TypeError("only the admission evaluator may mint a Protocol handle")
        self._issuer = _PROTOCOL_ISSUER
        self.protocol_id = protocol_id
        self.core_handle = core_handle
        self.profile_id = core_handle.profile_id

    def __reduce_ex__(self, _protocol: int) -> object:
        raise TypeError("an admitted Protocol handle is process-local")


def _record(*fields: object) -> object:
    return k1.DatumRecord(tuple((index, value) for index, value in enumerate(fields)))


def _seq(values: tuple[object, ...]) -> object:
    return k1.DatumSeq(values)


def _variant(tag: int, payload: object = k1.UNIT) -> object:
    return k1.DatumVariant(tag, payload)


def module_declaration_ref_datum(reference: ModuleDeclarationRef) -> object:
    return _variant(
        1,
        _record(
            k1.BytesValue(reference.module.internal_reference()),
            k1.Symbol(reference.declaration_kind),
            k1.Nat(reference.local_ordinal),
        ),
    )


def value_ref_datum(reference: ValueRef) -> object:
    if type(reference) is PublicInputRef:
        return _variant(0, k1.Nat(reference.ordinal))
    if type(reference) is VerifierPrivateInputRef:
        return _variant(1, k1.Nat(reference.ordinal))
    if type(reference) is ConstantRef:
        return _variant(2, k1.Nat(reference.ordinal))
    if type(reference) is DerivedValueRef:
        return _variant(3, k1.Nat(reference.ordinal))
    if type(reference) is OccurrenceOutputRef:
        return _variant(
            4, _record(k1.Nat(reference.occurrence), k1.Nat(reference.output_ordinal))
        )
    raise k1.ModelError("unknown target ValueRef carrier")


def _input_datum(item: InputDecl) -> object:
    return _record(k1.value_type_datum(item.value_type))


def _constant_datum(item: TypedConstantDecl) -> object:
    admitted = k1.admit_value(item.value_type, item.value.datum)
    return _record(k1.value_type_datum(item.value_type), admitted.datum)


def _derived_datum(item: DerivedValueDecl) -> object:
    return _record(
        k1.BytesValue(item.algorithm.internal_reference()),
        k1.BytesValue(item.evaluation_contract.internal_reference()),
        _seq(tuple(value_ref_datum(value) for value in item.inputs)),
        k1.value_type_datum(item.result_type),
    )


def _scope_datum(item: ScopeDecl) -> object:
    parent = _variant(0) if item.parent is None else _variant(1, k1.Nat(item.parent))
    opening = _variant(0) if item.opening is None else _variant(1, k1.Nat(item.opening))
    return _record(parent, opening)


def _binding_datum(item: PublicBindingDecl) -> object:
    return _record(
        k1.Nat(item.scope),
        _variant(item.binding_class.value),
        value_ref_datum(item.value),
    )


def _challenge_datum(item: ChallengeDecl) -> object:
    if type(item.correlation) is IndependentCorrelation:
        correlation = _variant(0)
    elif type(item.correlation) is JointCorrelation:
        correlation = _variant(
            1,
            _record(
                module_declaration_ref_datum(item.correlation.group),
                k1.Nat(item.correlation.index),
                _seq(tuple(k1.Nat(value) for value in item.correlation.prior_members)),
            ),
        )
    else:
        raise k1.ModelError("unknown target coin-correlation carrier")
    if type(item.reduction_use) is ExclusiveReductionUse:
        reduction_use = _variant(0)
    elif type(item.reduction_use) is SharedReductionUse:
        reduction_use = _variant(
            1, module_declaration_ref_datum(item.reduction_use.contract)
        )
    else:
        raise k1.ModelError("unknown target reduction-use carrier")
    return _record(
        k1.Nat(item.scope),
        k1.value_type_datum(item.value_type),
        module_declaration_ref_datum(item.domain),
        module_declaration_ref_datum(item.fresh_law),
        correlation,
        reduction_use,
        _seq(tuple(value_ref_datum(value) for value in item.public_conditions)),
    )


def _check_datum(item: CheckDecl) -> object:
    return _record(
        k1.BytesValue(item.algorithm.internal_reference()),
        k1.BytesValue(item.evaluation_contract.internal_reference()),
        _seq(tuple(value_ref_datum(value) for value in item.inputs)),
    )


def _claim_datum(item: ClaimDecl) -> object:
    return _record(
        module_declaration_ref_datum(item.contract),
        k1.Nat(item.scope),
        _variant(item.usage.value),
        _variant(0, k1.Nat(item.source_binding)),
    )


def _terminal_datum(item: TerminalDecl) -> object:
    return _record(
        _variant(item.verdict.value),
        _seq(tuple(value_ref_datum(value) for value in item.public_outputs)),
        _seq(tuple(k1.Nat(value) for value in item.required_true_checks)),
        _seq(
            tuple(
                _record(k1.Nat(entry.claim), _variant(entry.disposition.value))
                for entry in item.claim_dispositions
            )
        ),
    )


def _guard_datum(guard: Guard) -> object:
    if type(guard) is AlwaysGuard:
        return _variant(0)
    if type(guard) is EvaluateGuard:
        return _variant(
            1,
            _record(
                k1.BytesValue(guard.algorithm.internal_reference()),
                k1.BytesValue(guard.evaluation_contract.internal_reference()),
                _seq(tuple(value_ref_datum(value) for value in guard.inputs)),
            ),
        )
    raise k1.ModelError("unknown target guard carrier")


def _effect_datum(effect: Effect) -> object:
    if type(effect) is ProverMessageEffect:
        return _variant(
            0,
            _record(
                module_declaration_ref_datum(effect.channel),
                k1.value_type_datum(effect.payload_type),
            ),
        )
    if type(effect) is ChallengeEffect:
        return _variant(2, k1.Nat(effect.challenge))
    if type(effect) is CheckEffect:
        return _variant(3, k1.Nat(effect.check))
    if type(effect) is TerminalEffect:
        return _variant(5, k1.Nat(effect.terminal))
    raise k1.ModelError("unknown or unsupported target effect carrier")


def _occurrence_datum(item: OccurrenceDecl) -> object:
    return _record(
        k1.Nat(item.scope), _guard_datum(item.guard), _effect_datum(item.effect)
    )


def core_domain_datum(core: InteractiveCore) -> object:
    """Compile all fourteen target fields, including empty family sequences."""

    if type(core) is not InteractiveCore:
        raise k1.ModelError("Core has the wrong exact target carrier")
    fields = (
        _seq(
            tuple(
                k1.BytesValue(item.internal_reference()) for item in core.used_modules
            )
        ),
        _seq(tuple(_input_datum(item) for item in core.public_inputs)),
        _seq(tuple(_input_datum(item) for item in core.verifier_private_inputs)),
        _seq(tuple(_constant_datum(item) for item in core.constants)),
        _seq(tuple(_derived_datum(item) for item in core.derived_values)),
        _seq(tuple(_scope_datum(item) for item in core.scopes)),
        _seq(tuple(_binding_datum(item) for item in core.public_bindings)),
        _seq(tuple(_challenge_datum(item) for item in core.challenges)),
        _seq(tuple(item for item in core.oracles)),
        _seq(tuple(_check_datum(item) for item in core.checks)),
        _seq(tuple(_claim_datum(item) for item in core.claims)),
        _seq(tuple(item for item in core.reductions)),
        _seq(tuple(_terminal_datum(item) for item in core.terminals)),
        _seq(tuple(_occurrence_datum(item) for item in core.occurrences)),
    )
    return _record(*fields)


def core_profiled_body(core: InteractiveCore, profile_id: object) -> bytes:
    return k1.encode_datum(
        k1.profiled_semantic_body(profile_id, core_domain_datum(core))
    )


def core_id(core: InteractiveCore, profile_id: object) -> object:
    return k1.profiled_content_id(
        TARGET_CORE_KIND,
        profile_id,
        core_domain_datum(core),
        semantic_regime=k1.SEMANTIC_REGIME_ID,
    )


def protocol_domain_datum(core_identifier: object) -> object:
    return _record(k1.BytesValue(core_identifier.internal_reference()), _variant(0))


def protocol_profiled_body(core_identifier: object, profile_id: object) -> bytes:
    return k1.encode_datum(
        k1.profiled_semantic_body(profile_id, protocol_domain_datum(core_identifier))
    )


def protocol_id(core_identifier: object, profile_id: object) -> object:
    return k1.profiled_content_id(
        TARGET_PROTOCOL_KIND,
        profile_id,
        protocol_domain_datum(core_identifier),
        semantic_regime=k1.SEMANTIC_REGIME_ID,
    )


def make_core_candidate(core: InteractiveCore, profile_id: object) -> CoreCandidate:
    return CoreCandidate(core_id(core, profile_id), core)


def make_protocol_candidate(
    core_identifier: object, profile_id: object
) -> FreshProtocolCandidate:
    return FreshProtocolCandidate(
        protocol_id(core_identifier, profile_id), core_identifier
    )


def _nominal_body(symbol: str) -> object:
    return _record(k1.Symbol(symbol))


def _catalog(kind: str, bodies: tuple[object, ...]) -> object:
    return _record(k1.Symbol(kind), _seq(bodies))


def protocol_module() -> object:
    catalogs = (
        _catalog("pir.challenge-domain", (_nominal_body("finite-additive-z3"),)),
        _catalog(
            "pir.challenge-sharing-contract",
            (_nominal_body("bounded-shared-challenge"),),
        ),
        _catalog("pir.claim-contract", (_nominal_body("bounded-schnorr-claim"),)),
        _catalog("pir.coin-correlation-group", (_nominal_body("bounded-joint-coins"),)),
        _catalog(
            "pir.message-channel",
            (_nominal_body("commitment"), _nominal_body("response")),
        ),
        _catalog("pir.public-coin-law", (_nominal_body("fresh-uniform-z3"),)),
    )
    return k1.SemanticModuleCandidate(
        k1.Symbol("f1r1b.target-finite-schnorr"), (), _seq(catalogs)
    )


Z3 = k1.ValueType(k1.NAT_DOMAIN, k1.NatSchema(2))


def _z3_literal(value: int) -> object:
    return k1.Literal(k1.admit_value(Z3, k1.Nat(value)))


def _bool_literal(value: bool) -> object:
    return k1.Literal(k1.admit_value(k1.BOOL, value))


def _switch3(selector: object, branches: tuple[object, object, object]) -> object:
    less_than_one = k1.PrimitiveCall(
        k1.PRIMITIVE_REFS_BY_KEY[("nat.lt", 1)], (selector, _z3_literal(1))
    )
    less_than_two = k1.PrimitiveCall(
        k1.PRIMITIVE_REFS_BY_KEY[("nat.lt", 1)], (selector, _z3_literal(2))
    )
    return k1.Conditional(
        less_than_one,
        branches[0],
        k1.Conditional(less_than_two, branches[1], branches[2]),
    )


def finite_schnorr_algorithm() -> object:
    variables = tuple(k1.Variable(index, Z3) for index in range(4))
    y, commitment, challenge, response = variables

    def response_test(y_value: int, a_value: int, c_value: int) -> object:
        expected = (a_value + c_value * y_value) % 3
        return _switch3(
            response,
            tuple(_bool_literal(value == expected) for value in range(3)),
        )

    term = _switch3(
        y,
        tuple(
            _switch3(
                commitment,
                tuple(
                    _switch3(
                        challenge,
                        tuple(
                            response_test(y_value, a_value, c_value)
                            for c_value in range(3)
                        ),
                    )
                    for a_value in range(3)
                ),
            )
            for y_value in range(3)
        ),
    )
    return k1.CanonicalAlgorithm(
        k1.Symbol("F1R1BFiniteZ3SchnorrVerify"), (Z3, Z3, Z3, Z3), term
    )


def boolean_identity_algorithm() -> object:
    return k1.CanonicalAlgorithm(
        k1.Symbol("F1R1BBooleanIdentity"),
        (k1.BOOL,),
        k1.Variable(0, k1.BOOL),
    )


@dataclass(frozen=True)
class Fixture:
    environment: Environment
    core_candidate: CoreCandidate
    protocol_candidate: FreshProtocolCandidate
    module: object
    schnorr_algorithm: object
    guard_algorithm: object


def make_fixture() -> Fixture:
    repository = publication.compile_repository()
    target = repository.profiles[TARGET_PROFILE_KEY]
    module = protocol_module()
    module_id = module.identity
    schnorr = finite_schnorr_algorithm()
    guard = boolean_identity_algorithm()
    contract = k1.DEFAULT_EVALUATION_CONTRACT

    channel_commitment = ModuleDeclarationRef(module_id, "pir.message-channel", 0)
    channel_response = ModuleDeclarationRef(module_id, "pir.message-channel", 1)
    challenge_domain = ModuleDeclarationRef(module_id, "pir.challenge-domain", 0)
    fresh_law = ModuleDeclarationRef(module_id, "pir.public-coin-law", 0)

    checks = (
        CheckDecl(
            schnorr.identity,
            contract.identity,
            (
                PublicInputRef(0),
                OccurrenceOutputRef(0, 0),
                OccurrenceOutputRef(1, 0),
                OccurrenceOutputRef(2, 0),
            ),
        ),
    )
    terminals = (
        TerminalDecl(TerminalVerdict.ACCEPT, (), (0,), ()),
        TerminalDecl(TerminalVerdict.REJECT, (), (), ()),
    )
    occurrences = (
        OccurrenceDecl(0, AlwaysGuard(), ProverMessageEffect(channel_commitment, Z3)),
        OccurrenceDecl(0, AlwaysGuard(), ChallengeEffect(0)),
        OccurrenceDecl(0, AlwaysGuard(), ProverMessageEffect(channel_response, Z3)),
        OccurrenceDecl(0, AlwaysGuard(), CheckEffect(0)),
        OccurrenceDecl(
            0,
            EvaluateGuard(
                guard.identity,
                contract.identity,
                (OccurrenceOutputRef(3, 0),),
            ),
            TerminalEffect(0),
        ),
        OccurrenceDecl(0, AlwaysGuard(), TerminalEffect(1)),
    )
    core = InteractiveCore(
        used_modules=(module_id,),
        public_inputs=(InputDecl(Z3),),
        verifier_private_inputs=(),
        constants=(),
        derived_values=(),
        scopes=(ScopeDecl(None, None),),
        public_bindings=(
            PublicBindingDecl(0, BindingClass.STATEMENT, PublicInputRef(0)),
        ),
        challenges=(
            ChallengeDecl(
                0,
                Z3,
                challenge_domain,
                fresh_law,
                IndependentCorrelation(),
                ExclusiveReductionUse(),
                (),
            ),
        ),
        oracles=(),
        checks=checks,
        claims=(),
        reductions=(),
        terminals=terminals,
        occurrences=occurrences,
    )
    algorithms = {schnorr.identity: schnorr, guard.identity: guard}
    algorithm_modules = {
        schnorr.identity: k1.FIXTURE_MODULE_PREIMAGES,
        guard.identity: MappingProxyType({}),
    }
    environment = Environment(
        target.profile_id,
        MappingProxyType({target.profile_id: target.profile}),
        MappingProxyType({module_id: module}),
        MappingProxyType(algorithms),
        MappingProxyType(algorithm_modules),
        MappingProxyType({contract.identity: contract}),
    )
    candidate = make_core_candidate(core, target.profile_id)
    return Fixture(
        environment,
        candidate,
        make_protocol_candidate(candidate.asserted_id, target.profile_id),
        module,
        schnorr,
        guard,
    )


def environment_for_core(base: Environment, core: InteractiveCore) -> Environment:
    """Restrict algorithm/contract bundles to the exact candidate references."""

    algorithms, contracts = _ordinary_references(core)
    return replace(
        base,
        algorithm_preimages=MappingProxyType(
            {item: base.algorithm_preimages[item] for item in algorithms}
        ),
        algorithm_modules=MappingProxyType(
            {item: base.algorithm_modules[item] for item in algorithms}
        ),
        contract_preimages=MappingProxyType(
            {item: base.contract_preimages[item] for item in contracts}
        ),
    )


def _fail(outcome: str, code: str, detail: str) -> None:
    raise AdmissionFailure(outcome, code, detail)


def _u64(value: object, label: str) -> int:
    if type(value) is not int or not 0 <= value < 1 << 64:
        _fail("Malformed", "F1R1B-M-U64", f"{label} is not a u64 natural")
    return value


def _bounded_tuple(value: object, label: str) -> tuple[object, ...]:
    if type(value) is not tuple:
        _fail("Malformed", "F1R1B-M-CARRIER", f"{label} is not an immutable tuple")
    if len(value) > MAX_LOCAL_ITEMS:
        _fail(
            "DeterministicLimitExceeded",
            "F1R1B-L-LOCAL-SEQUENCE",
            f"{label} crosses the target local bound",
        )
    return value


def _ordinary_references(
    core: InteractiveCore,
) -> tuple[tuple[object, ...], tuple[object, ...]]:
    algorithms: set[object] = set()
    contracts: set[object] = set()
    for item in core.derived_values:
        algorithms.add(item.algorithm)
        contracts.add(item.evaluation_contract)
    for item in core.checks:
        algorithms.add(item.algorithm)
        contracts.add(item.evaluation_contract)
    for occurrence in core.occurrences:
        if type(occurrence.guard) is EvaluateGuard:
            algorithms.add(occurrence.guard.algorithm)
            contracts.add(occurrence.guard.evaluation_contract)

    def reference_key(item: object) -> bytes:
        return item.internal_reference()

    return tuple(sorted(algorithms, key=reference_key)), tuple(
        sorted(contracts, key=reference_key)
    )


def _module_references(core: InteractiveCore) -> tuple[ModuleDeclarationRef, ...]:
    result: list[ModuleDeclarationRef] = []
    for challenge in core.challenges:
        result.extend((challenge.domain, challenge.fresh_law))
        if type(challenge.correlation) is JointCorrelation:
            result.append(challenge.correlation.group)
        if type(challenge.reduction_use) is SharedReductionUse:
            result.append(challenge.reduction_use.contract)
    for claim in core.claims:
        result.append(claim.contract)
    for occurrence in core.occurrences:
        if type(occurrence.effect) is ProverMessageEffect:
            result.append(occurrence.effect.channel)
    return tuple(result)


def _authenticate_step_one(
    candidate: CoreCandidate, environment: Environment
) -> tuple[object, Mapping[object, object]]:
    if environment.profile_id != target_profile_id():
        _fail(
            "KindMismatch",
            "F1R1B-K-TARGET-PROFILE",
            "the evaluator accepts only the frozen target Interaction profile",
        )
    ledger = k1.AuthenticationLedger()
    try:
        k1.authenticate_prior_meta_basis(
            environment.prior_meta_preimages, ledger=ledger
        )
        k1.effective_semantic_context(
            environment.profile_id,
            dict(environment.profile_preimages),
            semantic_regime=k1.SEMANTIC_REGIME_ID,
            ledger=ledger,
        )
        if type(candidate.asserted_id) is not k1.TypedContentId:
            _fail("Malformed", "F1R1B-M-CORE-ID", "Core ID has the wrong carrier")
        if candidate.asserted_id.subject_kind != TARGET_CORE_KIND:
            _fail("KindMismatch", "F1R1B-K-CORE-ID", "Core ID has the wrong kind")
        body = core_profiled_body(candidate.core, environment.profile_id)
        k1.authenticate_content_id(
            candidate.asserted_id,
            body,
            environment.prior_meta_preimages,
            ledger=ledger,
        )
        k1.authenticate_module_closure(
            candidate.core.used_modules,
            dict(environment.module_preimages),
            semantic_regime=k1.SEMANTIC_REGIME_ID,
            ledger=ledger,
        )
    except AdmissionFailure:
        raise
    except Exception as error:
        outcome = getattr(getattr(error, "outcome", None), "value", None)
        code = getattr(error, "code", "")
        if outcome == "MissingDependency" and code == "K1-MISSING-MODULE":
            _fail(
                "MissingDependency",
                "F1R1B-D-MODULE-PREIMAGE",
                "an asserted direct owner module has no authenticated preimage",
            )
        if "does not authenticate" in str(error):
            _fail(
                "Refused",
                "F1R1B-R-CORE-ID",
                "the asserted Core ID does not authenticate the exact target body",
            )
        _fail(outcome or "Malformed", code or "F1R1B-M-AUTH", str(error))

    algorithm_ids, contract_ids = _ordinary_references(candidate.core)
    function_types: dict[object, object] = {}
    for identifier in algorithm_ids:
        algorithm = environment.algorithm_preimages.get(identifier)
        if algorithm is None:
            _fail(
                "MissingDependency",
                "F1R1B-D-ALGORITHM-PREIMAGE",
                "a referenced portable algorithm preimage is missing",
            )
        modules = environment.algorithm_modules.get(identifier)
        if modules is None:
            _fail(
                "MissingDependency",
                "F1R1B-D-ALGORITHM-MODULES",
                "an algorithm module bundle is missing",
            )
        try:
            authenticated = k1.authenticate_algorithm_identity(algorithm, ledger=ledger)
            if authenticated != identifier:
                _fail(
                    "Refused",
                    "F1R1B-R-ALGORITHM-ID",
                    "algorithm preimage disagrees with its referenced ID",
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
        except AdmissionFailure:
            raise
        except Exception as error:
            outcome = getattr(getattr(error, "outcome", None), "value", None)
            _fail(
                outcome or "Refused",
                getattr(error, "code", "F1R1B-R-ALGORITHM"),
                str(error),
            )

    for identifier in contract_ids:
        contract = environment.contract_preimages.get(identifier)
        if contract is None:
            _fail(
                "MissingDependency",
                "F1R1B-D-CONTRACT-PREIMAGE",
                "a referenced evaluation contract preimage is missing",
            )
        try:
            if contract.identity != identifier:
                _fail(
                    "Refused",
                    "F1R1B-R-CONTRACT-ID",
                    "evaluation contract preimage disagrees with its reference",
                )
            k1.authenticate_content_id(
                identifier,
                contract.body(),
                environment.prior_meta_preimages,
                ledger=ledger,
            )
        except AdmissionFailure:
            raise
        except Exception as error:
            _fail("Malformed", "F1R1B-M-CONTRACT", str(error))
    return ledger, MappingProxyType(function_types)


def _validate_step_two(core: InteractiveCore) -> None:
    if type(core) is not InteractiveCore:
        _fail("Malformed", "F1R1B-M-CARRIER", "Core has the wrong exact carrier")
    fields = (
        (core.used_modules, "used modules"),
        (core.public_inputs, "public inputs"),
        (core.verifier_private_inputs, "verifier-private inputs"),
        (core.constants, "constants"),
        (core.derived_values, "derived values"),
        (core.scopes, "scopes"),
        (core.public_bindings, "public bindings"),
        (core.challenges, "challenges"),
        (core.oracles, "oracles"),
        (core.checks, "checks"),
        (core.claims, "claims"),
        (core.reductions, "reductions"),
        (core.terminals, "terminals"),
        (core.occurrences, "occurrences"),
    )
    for value, label in fields:
        _bounded_tuple(value, label)
    if core.constants or core.derived_values or core.oracles or core.reductions:
        _fail(
            "Unsupported",
            "F1R1B-U-OUTSIDE-SLICE",
            "the bounded evaluator does not implement this exact target family",
        )
    module_keys = tuple(item.internal_reference() for item in core.used_modules)
    if module_keys != tuple(sorted(set(module_keys))):
        _fail(
            "Malformed",
            "F1R1B-M-USED-MODULE-ORDER",
            "used modules are not ContentRef-sorted-unique",
        )
    exact_types = (
        (core.public_inputs, InputDecl),
        (core.verifier_private_inputs, InputDecl),
        (core.scopes, ScopeDecl),
        (core.public_bindings, PublicBindingDecl),
        (core.challenges, ChallengeDecl),
        (core.checks, CheckDecl),
        (core.claims, ClaimDecl),
        (core.terminals, TerminalDecl),
        (core.occurrences, OccurrenceDecl),
    )
    if any(
        type(item) is not expected
        for values, expected in exact_types
        for item in values
    ):
        _fail(
            "Malformed",
            "F1R1B-M-CARRIER",
            "a target sequence has a wrong element carrier",
        )
    if not core.scopes or not core.occurrences or not core.terminals:
        _fail(
            "Refused",
            "F1R1B-R-NONEMPTY",
            "scope, occurrence, and terminal families must be nonempty",
        )

    def check_ref(value: ValueRef) -> None:
        if type(value) is PublicInputRef:
            bound = len(core.public_inputs)
            ordinal = value.ordinal
        elif type(value) is VerifierPrivateInputRef:
            bound = len(core.verifier_private_inputs)
            ordinal = value.ordinal
        elif type(value) is ConstantRef:
            bound = len(core.constants)
            ordinal = value.ordinal
        elif type(value) is DerivedValueRef:
            bound = len(core.derived_values)
            ordinal = value.ordinal
        elif type(value) is OccurrenceOutputRef:
            _u64(value.occurrence, "occurrence reference")
            _u64(value.output_ordinal, "occurrence output ordinal")
            if value.occurrence >= len(core.occurrences):
                _fail(
                    "Refused",
                    "F1R1B-R-REFERENCE-BOUND",
                    "occurrence reference is out of range",
                )
            return
        else:
            _fail("Malformed", "F1R1B-M-VALUE-REF", "unknown ValueRef branch")
        _u64(ordinal, "value reference")
        if ordinal >= bound:
            _fail(
                "Refused", "F1R1B-R-REFERENCE-BOUND", "value reference is out of range"
            )

    for binding in core.public_bindings:
        _u64(binding.scope, "binding scope")
        check_ref(binding.value)
        if type(binding.binding_class) is not BindingClass:
            _fail("Malformed", "F1R1B-M-BINDING-CLASS", "unknown binding class")
    for challenge in core.challenges:
        _u64(challenge.scope, "challenge scope")
        _bounded_tuple(challenge.public_conditions, "challenge conditions")
        for value in challenge.public_conditions:
            check_ref(value)
    for check in core.checks:
        _bounded_tuple(check.inputs, "check inputs")
        for value in check.inputs:
            check_ref(value)
    for claim in core.claims:
        _u64(claim.scope, "claim scope")
        _u64(claim.source_binding, "claim source binding")
        if type(claim.usage) is not ClaimUsage:
            _fail("Malformed", "F1R1B-M-CLAIM-USAGE", "unknown claim usage")
    for terminal in core.terminals:
        if type(terminal.verdict) is not TerminalVerdict:
            _fail("Malformed", "F1R1B-M-TERMINAL-VERDICT", "unknown verdict")
        for value in terminal.public_outputs:
            check_ref(value)
        for check in terminal.required_true_checks:
            _u64(check, "required check")
            if check >= len(core.checks):
                _fail(
                    "Refused",
                    "F1R1B-R-REFERENCE-BOUND",
                    "required check is out of range",
                )
        for entry in terminal.claim_dispositions:
            if type(entry) is not ClaimDispositionEntry:
                _fail(
                    "Malformed",
                    "F1R1B-M-CLAIM-DISPOSITION",
                    "wrong claim-disposition carrier",
                )
            _u64(entry.claim, "claim disposition")
            if entry.claim >= len(core.claims):
                _fail(
                    "Refused",
                    "F1R1B-R-REFERENCE-BOUND",
                    "claim disposition is out of range",
                )
    for occurrence in core.occurrences:
        _u64(occurrence.scope, "occurrence scope")
        if type(occurrence.guard) is EvaluateGuard:
            for value in occurrence.guard.inputs:
                check_ref(value)
        elif type(occurrence.guard) is not AlwaysGuard:
            _fail("Malformed", "F1R1B-M-GUARD", "unknown guard carrier")
        effect = occurrence.effect
        if type(effect) is ChallengeEffect:
            if (
                not 0
                <= _u64(effect.challenge, "challenge backlink")
                < len(core.challenges)
            ):
                _fail(
                    "Refused",
                    "F1R1B-R-REFERENCE-BOUND",
                    "challenge backlink is out of range",
                )
        elif type(effect) is CheckEffect:
            if not 0 <= _u64(effect.check, "check backlink") < len(core.checks):
                _fail(
                    "Refused",
                    "F1R1B-R-REFERENCE-BOUND",
                    "check backlink is out of range",
                )
        elif type(effect) is TerminalEffect:
            if (
                not 0
                <= _u64(effect.terminal, "terminal backlink")
                < len(core.terminals)
            ):
                _fail(
                    "Refused",
                    "F1R1B-R-REFERENCE-BOUND",
                    "terminal backlink is out of range",
                )
        elif type(effect) is not ProverMessageEffect:
            _fail(
                "Unsupported",
                "F1R1B-U-EFFECT",
                "effect constructor is outside the bounded evaluator",
            )


def _validate_nominal(
    reference: ModuleDeclarationRef, expected_kind: str, environment: Environment
) -> None:
    if type(reference) is not ModuleDeclarationRef:
        _fail(
            "Malformed",
            "F1R1B-M-MODULE-REF",
            "module declaration reference has the wrong carrier",
        )
    if reference.declaration_kind != expected_kind:
        _fail(
            "KindMismatch",
            "F1R1B-K-DECLARATION",
            f"expected declaration kind {expected_kind}",
        )
    candidate = environment.module_preimages.get(reference.module)
    if candidate is None:
        _fail(
            "MissingDependency",
            "F1R1B-D-MODULE-PREIMAGE",
            "declaration owner is missing",
        )
    try:
        body = k1.resolve_module_declaration(
            candidate, reference.declaration_kind, reference.local_ordinal
        )
    except Exception as error:
        _fail("Refused", "F1R1B-R-DECLARATION-COORDINATE", str(error))
    if (
        type(body) is not k1.DatumRecord
        or tuple(index for index, _ in body.fields) != (0,)
        or type(body.fields[0][1]) is not k1.Symbol
    ):
        _fail(
            "Refused",
            "F1R1B-R-NOMINAL-BODY",
            "nominal declaration has the wrong exact body",
        )


def _validate_step_three(core: InteractiveCore, environment: Environment) -> None:
    references = _module_references(core)
    direct = tuple(
        sorted(
            {item.module for item in references},
            key=lambda item: item.internal_reference(),
        )
    )
    if core.used_modules != direct:
        _fail(
            "Refused",
            "F1R1B-R-EXACT-USED-MODULES",
            "the asserted used-module set differs from DirectOwnerModules",
        )
    for challenge in core.challenges:
        _validate_nominal(challenge.domain, "pir.challenge-domain", environment)
        _validate_nominal(challenge.fresh_law, "pir.public-coin-law", environment)
        if type(challenge.correlation) is JointCorrelation:
            _validate_nominal(
                challenge.correlation.group, "pir.coin-correlation-group", environment
            )
        if type(challenge.reduction_use) is SharedReductionUse:
            _validate_nominal(
                challenge.reduction_use.contract,
                "pir.challenge-sharing-contract",
                environment,
            )
    for claim in core.claims:
        _validate_nominal(claim.contract, "pir.claim-contract", environment)
    for occurrence in core.occurrences:
        if type(occurrence.effect) is ProverMessageEffect:
            _validate_nominal(
                occurrence.effect.channel, "pir.message-channel", environment
            )
    algorithms, contracts = _ordinary_references(core)
    environment_algorithms = tuple(
        sorted(
            environment.algorithm_preimages,
            key=lambda item: item.internal_reference(),
        )
    )
    if environment_algorithms != algorithms:
        _fail(
            "Refused",
            "F1R1B-R-EXACT-ALGORITHMS",
            "algorithm preimages are missing or extra",
        )
    environment_contracts = tuple(
        sorted(
            environment.contract_preimages,
            key=lambda item: item.internal_reference(),
        )
    )
    if environment_contracts != contracts:
        _fail(
            "Refused",
            "F1R1B-R-EXACT-CONTRACTS",
            "contract preimages are missing or extra",
        )
    if any(item != k1.DEFAULT_EVALUATION_CONTRACT.identity for item in contracts):
        _fail(
            "Unsupported",
            "F1R1B-U-EVALUATION-CONTRACT",
            "the bounded evaluator lacks this contract",
        )


def _output_types(core: InteractiveCore) -> tuple[tuple[object, ...], ...]:
    result: list[tuple[object, ...]] = []
    for occurrence in core.occurrences:
        effect = occurrence.effect
        if type(effect) is ProverMessageEffect:
            result.append((effect.payload_type,))
        elif type(effect) is ChallengeEffect:
            result.append((core.challenges[effect.challenge].value_type,))
        elif type(effect) is CheckEffect:
            result.append((k1.BOOL,))
        else:
            result.append(())
    return tuple(result)


def _value_type(
    core: InteractiveCore, outputs: tuple[tuple[object, ...], ...], reference: ValueRef
) -> object:
    if type(reference) is PublicInputRef:
        return core.public_inputs[reference.ordinal].value_type
    if type(reference) is VerifierPrivateInputRef:
        return core.verifier_private_inputs[reference.ordinal].value_type
    if type(reference) is OccurrenceOutputRef:
        values = outputs[reference.occurrence]
        if reference.output_ordinal >= len(values):
            _fail("Refused", "F1R1B-R-OUTPUT-ORDINAL", "occurrence has no named output")
        return values[reference.output_ordinal]
    _fail(
        "Unsupported",
        "F1R1B-U-VALUE-FAMILY",
        "value reference is outside the bounded evaluator",
    )


def _check_abi(
    algorithm: object,
    inputs: tuple[ValueRef, ...],
    core: InteractiveCore,
    outputs: tuple[tuple[object, ...], ...],
    function_types: Mapping[object, object],
    label: str,
) -> None:
    abi = function_types[algorithm]
    observed = tuple(_value_type(core, outputs, value) for value in inputs)
    if observed != abi.inputs or abi.output != k1.BOOL or abi.failures:
        _fail(
            "KindMismatch",
            "F1R1B-K-ALGORITHM-ABI",
            f"{label} algorithm ABI is not exact total Boolean",
        )


def _validate_step_four(
    core: InteractiveCore,
    environment: Environment,
    function_types: Mapping[object, object],
) -> tuple[tuple[object, ...], ...]:
    types: list[object] = []
    types.extend(item.value_type for item in core.public_inputs)
    types.extend(item.value_type for item in core.verifier_private_inputs)
    types.extend(item.value_type for item in core.challenges)
    types.extend(
        occurrence.effect.payload_type
        for occurrence in core.occurrences
        if type(occurrence.effect) is ProverMessageEffect
    )
    try:
        for value_type in types:
            if type(value_type) is not k1.ValueType:
                _fail(
                    "Malformed",
                    "F1R1B-M-VALUE-TYPE",
                    "value type has the wrong carrier",
                )
            value_type.__post_init__()
            k1.authenticate_value_type_reference(
                value_type,
                dict(environment.module_preimages),
                semantic_regime=k1.SEMANTIC_REGIME_ID,
            )
    except AdmissionFailure:
        raise
    except Exception as error:
        _fail("KindMismatch", "F1R1B-K-VALUE-TYPE", str(error))
    outputs = _output_types(core)
    for check in core.checks:
        _check_abi(
            check.algorithm, check.inputs, core, outputs, function_types, "check"
        )
    for occurrence in core.occurrences:
        if type(occurrence.guard) is EvaluateGuard:
            _check_abi(
                occurrence.guard.algorithm,
                occurrence.guard.inputs,
                core,
                outputs,
                function_types,
                "guard",
            )
    for terminal in core.terminals:
        for output in terminal.public_outputs:
            _value_type(core, outputs, output)
    return outputs


def _validate_step_five(
    core: InteractiveCore, outputs: tuple[tuple[object, ...], ...]
) -> None:
    if core.scopes[0] != ScopeDecl(None, None):
        _fail(
            "Refused", "F1R1B-R-ROOT-SCOPE", "scope zero is not the unique initial root"
        )
    opening_positions: list[int] = [-1]
    depths: list[int] = [0]
    for ordinal, scope in enumerate(core.scopes[1:], start=1):
        if scope.parent is None or not 0 <= scope.parent < ordinal:
            _fail(
                "Refused",
                "F1R1B-R-SCOPE-PARENT",
                "scope parent does not precede its child",
            )
        if scope.opening is None or not 0 <= scope.opening < len(core.occurrences):
            _fail(
                "Refused",
                "F1R1B-R-SCOPE-OPENING",
                "nested scope has no valid opening boundary",
            )
        depth = depths[scope.parent] + 1
        if depth > 384:
            _fail(
                "DeterministicLimitExceeded",
                "F1R1B-L-SCOPE-DEPTH",
                "scope depth exceeds 384",
            )
        if scope.opening < opening_positions[scope.parent]:
            _fail("Refused", "F1R1B-R-SCOPE-OPENING", "scope opens before its parent")
        opening_positions.append(scope.opening)
        depths.append(depth)
    for scope_ref in range(1, len(core.scopes)):
        members = [
            index
            for index, item in enumerate(core.occurrences)
            if item.scope == scope_ref
        ]
        if not members or opening_positions[scope_ref] > members[0]:
            _fail(
                "Refused",
                "F1R1B-R-SCOPE-OPENING",
                "scope does not open by its first occurrence",
            )
    for index, occurrence in enumerate(core.occurrences):
        if occurrence.scope >= len(core.scopes):
            _fail(
                "Refused", "F1R1B-R-SCOPE-REFERENCE", "occurrence names an absent scope"
            )
        if opening_positions[occurrence.scope] > index:
            _fail(
                "Refused",
                "F1R1B-R-SCOPE-MEMBERSHIP",
                "occurrence precedes its scope opening",
            )

    triples: set[tuple[object, ...]] = set()
    bound_public: set[int] = set()
    for binding in core.public_bindings:
        if binding.scope >= len(core.scopes):
            _fail("Refused", "F1R1B-R-SCOPE-REFERENCE", "binding names an absent scope")
        if type(binding.value) is VerifierPrivateInputRef:
            _fail(
                "Refused",
                "F1R1B-R-PRIVATE-BINDING",
                "private input cannot be publicly bound",
            )
        if type(binding.value) is PublicInputRef:
            bound_public.add(binding.value.ordinal)
        if type(binding.value) is OccurrenceOutputRef:
            producer = binding.value.occurrence
            if (
                producer >= opening_positions[binding.scope]
                or type(core.occurrences[producer].guard) is not AlwaysGuard
            ):
                _fail(
                    "Refused",
                    "F1R1B-R-SCOPE-BINDING-AVAILABILITY",
                    "a scope binding is not unconditionally available before opening",
                )
        triple = (binding.scope, binding.binding_class, binding.value)
        if triple in triples:
            _fail("Refused", "F1R1B-R-DUPLICATE-BINDING", "duplicate binding triple")
        triples.add(triple)
    if bound_public != set(range(len(core.public_inputs))):
        _fail(
            "Refused",
            "F1R1B-R-BINDING-COMPLETENESS",
            "public-input binding coverage is not total",
        )

    available: set[ValueRef] = {
        *(PublicInputRef(index) for index in range(len(core.public_inputs))),
        *(
            VerifierPrivateInputRef(index)
            for index in range(len(core.verifier_private_inputs))
        ),
    }
    for index, occurrence in enumerate(core.occurrences):
        reads: tuple[ValueRef, ...] = ()
        if type(occurrence.guard) is EvaluateGuard:
            reads += occurrence.guard.inputs
        effect = occurrence.effect
        if type(effect) is ChallengeEffect:
            reads += core.challenges[effect.challenge].public_conditions
        elif type(effect) is CheckEffect:
            reads += core.checks[effect.check].inputs
        elif type(effect) is TerminalEffect:
            reads += core.terminals[effect.terminal].public_outputs
        if any(value not in available for value in reads):
            _fail(
                "Refused",
                "F1R1B-R-VALUE-AVAILABILITY",
                "an occurrence reads outside its exact prior prefix",
            )
        available.update(
            OccurrenceOutputRef(index, output) for output in range(len(outputs[index]))
        )


def _validate_step_six(
    core: InteractiveCore,
) -> tuple[dict[int, int], dict[int, int], dict[int, int]]:
    challenge_positions: dict[int, list[int]] = {
        index: [] for index in range(len(core.challenges))
    }
    check_positions: dict[int, list[int]] = {
        index: [] for index in range(len(core.checks))
    }
    terminal_positions: dict[int, list[int]] = {
        index: [] for index in range(len(core.terminals))
    }
    for position, occurrence in enumerate(core.occurrences):
        effect = occurrence.effect
        if type(effect) is ChallengeEffect:
            challenge_positions[effect.challenge].append(position)
        elif type(effect) is CheckEffect:
            check_positions[effect.check].append(position)
        elif type(effect) is TerminalEffect:
            terminal_positions[effect.terminal].append(position)
    families = (
        (challenge_positions, "challenge"),
        (check_positions, "check"),
        (terminal_positions, "terminal"),
    )
    for positions, label in families:
        if any(len(value) != 1 for value in positions.values()):
            _fail(
                "Refused",
                "F1R1B-R-BACKLINK",
                f"{label} occurrence backlink is not one-to-one",
            )
    return (
        {key: value[0] for key, value in challenge_positions.items()},
        {key: value[0] for key, value in check_positions.items()},
        {key: value[0] for key, value in terminal_positions.items()},
    )


def _validate_step_seven(core: InteractiveCore) -> None:
    def static_public(reference: ValueRef) -> bool:
        # Constants and total static derived values are outside this bounded
        # positive slice.  No occurrence output is a static Challenge
        # condition; public-history correlation uses JointMember instead.
        return type(reference) is PublicInputRef

    for challenge in core.challenges:
        if any(not static_public(value) for value in challenge.public_conditions):
            _fail(
                "Refused",
                "F1R1B-R-CHALLENGE-CONDITION-PUBLIC",
                "challenge conditions are not all static-public values",
            )


def _validate_step_eight(
    core: InteractiveCore, challenge_positions: Mapping[int, int]
) -> None:
    del challenge_positions
    for challenge in core.challenges:
        if type(challenge.correlation) is JointCorrelation:
            _fail(
                "Unsupported",
                "F1R1B-U-JOINT-COINS",
                "joint-coin closure is outside the bounded evaluator",
            )
        if type(challenge.correlation) is not IndependentCorrelation:
            _fail("Malformed", "F1R1B-M-CORRELATION", "unknown coin-correlation branch")
        if type(challenge.reduction_use) is SharedReductionUse:
            _fail(
                "Refused",
                "F1R1B-R-SHARED-CONSUMERS",
                "Shared requires at least two exact reduction-role consumers",
            )
        if type(challenge.reduction_use) is not ExclusiveReductionUse:
            _fail("Malformed", "F1R1B-M-REDUCTION-USE", "unknown reduction-use branch")


def _validate_step_nine(
    core: InteractiveCore,
    check_positions: Mapping[int, int],
    terminal_positions: Mapping[int, int],
) -> None:
    for claim in core.claims:
        if claim.scope >= len(core.scopes) or claim.source_binding >= len(
            core.public_bindings
        ):
            _fail("Refused", "F1R1B-R-CLAIM-SOURCE", "initial claim source is absent")
        binding = core.public_bindings[claim.source_binding]
        if binding.binding_class is not BindingClass.STATEMENT:
            _fail(
                "Refused",
                "F1R1B-R-CLAIM-SOURCE",
                "initial claim does not cite a Statement binding",
            )
        if binding.scope != claim.scope:
            _fail(
                "Unsupported",
                "F1R1B-U-ANCESTOR-CLAIM",
                "ancestor claim sourcing is outside the bounded evaluator",
            )
    expected_claims = set(range(len(core.claims)))
    for terminal_ref, terminal in enumerate(core.terminals):
        position = terminal_positions[terminal_ref]
        if any(
            check_positions[item] >= position for item in terminal.required_true_checks
        ):
            _fail(
                "Refused",
                "F1R1B-R-TERMINAL-CHECK-ORDER",
                "terminal requires a check that has not occurred",
            )
        disposition_refs = tuple(item.claim for item in terminal.claim_dispositions)
        if len(set(disposition_refs)) != len(disposition_refs):
            _fail(
                "Refused",
                "F1R1B-R-CLAIM-LINEARITY",
                "terminal repeats a claim disposition",
            )
        if set(disposition_refs) != expected_claims:
            _fail(
                "Refused",
                "F1R1B-R-TERMINAL-CLAIM-CLOSURE",
                "a terminal path leaves an initial claim unresolved",
            )


def _validate_step_ten(core: InteractiveCore) -> None:
    final = core.occurrences[-1]
    if type(final.guard) is not AlwaysGuard or type(final.effect) is not TerminalEffect:
        _fail(
            "Refused",
            "F1R1B-R-FINAL-FALLBACK",
            "the final occurrence is not an unconditional terminal fallback",
        )


def admit_core(candidate: CoreCandidate, environment: Environment) -> AdmissionResult:
    try:
        if type(candidate) is not CoreCandidate or type(environment) is not Environment:
            _fail(
                "Malformed",
                "F1R1B-M-REQUEST",
                "admission request has the wrong carrier",
            )
        _ledger, function_types = _authenticate_step_one(candidate, environment)
        _validate_step_two(candidate.core)
        _validate_step_three(candidate.core, environment)
        outputs = _validate_step_four(candidate.core, environment, function_types)
        _validate_step_five(candidate.core, outputs)
        challenge_positions, check_positions, terminal_positions = _validate_step_six(
            candidate.core
        )
        _validate_step_seven(candidate.core)
        _validate_step_eight(candidate.core, challenge_positions)
        _validate_step_nine(candidate.core, check_positions, terminal_positions)
        _validate_step_ten(candidate.core)
        handle = AdmittedCore(
            candidate.asserted_id,
            candidate.core,
            environment.profile_id,
            environment,
            _CORE_ISSUER,
        )
        return AdmissionResult(
            "Affirmative",
            "F1R1B-A-CORE-ADMITTED",
            "all ten applicable target admission stages completed",
            handle,
        )
    except AdmissionFailure as error:
        return AdmissionResult(error.outcome, error.code, error.detail)
    except Exception as error:  # pragma: no cover - fail-closed checker defect
        return AdmissionResult("CheckerFailure", "F1R1B-CHECKER", str(error))


def admit_fresh_protocol(
    core_handle: object,
    candidate: FreshProtocolCandidate,
    environment: Environment,
) -> AdmissionResult:
    try:
        if (
            type(core_handle) is not AdmittedCore
            or core_handle._issuer is not _CORE_ISSUER
        ):
            _fail(
                "Refused",
                "F1R1B-R-CORE-AUTHORITY",
                "Fresh formation requires this evaluator's live admitted Core",
            )
        if (
            core_handle.profile_id != environment.profile_id
            or environment.profile_id != target_profile_id()
        ):
            _fail(
                "KindMismatch",
                "F1R1B-K-TARGET-PROFILE",
                "Fresh Core and target profile differ",
            )
        if core_handle.environment is not environment:
            _fail(
                "Refused",
                "F1R1B-R-EVALUATOR-AUTHORITY",
                "Fresh formation requires the identical retained admission environment",
            )
        if type(candidate) is not FreshProtocolCandidate:
            _fail(
                "Malformed",
                "F1R1B-M-PROTOCOL",
                "Fresh Protocol candidate has the wrong carrier",
            )
        if candidate.core_id != core_handle.core_id:
            _fail(
                "Refused",
                "F1R1B-R-PROTOCOL-CORE",
                "Fresh Protocol cites a different or unadmitted Core",
            )
        ledger = k1.AuthenticationLedger()
        k1.authenticate_prior_meta_basis(
            environment.prior_meta_preimages, ledger=ledger
        )
        k1.effective_semantic_context(
            environment.profile_id,
            dict(environment.profile_preimages),
            semantic_regime=k1.SEMANTIC_REGIME_ID,
            ledger=ledger,
        )
        if candidate.asserted_id.subject_kind != TARGET_PROTOCOL_KIND:
            _fail(
                "KindMismatch", "F1R1B-K-PROTOCOL-ID", "Protocol ID has the wrong kind"
            )
        k1.authenticate_content_id(
            candidate.asserted_id,
            protocol_profiled_body(candidate.core_id, environment.profile_id),
            environment.prior_meta_preimages,
            ledger=ledger,
        )
        handle = AdmittedFreshProtocol(
            candidate.asserted_id, core_handle, _PROTOCOL_ISSUER
        )
        return AdmissionResult(
            "Affirmative",
            "F1R1B-A-FRESH-ADMITTED",
            "Fresh Protocol formed from the exact live admitted target Core",
            handle,
        )
    except AdmissionFailure as error:
        return AdmissionResult(error.outcome, error.code, error.detail)
    except Exception as error:
        if "does not authenticate" in str(error):
            return AdmissionResult(
                "Refused",
                "F1R1B-R-PROTOCOL-ID",
                "Protocol ID does not authenticate its target body",
            )
        return AdmissionResult("CheckerFailure", "F1R1B-CHECKER", str(error))


_TARGET_PROFILE_ID: object | None = None


def target_profile_id() -> object:
    global _TARGET_PROFILE_ID
    if _TARGET_PROFILE_ID is None:
        _TARGET_PROFILE_ID = (
            publication.compile_repository().profiles[TARGET_PROFILE_KEY].profile_id
        )
    return _TARGET_PROFILE_ID
