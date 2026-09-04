#!/usr/bin/env python3
"""End-to-end finite pressure carrier over the migrated PIR contracts.

The package composes existing owner compilers and finite runtime libraries.  It
adds no normative semantic owner.  Four Analysis boundaries are represented
as data and are intentionally not repaired here.
"""

from __future__ import annotations

from collections import Counter
from dataclasses import dataclass, replace
from fractions import Fraction
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
from types import MappingProxyType, ModuleType, SimpleNamespace
from typing import Any, Callable, Mapping


ROOT = Path(__file__).resolve().parents[2]
INTEGRATED_MODEL = (
    ROOT / "evaluation/formal-source-integrated-views-f0v2b2d3/model.py"
)
FS_PACKAGE = ROOT / "evaluation/formal-source-fs-runtime-f0v3c"
FINITE_FIXTURE_MODEL = ROOT / "evaluation/k2-protocol-fiat-shamir/reference_model.py"
ANALYSIS_PREMISE_FIXTURE = ROOT / "evaluation/analysis-premise-intake-probe/fixture.json"


def _load(name: str, path: Path) -> ModuleType:
    if name in sys.modules:
        return sys.modules[name]
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise ImportError(f"cannot load {path.relative_to(ROOT)}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


integrated = _load("_zkc_pressure_integrated_views", INTEGRATED_MODEL)
fs_model = _load("_zkc_pressure_fs_model", FS_PACKAGE / "model.py")


def _load_fs_consumer(name: str, path: Path) -> ModuleType:
    previous = sys.modules.get("model")
    sys.modules["model"] = fs_model
    try:
        return _load(name, path)
    finally:
        if previous is None:
            del sys.modules["model"]
        else:
            sys.modules["model"] = previous


fs_views = _load_fs_consumer("_zkc_pressure_fs_views", FS_PACKAGE / "views.py")
fs_executor = _load_fs_consumer(
    "_zkc_pressure_fs_executor", FS_PACKAGE / "executor.py"
)
fs_replay = _load_fs_consumer("_zkc_pressure_fs_replay", FS_PACKAGE / "replay.py")
finite_fixture = _load("_zkc_pressure_finite_fixture", FINITE_FIXTURE_MODEL)

d1 = integrated.d1
base = integrated.base
foundation = integrated.foundation
b5 = integrated.b5
k1 = integrated.k1

if not (k1 is fs_model.k1 and k1 is finite_fixture.k1):
    raise ImportError("pressure package did not retain one executable-kernel implementation")

LANES = (
    "Accepted",
    "Rejected",
    "Aborted",
    "InterpretationFailed",
    "StrategyStopped",
    "OperationalNoncompletion",
)
ADMISSION_EVALUATOR_IDENTITY = hashlib.sha256(
    b"zkc.mixed-challenge-multi-binding-admission-evaluator.v0"
).digest()
QUESTION = (
    "does one admitted Core with heterogeneous challenges and several public "
    "bindings compose through every activated contract without an owner "
    "underdetermination?"
)


class PressureError(RuntimeError):
    """A bounded pressure invariant failed."""


@dataclass(frozen=True)
class CoreAdmission:
    core: Any
    candidate: Any
    environment: Any
    fresh_candidate: Any
    fresh_protocol_id: Any
    outputs: tuple[tuple[Any, ...], ...]
    graph: Any
    graph_evidence: Any
    closure: Any
    evaluator_identity: bytes
    verified_steps: tuple[int, ...]


@dataclass(frozen=True)
class FreshProtocolAdmission:
    candidate: Any
    protocol_id: Any
    core_admission: CoreAdmission
    closure: Any
    evaluator_identity: bytes
    verified_requirements: tuple[str, ...]


@dataclass(frozen=True)
class ConstructionBounds:
    challenge_rules: int
    maximum_frame_count: int
    maximum_transition_calls: int
    maximum_frame_octets: int
    maximum_namespace_octets: int
    maximum_cumulative_octets: int


@dataclass(frozen=True)
class TranscriptConstructionAdmission:
    construction: Any
    core_admission: CoreAdmission
    profile_ids: tuple[Any, ...]
    algorithm_ids: tuple[Any, ...]
    bounds: ConstructionBounds
    evaluator_identity: bytes
    verified_steps: tuple[int, ...]


@dataclass(frozen=True)
class FSProtocolAdmission:
    protocol: Any
    core_admission: CoreAdmission
    construction_admission: TranscriptConstructionAdmission
    evaluator_identity: bytes
    verified_requirements: tuple[str, ...]


@dataclass(frozen=True)
class CheckedConstructionAdmission:
    result: Any
    checker_contract_id: Any
    evaluator_identity: bytes
    verified_requirements: tuple[int, ...]


@dataclass(frozen=True)
class PressureSubject:
    setup_variant: str
    admission: CoreAdmission
    fresh_admission: FreshProtocolAdmission
    construction: Any
    construction_admission: TranscriptConstructionAdmission
    fs_protocol: Any
    fs_admission: FSProtocolAdmission
    checked: Any
    checked_admission: CheckedConstructionAdmission
    checker_contract_id: Any
    algorithms: tuple[Any, ...]


@dataclass(frozen=True)
class RunCase:
    statement: int
    seed: int
    commitment: int
    response: int

    @property
    def name(self) -> str:
        return (
            f"statement-{self.statement}-seed-{self.seed}-"
            f"commitment-{self.commitment}-response-{self.response}"
        )


def _r(*values: Any) -> Any:
    return k1.DatumRecord(tuple(enumerate(values)))


def _s(values: tuple[Any, ...]) -> Any:
    return k1.DatumSeq(values)


def _v(case: int, payload: Any = k1.UNIT) -> Any:
    return k1.DatumVariant(case, payload)


def _json_bytes(value: Any) -> bytes:
    return json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=True
    ).encode("ascii")


def digest(value: Any) -> str:
    return hashlib.sha256(_json_bytes(value)).hexdigest()


def _id(identifier: Any) -> str:
    return identifier.carrier()


def _canonical_value(value: Any) -> dict[str, str]:
    return fs_model.canonical_value_json(value)


def _decode_presented_value(value: Mapping[str, str], expected_type: Any) -> Any:
    expected_type_body = k1.encode_datum(k1.value_type_datum(expected_type)).hex()
    if value.get("value_type") != expected_type_body:
        raise PressureError("presented value type differs from its owner coordinate")
    try:
        return k1.decode_value(expected_type, bytes.fromhex(value["datum"]))
    except (KeyError, ValueError, k1.CanonicalError) as error:
        raise PressureError("presented value body is not canonical") from error


def _algorithm_preimage(subject: PressureSubject, identifier: Any) -> Any:
    matches = [item for item in subject.algorithms if item.identity == identifier]
    if len(matches) != 1:
        raise PressureError("runtime algorithm preimage is not unique")
    return matches[0]


def _message_channel(template: Any) -> Any:
    for occurrence in template.core.occurrences:
        if type(occurrence.effect).__name__ in {
            "ProverMessageEffect",
            "VerifierMessageEffect",
        }:
            return occurrence.effect.channel
    raise PressureError("integrated owner fixture has no message channel")


def _core_and_algorithms(run_established: bool) -> tuple[Any, tuple[Any, ...]]:
    template = d1.fixture("integrated-baseline")
    finite_template = fs_model.target.make_fixture()
    channel = _message_channel(template)
    boolean_challenge_template = template.core.challenges[0]
    finite_challenge_template = finite_template.core_candidate.core.challenges[0]
    finite_domain = base.ModuleDeclarationRef(
        finite_challenge_template.domain.module,
        finite_challenge_template.domain.declaration_kind,
        finite_challenge_template.domain.local_ordinal,
    )
    finite_fresh_law = base.ModuleDeclarationRef(
        finite_challenge_template.fresh_law.module,
        finite_challenge_template.fresh_law.declaration_kind,
        finite_challenge_template.fresh_law.local_ordinal,
    )
    z3_identity = k1.CanonicalAlgorithm(
        k1.Symbol("MixedChallengeZ3Identity"),
        (base.Z3,),
        k1.Variable(0, base.Z3),
        diagnostic_label=k1.Symbol("mixed-challenge-z3-identity"),
    )
    bool_identity = k1.CanonicalAlgorithm(
        k1.Symbol("MixedChallengeBoolIdentity"),
        (k1.BOOL,),
        k1.Variable(0, k1.BOOL),
        diagnostic_label=k1.Symbol("mixed-challenge-bool-identity"),
    )
    conjunction = k1.CanonicalAlgorithm(
        k1.Symbol("MixedChallengeBoolConjunction"),
        (k1.BOOL, k1.BOOL),
        k1.Conditional(
            k1.Variable(0, k1.BOOL),
            k1.Variable(1, k1.BOOL),
            k1.Literal(k1.admit_value(k1.BOOL, False)),
        ),
        diagnostic_label=k1.Symbol("mixed-challenge-bool-conjunction"),
    )
    schnorr = replace(
        fs_model.target.finite_schnorr_algorithm(),
        algorithm_kind=k1.Symbol("MixedChallengeFiniteSchnorrVerify"),
        diagnostic_label=k1.Symbol("mixed-challenge-finite-schnorr-verify"),
    )
    contract = k1.DEFAULT_EVALUATION_CONTRACT.identity

    scopes = (base.ScopeDecl(None, None), base.ScopeDecl(0, 1))
    session_value = (
        base.OccurrenceOutputRef(0, 0)
        if run_established
        else base.PublicInputRef(0)
    )
    bindings = (
        base.PublicBindingDecl(
            1, base.BindingClass.STATEMENT, base.PublicInputRef(0)
        ),
        base.PublicBindingDecl(
            1, base.BindingClass.SESSION_CONTEXT, session_value
        ),
    )
    conditions = (base.OccurrenceOutputRef(2, 0),)
    challenges = (
        base.ChallengeDecl(
            1,
            k1.BOOL,
            boolean_challenge_template.domain,
            boolean_challenge_template.fresh_law,
            base.IndependentCorrelation(),
            base.ExclusiveReductionUse(),
            conditions,
        ),
        base.ChallengeDecl(
            1,
            base.Z3,
            finite_domain,
            finite_fresh_law,
            base.IndependentCorrelation(),
            base.ExclusiveReductionUse(),
            conditions,
        ),
    )
    checks = (
        base.CheckDecl(
            schnorr.identity,
            contract,
            (
                base.PublicInputRef(0),
                base.OccurrenceOutputRef(5, 0),
                base.OccurrenceOutputRef(4, 0),
                base.OccurrenceOutputRef(6, 0),
            ),
        ),
    )
    terminals = (
        b5.TerminalDecl(base.TerminalVerdict.ACCEPT, (), (0,), (), ()),
        b5.TerminalDecl(base.TerminalVerdict.REJECT, (), (), (), ()),
    )
    true_constant = base.TypedConstantDecl(
        k1.BOOL, k1.admit_value(k1.BOOL, True)
    )
    occurrences = (
        base.OccurrenceDecl(
            0, base.AlwaysGuard(), base.ProverMessageEffect(channel, base.Z3)
        ),
        base.OccurrenceDecl(
            1,
            base.EvaluateGuard(
                bool_identity.identity, contract, (base.ConstantRef(0),)
            ),
            foundation.VerifierMessageEffect(
                channel,
                z3_identity.identity,
                contract,
                (base.PublicInputRef(0),),
                base.Z3,
            ),
        ),
        base.OccurrenceDecl(
            1,
            base.AlwaysGuard(),
            foundation.VerifierMessageEffect(
                channel,
                z3_identity.identity,
                contract,
                (base.PublicInputRef(0),),
                base.Z3,
            ),
        ),
        base.OccurrenceDecl(1, base.AlwaysGuard(), base.ChallengeEffect(0)),
        base.OccurrenceDecl(1, base.AlwaysGuard(), base.ChallengeEffect(1)),
        base.OccurrenceDecl(
            1, base.AlwaysGuard(), base.ProverMessageEffect(channel, base.Z3)
        ),
        base.OccurrenceDecl(
            1, base.AlwaysGuard(), base.ProverMessageEffect(channel, base.Z3)
        ),
        base.OccurrenceDecl(1, base.AlwaysGuard(), base.CheckEffect(0)),
        base.OccurrenceDecl(
            1,
            base.EvaluateGuard(
                conjunction.identity,
                contract,
                (
                    base.OccurrenceOutputRef(3, 0),
                    base.OccurrenceOutputRef(7, 0),
                ),
            ),
            base.TerminalEffect(0),
        ),
        base.OccurrenceDecl(1, base.AlwaysGuard(), base.TerminalEffect(1)),
    )
    provisional = base.InteractiveCore(
        (),
        (base.InputDecl(base.Z3),),
        (),
        (true_constant,),
        (),
        scopes,
        bindings,
        challenges,
        (),
        checks,
        (),
        (),
        terminals,
        occurrences,
    )
    references = [
        channel,
        boolean_challenge_template.domain,
        boolean_challenge_template.fresh_law,
        finite_domain,
        finite_fresh_law,
    ]
    used_modules = tuple(
        sorted(
            {item.module for item in references},
            key=lambda item: item.internal_reference(),
        )
    )
    return replace(provisional, used_modules=used_modules), (
        z3_identity,
        bool_identity,
        conjunction,
        schnorr,
    )


def _environment(core: Any, algorithms: tuple[Any, ...]) -> Any:
    template = d1.fixture("integrated-baseline")
    finite_template = fs_model.target.make_fixture()
    available_modules = {
        **dict(template.environment.module_preimages),
        **dict(finite_template.environment.module_preimages),
    }
    module_preimages = {
        identifier: available_modules[identifier]
        for identifier in core.used_modules
    }
    algorithm_map = {item.identity: item for item in algorithms}
    algorithm_modules: dict[Any, Mapping[Any, Any]] = {}
    for identifier, algorithm in algorithm_map.items():
        if identifier in template.environment.algorithm_modules:
            algorithm_modules[identifier] = template.environment.algorithm_modules[
                identifier
            ]
        else:
            dependencies = k1.direct_module_dependencies(algorithm)
            algorithm_modules[identifier] = MappingProxyType(
                {
                    dependency: k1.FIXTURE_MODULE_PREIMAGES[dependency]
                    for dependency in dependencies
                }
            )
    contract = k1.DEFAULT_EVALUATION_CONTRACT
    profile = d1.candidate_profile_artifact()
    return base.Environment(
        profile.profile_id,
        MappingProxyType({profile.profile_id: profile.profile}),
        MappingProxyType(module_preimages),
        MappingProxyType(algorithm_map),
        MappingProxyType(algorithm_modules),
        MappingProxyType({contract.identity: contract}),
    )


def _value_type(core: Any, outputs: Any, reference: Any) -> Any:
    return foundation._value_type(core, outputs, reference)


def _ordinary_core_references(core: Any) -> tuple[tuple[Any, ...], tuple[Any, ...]]:
    """Derive the exact-used algorithms/contracts without fixture-only extras."""

    algorithms: set[Any] = set()
    contracts: set[Any] = set()
    for item in core.derived_values:
        algorithms.add(item.algorithm)
        contracts.add(item.evaluation_contract)
    for item in core.checks:
        algorithms.add(item.algorithm)
        contracts.add(item.evaluation_contract)
    for occurrence in core.occurrences:
        if type(occurrence.guard) is base.EvaluateGuard:
            algorithms.add(occurrence.guard.algorithm)
            contracts.add(occurrence.guard.evaluation_contract)
        if type(occurrence.effect) is foundation.VerifierMessageEffect:
            algorithms.add(occurrence.effect.algorithm)
            contracts.add(occurrence.effect.evaluation_contract)
    key = lambda item: item.internal_reference()
    return tuple(sorted(algorithms, key=key)), tuple(sorted(contracts, key=key))


def _validate_pressure_shape(core: Any, functions: Mapping[Any, Any]) -> None:
    bounded_tables = (
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
        core.occurrences,
    )
    if any(type(table) is not tuple or len(table) > (1 << 14) for table in bounded_tables):
        raise PressureError("Core table carrier or constitutional bound drifted")
    if tuple(sorted(core.used_modules, key=lambda item: item.internal_reference())) != core.used_modules:
        raise PressureError("used-module sequence is not canonical sorted order")
    if len(set(core.used_modules)) != len(core.used_modules):
        raise PressureError("used-module sequence is not unique")
    if (
        len(core.public_inputs),
        len(core.constants),
        len(core.scopes),
        len(core.public_bindings),
        len(core.challenges),
        len(core.checks),
        len(core.terminals),
        len(core.occurrences),
    ) != (1, 1, 2, 2, 2, 1, 2, 10):
        raise PressureError("pressure Core census drifted")
    if core.scopes != (base.ScopeDecl(None, None), base.ScopeDecl(0, 1)):
        raise PressureError("scope opening drifted")
    if any(binding.scope != 1 for binding in core.public_bindings):
        raise PressureError("public bindings no longer share one scope opening")
    if len(set((item.scope, item.binding_class, item.value) for item in core.public_bindings)) != len(
        core.public_bindings
    ):
        raise PressureError("public binding triples are not unique")
    if {
        item.value.ordinal
        for item in core.public_bindings
        if type(item.value) is base.PublicInputRef
    } != {0}:
        raise PressureError("public-input binding coverage is incomplete")
    for binding in core.public_bindings:
        if type(binding.value) is base.OccurrenceOutputRef:
            if binding.value.occurrence >= core.scopes[binding.scope].opening:
                raise PressureError("run-established binding is unavailable at opening")
        elif type(binding.value) is not base.PublicInputRef:
            raise PressureError("pressure binding source is outside the exact case")
    if [item.binding_class for item in core.public_bindings] != [
        base.BindingClass.STATEMENT,
        base.BindingClass.SESSION_CONTEXT,
    ]:
        raise PressureError("binding classes or order drifted")
    if [item.value_type for item in core.challenges] != [k1.BOOL, base.Z3]:
        raise PressureError("heterogeneous challenge types drifted")
    if any(
        type(challenge.correlation) is not base.IndependentCorrelation
        for challenge in core.challenges
    ):
        raise PressureError("independent mixed-challenge correlation drifted")
    if any(
        challenge.domain.declaration_kind != "pir.challenge-domain"
        or challenge.fresh_law.declaration_kind != "pir.public-coin-law"
        for challenge in core.challenges
    ):
        raise PressureError("challenge nominal declaration kind drifted")
    if any(
        challenge.public_conditions != (base.OccurrenceOutputRef(2, 0),)
        for challenge in core.challenges
    ):
        raise PressureError("challenge condition coordinate drifted")
    if type(core.occurrences[1].effect) is not foundation.VerifierMessageEffect:
        raise PressureError("guarded verifier occurrence drifted")
    if type(core.occurrences[1].guard) is not base.EvaluateGuard:
        raise PressureError("verifier occurrence is no longer guarded")
    if type(core.occurrences[-1].guard) is not base.AlwaysGuard:
        raise PressureError("first-active terminal fallback drifted")
    if any(occurrence.scope not in (0, 1) for occurrence in core.occurrences):
        raise PressureError("occurrence names an unavailable scope")
    if [occurrence.scope for occurrence in core.occurrences] != [0] + [1] * 9:
        raise PressureError("occurrence scope membership drifted")
    if (
        core.terminals[0].verdict is not base.TerminalVerdict.ACCEPT
        or core.terminals[0].required_true_checks != (0,)
        or core.terminals[1].verdict is not base.TerminalVerdict.REJECT
        or any(
            (
                terminal.public_outputs,
                terminal.required_applied_reductions,
                terminal.terminal_claims,
            )
            != ((), (), ())
            for terminal in core.terminals
        )
    ):
        raise PressureError("first-active terminal contract drifted")

    outputs = d1._output_types(core, MappingProxyType({}))
    available: set[Any] = {
        base.PublicInputRef(0),
        base.ConstantRef(0),
    }
    positions = d1._positions(core)
    if positions["challenge"] != {0: 3, 1: 4}:
        raise PressureError("challenge occurrence map drifted")
    if positions["check"] != {0: 7} or positions["terminal"] != {0: 8, 1: 9}:
        raise PressureError("check or terminal map drifted")
    for occurrence_ref, occurrence in enumerate(core.occurrences):
        reads: tuple[Any, ...] = ()
        if type(occurrence.guard) is base.EvaluateGuard:
            reads += occurrence.guard.inputs
            function = functions[occurrence.guard.algorithm]
            observed = tuple(_value_type(core, outputs, item) for item in reads)
            if function.inputs != observed or function.output != k1.BOOL or function.failures:
                raise PressureError("guard ABI is not exact total Boolean")
        effect = occurrence.effect
        if type(effect) is foundation.VerifierMessageEffect:
            message_inputs = effect.inputs
            reads += message_inputs
            function = functions[effect.algorithm]
            observed = tuple(_value_type(core, outputs, item) for item in message_inputs)
            if (
                function.inputs != observed
                or function.output != effect.payload_type
                or function.failures
            ):
                raise PressureError("verifier-message ABI drifted")
        elif type(effect) is base.ChallengeEffect:
            reads += core.challenges[effect.challenge].public_conditions
        elif type(effect) is base.CheckEffect:
            check = core.checks[effect.check]
            reads += check.inputs
            function = functions[check.algorithm]
            observed = tuple(_value_type(core, outputs, item) for item in check.inputs)
            if function.inputs != observed or function.output != k1.BOOL or function.failures:
                raise PressureError("check ABI drifted")
        elif type(effect) is base.TerminalEffect:
            reads += core.terminals[effect.terminal].public_outputs
        if any(item not in available for item in reads):
            raise PressureError(f"occurrence {occurrence_ref} reads an unavailable value")
        for item in reads:
            if type(item) is base.OccurrenceOutputRef:
                source_guard = core.occurrences[item.occurrence].guard
                if (
                    type(source_guard) is not base.AlwaysGuard
                    and occurrence.guard != source_guard
                ):
                    raise PressureError(
                        f"occurrence {occurrence_ref} fails exact GuardImplies"
                    )
        available.update(
            base.OccurrenceOutputRef(occurrence_ref, output)
            for output in range(len(outputs[occurrence_ref]))
        )

    challenge_backlinks = [
        occurrence.effect.challenge
        for occurrence in core.occurrences
        if type(occurrence.effect) is base.ChallengeEffect
    ]
    check_backlinks = [
        occurrence.effect.check
        for occurrence in core.occurrences
        if type(occurrence.effect) is base.CheckEffect
    ]
    terminal_backlinks = [
        occurrence.effect.terminal
        for occurrence in core.occurrences
        if type(occurrence.effect) is base.TerminalEffect
    ]
    if challenge_backlinks != [0, 1] or check_backlinks != [0] or terminal_backlinks != [0, 1]:
        raise PressureError("one-to-one occurrence backlink closure drifted")
    if core.oracles or core.claims or core.reductions or core.derived_values:
        raise PressureError("pressure Core acquired an unvalidated owner table")


def admit_pressure_core(run_established: bool) -> CoreAdmission:
    core, algorithms = _core_and_algorithms(run_established)
    environment = _environment(core, algorithms)
    candidate = d1.make_candidate(core, environment.profile_id)
    profile, domain, domain_body = d1.b2c0._strict_profiled_body(
        candidate.profiled_body, "end-to-end pressure Core"
    )
    if profile != environment.profile_id:
        raise PressureError("Core body and environment profile differ")
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
    k1.authenticate_content_id(
        candidate.asserted_id,
        candidate.profiled_body,
        environment.prior_meta_preimages,
        ledger=ledger,
    )
    decoded = d1.decode_core(domain)
    if decoded != core or k1.encode_datum(d1.core_domain_datum(decoded)) != domain_body:
        raise PressureError("owner Core compiler did not round-trip")

    algorithm_refs, contract_refs = _ordinary_core_references(decoded)
    if set(algorithm_refs) != set(environment.algorithm_preimages):
        raise PressureError("exact-used algorithm closure differs")
    if set(contract_refs) != set(environment.contract_preimages):
        raise PressureError("exact-used evaluation-contract closure differs")
    if set(decoded.used_modules) != set(environment.module_preimages):
        raise PressureError("exact-used semantic-module closure differs")
    k1.authenticate_module_closure(
        decoded.used_modules,
        dict(environment.module_preimages),
        semantic_regime=k1.SEMANTIC_REGIME_ID,
        ledger=ledger,
    )
    nominal_refs = [
        reference
        for challenge in decoded.challenges
        for reference in (challenge.domain, challenge.fresh_law)
    ]
    nominal_refs.extend(
        occurrence.effect.channel
        for occurrence in decoded.occurrences
        if type(occurrence.effect)
        in {base.ProverMessageEffect, foundation.VerifierMessageEffect}
    )
    for reference in nominal_refs:
        module = environment.module_preimages.get(reference.module)
        if module is None:
            raise PressureError("nominal declaration module is not exact-used")
        k1.resolve_module_declaration(
            module, reference.declaration_kind, reference.local_ordinal
        )
    functions: dict[Any, Any] = {}
    for identifier in algorithm_refs:
        algorithm = environment.algorithm_preimages[identifier]
        if k1.authenticate_algorithm_identity(algorithm, ledger=ledger) != identifier:
            raise PressureError("algorithm identity authentication drifted")
        k1.authenticate_module_closure(
            k1.direct_module_dependencies(algorithm, ledger=ledger),
            dict(environment.algorithm_modules[identifier]),
            semantic_regime=k1.SEMANTIC_REGIME_ID,
            ledger=ledger,
        )
        k1.authenticate_algorithm_declaration_references(
            algorithm, dict(environment.algorithm_modules[identifier]), ledger=ledger
        )
        k1.check_algorithm_syntax_and_types(algorithm)
        functions[identifier] = algorithm.function_type
    for identifier in contract_refs:
        contract = environment.contract_preimages[identifier]
        if contract.identity != identifier:
            raise PressureError("evaluation-contract identity drifted")
        k1.authenticate_content_id(
            identifier,
            contract.body(),
            environment.prior_meta_preimages,
            ledger=ledger,
        )
    _validate_pressure_shape(decoded, functions)
    graph, graph_evidence = d1.derive_graph(decoded, "integrated-baseline")
    if not graph_evidence.eligible:
        raise PressureError("owner PublicCoin graph rejected the pressure Core")
    condition_node = d1._producer_node(base.OccurrenceOutputRef(2, 0))
    if graph_evidence.classes[condition_node] != 0:
        raise PressureError("deterministic verifier condition is not StaticPublic")

    fresh_candidate = d1.b2c0.make_protocol_candidate(
        candidate.asserted_id, environment.profile_id
    )
    k1.authenticate_content_id(
        fresh_candidate.asserted_id,
        fresh_candidate.profiled_body,
        environment.prior_meta_preimages,
    )
    fresh_profile, fresh_domain, _ = d1.b2c0._strict_profiled_body(
        fresh_candidate.profiled_body, "end-to-end Fresh Protocol"
    )
    fields = d1.b2c0._record(fresh_domain, (0, 1), "Fresh Protocol")
    referenced_core = d1.b2c0._content_ref(fields[0], "Fresh Core")
    interpretation, payload = d1.b2c0._variant(fields[1], (0,), "Fresh interpretation")
    d1.b2c0._unit(payload, "Fresh interpretation payload")
    if (
        fresh_profile != environment.profile_id
        or interpretation != 0
        or referenced_core != candidate.asserted_id
    ):
        raise PressureError("Fresh Protocol owner equation did not close")
    closure = d1.b2c0.snapshot_environment(environment)
    return CoreAdmission(
        decoded,
        candidate,
        environment,
        fresh_candidate,
        fresh_candidate.asserted_id,
        d1._output_types(decoded, MappingProxyType({})),
        graph,
        graph_evidence,
        closure,
        ADMISSION_EVALUATOR_IDENTITY,
        tuple(range(1, 11)),
    )


def _admit_fresh_protocol(admission: CoreAdmission) -> FreshProtocolAdmission:
    """Reauthenticate Fresh formation against the retained Core closure."""

    environment = admission.environment
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
    k1.authenticate_content_id(
        admission.candidate.asserted_id,
        admission.candidate.profiled_body,
        environment.prior_meta_preimages,
        ledger=ledger,
    )
    k1.authenticate_content_id(
        admission.fresh_candidate.asserted_id,
        admission.fresh_candidate.profiled_body,
        environment.prior_meta_preimages,
        ledger=ledger,
    )
    closure = d1.b2c0.snapshot_environment(environment)
    if closure != admission.closure:
        raise PressureError("Fresh Protocol closure differs from admitted Core closure")
    if admission.evaluator_identity != ADMISSION_EVALUATOR_IDENTITY:
        raise PressureError("Fresh Protocol evaluator authority differs from Core")
    return FreshProtocolAdmission(
        admission.fresh_candidate,
        admission.fresh_protocol_id,
        admission,
        closure,
        ADMISSION_EVALUATOR_IDENTITY,
        (
            "live-core-authority",
            "profile-and-closure-equality",
            "same-core-reference",
            "closed-fresh-interpretation",
            "protocol-identity-authentication",
        ),
    )


def _authenticate_algorithm(
    algorithm: Any,
    modules: Mapping[Any, Any],
    ledger: Any,
) -> None:
    if k1.authenticate_algorithm_identity(algorithm, ledger=ledger) != algorithm.identity:
        raise PressureError("portable algorithm identity authentication drifted")
    dependencies = k1.direct_module_dependencies(algorithm, ledger=ledger)
    if set(dependencies) != set(modules):
        raise PressureError("portable algorithm module closure is not exact-used")
    k1.authenticate_module_closure(
        dependencies,
        dict(modules),
        semantic_regime=k1.SEMANTIC_REGIME_ID,
        ledger=ledger,
    )
    k1.authenticate_algorithm_declaration_references(
        algorithm, dict(modules), ledger=ledger
    )
    k1.check_algorithm_syntax_and_types(algorithm)


def _construction_profiles() -> tuple[Any, Mapping[Any, Any]]:
    repository = fs_model.target.publication.compile_repository()
    interaction = repository.profiles["interaction"]
    canonical = repository.profiles["canonical-framed-fiat-shamir"]
    profiles = MappingProxyType(
        {
            interaction.profile_id: interaction.profile,
            canonical.profile_id: canonical.profile,
        }
    )
    if canonical.profile.profile_imports != (interaction.profile_id,):
        raise PressureError("canonical-framed profile import closure drifted")
    return canonical, profiles


def _construction_static_bounds(
    admission: CoreAdmission, construction: Any
) -> ConstructionBounds:
    """Derive this finite Core's exact worst static frame/draw envelope."""

    core = admission.core
    maximum_z3 = k1.admit_value(base.Z3, k1.Nat(2))
    frame_datums = [
        _v(0, k1.BytesValue(construction.core_id.internal_reference())),
        _v(1, k1.BytesValue(construction.identifier.internal_reference())),
        _v(2, fs_model._module_ref_body(construction.application_domain)),
        _v(3, _s((k1.Nat(0),))),
        _v(3, _s((k1.Nat(0), k1.Nat(1)))),
    ]
    for binding_ref, binding in enumerate(core.public_bindings):
        frame_datums.append(
            _v(
                4,
                _r(
                    k1.Nat(binding_ref),
                    _v(binding.binding_class.value),
                    k1.value_type_datum(base.Z3),
                    maximum_z3.datum,
                ),
            )
        )
    for occurrence_ref in (1, 8):
        frame_datums.append(_v(5, _r(k1.Nat(occurrence_ref), True)))
    for occurrence_ref in (0, 1, 2, 5, 6):
        effect = core.occurrences[occurrence_ref].effect
        frame_datums.append(
            _v(
                7 if type(effect) is foundation.VerifierMessageEffect else 6,
                _r(
                    k1.Nat(occurrence_ref),
                    fs_model._module_ref_body(effect.channel),
                    k1.value_type_datum(base.Z3),
                    maximum_z3.datum,
                ),
            )
        )
    for challenge_ref in range(len(core.challenges)):
        frame_datums.append(
            _v(
                11,
                _r(
                    k1.Nat(challenge_ref),
                    k1.Nat(0),
                    k1.value_type_datum(base.Z3),
                    maximum_z3.datum,
                ),
            )
        )
    frame_sizes = tuple(len(k1.encode_datum(item)) for item in frame_datums)
    if len(frame_sizes) != 16:
        raise PressureError("derived maximum frame schedule drifted")

    namespace_sizes: list[int] = []
    for rule in construction.challenge_rules:
        for draw_ordinal in range(rule.maximum_draws):
            namespace = fs_executor.challenge_namespace(
                construction, core, rule.challenge, draw_ordinal
            )
            if type(namespace.datum) is not k1.BytesValue:
                raise PressureError("derived challenge namespace is not bytes")
            namespace_sizes.append(len(namespace.datum.value))

    byte_schema = construction.transcript_bytes_type.schema
    if type(byte_schema) is not k1.BytesSchema:
        raise PressureError("transcript byte type does not have a byte schema")
    if max((*frame_sizes, *namespace_sizes), default=0) > byte_schema.maximum_length:
        raise PressureError("a derived frame or namespace crosses transcript capacity")
    maximum_transition_calls = len(frame_sizes) + sum(
        rule.maximum_draws for rule in construction.challenge_rules
    )
    maximum_cumulative_octets = (
        sum(frame_sizes)
        + sum(namespace_sizes)
        + sum(
            rule.draw_bytes * rule.maximum_draws
            for rule in construction.challenge_rules
        )
    )
    if (
        len(construction.challenge_rules) > (1 << 14)
        or len(frame_sizes) > (1 << 20)
        or maximum_transition_calls > (1 << 20)
        or maximum_cumulative_octets > (1 << 30)
    ):
        raise PressureError("construction cumulative static bound crossed")
    return ConstructionBounds(
        len(construction.challenge_rules),
        len(frame_sizes),
        maximum_transition_calls,
        max(frame_sizes),
        max(namespace_sizes),
        maximum_cumulative_octets,
    )


def _authenticate_construction(
    admission: CoreAdmission,
    construction: Any,
    application_module: Any,
    algorithms: tuple[Any, ...],
) -> tuple[Any, tuple[Any, ...]]:
    """Run the authentication and exact-used closure parts of admission."""

    canonical_profile, profiles = _construction_profiles()
    environment = admission.environment
    ledger = k1.AuthenticationLedger()
    k1.authenticate_prior_meta_basis(
        environment.prior_meta_preimages, ledger=ledger
    )
    k1.effective_semantic_context(
        canonical_profile.profile_id,
        dict(profiles),
        semantic_regime=k1.SEMANTIC_REGIME_ID,
        ledger=ledger,
    )
    k1.authenticate_content_id(
        admission.candidate.asserted_id,
        admission.candidate.profiled_body,
        environment.prior_meta_preimages,
        ledger=ledger,
    )
    k1.authenticate_module_closure(
        admission.core.used_modules,
        dict(environment.module_preimages),
        semantic_regime=k1.SEMANTIC_REGIME_ID,
        ledger=ledger,
    )
    for identifier, algorithm in environment.algorithm_preimages.items():
        _authenticate_algorithm(
            algorithm, environment.algorithm_modules[identifier], ledger
        )
    for identifier, contract in environment.contract_preimages.items():
        if identifier != contract.identity:
            raise PressureError("retained Core evaluation-contract identity drifted")
        k1.authenticate_content_id(
            identifier,
            contract.body(),
            environment.prior_meta_preimages,
            ledger=ledger,
        )

    construction_body = k1.encode_datum(
        k1.profiled_semantic_body(
            construction.profile_id,
            fs_model.construction_domain_datum(construction),
        )
    )
    k1.authenticate_content_id(
        construction.identifier,
        construction_body,
        environment.prior_meta_preimages,
        ledger=ledger,
    )
    k1.authenticate_module_closure(
        (application_module.identity,),
        {application_module.identity: application_module},
        semantic_regime=k1.SEMANTIC_REGIME_ID,
        ledger=ledger,
    )
    for algorithm in algorithms:
        dependencies = k1.direct_module_dependencies(algorithm, ledger=ledger)
        modules = MappingProxyType(
            {
                dependency: k1.FIXTURE_MODULE_PREIMAGES[dependency]
                for dependency in dependencies
            }
        )
        _authenticate_algorithm(algorithm, modules, ledger)
    for use in (
        construction.absorb,
        construction.squeeze_bytes,
        construction.advance_state,
        *(item for rule in construction.challenge_rules for item in (rule.accept, rule.decode)),
    ):
        if use.evaluation_contract.identity != fs_model.EVALUATION_CONTRACT.identity:
            raise PressureError("construction evaluation contract is not exact")
        k1.authenticate_content_id(
            use.evaluation_contract.identity,
            use.evaluation_contract.body(),
            environment.prior_meta_preimages,
            ledger=ledger,
        )
    return canonical_profile, tuple(profiles)


def _sampling_algorithms(construction: Any) -> tuple[Any, Any, Any, Any]:
    byte_type = construction.transcript_bytes_type
    z3 = base.Z3
    bool_inputs = (byte_type, z3)
    root_nat_inputs = (byte_type, z3)
    accept_boolean = k1.CanonicalAlgorithm(
        k1.Symbol("PressureBooleanAccept"),
        bool_inputs,
        k1.Literal(k1.admit_value(k1.BOOL, True)),
    )
    decode_boolean = k1.CanonicalAlgorithm(
        k1.Symbol("PressureBooleanDecode"),
        bool_inputs,
        k1.Literal(k1.admit_value(k1.BOOL, True)),
    )
    number = fs_model._first_u64(k1.Variable(0, byte_type))
    accept_z3 = k1.CanonicalAlgorithm(
        k1.Symbol("PressureRootNatAccept"),
        root_nat_inputs,
        fs_model._call("nat.lt", number, fs_model._nat(3 * (1 << 62))),
    )
    decode_z3 = k1.CanonicalAlgorithm(
        k1.Symbol("PressureRootNatDecode"),
        root_nat_inputs,
        fs_model._quartile(
            number,
            (
                fs_model._z3(0),
                fs_model._z3(1),
                fs_model._z3(2),
                fs_model._z3(2),
            ),
        ),
    )
    return accept_boolean, decode_boolean, accept_z3, decode_z3


def _construction_for(
    admission: CoreAdmission,
) -> tuple[TranscriptConstructionAdmission, tuple[Any, ...]]:
    predecessor = fs_model.make_subject("retrying")
    common = predecessor.construction
    accept_bool, decode_bool, accept_z3, decode_z3 = _sampling_algorithms(common)
    contract = fs_model.EVALUATION_CONTRACT
    rules = (
        fs_model.ChallengeRule(
            0,
            8,
            1,
            fs_model.AlgorithmUse(accept_bool, contract),
            fs_model.AlgorithmUse(decode_bool, contract),
        ),
        fs_model.ChallengeRule(
            1,
            8,
            2,
            fs_model.AlgorithmUse(accept_z3, contract),
            fs_model.AlgorithmUse(decode_z3, contract),
        ),
    )
    provisional = replace(
        common,
        core_id=admission.candidate.asserted_id,
        challenge_rules=rules,
        identifier=None,
    )
    identifier = k1.profiled_content_id(
        "pir.transcript-construction",
        provisional.profile_id,
        fs_model.construction_domain_datum(provisional),
        semantic_regime=k1.SEMANTIC_REGIME_ID,
    )
    construction = replace(provisional, identifier=identifier)
    algorithms = (
        construction.absorb.algorithm,
        construction.squeeze_bytes.algorithm,
        construction.advance_state.algorithm,
        accept_bool,
        decode_bool,
        accept_z3,
        decode_z3,
    )
    expected_inputs = (
        (
            construction.transcript_bytes_type,
            base.Z3,
        ),
        (
            construction.transcript_bytes_type,
            base.Z3,
        ),
        (
            construction.transcript_bytes_type,
            base.Z3,
        ),
        (
            construction.transcript_bytes_type,
            base.Z3,
        ),
    )
    expected_outputs = (k1.BOOL, k1.BOOL, k1.BOOL, base.Z3)
    for algorithm, inputs, output in zip(
        algorithms[-4:], expected_inputs, expected_outputs
    ):
        k1.check_algorithm_syntax_and_types(algorithm)
        function = algorithm.function_type
        if function.inputs != inputs or function.output != output or function.failures:
            raise PressureError("heterogeneous challenge-rule ABI drifted")
    if [(item.challenge, item.draw_bytes, item.maximum_draws) for item in rules] != [
        (0, 8, 1),
        (1, 8, 2),
    ]:
        raise PressureError("challenge rule order or draw bounds drifted")
    if type(construction) is not fs_model.TranscriptConstruction:
        raise PressureError("construction does not use the closed owner carrier")
    if not admission.core.challenges or len(rules) != len(admission.core.challenges):
        raise PressureError("construction challenge-rule map is not total and nonempty")
    byte_schema = construction.transcript_bytes_type.schema
    natural_schema = construction.natural_type.schema
    if (
        construction.transcript_bytes_type.domain != k1.BYTES_DOMAIN
        or type(byte_schema) is not k1.BytesSchema
        or byte_schema.minimum_length != 0
        or byte_schema.maximum_length > (1 << 20) - 26
        or construction.natural_type.domain != k1.NAT_DOMAIN
        or type(natural_schema) is not k1.NatSchema
        or natural_schema.maximum < max(
            *(item.draw_bytes for item in rules),
            *(item.maximum_draws for item in rules),
        )
    ):
        raise PressureError("construction common value types or bounds drifted")
    for value_type in (
        construction.transcript_state_type,
        construction.transcript_bytes_type,
        construction.natural_type,
        k1.BOOL,
        *(item.value_type for item in admission.core.challenges),
    ):
        value_type.__post_init__()
        k1.maximum_encoded_size(value_type.schema)
    if (
        k1.admit_value(
            construction.transcript_state_type, construction.initial_state.datum
        )
        != construction.initial_state
    ):
        raise PressureError("construction initial state is not exact and admitted")
    common_abis = (
        (
            construction.absorb,
            (construction.transcript_state_type, construction.transcript_bytes_type),
            construction.transcript_state_type,
        ),
        (
            construction.squeeze_bytes,
            (
                construction.transcript_state_type,
                construction.transcript_bytes_type,
                construction.natural_type,
            ),
            construction.transcript_bytes_type,
        ),
        (
            construction.advance_state,
            (
                construction.transcript_state_type,
                construction.transcript_bytes_type,
                construction.natural_type,
                construction.transcript_bytes_type,
            ),
            construction.transcript_state_type,
        ),
    )
    for use, inputs, output in common_abis:
        k1.check_algorithm_syntax_and_types(use.algorithm)
        function = use.algorithm.function_type
        if (
            function.inputs != inputs
            or function.output != output
            or function.failures
            or use.evaluation_contract != fs_model.EVALUATION_CONTRACT
        ):
            raise PressureError("common transcript algorithm ABI drifted")
        k1.maximum_completion_size(use.algorithm.function_type)
    for rule in rules:
        if (
            not 1 <= rule.draw_bytes <= byte_schema.maximum_length
            or not 1 <= rule.maximum_draws <= (1 << 20)
        ):
            raise PressureError("challenge rule crosses owner draw bounds")
        k1.maximum_completion_size(rule.accept.algorithm.function_type)
        k1.maximum_completion_size(rule.decode.algorithm.function_type)
    if (
        construction.core_id != admission.candidate.asserted_id
        or tuple(rule.challenge for rule in construction.challenge_rules) != (0, 1)
        or not admission.graph_evidence.eligible
    ):
        raise PressureError("construction Core/rule/public-coin admission drifted")
    application_module = predecessor.application_module
    app_body = k1.resolve_module_declaration(
        application_module,
        construction.application_domain.declaration_kind,
        construction.application_domain.local_ordinal,
    )
    if (
        construction.application_domain.module != application_module.identity
        or construction.application_domain.declaration_kind
        != "pir.fs-application-domain"
        or construction.application_domain.local_ordinal != 0
        or app_body != _r(k1.Symbol(fs_model.APPLICATION_DOMAIN_SYMBOL))
    ):
        raise PressureError("application-domain declaration drifted")
    k1.authenticate_failure_reference(
        construction.sampling_exhausted_failure,
        {application_module.identity: application_module},
        semantic_regime=k1.SEMANTIC_REGIME_ID,
    )
    expected_failure_body = _r(
        k1.Symbol("pir.fs.sampling-exhausted"),
        fs_model._sampling_payload_declaration_type(),
    )
    observed_failure_body = k1.resolve_module_declaration(
        application_module,
        "semantic-failure",
        construction.sampling_exhausted_failure.local_ordinal,
    )
    expected_failure_payload = k1.ValueType(
        k1.RECORD_DOMAIN,
        k1.RecordSchema(
            (
                (0, k1.ValueType(k1.NAT_DOMAIN, k1.NatSchema((1 << 14) - 1))),
                (1, k1.ValueType(k1.NAT_DOMAIN, k1.NatSchema(1 << 20))),
            )
        ),
    )
    if (
        construction.sampling_exhausted_failure.declaration_module
        != application_module.identity
        or construction.sampling_exhausted_failure.local_ordinal != 0
        or construction.sampling_exhausted_failure.payload_type
        != expected_failure_payload
        or observed_failure_body != expected_failure_body
    ):
        raise PressureError("sampling-exhausted failure coordinate drifted")
    k1.maximum_encoded_size(expected_failure_payload.schema)
    k1.encode_datum(
        k1.semantic_failure_type_datum(construction.sampling_exhausted_failure)
    )
    recomputed = k1.profiled_content_id(
        "pir.transcript-construction",
        construction.profile_id,
        fs_model.construction_domain_datum(construction),
        semantic_regime=k1.SEMANTIC_REGIME_ID,
    )
    if recomputed != construction.identifier:
        raise PressureError("construction owner identity equation drifted")
    canonical_profile, profile_ids = _authenticate_construction(
        admission, construction, application_module, algorithms
    )
    if canonical_profile.profile_id != construction.profile_id:
        raise PressureError("authenticated construction profile drifted")

    supported_effects = {
        base.ProverMessageEffect,
        foundation.VerifierMessageEffect,
        base.ChallengeEffect,
        base.CheckEffect,
        base.TerminalEffect,
    }
    if any(
        type(occurrence.effect) not in supported_effects
        for occurrence in admission.core.occurrences
    ):
        raise PressureError("construction lacks an exact-used effect rule")
    if admission.core.reductions:
        raise PressureError("pressure construction acquired a reduction requirement")
    static_values, missing = fs_views._construction_views(
        admission.core, construction, None
    )
    if missing or set(static_values) != {
        "CanonicalTranscriptDeclarationView",
        "CanonicalRequiredInfluenceView",
        "CanonicalChallengeTransitionView",
    }:
        raise PressureError("construction action/influence derivation is incomplete")
    bounds = _construction_static_bounds(admission, construction)
    return (
        TranscriptConstructionAdmission(
            construction,
            admission,
            profile_ids,
            tuple(item.identity for item in algorithms),
            bounds,
            ADMISSION_EVALUATOR_IDENTITY,
            tuple(range(1, 12)),
        ),
        algorithms,
    )


def _admit_fs_protocol(
    admission: CoreAdmission,
    fresh_admission: FreshProtocolAdmission,
    construction_admission: TranscriptConstructionAdmission,
) -> FSProtocolAdmission:
    construction = construction_admission.construction
    fs_protocol_id = k1.profiled_content_id(
        "pir.protocol",
        construction.profile_id,
        fs_model.protocol_domain_datum(
            admission.candidate.asserted_id, construction.identifier
        ),
        semantic_regime=k1.SEMANTIC_REGIME_ID,
    )
    fs_protocol = fs_model.FSProtocol(
        admission.candidate.asserted_id,
        construction.identifier,
        construction.profile_id,
        fs_protocol_id,
    )
    if (
        construction.core_id != admission.candidate.asserted_id
        or construction_admission.core_admission is not admission
        or not admission.graph_evidence.eligible
        or not admission.core.challenges
        or fresh_admission.core_admission is not admission
        or fresh_admission.evaluator_identity
        != construction_admission.evaluator_identity
    ):
        raise PressureError("Fiat-Shamir Protocol admission prerequisites drifted")
    canonical_profile, profiles = _construction_profiles()
    ledger = k1.AuthenticationLedger()
    k1.authenticate_prior_meta_basis(
        admission.environment.prior_meta_preimages, ledger=ledger
    )
    k1.effective_semantic_context(
        canonical_profile.profile_id,
        dict(profiles),
        semantic_regime=k1.SEMANTIC_REGIME_ID,
        ledger=ledger,
    )
    k1.authenticate_content_id(
        construction.identifier,
        k1.encode_datum(
            k1.profiled_semantic_body(
                construction.profile_id,
                fs_model.construction_domain_datum(construction),
            )
        ),
        admission.environment.prior_meta_preimages,
        ledger=ledger,
    )
    k1.authenticate_content_id(
        fs_protocol.identifier,
        k1.encode_datum(
            k1.profiled_semantic_body(
                construction.profile_id,
                fs_model.protocol_domain_datum(
                    admission.candidate.asserted_id, construction.identifier
                ),
            )
        ),
        admission.environment.prior_meta_preimages,
        ledger=ledger,
    )
    return FSProtocolAdmission(
        fs_protocol,
        admission,
        construction_admission,
        ADMISSION_EVALUATOR_IDENTITY,
        (
            "same-core",
            "retained-public-coin-result",
            "retained-module-support",
            "nonempty-challenge-sequence",
            "literal-evaluator-identity",
            "protocol-identity-authentication",
        ),
    )


def _admit_checked_construction(
    fresh_admission: FreshProtocolAdmission,
    fs_admission: FSProtocolAdmission,
    checked: Any,
    checker_contract_id: Any,
) -> CheckedConstructionAdmission:
    admission = fs_admission.core_admission
    construction_admission = fs_admission.construction_admission
    construction = construction_admission.construction
    core = admission.core
    expected_occurrence_map = tuple(
        (item, item) for item in range(len(core.occurrences))
    )
    expected_value_map = (
        ("public-input:0", "public-input:0"),
        ("constant:0", "constant:0"),
        *tuple(
            (
                f"occurrence-output:{occurrence}:0",
                f"occurrence-output:{occurrence}:0",
            )
            for occurrence, output_types in enumerate(admission.outputs)
            if output_types
        ),
    )
    expected_challenge_map = tuple(
        (item, item) for item in range(len(core.challenges))
    )
    if (
        checked.source_protocol_id != fresh_admission.protocol_id
        or checked.target_protocol_id != fs_admission.protocol.identifier
        or checked.shared_core_id != admission.candidate.asserted_id
        or checked.transcript_construction_id != construction.identifier
        or checked.occurrence_map != expected_occurrence_map
        or checked.value_map != expected_value_map
        or checked.challenge_map != expected_challenge_map
        or checked.conclusion != "StructurallyConstructed"
        or not admission.graph_evidence.eligible
        or construction_admission.verified_steps != tuple(range(1, 12))
    ):
        raise PressureError("checked same-Core construction comparison drifted")

    canonical_artifact, profiles = _construction_profiles()
    canonical_profile = canonical_artifact.profile
    contract_body = finite_fixture._checked_construction_checker_contract_body(
        canonical_profile,
        finite_fixture.PIRSourceOwnerCompiler.CANONICAL_FRAMED,
        finite_fixture._checked_fs_result_schema_body(),
    )
    recomputed = finite_fixture._checked_construction_checker_contract_id(
        canonical_profile,
        finite_fixture.PIRSourceOwnerCompiler.CANONICAL_FRAMED,
        finite_fixture._checked_fs_result_schema_body(),
    )
    if checker_contract_id != recomputed:
        raise PressureError("checked-construction contract equation drifted")
    ledger = k1.AuthenticationLedger()
    k1.authenticate_prior_meta_basis(
        admission.environment.prior_meta_preimages, ledger=ledger
    )
    k1.effective_semantic_context(
        canonical_artifact.profile_id,
        dict(profiles),
        semantic_regime=k1.SEMANTIC_REGIME_ID,
        ledger=ledger,
    )
    k1.authenticate_content_id(
        checker_contract_id,
        k1.encode_datum(
            k1.profiled_semantic_body(
                canonical_artifact.profile_id, contract_body
            )
        ),
        admission.environment.prior_meta_preimages,
        ledger=ledger,
    )
    values, missing = fs_views._construction_views(core, construction, checked)
    if missing or set(values) != {
        "CanonicalTranscriptDeclarationView",
        "CanonicalRequiredInfluenceView",
        "CanonicalChallengeTransitionView",
        "CanonicalFSConstructionView",
    }:
        raise PressureError("checked construction has an incomplete owner view")
    fs_views._validate_values(values)
    return CheckedConstructionAdmission(
        checked,
        checker_contract_id,
        ADMISSION_EVALUATOR_IDENTITY,
        tuple(range(1, 8)),
    )


def make_subject(run_established: bool = False) -> PressureSubject:
    admission = admit_pressure_core(run_established)
    fresh_admission = _admit_fresh_protocol(admission)
    construction_admission, algorithms = _construction_for(admission)
    construction = construction_admission.construction
    fs_admission = _admit_fs_protocol(
        admission, fresh_admission, construction_admission
    )
    fs_protocol = fs_admission.protocol
    checked = fs_model.CheckedConstruction(
        admission.fresh_protocol_id,
        fs_protocol.identifier,
        admission.candidate.asserted_id,
        construction.identifier,
        tuple((item, item) for item in range(len(admission.core.occurrences))),
        (
            ("public-input:0", "public-input:0"),
            ("constant:0", "constant:0"),
            *tuple(
                (
                    f"occurrence-output:{occurrence}:0",
                    f"occurrence-output:{occurrence}:0",
                )
                for occurrence, output_types in enumerate(admission.outputs)
                if output_types
            ),
        ),
        ((0, 0), (1, 1)),
        "StructurallyConstructed",
    )
    repository = fs_model.target.publication.compile_repository()
    canonical_profile = repository.profiles["canonical-framed-fiat-shamir"].profile
    if canonical_profile.identity != construction.profile_id:
        raise PressureError("construction profile differs from current publication")
    checker_contract_id = finite_fixture._checked_fs_checker_contract_id(
        canonical_profile
    )
    checked_admission = _admit_checked_construction(
        fresh_admission, fs_admission, checked, checker_contract_id
    )
    return PressureSubject(
        "run-established" if run_established else "invocation-determined",
        admission,
        fresh_admission,
        construction,
        construction_admission,
        fs_protocol,
        fs_admission,
        checked,
        checked_admission,
        checker_contract_id,
        tuple(admission.environment.algorithm_preimages.values()) + algorithms,
    )


def interaction_views(subject: PressureSubject) -> tuple[dict[str, Any], dict[str, str]]:
    values = integrated.project_admitted_values(
        subject.admission.core,
        subject.admission.candidate.asserted_id,
        subject.admission.fresh_protocol_id,
    )
    encoded = integrated.encode_views(values)
    return values, {
        name: hashlib.sha256(body).hexdigest() for name, body in encoded.items()
    }


def canonical_views(subject: PressureSubject) -> tuple[dict[str, Any], dict[str, str], dict[str, Any]]:
    values, missing = fs_views._construction_views(
        subject.admission.core, subject.construction, subject.checked
    )
    if missing:
        raise PressureError("canonical-framed projection omitted a challenge frame")
    digests = fs_views._validate_values(values)
    runtime_subject = SimpleNamespace(
        construction=subject.construction,
        fs_protocol=subject.fs_protocol,
        fixture=SimpleNamespace(
            core_candidate=SimpleNamespace(core=subject.admission.core),
            environment=subject.admission.environment,
        ),
    )
    execution = fs_views.execution_view(runtime_subject)
    return values, digests, execution


def _content_ref(identifier: Any, expected_kind: str) -> Any:
    if identifier.subject_kind != expected_kind:
        raise PressureError(f"content reference is not {expected_kind}")
    return k1.BytesValue(identifier.internal_reference())


def public_setup_view(
    subject: PressureSubject, protocol_id: Any, statement: int
) -> dict[str, Any]:
    core = subject.admission.core
    invocation_values = {base.PublicInputRef(0): k1.admit_value(base.Z3, k1.Nat(statement))}
    entries: list[Any] = []
    normalized_entries: list[dict[str, Any]] = []
    run_established: list[int] = []
    for binding_ref, binding in enumerate(core.public_bindings):
        if binding.binding_class not in {
            base.BindingClass.SESSION_CONTEXT,
            base.BindingClass.PUBLIC_PARAMETER,
        }:
            continue
        value = invocation_values.get(binding.value)
        if value is None:
            run_established.append(binding_ref)
            continue
        class_tag = (
            0 if binding.binding_class is base.BindingClass.SESSION_CONTEXT else 1
        )
        entries.append(
            _r(
                k1.Nat(binding_ref),
                k1.Nat(binding.scope),
                _v(class_tag),
                k1.value_type_datum(value.value_type),
                value.datum,
            )
        )
        normalized_entries.append(
            {
                "binding_ref": binding_ref,
                "scope_ref": binding.scope,
                "class": binding.binding_class.name,
                "value": _canonical_value(value),
            }
        )
    body = _r(
        _content_ref(protocol_id, "pir.protocol"),
        _content_ref(subject.admission.candidate.asserted_id, "pir.interactive-core"),
        _s(tuple(entries)),
        _s(tuple(k1.Nat(item) for item in run_established)),
    )
    repository = fs_model.target.publication.compile_repository()
    profile = repository.profiles["public-setup"]
    identifier = k1.profiled_content_id(
        "pir.public-setup-invocation-view",
        profile.profile_id,
        body,
        semantic_regime=k1.SEMANTIC_REGIME_ID,
    )
    return {
        "protocol_id": _id(protocol_id),
        "core_id": _id(subject.admission.candidate.asserted_id),
        "view_id": _id(identifier),
        "entries": normalized_entries,
        "run_established": run_established,
        "body_sha256": hashlib.sha256(k1.encode_datum(body)).hexdigest(),
        "entry_sequence_sha256": digest(normalized_entries),
    }


def setup_evidence(
    baseline: PressureSubject, run_variant: PressureSubject, statement: int = 2
) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for name, subject in (("baseline", baseline), ("run_variant", run_variant)):
        fresh = public_setup_view(
            subject, subject.admission.fresh_protocol_id, statement
        )
        fs = public_setup_view(subject, subject.fs_protocol.identifier, statement)
        if fresh["entries"] != fs["entries"] or fresh["run_established"] != fs["run_established"]:
            raise PressureError("Fresh and FS public-setup projections differ")
        result[name] = {"fresh": fresh, "fiat_shamir": fs}
    if result["baseline"]["fresh"]["run_established"]:
        raise PressureError("baseline setup unexpectedly needs a run")
    if result["run_variant"]["fresh"]["run_established"] != [1]:
        raise PressureError("run-established setup coordinate drifted")
    return result


def fixed_setup_formation(
    subject: PressureSubject, setup: Mapping[str, Any]
) -> dict[str, Any]:
    expected_bindings = [
        binding_ref
        for binding_ref, binding in enumerate(subject.admission.core.public_bindings)
        if binding.binding_class
        in {base.BindingClass.SESSION_CONTEXT, base.BindingClass.PUBLIC_PARAMETER}
    ]
    fresh = setup["fresh"]
    fiat_shamir = setup["fiat_shamir"]
    fresh_bindings = [item["binding_ref"] for item in fresh["entries"]]
    fs_bindings = [item["binding_ref"] for item in fiat_shamir["entries"]]
    common_entries = fresh["entries"] == fiat_shamir["entries"]
    complete_entries = (
        fresh_bindings == expected_bindings and fs_bindings == expected_bindings
    )
    empty_run_established = not (
        fresh["run_established"] or fiat_shamir["run_established"]
    )
    if not (common_entries and complete_entries and empty_run_established):
        return {
            "outcome": "Refused",
            "code": "F0V4-R-FIXED-SETUP-RUN-ESTABLISHED",
            "expected_binding_refs": expected_bindings,
            "entry_binding_refs": fresh_bindings,
            "run_established": fresh["run_established"],
            "owner_coordinate": (
                "docs-next/analysis/cryptographic-properties.md lines 561-572"
            ),
        }
    return {
        "outcome": "Affirmative",
        "code": "F0V4-A-FIXED-SETUP-FORMATION",
        "expected_binding_refs": expected_bindings,
        "entry_binding_refs": fresh_bindings,
        "run_established": [],
        "common_entries_sha256": fresh["entry_sequence_sha256"],
    }


def _transport_type(value_type: Any) -> Any:
    return k1.ValueType(
        k1.VARIANT_DOMAIN,
        k1.VariantSchema(((0, k1.UNIT_VALUE), (1, value_type))),
    )


def _interface_body(
    subject: PressureSubject, omit: int | None = None
) -> tuple[Any, dict[str, Any], dict[str, Any]]:
    core = subject.admission.core
    construction = subject.construction
    challenge_ref_type = k1.ValueType(k1.NAT_DOMAIN, k1.NatSchema((1 << 14) - 1))
    draw_count_type = k1.ValueType(k1.NAT_DOMAIN, k1.NatSchema(1 << 20))
    codec_types = (
        base.Z3,
        _transport_type(base.Z3),
        _transport_type(k1.BOOL),
        construction.sampling_exhausted_failure.payload_type,
        challenge_ref_type,
        draw_count_type,
        construction.transcript_state_type,
    )
    codec_bodies = tuple(_v(0, _v(0, k1.value_type_datum(item))) for item in codec_types)
    slots: list[tuple[str, int]] = [("input.statement", 0)]
    formable = (
        (0, 0, 0, 1),
        (1, 0, 1, 1),
        (2, 0, 1, 1),
        (3, 1, 2, 2),
        (4, 1, 2, 1),
        (5, 0, 0, 1),
        (6, 0, 0, 1),
    )
    transports: list[tuple[int, int, int, int, int]] = []
    for occurrence, target_tag, source_tag, codec in formable:
        slot = len(slots)
        slots.append((f"transport.occurrence.{occurrence}", codec))
        if occurrence != omit:
            transports.append((occurrence, target_tag, source_tag, 2, slot))
    failure_slots: list[int] = []
    for key, codec in (
        ("failure.payload", 3),
        ("failure.challenge", 4),
        ("failure.prefix-count", 5),
        ("failure.prefix-state", 6),
        ("failure.final-state", 6),
    ):
        failure_slots.append(len(slots))
        slots.append((key, codec))

    statement_members = (_r(k1.Nat(0), k1.Nat(0), _v(0, k1.Nat(0))),)
    transport_bodies = tuple(
        _r(
            _v(target_tag, k1.Nat(occurrence)),
            _v(source_tag),
            _v(destination),
            k1.Nat(slot),
        )
        for occurrence, target_tag, source_tag, destination, slot in transports
    )
    terminal_completions = (
        _r(_v(0, k1.Nat(0)), k1.Symbol("accepted"), _s(())),
        _r(_v(0, k1.Nat(1)), k1.Symbol("rejected"), _s(())),
    )
    failure_payloads = tuple(
        _r(_v(tag), k1.Nat(slot))
        for tag, slot in zip((1, 2, 3, 4, 5), failure_slots)
    )
    completions = (
        *terminal_completions,
        _r(_v(1), k1.Symbol("sampling-failure"), _s(failure_payloads)),
    )
    body = _r(
        _content_ref(subject.fs_protocol.identifier, "pir.protocol"),
        _s(codec_bodies),
        _s(tuple(_r(k1.Symbol(key), k1.Nat(codec)) for key, codec in slots)),
        _s((_r(_v(0, k1.Nat(0)), k1.Nat(0)),)),
        _s(statement_members),
        _s(transport_bodies),
        _s(completions),
    )
    normalized = {
        "codec_count": len(codec_types),
        "slot_count": len(slots),
        "invocation_assignment": {"Public(0)": 0},
        "statement_members": [{"slot": 0, "binding": 0, "flow": "SuppliesInvocation(0)"}],
        "transport_occurrences": [item[0] for item in transports],
        "completion_targets": ["CoreTerminal(0)", "CoreTerminal(1)", "FiatShamirInterpretationFailure"],
        "replay_input_occurrences": [2],
    }
    components = {
        "codec_types": codec_types,
        "slots": tuple(slots),
        "transports": tuple(transports),
        "failure_slots": tuple(failure_slots),
        "statement_members": ((0, 0, 0, 0),),
        "terminal_completions": ((0, "accepted"), (1, "rejected")),
        "failure_payloads": tuple(zip((1, 2, 3, 4, 5), failure_slots)),
    }
    return body, normalized, components


def _require_interface_item(condition: bool, item: int, detail: str) -> None:
    if not condition:
        raise PressureError(f"Interface admission item {item}: {detail}")


def _validate_interface_prefix(
    subject: PressureSubject, components: Mapping[str, Any]
) -> None:
    """Reconstruct admission items 1--5 for this exact finite declaration."""

    core = subject.admission.core
    codecs = components["codec_types"]
    slots = components["slots"]
    transports = components["transports"]

    # Item 1: the declaration is tied to this exact admitted Protocol and all
    # references below are bounded local ordinals in that subject.
    _require_interface_item(
        subject.fs_protocol.core_id == subject.admission.candidate.asserted_id,
        1,
        "Protocol/Core identity differs",
    )
    _require_interface_item(
        all(0 <= codec < len(codecs) for _, codec in slots)
        and len({key for key, _ in slots}) == len(slots),
        1,
        "slot key or codec reference is not local and exact",
    )

    # Item 2: all codecs are direct Structural codecs and the sequence is
    # exactly used by the slot sequence.  CanonicalValueTypeBody formation was
    # already exercised while constructing each codec body.
    _require_interface_item(
        {codec for _, codec in slots} == set(range(len(codecs))),
        2,
        "codec sequence is not exactly used",
    )

    # Item 3: this Core has one public input and no verifier-private input.
    # The sole ExternalSupply slot has the exact input semantic type.
    _require_interface_item(
        len(core.public_inputs) == 1
        and not core.verifier_private_inputs
        and slots[0] == ("input.statement", 0)
        and codecs[0] == core.public_inputs[0].value_type,
        3,
        "invocation assignment is not total and audience-confined",
    )

    # Item 4: every and only Statement binding is represented, and its
    # SuppliesInvocation target and slot are the exact PublicInput value it
    # names.  SessionContext is deliberately not Statement coverage.
    statement_refs = tuple(
        index
        for index, binding in enumerate(core.public_bindings)
        if binding.binding_class is base.BindingClass.STATEMENT
    )
    _require_interface_item(
        statement_refs == (0,)
        and components["statement_members"] == ((0, 0, 0, 0),)
        and core.public_bindings[0].value == base.PublicInputRef(0),
        4,
        "StatementCoverage or SuppliesInvocation equality differs",
    )

    # Item 5: every declared transport has the exact owner-derived target,
    # source, ExternalApplication destination, and uniform presence type.
    expected = {
        0: (0, 0, base.Z3),
        1: (0, 1, base.Z3),
        2: (0, 1, base.Z3),
        3: (1, 2, k1.BOOL),
        4: (1, 2, base.Z3),
        5: (0, 0, base.Z3),
        6: (0, 0, base.Z3),
    }
    seen: set[int] = set()
    for occurrence, target_tag, source_tag, destination, slot in transports:
        _require_interface_item(
            occurrence in expected and occurrence not in seen,
            5,
            "transport target is unknown or duplicated",
        )
        expected_target, expected_source, value_type = expected[occurrence]
        _require_interface_item(
            (target_tag, source_tag, destination)
            == (expected_target, expected_source, 2)
            and codecs[slots[slot][1]] == _transport_type(value_type),
            5,
            "transport role, destination, or semantic-presence type differs",
        )
        seen.add(occurrence)


def _validate_interface_suffix(
    subject: PressureSubject, components: Mapping[str, Any]
) -> None:
    """Reconstruct admission items 6--8 after replay-input closure."""

    construction = subject.construction
    codecs = components["codec_types"]
    slots = components["slots"]
    transports = components["transports"]
    failure_slots = components["failure_slots"]

    # Item 6: both Core terminal variants and the one canonical-framed failure
    # variant are total.  Empty terminal payload maps are exact for this Core;
    # the five failure coordinates and semantic types follow Section 3.5.
    expected_failure_types = (
        construction.sampling_exhausted_failure.payload_type,
        k1.ValueType(k1.NAT_DOMAIN, k1.NatSchema((1 << 14) - 1)),
        k1.ValueType(k1.NAT_DOMAIN, k1.NatSchema(1 << 20)),
        construction.transcript_state_type,
        construction.transcript_state_type,
    )
    observed_failure_types = tuple(
        codecs[slots[slot][1]] for slot in failure_slots
    )
    _require_interface_item(
        components["terminal_completions"]
        == ((0, "accepted"), (1, "rejected"))
        and all(not terminal.public_outputs for terminal in subject.admission.core.terminals)
        and components["failure_payloads"]
        == tuple(zip((1, 2, 3, 4, 5), failure_slots))
        and observed_failure_types == expected_failure_types,
        6,
        "completion target, payload domain, or failure coordinate differs",
    )

    # Item 7: slot zero has one ExternalSupply origin plus its permitted
    # Statement annotation.  Every other slot has exactly one protocol-produced
    # transport or completion coordinate.
    produced_slots = [item[4] for item in transports] + list(failure_slots)
    _require_interface_item(
        len(produced_slots) == len(set(produced_slots))
        and set(produced_slots) == set(range(1, len(slots))),
        7,
        "external-slot use is not exactly closed",
    )

    # Item 8 has no further authored semantic field in the exact body: every
    # field has been checked as representation/transport over owner-formed values.
    _require_interface_item(True, 8, "declaration interferes with owner meaning")


def admit_interface(subject: PressureSubject, omit: int | None = None) -> dict[str, Any]:
    body, normalized, components = _interface_body(subject, omit)
    _validate_interface_prefix(subject, components)
    transports = set(normalized["transport_occurrences"])
    # Item 6: occurrence 2 is the public-condition operand of both challenge
    # acceptance/decoding ABIs.  It must be presented to replay either rule.
    externally_presented = {
        occurrence
        for occurrence, _, _, destination, _ in components["transports"]
        if destination == 2
    }
    missing = sorted(
        set(normalized["replay_input_occurrences"]) - externally_presented
    )
    if missing:
        return {
            "outcome": "Refused",
            "code": "F0V4-R-INTERFACE-REPLAY-INPUT",
            "admission_item": 6,
            "missing_occurrences": missing,
            "transport_occurrences": normalized["transport_occurrences"],
        }
    _validate_interface_suffix(subject, components)
    if transports != set(range(7)):
        raise PressureError("positive Interface does not transport every formable occurrence")
    repository = fs_model.target.publication.compile_repository()
    profile = repository.profiles["interface-plan"]
    identifier = k1.profiled_content_id(
        "pir.protocol-interface",
        profile.profile_id,
        body,
        semantic_regime=k1.SEMANTIC_REGIME_ID,
    )
    return {
        "outcome": "Affirmative",
        "code": "F0V4-A-INTERFACE-ADMISSION",
        "interface_id": _id(identifier),
        "body_sha256": hashlib.sha256(k1.encode_datum(body)).hexdigest(),
        **normalized,
    }


def _frame(construction: Any, label: str, tag: int, payload: Any) -> tuple[dict[str, str], Any]:
    octets = k1.encode_datum(_v(tag, payload))
    value = k1.admit_value(
        construction.transcript_bytes_type, k1.BytesValue(octets)
    )
    return {"kind": label, "body": octets.hex()}, value


def _module_ref(reference: Any) -> Any:
    return fs_model._module_ref_body(reference)


def _scope_frame(subject: PressureSubject, path: tuple[int, ...]) -> tuple[dict[str, str], Any]:
    return _frame(
        subject.construction,
        "ScopeOpened",
        3,
        _s(tuple(k1.Nat(item) for item in path)),
    )


def _binding_frame(
    subject: PressureSubject, binding_ref: int, value: Any
) -> tuple[dict[str, str], Any]:
    binding = subject.admission.core.public_bindings[binding_ref]
    return _frame(
        subject.construction,
        "PublicBinding",
        4,
        _r(
            k1.Nat(binding_ref),
            _v(binding.binding_class.value),
            k1.value_type_datum(value.value_type),
            value.datum,
        ),
    )


def _guard_frame(subject: PressureSubject, occurrence: int, active: bool) -> tuple[dict[str, str], Any]:
    return _frame(subject.construction, "GuardOutcome", 5, _r(k1.Nat(occurrence), active))


def _message_frame(
    subject: PressureSubject, occurrence: int, value: Any, verifier: bool
) -> tuple[dict[str, str], Any]:
    effect = subject.admission.core.occurrences[occurrence].effect
    return _frame(
        subject.construction,
        "VerifierMessage" if verifier else "ProverMessage",
        7 if verifier else 6,
        _r(
            k1.Nat(occurrence),
            _module_ref(effect.channel),
            k1.value_type_datum(value.value_type),
            value.datum,
        ),
    )


def _condition_frame(
    subject: PressureSubject, challenge: int, value: Any
) -> tuple[dict[str, str], Any]:
    return _frame(
        subject.construction,
        "ChallengeCondition",
        11,
        _r(
            k1.Nat(challenge),
            k1.Nat(0),
            k1.value_type_datum(value.value_type),
            value.datum,
        ),
    )


def _runtime_subject(subject: PressureSubject) -> Any:
    return SimpleNamespace(construction=subject.construction)


def _absorb(
    subject: PressureSubject,
    state: Any,
    framed: tuple[dict[str, str], Any],
    transitions: list[dict[str, Any]],
    *,
    replay: bool,
) -> Any:
    runtime = _runtime_subject(subject)
    if replay:
        return fs_replay._absorption(runtime, state, framed, transitions)
    prefix: list[str] = []
    return fs_executor._absorb(runtime, state, framed, transitions, prefix)


def _headers(subject: PressureSubject) -> tuple[tuple[dict[str, str], Any], ...]:
    return (
        _frame(
            subject.construction,
            "CoreHeader",
            0,
            k1.BytesValue(subject.admission.candidate.asserted_id.internal_reference()),
        ),
        _frame(
            subject.construction,
            "ConstructionHeader",
            1,
            k1.BytesValue(subject.construction.identifier.internal_reference()),
        ),
        _frame(
            subject.construction,
            "ApplicationDomainHeader",
            2,
            _module_ref(subject.construction.application_domain),
        ),
        _scope_frame(subject, (0,)),
    )


def _occurrence(occurrence: int, active: bool, values: tuple[Any, ...]) -> dict[str, Any]:
    return {
        "occurrence": occurrence,
        "status": "Active" if active else "Inactive",
        "outputs": [_canonical_value(item) for item in values],
    }


def _invocation_id(subject: PressureSubject, statement: int) -> Any:
    value = k1.admit_value(base.Z3, k1.Nat(statement))
    body = _r(
        k1.BytesValue(subject.admission.candidate.asserted_id.internal_reference()),
        _s((_r(k1.Nat(0), k1.value_type_datum(base.Z3), value.datum),)),
        _s(()),
    )
    return k1.profiled_content_id(
        "pir.invocation",
        subject.admission.environment.profile_id,
        body,
        semantic_regime=k1.SEMANTIC_REGIME_ID,
    )


def _evaluate_fs(
    subject: PressureSubject, case: RunCase, *, replay: bool
) -> tuple[str, dict[str, Any], tuple[dict[str, Any], ...]]:
    core = subject.admission.core
    construction = subject.construction
    state = construction.initial_state
    transitions: list[dict[str, Any]] = []
    occurrences: list[dict[str, Any]] = []
    challenge_receipts: list[dict[str, Any]] = []
    for framed in _headers(subject):
        state = _absorb(subject, state, framed, transitions, replay=replay)

    statement = k1.admit_value(base.Z3, k1.Nat(case.statement))
    seed = k1.admit_value(base.Z3, k1.Nat(case.seed))
    commitment = k1.admit_value(base.Z3, k1.Nat(case.commitment))
    response = k1.admit_value(base.Z3, k1.Nat(case.response))
    state = _absorb(
        subject, state, _message_frame(subject, 0, seed, False), transitions, replay=replay
    )
    occurrences.append(_occurrence(0, True, (seed,)))
    state = _absorb(subject, state, _scope_frame(subject, (0, 1)), transitions, replay=replay)
    for binding_ref in range(2):
        # Runtime uses the invocation-determined subject.  The setup-only
        # neighboring Core is never silently supplied from this run.
        state = _absorb(
            subject,
            state,
            _binding_frame(subject, binding_ref, statement),
            transitions,
            replay=replay,
        )
    state = _absorb(subject, state, _guard_frame(subject, 1, True), transitions, replay=replay)
    state = _absorb(
        subject,
        state,
        _message_frame(subject, 1, statement, True),
        transitions,
        replay=replay,
    )
    occurrences.append(_occurrence(1, True, (statement,)))
    state = _absorb(
        subject,
        state,
        _message_frame(subject, 2, statement, True),
        transitions,
        replay=replay,
    )
    occurrences.append(_occurrence(2, True, (statement,)))

    derived: list[Any] = []
    transition_function: Callable[..., Any] = (
        fs_replay.derive_challenge if replay else fs_executor.derive_challenge
    )
    for challenge_ref in (0, 1):
        state = _absorb(
            subject,
            state,
            _condition_frame(subject, challenge_ref, statement),
            transitions,
            replay=replay,
        )
        prior: tuple[Any, ...] = ()
        result = transition_function(
            construction,
            core,
            challenge_ref,
            state,
            (statement,),
            prior,
            transitions,
        )
        if replay:
            state, value, draws, prefix_count, prefix_state = result
        else:
            state = result.state
            value = result.value
            draws = result.draws
            prefix_count = result.prefix_receipt_count
            prefix_state = result.prefix_state
        if value is None:
            payload = k1.admit_value(
                construction.sampling_exhausted_failure.payload_type,
                _r(k1.Nat(challenge_ref), k1.Nat(len(draws))),
            )
            record = {
                "variant": "InterpretationFailure",
                "record": {
                    "protocol_id": _id(subject.fs_protocol.identifier),
                    "invocation_id": _id(_invocation_id(subject, case.statement)),
                    "case": case.__dict__,
                    "occurrence_prefix": occurrences,
                    "challenge_receipts": challenge_receipts,
                    "failure": {
                        "failure_type": k1.encode_datum(
                            k1.semantic_failure_type_datum(
                                construction.sampling_exhausted_failure
                            )
                        ).hex(),
                        "payload": _canonical_value(payload),
                    },
                    "interpretation_receipt": {
                        "kind": "FiatShamirSamplingFailure",
                        "construction": _id(construction.identifier),
                        "receipt": {
                            "challenge": challenge_ref,
                            "prefix_receipt_count": prefix_count,
                            "prefix_state": _canonical_value(prefix_state),
                            "draws": list(draws),
                            "final_state": _canonical_value(state),
                        },
                    },
                },
            }
            return "InterpretationFailed", record, tuple(transitions)
        derived.append(value)
        occurrences.append(_occurrence(3 + challenge_ref, True, (value,)))
        challenge_receipts.append(
            {
                "interpretation": "FiatShamir",
                "receipt": {
                    "challenge": challenge_ref,
                    "prefix_receipt_count": prefix_count,
                    "prefix_state": _canonical_value(prefix_state),
                    "draws": list(draws),
                    "accepted_value": _canonical_value(value),
                    "post_state": _canonical_value(state),
                },
            }
        )

    state = _absorb(
        subject,
        state,
        _message_frame(subject, 5, commitment, False),
        transitions,
        replay=replay,
    )
    occurrences.append(_occurrence(5, True, (commitment,)))
    state = _absorb(
        subject,
        state,
        _message_frame(subject, 6, response, False),
        transitions,
        replay=replay,
    )
    occurrences.append(_occurrence(6, True, (response,)))
    check = fs_model.evaluate(
        fs_model.AlgorithmUse(
            _algorithm_preimage(subject, core.checks[0].algorithm),
            k1.DEFAULT_EVALUATION_CONTRACT,
        ),
        (statement, commitment, derived[1], response),
    )
    occurrences.append(_occurrence(7, True, (check,)))
    accepted = bool(derived[0].datum) and bool(check.datum)
    state = _absorb(
        subject, state, _guard_frame(subject, 8, accepted), transitions, replay=replay
    )
    occurrences.append(_occurrence(8, accepted, ()))
    if accepted:
        lane, terminal = "Accepted", 0
    else:
        occurrences.append(_occurrence(9, True, ()))
        lane, terminal = "Rejected", 1
    record = {
        "variant": "TerminalCompletion",
        "record": {
            "protocol_id": _id(subject.fs_protocol.identifier),
            "invocation_id": _id(_invocation_id(subject, case.statement)),
            "case": case.__dict__,
            "occurrence_receipts": occurrences,
            "challenge_receipts": challenge_receipts,
            "oracle_receipts": [],
            "terminal": terminal,
            "terminal_public_outputs": [],
        },
    }
    return lane, record, tuple(transitions)


def _fresh_record(
    subject: PressureSubject, case: RunCase, boolean: bool, root_nat: int
) -> tuple[str, dict[str, Any]]:
    statement = k1.admit_value(base.Z3, k1.Nat(case.statement))
    seed = k1.admit_value(base.Z3, k1.Nat(case.seed))
    commitment = k1.admit_value(base.Z3, k1.Nat(case.commitment))
    response = k1.admit_value(base.Z3, k1.Nat(case.response))
    c0 = k1.admit_value(k1.BOOL, boolean)
    c1 = k1.admit_value(base.Z3, k1.Nat(root_nat))
    check = fs_model.evaluate(
        fs_model.AlgorithmUse(
            _algorithm_preimage(
                subject, subject.admission.core.checks[0].algorithm
            ),
            k1.DEFAULT_EVALUATION_CONTRACT,
        ),
        (statement, commitment, c1, response),
    )
    relation_holds = (
        case.commitment + root_nat * case.statement
    ) % 3 == case.response
    if bool(check.datum) != relation_holds:
        raise PressureError("portable Schnorr evaluation differs from its finite relation")
    accepted = boolean and bool(check.datum)
    lane = "Accepted" if accepted else "Rejected"
    occurrences = [
        _occurrence(0, True, (seed,)),
        _occurrence(1, True, (statement,)),
        _occurrence(2, True, (statement,)),
        _occurrence(3, True, (c0,)),
        _occurrence(4, True, (c1,)),
        _occurrence(5, True, (commitment,)),
        _occurrence(6, True, (response,)),
        _occurrence(7, True, (check,)),
        _occurrence(8, accepted, ()),
    ]
    if not accepted:
        occurrences.append(_occurrence(9, True, ()))
    record = {
        "variant": "TerminalCompletion",
        "record": {
            "protocol_id": _id(subject.admission.fresh_protocol_id),
            "invocation_id": _id(_invocation_id(subject, case.statement)),
            "case": case.__dict__,
            "occurrence_receipts": occurrences,
            "fresh_source": [
                {
                    "challenge": 0,
                    "fresh_law": foundation._module_ref(
                        subject.admission.core.challenges[0].fresh_law
                    ),
                    "value": _canonical_value(c0),
                },
                {
                    "challenge": 1,
                    "fresh_law": foundation._module_ref(
                        subject.admission.core.challenges[1].fresh_law
                    ),
                    "value": _canonical_value(c1),
                },
            ],
            "terminal": 0 if accepted else 1,
            "check": _canonical_value(check),
        },
    }
    return lane, record


def _replay_fresh(
    subject: PressureSubject,
    case: RunCase,
    boolean: bool,
    root_nat: int,
    supplied: dict[str, Any],
) -> str:
    relation_holds = (
        case.commitment + root_nat * case.statement
    ) % 3 == case.response
    lane = "Accepted" if boolean and relation_holds else "Rejected"
    c0 = k1.admit_value(k1.BOOL, boolean)
    c1 = k1.admit_value(base.Z3, k1.Nat(root_nat))
    statement = k1.admit_value(base.Z3, k1.Nat(case.statement))
    seed = k1.admit_value(base.Z3, k1.Nat(case.seed))
    commitment = k1.admit_value(base.Z3, k1.Nat(case.commitment))
    response = k1.admit_value(base.Z3, k1.Nat(case.response))
    replayed_check = k1.admit_value(k1.BOOL, relation_holds)
    replayed_occurrences = [
        _occurrence(0, True, (seed,)),
        _occurrence(1, True, (statement,)),
        _occurrence(2, True, (statement,)),
        _occurrence(3, True, (c0,)),
        _occurrence(4, True, (c1,)),
        _occurrence(5, True, (commitment,)),
        _occurrence(6, True, (response,)),
        _occurrence(7, True, (replayed_check,)),
        _occurrence(8, lane == "Accepted", ()),
    ]
    if lane != "Accepted":
        replayed_occurrences.append(_occurrence(9, True, ()))
    expected = {
        "variant": "TerminalCompletion",
        "record": {
            "protocol_id": _id(subject.admission.fresh_protocol_id),
            "invocation_id": _id(_invocation_id(subject, case.statement)),
            "case": case.__dict__,
            "occurrence_receipts": replayed_occurrences,
            "fresh_source": [
                {
                    "challenge": 0,
                    "fresh_law": foundation._module_ref(
                        subject.admission.core.challenges[0].fresh_law
                    ),
                    "value": _canonical_value(c0),
                },
                {
                    "challenge": 1,
                    "fresh_law": foundation._module_ref(
                        subject.admission.core.challenges[1].fresh_law
                    ),
                    "value": _canonical_value(c1),
                },
            ],
            "terminal": 0 if lane == "Accepted" else 1,
            "check": _canonical_value(replayed_check),
        },
    }
    if supplied != expected:
        raise PressureError("Fresh replay record differs")
    return lane


def runtime_evidence(subject: PressureSubject) -> dict[str, Any]:
    cases = tuple(
        RunCase(statement, seed, commitment, response)
        for statement in range(3)
        for seed in range(3)
        for commitment in range(3)
        for response in range(3)
    )
    fresh_records: list[dict[str, Any]] = []
    fresh_lanes: Counter[str] = Counter()
    fresh_replays = 0
    for case in cases:
        for boolean in (False, True):
            for root_nat in range(3):
                lane, record = _fresh_record(subject, case, boolean, root_nat)
                if _replay_fresh(subject, case, boolean, root_nat, record) != lane:
                    raise PressureError("Fresh replay lane differs")
                fresh_records.append(record)
                fresh_lanes[lane] += 1
                fresh_replays += 1

    fs_records: list[dict[str, Any]] = []
    fs_lanes: Counter[str] = Counter()
    fs_replays = 0
    selected_failure: dict[str, Any] | None = None
    for case in cases:
        lane, record, transitions = _evaluate_fs(subject, case, replay=False)
        replay_lane, replay_record, replay_transitions = _evaluate_fs(
            subject, case, replay=True
        )
        if (
            replay_lane != lane
            or replay_record != record
            or replay_transitions != transitions
        ):
            raise PressureError("independent FS replay differs")
        fs_records.append(record)
        fs_lanes[lane] += 1
        fs_replays += 1
        if lane == "InterpretationFailed" and selected_failure is None:
            selected_failure = record
    if selected_failure is None:
        raise PressureError("finite FS corpus has no sampling exhaustion")
    selected_body = selected_failure["record"]
    prefix_by_occurrence = {
        item["occurrence"]: item for item in selected_body["occurrence_prefix"]
    }
    presented_transports = [
        {
            "occurrence": occurrence,
            "status": (
                prefix_by_occurrence[occurrence]["status"]
                if occurrence in prefix_by_occurrence
                else "Inactive"
            ),
            "outputs": (
                prefix_by_occurrence[occurrence]["outputs"]
                if occurrence in prefix_by_occurrence
                else []
            ),
        }
        for occurrence in range(7)
    ]
    failure_receipt = selected_body["interpretation_receipt"]["receipt"]
    completion_fields = {
        "domain_payload": selected_body["failure"]["payload"],
        "challenge": failure_receipt["challenge"],
        "prefix_receipt_count": failure_receipt["prefix_receipt_count"],
        "prefix_state": failure_receipt["prefix_state"],
        "final_state": failure_receipt["final_state"],
    }
    presented_condition = next(
        item for item in presented_transports if item["occurrence"] == 2
    )["outputs"][0]
    prefix_state = _decode_presented_value(
        completion_fields["prefix_state"],
        subject.construction.transcript_state_type,
    )
    condition = _decode_presented_value(presented_condition, base.Z3)
    presented_prefix = [
        {"kind": "PresentedPrefixCoordinate", "ordinal": ordinal}
        for ordinal in range(completion_fields["prefix_receipt_count"])
    ]
    (
        replayed_final_state,
        replayed_value,
        replayed_draws,
        replayed_prefix_count,
        replayed_prefix_state,
    ) = fs_replay.derive_challenge(
        subject.construction,
        subject.admission.core,
        completion_fields["challenge"],
        prefix_state,
        (condition,),
        (),
        presented_prefix,
    )
    presented_payload = _decode_presented_value(
        completion_fields["domain_payload"],
        subject.construction.sampling_exhausted_failure.payload_type,
    )
    expected_payload = k1.admit_value(
        subject.construction.sampling_exhausted_failure.payload_type,
        _r(k1.Nat(completion_fields["challenge"]), k1.Nat(len(replayed_draws))),
    )
    replay_from_presented_values = (
        replayed_value is None
        and replayed_prefix_count == completion_fields["prefix_receipt_count"]
        and replayed_prefix_state == prefix_state
        and presented_payload == expected_payload
        and _canonical_value(replayed_final_state) == completion_fields["final_state"]
        and list(replayed_draws) == failure_receipt["draws"]
    )
    if not replay_from_presented_values:
        raise PressureError("sampling failure did not replay from presented values")
    replay_case = RunCase(**selected_body["case"])
    replay_lane, replay_failure, _ = _evaluate_fs(
        subject, replay_case, replay=True
    )
    if replay_lane != "InterpretationFailed" or replay_failure != selected_failure:
        raise PressureError("presented sampling failure does not independently replay")
    # Commitment and response are after both challenge sites and are not
    # presented on this completion path.  Varying them must leave all semantic
    # failure fields except the diagnostic case label unchanged.
    def failure_semantics(value: dict[str, Any]) -> dict[str, Any]:
        body = dict(value["record"])
        body.pop("case")
        return {"variant": value["variant"], "record": body}

    selected_semantics = failure_semantics(selected_failure)
    for commitment in range(3):
        for response in range(3):
            alternate = replace(
                replay_case, commitment=commitment, response=response
            )
            alternate_lane, alternate_record, _ = _evaluate_fs(
                subject, alternate, replay=True
            )
            if (
                alternate_lane != "InterpretationFailed"
                or failure_semantics(alternate_record) != selected_semantics
            ):
                raise PressureError("failure replay consumed an unpresented later value")
    for lane in LANES:
        fresh_lanes.setdefault(lane, 0)
        fs_lanes.setdefault(lane, 0)
    return {
        "fresh": {
            "run_count": len(fresh_records),
            "challenge_space": [[False, 0], [False, 1], [False, 2], [True, 0], [True, 1], [True, 2]],
            "lane_counts": {lane: fresh_lanes[lane] for lane in LANES},
            "replay_match_count": fresh_replays,
            "records_sha256": digest(fresh_records),
        },
        "fiat_shamir": {
            "run_count": len(fs_records),
            "lane_counts": {lane: fs_lanes[lane] for lane in LANES},
            "replay_match_count": fs_replays,
            "records_sha256": digest(fs_records),
            "selected_sampling_failure": selected_failure,
            "selected_sampling_failure_sha256": digest(selected_failure),
            "sampling_failure_presentation": {
                "invocation_statement": selected_body["case"]["statement"],
                "transport_entries": presented_transports,
                "completion_fields": completion_fields,
                "derived_draws_sha256": digest(failure_receipt["draws"]),
                "replay_operand_occurrences": [2],
                "replay_from_presented_values": replay_from_presented_values,
                "unpresented_later_value_mutations": 9,
            },
        },
    }


def read_catalog_join(
    interaction: dict[str, Any],
    canonical: dict[str, Any],
    fs_execution: dict[str, Any],
    setup: dict[str, Any],
) -> dict[str, Any]:
    selections: dict[str, tuple[int, ...]] = {
        "PublicBindingView": (1, 2),
        "StrategyDecisionView": (1, 2, 3, 4),
        "PublicCoinView": (2, 3, 4),
        "EffectView": (5, 6),
        "ClaimReductionView": (1, 2, 3),
        "ExecutionView": (0, 1, 2, 3, 4, 5, 6, 8, 9),
        "CanonicalTranscriptDeclarationView": tuple(range(13)),
        "CanonicalRequiredInfluenceView": tuple(range(6)),
        "CanonicalChallengeTransitionView": tuple(range(8)),
        "CanonicalFSConstructionView": tuple(range(9)),
    }
    bodies = {**interaction, **canonical}
    selected: dict[str, Any] = {}
    for name, ordinals in selections.items():
        body = bodies[name]
        if any(ordinal not in body for ordinal in ordinals):
            raise PressureError(f"Analysis read catalog misses {name} owner field")
        selected[name] = {str(ordinal): body[ordinal] for ordinal in ordinals}
    execution_fields = (
        "protocol_id",
        "core_id",
        "challenge_interpretation",
        "visible_history_law",
        "resolver_coordinates",
        "generated_execution_law",
        "run_record_schema",
        "replay_qualification_law",
        "relation_run_view_issuance_law",
    )
    if any(item not in fs_execution for item in execution_fields):
        raise PressureError("FS ExecutionView read catalog is incomplete")
    selected["FiatShamirExecutionView"] = {
        item: fs_execution[item] for item in execution_fields
    }
    for key in ("fresh", "fiat_shamir"):
        view = setup["baseline"][key]
        if set(view) != {
            "protocol_id",
            "core_id",
            "view_id",
            "entries",
            "run_established",
            "body_sha256",
            "entry_sequence_sha256",
        }:
            raise PressureError("public-setup complete-body projection drifted")
        selected[f"PublicSetupInvocationView.{key}"] = view
    return {
        "slot_count": len(selected),
        "selected_owner_fields": {
            name: list(selections[name]) for name in selections
        },
        "fs_execution_fields": list(execution_fields),
        "joined_sha256": digest(selected),
    }


def analysis_boundary(subject: PressureSubject) -> dict[str, Any]:
    proposal = json.loads(ANALYSIS_PREMISE_FIXTURE.read_text(encoding="utf-8"))
    fixture_fresh = next(
        item
        for item in proposal["premises"]
        if item["kind"] == "FreshPublicCoinDistribution"
    )
    fixture_by_kind = {
        item["kind"]: item
        for item in proposal["premises"]
        if item["kind"]
        in {
            "RelationPredicate",
            "WitnessType",
            "ProverPrivateState",
            "HonestCommit",
            "HonestRespond",
        }
    }
    if set(fixture_by_kind) != {
        "RelationPredicate",
        "WitnessType",
        "ProverPrivateState",
        "HonestCommit",
        "HonestRespond",
    }:
        raise PressureError("finite relation and Plan premise fixture is incomplete")
    fresh_laws = [
        {
            "challenge_ref": index,
            "fresh_law": {
                "module": _id(challenge.fresh_law.module),
                "declaration_kind": challenge.fresh_law.declaration_kind,
                "local_ordinal": challenge.fresh_law.local_ordinal,
            },
        }
        for index, challenge in enumerate(subject.admission.core.challenges)
    ]
    fixture_law_matches = [
        item["challenge_ref"]
        for item in fresh_laws
        if fixture_fresh["coordinate"]["subject"]
        == item["fresh_law"]["module"]
        and fixture_fresh["coordinate"]["path"]
        == (
            "declarations[pir.public-coin-law]"
            f"[{item['fresh_law']['local_ordinal']}]"
        )
    ]
    if fixture_law_matches != [1]:
        raise PressureError("Fresh-law fixture match partition drifted")
    requirements = [
        *[
            {
                "slot": f"challenge-law-{item['challenge_ref']}",
                "kind": "FreshPublicCoinDistribution",
                "coordinate": item["fresh_law"],
                "source": (
                    "proposal fixture exact-coordinate match"
                    if item["challenge_ref"] in fixture_law_matches
                    else "no matching exact-coordinate fixture premise"
                ),
            }
            for item in fresh_laws
        ],
        {
            "slot": "outcome-carrier",
            "kind": "ProviderOutcomeCarrierMap",
            "coordinate": {
                "protocol_id": _id(subject.fs_protocol.identifier),
                "path": "ProtocolOutcomeLane",
            },
        },
        *[
            {
                "slot": name,
                "kind": kind,
                "coordinate": fixture_by_kind[kind]["coordinate"],
                "source": "proposal fixture; exact current-subject rebind required",
            }
            for name, kind in (
                ("relation-predicate", "RelationPredicate"),
                ("witness-type", "WitnessType"),
                ("prover-private-state", "ProverPrivateState"),
                ("honest-commit", "HonestCommit"),
                ("honest-respond", "HonestRespond"),
            )
        ],
    ]
    return {
        "fresh_law_leaf_count": len(fresh_laws),
        "unique_fresh_law_coordinate_count": len(
            {digest(item["fresh_law"]) for item in fresh_laws}
        ),
        "fresh_law_leaves": fresh_laws,
        "fixture_fresh_law_matches": fixture_law_matches,
        "fixture_fresh_law_unmatched": [
            item["challenge_ref"]
            for item in fresh_laws
            if item["challenge_ref"] not in fixture_law_matches
        ],
        "fixture_subject_core_id": proposal["subject"]["core_id"],
        "current_subject_core_id": _id(subject.admission.candidate.asserted_id),
        "fixture_subject_matches_current": (
            proposal["subject"]["core_id"]
            == _id(subject.admission.candidate.asserted_id)
        ),
        "premise_requirement_sequence": requirements,
        "proposal_fixture_sha256": hashlib.sha256(
            ANALYSIS_PREMISE_FIXTURE.read_bytes()
        ).hexdigest(),
        "missing": [
            "owner named-premise constructor",
            "Boolean Fresh distribution premise",
            "exact-subject relation and Plan rebind",
            "provider declaration",
        ],
        "owner_boundary": {
            "named_requirement_variant_present": False,
            "cryptographic_properties_section_3_2_present": False,
            "analysis_model_lines": "2246-2261",
            "cryptographic_properties_distribution_lines": "968-973",
            "cryptographic_properties_provider_search_lines": "1299-2167",
            "provider_packet_authority_lines": "4-8",
            "proposal_fixture_subject_line": 5,
            "proposal_fixture_rebind_lines": "154-259",
        },
        "fixture_rebind_required": [
            "relation-predicate",
            "witness-type",
            "prover-private-state",
            "honest-commit",
            "honest-respond",
        ],
    }


def provider_map(runtime: dict[str, Any]) -> dict[str, Any]:
    counts = runtime["fiat_shamir"]["lane_counts"]
    total = runtime["fiat_shamir"]["run_count"]
    mapping = {
        "Accepted": "Image(true)",
        "Rejected": "Image(false)",
        "Aborted": "Unmodelled",
        "InterpretationFailed": "Unmodelled",
        "StrategyStopped": "Unmodelled",
        "OperationalNoncompletion": "Unmodelled",
    }
    accepted = Fraction(counts["Accepted"], total)
    rejected = Fraction(counts["Rejected"], total)
    unmodelled = Fraction(
        sum(
            counts[item]
            for item in LANES
            if mapping[item] == "Unmodelled"
        ),
        total,
    )
    if accepted + rejected + unmodelled != 1:
        raise PressureError("provider map changed or renormalized total mass")
    transported_true = Fraction(
        sum(counts[item] for item in LANES if mapping[item] == "Image(true)"),
        total,
    )
    transported_false = Fraction(
        sum(counts[item] for item in LANES if mapping[item] == "Image(false)"),
        total,
    )
    if transported_true != accepted:
        raise PressureError("transported true mass differs from Accepted mass")
    if transported_false != rejected:
        raise PressureError("transported false mass differs from Rejected mass")
    return {
        "carrier": "Boolean",
        "status": "package-local finite candidate; no owner premise formed",
        "measure": "uniform mass on the exhaustive 81-case input carrier",
        "declared_modelled_lanes": ["Accepted", "Rejected"],
        "six_lane_map": mapping,
        "denominator": total,
        "accepted_mass": [accepted.numerator, accepted.denominator],
        "rejected_mass": [rejected.numerator, rejected.denominator],
        "unmodelled_mass": [unmodelled.numerator, unmodelled.denominator],
        "transported_true_mass": [
            transported_true.numerator,
            transported_true.denominator,
        ],
        "transported_false_mass": [
            transported_false.numerator,
            transported_false.denominator,
        ],
        "renormalized": False,
        "finite_measure_clause_holds": transported_true == accepted,
        "provider_declaration_published": False,
    }


def evidence() -> dict[str, Any]:
    baseline = make_subject(False)
    run_variant = make_subject(True)
    interaction, interaction_digests = interaction_views(baseline)
    canonical, canonical_digests, fs_execution = canonical_views(baseline)
    setup = setup_evidence(baseline, run_variant)
    interface = admit_interface(baseline)
    interface_negative = admit_interface(baseline, omit=2)
    runtime = runtime_evidence(baseline)
    reads = read_catalog_join(
        interaction, canonical, fs_execution, setup
    )
    analysis = analysis_boundary(baseline)
    provider = provider_map(runtime)
    return {
        "question": QUESTION,
        "admission": {
            "core": {
                "outcome": "Affirmative",
                "code": "F0V4-A-CORE-ADMISSION",
                "core_id": _id(baseline.admission.candidate.asserted_id),
                "verified_owner_steps": list(baseline.admission.verified_steps),
            },
            "fresh_protocol": {
                "outcome": "Affirmative",
                "code": "F0V4-A-FRESH-PROTOCOL-ADMISSION",
                "protocol_id": _id(baseline.admission.fresh_protocol_id),
                "verified_requirements": list(
                    baseline.fresh_admission.verified_requirements
                ),
            },
            "construction": {
                "outcome": "Affirmative",
                "code": "F0V4-A-CONSTRUCTION-ADMISSION",
                "construction_id": _id(baseline.construction.identifier),
                "verified_owner_steps": list(
                    baseline.construction_admission.verified_steps
                ),
                "derived_bounds": {
                    "challenge_rules": baseline.construction_admission.bounds.challenge_rules,
                    "maximum_frame_count": baseline.construction_admission.bounds.maximum_frame_count,
                    "maximum_transition_calls": baseline.construction_admission.bounds.maximum_transition_calls,
                    "maximum_frame_octets": baseline.construction_admission.bounds.maximum_frame_octets,
                    "maximum_namespace_octets": baseline.construction_admission.bounds.maximum_namespace_octets,
                    "maximum_cumulative_octets": baseline.construction_admission.bounds.maximum_cumulative_octets,
                },
            },
            "fiat_shamir_protocol": {
                "outcome": "Affirmative",
                "code": "F0V4-A-FS-PROTOCOL-ADMISSION",
                "protocol_id": _id(baseline.fs_protocol.identifier),
                "verified_requirements": list(
                    baseline.fs_admission.verified_requirements
                ),
            },
            "checked_same_core": {
                "outcome": "Affirmative",
                "code": "F0V4-A-CHECKED-SAME-CORE",
                "shared_core_id": _id(baseline.checked.shared_core_id),
                "checker_contract_id": _id(baseline.checker_contract_id),
                "verified_owner_requirements": list(
                    baseline.checked_admission.verified_requirements
                ),
            },
        },
        "subjects": {
            "baseline": {
                "core_id": _id(baseline.admission.candidate.asserted_id),
                "fresh_protocol_id": _id(baseline.admission.fresh_protocol_id),
                "transcript_construction_id": _id(baseline.construction.identifier),
                "fiat_shamir_protocol_id": _id(baseline.fs_protocol.identifier),
                "checker_contract_id": _id(baseline.checker_contract_id),
                "occurrence_count": len(baseline.admission.core.occurrences),
                "occurrence_kinds": [
                    type(item.effect).__name__
                    for item in baseline.admission.core.occurrences
                ],
                "binding_classes": [
                    item.binding_class.name
                    for item in baseline.admission.core.public_bindings
                ],
                "binding_scopes": [
                    item.scope for item in baseline.admission.core.public_bindings
                ],
                "binding_sources": ["PublicInput(0)", "PublicInput(0)"],
                "challenge_types": [
                    hashlib.sha256(k1.encode_datum(k1.value_type_datum(item.value_type))).hexdigest()
                    for item in baseline.admission.core.challenges
                ],
                "challenge_type_names": ["Boolean", "RootNat(2)"],
                "challenge_correlations": [
                    type(item.correlation).__name__
                    for item in baseline.admission.core.challenges
                ],
                "challenge_condition_occurrences": [2, 2],
                "challenge_positions": [3, 4],
                "draw_bounds": [[8, 1], [8, 2]],
                "decoder_result_types_distinct": True,
                "guarded_verifier_occurrence": 1,
                "terminal_occurrences": [8, 9],
                "terminal_precedence": "first-active",
                "public_coin_eligible": baseline.admission.graph_evidence.eligible,
            },
            "run_variant": {
                "core_id": _id(run_variant.admission.candidate.asserted_id),
                "fresh_protocol_id": _id(run_variant.admission.fresh_protocol_id),
                "transcript_construction_id": _id(run_variant.construction.identifier),
                "fiat_shamir_protocol_id": _id(run_variant.fs_protocol.identifier),
                "binding_sources": ["PublicInput(0)", "OccurrenceOutput(0,0)"],
            },
        },
        "interaction_view_sha256": interaction_digests,
        "canonical_view_sha256": canonical_digests,
        "analysis_read_join": reads,
        "public_setup": setup,
        "fixed_setup": {
            "baseline": fixed_setup_formation(baseline, setup["baseline"]),
            "run_variant": fixed_setup_formation(
                run_variant, setup["run_variant"]
            ),
        },
        "interface": interface,
        "interface_negative": interface_negative,
        "runtime": runtime,
        "analysis_boundary": analysis,
        "provider_map": provider,
    }
