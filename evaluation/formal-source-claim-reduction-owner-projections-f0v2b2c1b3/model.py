"""Typed owner evaluator for the F0-V2B2C1B3 claim/reduction slice.

This is temporary research code.  It extends the canonical-byte owner
substrate through claims, reductions, and joint/shared Challenges.  It is not
the published PIR evaluator and it executes neither a reduction nor a claim
theorem.
"""

from __future__ import annotations

from dataclasses import dataclass, replace
import hashlib
import importlib.util
from pathlib import Path
import sys
from types import MappingProxyType, ModuleType
from typing import Any, Mapping


ROOT = Path(__file__).resolve().parents[2]
PREDECESSOR_MODEL = (
    ROOT
    / "evaluation"
    / "formal-source-oracle-owner-projections-f0v2b2c1b2"
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


prior = _load("_zkc_f0v2b2c1b3_predecessor", PREDECESSOR_MODEL)
foundation = prior.foundation
base = prior.base
b2c0 = prior.b2c0
b2b = prior.b2b
codec = prior.codec
k1 = prior.k1
VIEW_SCHEMAS = prior.VIEW_SCHEMAS

EVALUATOR_FINGERPRINT = hashlib.sha256(
    b"zkc-f0-v2b2c1b3-claim-reduction-owner-evaluator-v0"
).digest()
MAX_LOCAL_ITEMS = 1 << 14


class FamilyFailure(ValueError):
    """Stable fail-closed result from the bounded B2C1B3 evaluator."""

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


@dataclass(frozen=True)
class InitialClaimSource:
    binding: int


@dataclass(frozen=True)
class ReductionOutputClaimSource:
    reduction: int
    output_ordinal: int


@dataclass(frozen=True)
class ClaimDecl:
    contract: object
    scope: int
    usage: object
    source: object


@dataclass(frozen=True)
class ReductionPublicationRequirement:
    publication: int
    next_challenge: int | None


@dataclass(frozen=True)
class ReductionDecl:
    contract: object
    scope: int
    input_claims: tuple[int, ...]
    side_inputs: tuple[object, ...]
    required_challenges: tuple[int, ...]
    required_publications: tuple[ReductionPublicationRequirement, ...]
    output_contracts: tuple[object, ...]


@dataclass(frozen=True)
class ApplyReductionEffect:
    reduction: int


def _fail(outcome: str, code: str, detail: str) -> None:
    raise FamilyFailure(outcome, code, detail)


def _record(*values: object) -> object:
    return k1.DatumRecord(tuple((index, value) for index, value in enumerate(values)))


def _seq(values: tuple[object, ...]) -> object:
    return k1.DatumSeq(values)


def _variant(case: int, payload: object = k1.UNIT) -> object:
    return k1.DatumVariant(case, payload)


def _claim_datum(claim: object) -> object:
    if type(claim) is not ClaimDecl:
        raise k1.ModelError("claim has another exact carrier")
    if type(claim.source) is InitialClaimSource:
        source = _variant(0, k1.Nat(claim.source.binding))
    elif type(claim.source) is ReductionOutputClaimSource:
        source = _variant(
            1,
            _record(
                k1.Nat(claim.source.reduction),
                k1.Nat(claim.source.output_ordinal),
            ),
        )
    else:
        raise k1.ModelError("claim source has another exact carrier")
    return _record(
        base.module_declaration_ref_datum(claim.contract),
        k1.Nat(claim.scope),
        _variant(claim.usage.value),
        source,
    )


def _optional_challenge_datum(challenge: int | None) -> object:
    return _variant(0) if challenge is None else _variant(1, k1.Nat(challenge))


def _reduction_datum(reduction: object) -> object:
    if type(reduction) is not ReductionDecl:
        raise k1.ModelError("reduction has another exact carrier")
    return _record(
        base.module_declaration_ref_datum(reduction.contract),
        k1.Nat(reduction.scope),
        _seq(tuple(k1.Nat(item) for item in reduction.input_claims)),
        _seq(tuple(base.value_ref_datum(item) for item in reduction.side_inputs)),
        _seq(tuple(k1.Nat(item) for item in reduction.required_challenges)),
        _seq(
            tuple(
                _record(
                    k1.Nat(item.publication),
                    _optional_challenge_datum(item.next_challenge),
                )
                for item in reduction.required_publications
            )
        ),
        _seq(
            tuple(
                base.module_declaration_ref_datum(item)
                for item in reduction.output_contracts
            )
        ),
    )


def _effect_datum(effect: object) -> object:
    if type(effect) is base.ProverMessageEffect:
        return foundation._effect_datum(effect)
    if type(effect) is base.ChallengeEffect:
        return _variant(2, k1.Nat(effect.challenge))
    if type(effect) is ApplyReductionEffect:
        return _variant(4, k1.Nat(effect.reduction))
    if type(effect) is base.TerminalEffect:
        return _variant(5, k1.Nat(effect.terminal))
    raise k1.ModelError("effect belongs to another constructor slice")


def core_domain_datum(core: object) -> object:
    if type(core) is not base.InteractiveCore:
        raise k1.ModelError("Core has another carrier")
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
        _seq(tuple(_claim_datum(item) for item in core.claims)),
        _seq(tuple(_reduction_datum(item) for item in core.reductions)),
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


def _decode_challenge(value: object) -> object:
    fields = b2c0._record(value, tuple(range(7)), "Challenge")
    correlation_case, correlation_payload = b2c0._variant(
        fields[4], (0, 1), "coin correlation"
    )
    if correlation_case == 0:
        b2c0._unit(correlation_payload, "independent correlation")
        correlation: object = base.IndependentCorrelation()
    else:
        group, index, prior = b2c0._record(
            correlation_payload, (0, 1, 2), "joint correlation"
        )
        correlation = base.JointCorrelation(
            b2c0._decode_module_ref(group),
            b2c0._nat(index, "joint index"),
            tuple(
                b2c0._nat(item, "prior joint member")
                for item in b2c0._sequence(prior, "prior joint members")
            ),
        )
    use_case, use_payload = b2c0._variant(fields[5], (0, 1), "reduction use")
    if use_case == 0:
        b2c0._unit(use_payload, "exclusive reduction use")
        reduction_use: object = base.ExclusiveReductionUse()
    else:
        reduction_use = base.SharedReductionUse(b2c0._decode_module_ref(use_payload))
    return base.ChallengeDecl(
        b2c0._nat(fields[0], "challenge scope"),
        b2c0._decode_value_type(fields[1]),
        b2c0._decode_module_ref(fields[2]),
        b2c0._decode_module_ref(fields[3]),
        correlation,
        reduction_use,
        tuple(
            b2c0._decode_value_ref(item)
            for item in b2c0._sequence(fields[6], "challenge conditions")
        ),
    )


def _decode_claim(value: object) -> ClaimDecl:
    contract, scope, usage, source = b2c0._record(value, (0, 1, 2, 3), "claim")
    usage_case, usage_payload = b2c0._variant(usage, (0, 1), "claim usage")
    b2c0._unit(usage_payload, "claim usage payload")
    source_case, source_payload = b2c0._variant(source, (0, 1), "claim source")
    if source_case == 0:
        decoded_source: object = InitialClaimSource(
            b2c0._nat(source_payload, "claim source binding")
        )
    else:
        reduction, output = b2c0._record(
            source_payload, (0, 1), "reduction-output claim source"
        )
        decoded_source = ReductionOutputClaimSource(
            b2c0._nat(reduction, "source reduction"),
            b2c0._nat(output, "source output ordinal"),
        )
    return ClaimDecl(
        b2c0._decode_module_ref(contract),
        b2c0._nat(scope, "claim scope"),
        base.ClaimUsage(usage_case),
        decoded_source,
    )


def _decode_reduction(value: object) -> ReductionDecl:
    fields = b2c0._record(value, tuple(range(7)), "reduction")
    publications: list[ReductionPublicationRequirement] = []
    for item in b2c0._sequence(fields[5], "required publications"):
        publication, next_challenge = b2c0._record(
            item, (0, 1), "publication requirement"
        )
        next_case, next_payload = b2c0._variant(
            next_challenge, (0, 1), "next challenge"
        )
        if next_case == 0:
            b2c0._unit(next_payload, "absent next challenge")
        publications.append(
            ReductionPublicationRequirement(
                b2c0._nat(publication, "publication occurrence"),
                None if next_case == 0 else b2c0._nat(next_payload, "next challenge"),
            )
        )
    return ReductionDecl(
        b2c0._decode_module_ref(fields[0]),
        b2c0._nat(fields[1], "reduction scope"),
        tuple(
            b2c0._nat(item, "input claim")
            for item in b2c0._sequence(fields[2], "input claims")
        ),
        tuple(
            b2c0._decode_value_ref(item)
            for item in b2c0._sequence(fields[3], "side inputs")
        ),
        tuple(
            b2c0._nat(item, "required challenge")
            for item in b2c0._sequence(fields[4], "required challenges")
        ),
        tuple(publications),
        tuple(
            b2c0._decode_module_ref(item)
            for item in b2c0._sequence(fields[6], "output contracts")
        ),
    )


def _decode_terminal(value: object) -> object:
    verdict, outputs, checks, dispositions = b2c0._record(
        value, (0, 1, 2, 3), "terminal"
    )
    verdict_case, verdict_payload = b2c0._variant(
        verdict, (0, 1, 2), "terminal verdict"
    )
    b2c0._unit(verdict_payload, "terminal verdict payload")
    if b2c0._sequence(checks, "terminal checks"):
        _fail(
            "Unsupported",
            "F0V2B2C1B3-U-CHECKS",
            "Check-backed terminal behavior belongs to another slice",
        )
    decoded_dispositions: list[object] = []
    for item in b2c0._sequence(dispositions, "terminal dispositions"):
        claim, disposition = b2c0._record(item, (0, 1), "claim disposition")
        disposition_case, payload = b2c0._variant(
            disposition, (0, 1), "claim disposition"
        )
        b2c0._unit(payload, "claim disposition payload")
        decoded_dispositions.append(
            base.ClaimDispositionEntry(
                b2c0._nat(claim, "disposed claim"),
                base.ClaimDisposition(disposition_case),
            )
        )
    return base.TerminalDecl(
        base.TerminalVerdict(verdict_case),
        tuple(
            b2c0._decode_value_ref(item)
            for item in b2c0._sequence(outputs, "terminal outputs")
        ),
        (),
        tuple(decoded_dispositions),
    )


def _decode_effect(value: object) -> object:
    case, payload = b2c0._variant(value, tuple(range(8)), "Core effect")
    if case == 0:
        channel, payload_type = b2c0._record(payload, (0, 1), "Prover message")
        return base.ProverMessageEffect(
            b2c0._decode_module_ref(channel), b2c0._decode_value_type(payload_type)
        )
    if case == 2:
        return base.ChallengeEffect(b2c0._nat(payload, "challenge backlink"))
    if case == 4:
        return ApplyReductionEffect(b2c0._nat(payload, "reduction backlink"))
    if case == 5:
        return base.TerminalEffect(b2c0._nat(payload, "terminal backlink"))
    _fail(
        "Unsupported",
        "F0V2B2C1B3-U-EFFECT",
        f"effect tag {case} belongs to another isolation slice",
    )
    raise AssertionError("unreachable")


def decode_core(domain: object) -> object:
    """Strictly decode the bounded claim/reduction Core from canonical bytes."""

    fields = b2c0._record(domain, tuple(range(14)), "InteractiveCore")
    tables = tuple(
        b2c0._sequence(value, f"InteractiveCore field {ordinal}")
        for ordinal, value in enumerate(fields)
    )
    if any(tables[index] for index in (2, 4, 8, 9)):
        _fail(
            "Unsupported",
            "F0V2B2C1B3-U-OTHER-SLICE",
            "private, derived, Oracle, and Check constructors are outside B2C1B3",
        )
    used_modules = tuple(b2c0._content_ref(item, "used module") for item in tables[0])
    public_inputs = tuple(
        base.InputDecl(
            b2c0._decode_value_type(b2c0._record(item, (0,), "public input")[0])
        )
        for item in tables[1]
    )
    constants: list[object] = []
    for item in tables[3]:
        value_type, datum = b2c0._record(item, (0, 1), "constant")
        decoded_type = b2c0._decode_value_type(value_type)
        try:
            admitted = k1.admit_value(decoded_type, datum)
        except Exception as error:
            _fail("Refused", "F0V2B2C1B3-R-CONSTANT", str(error))
        constants.append(base.TypedConstantDecl(decoded_type, admitted))
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
        used_modules,
        public_inputs,
        (),
        tuple(constants),
        (),
        tuple(scopes),
        tuple(bindings),
        tuple(_decode_challenge(item) for item in tables[7]),
        (),
        (),
        tuple(_decode_claim(item) for item in tables[10]),
        tuple(_decode_reduction(item) for item in tables[11]),
        tuple(_decode_terminal(item) for item in tables[12]),
        occurrences,
    )


def _module_references(core: object) -> tuple[object, ...]:
    refs: list[object] = []
    for challenge in core.challenges:
        refs.extend((challenge.domain, challenge.fresh_law))
        if type(challenge.correlation) is base.JointCorrelation:
            refs.append(challenge.correlation.group)
        if type(challenge.reduction_use) is base.SharedReductionUse:
            refs.append(challenge.reduction_use.contract)
    refs.extend(claim.contract for claim in core.claims)
    for reduction in core.reductions:
        refs.append(reduction.contract)
        refs.extend(reduction.output_contracts)
    refs.extend(
        occurrence.effect.channel
        for occurrence in core.occurrences
        if type(occurrence.effect) is base.ProverMessageEffect
    )
    return tuple(refs)


def _ordinary_references(core: object) -> tuple[tuple[object, ...], tuple[object, ...]]:
    algorithms: set[object] = set()
    contracts: set[object] = set()
    for occurrence in core.occurrences:
        if type(occurrence.guard) is base.EvaluateGuard:
            algorithms.add(occurrence.guard.algorithm)
            contracts.add(occurrence.guard.evaluation_contract)

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
            "F0V2B2C1B3-R-EXACT-ALGORITHMS",
            "guard algorithm closure is missing or contains unused preimages",
        )
    if set(environment.contract_preimages) != set(contracts):
        _fail(
            "Refused",
            "F0V2B2C1B3-R-EXACT-CONTRACTS",
            "guard evaluation-contract closure is missing or contains unused preimages",
        )
    function_types: dict[object, object] = {}
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
                    "F0V2B2C1B3-R-ALGORITHM-ID",
                    "guard algorithm identity differs from its reference",
                )
            modules = environment.algorithm_modules.get(identifier)
            if modules is None:
                _fail(
                    "MissingDependency",
                    "F0V2B2C1B3-D-ALGORITHM-MODULES",
                    "guard algorithm module closure is missing",
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
        for identifier in contracts:
            contract = environment.contract_preimages[identifier]
            if contract.identity != identifier:
                _fail(
                    "Refused",
                    "F0V2B2C1B3-R-CONTRACT-ID",
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
        _fail(outcome or "Refused", "F0V2B2C1B3-R-DEPENDENCY", str(error))
    return MappingProxyType(function_types)


def _resolve_declaration(
    reference: object, expected: str, environment: object
) -> object:
    if type(reference) is not base.ModuleDeclarationRef:
        _fail(
            "Malformed",
            "F0V2B2C1B3-M-MODULE-REF",
            "module declaration reference has another carrier",
        )
    if reference.declaration_kind != expected:
        _fail(
            "KindMismatch",
            "F0V2B2C1B3-K-DECLARATION",
            f"expected declaration kind {expected}",
        )
    module = environment.module_preimages.get(reference.module)
    if module is None:
        _fail(
            "MissingDependency",
            "F0V2B2C1B3-D-MODULE-PREIMAGE",
            "declaration owner is missing",
        )
    try:
        return k1.resolve_module_declaration(
            module, reference.declaration_kind, reference.local_ordinal
        )
    except Exception as error:
        _fail("Refused", "F0V2B2C1B3-R-DECLARATION-COORDINATE", str(error))
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
            "F0V2B2C1B3-R-NOMINAL-BODY",
            f"{expected} declaration has another exact body",
        )


def _scope_paths(core: object) -> tuple[tuple[int, ...], ...]:
    paths: list[tuple[int, ...]] = []
    for ordinal in range(len(core.scopes)):
        trail: list[int] = []
        current: int | None = ordinal
        while current is not None:
            trail.append(current)
            current = core.scopes[current].parent
        paths.append(tuple(reversed(trail)))
    return tuple(paths)


def _output_types(core: object) -> tuple[tuple[object, ...], ...]:
    result: list[tuple[object, ...]] = []
    for occurrence in core.occurrences:
        effect = occurrence.effect
        if type(effect) is base.ProverMessageEffect:
            result.append((effect.payload_type,))
        elif type(effect) is base.ChallengeEffect:
            if not 0 <= effect.challenge < len(core.challenges):
                _fail(
                    "Refused",
                    "F0V2B2C1B3-R-CHALLENGE-REF",
                    "Challenge occurrence names an absent declaration",
                )
            result.append((core.challenges[effect.challenge].value_type,))
        elif type(effect) in (ApplyReductionEffect, base.TerminalEffect):
            result.append(())
        else:
            _fail("Unsupported", "F0V2B2C1B3-U-EFFECT", "unsupported effect")
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
            _fail("Refused", "F0V2B2C1B3-R-VALUE-REF", "occurrence is absent")
        values = outputs[reference.occurrence]
        if not 0 <= reference.output_ordinal < len(values):
            _fail("Refused", "F0V2B2C1B3-R-VALUE-REF", "output is absent")
        return values[reference.output_ordinal]
    else:
        _fail(
            "Malformed",
            "F0V2B2C1B3-M-VALUE-REF",
            "ValueRef belongs to another isolation slice",
        )
    if not 0 <= ordinal < len(table):
        _fail("Refused", "F0V2B2C1B3-R-VALUE-REF", "value ordinal is absent")
    return table[ordinal].value_type


def _producer_node(reference: object) -> tuple[int, ...]:
    if type(reference) is base.PublicInputRef:
        return 0, reference.ordinal
    if type(reference) is base.ConstantRef:
        return 2, reference.ordinal
    if type(reference) is base.OccurrenceOutputRef:
        return 8, reference.occurrence, reference.output_ordinal
    _fail("Malformed", "F0V2B2C1B3-M-VALUE-REF", "producer is outside the slice")
    raise AssertionError("unreachable")


def _guard_implies(use: object, source: object) -> bool:
    return type(source) is base.AlwaysGuard or use == source


def _is_ancestor_scope(
    paths: tuple[tuple[int, ...], ...], parent: int, child: int
) -> bool:
    return parent in paths[child]


def _source_guard(core: object, reference: object) -> object:
    if type(reference) is base.OccurrenceOutputRef:
        return core.occurrences[reference.occurrence].guard
    return base.AlwaysGuard()


@dataclass(frozen=True)
class ValidationEvidence:
    outputs: tuple[tuple[object, ...], ...]
    paths: tuple[tuple[int, ...], ...]
    openings: tuple[int, ...]
    challenge_positions: Mapping[int, int]
    reduction_positions: Mapping[int, int]
    terminal_positions: Mapping[int, int]
    reduction_consumers: Mapping[int, tuple[int, ...]]
    claim_uses: Mapping[int, tuple[tuple[str, int, int, int], ...]]


def _validate_core(
    core: object, environment: object, function_types: Mapping[object, object]
) -> ValidationEvidence:
    if not core.scopes or not core.occurrences or not core.terminals:
        _fail(
            "Refused",
            "F0V2B2C1B3-R-NONEMPTY",
            "scope, occurrence, and terminal tables must be nonempty",
        )
    if len(core.occurrences) > MAX_LOCAL_ITEMS:
        _fail(
            "DeterministicLimitExceeded",
            "F0V2B2C1B3-L-OCCURRENCES",
            "occurrence table crosses the target local bound",
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
            "F0V2B2C1B3-R-EXACT-USED-MODULES",
            "used_modules differs from the exact declaration-owner set",
        )
    for occurrence in core.occurrences:
        if type(occurrence.effect) is base.ProverMessageEffect:
            _validate_nominal(
                occurrence.effect.channel, "pir.message-channel", environment
            )
    for challenge in core.challenges:
        if type(challenge) is not base.ChallengeDecl:
            _fail("Malformed", "F0V2B2C1B3-M-CHALLENGE", "Challenge carrier differs")
        _validate_nominal(challenge.domain, "pir.challenge-domain", environment)
        _validate_nominal(challenge.fresh_law, "pir.public-coin-law", environment)
        if type(challenge.correlation) is base.JointCorrelation:
            _validate_nominal(
                challenge.correlation.group,
                "pir.coin-correlation-group",
                environment,
            )
        elif type(challenge.correlation) is not base.IndependentCorrelation:
            _fail(
                "Malformed",
                "F0V2B2C1B3-M-CORRELATION",
                "coin correlation branch differs",
            )
        if type(challenge.reduction_use) is base.SharedReductionUse:
            _validate_nominal(
                challenge.reduction_use.contract,
                "pir.challenge-sharing-contract",
                environment,
            )
        elif type(challenge.reduction_use) is not base.ExclusiveReductionUse:
            _fail(
                "Malformed",
                "F0V2B2C1B3-M-REDUCTION-USE",
                "reduction-use branch differs",
            )
    for claim in core.claims:
        if type(claim) is not ClaimDecl:
            _fail("Malformed", "F0V2B2C1B3-M-CLAIM", "claim carrier differs")
        _validate_nominal(claim.contract, "pir.claim-contract", environment)
    for reduction in core.reductions:
        if type(reduction) is not ReductionDecl:
            _fail("Malformed", "F0V2B2C1B3-M-REDUCTION", "reduction carrier differs")
        _validate_nominal(reduction.contract, "pir.reduction-contract", environment)
        for contract in reduction.output_contracts:
            _validate_nominal(contract, "pir.claim-contract", environment)

    all_types = [
        *(item.value_type for item in core.public_inputs),
        *(item.value_type for item in core.constants),
        *(item.value_type for item in core.challenges),
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
    except Exception as error:
        _fail("KindMismatch", "F0V2B2C1B3-K-VALUE-TYPE", str(error))

    outputs = _output_types(core)
    if core.scopes[0] != base.ScopeDecl(None, None):
        _fail("Refused", "F0V2B2C1B3-R-ROOT-SCOPE", "scope zero is not initial")
    openings = [-1]
    depths = [0]
    for ordinal, scope in enumerate(core.scopes[1:], start=1):
        if scope.parent is None or not 0 <= scope.parent < ordinal:
            _fail(
                "Refused",
                "F0V2B2C1B3-R-SCOPE-PARENT",
                "scope parent does not precede its child",
            )
        if scope.opening is None or not 0 <= scope.opening < len(core.occurrences):
            _fail(
                "Refused",
                "F0V2B2C1B3-R-SCOPE-OPENING",
                "child scope opening is absent",
            )
        depth = depths[scope.parent] + 1
        if depth > 384:
            _fail(
                "DeterministicLimitExceeded",
                "F0V2B2C1B3-L-SCOPE-DEPTH",
                "scope depth exceeds the target bound",
            )
        if scope.opening < openings[scope.parent]:
            _fail(
                "Refused",
                "F0V2B2C1B3-R-SCOPE-OPENING",
                "scope opens before its parent",
            )
        members = [
            index
            for index, occurrence in enumerate(core.occurrences)
            if occurrence.scope == ordinal
        ]
        if not members or scope.opening > members[0]:
            _fail(
                "Refused",
                "F0V2B2C1B3-R-SCOPE-OPENING",
                "child scope opens after its first member or has no member",
            )
        openings.append(scope.opening)
        depths.append(depth)
    paths = _scope_paths(core)

    binding_triples: set[tuple[object, ...]] = set()
    bound_public: set[int] = set()
    for binding in core.public_bindings:
        if not 0 <= binding.scope < len(core.scopes):
            _fail("Refused", "F0V2B2C1B3-R-SCOPE-REF", "binding scope is absent")
        _value_type(core, outputs, binding.value)
        if type(binding.value) is base.OccurrenceOutputRef:
            source = binding.value.occurrence
            if (
                openings[binding.scope] < 0
                or source >= openings[binding.scope]
                or type(core.occurrences[source].guard) is not base.AlwaysGuard
            ):
                _fail(
                    "Refused",
                    "F0V2B2C1B3-R-BINDING-AVAILABILITY",
                    "scope binding is not unconditionally available before opening",
                )
        if type(binding.value) is base.PublicInputRef:
            bound_public.add(binding.value.ordinal)
        triple = (binding.scope, binding.binding_class, binding.value)
        if triple in binding_triples:
            _fail(
                "Refused",
                "F0V2B2C1B3-R-DUPLICATE-BINDING",
                "public binding triple is duplicated",
            )
        binding_triples.add(triple)
    if bound_public != set(range(len(core.public_inputs))):
        _fail(
            "Refused",
            "F0V2B2C1B3-R-BINDING-COMPLETENESS",
            "public inputs lack complete binding coverage",
        )

    challenge_positions: dict[int, list[int]] = {
        index: [] for index in range(len(core.challenges))
    }
    reduction_positions: dict[int, list[int]] = {
        index: [] for index in range(len(core.reductions))
    }
    terminal_positions: dict[int, list[int]] = {
        index: [] for index in range(len(core.terminals))
    }
    available: set[object] = {
        *(base.PublicInputRef(index) for index in range(len(core.public_inputs))),
        *(base.ConstantRef(index) for index in range(len(core.constants))),
    }
    for occurrence_ref, occurrence in enumerate(core.occurrences):
        if not 0 <= occurrence.scope < len(core.scopes):
            _fail("Refused", "F0V2B2C1B3-R-SCOPE-REF", "occurrence scope is absent")
        if openings[occurrence.scope] > occurrence_ref:
            _fail(
                "Refused",
                "F0V2B2C1B3-R-SCOPE-OPENING",
                "occurrence precedes its scope opening",
            )
        guard_reads: tuple[object, ...] = ()
        if type(occurrence.guard) is base.EvaluateGuard:
            guard_reads = occurrence.guard.inputs
            function = function_types.get(occurrence.guard.algorithm)
            observed = tuple(_value_type(core, outputs, item) for item in guard_reads)
            if (
                function is None
                or function.inputs != observed
                or function.output != k1.BOOL
                or function.failures
            ):
                _fail(
                    "KindMismatch",
                    "F0V2B2C1B3-K-GUARD-ABI",
                    "guard algorithm is not exact, total, and Boolean",
                )
        elif type(occurrence.guard) is not base.AlwaysGuard:
            _fail("Malformed", "F0V2B2C1B3-M-GUARD", "guard carrier differs")
        if any(item not in available for item in guard_reads):
            _fail(
                "Refused",
                "F0V2B2C1B3-R-VALUE-AVAILABILITY",
                "guard reads a future or absent value",
            )
        for item in guard_reads:
            if not _guard_implies(occurrence.guard, _source_guard(core, item)):
                _fail(
                    "Refused",
                    "F0V2B2C1B3-R-GUARD-IMPLIES",
                    "guard does not imply a conditional input source",
                )

        effect = occurrence.effect
        reads: tuple[object, ...] = ()
        if type(effect) is base.ChallengeEffect:
            if not 0 <= effect.challenge < len(core.challenges):
                _fail(
                    "Refused",
                    "F0V2B2C1B3-R-CHALLENGE-REF",
                    "Challenge occurrence names an absent declaration",
                )
            challenge_positions[effect.challenge].append(occurrence_ref)
            challenge = core.challenges[effect.challenge]
            if occurrence.scope != challenge.scope:
                _fail(
                    "Refused",
                    "F0V2B2C1B3-R-CHALLENGE-SCOPE",
                    "Challenge occurrence differs from declaration scope",
                )
            reads = challenge.public_conditions
        elif type(effect) is ApplyReductionEffect:
            if not 0 <= effect.reduction < len(core.reductions):
                _fail(
                    "Refused",
                    "F0V2B2C1B3-R-REDUCTION-REF",
                    "ApplyReduction names an absent declaration",
                )
            reduction_positions[effect.reduction].append(occurrence_ref)
            reduction = core.reductions[effect.reduction]
            if occurrence.scope != reduction.scope:
                _fail(
                    "Refused",
                    "F0V2B2C1B3-R-REDUCTION-SCOPE",
                    "ApplyReduction differs from declaration scope",
                )
            reads = reduction.side_inputs
        elif type(effect) is base.TerminalEffect:
            if not 0 <= effect.terminal < len(core.terminals):
                _fail(
                    "Refused",
                    "F0V2B2C1B3-R-TERMINAL-REF",
                    "terminal backlink is absent",
                )
            terminal_positions[effect.terminal].append(occurrence_ref)
            reads = core.terminals[effect.terminal].public_outputs
        elif type(effect) is not base.ProverMessageEffect:
            _fail("Unsupported", "F0V2B2C1B3-U-EFFECT", "unsupported effect")
        if any(item not in available for item in reads):
            _fail(
                "Refused",
                "F0V2B2C1B3-R-VALUE-AVAILABILITY",
                "occurrence reads a future or absent value",
            )
        for item in reads:
            if not _guard_implies(occurrence.guard, _source_guard(core, item)):
                _fail(
                    "Refused",
                    "F0V2B2C1B3-R-GUARD-IMPLIES",
                    "occurrence guard does not imply a value source guard",
                )
        for output in range(len(outputs[occurrence_ref])):
            available.add(base.OccurrenceOutputRef(occurrence_ref, output))

    for positions, code, label in (
        (challenge_positions, "CHALLENGE", "Challenge"),
        (reduction_positions, "REDUCTION", "Reduction"),
        (terminal_positions, "TERMINAL", "terminal"),
    ):
        if any(len(items) != 1 for items in positions.values()):
            _fail(
                "Refused",
                f"F0V2B2C1B3-R-{code}-BACKLINK",
                f"{label} occurrence backlink is not one-to-one",
            )
    exact_challenge_positions = {
        key: value[0] for key, value in challenge_positions.items()
    }
    exact_reduction_positions = {
        key: value[0] for key, value in reduction_positions.items()
    }
    exact_terminal_positions = {
        key: value[0] for key, value in terminal_positions.items()
    }

    for challenge_ref, challenge in enumerate(core.challenges):
        if not 0 <= challenge.scope < len(core.scopes):
            _fail(
                "Refused",
                "F0V2B2C1B3-R-CHALLENGE-SCOPE",
                "Challenge scope is absent",
            )
        for condition in challenge.public_conditions:
            _value_type(core, outputs, condition)
            if type(condition) not in (base.PublicInputRef, base.ConstantRef):
                _fail(
                    "Refused",
                    "F0V2B2C1B3-R-CHALLENGE-CONDITION-PUBLIC",
                    "Challenge condition is not StaticPublic in this slice",
                )
        correlation = challenge.correlation
        if type(correlation) is base.JointCorrelation:
            members = [
                prior_ref
                for prior_ref, prior_challenge in enumerate(
                    core.challenges[:challenge_ref]
                )
                if type(prior_challenge.correlation) is base.JointCorrelation
                and prior_challenge.correlation.group == correlation.group
            ]
            if correlation.index != len(members) or correlation.prior_members != tuple(
                members
            ):
                _fail(
                    "Refused",
                    "F0V2B2C1B3-R-JOINT-CLOSURE",
                    "joint index or complete prior-member closure differs",
                )
            for prior_ref in members:
                prior_challenge = core.challenges[prior_ref]
                if (
                    prior_challenge.value_type != challenge.value_type
                    or prior_challenge.domain != challenge.domain
                    or prior_challenge.fresh_law != challenge.fresh_law
                    or prior_challenge.scope != challenge.scope
                    or exact_challenge_positions[prior_ref]
                    >= exact_challenge_positions[challenge_ref]
                ):
                    _fail(
                        "Refused",
                        "F0V2B2C1B3-R-JOINT-COMPATIBILITY",
                        "joint members differ in type, law, scope, or occurrence order",
                    )

    claim_sources: dict[int, tuple[str, int, int]] = {}
    output_claims: dict[tuple[int, int], int] = {}
    for claim_ref, claim in enumerate(core.claims):
        if not 0 <= claim.scope < len(core.scopes):
            _fail("Refused", "F0V2B2C1B3-R-CLAIM-SCOPE", "claim scope is absent")
        if type(claim.usage) is not base.ClaimUsage:
            _fail("Malformed", "F0V2B2C1B3-M-CLAIM-USAGE", "claim usage differs")
        if type(claim.source) is InitialClaimSource:
            if not 0 <= claim.source.binding < len(core.public_bindings):
                _fail(
                    "Refused",
                    "F0V2B2C1B3-R-CLAIM-SOURCE",
                    "initial claim source binding is absent",
                )
            binding = core.public_bindings[claim.source.binding]
            if (
                binding.binding_class is not base.BindingClass.STATEMENT
                or not _is_ancestor_scope(paths, binding.scope, claim.scope)
            ):
                _fail(
                    "Refused",
                    "F0V2B2C1B3-R-CLAIM-SOURCE",
                    "initial claim does not cite an ancestor Statement binding",
                )
            claim_sources[claim_ref] = (
                "initial",
                openings[binding.scope],
                claim.source.binding,
            )
        elif type(claim.source) is ReductionOutputClaimSource:
            source = claim.source
            if not 0 <= source.reduction < len(core.reductions):
                _fail(
                    "Refused",
                    "F0V2B2C1B3-R-CLAIM-SOURCE",
                    "output claim source reduction is absent",
                )
            reduction = core.reductions[source.reduction]
            if not 0 <= source.output_ordinal < len(reduction.output_contracts):
                _fail(
                    "Refused",
                    "F0V2B2C1B3-R-CLAIM-OUTPUT",
                    "output claim ordinal is absent",
                )
            if (
                claim.contract != reduction.output_contracts[source.output_ordinal]
                or claim.scope != reduction.scope
            ):
                _fail(
                    "KindMismatch",
                    "F0V2B2C1B3-K-CLAIM-OUTPUT",
                    "output claim contract or scope differs from the reduction output",
                )
            coordinate = (source.reduction, source.output_ordinal)
            if coordinate in output_claims:
                _fail(
                    "Refused",
                    "F0V2B2C1B3-R-CLAIM-OUTPUT-UNIQUE",
                    "a reduction output creates more than one ClaimRef",
                )
            output_claims[coordinate] = claim_ref
            claim_sources[claim_ref] = (
                "reduction",
                exact_reduction_positions[source.reduction],
                source.reduction,
            )
        else:
            _fail("Malformed", "F0V2B2C1B3-M-CLAIM-SOURCE", "claim source differs")
    expected_outputs = {
        (reduction_ref, output)
        for reduction_ref, reduction in enumerate(core.reductions)
        for output in range(len(reduction.output_contracts))
    }
    if set(output_claims) != expected_outputs:
        _fail(
            "Refused",
            "F0V2B2C1B3-R-CLAIM-OUTPUT-COVERAGE",
            "reduction outputs and ReductionOutput claims are not a bijection",
        )

    def publication_dependencies(reference: object) -> set[int]:
        pending = [reference]
        seen: set[object] = set()
        result: set[int] = set()
        while pending:
            current = pending.pop()
            if current in seen:
                continue
            seen.add(current)
            if type(current) is not base.OccurrenceOutputRef:
                continue
            effect = core.occurrences[current.occurrence].effect
            if type(effect) is base.ProverMessageEffect:
                result.add(current.occurrence)
            elif type(effect) is base.ChallengeEffect:
                challenge = core.challenges[effect.challenge]
                pending.extend(challenge.public_conditions)
                if type(challenge.correlation) is base.JointCorrelation:
                    pending.extend(
                        base.OccurrenceOutputRef(exact_challenge_positions[item], 0)
                        for item in challenge.correlation.prior_members
                    )
        return result

    claim_uses: dict[int, list[tuple[str, int, int, int]]] = {
        index: [] for index in range(len(core.claims))
    }
    reduction_consumers: dict[int, list[int]] = {
        index: [] for index in range(len(core.challenges))
    }
    for reduction_ref, reduction in enumerate(core.reductions):
        position = exact_reduction_positions[reduction_ref]
        occurrence = core.occurrences[position]
        if not reduction.input_claims:
            _fail(
                "Refused",
                "F0V2B2C1B3-R-REDUCTION-NONEMPTY",
                "reduction input claims are empty",
            )
        for input_ordinal, claim_ref in enumerate(reduction.input_claims):
            if not 0 <= claim_ref < len(core.claims):
                _fail(
                    "Refused",
                    "F0V2B2C1B3-R-REDUCTION-CLAIM",
                    "reduction input claim is absent",
                )
            source_kind, source_position, _source_ref = claim_sources[claim_ref]
            if source_kind == "reduction" and source_position >= position:
                _fail(
                    "Refused",
                    "F0V2B2C1B3-R-CLAIM-AVAILABILITY",
                    "reduction consumes a claim before its creation",
                )
            if source_kind == "reduction" and not _guard_implies(
                occurrence.guard, core.occurrences[source_position].guard
            ):
                _fail(
                    "Refused",
                    "F0V2B2C1B3-R-GUARD-IMPLIES",
                    "reduction guard does not imply output-claim creation",
                )
            claim_uses[claim_ref].append(
                ("reduction", position, reduction_ref, input_ordinal)
            )
        challenge_positions_in_reduction = [
            exact_challenge_positions[item] if 0 <= item < len(core.challenges) else -1
            for item in reduction.required_challenges
        ]
        if len(set(reduction.required_challenges)) != len(
            reduction.required_challenges
        ) or challenge_positions_in_reduction != sorted(
            challenge_positions_in_reduction
        ):
            _fail(
                "Refused",
                "F0V2B2C1B3-R-CHALLENGE-ORDER",
                "required challenges are not unique in occurrence order",
            )
        for challenge_ref, challenge_position in zip(
            reduction.required_challenges,
            challenge_positions_in_reduction,
            strict=True,
        ):
            if (
                challenge_position < 0
                or challenge_position >= position
                or not _is_ancestor_scope(
                    paths, core.challenges[challenge_ref].scope, reduction.scope
                )
                or not _guard_implies(
                    occurrence.guard, core.occurrences[challenge_position].guard
                )
            ):
                _fail(
                    "Refused",
                    "F0V2B2C1B3-R-CHALLENGE-AVAILABILITY",
                    "required Challenge is future, inactive, or out of scope",
                )
            reduction_consumers[challenge_ref].append(reduction_ref)

        if any(
            type(item) is not ReductionPublicationRequirement
            for item in reduction.required_publications
        ):
            _fail(
                "Malformed",
                "F0V2B2C1B3-M-PUBLICATION",
                "publication requirement carrier differs",
            )
        publication_refs = tuple(
            item.publication for item in reduction.required_publications
        )
        if len(set(publication_refs)) != len(
            publication_refs
        ) or publication_refs != tuple(sorted(publication_refs)):
            _fail(
                "Refused",
                "F0V2B2C1B3-R-PUBLICATION-ORDER",
                "required publications are not unique in occurrence order",
            )
        for requirement in reduction.required_publications:
            publication = requirement.publication
            if not 0 <= publication < position:
                _fail(
                    "Refused",
                    "F0V2B2C1B3-R-PUBLICATION-AVAILABILITY",
                    "required publication is absent or does not precede reduction",
                )
            publication_occurrence = core.occurrences[publication]
            if type(publication_occurrence.effect) is not base.ProverMessageEffect:
                _fail(
                    "KindMismatch",
                    "F0V2B2C1B3-K-PUBLICATION-KIND",
                    "required publication is not a Prover publication in this slice",
                )
            if not _is_ancestor_scope(
                paths, publication_occurrence.scope, reduction.scope
            ) or not _guard_implies(occurrence.guard, publication_occurrence.guard):
                _fail(
                    "Refused",
                    "F0V2B2C1B3-R-PUBLICATION-AVAILABILITY",
                    "required publication is inactive or out of scope",
                )
            following = [
                challenge_ref
                for challenge_ref in reduction.required_challenges
                if exact_challenge_positions[challenge_ref] > publication
            ]
            expected_next = following[0] if following else None
            if requirement.next_challenge != expected_next:
                _fail(
                    "Refused",
                    "F0V2B2C1B3-R-LAST-CHALLENGE",
                    "publication does not name its least following required Challenge",
                )
        dependency_publications: set[int] = set()
        for side_input in reduction.side_inputs:
            dependency_publications.update(publication_dependencies(side_input))
        if not dependency_publications.issubset(set(publication_refs)):
            _fail(
                "Refused",
                "F0V2B2C1B3-R-PUBLICATION-CLOSURE",
                "side-input publication closure is incomplete",
            )

    for challenge_ref, challenge in enumerate(core.challenges):
        consumers = sorted(
            reduction_consumers[challenge_ref],
            key=lambda item: (exact_reduction_positions[item], item),
        )
        reduction_consumers[challenge_ref] = consumers
        if type(challenge.reduction_use) is base.ExclusiveReductionUse:
            if len(consumers) > 1:
                _fail(
                    "Refused",
                    "F0V2B2C1B3-R-EXCLUSIVE-CONSUMERS",
                    "Exclusive Challenge has more than one reduction-role consumer",
                )
        elif len(consumers) < 2:
            _fail(
                "Refused",
                "F0V2B2C1B3-R-SHARED-CONSUMERS",
                "Shared Challenge has fewer than two reduction-role consumers",
            )

    for claim_ref, uses in claim_uses.items():
        reduction_uses = [item for item in uses if item[0] == "reduction"]
        if (
            core.claims[claim_ref].usage is base.ClaimUsage.LINEAR
            and len(reduction_uses) > 1
        ):
            _fail(
                "Refused",
                "F0V2B2C1B3-R-CLAIM-LINEARITY",
                "linear claim has more than one reduction use",
            )

    globally_live = set(range(len(core.claims)))
    for claim_ref, uses in claim_uses.items():
        if core.claims[claim_ref].usage is base.ClaimUsage.LINEAR and any(
            item[0] == "reduction" for item in uses
        ):
            globally_live.discard(claim_ref)
    for terminal_ref, terminal in enumerate(core.terminals):
        position = exact_terminal_positions[terminal_ref]
        disposition_claims: list[int] = []
        for disposition_ordinal, entry in enumerate(terminal.claim_dispositions):
            if type(entry) is not base.ClaimDispositionEntry:
                _fail(
                    "Malformed",
                    "F0V2B2C1B3-M-CLAIM-DISPOSITION",
                    "terminal disposition carrier differs",
                )
            if not 0 <= entry.claim < len(core.claims):
                _fail(
                    "Refused",
                    "F0V2B2C1B3-R-CLAIM-DISPOSITION",
                    "terminal disposition claim is absent",
                )
            if entry.claim not in globally_live:
                _fail(
                    "Refused",
                    "F0V2B2C1B3-R-CLAIM-DISPOSITION",
                    "terminal disposes a statically consumed claim",
                )
            source_kind, source_position, _source_ref = claim_sources[entry.claim]
            if source_kind == "reduction":
                if source_position >= position or not _guard_implies(
                    core.occurrences[position].guard,
                    core.occurrences[source_position].guard,
                ):
                    _fail(
                        "Refused",
                        "F0V2B2C1B3-R-CLAIM-AVAILABILITY",
                        "terminal disposition does not follow claim creation",
                    )
            disposition_claims.append(entry.claim)
            claim_uses[entry.claim].append(
                ("terminal", position, terminal_ref, disposition_ordinal)
            )
        if len(set(disposition_claims)) != len(disposition_claims):
            _fail(
                "Refused",
                "F0V2B2C1B3-R-CLAIM-DISPOSITION-UNIQUE",
                "terminal repeats a claim disposition",
            )
        if set(disposition_claims) != globally_live:
            _fail(
                "Refused",
                "F0V2B2C1B3-R-TERMINAL-CLAIM-CLOSURE",
                "terminal does not close every statically live claim",
            )
    final = core.occurrences[-1]
    if (
        type(final.guard) is not base.AlwaysGuard
        or type(final.effect) is not base.TerminalEffect
    ):
        _fail(
            "Refused",
            "F0V2B2C1B3-R-FINAL-FALLBACK",
            "final occurrence is not an unconditional terminal fallback",
        )
    return ValidationEvidence(
        outputs,
        paths,
        tuple(openings),
        MappingProxyType(exact_challenge_positions),
        MappingProxyType(exact_reduction_positions),
        MappingProxyType(exact_terminal_positions),
        MappingProxyType(
            {key: tuple(value) for key, value in reduction_consumers.items()}
        ),
        MappingProxyType({key: tuple(value) for key, value in claim_uses.items()}),
    )


def _pc_value(node: tuple[int, ...]) -> dict[str, Any]:
    tag, *arguments = node
    if tag in (8, 12, 13):
        return foundation._v(
            tag,
            {
                0: foundation._ordinal("occurrence-ref-body-v0", arguments[0]),
                1: arguments[1],
            },
        )
    compiler = {
        0: "public-input-ref-body-v0",
        2: "constant-ref-body-v0",
        4: "scope-ref-body-v0",
        5: "binding-ref-body-v0",
        6: "occurrence-ref-body-v0",
        7: "occurrence-ref-body-v0",
        9: "claim-ref-body-v0",
        10: "reduction-ref-body-v0",
        11: "terminal-ref-body-v0",
    }.get(tag)
    if compiler is None or len(arguments) != 1:
        _fail("CheckerFailure", "F0V2B2C1B3-CHECKER", "invalid PCNode")
    return foundation._v(tag, foundation._ordinal(compiler, arguments[0]))


_PC_GRAPH_SCHEMA = codec.record_field(VIEW_SCHEMAS["PublicCoinView"], 1)
_PC_NODE_SCHEMA = codec.record_field(_PC_GRAPH_SCHEMA, 0)["element"]
_PC_EDGE_SCHEMA = codec.record_field(_PC_GRAPH_SCHEMA, 1)["element"]
_READ_SCHEMA = codec.record_field(VIEW_SCHEMAS["StrategyDecisionView"], 3)["element"]


def _pc_key(node: tuple[int, ...]) -> bytes:
    return codec.encode_value(_PC_NODE_SCHEMA, _pc_value(node))


def _edge_value(pair: tuple[tuple[int, ...], tuple[int, ...]]) -> dict[int, Any]:
    return {0: _pc_value(pair[0]), 1: _pc_value(pair[1])}


def _edge_key(pair: tuple[tuple[int, ...], tuple[int, ...]]) -> bytes:
    return codec.encode_value(_PC_EDGE_SCHEMA, _edge_value(pair))


def _graph(
    core: object, validation: ValidationEvidence
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
        if type(effect) is base.ChallengeEffect:
            challenge = core.challenges[effect.challenge]
            for condition in challenge.public_conditions:
                edge(_producer_node(condition), effect_node)
            if type(challenge.correlation) is base.JointCorrelation:
                for prior_member in challenge.correlation.prior_members:
                    edge(
                        (
                            8,
                            validation.challenge_positions[prior_member],
                            0,
                        ),
                        effect_node,
                    )
        elif type(effect) is ApplyReductionEffect:
            reduction = core.reductions[effect.reduction]
            for claim_ref in reduction.input_claims:
                edge((9, claim_ref), effect_node)
            for side_input in reduction.side_inputs:
                edge(_producer_node(side_input), effect_node)
            for challenge_ref in reduction.required_challenges:
                edge(
                    (8, validation.challenge_positions[challenge_ref], 0),
                    effect_node,
                )
            for requirement in reduction.required_publications:
                edge((7, requirement.publication), effect_node)
            edge(effect_node, (10, effect.reduction))
        elif type(effect) is base.TerminalEffect:
            terminal = core.terminals[effect.terminal]
            for output in terminal.public_outputs:
                edge(_producer_node(output), effect_node)
            for disposition in terminal.claim_dispositions:
                edge((9, disposition.claim), effect_node)
            edge(effect_node, (11, effect.terminal))
            prior_terminals.append((11, effect.terminal))
        for output in range(len(validation.outputs[occurrence_ref])):
            edge(effect_node, (8, occurrence_ref, output))

    for claim_ref, claim in enumerate(core.claims):
        if type(claim.source) is InitialClaimSource:
            edge((5, claim.source.binding), (9, claim_ref))
        else:
            edge((10, claim.source.reduction), (9, claim_ref))
    for reduction_ref, occurrence_ref in validation.reduction_positions.items():
        edge((7, occurrence_ref), (10, reduction_ref))

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
        _fail(
            "Refused",
            "F0V2B2C1B3-R-PCGRAPH-CYCLE",
            "claim/reduction PCGraph is cyclic",
        )

    classes: dict[tuple[int, ...], int] = {}
    challenge_validity: dict[int, bool] = {}
    for node in topological:
        joined = max((classes[parent] for parent in incoming[node]), default=0)
        if node[0] in (0, 2):
            value = 0
        elif node[0] == 7:
            effect = core.occurrences[node[1]].effect
            if type(effect) is base.ProverMessageEffect:
                activity_class = classes[(6, node[1])]
                value = 1 if activity_class <= 1 else activity_class
            elif type(effect) is base.ChallengeEffect:
                challenge = core.challenges[effect.challenge]
                activity_class = classes[(6, node[1])]
                condition_classes = [
                    classes[_producer_node(item)]
                    for item in challenge.public_conditions
                ]
                prior_classes = (
                    [
                        classes[
                            (
                                8,
                                validation.challenge_positions[item],
                                0,
                            )
                        ]
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
                elif activity_class <= 1:
                    value = 1
                else:  # pragma: no cover - closed lattice cases above
                    value = 3
                challenge_validity[effect.challenge] = value == 1
            else:
                value = joined
        else:
            value = joined
        classes[node] = value

    activities = {(6, index) for index in range(len(core.occurrences))}
    challenge_sinks = {
        (7, occurrence) for occurrence in validation.challenge_positions.values()
    }
    reduction_sinks = {(10, index) for index in range(len(core.reductions))}
    terminal_sinks = {(11, index) for index in range(len(core.terminals))}
    public_observations = {
        (8, occurrence_ref, 0)
        for occurrence_ref, occurrence in enumerate(core.occurrences)
        if type(occurrence.effect) is base.ProverMessageEffect
    }
    terminal_outputs = {
        _producer_node(output)
        for terminal in core.terminals
        for output in terminal.public_outputs
    }
    sinks = (
        activities
        | challenge_sinks
        | reduction_sinks
        | terminal_sinks
        | public_observations
        | terminal_outputs
    )
    accepting_terminals = {
        (11, terminal_ref)
        for terminal_ref, terminal in enumerate(core.terminals)
        if terminal.verdict is base.TerminalVerdict.ACCEPT
    }
    acceptance = (
        reduction_sinks
        | accepting_terminals
        | {
            _producer_node(output)
            for terminal_ref, terminal in enumerate(core.terminals)
            if (11, terminal_ref) in accepting_terminals
            for output in terminal.public_outputs
        }
    )
    eligible = all(classes[node] in (0, 1) for node in sinks) and all(
        challenge_validity.get(index, False) for index in range(len(core.challenges))
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
        6: [],
    }
    return graph, {
        "nodes": len(nodes),
        "edges": len(edges),
        "eligible": eligible,
        "classes": classes,
        "challenge_validity": challenge_validity,
        "acceptance_sinks": len(acceptance),
    }


def admit_core(candidate: object, environment: object) -> AdmissionResult:
    try:
        if type(candidate) is not b2c0.CanonicalCoreCandidate:
            _fail("Malformed", "F0V2B2C1B3-M-REQUEST", "Core request is malformed")
        if type(environment) is not base.Environment:
            _fail(
                "Malformed",
                "F0V2B2C1B3-M-ENVIRONMENT",
                "environment is malformed",
            )
        if candidate.profile_id != environment.profile_id:
            _fail("KindMismatch", "F0V2B2C1B3-K-REQUEST-PROFILE", "profiles differ")
        if environment.profile_id != base.target_profile_id():
            _fail(
                "KindMismatch",
                "F0V2B2C1B3-K-TARGET-PROFILE",
                "profile is unsupported",
            )
        profile, domain, domain_body = b2c0._strict_profiled_body(
            candidate.profiled_body, "B2C1B3 claim/reduction Core"
        )
        if profile != candidate.profile_id:
            _fail("KindMismatch", "F0V2B2C1B3-K-BODY-PROFILE", "body profile differs")
        if (
            type(candidate.asserted_id) is not k1.TypedContentId
            or candidate.asserted_id.subject_kind != base.TARGET_CORE_KIND
        ):
            _fail("KindMismatch", "F0V2B2C1B3-K-CORE-ID", "Core ID kind differs")
        try:
            k1.authenticate_content_id(
                candidate.asserted_id,
                candidate.profiled_body,
                environment.prior_meta_preimages,
            )
        except Exception as error:
            _fail("Malformed", "F0V2B2C1B3-M-CORE-ID", str(error))
        core = decode_core(domain)
        closure = b2c0.snapshot_environment(environment)
        functions = _authenticate_algorithms(core, environment)
        validation = _validate_core(core, environment, functions)
        _graph_value, graph_evidence = _graph(core, validation)
        summary = (
            ("slice", "F0-V2B2C1B3"),
            ("core", core),
            ("validation", validation),
            ("graph_evidence", graph_evidence),
        )
        handle = b2c0.AdmittedCoreSnapshot(
            candidate.asserted_id.internal_reference(),
            candidate.profile_id.internal_reference(),
            bytes(candidate.profiled_body),
            bytes(domain_body),
            closure,
            summary,
            EVALUATOR_FINGERPRINT,
            tuple(range(1, 15)),
            b2c0._CORE_ISSUER,
        )
        return AdmissionResult(
            "Affirmative",
            "F0V2B2C1B3-A-CORE-ADMITTED",
            "exact bytes passed the bounded claim/reduction owner evaluator",
            handle,
        )
    except FamilyFailure as error:
        return AdmissionResult(error.outcome, error.code, error.detail)
    except b2c0.SnapshotFailure as error:
        return AdmissionResult(error.outcome, error.code, error.detail)
    except Exception as error:  # pragma: no cover - fail-closed defect lane
        return AdmissionResult("CheckerFailure", "F0V2B2C1B3-CHECKER", str(error))


def _retained_core(handle: object) -> tuple[object, ValidationEvidence]:
    if (
        type(handle) is not b2c0.AdmittedCoreSnapshot
        or not handle._issued_by(b2c0._CORE_ISSUER)
        or handle.evaluator_fingerprint != EVALUATOR_FINGERPRINT
    ):
        _fail("Refused", "F0V2B2C1B3-R-CORE-AUTHORITY", "Core authority differs")
    summary = dict(handle.structural_summary)
    if (
        summary.get("slice") != "F0-V2B2C1B3"
        or type(summary.get("core")) is not base.InteractiveCore
        or type(summary.get("validation")) is not ValidationEvidence
    ):
        _fail(
            "Refused",
            "F0V2B2C1B3-R-RETAINED-FACTS",
            "retained owner facts differ",
        )
    core = summary["core"]
    profile = k1.decode_content_reference(handle.profile_reference)
    if core_profiled_body(core, profile) != handle.profiled_body:
        _fail("Refused", "F0V2B2C1B3-R-RETAINED-BODY", "retained body differs")
    return core, summary["validation"]


def admit_fresh_protocol(
    core_handle: object, candidate: object, environment: object
) -> AdmissionResult:
    try:
        _retained_core(core_handle)
        if type(candidate) is not b2c0.CanonicalFreshProtocolCandidate:
            _fail(
                "Malformed",
                "F0V2B2C1B3-M-PROTOCOL-REQUEST",
                "Protocol request differs",
            )
        profile, domain, _domain_body = b2c0._strict_profiled_body(
            candidate.profiled_body, "B2C1B3 Fresh Protocol"
        )
        if (
            profile.internal_reference() != core_handle.profile_reference
            or candidate.profile_id.internal_reference()
            != core_handle.profile_reference
        ):
            _fail(
                "KindMismatch",
                "F0V2B2C1B3-K-PROTOCOL-PROFILE",
                "Protocol profile differs",
            )
        core_ref, interpretation = b2c0._record(domain, (0, 1), "Fresh Protocol")
        referenced_core = b2c0._content_ref(core_ref, "Protocol Core")
        if referenced_core.internal_reference() != core_handle.core_reference:
            _fail(
                "Refused",
                "F0V2B2C1B3-R-PROTOCOL-CORE",
                "Protocol names another Core",
            )
        interpretation_case, payload = b2c0._variant(
            interpretation, (0,), "Fresh interpretation"
        )
        if interpretation_case != 0:
            _fail(
                "Refused",
                "F0V2B2C1B3-R-INTERPRETATION",
                "Protocol is not Fresh",
            )
        b2c0._unit(payload, "Fresh payload")
        if (
            type(candidate.asserted_id) is not k1.TypedContentId
            or candidate.asserted_id.subject_kind != base.TARGET_PROTOCOL_KIND
        ):
            _fail(
                "KindMismatch",
                "F0V2B2C1B3-K-PROTOCOL-ID",
                "Protocol ID kind differs",
            )
        try:
            k1.authenticate_content_id(
                candidate.asserted_id,
                candidate.profiled_body,
                environment.prior_meta_preimages,
            )
        except Exception as error:
            _fail("Malformed", "F0V2B2C1B3-M-PROTOCOL-ID", str(error))
        closure = b2c0.snapshot_environment(environment)
        if closure.fingerprint != core_handle.closure.fingerprint:
            _fail("Refused", "F0V2B2C1B3-R-CLOSURE-PAIR", "closure differs")
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
            "F0V2B2C1B3-A-FRESH-ADMITTED",
            "Fresh Protocol is paired to this evaluator and exact Core",
            handle,
        )
    except FamilyFailure as error:
        return AdmissionResult(error.outcome, error.code, error.detail)
    except b2c0.SnapshotFailure as error:
        return AdmissionResult(error.outcome, error.code, error.detail)
    except Exception as error:  # pragma: no cover - fail-closed defect lane
        return AdmissionResult("CheckerFailure", "F0V2B2C1B3-CHECKER", str(error))


def _correlation_value(correlation: object) -> dict[str, Any]:
    if type(correlation) is base.IndependentCorrelation:
        return foundation._v(0)
    if type(correlation) is base.JointCorrelation:
        return foundation._v(
            1,
            {
                0: foundation._module_ref(correlation.group),
                1: correlation.index,
                2: [
                    foundation._ordinal("challenge-ref-body-v0", item)
                    for item in correlation.prior_members
                ],
            },
        )
    _fail("Malformed", "F0V2B2C1B3-M-CORRELATION", "correlation differs")
    raise AssertionError("unreachable")


def _reduction_use_value(value: object) -> dict[str, Any]:
    if type(value) is base.ExclusiveReductionUse:
        return foundation._v(0)
    if type(value) is base.SharedReductionUse:
        return foundation._v(1, foundation._module_ref(value.contract))
    _fail("Malformed", "F0V2B2C1B3-M-REDUCTION-USE", "reduction use differs")
    raise AssertionError("unreachable")


def _claim_source_value(source: object) -> dict[str, Any]:
    if type(source) is InitialClaimSource:
        return foundation._v(
            0, foundation._ordinal("binding-ref-body-v0", source.binding)
        )
    if type(source) is ReductionOutputClaimSource:
        return foundation._v(
            1,
            {
                0: foundation._ordinal("reduction-ref-body-v0", source.reduction),
                1: source.output_ordinal,
            },
        )
    _fail("Malformed", "F0V2B2C1B3-M-CLAIM-SOURCE", "claim source differs")
    raise AssertionError("unreachable")


def _claim_creation_value(
    core: object, validation: ValidationEvidence, source: object
) -> dict[str, Any]:
    if type(source) is InitialClaimSource:
        scope = core.public_bindings[source.binding].scope
        opening = core.scopes[scope].opening
        return foundation._v(
            0,
            {
                0: foundation._ordinal("binding-ref-body-v0", source.binding),
                1: foundation._v(0)
                if opening is None
                else foundation._v(
                    1, foundation._ordinal("occurrence-ref-body-v0", opening)
                ),
            },
        )
    if type(source) is ReductionOutputClaimSource:
        return foundation._v(
            1,
            {
                0: foundation._ordinal(
                    "occurrence-ref-body-v0",
                    validation.reduction_positions[source.reduction],
                ),
                1: foundation._ordinal("reduction-ref-body-v0", source.reduction),
                2: source.output_ordinal,
            },
        )
    _fail("Malformed", "F0V2B2C1B3-M-CLAIM-SOURCE", "claim source differs")
    raise AssertionError("unreachable")


def _effect_value(effect: object) -> dict[str, Any]:
    if type(effect) is base.ProverMessageEffect:
        return foundation._v(
            0,
            {
                0: foundation._module_ref(effect.channel),
                1: foundation._value_type_body(effect.payload_type),
            },
        )
    if type(effect) is base.ChallengeEffect:
        return foundation._v(
            2, foundation._ordinal("challenge-ref-body-v0", effect.challenge)
        )
    if type(effect) is ApplyReductionEffect:
        return foundation._v(
            4, foundation._ordinal("reduction-ref-body-v0", effect.reduction)
        )
    if type(effect) is base.TerminalEffect:
        return foundation._v(
            5, foundation._ordinal("terminal-ref-body-v0", effect.terminal)
        )
    _fail("Unsupported", "F0V2B2C1B3-U-EFFECT", "effect differs")
    raise AssertionError("unreachable")


def _reduction_publication_value(
    requirement: ReductionPublicationRequirement,
) -> dict[int, Any]:
    return {
        0: foundation._ordinal("occurrence-ref-body-v0", requirement.publication),
        1: foundation._v(0)
        if requirement.next_challenge is None
        else foundation._v(
            1,
            foundation._ordinal("challenge-ref-body-v0", requirement.next_challenge),
        ),
    }


def _condition_closure(reference: object) -> tuple[tuple[int, ...], ...]:
    return (_producer_node(reference),)


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
            "F0V2B2C1B3-R-PROTOCOL-AUTHORITY",
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
                0: foundation._ordinal("scope-ref-body-v0", scope_ref),
                1: foundation._v(0)
                if scope.parent is None
                else foundation._v(
                    1,
                    foundation._ordinal("scope-ref-body-v0", scope.parent),
                ),
                2: foundation._v(0)
                if scope.opening is None
                else foundation._v(
                    1,
                    foundation._ordinal("occurrence-ref-body-v0", scope.opening),
                ),
                3: [
                    foundation._ordinal("scope-ref-body-v0", item)
                    for item in validation.paths[scope_ref]
                ],
            }
            for scope_ref, scope in enumerate(core.scopes)
        ],
        2: [
            {
                0: foundation._ordinal("binding-ref-body-v0", binding_ref),
                1: foundation._ordinal("scope-ref-body-v0", binding.scope),
                2: foundation._v(binding.binding_class.value),
                3: foundation._value_ref(binding.value),
                4: foundation._value_type_body(
                    _value_type(core, validation.outputs, binding.value)
                ),
            }
            for binding_ref, binding in enumerate(core.public_bindings)
        ],
    }

    decisions = [
        (occurrence_ref, occurrence)
        for occurrence_ref, occurrence in enumerate(core.occurrences)
        if type(occurrence.effect) is base.ProverMessageEffect
    ]
    decision_rows: list[dict[int, Any]] = []
    read_rows: list[dict[int, Any]] = []
    legal_rows: list[dict[int, Any]] = []
    for occurrence_ref, occurrence in decisions:
        move = foundation._v(
            0, foundation._value_type_body(occurrence.effect.payload_type)
        )
        decision_rows.append(
            {
                0: foundation._ordinal("decision-ref-body-v0", occurrence_ref),
                1: foundation._ordinal("occurrence-ref-body-v0", occurrence_ref),
                2: [
                    foundation._ordinal("scope-ref-body-v0", item)
                    for item in validation.paths[occurrence.scope]
                ],
                3: foundation._guard_body(occurrence.guard),
                4: move,
                5: [
                    foundation._ordinal("decision-ref-body-v0", prior)
                    for prior, _prior_occurrence in decisions
                    if prior < occurrence_ref
                ],
            }
        )
        for input_ref, declaration in enumerate(core.public_inputs):
            read_rows.append(
                {
                    0: foundation._ordinal("decision-ref-body-v0", occurrence_ref),
                    1: foundation._v(
                        1,
                        foundation._ordinal("public-input-ref-body-v0", input_ref),
                    ),
                    2: foundation._value_type_body(declaration.value_type),
                }
            )
        for constant_ref, declaration in enumerate(core.constants):
            read_rows.append(
                {
                    0: foundation._ordinal("decision-ref-body-v0", occurrence_ref),
                    1: foundation._v(
                        0,
                        foundation._ordinal("constant-ref-body-v0", constant_ref),
                    ),
                    2: foundation._value_type_body(declaration.value_type),
                }
            )
        for binding_ref, binding in enumerate(core.public_bindings):
            if _is_ancestor_scope(validation.paths, binding.scope, occurrence.scope):
                read_rows.append(
                    {
                        0: foundation._ordinal("decision-ref-body-v0", occurrence_ref),
                        1: foundation._v(
                            2,
                            foundation._ordinal("binding-ref-body-v0", binding_ref),
                        ),
                        2: foundation._value_type_body(
                            _value_type(core, validation.outputs, binding.value)
                        ),
                    }
                )
        for prior_ref, prior_occurrence in enumerate(core.occurrences[:occurrence_ref]):
            prior_effect = prior_occurrence.effect
            if type(prior_effect) is base.ProverMessageEffect:
                read_rows.append(
                    {
                        0: foundation._ordinal("decision-ref-body-v0", occurrence_ref),
                        1: foundation._v(
                            3,
                            foundation._ordinal("occurrence-ref-body-v0", prior_ref),
                        ),
                        2: foundation._value_type_body(prior_effect.payload_type),
                    }
                )
                read_rows.append(
                    {
                        0: foundation._ordinal("decision-ref-body-v0", occurrence_ref),
                        1: foundation._v(
                            9,
                            foundation._ordinal("decision-ref-body-v0", prior_ref),
                        ),
                        2: foundation._value_type_body(prior_effect.payload_type),
                    }
                )
            elif type(prior_effect) is base.ChallengeEffect:
                read_rows.append(
                    {
                        0: foundation._ordinal("decision-ref-body-v0", occurrence_ref),
                        1: foundation._v(
                            4,
                            foundation._ordinal("occurrence-ref-body-v0", prior_ref),
                        ),
                        2: foundation._value_type_body(
                            core.challenges[prior_effect.challenge].value_type
                        ),
                    }
                )
        legal_rows.append(
            {0: foundation._ordinal("decision-ref-body-v0", occurrence_ref), 1: move}
        )
    read_rows.sort(key=lambda item: codec.encode_value(_READ_SCHEMA, item))
    strategy = {
        0: core_atom,
        1: decision_rows,
        2: foundation._law("core-admission-v0"),
        3: read_rows,
        4: legal_rows,
    }

    challenge_rows: list[dict[int, Any]] = []
    for challenge_ref, challenge in enumerate(core.challenges):
        closure_nodes = {
            node
            for condition in challenge.public_conditions
            for node in _condition_closure(condition)
        }
        challenge_rows.append(
            {
                0: foundation._ordinal("challenge-ref-body-v0", challenge_ref),
                1: foundation._ordinal(
                    "occurrence-ref-body-v0",
                    validation.challenge_positions[challenge_ref],
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
                9: [_pc_value(item) for item in sorted(closure_nodes, key=_pc_key)],
                10: [
                    {
                        0: foundation._ordinal("reduction-ref-body-v0", reduction_ref),
                        1: foundation._ordinal("challenge-ref-body-v0", challenge_ref),
                    }
                    for reduction_ref in validation.reduction_consumers[challenge_ref]
                ],
            }
        )
    public_coin = {
        0: core_atom,
        1: graph,
        2: graph_evidence["eligible"],
        3: [],
        4: challenge_rows,
    }

    value_rows: list[dict[int, Any]] = []
    for input_ref, declaration in enumerate(core.public_inputs):
        value_rows.append(
            {
                0: foundation._value_ref(base.PublicInputRef(input_ref)),
                1: foundation._value_type_body(declaration.value_type),
                2: [],
            }
        )
    for constant_ref, declaration in enumerate(core.constants):
        value_rows.append(
            {
                0: foundation._value_ref(base.ConstantRef(constant_ref)),
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
                    for item in validation.paths[occurrence.scope]
                ],
                2: foundation._guard_body(occurrence.guard),
                3: _effect_value(occurrence.effect),
                4: [
                    foundation._value_type_body(item)
                    for item in validation.outputs[occurrence_ref]
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
        for output_ordinal, output_type in enumerate(
            validation.outputs[occurrence_ref]
        ):
            predecessors: tuple[object, ...] = ()
            if type(occurrence.effect) is base.ChallengeEffect:
                challenge = core.challenges[occurrence.effect.challenge]
                predecessors = challenge.public_conditions
                if type(challenge.correlation) is base.JointCorrelation:
                    predecessors = (
                        *predecessors,
                        *(
                            base.OccurrenceOutputRef(
                                validation.challenge_positions[item], 0
                            )
                            for item in challenge.correlation.prior_members
                        ),
                    )
            value_rows.append(
                {
                    0: foundation._value_ref(
                        base.OccurrenceOutputRef(occurrence_ref, output_ordinal)
                    ),
                    1: foundation._value_type_body(output_type),
                    2: [foundation._value_ref(item) for item in predecessors],
                }
            )
    terminal_rows = [
        {
            0: foundation._ordinal("terminal-ref-body-v0", terminal_ref),
            1: foundation._v(terminal.verdict.value),
            2: [foundation._value_ref(item) for item in terminal.public_outputs],
            3: [],
            4: [
                {
                    0: foundation._ordinal("claim-ref-body-v0", disposition.claim),
                    1: foundation._v(disposition.disposition.value),
                }
                for disposition in terminal.claim_dispositions
            ],
            5: foundation._ordinal(
                "occurrence-ref-body-v0",
                validation.terminal_positions[terminal_ref],
            ),
        }
        for terminal_ref, terminal in enumerate(core.terminals)
    ]
    effect = {
        0: core_atom,
        1: occurrence_rows,
        2: value_rows,
        3: message_rows,
        4: [],
        5: [],
        6: terminal_rows,
        7: [],
    }

    claim_rows: list[dict[int, Any]] = []
    for claim_ref, claim in enumerate(core.claims):
        uses: list[dict[str, Any]] = []
        for kind, occurrence_ref, owner_ref, ordinal in sorted(
            validation.claim_uses[claim_ref],
            key=lambda item: (item[1], item[0], item[3]),
        ):
            if kind == "reduction":
                uses.append(
                    foundation._v(
                        0,
                        {
                            0: foundation._ordinal(
                                "occurrence-ref-body-v0", occurrence_ref
                            ),
                            1: foundation._ordinal("reduction-ref-body-v0", owner_ref),
                            2: ordinal,
                        },
                    )
                )
            else:
                uses.append(
                    foundation._v(
                        1,
                        {
                            0: foundation._ordinal(
                                "occurrence-ref-body-v0", occurrence_ref
                            ),
                            1: foundation._ordinal("terminal-ref-body-v0", owner_ref),
                            2: ordinal,
                        },
                    )
                )
        claim_rows.append(
            {
                0: foundation._ordinal("claim-ref-body-v0", claim_ref),
                1: foundation._module_ref(claim.contract),
                2: foundation._ordinal("scope-ref-body-v0", claim.scope),
                3: foundation._v(claim.usage.value),
                4: _claim_source_value(claim.source),
                5: _claim_creation_value(core, validation, claim.source),
                6: uses,
            }
        )
    reduction_rows = [
        {
            0: foundation._ordinal("reduction-ref-body-v0", reduction_ref),
            1: foundation._module_ref(reduction.contract),
            2: foundation._ordinal("scope-ref-body-v0", reduction.scope),
            3: foundation._ordinal(
                "occurrence-ref-body-v0",
                validation.reduction_positions[reduction_ref],
            ),
            4: [
                foundation._ordinal("claim-ref-body-v0", item)
                for item in reduction.input_claims
            ],
            5: [foundation._value_ref(item) for item in reduction.side_inputs],
            6: [
                foundation._ordinal("challenge-ref-body-v0", item)
                for item in reduction.required_challenges
            ],
            7: [
                _reduction_publication_value(item)
                for item in reduction.required_publications
            ],
            8: [foundation._module_ref(item) for item in reduction.output_contracts],
        }
        for reduction_ref, reduction in enumerate(core.reductions)
    ]
    disposition_rows = [
        {
            0: foundation._ordinal(
                "occurrence-ref-body-v0",
                validation.terminal_positions[terminal_ref],
            ),
            1: foundation._ordinal("terminal-ref-body-v0", terminal_ref),
            2: foundation._ordinal("claim-ref-body-v0", disposition.claim),
            3: foundation._v(disposition.disposition.value),
        }
        for terminal_ref, terminal in enumerate(core.terminals)
        for disposition in terminal.claim_dispositions
    ]
    claim_reduction = {
        0: core_atom,
        1: claim_rows,
        2: reduction_rows,
        3: disposition_rows,
    }

    resolver_rows = [
        {
            0: foundation._ordinal("challenge-ref-body-v0", challenge_ref),
            1: foundation._ordinal(
                "occurrence-ref-body-v0",
                validation.challenge_positions[challenge_ref],
            ),
            2: foundation._value_type_body(challenge.value_type),
            3: foundation._module_ref(challenge.domain),
            4: foundation._module_ref(challenge.fresh_law),
            5: [foundation._value_ref(item) for item in challenge.public_conditions],
            6: [
                foundation._ordinal("challenge-ref-body-v0", item)
                for item in (
                    challenge.correlation.prior_members
                    if type(challenge.correlation) is base.JointCorrelation
                    else ()
                )
            ],
        }
        for challenge_ref, challenge in enumerate(core.challenges)
    ]
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
        1: [
            {
                0: foundation._ordinal("challenge-ref-body-v0", challenge_ref),
                1: foundation._ordinal(
                    "occurrence-ref-body-v0",
                    validation.challenge_positions[challenge_ref],
                ),
                2: foundation._value_type_body(challenge.value_type),
            }
            for challenge_ref, challenge in enumerate(core.challenges)
        ],
        2: [],
        3: [
            {
                0: foundation._ordinal("terminal-ref-body-v0", terminal_ref),
                1: foundation._ordinal(
                    "occurrence-ref-body-v0",
                    validation.terminal_positions[terminal_ref],
                ),
                2: foundation._v(terminal.verdict.value),
                3: [
                    foundation._value_type_body(
                        _value_type(core, validation.outputs, item)
                    )
                    for item in terminal.public_outputs
                ],
            }
            for terminal_ref, terminal in enumerate(core.terminals)
        ],
    }
    execution = {
        0: protocol_atom,
        1: core_atom,
        2: foundation._v(0),
        3: foundation._law("core-admission-v0"),
        4: resolver_rows,
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
        "ClaimReductionView": claim_reduction,
        "ExecutionView": execution,
    }


def _nominal(symbol: str) -> object:
    return _record(k1.Symbol(symbol))


def _catalog(kind: str, values: tuple[object, ...]) -> object:
    return _record(k1.Symbol(kind), _seq(values))


def protocol_module() -> object:
    catalogs = (
        _catalog("pir.challenge-domain", (_nominal("bounded-z3-domain"),)),
        _catalog(
            "pir.challenge-sharing-contract",
            (_nominal("bounded-shared-reduction-coin"),),
        ),
        _catalog(
            "pir.claim-contract",
            (
                _nominal("bounded-input-claim"),
                _nominal("bounded-output-claim"),
            ),
        ),
        _catalog("pir.coin-correlation-group", (_nominal("bounded-joint-group"),)),
        _catalog(
            "pir.message-channel",
            (_nominal("round-publication"), _nominal("response-publication")),
        ),
        _catalog("pir.public-coin-law", (_nominal("fresh-uniform-z3"),)),
        _catalog(
            "pir.reduction-contract",
            (_nominal("bounded-reduction-a"), _nominal("bounded-reduction-b")),
        ),
    )
    return k1.SemanticModuleCandidate(
        k1.Symbol("f0v2b2c1b3.claim-reduction-fixture"),
        (),
        _seq(catalogs),
    )


def identity_algorithm(name: str, value_type: object) -> object:
    return k1.CanonicalAlgorithm(
        k1.Symbol(name), (value_type,), k1.Variable(0, value_type)
    )


def _environment(
    core: object, module: object, algorithms: tuple[object, ...] = ()
) -> object:
    fixture = base.make_fixture()
    algorithm_map = {item.identity: item for item in algorithms}
    _algorithm_ids, contract_ids = _ordinary_references(core)
    contract = k1.DEFAULT_EVALUATION_CONTRACT
    if set(contract_ids) - {contract.identity}:
        raise AssertionError("fixture uses an unexpected evaluation contract")
    return base.Environment(
        fixture.environment.profile_id,
        MappingProxyType(dict(fixture.environment.profile_preimages)),
        MappingProxyType({module.identity: module}),
        MappingProxyType(algorithm_map),
        MappingProxyType(
            {identifier: MappingProxyType({}) for identifier in algorithm_map}
        ),
        MappingProxyType({contract.identity: contract} if contract_ids else {}),
    )


def _used_modules(core: object) -> tuple[object, ...]:
    return tuple(
        sorted(
            {reference.module for reference in _module_references(core)},
            key=lambda item: item.internal_reference(),
        )
    )


def _assemble(
    module: object,
    *,
    public_inputs: tuple[object, ...],
    bindings: tuple[object, ...],
    challenges: tuple[object, ...] = (),
    claims: tuple[object, ...] = (),
    reductions: tuple[object, ...] = (),
    terminals: tuple[object, ...],
    occurrences: tuple[object, ...],
    algorithms: tuple[object, ...] = (),
) -> tuple[object, object]:
    provisional = base.InteractiveCore(
        (),
        public_inputs,
        (),
        (),
        (),
        (base.ScopeDecl(None, None),),
        bindings,
        challenges,
        (),
        (),
        claims,
        reductions,
        terminals,
        occurrences,
    )
    core = replace(provisional, used_modules=_used_modules(provisional))
    environment = _environment(core, module, algorithms)
    return environment, make_candidate(core, environment.profile_id)


def fixtures() -> dict[str, tuple[object, object]]:
    """Return the five exact positive claim/reduction/challenge carriers."""

    module = protocol_module()
    module_id = module.identity
    claim_a = base.ModuleDeclarationRef(module_id, "pir.claim-contract", 0)
    claim_b = base.ModuleDeclarationRef(module_id, "pir.claim-contract", 1)
    reduction_a = base.ModuleDeclarationRef(module_id, "pir.reduction-contract", 0)
    reduction_b = base.ModuleDeclarationRef(module_id, "pir.reduction-contract", 1)
    domain = base.ModuleDeclarationRef(module_id, "pir.challenge-domain", 0)
    fresh = base.ModuleDeclarationRef(module_id, "pir.public-coin-law", 0)
    joint = base.ModuleDeclarationRef(module_id, "pir.coin-correlation-group", 0)
    sharing = base.ModuleDeclarationRef(module_id, "pir.challenge-sharing-contract", 0)
    channel_a = base.ModuleDeclarationRef(module_id, "pir.message-channel", 0)
    channel_b = base.ModuleDeclarationRef(module_id, "pir.message-channel", 1)
    statement_z3 = (
        base.PublicBindingDecl(0, base.BindingClass.STATEMENT, base.PublicInputRef(0)),
    )

    initial_claim = ClaimDecl(claim_a, 0, base.ClaimUsage.LINEAR, InitialClaimSource(0))
    initial_terminal = base.TerminalDecl(
        base.TerminalVerdict.ACCEPT,
        (),
        (),
        (base.ClaimDispositionEntry(0, base.ClaimDisposition.CONSUME),),
    )
    initial = _assemble(
        module,
        public_inputs=(base.InputDecl(base.Z3),),
        bindings=statement_z3,
        claims=(initial_claim,),
        terminals=(initial_terminal,),
        occurrences=(
            base.OccurrenceDecl(0, base.AlwaysGuard(), base.TerminalEffect(0)),
        ),
    )

    source_claim = ClaimDecl(claim_a, 0, base.ClaimUsage.LINEAR, InitialClaimSource(0))
    output_claim = ClaimDecl(
        claim_b,
        0,
        base.ClaimUsage.REUSABLE,
        ReductionOutputClaimSource(0, 0),
    )
    output_reduction = ReductionDecl(
        reduction_a,
        0,
        (0,),
        (),
        (),
        (),
        (claim_b,),
    )
    output_terminal = base.TerminalDecl(
        base.TerminalVerdict.ACCEPT,
        (),
        (),
        (base.ClaimDispositionEntry(1, base.ClaimDisposition.DISCHARGE),),
    )
    reduction_output = _assemble(
        module,
        public_inputs=(base.InputDecl(base.Z3),),
        bindings=statement_z3,
        claims=(source_claim, output_claim),
        reductions=(output_reduction,),
        terminals=(output_terminal,),
        occurrences=(
            base.OccurrenceDecl(0, base.AlwaysGuard(), ApplyReductionEffect(0)),
            base.OccurrenceDecl(0, base.AlwaysGuard(), base.TerminalEffect(0)),
        ),
    )

    guard_algorithm = identity_algorithm("F0V2B2C1B3BoolGuard", k1.BOOL)
    guard = base.EvaluateGuard(
        guard_algorithm.identity,
        k1.DEFAULT_EVALUATION_CONTRACT.identity,
        (base.PublicInputRef(0),),
    )
    guarded_claim = ClaimDecl(
        claim_a, 0, base.ClaimUsage.REUSABLE, InitialClaimSource(0)
    )
    round_challenge = base.ChallengeDecl(
        0,
        base.Z3,
        domain,
        fresh,
        base.IndependentCorrelation(),
        base.ExclusiveReductionUse(),
        (base.PublicInputRef(0),),
    )
    publication_reduction = ReductionDecl(
        reduction_a,
        0,
        (0,),
        (base.OccurrenceOutputRef(0, 0), base.OccurrenceOutputRef(2, 0)),
        (0,),
        (
            ReductionPublicationRequirement(0, 0),
            ReductionPublicationRequirement(2, None),
        ),
        (),
    )
    publication_terminal = base.TerminalDecl(
        base.TerminalVerdict.ACCEPT,
        (),
        (),
        (base.ClaimDispositionEntry(0, base.ClaimDisposition.DISCHARGE),),
    )
    publication = _assemble(
        module,
        public_inputs=(base.InputDecl(k1.BOOL),),
        bindings=(
            base.PublicBindingDecl(
                0, base.BindingClass.STATEMENT, base.PublicInputRef(0)
            ),
        ),
        challenges=(round_challenge,),
        claims=(guarded_claim,),
        reductions=(publication_reduction,),
        terminals=(publication_terminal,),
        occurrences=(
            base.OccurrenceDecl(0, guard, base.ProverMessageEffect(channel_a, k1.BOOL)),
            base.OccurrenceDecl(0, guard, base.ChallengeEffect(0)),
            base.OccurrenceDecl(0, guard, base.ProverMessageEffect(channel_b, k1.BOOL)),
            base.OccurrenceDecl(0, guard, ApplyReductionEffect(0)),
            base.OccurrenceDecl(0, base.AlwaysGuard(), base.TerminalEffect(0)),
        ),
        algorithms=(guard_algorithm,),
    )

    first_joint = base.ChallengeDecl(
        0,
        base.Z3,
        domain,
        fresh,
        base.JointCorrelation(joint, 0, ()),
        base.ExclusiveReductionUse(),
        (base.PublicInputRef(0),),
    )
    second_joint = replace(
        first_joint, correlation=base.JointCorrelation(joint, 1, (0,))
    )
    joint_case = _assemble(
        module,
        public_inputs=(base.InputDecl(base.Z3),),
        bindings=statement_z3,
        challenges=(first_joint, second_joint),
        terminals=(base.TerminalDecl(base.TerminalVerdict.ACCEPT, (), (), ()),),
        occurrences=(
            base.OccurrenceDecl(0, base.AlwaysGuard(), base.ChallengeEffect(0)),
            base.OccurrenceDecl(0, base.AlwaysGuard(), base.ChallengeEffect(1)),
            base.OccurrenceDecl(0, base.AlwaysGuard(), base.TerminalEffect(0)),
        ),
    )

    shared_claim = ClaimDecl(
        claim_a, 0, base.ClaimUsage.REUSABLE, InitialClaimSource(0)
    )
    shared_challenge = base.ChallengeDecl(
        0,
        base.Z3,
        domain,
        fresh,
        base.IndependentCorrelation(),
        base.SharedReductionUse(sharing),
        (),
    )
    shared_reductions = (
        ReductionDecl(reduction_a, 0, (0,), (), (0,), (), ()),
        ReductionDecl(reduction_b, 0, (0,), (), (0,), (), ()),
    )
    shared_case = _assemble(
        module,
        public_inputs=(base.InputDecl(base.Z3),),
        bindings=statement_z3,
        challenges=(shared_challenge,),
        claims=(shared_claim,),
        reductions=shared_reductions,
        terminals=(
            base.TerminalDecl(
                base.TerminalVerdict.ACCEPT,
                (),
                (),
                (base.ClaimDispositionEntry(0, base.ClaimDisposition.DISCHARGE),),
            ),
        ),
        occurrences=(
            base.OccurrenceDecl(0, base.AlwaysGuard(), base.ChallengeEffect(0)),
            base.OccurrenceDecl(0, base.AlwaysGuard(), ApplyReductionEffect(0)),
            base.OccurrenceDecl(0, base.AlwaysGuard(), ApplyReductionEffect(1)),
            base.OccurrenceDecl(0, base.AlwaysGuard(), base.TerminalEffect(0)),
        ),
    )
    return {
        "claim-initial-linear": initial,
        "claim-reduction-output-reusable": reduction_output,
        "reduction-publication-before-after": publication,
        "joint-challenge-group": joint_case,
        "shared-challenge-consumers": shared_case,
    }


def mutate_core(name: str, mutation: str) -> tuple[object, object]:
    """Return a freshly authenticated semantic mutation of one family."""

    environment, candidate = fixtures()[name]
    _profile, domain, _domain_body = b2c0._strict_profiled_body(
        candidate.profiled_body, "B2C1B3 mutation source"
    )
    core = decode_core(domain)
    if mutation == "claim-source-binding":
        claims = (replace(core.claims[0], source=InitialClaimSource(1)),)
        core = replace(core, claims=claims)
    elif mutation == "claim-source-class":
        bindings = (
            replace(
                core.public_bindings[0],
                binding_class=base.BindingClass.SESSION_CONTEXT,
            ),
        )
        core = replace(core, public_bindings=bindings)
    elif mutation == "claim-contract-kind":
        wrong = replace(
            core.claims[0].contract, declaration_kind="pir.reduction-contract"
        )
        core = replace(core, claims=(replace(core.claims[0], contract=wrong),))
    elif mutation == "output-contract-mismatch":
        claims = list(core.claims)
        claims[1] = replace(claims[1], contract=claims[0].contract)
        core = replace(core, claims=tuple(claims))
    elif mutation == "output-claim-missing":
        core = replace(core, claims=core.claims[:1])
    elif mutation == "output-claim-duplicate":
        core = replace(core, claims=(*core.claims, core.claims[1]))
    elif mutation == "reduction-empty-input":
        reductions = list(core.reductions)
        reductions[0] = replace(reductions[0], input_claims=())
        core = replace(core, reductions=tuple(reductions))
    elif mutation == "reduction-missing-backlink":
        occurrences = list(core.occurrences)
        occurrences[0] = replace(occurrences[0], effect=base.TerminalEffect(0))
        core = replace(core, occurrences=tuple(occurrences))
    elif mutation == "reduction-duplicate-backlink":
        occurrences = list(core.occurrences)
        occurrences[-1] = replace(occurrences[-1], effect=ApplyReductionEffect(0))
        core = replace(core, occurrences=tuple(occurrences))
    elif mutation == "reduction-scope":
        reductions = list(core.reductions)
        reductions[0] = replace(reductions[0], scope=1)
        core = replace(core, reductions=tuple(reductions))
    elif mutation == "output-claim-cycle":
        reductions = list(core.reductions)
        reductions[0] = replace(reductions[0], input_claims=(1,))
        core = replace(core, reductions=tuple(reductions))
    elif mutation == "publication-closure":
        reduction = replace(
            core.reductions[0],
            required_publications=core.reductions[0].required_publications[:1],
        )
        core = replace(core, reductions=(reduction,))
    elif mutation == "publication-kind":
        requirements = list(core.reductions[0].required_publications)
        requirements[0] = replace(requirements[0], publication=1)
        core = replace(
            core,
            reductions=(
                replace(core.reductions[0], required_publications=tuple(requirements)),
            ),
        )
    elif mutation == "publication-order":
        core = replace(
            core,
            reductions=(
                replace(
                    core.reductions[0],
                    required_publications=tuple(
                        reversed(core.reductions[0].required_publications)
                    ),
                ),
            ),
        )
    elif mutation == "last-challenge":
        requirements = list(core.reductions[0].required_publications)
        requirements[0] = replace(requirements[0], next_challenge=None)
        core = replace(
            core,
            reductions=(
                replace(core.reductions[0], required_publications=tuple(requirements)),
            ),
        )
    elif mutation == "challenge-duplicate":
        core = replace(
            core,
            reductions=(replace(core.reductions[0], required_challenges=(0, 0)),),
        )
    elif mutation == "guard-implication":
        occurrences = list(core.occurrences)
        occurrences[3] = replace(occurrences[3], guard=base.AlwaysGuard())
        core = replace(core, occurrences=tuple(occurrences))
    elif mutation == "joint-index":
        challenges = list(core.challenges)
        challenges[1] = replace(
            challenges[1],
            correlation=replace(challenges[1].correlation, index=2),
        )
        core = replace(core, challenges=tuple(challenges))
    elif mutation == "joint-prior":
        challenges = list(core.challenges)
        challenges[1] = replace(
            challenges[1],
            correlation=replace(challenges[1].correlation, prior_members=()),
        )
        core = replace(core, challenges=tuple(challenges))
    elif mutation == "joint-type":
        challenges = list(core.challenges)
        challenges[1] = replace(challenges[1], value_type=k1.BOOL)
        core = replace(core, challenges=tuple(challenges))
    elif mutation == "shared-consumer-count":
        reductions = list(core.reductions)
        reductions[1] = replace(reductions[1], required_challenges=())
        core = replace(core, reductions=tuple(reductions))
    elif mutation == "exclusive-consumer-count":
        challenges = (
            replace(
                core.challenges[0],
                reduction_use=base.ExclusiveReductionUse(),
            ),
        )
        core = replace(core, challenges=challenges)
    elif mutation == "linear-double-use":
        core = replace(
            core,
            claims=(replace(core.claims[0], usage=base.ClaimUsage.LINEAR),),
        )
    elif mutation == "terminal-claim-closure":
        core = replace(
            core,
            terminals=(replace(core.terminals[0], claim_dispositions=()),),
        )
    elif mutation == "terminal-disposition-duplicate":
        entry = core.terminals[0].claim_dispositions[0]
        core = replace(
            core,
            terminals=(replace(core.terminals[0], claim_dispositions=(entry, entry)),),
        )
    else:
        raise KeyError(mutation)
    return environment, make_candidate(core, environment.profile_id)
