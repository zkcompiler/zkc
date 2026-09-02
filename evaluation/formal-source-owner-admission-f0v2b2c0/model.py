#!/usr/bin/env python3
"""Canonical-byte admission substrate for the F0-V2B2C isolation program.

This is a bounded research model.  It deliberately reuses the F1-R1B target
evaluator for the semantic predicates that evaluator already implements, but
it does not retain that evaluator's mutable process-local handle.  Authority
is minted only over a strict canonical-byte snapshot and an authenticated,
immutable dependency-closure snapshot.
"""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import importlib.util
from pathlib import Path
import pickle
import sys
from types import MappingProxyType, ModuleType
from typing import Any


ROOT = Path(__file__).resolve().parents[2]
BASE_MODEL = ROOT / "evaluation/formal-source-target-core-f1r1b/reference_model.py"
EVALUATOR_FINGERPRINT = hashlib.sha256(
    b"zkc.f0v2b2c0.canonical-byte-owner-admission.v0"
).digest()


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


base = _load_module("_zkc_f0v2b2c0_base_owner", BASE_MODEL)
k1 = base.k1


class SnapshotFailure(ValueError):
    """One classified failure at the canonical-byte owner boundary."""

    def __init__(self, outcome: str, code: str, detail: str) -> None:
        super().__init__(detail)
        self.outcome = outcome
        self.code = code
        self.detail = detail


@dataclass(frozen=True, slots=True)
class AdmissionResult:
    outcome: str
    code: str
    detail: str
    handle: object | None = None


@dataclass(frozen=True, slots=True)
class CanonicalCoreCandidate:
    asserted_id: object
    profile_id: object
    profiled_body: bytes


@dataclass(frozen=True, slots=True)
class CanonicalFreshProtocolCandidate:
    asserted_id: object
    profile_id: object
    profiled_body: bytes


@dataclass(frozen=True, slots=True)
class ClosureSnapshot:
    prior_meta_preimages: tuple[bytes, bytes, bytes]
    profile_preimages: tuple[tuple[bytes, bytes], ...]
    module_preimages: tuple[tuple[bytes, bytes], ...]
    algorithm_preimages: tuple[tuple[bytes, bytes], ...]
    contract_preimages: tuple[tuple[bytes, bytes], ...]

    @property
    def fingerprint(self) -> bytes:
        digest = hashlib.sha256()
        digest.update(b"zkc.f0v2b2c0.closure-snapshot.v0")
        for category in (
            self.prior_meta_preimages,
            self.profile_preimages,
            self.module_preimages,
            self.algorithm_preimages,
            self.contract_preimages,
        ):
            digest.update(len(category).to_bytes(8, "big"))
            for item in category:
                values = item if type(item) is tuple else (item,)
                for value in values:
                    digest.update(len(value).to_bytes(8, "big"))
                    digest.update(value)
        return digest.digest()


_CORE_ISSUER = object()
_PROTOCOL_ISSUER = object()


class AdmittedCoreSnapshot:
    """Live authority over an immutable, alias-free canonical Core snapshot.

    This is intentionally not a dataclass.  ``dataclasses.replace`` can copy a
    frozen dataclass's private mint field while changing another field.  The
    custom carrier has no public reconstruction protocol, no writable
    descriptor, and refuses copy, deepcopy, and pickle under ordinary Python
    operations.
    """

    __slots__ = (
        "__core_reference",
        "__profile_reference",
        "__profiled_body",
        "__domain_body",
        "__closure",
        "__structural_summary",
        "__evaluator_fingerprint",
        "__admission_steps",
        "__issuer",
    )

    def __init__(
        self,
        core_reference: bytes,
        profile_reference: bytes,
        profiled_body: bytes,
        domain_body: bytes,
        closure: ClosureSnapshot,
        structural_summary: tuple[tuple[str, object], ...],
        evaluator_fingerprint: bytes,
        admission_steps: tuple[int, ...],
        mint: object,
    ) -> None:
        if mint is not _CORE_ISSUER:
            raise TypeError("only the B2C0 owner evaluator may mint a Core snapshot")
        values = (
            ("_AdmittedCoreSnapshot__core_reference", core_reference),
            ("_AdmittedCoreSnapshot__profile_reference", profile_reference),
            ("_AdmittedCoreSnapshot__profiled_body", profiled_body),
            ("_AdmittedCoreSnapshot__domain_body", domain_body),
            ("_AdmittedCoreSnapshot__closure", closure),
            ("_AdmittedCoreSnapshot__structural_summary", structural_summary),
            ("_AdmittedCoreSnapshot__evaluator_fingerprint", evaluator_fingerprint),
            ("_AdmittedCoreSnapshot__admission_steps", admission_steps),
            ("_AdmittedCoreSnapshot__issuer", mint),
        )
        for name, value in values:
            object.__setattr__(self, name, value)

    @property
    def core_reference(self) -> bytes:
        return self.__core_reference

    @property
    def profile_reference(self) -> bytes:
        return self.__profile_reference

    @property
    def profiled_body(self) -> bytes:
        return self.__profiled_body

    @property
    def domain_body(self) -> bytes:
        return self.__domain_body

    @property
    def closure(self) -> ClosureSnapshot:
        return self.__closure

    @property
    def structural_summary(self) -> tuple[tuple[str, object], ...]:
        return self.__structural_summary

    @property
    def evaluator_fingerprint(self) -> bytes:
        return self.__evaluator_fingerprint

    @property
    def admission_steps(self) -> tuple[int, ...]:
        return self.__admission_steps

    def _issued_by(self, mint: object) -> bool:
        return self.__issuer is mint

    def __setattr__(self, _name: str, _value: object) -> None:
        raise TypeError("an admitted Core snapshot is immutable")

    def __copy__(self) -> object:
        raise TypeError("an admitted Core snapshot is noncopyable")

    def __deepcopy__(self, _memo: object) -> object:
        raise TypeError("an admitted Core snapshot is noncopyable")

    def __reduce_ex__(self, _protocol: int) -> object:
        raise TypeError("an admitted Core snapshot is process-local authority")


class AdmittedFreshProtocolSnapshot:
    """Fresh Protocol authority paired to one exact admitted Core snapshot."""

    __slots__ = (
        "__protocol_reference",
        "__profile_reference",
        "__profiled_body",
        "__core_handle",
        "__closure_fingerprint",
        "__evaluator_fingerprint",
        "__issuer",
    )

    def __init__(
        self,
        protocol_reference: bytes,
        profile_reference: bytes,
        profiled_body: bytes,
        core_handle: AdmittedCoreSnapshot,
        closure_fingerprint: bytes,
        evaluator_fingerprint: bytes,
        mint: object,
    ) -> None:
        if mint is not _PROTOCOL_ISSUER:
            raise TypeError(
                "only the B2C0 owner evaluator may mint a Protocol snapshot"
            )
        values = (
            ("_AdmittedFreshProtocolSnapshot__protocol_reference", protocol_reference),
            ("_AdmittedFreshProtocolSnapshot__profile_reference", profile_reference),
            ("_AdmittedFreshProtocolSnapshot__profiled_body", profiled_body),
            ("_AdmittedFreshProtocolSnapshot__core_handle", core_handle),
            (
                "_AdmittedFreshProtocolSnapshot__closure_fingerprint",
                closure_fingerprint,
            ),
            (
                "_AdmittedFreshProtocolSnapshot__evaluator_fingerprint",
                evaluator_fingerprint,
            ),
            ("_AdmittedFreshProtocolSnapshot__issuer", mint),
        )
        for name, value in values:
            object.__setattr__(self, name, value)

    @property
    def protocol_reference(self) -> bytes:
        return self.__protocol_reference

    @property
    def profile_reference(self) -> bytes:
        return self.__profile_reference

    @property
    def profiled_body(self) -> bytes:
        return self.__profiled_body

    @property
    def core_handle(self) -> AdmittedCoreSnapshot:
        return self.__core_handle

    @property
    def closure_fingerprint(self) -> bytes:
        return self.__closure_fingerprint

    @property
    def evaluator_fingerprint(self) -> bytes:
        return self.__evaluator_fingerprint

    def _issued_by(self, mint: object) -> bool:
        return self.__issuer is mint

    def __setattr__(self, _name: str, _value: object) -> None:
        raise TypeError("an admitted Protocol snapshot is immutable")

    def __copy__(self) -> object:
        raise TypeError("an admitted Protocol snapshot is noncopyable")

    def __deepcopy__(self, _memo: object) -> object:
        raise TypeError("an admitted Protocol snapshot is noncopyable")

    def __reduce_ex__(self, _protocol: int) -> object:
        raise TypeError("an admitted Protocol snapshot is process-local authority")


def _fail(outcome: str, code: str, detail: str) -> None:
    raise SnapshotFailure(outcome, code, detail)


def _record(value: object, ordinals: tuple[int, ...], label: str) -> tuple[object, ...]:
    if (
        type(value) is not k1.DatumRecord
        or tuple(ordinal for ordinal, _item in value.fields) != ordinals
    ):
        _fail("Malformed", "F0V2B2C0-M-RECORD", f"{label} has another record shape")
    return tuple(item for _ordinal, item in value.fields)


def _sequence(value: object, label: str) -> tuple[object, ...]:
    if type(value) is not k1.DatumSeq or type(value.values) is not tuple:
        _fail("Malformed", "F0V2B2C0-M-SEQUENCE", f"{label} is not an exact sequence")
    if len(value.values) > base.MAX_LOCAL_ITEMS:
        _fail(
            "DeterministicLimitExceeded",
            "F0V2B2C0-L-SEQUENCE",
            f"{label} crosses the local sequence bound",
        )
    return value.values


def _variant(value: object, cases: tuple[int, ...], label: str) -> tuple[int, object]:
    if type(value) is not k1.DatumVariant or value.case not in cases:
        _fail("Malformed", "F0V2B2C0-M-VARIANT", f"{label} has another variant case")
    return value.case, value.payload


def _unit(value: object, label: str) -> None:
    if type(value) is not k1.Unit:
        _fail("Malformed", "F0V2B2C0-M-UNIT", f"{label} is not Unit")


def _nat(value: object, label: str) -> int:
    if type(value) is not k1.Nat or not 0 <= value.value < 1 << 64:
        _fail("Malformed", "F0V2B2C0-M-NATURAL", f"{label} is not a u64 natural")
    return value.value


def _bytes(value: object, label: str) -> bytes:
    if type(value) is not k1.BytesValue or type(value.value) is not bytes:
        _fail("Malformed", "F0V2B2C0-M-BYTES", f"{label} is not exact bytes")
    return value.value


def _content_ref(value: object, label: str) -> object:
    try:
        return k1.decode_content_reference(_bytes(value, label))
    except Exception as error:
        _fail("Malformed", "F0V2B2C0-M-CONTENT-REF", f"{label}: {error}")
    raise AssertionError("unreachable")


def _decode_schema(value: object, depth: int = 0) -> object:
    if depth > 48:
        _fail("DeterministicLimitExceeded", "F0V2B2C0-L-SCHEMA", "schema is too deep")
    tag, payload = _variant(value, tuple(range(9)), "value schema")
    if tag == 0:
        _unit(payload, "unit schema payload")
        return k1.UnitSchema()
    if tag == 1:
        _unit(payload, "Boolean schema payload")
        return k1.BoolSchema()
    if tag == 2:
        return k1.NatSchema(_nat(payload, "natural schema maximum"))
    if tag == 3:
        lower, upper = _record(payload, (0, 1), "integer schema")
        if type(lower) is not k1.IntValue or type(upper) is not k1.IntValue:
            _fail("Malformed", "F0V2B2C0-M-SCHEMA", "integer bounds have another type")
        return k1.IntSchema(lower.value, upper.value)
    if tag == 4:
        lower, upper = _record(payload, (0, 1), "bytes schema")
        return k1.BytesSchema(
            _nat(lower, "bytes schema minimum"),
            _nat(upper, "bytes schema maximum"),
        )
    if tag == 5:
        return k1.SymbolSchema(_nat(payload, "symbol schema maximum"))
    if tag == 6:
        element, maximum = _record(payload, (0, 1), "sequence schema")
        return k1.SeqSchema(
            _decode_value_type(element, depth + 1),
            _nat(maximum, "sequence schema maximum"),
        )
    entries = _sequence(payload, "aggregate schema entries")
    decoded: list[tuple[int, object]] = []
    for entry in entries:
        ordinal, child = _record(entry, (0, 1), "aggregate schema entry")
        decoded.append(
            (
                _nat(ordinal, "aggregate schema ordinal"),
                _decode_value_type(child, depth + 1),
            )
        )
    pairs = tuple(decoded)
    return k1.RecordSchema(pairs) if tag == 7 else k1.VariantSchema(pairs)


def _decode_value_type(value: object, depth: int = 0) -> object:
    domain_value, schema_value = _record(value, (0, 1), "value type")
    owner_case, owner_payload = _variant(domain_value, (0, 1), "value-domain owner")
    owner_ref, kind, ordinal = _record(owner_payload, (0, 1, 2), "value domain")
    owner_bytes = _bytes(owner_ref, "value-domain owner reference")
    try:
        owner_id = (
            k1.decode_prior_meta_reference(owner_bytes)
            if owner_case == 0
            else k1.decode_content_reference(owner_bytes)
        )
    except Exception as error:
        _fail("Malformed", "F0V2B2C0-M-VALUE-DOMAIN", str(error))
    if type(kind) is not k1.Symbol:
        _fail("Malformed", "F0V2B2C0-M-VALUE-DOMAIN", "domain kind is not a symbol")
    try:
        return k1.ValueType(
            k1.ValueDomain(owner_id, kind, _nat(ordinal, "value-domain ordinal")),
            _decode_schema(schema_value, depth + 1),
        )
    except SnapshotFailure:
        raise
    except Exception as error:
        _fail("Malformed", "F0V2B2C0-M-VALUE-TYPE", str(error))
    raise AssertionError("unreachable")


def _decode_module_ref(value: object) -> object:
    tag, payload = _variant(value, (1,), "module declaration reference")
    assert tag == 1
    module, kind, ordinal = _record(payload, (0, 1, 2), "module declaration")
    if type(kind) is not k1.Symbol:
        _fail("Malformed", "F0V2B2C0-M-MODULE-REF", "declaration kind is not a symbol")
    return base.ModuleDeclarationRef(
        _content_ref(module, "module owner"),
        kind.value,
        _nat(ordinal, "module declaration ordinal"),
    )


def _decode_value_ref(value: object) -> object:
    tag, payload = _variant(value, (0, 1, 2, 3, 4), "value reference")
    if tag < 4:
        ordinal = _nat(payload, "value reference ordinal")
        return (
            base.PublicInputRef,
            base.VerifierPrivateInputRef,
            base.ConstantRef,
            base.DerivedValueRef,
        )[tag](ordinal)
    occurrence, output = _record(payload, (0, 1), "occurrence-output reference")
    return base.OccurrenceOutputRef(
        _nat(occurrence, "occurrence reference"),
        _nat(output, "output ordinal"),
    )


def _decode_guard(value: object) -> object:
    tag, payload = _variant(value, (0, 1), "guard")
    if tag == 0:
        _unit(payload, "Always guard payload")
        return base.AlwaysGuard()
    algorithm, contract, inputs = _record(payload, (0, 1, 2), "Evaluate guard")
    return base.EvaluateGuard(
        _content_ref(algorithm, "guard algorithm"),
        _content_ref(contract, "guard contract"),
        tuple(_decode_value_ref(item) for item in _sequence(inputs, "guard inputs")),
    )


def _decode_baseline_effect(value: object) -> object:
    tag, payload = _variant(value, tuple(range(8)), "Core effect")
    if tag == 0:
        channel, payload_type = _record(payload, (0, 1), "Prover message")
        return base.ProverMessageEffect(
            _decode_module_ref(channel), _decode_value_type(payload_type)
        )
    if tag == 2:
        return base.ChallengeEffect(_nat(payload, "challenge backlink"))
    if tag == 3:
        return base.CheckEffect(_nat(payload, "check backlink"))
    if tag == 5:
        return base.TerminalEffect(_nat(payload, "terminal backlink"))
    _fail(
        "Unsupported",
        "F0V2B2C0-U-CONSTRUCTOR",
        f"Core effect tag {tag} belongs to the B2C1 constructor extension",
    )
    raise AssertionError("unreachable")


def decode_baseline_core(domain: object) -> object:
    """Strictly form the F1-R1B-supported target carrier from one K1 datum."""

    fields = _record(domain, tuple(range(14)), "InteractiveCore")
    sequences = tuple(
        _sequence(value, f"InteractiveCore field {ordinal}")
        for ordinal, value in enumerate(fields)
    )
    used_modules = tuple(_content_ref(item, "used module") for item in sequences[0])
    public_inputs = tuple(
        base.InputDecl(_decode_value_type(_record(item, (0,), "public input")[0]))
        for item in sequences[1]
    )
    private_inputs = tuple(
        base.InputDecl(
            _decode_value_type(_record(item, (0,), "verifier-private input")[0])
        )
        for item in sequences[2]
    )
    constants = []
    for item in sequences[3]:
        value_type, datum = _record(item, (0, 1), "typed constant")
        decoded_type = _decode_value_type(value_type)
        try:
            admitted = k1.admit_value(decoded_type, datum)
        except Exception as error:
            _fail("Refused", "F0V2B2C0-R-CONSTANT", str(error))
        constants.append(base.TypedConstantDecl(decoded_type, admitted))
    derived_values = []
    for item in sequences[4]:
        algorithm, contract, inputs, result_type = _record(
            item, (0, 1, 2, 3), "derived value"
        )
        derived_values.append(
            base.DerivedValueDecl(
                _content_ref(algorithm, "derived algorithm"),
                _content_ref(contract, "derived contract"),
                tuple(
                    _decode_value_ref(value)
                    for value in _sequence(inputs, "derived inputs")
                ),
                _decode_value_type(result_type),
            )
        )
    scopes = []
    for item in sequences[5]:
        parent, opening = _record(item, (0, 1), "scope")
        parent_tag, parent_payload = _variant(parent, (0, 1), "scope parent")
        opening_tag, opening_payload = _variant(opening, (0, 1), "scope opening")
        if parent_tag == 0:
            _unit(parent_payload, "absent scope parent")
        if opening_tag == 0:
            _unit(opening_payload, "initial scope opening")
        scopes.append(
            base.ScopeDecl(
                None if parent_tag == 0 else _nat(parent_payload, "scope parent"),
                None
                if opening_tag == 0
                else _nat(opening_payload, "scope opening occurrence"),
            )
        )
    bindings = []
    for item in sequences[6]:
        scope, binding_class, value = _record(item, (0, 1, 2), "public binding")
        class_tag, class_payload = _variant(binding_class, (0, 1, 2), "binding class")
        _unit(class_payload, "binding-class payload")
        bindings.append(
            base.PublicBindingDecl(
                _nat(scope, "binding scope"),
                base.BindingClass(class_tag),
                _decode_value_ref(value),
            )
        )
    challenges = []
    for item in sequences[7]:
        values = _record(item, tuple(range(7)), "challenge")
        correlation_tag, correlation_payload = _variant(
            values[4], (0, 1), "coin correlation"
        )
        if correlation_tag == 0:
            _unit(correlation_payload, "independent correlation")
            correlation: object = base.IndependentCorrelation()
        else:
            group, index, prior = _record(
                correlation_payload, (0, 1, 2), "joint correlation"
            )
            correlation = base.JointCorrelation(
                _decode_module_ref(group),
                _nat(index, "joint index"),
                tuple(
                    _nat(member, "prior joint member")
                    for member in _sequence(prior, "prior joint members")
                ),
            )
        use_tag, use_payload = _variant(values[5], (0, 1), "reduction use")
        if use_tag == 0:
            _unit(use_payload, "exclusive reduction use")
            reduction_use: object = base.ExclusiveReductionUse()
        else:
            reduction_use = base.SharedReductionUse(_decode_module_ref(use_payload))
        challenges.append(
            base.ChallengeDecl(
                _nat(values[0], "challenge scope"),
                _decode_value_type(values[1]),
                _decode_module_ref(values[2]),
                _decode_module_ref(values[3]),
                correlation,
                reduction_use,
                tuple(
                    _decode_value_ref(condition)
                    for condition in _sequence(values[6], "challenge conditions")
                ),
            )
        )
    if sequences[8] or sequences[11]:
        _fail(
            "Unsupported",
            "F0V2B2C0-U-CONSTRUCTOR",
            "Oracle and Reduction bodies belong to the B2C1 extension",
        )
    checks = []
    for item in sequences[9]:
        algorithm, contract, inputs = _record(item, (0, 1, 2), "check")
        checks.append(
            base.CheckDecl(
                _content_ref(algorithm, "check algorithm"),
                _content_ref(contract, "check contract"),
                tuple(
                    _decode_value_ref(value)
                    for value in _sequence(inputs, "check inputs")
                ),
            )
        )
    claims = []
    for item in sequences[10]:
        contract, scope, usage, source = _record(item, (0, 1, 2, 3), "claim")
        usage_tag, usage_payload = _variant(usage, (0, 1), "claim usage")
        _unit(usage_payload, "claim usage payload")
        source_tag, source_payload = _variant(source, (0, 1), "claim source")
        if source_tag != 0:
            _fail(
                "Unsupported",
                "F0V2B2C0-U-CONSTRUCTOR",
                "Reduction-output claims belong to the B2C1 extension",
            )
        claims.append(
            base.ClaimDecl(
                _decode_module_ref(contract),
                _nat(scope, "claim scope"),
                base.ClaimUsage(usage_tag),
                _nat(source_payload, "claim source binding"),
            )
        )
    terminals = []
    for item in sequences[12]:
        verdict, outputs, checks_value, dispositions = _record(
            item, (0, 1, 2, 3), "terminal"
        )
        verdict_tag, verdict_payload = _variant(verdict, (0, 1, 2), "verdict")
        _unit(verdict_payload, "verdict payload")
        disposition_values = []
        for entry in _sequence(dispositions, "terminal dispositions"):
            claim, disposition = _record(entry, (0, 1), "claim disposition")
            disposition_tag, disposition_payload = _variant(
                disposition, (0, 1), "claim disposition"
            )
            _unit(disposition_payload, "claim-disposition payload")
            disposition_values.append(
                base.ClaimDispositionEntry(
                    _nat(claim, "disposed claim"),
                    base.ClaimDisposition(disposition_tag),
                )
            )
        terminals.append(
            base.TerminalDecl(
                base.TerminalVerdict(verdict_tag),
                tuple(
                    _decode_value_ref(value)
                    for value in _sequence(outputs, "terminal outputs")
                ),
                tuple(
                    _nat(check, "terminal check")
                    for check in _sequence(checks_value, "terminal checks")
                ),
                tuple(disposition_values),
            )
        )
    occurrences = []
    for item in sequences[13]:
        scope, guard, effect = _record(item, (0, 1, 2), "occurrence")
        occurrences.append(
            base.OccurrenceDecl(
                _nat(scope, "occurrence scope"),
                _decode_guard(guard),
                _decode_baseline_effect(effect),
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
        tuple(challenges),
        (),
        tuple(checks),
        tuple(claims),
        (),
        tuple(terminals),
        tuple(occurrences),
    )


def _strict_profiled_body(body: bytes, label: str) -> tuple[object, object, bytes]:
    if type(body) is not bytes or not body:
        _fail("Malformed", "F0V2B2C0-M-BODY", f"{label} body is not nonempty bytes")
    try:
        decoded = k1.decode_datum(body)
        if k1.encode_datum(decoded) != body:
            _fail(
                "Malformed",
                "F0V2B2C0-M-NONCANONICAL",
                f"{label} body does not re-encode byte-identically",
            )
    except SnapshotFailure:
        raise
    except Exception as error:
        _fail("Malformed", "F0V2B2C0-M-DECODE", f"{label}: {error}")
    profile, domain = _record(decoded, (0, 1), f"profiled {label}")
    profile_id = _content_ref(profile, f"{label} profile")
    return profile_id, domain, k1.encode_datum(domain)


def _ordered_preimages(mapping: object, body: Any) -> tuple[tuple[bytes, bytes], ...]:
    try:
        items = tuple(mapping.items())
    except AttributeError as error:
        _fail("Malformed", "F0V2B2C0-M-ENVIRONMENT", str(error))
    result = tuple(
        sorted(
            (
                (identifier.internal_reference(), body(preimage))
                for identifier, preimage in items
            ),
            key=lambda item: item[0],
        )
    )
    if len({key for key, _value in result}) != len(result):
        _fail("Malformed", "F0V2B2C0-M-CLOSURE", "closure contains duplicate IDs")
    return result


def snapshot_environment(environment: object) -> ClosureSnapshot:
    if type(environment) is not base.Environment:
        _fail("Malformed", "F0V2B2C0-M-ENVIRONMENT", "environment has another carrier")
    prior = environment.prior_meta_preimages
    prior_values = (
        prior.identity_profile,
        prior.hash_suite,
        prior.semantic_regime,
    )
    snapshot = ClosureSnapshot(
        prior_values,
        _ordered_preimages(
            environment.profile_preimages,
            lambda profile: k1.encode_datum(profile.body()),
        ),
        _ordered_preimages(environment.module_preimages, lambda module: module.body()),
        _ordered_preimages(environment.algorithm_preimages, k1.algorithm_preimage),
        _ordered_preimages(
            environment.contract_preimages, lambda contract: contract.body()
        ),
    )
    # Exercise Foundation authentication before any snapshot can be retained.
    ledger = k1.AuthenticationLedger()
    try:
        k1.authenticate_prior_meta_basis(prior, ledger=ledger)
        k1.effective_semantic_context(
            environment.profile_id,
            dict(environment.profile_preimages),
            semantic_regime=k1.SEMANTIC_REGIME_ID,
            ledger=ledger,
        )
        k1.authenticate_module_closure(
            tuple(environment.module_preimages),
            dict(environment.module_preimages),
            semantic_regime=k1.SEMANTIC_REGIME_ID,
            ledger=ledger,
        )
        for identifier, algorithm in environment.algorithm_preimages.items():
            if (
                k1.authenticate_algorithm_identity(algorithm, ledger=ledger)
                != identifier
            ):
                _fail("Refused", "F0V2B2C0-R-ALGORITHM-ID", "algorithm ID drift")
        for identifier, contract in environment.contract_preimages.items():
            if contract.identity != identifier:
                _fail("Refused", "F0V2B2C0-R-CONTRACT-ID", "contract ID drift")
            k1.authenticate_content_id(
                identifier, contract.body(), prior, ledger=ledger
            )
    except SnapshotFailure:
        raise
    except Exception as error:
        _fail("Refused", "F0V2B2C0-R-CLOSURE", str(error))
    return snapshot


def _summary(core: object) -> tuple[tuple[str, object], ...]:
    return (
        ("used_modules", len(core.used_modules)),
        ("public_inputs", len(core.public_inputs)),
        ("verifier_private_inputs", len(core.verifier_private_inputs)),
        ("constants", len(core.constants)),
        ("derived_values", len(core.derived_values)),
        ("scopes", len(core.scopes)),
        ("bindings", len(core.public_bindings)),
        ("challenges", len(core.challenges)),
        ("oracles", len(core.oracles)),
        ("checks", len(core.checks)),
        ("claims", len(core.claims)),
        ("reductions", len(core.reductions)),
        ("terminals", len(core.terminals)),
        ("occurrences", len(core.occurrences)),
        (
            "effect_tags",
            tuple(
                {
                    base.ProverMessageEffect: 0,
                    base.ChallengeEffect: 2,
                    base.CheckEffect: 3,
                    base.TerminalEffect: 5,
                }[type(item.effect)]
                for item in core.occurrences
            ),
        ),
    )


def make_core_candidate(core: object, profile_id: object) -> CanonicalCoreCandidate:
    return CanonicalCoreCandidate(
        base.core_id(core, profile_id),
        profile_id,
        base.core_profiled_body(core, profile_id),
    )


def make_protocol_candidate(
    core_id: object, profile_id: object
) -> CanonicalFreshProtocolCandidate:
    return CanonicalFreshProtocolCandidate(
        base.protocol_id(core_id, profile_id),
        profile_id,
        base.protocol_profiled_body(core_id, profile_id),
    )


def admit_core_snapshot(candidate: object, environment: object) -> AdmissionResult:
    try:
        if type(candidate) is not CanonicalCoreCandidate:
            _fail("Malformed", "F0V2B2C0-M-REQUEST", "Core request has another carrier")
        if candidate.profile_id != environment.profile_id:
            _fail(
                "KindMismatch",
                "F0V2B2C0-K-REQUEST-PROFILE",
                "candidate and environment profiles differ",
            )
        if candidate.profile_id != base.target_profile_id():
            _fail(
                "KindMismatch",
                "F0V2B2C0-K-TARGET-PROFILE",
                "the snapshot evaluator accepts only Interaction revision 0",
            )
        body_profile, domain, domain_body = _strict_profiled_body(
            candidate.profiled_body, "Core"
        )
        if body_profile != candidate.profile_id:
            _fail(
                "KindMismatch",
                "F0V2B2C0-K-BODY-PROFILE",
                "Core body and request select different profiles",
            )
        if (
            type(candidate.asserted_id) is not k1.TypedContentId
            or candidate.asserted_id.subject_kind != base.TARGET_CORE_KIND
        ):
            _fail("KindMismatch", "F0V2B2C0-K-CORE-ID", "Core ID has another kind")
        try:
            k1.authenticate_content_id(
                candidate.asserted_id,
                candidate.profiled_body,
                environment.prior_meta_preimages,
            )
        except Exception as error:
            _fail("Malformed", "F0V2B2C0-M-CORE-ID", str(error))
        core = decode_baseline_core(domain)
        # The old handle is used only as a temporary verdict from the existing
        # semantic predicates.  It is never retained in the new authority.
        legacy = base.admit_core(
            base.CoreCandidate(candidate.asserted_id, core), environment
        )
        if legacy.outcome != "Affirmative":
            _fail(legacy.outcome, legacy.code, legacy.detail)
        closure = snapshot_environment(environment)
        handle = AdmittedCoreSnapshot(
            candidate.asserted_id.internal_reference(),
            candidate.profile_id.internal_reference(),
            bytes(candidate.profiled_body),
            bytes(domain_body),
            closure,
            _summary(core),
            EVALUATOR_FINGERPRINT,
            tuple(range(1, 11)),
            _CORE_ISSUER,
        )
        return AdmissionResult(
            "Affirmative",
            "F0V2B2C0-A-CORE-SNAPSHOT",
            "strict canonical intake and all applicable target admission stages passed",
            handle,
        )
    except SnapshotFailure as error:
        return AdmissionResult(error.outcome, error.code, error.detail)
    except Exception as error:  # pragma: no cover - fail-closed checker defect
        return AdmissionResult("CheckerFailure", "F0V2B2C0-CHECKER", str(error))


def admit_fresh_protocol_snapshot(
    core_handle: object,
    candidate: object,
    environment: object,
) -> AdmissionResult:
    try:
        if type(core_handle) is not AdmittedCoreSnapshot or not core_handle._issued_by(
            _CORE_ISSUER
        ):
            _fail(
                "Refused",
                "F0V2B2C0-R-CORE-AUTHORITY",
                "Fresh formation requires this evaluator's live immutable Core snapshot",
            )
        if type(candidate) is not CanonicalFreshProtocolCandidate:
            _fail(
                "Malformed",
                "F0V2B2C0-M-PROTOCOL-REQUEST",
                "Protocol request has another carrier",
            )
        if candidate.profile_id != environment.profile_id:
            _fail(
                "KindMismatch",
                "F0V2B2C0-K-PROTOCOL-PROFILE",
                "Protocol request and environment profiles differ",
            )
        profile, domain, _domain_body = _strict_profiled_body(
            candidate.profiled_body, "Protocol"
        )
        if (
            profile.internal_reference() != core_handle.profile_reference
            or candidate.profile_id.internal_reference()
            != core_handle.profile_reference
        ):
            _fail(
                "KindMismatch",
                "F0V2B2C0-K-PROTOCOL-PROFILE",
                "Fresh Protocol and admitted Core profiles differ",
            )
        core_ref, interpretation = _record(domain, (0, 1), "Fresh Protocol")
        referenced_core = _content_ref(core_ref, "Protocol Core")
        if referenced_core.internal_reference() != core_handle.core_reference:
            _fail(
                "Refused",
                "F0V2B2C0-R-PROTOCOL-CORE",
                "Fresh Protocol cites another Core snapshot",
            )
        tag, payload = _variant(interpretation, (0,), "Fresh interpretation")
        assert tag == 0
        _unit(payload, "Fresh interpretation payload")
        if (
            type(candidate.asserted_id) is not k1.TypedContentId
            or candidate.asserted_id.subject_kind != base.TARGET_PROTOCOL_KIND
        ):
            _fail(
                "KindMismatch",
                "F0V2B2C0-K-PROTOCOL-ID",
                "Protocol ID has another kind",
            )
        try:
            k1.authenticate_content_id(
                candidate.asserted_id,
                candidate.profiled_body,
                environment.prior_meta_preimages,
            )
        except Exception as error:
            _fail("Malformed", "F0V2B2C0-M-PROTOCOL-ID", str(error))
        closure = snapshot_environment(environment)
        if closure.fingerprint != core_handle.closure.fingerprint:
            _fail(
                "Refused",
                "F0V2B2C0-R-CLOSURE-PAIR",
                "Fresh formation closure differs from the admitted Core closure",
            )
        handle = AdmittedFreshProtocolSnapshot(
            candidate.asserted_id.internal_reference(),
            candidate.profile_id.internal_reference(),
            bytes(candidate.profiled_body),
            core_handle,
            closure.fingerprint,
            EVALUATOR_FINGERPRINT,
            _PROTOCOL_ISSUER,
        )
        return AdmissionResult(
            "Affirmative",
            "F0V2B2C0-A-FRESH-SNAPSHOT",
            "Fresh Protocol formed over the exact immutable Core and closure snapshots",
            handle,
        )
    except SnapshotFailure as error:
        return AdmissionResult(error.outcome, error.code, error.detail)
    except Exception as error:  # pragma: no cover - fail-closed checker defect
        return AdmissionResult("CheckerFailure", "F0V2B2C0-CHECKER", str(error))


def fixture() -> tuple[object, CanonicalCoreCandidate, CanonicalFreshProtocolCandidate]:
    value = base.make_fixture()
    core = make_core_candidate(value.core_candidate.core, value.environment.profile_id)
    protocol = make_protocol_candidate(core.asserted_id, value.environment.profile_id)
    return value.environment, core, protocol


def reconstructed_environment(environment: object) -> object:
    """Build an equal-content environment with fresh map objects."""

    return base.Environment(
        environment.profile_id,
        MappingProxyType(dict(environment.profile_preimages)),
        MappingProxyType(dict(environment.module_preimages)),
        MappingProxyType(dict(environment.algorithm_preimages)),
        MappingProxyType(
            {
                key: MappingProxyType(dict(value))
                for key, value in environment.algorithm_modules.items()
            }
        ),
        MappingProxyType(dict(environment.contract_preimages)),
        environment.prior_meta_preimages,
    )


def authority_summary(
    core_handle: object, protocol_handle: object | None = None
) -> dict[str, object]:
    if type(core_handle) is not AdmittedCoreSnapshot or not core_handle._issued_by(
        _CORE_ISSUER
    ):
        _fail("Refused", "F0V2B2C0-R-CORE-AUTHORITY", "not a live Core snapshot")
    result: dict[str, object] = {
        "core_reference_sha256": hashlib.sha256(core_handle.core_reference).hexdigest(),
        "profile_reference_sha256": hashlib.sha256(
            core_handle.profile_reference
        ).hexdigest(),
        "profiled_body_sha256": hashlib.sha256(core_handle.profiled_body).hexdigest(),
        "domain_body_sha256": hashlib.sha256(core_handle.domain_body).hexdigest(),
        "closure_sha256": core_handle.closure.fingerprint.hex(),
        "structural_summary": dict(core_handle.structural_summary),
        "admission_steps": core_handle.admission_steps,
    }
    if protocol_handle is not None:
        if (
            type(protocol_handle) is not AdmittedFreshProtocolSnapshot
            or not protocol_handle._issued_by(_PROTOCOL_ISSUER)
            or protocol_handle.core_handle is not core_handle
        ):
            _fail(
                "Refused",
                "F0V2B2C0-R-PROTOCOL-AUTHORITY",
                "Protocol is not paired to the identical live Core snapshot",
            )
        result["protocol_reference_sha256"] = hashlib.sha256(
            protocol_handle.protocol_reference
        ).hexdigest()
        result["protocol_body_sha256"] = hashlib.sha256(
            protocol_handle.profiled_body
        ).hexdigest()
    return result


def serialization_refuses(handle: object) -> bool:
    try:
        pickle.dumps(handle)
    except (TypeError, pickle.PickleError):
        return True
    return False
