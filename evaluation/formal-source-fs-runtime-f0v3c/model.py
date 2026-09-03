#!/usr/bin/env python3
"""Finite canonical-framed Fiat--Shamir subjects and portable algorithms.

Both subjects are deliberately bounded to the finite Schnorr Core and use the
K1 canonical terms and evaluator from the executable-foundations package.  The
canonical-framed owner page fixes the nominal application-domain declaration
body, so both exact constructions are owner-determined admitted subjects.
"""

from __future__ import annotations

from dataclasses import dataclass
import importlib.util
from pathlib import Path
import sys
from types import ModuleType
from typing import Any


ROOT = Path(__file__).resolve().parents[2]
TARGET_MODEL = ROOT / "evaluation/formal-source-target-core-f1r1b/reference_model.py"


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


target = _load("_zkc_fs_runtime_target", TARGET_MODEL)
k1 = target.k1

TRANSCRIPT_CAPACITY = 4096
DRAW_BYTES = 8
RETRYING_MAXIMUM_DRAWS = 2
ONE_SHOT_MAXIMUM_DRAWS = 1
MAXIMUM_DRAWS = RETRYING_MAXIMUM_DRAWS
STATE_TYPE = k1.BYTES_32
TRANSCRIPT_BYTES_TYPE = k1.ValueType(
    k1.BYTES_DOMAIN, k1.BytesSchema(0, TRANSCRIPT_CAPACITY)
)
NATURAL_TYPE = k1.NAT_U64
Z3 = target.Z3
INITIAL_STATE = k1.admit_value(STATE_TYPE, k1.BytesValue(bytes(32)))
EVALUATION_CONTRACT = k1.DEFAULT_EVALUATION_CONTRACT
APPLICATION_DOMAIN_SYMBOL = "finite-schnorr-runtime"


class SubjectError(RuntimeError):
    """The bounded candidate or one exact dependency is inconsistent."""


@dataclass(frozen=True)
class AlgorithmUse:
    algorithm: Any
    evaluation_contract: Any


@dataclass(frozen=True)
class ChallengeRule:
    challenge: int
    draw_bytes: int
    maximum_draws: int
    accept: AlgorithmUse
    decode: AlgorithmUse


@dataclass(frozen=True)
class TranscriptConstruction:
    core_id: Any
    transcript_state_type: Any
    transcript_bytes_type: Any
    natural_type: Any
    initial_state: Any
    absorb: AlgorithmUse
    squeeze_bytes: AlgorithmUse
    advance_state: AlgorithmUse
    application_domain: Any
    sampling_exhausted_failure: Any
    challenge_rules: tuple[ChallengeRule, ...]
    profile_id: Any
    identifier: Any


@dataclass(frozen=True)
class FSProtocol:
    core_id: Any
    transcript_construction_id: Any
    profile_id: Any
    identifier: Any


@dataclass(frozen=True)
class CheckedConstruction:
    source_protocol_id: Any
    target_protocol_id: Any
    shared_core_id: Any
    transcript_construction_id: Any
    occurrence_map: tuple[tuple[int, int], ...]
    value_map: tuple[tuple[str, str], ...]
    challenge_map: tuple[tuple[int, int], ...]
    conclusion: str


@dataclass(frozen=True)
class Subject:
    name: str
    fixture: Any
    admitted_core: Any
    admitted_fresh_protocol: Any
    construction: TranscriptConstruction
    fs_protocol: FSProtocol
    checked: CheckedConstruction
    application_module: Any
    algorithms: tuple[Any, ...]
    admission_outcome: str
    admission_code: str
    admission_detail: str


def _record(*values: Any) -> Any:
    return k1.DatumRecord(tuple(enumerate(values)))


def _variant(case: int, payload: Any = k1.UNIT) -> Any:
    return k1.DatumVariant(case, payload)


def _seq(values: tuple[Any, ...]) -> Any:
    return k1.DatumSeq(values)


def _call(name: str, *arguments: Any) -> Any:
    return k1.PrimitiveCall(k1.PRIMITIVE_REFS_BY_KEY[(name, 1)], arguments)


def _literal(value_type: Any, datum: Any) -> Any:
    return k1.Literal(k1.admit_value(value_type, datum))


def _nat(value: int) -> Any:
    return _literal(NATURAL_TYPE, k1.Nat(value))


def _z3(value: int) -> Any:
    return _literal(Z3, k1.Nat(value))


def _bytes(value: bytes) -> Any:
    return _literal(TRANSCRIPT_BYTES_TYPE, k1.BytesValue(value))


def _first_u64(term: Any) -> Any:
    return _call("bytes.first-u64-be", _call("sha2-256", term))


def _quartile(term: Any, branches: tuple[Any, Any, Any, Any]) -> Any:
    quarter = 1 << 62
    return k1.Conditional(
        _call("nat.lt", term, _nat(quarter)),
        branches[0],
        k1.Conditional(
            _call("nat.lt", term, _nat(2 * quarter)),
            branches[1],
            k1.Conditional(
                _call("nat.lt", term, _nat(3 * quarter)),
                branches[2],
                branches[3],
            ),
        ),
    )


def portable_algorithms(*, always_accept: bool = False) -> tuple[Any, Any, Any, Any, Any]:
    """Return the exact toy transition suite as K1 portable terms.

    SHA-256 here is only an admitted deterministic primitive.  No security or
    distribution property is used by admission or by the finite checks.
    """

    absorb = k1.CanonicalAlgorithm(
        k1.Symbol("CanonicalFramedAbsorb"),
        (STATE_TYPE, TRANSCRIPT_BYTES_TYPE),
        _call(
            "sha2-256",
            _call(
                "bytes.concat",
                k1.Variable(0, STATE_TYPE),
                k1.Variable(1, TRANSCRIPT_BYTES_TYPE),
            ),
        ),
    )

    squeeze_seed = _call(
        "bytes.concat",
        k1.Variable(0, STATE_TYPE),
        _call(
            "bytes.concat",
            k1.Variable(1, TRANSCRIPT_BYTES_TYPE),
            _call("u64.to-be", k1.Variable(2, NATURAL_TYPE)),
        ),
    )
    squeeze_selector = _first_u64(squeeze_seed)
    # The four exact outputs hash into quartiles 0, 1, 2, and 3 respectively.
    squeeze = k1.CanonicalAlgorithm(
        k1.Symbol("CanonicalFramedSqueezeBytes"),
        (STATE_TYPE, TRANSCRIPT_BYTES_TYPE, NATURAL_TYPE),
        _quartile(
            squeeze_selector,
            (
                _bytes(bytes([1]) * DRAW_BYTES),
                _bytes(bytes([5]) * DRAW_BYTES),
                _bytes(bytes(DRAW_BYTES)),
                _bytes(bytes([3]) * DRAW_BYTES),
            ),
        ),
    )

    advance_preimage = _call(
        "bytes.concat",
        k1.Variable(0, STATE_TYPE),
        _call(
            "bytes.concat",
            k1.Variable(1, TRANSCRIPT_BYTES_TYPE),
            _call(
                "bytes.concat",
                _call("u64.to-be", k1.Variable(2, NATURAL_TYPE)),
                k1.Variable(3, TRANSCRIPT_BYTES_TYPE),
            ),
        ),
    )
    advance = k1.CanonicalAlgorithm(
        k1.Symbol("CanonicalFramedAdvanceState"),
        (
            STATE_TYPE,
            TRANSCRIPT_BYTES_TYPE,
            NATURAL_TYPE,
            TRANSCRIPT_BYTES_TYPE,
        ),
        _call("sha2-256", advance_preimage),
    )

    if always_accept:
        accept = k1.CanonicalAlgorithm(
            k1.Symbol("CanonicalFramedAlwaysAccept"),
            (TRANSCRIPT_BYTES_TYPE,),
            _literal(k1.BOOL, True),
        )
    else:
        accepted_number = _first_u64(k1.Variable(0, TRANSCRIPT_BYTES_TYPE))
        accept = k1.CanonicalAlgorithm(
            k1.Symbol("CanonicalFramedAccept"),
            (TRANSCRIPT_BYTES_TYPE,),
            _call("nat.lt", accepted_number, _nat(3 * (1 << 62))),
        )

    decode_number = _first_u64(k1.Variable(0, TRANSCRIPT_BYTES_TYPE))
    decode = k1.CanonicalAlgorithm(
        k1.Symbol("CanonicalFramedDecode"),
        (TRANSCRIPT_BYTES_TYPE,),
        _quartile(decode_number, (_z3(0), _z3(1), _z3(2), _z3(2))),
    )
    return absorb, squeeze, advance, accept, decode


def _root_type_descriptor(root_ordinal: int, schema: Any) -> Any:
    return _record(
        _variant(
            1,
            _variant(
                0,
                _record(
                    k1.BytesValue(k1.SEMANTIC_REGIME_ID.internal_reference()),
                    k1.Symbol("foundation.root-value-domain"),
                    k1.Nat(root_ordinal),
                ),
            ),
        ),
        schema,
    )


def _sampling_payload_declaration_type() -> Any:
    challenge_ref = _root_type_descriptor(
        2, _variant(2, k1.Nat((1 << 14) - 1))
    )
    draw_count = _root_type_descriptor(2, _variant(2, k1.Nat(1 << 20)))
    fields = _seq(
        (
            _record(k1.Nat(0), challenge_ref),
            _record(k1.Nat(1), draw_count),
        )
    )
    return _root_type_descriptor(7, _variant(7, fields))


def application_module() -> Any:
    """Build the exact nominal declaration module selected by the owner page."""

    application_catalog = _record(
        k1.Symbol("pir.fs-application-domain"),
        _seq((_record(k1.Symbol(APPLICATION_DOMAIN_SYMBOL)),)),
    )
    failure_catalog = _record(
        k1.Symbol("semantic-failure"),
        _seq(
            (
                _record(
                    k1.Symbol("pir.fs.sampling-exhausted"),
                    _sampling_payload_declaration_type(),
                ),
            )
        ),
    )
    return k1.SemanticModuleCandidate(
        k1.Symbol("canonical-framed-finite-schnorr"),
        (),
        _seq((application_catalog, failure_catalog)),
    )


def _algorithm_use_body(use: AlgorithmUse) -> Any:
    return _record(
        k1.BytesValue(use.algorithm.identity.internal_reference()),
        k1.BytesValue(use.evaluation_contract.identity.internal_reference()),
    )


def _module_ref_body(reference: Any) -> Any:
    return _variant(
        1,
        _record(
            k1.BytesValue(reference.module.internal_reference()),
            k1.Symbol(reference.declaration_kind),
            k1.Nat(reference.local_ordinal),
        ),
    )


def _failure_type_body(failure: Any) -> Any:
    return _record(
        _module_ref_body(
            target.ModuleDeclarationRef(
                failure.declaration_module,
                "semantic-failure",
                failure.local_ordinal,
            )
        ),
        k1.value_type_datum(failure.payload_type),
    )


def construction_domain_datum(construction: TranscriptConstruction) -> Any:
    rule = construction.challenge_rules[0]
    rule_body = _record(
        k1.Nat(rule.challenge),
        k1.Nat(rule.draw_bytes),
        k1.Nat(rule.maximum_draws),
        _algorithm_use_body(rule.accept),
        _algorithm_use_body(rule.decode),
    )
    return _record(
        k1.BytesValue(construction.core_id.internal_reference()),
        k1.value_type_datum(construction.transcript_state_type),
        k1.value_type_datum(construction.transcript_bytes_type),
        k1.value_type_datum(construction.natural_type),
        construction.initial_state.datum,
        _algorithm_use_body(construction.absorb),
        _algorithm_use_body(construction.squeeze_bytes),
        _algorithm_use_body(construction.advance_state),
        _module_ref_body(construction.application_domain),
        _failure_type_body(construction.sampling_exhausted_failure),
        _seq((rule_body,)),
    )


def protocol_domain_datum(core_id: Any, construction_id: Any) -> Any:
    return _record(
        k1.BytesValue(core_id.internal_reference()),
        _variant(1, k1.BytesValue(construction_id.internal_reference())),
    )


def invocation_id(subject: Subject, statement: int) -> Any:
    value = k1.admit_value(Z3, k1.Nat(statement))
    datum = _record(
        k1.BytesValue(subject.construction.core_id.internal_reference()),
        _seq(
            (
                _record(
                    k1.Nat(0),
                    k1.value_type_datum(Z3),
                    value.datum,
                ),
            )
        ),
        _seq(()),
    )
    return k1.profiled_content_id(
        "pir.invocation",
        subject.fixture.environment.profile_id,
        datum,
        semantic_regime=k1.SEMANTIC_REGIME_ID,
    )


def canonical_value_json(value: Any) -> dict[str, str]:
    return {
        "value_type": k1.encode_datum(k1.value_type_datum(value.value_type)).hex(),
        "datum": k1.encode_datum(value.datum).hex(),
    }


def identifier_text(identifier: Any) -> str:
    return identifier.carrier()


def _require_completed_value(result: Any, label: str) -> Any:
    if result.outcome is not k1.Outcome.COMPLETED or not isinstance(
        result.completion, k1.Success
    ):
        raise SubjectError(f"{label} did not complete: {result.outcome.value}/{result.code}")
    return result.completion.value


def evaluate(use: AlgorithmUse, inputs: tuple[Any, ...]) -> Any:
    dependencies = set(use.algorithm.module_dependencies)
    modules = {
        identifier: candidate
        for identifier, candidate in k1.FIXTURE_MODULE_PREIMAGES.items()
        if identifier in dependencies
    }
    result = k1.Evaluator().evaluate(
        use.algorithm,
        inputs,
        modules=modules,
        evaluation_contract=use.evaluation_contract,
    )
    return _require_completed_value(result, use.algorithm.algorithm_kind.value)


def make_subject(name: str = "retrying") -> Subject:
    if name not in {"retrying", "one-shot"}:
        raise SubjectError(f"unknown finite subject: {name}")
    fixture = target.make_fixture()
    core_result = target.admit_core(fixture.core_candidate, fixture.environment)
    if core_result.outcome != "Affirmative" or core_result.handle is None:
        raise SubjectError(
            f"finite Core did not admit: {core_result.outcome}/{core_result.code}"
        )
    fresh_result = target.admit_fresh_protocol(
        core_result.handle, fixture.protocol_candidate, fixture.environment
    )
    if fresh_result.outcome != "Affirmative" or fresh_result.handle is None:
        raise SubjectError(
            f"Fresh protocol did not admit: {fresh_result.outcome}/{fresh_result.code}"
        )

    one_shot = name == "one-shot"
    absorb, squeeze, advance, accept, decode = portable_algorithms(
        always_accept=one_shot
    )
    algorithms = (absorb, squeeze, advance, accept, decode)
    expected_types = (
        (STATE_TYPE, ()),
        (TRANSCRIPT_BYTES_TYPE, ()),
        (STATE_TYPE, ()),
        (k1.BOOL, ()),
        (Z3, ()),
    )
    for algorithm, (output, failures) in zip(algorithms, expected_types):
        k1.check_algorithm_syntax_and_types(algorithm)
        function_type = algorithm.function_type
        if function_type.output != output or function_type.failures != failures:
            raise SubjectError(
                f"portable ABI drifted for {algorithm.algorithm_kind.value}"
            )

    module = application_module()
    app_ref = target.ModuleDeclarationRef(
        module.identity, "pir.fs-application-domain", 0
    )
    app_body = k1.resolve_module_declaration(
        module, app_ref.declaration_kind, app_ref.local_ordinal
    )
    if app_body != _record(k1.Symbol(APPLICATION_DOMAIN_SYMBOL)):
        raise SubjectError("candidate application-domain body drifted")

    sampling_payload = k1.ValueType(
        k1.RECORD_DOMAIN,
        k1.RecordSchema(
            (
                (0, k1.ValueType(k1.NAT_DOMAIN, k1.NatSchema((1 << 14) - 1))),
                (1, k1.ValueType(k1.NAT_DOMAIN, k1.NatSchema(1 << 20))),
            )
        ),
    )
    failure = k1.SemanticFailureType(module.identity, 0, sampling_payload)
    k1.authenticate_failure_reference(
        failure,
        {module.identity: module},
        semantic_regime=k1.SEMANTIC_REGIME_ID,
    )

    repository = target.publication.compile_repository()
    profile = repository.profiles["canonical-framed-fiat-shamir"]
    contract = EVALUATION_CONTRACT
    placeholder = TranscriptConstruction(
        fixture.core_candidate.asserted_id,
        STATE_TYPE,
        TRANSCRIPT_BYTES_TYPE,
        NATURAL_TYPE,
        INITIAL_STATE,
        AlgorithmUse(absorb, contract),
        AlgorithmUse(squeeze, contract),
        AlgorithmUse(advance, contract),
        app_ref,
        failure,
        (
            ChallengeRule(
                0,
                DRAW_BYTES,
                ONE_SHOT_MAXIMUM_DRAWS if one_shot else RETRYING_MAXIMUM_DRAWS,
                AlgorithmUse(accept, contract),
                AlgorithmUse(decode, contract),
            ),
        ),
        profile.profile_id,
        None,
    )
    construction_id = k1.profiled_content_id(
        "pir.transcript-construction",
        profile.profile_id,
        construction_domain_datum(placeholder),
        semantic_regime=k1.SEMANTIC_REGIME_ID,
    )
    construction = TranscriptConstruction(
        **{**placeholder.__dict__, "identifier": construction_id}
    )
    fs_protocol_id = k1.profiled_content_id(
        "pir.protocol",
        profile.profile_id,
        protocol_domain_datum(construction.core_id, construction.identifier),
        semantic_regime=k1.SEMANTIC_REGIME_ID,
    )
    fs_protocol = FSProtocol(
        construction.core_id,
        construction.identifier,
        profile.profile_id,
        fs_protocol_id,
    )
    checked = CheckedConstruction(
        fresh_result.handle.protocol_id,
        fs_protocol.identifier,
        construction.core_id,
        construction.identifier,
        tuple((index, index) for index in range(6)),
        (
            ("public-input:0", "public-input:0"),
            ("occurrence-output:0:0", "occurrence-output:0:0"),
            ("occurrence-output:1:0", "occurrence-output:1:0"),
            ("occurrence-output:2:0", "occurrence-output:2:0"),
            ("occurrence-output:3:0", "occurrence-output:3:0"),
        ),
        ((0, 0),),
        "StructurallyConstructed",
    )
    return Subject(
        name,
        fixture,
        core_result.handle,
        fresh_result.handle,
        construction,
        fs_protocol,
        checked,
        module,
        algorithms,
        "Affirmative",
        "F0V3C-A-OWNER-ADMISSION",
        (
            "docs-next/pir/fiat-shamir.md Section 2 fixes the application-domain "
            "declaration as the companion page's NominalProtocolDeclarationBody"
        ),
    )
