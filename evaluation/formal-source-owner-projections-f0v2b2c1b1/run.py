#!/usr/bin/env python3
"""Validate the F0-V2B2C1B1 foundation owner-projection slice."""

from __future__ import annotations

import argparse
import copy
from dataclasses import asdict, dataclass
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
from types import ModuleType
from typing import Any, Callable


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
MODEL = HERE / "model.py"
INDEPENDENT = HERE / "independent.py"
EXPECTED = HERE / "expected-findings.json"
INVENTORY = ROOT / "evaluation/formal-source-constructor-closure-f0v2b2a/inventory.json"
AGGREGATE = "F0V2B2C1B1-A-FOUNDATION-OWNER-PROJECTIONS"
FOUNDATION_FAMILIES = (
    "verifier-private-dependency",
    "constant-and-derived-value",
    "child-scope-and-nontrivial-guard",
    "deterministic-verifier-message",
)


class GateFailure(RuntimeError):
    """The executable package no longer satisfies its frozen contract."""


@dataclass(frozen=True)
class Finding:
    name: str
    outcome: str
    code: str
    detail: str


def _load(name: str, path: Path) -> ModuleType:
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:  # pragma: no cover - host failure
        raise ImportError(f"cannot load module at {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def _require(condition: bool, detail: str) -> None:
    if not condition:
        raise GateFailure(detail)


def _finding(name: str, outcome: str, code: str, detail: str) -> Finding:
    return Finding(name, outcome, code, detail)


def _expect_result(result: object, outcome: str, code: str, label: str) -> None:
    _require(
        result.outcome == outcome and result.code == code,
        f"{label}: expected {outcome}/{code}, got {result.outcome}/{result.code}",
    )


def _rejects(operation: Callable[[], object], expected: type[BaseException]) -> bool:
    try:
        operation()
    except expected:
        return True
    return False


def _field(schema: dict[str, Any], ordinal: int) -> dict[str, Any]:
    _require(schema.get("node") == "record", "expected a record schema")
    for field_ordinal, child in schema["fields"]:
        if field_ordinal == ordinal:
            return child
    raise GateFailure(f"record schema lacks field {ordinal}")


def _check_target_orders(
    codec: ModuleType, schema: dict[str, Any], value: object
) -> tuple[int, int]:
    """Recursively check every SortedUnique sequence by exact child bytes."""

    node = schema["node"]
    if node == "atom":
        return 0, 0
    if node == "record":
        _require(type(value) is dict, "record value has another carrier")
        totals = [
            _check_target_orders(codec, child, value[ordinal])
            for ordinal, child in schema["fields"]
        ]
        return sum(item[0] for item in totals), sum(item[1] for item in totals)
    if node == "variant":
        _require(
            type(value) is dict and set(value) == {"case", "value"},
            "variant value has another carrier",
        )
        cases = dict(schema["cases"])
        return _check_target_orders(codec, cases[value["case"]], value["value"])
    if node != "sequence" or type(value) is not list:
        raise GateFailure("unknown schema node or sequence carrier")
    nested = [_check_target_orders(codec, schema["element"], item) for item in value]
    sequences = sum(item[0] for item in nested)
    elements = sum(item[1] for item in nested)
    if schema["discipline"] == "sorted-unique":
        bodies = [codec.encode_value(schema["element"], item) for item in value]
        _require(
            bodies == sorted(set(bodies)),
            "SortedUnique value does not follow exact target-body order",
        )
        sequences += 1
        elements += len(bodies)
    return sequences, elements


def _binding_availability_mutation(model: ModuleType) -> tuple[object, object]:
    environment, candidate = model.fixtures()["child-scope-and-nontrivial-guard"]
    _profile, domain, _body = model.b2c0._strict_profiled_body(
        candidate.profiled_body, "binding mutation source"
    )
    core = model.decode_core(domain)
    bindings = (
        *core.public_bindings,
        model.base.PublicBindingDecl(
            1,
            model.base.BindingClass.SESSION_CONTEXT,
            model.base.OccurrenceOutputRef(0, 0),
        ),
    )
    mutated = model.base.InteractiveCore(
        core.used_modules,
        core.public_inputs,
        core.verifier_private_inputs,
        core.constants,
        core.derived_values,
        core.scopes,
        bindings,
        core.challenges,
        core.oracles,
        core.checks,
        core.claims,
        core.reductions,
        core.terminals,
        core.occurrences,
    )
    return environment, model.make_candidate(mutated, environment.profile_id)


def _inventory() -> dict[str, Any]:
    try:
        value = json.loads(INVENTORY.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        raise GateFailure("cannot read the B2A constructor inventory") from error
    if (
        type(value) is not dict
        or type(value.get("required_pressure_families")) is not list
    ):
        raise GateFailure("B2A constructor inventory has another shape")
    return value


def _canonical_case(model: ModuleType, value: dict[str, str]) -> int:
    datum = model.k1.decode_datum(bytes.fromhex(value["body"]))
    _require(type(datum) is model.k1.DatumVariant, "canonical atom is not a variant")
    return datum.case


def evaluate() -> tuple[list[Finding], dict[str, Any]]:
    model = _load("_zkc_f0v2b2c1b1_model", MODEL)
    cold = _load("_zkc_f0v2b2c1b1_independent", INDEPENDENT)
    inventory = _inventory()
    families = inventory["required_pressure_families"]
    b2c_families = tuple(item["id"] for item in families if item["stage"] == "B2C")
    b2d_families = tuple(item["id"] for item in families if item["stage"] == "B2D")
    _require(
        len(b2c_families) == 21
        and len(b2d_families) == 2
        and b2c_families[:4] == FOUNDATION_FAMILIES,
        "the B2A pressure-family partition drifted",
    )
    _require(
        model.VIEW_SCHEMAS == cold.VIEW_SCHEMAS,
        "reference and independent B2B schema compilers disagree",
    )
    _require(
        model.b2b.PROFILE["profile_digest"] == cold.PROFILE_DIGEST,
        "the two projectors cite different owner profiles",
    )
    _require(
        model.k1 is not cold.k1 and model.b2b is not cold.b2b,
        "cold path reused a reference parser or schema module instance",
    )

    findings = [
        _finding(
            "predecessor-and-family-pins",
            "Affirmative",
            "F0V2B2C1B1-A-PREDECESSOR-PINS",
            "the exact B2C0/B2B/B2C1A inputs and 21-plus-2 B2A family split remain selected",
        ),
        _finding(
            "cold-path-module-separation",
            "Affirmative",
            "F0V2B2C1B1-A-COLD-PATH-SEPARATION",
            "the cold path uses distinct Foundation, schema-compiler, and iterative-codec module instances",
        ),
    ]

    fixture_records: dict[str, dict[str, Any]] = {}
    handles: dict[str, tuple[object, object, object, object]] = {}
    all_bodies: list[bytes] = []
    sorted_sequences = 0
    sorted_elements = 0
    for name, (environment, candidate) in model.fixtures().items():
        core_result = model.admit_core(candidate, environment)
        _expect_result(
            core_result,
            "Affirmative",
            "F0V2B2C1B1-A-CORE-ADMITTED",
            f"{name} Core admission",
        )
        _require(core_result.handle is not None, f"{name} omitted its Core handle")
        protocol_candidate = model.b2c0.make_protocol_candidate(
            candidate.asserted_id, environment.profile_id
        )
        protocol_result = model.admit_fresh_protocol(
            core_result.handle, protocol_candidate, environment
        )
        _expect_result(
            protocol_result,
            "Affirmative",
            "F0V2B2C1B1-A-FRESH-ADMITTED",
            f"{name} Fresh admission",
        )
        _require(
            protocol_result.handle is not None,
            f"{name} omitted its Protocol handle",
        )
        reference_views = model.project_views(
            core_result.handle, protocol_result.handle
        )
        reference_bodies = {
            view: model.codec.encode_value(model.VIEW_SCHEMAS[view], value)
            for view, value in reference_views.items()
        }
        cold_views, cold_evidence = cold.project(
            core_result.handle.profiled_body,
            core_result.handle.core_reference,
            protocol_result.handle.profiled_body,
            protocol_result.handle.protocol_reference,
        )
        cold_bodies = cold.encode_views(cold_views)
        _require(
            reference_bodies == cold_bodies,
            f"{name} reference and cold exact view bodies disagree",
        )
        for view, body in reference_bodies.items():
            decoded = model.k1.decode_datum(body)
            _require(
                model.k1.encode_datum(decoded) == body,
                f"{name}/{view} does not round-trip exactly",
            )
            sequences, elements = _check_target_orders(
                model.codec, model.VIEW_SCHEMAS[view], reference_views[view]
            )
            sorted_sequences += sequences
            sorted_elements += elements
            all_bodies.append(body)
        repeated = model.project_views(core_result.handle, protocol_result.handle)
        repeated_bodies = {
            view: model.codec.encode_value(model.VIEW_SCHEMAS[view], value)
            for view, value in repeated.items()
        }
        _require(reference_bodies == repeated_bodies, f"{name} projection is unstable")
        fixture_records[name] = {
            "view_body_sha256": {
                view: hashlib.sha256(body).hexdigest()
                for view, body in reference_bodies.items()
            },
            "cold_evidence": cold_evidence,
            "combined_sha256": hashlib.sha256(
                b"".join(reference_bodies.values())
            ).hexdigest(),
        }
        handles[name] = (
            environment,
            candidate,
            core_result.handle,
            protocol_result.handle,
        )

    _require(len(all_bodies) == 36, "the six-by-six exact body census drifted")
    _require(len(set(all_bodies)) == 36, "two fixture/view bodies unexpectedly alias")
    findings.extend(
        (
            _finding(
                "six-exact-core-admissions",
                "Affirmative",
                "F0V2B2C1B1-A-SIX-CORE-ADMISSIONS",
                "six isolated exact carriers pass the supported ten-stage owner admission slice",
            ),
            _finding(
                "six-exact-fresh-pairings",
                "Affirmative",
                "F0V2B2C1B1-A-SIX-FRESH-PAIRINGS",
                "each admitted Core forms one exact Fresh Protocol under the same evaluator and closure",
            ),
            _finding(
                "six-view-reference-formation",
                "Affirmative",
                "F0V2B2C1B1-A-SIX-VIEW-FORMATION",
                "the owner path forms all six schema-valid exact values for every isolated carrier",
            ),
            _finding(
                "cold-byte-projection-agreement",
                "Affirmative",
                "F0V2B2C1B1-A-COLD-BYTE-AGREEMENT",
                "an authenticated profiled-byte cold projector agrees on all thirty-six exact view bodies",
            ),
            _finding(
                "exact-view-roundtrip",
                "Affirmative",
                "F0V2B2C1B1-A-EXACT-VIEW-ROUNDTRIP",
                "all thirty-six view bodies decode fully and re-encode byte-identically",
            ),
            _finding(
                "target-body-collection-order",
                "Affirmative",
                "F0V2B2C1B1-A-TARGET-COLLECTION-ORDER",
                "every inhabited sorted-unique collection follows exact child-body order",
            ),
            _finding(
                "projection-determinism",
                "Affirmative",
                "F0V2B2C1B1-A-PROJECTION-DETERMINISM",
                "reprojection from each immutable admitted bearer reproduces identical bodies",
            ),
        )
    )

    def projected(name: str) -> dict[str, Any]:
        _environment, _candidate, core_handle, protocol_handle = handles[name]
        return model.project_views(core_handle, protocol_handle)

    dead_views = projected("verifier-private-dead")
    sink_views = projected("verifier-private-sink")
    binding_views = projected("public-history-binding-observation")
    dead_coin = dead_views["PublicCoinView"]
    sink_coin = sink_views["PublicCoinView"]
    binding_coin = binding_views["PublicCoinView"]
    _require(
        dead_coin[2] is True
        and dead_coin[3] == []
        and 1 not in {item["case"] for item in dead_coin[1][4]},
        "dead private source is not retained without poisoning eligibility",
    )
    _require(
        sink_coin[2] is False
        and [item["case"] for item in sink_coin[3]] == [1]
        and {item["case"] for item in sink_coin[1][4]} == {1, 5, 6, 11}
        and {item["case"] for item in sink_coin[1][5]} == {1, 11},
        "private terminal-output sink or exact source predecessor drifted",
    )
    _require(
        binding_coin[2] is True
        and binding_coin[3] == []
        and sum(item["case"] == 5 for item in binding_coin[1][4]) == 2
        and 8 not in {item["case"] for item in binding_coin[1][4]},
        "public-history binding observation was not retained as the exact sink",
    )
    findings.extend(
        (
            _finding(
                "dead-verifier-private-source",
                "Affirmative",
                "F0V2B2C1B1-A-DEAD-PRIVATE-SOURCE",
                "an unused private input has no sink-predecessor entry and does not poison eligibility",
            ),
            _finding(
                "private-to-public-sinks",
                "Affirmative",
                "F0V2B2C1B1-A-PRIVATE-SINK-DISCRIMINATORS",
                "routing private influence to an accepting terminal retains its exact source predecessor and makes eligibility false",
            ),
            _finding(
                "public-history-binding-observation",
                "Affirmative",
                "F0V2B2C1B1-A-PUBLIC-HISTORY-BINDING",
                "a binding of an earlier unconditional Prover output retains the binding observation as its public-history sink",
            ),
        )
    )

    constant_views = projected("constant-and-derived-value")
    constant_effect = constant_views["EffectView"]
    constant_value_cases = [
        _canonical_case(model, row[0]) for row in constant_effect[2]
    ]
    constant_read_cases = [
        row[1]["case"] for row in constant_views["StrategyDecisionView"][3]
    ]
    _require(
        constant_value_cases == [0, 2, 3, 4]
        and constant_read_cases == [0, 1, 2]
        and constant_effect[2][2][2] == [model._value_ref(model.base.ConstantRef(0))],
        "constant/derived value or guaranteed-read projection drifted",
    )
    findings.append(
        _finding(
            "constant-and-derived-value-projection",
            "Affirmative",
            "F0V2B2C1B1-A-CONSTANT-DERIVED-PROJECTION",
            "the exact constant, derived predecessor, value graph, static read, and terminal use are owner-derived",
        )
    )

    child_views = projected("child-scope-and-nontrivial-guard")
    child_binding = child_views["PublicBindingView"]
    child_strategy = child_views["StrategyDecisionView"]
    _require(
        [len(row[3]) for row in child_binding[1]] == [1, 2]
        and child_strategy[1][0][2]
        == [
            model._ordinal("scope-ref-body-v0", 0),
            model._ordinal("scope-ref-body-v0", 1),
        ]
        and child_strategy[1][0][3]["compiler"] == "guard-body-v0"
        and [row[1]["case"] for row in child_strategy[3]] == [1, 2],
        "child binding/decision scope path, guard, or opening-gated reads drifted",
    )
    findings.append(
        _finding(
            "child-scope-and-guard-projection",
            "Affirmative",
            "F0V2B2C1B1-A-CHILD-SCOPE-GUARD-PROJECTION",
            "the child path, exact opening, nontrivial guard, opened reads, and guarded terminal dependency are retained",
        )
    )

    verifier_views = projected("deterministic-verifier-message")
    verifier_strategy = verifier_views["StrategyDecisionView"]
    verifier_effect = verifier_views["EffectView"]
    verifier_coin = verifier_views["PublicCoinView"]
    _require(
        [row[1]["case"] for row in verifier_effect[3]] == [1, 0]
        and [row[1]["case"] for row in verifier_strategy[3]] == [1, 2, 3]
        and 8 in {item["case"] for item in verifier_coin[1][4]}
        and 7 not in {item["case"] for item in verifier_coin[1][4]}
        and fixture_records["deterministic-verifier-message"]["cold_evidence"][
            "messages"
        ]
        == 2,
        "deterministic Verifier message or later visible-read projection drifted",
    )
    findings.append(
        _finding(
            "deterministic-verifier-message-projection",
            "Affirmative",
            "F0V2B2C1B1-A-VERIFIER-MESSAGE-PROJECTION",
            "a total deterministic Verifier output is public, typed, retained as an exact output sink, and guaranteed visible to the later Prover decision",
        )
    )

    for name, expected_outcome, expected_code in (
        (
            "constant-and-derived-value",
            "KindMismatch",
            "F0V2B2C1B1-K-DERIVED-ABI",
        ),
        (
            "child-scope-and-nontrivial-guard",
            "Refused",
            "F0V2B2C1B1-R-GUARD-IMPLIES",
        ),
        (
            "deterministic-verifier-message",
            "KindMismatch",
            "F0V2B2C1B1-K-VERIFIER-MESSAGE-ABI",
        ),
    ):
        environment, candidate = model.mutated_fixture(name)
        result = model.admit_core(candidate, environment)
        _expect_result(result, expected_outcome, expected_code, f"{name} mutation")
    findings.extend(
        (
            _finding(
                "derived-value-abi-mutation",
                "KindMismatch",
                "F0V2B2C1B1-K-DERIVED-ABI",
                "a freshly identified Core with a wrong derived result ABI does not admit",
            ),
            _finding(
                "guard-implication-mutation",
                "Refused",
                "F0V2B2C1B1-R-GUARD-IMPLIES",
                "changing a conditional consumer to Always does not widen the closed syntactic GuardImplies law",
            ),
            _finding(
                "verifier-message-abi-mutation",
                "KindMismatch",
                "F0V2B2C1B1-K-VERIFIER-MESSAGE-ABI",
                "a freshly identified deterministic Verifier message with a wrong payload type does not admit",
            ),
        )
    )

    binding_environment, binding_candidate = _binding_availability_mutation(model)
    binding_result = model.admit_core(binding_candidate, binding_environment)
    _expect_result(
        binding_result,
        "Refused",
        "F0V2B2C1B1-R-BINDING-AVAILABILITY",
        "scope binding availability mutation",
    )
    findings.append(
        _finding(
            "scope-binding-before-producer-mutation",
            "Refused",
            "F0V2B2C1B1-R-BINDING-AVAILABILITY",
            "a child binding cannot read an output from the occurrence at whose before-boundary the child opens",
        )
    )

    private_binding_environment, private_binding_candidate = (
        model.private_binding_mutation()
    )
    private_binding_result = model.admit_core(
        private_binding_candidate, private_binding_environment
    )
    _expect_result(
        private_binding_result,
        "Refused",
        "F0V2B2C1B1-R-PRIVATE-BINDING",
        "verifier-private derived binding mutation",
    )
    findings.append(
        _finding(
            "verifier-private-derived-binding-mutation",
            "Refused",
            "F0V2B2C1B1-R-PRIVATE-BINDING",
            "a derived value with verifier-private ancestry cannot become a public binding",
        )
    )

    unsupported = model.base.make_fixture()
    unsupported_candidate = model.make_candidate(
        unsupported.core_candidate.core, unsupported.environment.profile_id
    )
    unsupported_result = model.admit_core(
        unsupported_candidate, unsupported.environment
    )
    _expect_result(
        unsupported_result,
        "Unsupported",
        "F0V2B2C1B1-U-OTHER-SLICE",
        "challenge-family deferral",
    )
    findings.append(
        _finding(
            "unsupported-neighbor-constructor",
            "Unsupported",
            "F0V2B2C1B1-U-OTHER-SLICE",
            "a Challenge-bearing Core fails closed instead of receiving an invented foundation projection",
        )
    )

    dead_environment, _dead_candidate, dead_core, dead_protocol = handles[
        "verifier-private-dead"
    ]
    _other_environment, other_candidate, other_core, other_protocol = handles[
        "constant-and-derived-value"
    ]
    cross_candidate = model.b2c0.make_protocol_candidate(
        other_candidate.asserted_id, dead_environment.profile_id
    )
    cross_result = model.admit_fresh_protocol(
        dead_core, cross_candidate, dead_environment
    )
    _expect_result(
        cross_result,
        "Refused",
        "F0V2B2C1B1-R-PROTOCOL-CORE",
        "cross-Core Fresh pairing",
    )
    findings.append(
        _finding(
            "cross-core-fresh-pairing",
            "Refused",
            "F0V2B2C1B1-R-PROTOCOL-CORE",
            "a valid Fresh body naming another admitted Core cannot pair with this Core authority",
        )
    )

    legacy_environment, legacy_core_candidate, legacy_protocol_candidate = (
        model.b2c0.fixture()
    )
    legacy_core_result = model.b2c0.admit_core_snapshot(
        legacy_core_candidate, legacy_environment
    )
    legacy_protocol_result = model.b2c0.admit_fresh_protocol_snapshot(
        legacy_core_result.handle,
        legacy_protocol_candidate,
        legacy_environment,
    )
    _require(
        legacy_core_result.outcome == "Affirmative"
        and legacy_protocol_result.outcome == "Affirmative",
        "B2C0 foreign-authority controls no longer admit",
    )
    _require(
        _rejects(
            lambda: model.project_views(
                legacy_core_result.handle, legacy_protocol_result.handle
            ),
            model.FamilyFailure,
        ),
        "foreign predecessor evaluator authority projected a B2C1B1 view",
    )
    findings.append(
        _finding(
            "foreign-evaluator-authority",
            "Refused",
            "F0V2B2C1B1-R-CORE-AUTHORITY",
            "an authentic predecessor snapshot with another evaluator fingerprint cannot project this slice",
        )
    )

    closure_substituted_protocol = model.b2c0.AdmittedFreshProtocolSnapshot(
        dead_protocol.protocol_reference,
        dead_protocol.profile_reference,
        dead_protocol.profiled_body,
        dead_core,
        b"\xff" * 32,
        model.EVALUATOR_FINGERPRINT,
        model.b2c0._PROTOCOL_ISSUER,
    )
    _require(
        _rejects(
            lambda: model.project_views(dead_core, closure_substituted_protocol),
            model.FamilyFailure,
        ),
        "a Protocol bearer with a substituted closure reached projection",
    )
    findings.append(
        _finding(
            "protocol-authority-closure-substitution",
            "Refused",
            "F0V2B2C1B1-R-PROTOCOL-AUTHORITY",
            "projection rechecks the Protocol issuer, evaluator, profile, identical Core bearer, and closure fingerprint",
        )
    )

    child_mutation = copy.deepcopy(child_views["PublicCoinView"])
    child_mutation[1][1].reverse()
    public_coin_schema = model.VIEW_SCHEMAS["PublicCoinView"]
    _require(
        _rejects(
            lambda: model.codec.encode_value(public_coin_schema, child_mutation),
            model.codec.CodecError,
        )
        and _rejects(
            lambda: cold.codec.encode_value(public_coin_schema, child_mutation),
            cold.codec.ColdCodecError,
        ),
        "an exact PCGraph edge-order mutation was accepted",
    )
    findings.append(
        _finding(
            "pcgraph-edge-target-order-mutation",
            "Refused",
            "F0V2B2C1B1-R-EDGE-TARGET-ORDER",
            "both exact codecs reject reversal of the child fixture's sorted PCGraph edge set",
        )
    )

    eligibility_mutation = copy.deepcopy(dead_views["PublicCoinView"])
    eligibility_mutation[2] = False
    alternate_reference = model.codec.encode_value(
        public_coin_schema, eligibility_mutation
    )
    alternate_cold = cold.codec.encode_value(public_coin_schema, eligibility_mutation)
    expected_dead = model.codec.encode_value(public_coin_schema, dead_coin)
    _require(
        alternate_reference == alternate_cold and alternate_reference != expected_dead,
        "a schema-valid eligibility substitution escaped exact owner equality",
    )
    findings.append(
        _finding(
            "schema-valid-eligibility-substitution",
            "Refused",
            "F0V2B2C1B1-R-OWNER-VALUE-SUBSTITUTION",
            "schema validity alone accepts a Boolean flip, while exact owner rederivation detects and refuses it",
        )
    )

    _require(
        _rejects(
            lambda: cold.project(
                dead_core.profiled_body[:-1],
                dead_core.core_reference,
                dead_protocol.profiled_body,
                dead_protocol.protocol_reference,
            ),
            cold.ColdProjectionError,
        ),
        "the cold projector accepted a truncated owner body",
    )
    findings.append(
        _finding(
            "cold-owner-body-truncation",
            "Malformed",
            "F0V2B2C1B1-M-COLD-OWNER-BODY",
            "the cold path refuses truncated Core bytes before deriving any view value",
        )
    )

    _require(
        _rejects(
            lambda: cold.project(
                other_core.profiled_body,
                dead_core.core_reference,
                dead_protocol.profiled_body,
                dead_protocol.protocol_reference,
            ),
            cold.ColdProjectionError,
        ),
        "the cold projector accepted a Core body/reference substitution",
    )
    findings.append(
        _finding(
            "cold-core-body-reference-substitution",
            "Refused",
            "F0V2B2C1B1-R-COLD-CORE-BODY-REFERENCE",
            "the cold path independently authenticates the complete profiled Core body against its exact reference",
        )
    )

    _require(
        _rejects(
            lambda: cold.project(
                dead_core.profiled_body,
                dead_core.core_reference,
                other_protocol.profiled_body,
                dead_protocol.protocol_reference,
            ),
            cold.ColdProjectionError,
        ),
        "the cold projector accepted a Protocol body/reference substitution",
    )
    findings.append(
        _finding(
            "cold-protocol-body-reference-substitution",
            "Refused",
            "F0V2B2C1B1-R-COLD-PROTOCOL-BODY-REFERENCE",
            "the cold path independently authenticates the complete profiled Protocol body against its exact reference",
        )
    )

    _require(
        _rejects(
            lambda: cold.project(
                dead_core.profiled_body,
                dead_core.core_reference,
                other_protocol.profiled_body,
                other_protocol.protocol_reference,
            ),
            cold.ColdProjectionError,
        ),
        "the cold projector accepted a self-authenticating Protocol for another Core",
    )
    findings.append(
        _finding(
            "cold-protocol-core-substitution",
            "Refused",
            "F0V2B2C1B1-R-COLD-PROTOCOL-CORE",
            "a self-authenticating Fresh Protocol body for another Core cannot supply this Core's ExecutionView",
        )
    )

    _require(
        _rejects(
            lambda: cold.project(
                dead_core.profiled_body,
                dead_core.core_reference,
                dead_protocol.profiled_body,
                dead_core.core_reference,
            ),
            cold.ColdProjectionError,
        ),
        "the cold projector accepted a Core reference as a Protocol reference",
    )
    findings.append(
        _finding(
            "cold-protocol-kind-substitution",
            "KindMismatch",
            "F0V2B2C1B1-K-COLD-PROTOCOL-REFERENCE",
            "the cold path rejects a well-formed Core content reference at the Protocol coordinate",
        )
    )

    remaining_b2c = b2c_families[4:]
    _require(len(remaining_b2c) == 17, "remaining B2C family count drifted")
    findings.extend(
        (
            _finding(
                "oracle-lifecycle-projections",
                "CannotAnswer",
                "F0V2B2C1B1-C-ORACLE-LIFECYCLE",
                "the eight Oracle origin, publication, query, visibility, and receipt families require a separate B2C1B slice",
            ),
            _finding(
                "claim-reduction-challenge-projections",
                "CannotAnswer",
                "F0V2B2C1B1-C-CLAIM-REDUCTION-CHALLENGE",
                "the five claim, reduction, publication-order, joint, and shared-challenge families are not evaluated here",
            ),
            _finding(
                "module-effect-projections",
                "CannotAnswer",
                "F0V2B2C1B1-C-MODULE-EFFECTS",
                "the three authenticated module decision and publication classes remain a separate owner-law slice",
            ),
            _finding(
                "expanded-terminal-projection",
                "CannotAnswer",
                "F0V2B2C1B1-C-EXPANDED-TERMINALS",
                "Abort plus claim Consume and Discharge dispositions remain outside the foundation terminal subset",
            ),
            _finding(
                "integrated-graph-and-runtime-closure",
                "CannotAnswer",
                "F0V2B2C1B1-C-B2D-INTEGRATION",
                "the two B2D families still own all-class integrated PCGraph and Fresh Oracle-receipt closure",
            ),
            _finding(
                "target-publication-and-migration",
                "CannotAnswer",
                "F0V2B2C1B1-C-TARGET-PUBLICATION",
                "the normalized schemas and projectors remain research candidates until F0-V2C",
            ),
            _finding(
                "live-implementation-correspondence",
                "CannotAnswer",
                "F0V2B2C1B1-C-LIVE-CORRESPONDENCE",
                "no current compiler or runtime path is shown to implement these offline owner projections",
            ),
            _finding(
                "formal-and-security-claims",
                "CannotAnswer",
                "F0V2B2C1B1-C-FORMAL-SECURITY-Q1",
                "bounded differential evidence is not a proof, security theorem, Fiat-Shamir claim, or Q1 closure",
            ),
        )
    )
    _require(len(findings) == 39, "finding census drifted")

    family_status = {
        item["id"]: (
            "affirmative-foundation-slice"
            if item["id"] in FOUNDATION_FAMILIES
            else "deferred-b2c1b"
            if item["stage"] == "B2C"
            else "deferred-b2d"
        )
        for item in families
    }
    finding_rows = [asdict(item) for item in findings]
    evidence = {
        "aggregate": AGGREGATE,
        "owner_profile_digest": model.b2b.PROFILE["profile_digest"],
        "schema_source_sha256": hashlib.sha256(
            model.b2b.SOURCE.read_bytes()
        ).hexdigest(),
        "constructor_inventory_sha256": hashlib.sha256(
            INVENTORY.read_bytes()
        ).hexdigest(),
        "evaluator_fingerprint": model.EVALUATOR_FINGERPRINT.hex(),
        "fixture_count": len(fixture_records),
        "view_body_count": len(all_bodies),
        "distinct_view_body_count": len(set(all_bodies)),
        "sorted_unique_sequences_checked": sorted_sequences,
        "sorted_unique_elements_checked": sorted_elements,
        "fixtures": fixture_records,
        "family_partition": {
            "affirmative_foundation": len(FOUNDATION_FAMILIES),
            "deferred_b2c1b": len(remaining_b2c),
            "deferred_b2d": len(b2d_families),
        },
        "family_status": family_status,
        "finding_counts": {
            outcome: sum(item.outcome == outcome for item in findings)
            for outcome in sorted({item.outcome for item in findings})
        },
        "findings_sha256": hashlib.sha256(
            json.dumps(
                finding_rows,
                sort_keys=True,
                separators=(",", ":"),
                ensure_ascii=True,
            ).encode("ascii")
        ).hexdigest(),
    }
    return findings, evidence


def _load_expected() -> dict[str, Any]:
    try:
        value = json.loads(EXPECTED.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        raise GateFailure("cannot read expected B2C1B1 findings") from error
    if (
        type(value) is not dict
        or set(value) != {"aggregate", "findings_sha256", "finding_codes"}
        or value["aggregate"] != AGGREGATE
        or type(value["findings_sha256"]) is not str
        or type(value["finding_codes"]) is not list
        or any(
            type(item) is not list
            or len(item) != 3
            or any(type(child) is not str for child in item)
            for item in value["finding_codes"]
        )
    ):
        raise GateFailure("expected B2C1B1 findings have another shape")
    return value


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--print-findings", action="store_true")
    parser.add_argument("--print-evidence", action="store_true")
    args = parser.parse_args()
    if not (args.check or args.print_findings or args.print_evidence):
        parser.error("select --check, --print-findings, or --print-evidence")
    try:
        findings, evidence = evaluate()
        observed = [asdict(item) for item in findings]
        if args.check:
            expected = _load_expected()
            observed_codes = [[item.name, item.outcome, item.code] for item in findings]
            _require(
                observed_codes == expected["finding_codes"]
                and evidence["findings_sha256"] == expected["findings_sha256"],
                "frozen B2C1B1 findings drifted",
            )
        if args.print_findings:
            print(json.dumps(observed, indent=2, sort_keys=True))
        if args.print_evidence:
            print(json.dumps(evidence, indent=2, sort_keys=True))
        print(
            "[formal-source-owner-projections-f0v2b2c1b1] "
            f"{len(findings)}/{len(findings)} findings; Affirmative/{AGGREGATE}; "
            f"{evidence['view_body_count']} exact view bodies; "
            f"{evidence['finding_counts']}"
        )
        return 0
    except Exception as error:
        print(f"[formal-source-owner-projections-f0v2b2c1b1] FAIL: {error}")
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
