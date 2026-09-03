"""Typed Fresh completed-record schema projector for F0-V2B2D2.

The projector consumes only the exact D1 admitted Core and Fresh Protocol
handles.  It derives a research-only candidate ExecutionView body and never
constructs, executes, or replays a run.
"""

from __future__ import annotations

import copy
from dataclasses import dataclass
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
from types import ModuleType
from typing import Any, Mapping


ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
D1_MODEL = ROOT / "evaluation/formal-source-integrated-graph-f0v2b2d1/model.py"
SCHEMA_DELTA = HERE / "schema-delta.json"

CANDIDATE_SCHEMA_FORMAT = (
    "zkc.formal-source-fresh-run-schema-f0v2b2d2.schema-source.v0"
)
CANDIDATE_SCHEMA_SCOPE = "fresh-completed-record-schema-over-five-d1-carriers"
PREDECESSOR_SCHEMA_SHA256 = (
    "c06c9e13e1c10d33943325c5b234f1f7178b3aec3502df874284451ac0195ee7"
)
OPERATIONAL_NONCOMPLETION_NAMES = (
    "Unsupported",
    "MissingDependency",
    "CannotAnswer",
    "KindMismatch",
    "Malformed",
    "Refused",
    "DeterministicLimitExceeded",
    "CheckerFailure",
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


d1 = _load("_zkc_f0v2b2d2_d1", D1_MODEL)
k1 = d1.k1
base = d1.base
oracle = d1.oracle
foundation = d1.foundation
codec = d1.codec
b2b = d1.b5.b2b


class SchemaFailure(ValueError):
    """One classified D2 projection or claim failure."""

    def __init__(self, outcome: str, code: str, detail: str) -> None:
        super().__init__(detail)
        self.outcome = outcome
        self.code = code
        self.detail = detail


@dataclass(frozen=True)
class ClaimResult:
    outcome: str
    code: str
    detail: str


def _fail(outcome: str, code: str, detail: str) -> None:
    raise SchemaFailure(outcome, code, detail)


def _wire(value: object) -> bytes:
    return json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=True
    ).encode("ascii")


def _digest(value: object) -> str:
    return hashlib.sha256(_wire(value)).hexdigest()


def _load_delta() -> dict[str, Any]:
    try:
        value = json.loads(SCHEMA_DELTA.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        _fail("Malformed", "F0V2B2D2-M-SCHEMA-DELTA", str(error))
    if type(value) is not dict or set(value) != {
        "format",
        "predecessor",
        "candidate_format",
        "candidate_scope",
        "replace_definitions",
        "add_definitions",
    }:
        _fail(
            "Malformed",
            "F0V2B2D2-M-SCHEMA-DELTA",
            "schema delta has another exact outer shape",
        )
    return value


def candidate_schema_source() -> dict[str, Any]:
    """Apply the D2 delta to the exact D1/B5B2 finite grammar."""

    source = copy.deepcopy(d1.candidate_schema_source())
    delta = _load_delta()
    if (
        source["format"] != delta["predecessor"].get("format")
        or _digest(source) != delta["predecessor"].get("sha256")
        or _digest(source) != PREDECESSOR_SCHEMA_SHA256
    ):
        _fail(
            "Refused",
            "F0V2B2D2-R-SCHEMA-PREDECESSOR",
            "D2 delta does not name the exact D1/B5B2 schema source",
        )
    if (
        delta["candidate_format"] != CANDIDATE_SCHEMA_FORMAT
        or delta["candidate_scope"] != CANDIDATE_SCHEMA_SCOPE
    ):
        _fail(
            "Refused",
            "F0V2B2D2-R-SCHEMA-IDENTITY",
            "D2 delta names another candidate grammar",
        )
    source["format"] = CANDIDATE_SCHEMA_FORMAT
    source["scope"] = CANDIDATE_SCHEMA_SCOPE
    definitions = source["definitions"]
    for name, replacement in delta["replace_definitions"].items():
        if (
            name not in definitions
            or type(replacement) is not dict
            or set(replacement) != {"prior_sha256", "value"}
            or _digest(definitions[name]) != replacement["prior_sha256"]
        ):
            _fail(
                "Refused",
                "F0V2B2D2-R-SCHEMA-REPLACEMENT",
                f"D2 schema replacement predecessor drifted: {name}",
            )
        definitions[name] = copy.deepcopy(replacement["value"])
    for name, definition in delta["add_definitions"].items():
        if name in definitions:
            _fail(
                "Refused",
                "F0V2B2D2-R-SCHEMA-ADDITION",
                f"D2 schema addition already exists: {name}",
            )
        definitions[name] = copy.deepcopy(definition)
    source["definitions"] = {name: definitions[name] for name in sorted(definitions)}
    return source


def _compile_schema() -> tuple[dict[str, Any], dict[str, str], dict[str, int]]:
    source = candidate_schema_source()
    b2b.FORMAT = CANDIDATE_SCHEMA_FORMAT
    b2b.SCOPE = CANDIDATE_SCHEMA_SCOPE
    b2b.PROFILE = copy.deepcopy(source["owner_profile"])
    codec.b2b.PROFILE = copy.deepcopy(source["owner_profile"])
    return b2b.compile_source(source)


VIEW_SCHEMAS, VIEW_OWNERS, VIEW_SCHEMA_STATS = _compile_schema()
EXECUTION_SCHEMA = VIEW_SCHEMAS["ExecutionView"]


def schema_evidence() -> dict[str, Any]:
    source = candidate_schema_source()
    grammar = {key: value for key, value in source.items() if key != "owner_profile"}
    return {
        "schema_grammar_sha256": _digest(grammar),
        "schema_source_sha256": _digest(source),
        **VIEW_SCHEMA_STATS,
    }


def _law(name: str) -> dict[str, str]:
    return {
        "profile": d1.PROFILE_DIGEST if hasattr(d1, "PROFILE_DIGEST") else source_profile(),
        "kind": "pir.semantic-law",
        "name": name,
    }


def source_profile() -> str:
    return candidate_schema_source()["owner_profile"]["profile_digest"]


def _ref(compiler: str, ordinal: int) -> dict[str, str]:
    return foundation._ordinal(compiler, ordinal)


def _type(value: object) -> dict[str, str]:
    return foundation._value_type_body(value)


def _value_type(
    core: object,
    outputs: tuple[tuple[object, ...], ...],
    reference: object,
) -> object:
    if type(reference) is base.PublicInputRef:
        return core.public_inputs[reference.ordinal].value_type
    if type(reference) is base.VerifierPrivateInputRef:
        return core.verifier_private_inputs[reference.ordinal].value_type
    if type(reference) is base.ConstantRef:
        return core.constants[reference.ordinal].value_type
    if type(reference) is base.DerivedValueRef:
        return core.derived_values[reference.ordinal].result_type
    if type(reference) is base.OccurrenceOutputRef:
        return outputs[reference.occurrence][reference.output_ordinal]
    _fail("Malformed", "F0V2B2D2-M-VALUE-REF", "ValueRef carrier differs")
    raise AssertionError("unreachable")


def _protocol_core(protocol_handle: object) -> tuple[object, str, object]:
    if (
        type(protocol_handle) is not d1.b2c0.AdmittedFreshProtocolSnapshot
        or not protocol_handle._issued_by(d1.b2c0._PROTOCOL_ISSUER)
        or protocol_handle.evaluator_fingerprint != d1.EVALUATOR_FINGERPRINT
        or protocol_handle.profile_reference
        != d1.candidate_profile_artifact().profile_id.internal_reference()
        or protocol_handle.core_handle.closure.fingerprint
        != protocol_handle.closure_fingerprint
    ):
        _fail(
            "Refused",
            "F0V2B2D2-R-PROTOCOL-AUTHORITY",
            "Fresh schema projection has no exact D1 Protocol authority",
        )
    core, scenario = d1._retained_core(protocol_handle.core_handle)
    try:
        profile, domain, _body = d1.b2c0._strict_profiled_body(
            protocol_handle.profiled_body, "D2 retained Fresh Protocol"
        )
        core_value, interpretation = d1.b2c0._record(
            domain, (0, 1), "D2 retained Fresh Protocol"
        )
        tag, payload = d1.b2c0._variant(interpretation, (0,), "Fresh interpretation")
        d1.b2c0._unit(payload, "Fresh interpretation payload")
        retained_core = d1.b2c0._content_ref(core_value, "Fresh Protocol Core")
    except Exception as error:
        _fail("Malformed", "F0V2B2D2-M-PROTOCOL", str(error))
    if (
        tag != 0
        or profile.internal_reference() != protocol_handle.profile_reference
        or retained_core.internal_reference() != protocol_handle.core_handle.core_reference
    ):
        _fail(
            "Refused",
            "F0V2B2D2-R-PROTOCOL-CORE",
            "Fresh Protocol no longer pairs to its retained D1 Core",
        )
    return core, scenario, protocol_handle.core_handle


def _strategy_stops(
    core: object, module_occurrences: Mapping[int, object]
) -> tuple[int, ...]:
    result: list[int] = []
    for occurrence_ref, occurrence in enumerate(core.occurrences):
        effect = occurrence.effect
        if type(effect) is base.ProverMessageEffect:
            result.append(occurrence_ref)
        elif type(effect) is oracle.PublishOracleEffect:
            declaration = core.oracles[effect.oracle]
            if declaration.origin is oracle.OracleOrigin.PROVER:
                result.append(occurrence_ref)
        elif type(effect) is d1.ModuleEffectRef:
            semantics = module_occurrences[occurrence_ref]
            if semantics.decision_class is not d1.ModuleDecisionClass.NO_PROVER_DECISION:
                result.append(occurrence_ref)
    return tuple(result)


def _terminal_rows(
    core: object,
    outputs: tuple[tuple[object, ...], ...],
    positions: Mapping[str, Mapping[int, int]],
) -> list[dict[int, Any]]:
    rows: list[dict[int, Any]] = []
    for terminal_ref, terminal in enumerate(core.terminals):
        occurrence_ref = positions["terminal"][terminal_ref]
        rows.append(
            {
                0: _ref("terminal-ref-body-v0", terminal_ref),
                1: _ref("occurrence-ref-body-v0", occurrence_ref),
                2: foundation._v(terminal.verdict.value),
                3: [
                    _type(_value_type(core, outputs, item))
                    for item in terminal.public_outputs
                ],
                4: [
                    _ref("occurrence-ref-body-v0", item)
                    for item in range(occurrence_ref + 1)
                ],
            }
        )
    return rows


def project_execution(protocol_handle: object) -> tuple[dict[int, Any], dict[str, Any]]:
    """Derive one exact candidate ExecutionView without executing a run."""

    core, scenario, core_handle = _protocol_core(protocol_handle)
    module_occurrences = d1._module_occurrence_semantics(
        core, scenario == "invalid-module-control-sink"
    )
    outputs = d1._output_types(core, module_occurrences)
    positions = d1._positions(core)
    core_id = k1.decode_content_reference(core_handle.core_reference)
    protocol_id = k1.decode_content_reference(protocol_handle.protocol_reference)

    resolver_rows = []
    challenge_rows = []
    for challenge_ref, challenge in enumerate(core.challenges):
        occurrence_ref = positions["challenge"][challenge_ref]
        prior = (
            challenge.correlation.prior_members
            if type(challenge.correlation) is base.JointCorrelation
            else ()
        )
        resolver_rows.append(
            {
                0: _ref("challenge-ref-body-v0", challenge_ref),
                1: _ref("occurrence-ref-body-v0", occurrence_ref),
                2: _type(challenge.value_type),
                3: foundation._module_ref(challenge.domain),
                4: foundation._module_ref(challenge.fresh_law),
                5: [foundation._value_ref(item) for item in challenge.public_conditions],
                6: [_ref("challenge-ref-body-v0", item) for item in prior],
            }
        )
        challenge_rows.append(
            {
                0: _ref("challenge-ref-body-v0", challenge_ref),
                1: _ref("occurrence-ref-body-v0", occurrence_ref),
                2: foundation._module_ref(challenge.fresh_law),
                3: _type(challenge.value_type),
            }
        )

    occurrence_rows = [
        {
            0: _ref("occurrence-ref-body-v0", occurrence_ref),
            1: [_type(item) for item in row],
        }
        for occurrence_ref, row in enumerate(outputs)
    ]

    oracle_rows: list[dict[str, Any]] = []
    for occurrence_ref, occurrence in enumerate(core.occurrences):
        effect = occurrence.effect
        if type(effect) is oracle.PublishOracleEffect:
            declaration = core.oracles[effect.oracle]
            publication_types = outputs[occurrence_ref]
            if type(declaration.publication_mode) is oracle.LogicalAccessOracle:
                observation = foundation._v(
                    1,
                    {
                        0: foundation._v(declaration.origin.value),
                        1: foundation._module_ref(
                            declaration.publication_mode.domain_law
                        ),
                    },
                )
            else:
                if len(publication_types) != 1:
                    _fail(
                        "CheckerFailure",
                        "F0V2B2D2-C-PUBLICATION-ARITY",
                        "value-publishing Oracle has another output arity",
                    )
                observation = foundation._v(0, _type(publication_types[0]))
            oracle_rows.append(
                foundation._v(
                    0,
                    {
                        0: _ref("occurrence-ref-body-v0", occurrence_ref),
                        1: _ref("oracle-ref-body-v0", effect.oracle),
                        2: oracle._mode_value(declaration.publication_mode),
                        3: foundation._v(oracle.OracleVisibility.PUBLIC.value),
                        4: [_type(item) for item in publication_types],
                        5: observation,
                    },
                )
            )
        elif type(effect) is oracle.QueryOracleEffect:
            declaration = core.oracles[effect.oracle]
            oracle_rows.append(
                foundation._v(
                    1,
                    {
                        0: _ref("occurrence-ref-body-v0", occurrence_ref),
                        1: _ref("oracle-ref-body-v0", effect.oracle),
                        2: _type(declaration.index_type),
                        3: foundation._v(effect.visibility.value),
                    },
                )
            )
        elif type(effect) is oracle.AnswerOracleEffect:
            query = core.occurrences[effect.query].effect
            if type(query) is not oracle.QueryOracleEffect or len(outputs[occurrence_ref]) != 1:
                _fail(
                    "CheckerFailure",
                    "F0V2B2D2-C-ANSWER-SHAPE",
                    "admitted Answer occurrence has another exact shape",
                )
            oracle_rows.append(
                foundation._v(
                    2,
                    {
                        0: _ref("occurrence-ref-body-v0", occurrence_ref),
                        1: _ref("oracle-ref-body-v0", query.oracle),
                        2: _type(outputs[occurrence_ref][0]),
                        3: foundation._v(query.visibility.value),
                    },
                )
            )

    terminal_rows = _terminal_rows(core, outputs, positions)
    strategy_rows = [
        {
            0: _ref("occurrence-ref-body-v0", occurrence_ref),
            1: [
                _ref("occurrence-ref-body-v0", item)
                for item in range(occurrence_ref)
            ],
        }
        for occurrence_ref in _strategy_stops(core, module_occurrences)
    ]
    runtime = {
        0: occurrence_rows,
        1: challenge_rows,
        2: oracle_rows,
        3: terminal_rows,
        4: [
            foundation._v(0, copy.deepcopy(terminal_rows)),
            foundation._v(1),
            foundation._v(2, strategy_rows),
        ],
        5: [
            foundation._v(index)
            for index, _name in enumerate(OPERATIONAL_NONCOMPLETION_NAMES)
        ],
    }
    value = {
        0: foundation._identifier("protocol-id-body-v0", protocol_id),
        1: foundation._identifier("core-id-body-v0", core_id),
        2: foundation._v(0),
        3: _law("core-admission-v0"),
        4: resolver_rows,
        5: _law("execution-and-replay-v0"),
        6: runtime,
        7: foundation._v(0),
        8: _law("execution-and-replay-v0"),
        9: _law("run-view-issuance-v0"),
    }
    body = codec.encode_value(EXECUTION_SCHEMA, value)
    return value, {
        "scenario": scenario,
        "core_domain_sha256": hashlib.sha256(core_handle.domain_body).hexdigest(),
        "body_bytes": len(body),
        "occurrence_receipts": len(occurrence_rows),
        "challenge_receipts": len(challenge_rows),
        "oracle_receipts": len(oracle_rows),
        "oracle_branches": tuple(item["case"] for item in oracle_rows),
        "terminal_alternatives": len(terminal_rows),
        "strategy_stop_alternatives": len(strategy_rows),
        "interpretation_failure_none": runtime[4][1] == foundation._v(1),
        "operational_noncompletion_classes": len(runtime[5]),
        "operational_noncompletion_names": OPERATIONAL_NONCOMPLETION_NAMES,
        "run_executions": 0,
        "replay_executions": 0,
    }


def execution_body(protocol_handle: object) -> bytes:
    value, _evidence = project_execution(protocol_handle)
    return codec.encode_value(EXECUTION_SCHEMA, value)


def _different(left: object, right: object) -> bool:
    return left != right


def _classify_substitution(expected: dict[int, Any], claimed: dict[int, Any]) -> str:
    expected_runtime = expected[6]
    claimed_runtime = claimed[6]
    for left, right in zip(expected_runtime[2], claimed_runtime[2]):
        if left["case"] != right["case"]:
            return "F0V2B2D2-R-RECEIPT-BRANCH"
    if _different(expected_runtime[1], claimed_runtime[1]):
        for left, right in zip(expected_runtime[1], claimed_runtime[1]):
            if left[1] != right[1]:
                return "F0V2B2D2-R-RECEIPT-COORDINATE"
            if left[3] != right[3]:
                return "F0V2B2D2-R-RECEIPT-TYPE"
    for left, right in zip(expected_runtime[2], claimed_runtime[2]):
        if left["case"] in (1, 2) and left["value"][3] != right["value"][3]:
            return "F0V2B2D2-R-RECEIPT-VISIBILITY"
        if left["case"] == 0 and left["value"][2] != right["value"][2]:
            return "F0V2B2D2-R-PUBLICATION-MODE"
        if (
            left["case"] == 0
            and left["value"][5]["case"] == 1
            and right["value"][5]["case"] != 1
        ):
            return "F0V2B2D2-R-FIXATION-MARKER"
    if _different(expected_runtime[0], claimed_runtime[0]):
        for left, right in zip(expected_runtime[0], claimed_runtime[0]):
            if len(left[1]) != len(right[1]):
                return "F0V2B2D2-R-RECEIPT-ARITY"
            if left[1] != right[1]:
                return "F0V2B2D2-R-RECEIPT-TYPE"
    if _different(expected_runtime[3], claimed_runtime[3]):
        return "F0V2B2D2-R-TERMINAL-REFERENCE"
    completed = expected_runtime[4][0]["value"]
    candidate = claimed_runtime[4][0]["value"]
    if _different(completed, candidate):
        for left, right in zip(completed, candidate):
            if left[0] != right[0] or left[1] != right[1]:
                return "F0V2B2D2-R-STOPPING-TERMINAL"
            if left[4] != right[4]:
                return "F0V2B2D2-R-INACTIVE-OCCURRENCE-RECEIPT"
    return "F0V2B2D2-R-SCHEMA-SUBSTITUTION"


def admit_schema_claim(protocol_handle: object, claimed: object) -> ClaimResult:
    try:
        expected, _evidence = project_execution(protocol_handle)
        try:
            claimed_body = codec.encode_value(EXECUTION_SCHEMA, claimed)
        except Exception as error:
            return ClaimResult(
                "Malformed", "F0V2B2D2-M-SCHEMA-CARRIER", str(error)
            )
        expected_body = codec.encode_value(EXECUTION_SCHEMA, expected)
        if claimed_body == expected_body:
            return ClaimResult(
                "Affirmative",
                "F0V2B2D2-A-EXACT-SCHEMA-CLAIM",
                "claimed ExecutionView body equals the owner-derived body",
            )
        if type(claimed) is not dict or set(claimed) != set(expected):
            return ClaimResult(
                "Refused",
                "F0V2B2D2-R-SCHEMA-SUBSTITUTION",
                "claimed schema body differs",
            )
        return ClaimResult(
            "Refused",
            _classify_substitution(expected, claimed),
            "claimed schema body differs from the exact Core/Fresh derivation",
        )
    except SchemaFailure as error:
        return ClaimResult(error.outcome, error.code, error.detail)
    except Exception as error:  # pragma: no cover - fail-closed defect lane
        return ClaimResult("CheckerFailure", "F0V2B2D2-CHECKER", str(error))
