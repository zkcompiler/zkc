"""Cold byte-derived Fresh completed-record schema projector for F0-V2B2D2.

This path does not import the typed D2 or D1 owner model.  It starts from the
canonical Core and Fresh Protocol bytes, reuses the independently written D1
parser/authenticator, compiles the D2 grammar with the iterative B2B compiler,
and derives the candidate ExecutionView body without a run.
"""

from __future__ import annotations

import copy
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
from types import ModuleType
from typing import Any, Mapping


ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
D1_COLD = ROOT / "evaluation/formal-source-integrated-graph-f0v2b2d1/independent.py"
SCHEMA_DELTA = HERE / "schema-delta.json"

CANDIDATE_SCHEMA_FORMAT = (
    "zkc.formal-source-fresh-run-schema-f0v2b2d2.schema-source.v0"
)
CANDIDATE_SCHEMA_SCOPE = "fresh-completed-record-schema-over-five-d1-carriers"
PREDECESSOR_SCHEMA_SHA256 = (
    "c87b09d89ddbe92f8a6cdad8eae6bb0dbcfea6ed69e65e335e551efba0f6e03d"
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


class ColdSchemaError(ValueError):
    """The cold D2 schema compiler or byte-derived projector refused input."""


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


d1 = _load("_zkc_f0v2b2d2_cold_d1", D1_COLD)
cold = d1.cold
k1 = d1.k1
codec = d1.codec
b2b = d1.schema.b2b

VIEW_SCHEMAS: dict[str, Any] = {}
VIEW_SCHEMA_STATS: dict[str, int] = {}
EXECUTION_SCHEMA: dict[str, Any] = {}
PROFILE_DIGEST = ""
SCHEMA_SOURCE: dict[str, Any] = {}


def _wire(value: object) -> bytes:
    return json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=True
    ).encode("ascii")


def _digest(value: object) -> str:
    return hashlib.sha256(_wire(value)).hexdigest()


def _load_json(path: Path, label: str) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        raise ColdSchemaError(f"{label} does not load: {error}") from error
    if type(value) is not dict:
        raise ColdSchemaError(f"{label} has another outer carrier")
    return value


def configure(profile_digest: str, profile_body_sha256: str) -> dict[str, Any]:
    """Compile the D2 delta independently over the exact cold D1 grammar."""

    global VIEW_SCHEMAS, VIEW_SCHEMA_STATS, EXECUTION_SCHEMA
    global PROFILE_DIGEST, SCHEMA_SOURCE

    d1.configure(profile_digest, profile_body_sha256)
    source = copy.deepcopy(d1.schema.SCHEMA_SOURCE)
    delta = _load_json(SCHEMA_DELTA, "D2 schema delta")
    if set(delta) != {
        "format",
        "predecessor",
        "candidate_format",
        "candidate_scope",
        "replace_definitions",
        "add_definitions",
    }:
        raise ColdSchemaError("D2 schema delta has another exact shape")
    if delta["predecessor"] != {
        "format": source.get("format"),
        "sha256": _digest(source),
    } or _digest(source) != PREDECESSOR_SCHEMA_SHA256:
        raise ColdSchemaError("D2 schema delta names another cold predecessor")
    if (
        delta["candidate_format"] != CANDIDATE_SCHEMA_FORMAT
        or delta["candidate_scope"] != CANDIDATE_SCHEMA_SCOPE
    ):
        raise ColdSchemaError("D2 schema delta names another candidate grammar")

    source["format"] = CANDIDATE_SCHEMA_FORMAT
    source["scope"] = CANDIDATE_SCHEMA_SCOPE
    definitions = source.get("definitions")
    if type(definitions) is not dict:
        raise ColdSchemaError("cold D2 definitions have another carrier")
    for name, replacement in delta["replace_definitions"].items():
        if (
            name not in definitions
            or type(replacement) is not dict
            or set(replacement) != {"prior_sha256", "value"}
            or _digest(definitions[name]) != replacement["prior_sha256"]
        ):
            raise ColdSchemaError(f"cold schema replacement drifted: {name}")
        definitions[name] = copy.deepcopy(replacement["value"])
    for name, definition in delta["add_definitions"].items():
        if name in definitions:
            raise ColdSchemaError(f"cold schema addition already exists: {name}")
        definitions[name] = copy.deepcopy(definition)
    source["definitions"] = {name: definitions[name] for name in sorted(definitions)}

    b2b.FORMAT = CANDIDATE_SCHEMA_FORMAT
    b2b.SCOPE = CANDIDATE_SCHEMA_SCOPE
    b2b.PROFILE = copy.deepcopy(source["owner_profile"])
    codec.b2b.PROFILE = copy.deepcopy(source["owner_profile"])
    schemas, _owners, stats = b2b.compile_source(source)
    grammar = {key: value for key, value in source.items() if key != "owner_profile"}
    VIEW_SCHEMAS = schemas
    VIEW_SCHEMA_STATS = stats
    EXECUTION_SCHEMA = schemas["ExecutionView"]
    PROFILE_DIGEST = profile_digest
    SCHEMA_SOURCE = source
    return {
        "schema_grammar_sha256": _digest(grammar),
        "schema_source_sha256": _digest(source),
        **stats,
    }


def _ref(compiler: str, ordinal: int) -> dict[str, str]:
    return cold._ordinal(compiler, ordinal)


def _type(value: object) -> dict[str, str]:
    return cold._value_type(value)


def _law(name: str) -> dict[str, str]:
    return {
        "profile": PROFILE_DIGEST,
        "kind": "pir.semantic-law",
        "name": name,
    }


def _output_types(
    core: dict[str, Any], modules: Mapping[int, dict[str, Any]]
) -> tuple[tuple[object, ...], ...]:
    rows: list[tuple[object, ...]] = []
    for occurrence_ref, occurrence in enumerate(core["occurrences"]):
        effect = occurrence["effect"]
        tag = effect["tag"]
        if tag in (0, 1):
            rows.append((effect["payload_type"],))
        elif tag == 2:
            rows.append((core["challenges"][effect["challenge"]]["type"],))
        elif tag == 3:
            rows.append((k1.value_type_datum(k1.BOOL),))
        elif tag in (4, 5):
            rows.append(())
        elif tag == 6:
            oracle_tag = effect["oracle_tag"]
            if oracle_tag == 0:
                rows.append(
                    d1.oraclecold._publication_types(
                        core["oracles"][effect["oracle"]]
                    )
                )
            elif oracle_tag == 1:
                rows.append(())
            else:
                if not 0 <= effect["query"] < occurrence_ref:
                    raise ColdSchemaError("Answer query is not earlier")
                query = core["occurrences"][effect["query"]]["effect"]
                if query["tag"] != 6 or query["oracle_tag"] != 1:
                    raise ColdSchemaError("Answer backlink does not name a Query")
                rows.append(
                    (d1.oraclecold._answer_type(core["oracles"][query["oracle"]]),)
                )
        elif tag == 7:
            rows.append(tuple(item["type"] for item in modules[occurrence_ref]["outputs"]))
        else:  # pragma: no cover - D1 parser closes the effect sum
            raise ColdSchemaError("cold output derivation found an unknown effect")
    return tuple(rows)


def _value_type(
    core: dict[str, Any],
    outputs: tuple[tuple[object, ...], ...],
    reference: tuple[int, int, int],
) -> object:
    tag, first, second = reference
    if tag == 0:
        return core["public_inputs"][first]["type"]
    if tag == 1:
        return core["private_inputs"][first]["type"]
    if tag == 2:
        return core["constants"][first]["type"]
    if tag == 3:
        return core["derived"][first]["type"]
    if tag == 4:
        return outputs[first][second]
    raise ColdSchemaError("cold ValueRef selected another case")


def _strategy_stops(
    core: dict[str, Any], modules: Mapping[int, dict[str, Any]]
) -> tuple[int, ...]:
    rows: list[int] = []
    for occurrence_ref, occurrence in enumerate(core["occurrences"]):
        effect = occurrence["effect"]
        if effect["tag"] == 0:
            rows.append(occurrence_ref)
        elif effect["tag"] == 6 and effect["oracle_tag"] == 0:
            if core["oracles"][effect["oracle"]]["origin"] == 1:
                rows.append(occurrence_ref)
        elif effect["tag"] == 7 and modules[occurrence_ref]["decision"] != 0:
            rows.append(occurrence_ref)
    return tuple(rows)


def _terminal_rows(
    core: dict[str, Any],
    outputs: tuple[tuple[object, ...], ...],
    positions: Mapping[str, Mapping[int, int]],
) -> list[dict[int, Any]]:
    rows: list[dict[int, Any]] = []
    for terminal_ref, terminal in enumerate(core["terminals"]):
        occurrence_ref = positions["terminal"][terminal_ref]
        rows.append(
            {
                0: _ref("terminal-ref-body-v0", terminal_ref),
                1: _ref("occurrence-ref-body-v0", occurrence_ref),
                2: cold._v(terminal["verdict"]),
                3: [
                    _type(_value_type(core, outputs, item))
                    for item in terminal["outputs"]
                ],
                4: [
                    _ref("occurrence-ref-body-v0", item)
                    for item in range(occurrence_ref + 1)
                ],
            }
        )
    return rows


def project(
    core_profiled_body: bytes,
    core_reference: bytes,
    protocol_profiled_body: bytes,
    protocol_reference: bytes,
    module_sources: tuple[tuple[bytes, bytes], ...],
    algorithm_preimages: tuple[tuple[bytes, bytes], ...],
    evaluation_contract_reference: bytes,
) -> tuple[dict[int, Any], dict[str, Any]]:
    """Authenticate exact bytes and derive the candidate ExecutionView."""

    if not PROFILE_DIGEST or not EXECUTION_SCHEMA:
        raise ColdSchemaError("cold D2 schema compiler is not configured")

    # Replay the complete D1 cold admission boundary before deriving D2 data.
    d1.project(
        core_profiled_body,
        core_reference,
        protocol_profiled_body,
        protocol_reference,
        module_sources,
        algorithm_preimages,
        evaluation_contract_reference,
    )
    try:
        core_profile, core_domain = cold._authenticated_subject(
            core_profiled_body,
            core_reference,
            "pir.interactive-core",
            "cold D2 Core",
        )
        protocol_profile, protocol_domain = cold._authenticated_subject(
            protocol_profiled_body,
            protocol_reference,
            "pir.protocol",
            "cold D2 Fresh Protocol",
        )
    except Exception as error:
        raise ColdSchemaError(str(error)) from error
    if core_profile != protocol_profile:
        raise ColdSchemaError("cold D2 Core and Protocol profiles differ")
    protocol_core, interpretation = d1._record(
        protocol_domain, (0, 1), "cold D2 Fresh Protocol"
    )
    tag, payload = d1._variant(interpretation, {0}, "Fresh interpretation")
    d1._unit(payload, "Fresh interpretation payload")
    if tag != 0 or d1._bytes(protocol_core, "Fresh Protocol Core") != core_reference:
        raise ColdSchemaError("cold D2 Protocol does not name the exact Core")

    core = d1._decode_core(core_domain)
    sources = d1._source_closure(core["used_modules"], module_sources)
    modules = d1._module_occurrences(core, sources)
    outputs = _output_types(core, modules)
    positions = d1._positions(core)

    resolver_rows = []
    challenge_rows = []
    for challenge_ref, challenge in enumerate(core["challenges"]):
        occurrence_ref = positions["challenge"][challenge_ref]
        resolver_rows.append(
            {
                0: _ref("challenge-ref-body-v0", challenge_ref),
                1: _ref("occurrence-ref-body-v0", occurrence_ref),
                2: _type(challenge["type"]),
                3: cold._module_ref(challenge["domain"]),
                4: cold._module_ref(challenge["fresh_law"]),
                5: [cold._value_ref(item) for item in challenge["conditions"]],
                6: [
                    _ref("challenge-ref-body-v0", item)
                    for item in challenge["correlation"]["prior"]
                ],
            }
        )
        challenge_rows.append(
            {
                0: _ref("challenge-ref-body-v0", challenge_ref),
                1: _ref("occurrence-ref-body-v0", occurrence_ref),
                2: cold._module_ref(challenge["fresh_law"]),
                3: _type(challenge["type"]),
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
    for occurrence_ref, occurrence in enumerate(core["occurrences"]):
        effect = occurrence["effect"]
        if effect["tag"] != 6:
            continue
        oracle_tag = effect["oracle_tag"]
        if oracle_tag == 0:
            declaration = core["oracles"][effect["oracle"]]
            publication_types = outputs[occurrence_ref]
            if declaration["mode"]["tag"] == 2:
                observation = cold._v(
                    1,
                    {
                        0: cold._v(declaration["origin"]),
                        1: cold._module_ref(declaration["mode"]["domain_law"]),
                    },
                )
            else:
                if len(publication_types) != 1:
                    raise ColdSchemaError(
                        "cold value-publishing Oracle has another output arity"
                    )
                observation = cold._v(0, _type(publication_types[0]))
            oracle_rows.append(
                cold._v(
                    0,
                    {
                        0: _ref("occurrence-ref-body-v0", occurrence_ref),
                        1: _ref("oracle-ref-body-v0", effect["oracle"]),
                        2: d1.oraclecold._mode_value(declaration["mode"]),
                        3: cold._v(0),
                        4: [_type(item) for item in publication_types],
                        5: observation,
                    },
                )
            )
        elif oracle_tag == 1:
            declaration = core["oracles"][effect["oracle"]]
            oracle_rows.append(
                cold._v(
                    1,
                    {
                        0: _ref("occurrence-ref-body-v0", occurrence_ref),
                        1: _ref("oracle-ref-body-v0", effect["oracle"]),
                        2: _type(declaration["index_type"]),
                        3: cold._v(effect["visibility"]),
                    },
                )
            )
        else:
            query = core["occurrences"][effect["query"]]["effect"]
            if query["tag"] != 6 or query["oracle_tag"] != 1 or len(outputs[occurrence_ref]) != 1:
                raise ColdSchemaError("cold Answer has another exact shape")
            oracle_rows.append(
                cold._v(
                    2,
                    {
                        0: _ref("occurrence-ref-body-v0", occurrence_ref),
                        1: _ref("oracle-ref-body-v0", query["oracle"]),
                        2: _type(outputs[occurrence_ref][0]),
                        3: cold._v(query["visibility"]),
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
        for occurrence_ref in _strategy_stops(core, modules)
    ]
    runtime = {
        0: occurrence_rows,
        1: challenge_rows,
        2: oracle_rows,
        3: terminal_rows,
        4: [
            cold._v(0, copy.deepcopy(terminal_rows)),
            cold._v(1),
            cold._v(2, strategy_rows),
        ],
        5: [
            cold._v(index)
            for index, _name in enumerate(OPERATIONAL_NONCOMPLETION_NAMES)
        ],
    }
    value = {
        0: cold._identifier("protocol-id-body-v0", protocol_reference),
        1: cold._identifier("core-id-body-v0", core_reference),
        2: cold._v(0),
        3: _law("core-admission-v0"),
        4: resolver_rows,
        5: _law("execution-and-replay-v0"),
        6: runtime,
        7: cold._v(0),
        8: _law("execution-and-replay-v0"),
        9: _law("run-view-issuance-v0"),
    }
    body = codec.encode_value(EXECUTION_SCHEMA, value)
    core_sha256 = hashlib.sha256(k1.encode_datum(core_domain)).hexdigest()
    return value, {
        "core_domain_sha256": core_sha256,
        "body_bytes": len(body),
        "occurrence_receipts": len(occurrence_rows),
        "challenge_receipts": len(challenge_rows),
        "oracle_receipts": len(oracle_rows),
        "oracle_branches": tuple(item["case"] for item in oracle_rows),
        "terminal_alternatives": len(terminal_rows),
        "strategy_stop_alternatives": len(strategy_rows),
        "interpretation_failure_none": runtime[4][1] == cold._v(1),
        "operational_noncompletion_classes": len(runtime[5]),
        "operational_noncompletion_names": OPERATIONAL_NONCOMPLETION_NAMES,
        "run_executions": 0,
        "replay_executions": 0,
    }


def encode_execution(value: dict[int, Any]) -> bytes:
    if not EXECUTION_SCHEMA:
        raise ColdSchemaError("cold D2 schema compiler is not configured")
    return codec.encode_value(EXECUTION_SCHEMA, value)
