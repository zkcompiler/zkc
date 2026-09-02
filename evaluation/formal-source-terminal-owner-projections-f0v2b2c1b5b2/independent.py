"""Cold byte-derived Terminal projector for F0-V2B2C1B5B2.

This path does not import the typed B5B2 owner or the B5B1 abstract analyzer.
It authenticates Core and Protocol bytes, authenticates portable-algorithm
preimages, exhaustively executes the finite Boolean witness, and independently
derives the six owner views under the synthetic Interaction profile.
"""

from __future__ import annotations

import copy
import hashlib
import heapq
import importlib.util
import itertools
import json
from pathlib import Path
import sys
from types import ModuleType
from typing import Any, Mapping


ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
PREDECESSOR_COLD = (
    ROOT
    / "evaluation"
    / "formal-source-claim-reduction-owner-projections-f0v2b2c1b3"
    / "independent.py"
)
B2B_SOURCE = (
    ROOT / "evaluation" / "formal-source-view-schema-f0v2b2b" / "schema-source.json"
)
SCHEMA_DELTA = HERE / "schema-delta.json"

CANDIDATE_SCHEMA_FORMAT = (
    "zkc.formal-source-terminal-owner-projections-f0v2b2c1b5b2.schema-source.v0"
)
CANDIDATE_SCHEMA_SCOPE = "interaction-r2-expanded-terminal-normalized-six-view-grammar"


class ColdTerminalError(ValueError):
    """Fail-closed result from the independent byte-derived path."""


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


prior = _load("_zkc_f0v2b2c1b5b2_cold_b3", PREDECESSOR_COLD)
cold = prior.cold
k1 = cold.k1
b2b = cold.b2b
codec = cold.codec

VIEW_SCHEMAS: dict[str, Any] = {}
VIEW_OWNERS: dict[str, str] = {}
VIEW_SCHEMA_STATS: dict[str, int] = {}
PROFILE_DIGEST = ""
PROFILE_BODY_SHA256 = ""
SCHEMA_SOURCE: dict[str, Any] = {}
_PC_NODE_SCHEMA: dict[str, Any] = {}
_PC_EDGE_SCHEMA: dict[str, Any] = {}


def _wire(value: object) -> bytes:
    return json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=True
    ).encode("ascii")


def _digest(value: object) -> str:
    return hashlib.sha256(_wire(value)).hexdigest()


def _schema_field(schema: dict[str, Any], ordinal: int) -> dict[str, Any]:
    selected = [child for field, child in schema["fields"] if field == ordinal]
    if len(selected) != 1:
        raise ColdTerminalError(f"schema record has no unique field {ordinal}")
    return selected[0]


def _load_json(path: Path, label: str) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        raise ColdTerminalError(f"{label} does not load: {error}") from error
    if type(value) is not dict:
        raise ColdTerminalError(f"{label} has another outer carrier")
    return value


def configure(profile_digest: str, profile_body_sha256: str) -> dict[str, Any]:
    """Independently compile the delta-bound candidate view grammar."""

    global PROFILE_DIGEST, PROFILE_BODY_SHA256, SCHEMA_SOURCE
    global VIEW_SCHEMAS, VIEW_OWNERS, VIEW_SCHEMA_STATS
    global _PC_NODE_SCHEMA, _PC_EDGE_SCHEMA

    if (
        type(profile_digest) is not str
        or len(profile_digest) != 64
        or type(profile_body_sha256) is not str
        or len(profile_body_sha256) != 64
    ):
        raise ColdTerminalError("candidate profile evidence is malformed")
    source = _load_json(B2B_SOURCE, "B2B schema source")
    delta = _load_json(SCHEMA_DELTA, "B5B2 schema delta")
    expected_delta = {
        "format",
        "predecessor",
        "candidate_format",
        "candidate_scope",
        "remove_definitions",
        "replace_definitions",
        "add_definitions",
    }
    if set(delta) != expected_delta:
        raise ColdTerminalError("schema delta has another exact shape")
    if delta["predecessor"] != {
        "format": source.get("format"),
        "sha256": _digest(source),
    }:
        raise ColdTerminalError("schema delta names another predecessor")
    if (
        delta["candidate_format"] != CANDIDATE_SCHEMA_FORMAT
        or delta["candidate_scope"] != CANDIDATE_SCHEMA_SCOPE
    ):
        raise ColdTerminalError("schema delta names another candidate grammar")

    candidate = copy.deepcopy(source)
    candidate["format"] = CANDIDATE_SCHEMA_FORMAT
    candidate["scope"] = CANDIDATE_SCHEMA_SCOPE
    definitions = candidate.get("definitions")
    if type(definitions) is not dict:
        raise ColdTerminalError("schema definitions have another carrier")
    for name, expected in delta["remove_definitions"].items():
        if name not in definitions or _digest(definitions[name]) != expected:
            raise ColdTerminalError(f"schema removal predecessor drifted: {name}")
        del definitions[name]
    for name, replacement in delta["replace_definitions"].items():
        if (
            name not in definitions
            or type(replacement) is not dict
            or set(replacement) != {"prior_sha256", "value"}
            or _digest(definitions[name]) != replacement["prior_sha256"]
        ):
            raise ColdTerminalError(f"schema replacement predecessor drifted: {name}")
        definitions[name] = copy.deepcopy(replacement["value"])
    for name, definition in delta["add_definitions"].items():
        if name in definitions:
            raise ColdTerminalError(f"schema addition already exists: {name}")
        definitions[name] = copy.deepcopy(definition)
    candidate["definitions"] = {name: definitions[name] for name in sorted(definitions)}
    grammar = {key: value for key, value in candidate.items() if key != "owner_profile"}
    candidate["owner_profile"] = {
        "key": "interaction",
        "revision": 2,
        "profile_digest": profile_digest,
        "profile_body_sha256": profile_body_sha256,
    }

    b2b.FORMAT = CANDIDATE_SCHEMA_FORMAT
    b2b.SCOPE = CANDIDATE_SCHEMA_SCOPE
    b2b.PROFILE = copy.deepcopy(candidate["owner_profile"])
    codec.b2b.PROFILE = copy.deepcopy(candidate["owner_profile"])
    schemas, owners, stats = b2b.compile_source(candidate)
    graph_schema = _schema_field(schemas["PublicCoinView"], 1)
    PROFILE_DIGEST = profile_digest
    PROFILE_BODY_SHA256 = profile_body_sha256
    SCHEMA_SOURCE = candidate
    VIEW_SCHEMAS, VIEW_OWNERS, VIEW_SCHEMA_STATS = schemas, owners, stats
    _PC_NODE_SCHEMA = _schema_field(graph_schema, 0)["element"]
    _PC_EDGE_SCHEMA = _schema_field(graph_schema, 1)["element"]
    cold.PROFILE_DIGEST = profile_digest
    prior.PROFILE_DIGEST = profile_digest
    return {
        "schema_grammar_sha256": _digest(grammar),
        "schema_source_sha256": _digest(candidate),
        **stats,
    }


def _record(value: object, ordinals: tuple[int, ...], label: str) -> tuple[object, ...]:
    try:
        return cold._record(value, ordinals, label)
    except Exception as error:
        raise ColdTerminalError(str(error)) from error


def _sequence(value: object, label: str) -> tuple[object, ...]:
    try:
        return cold._sequence(value, label)
    except Exception as error:
        raise ColdTerminalError(str(error)) from error


def _variant(value: object, cases: set[int], label: str) -> tuple[int, object]:
    try:
        return cold._variant(value, cases, label)
    except Exception as error:
        raise ColdTerminalError(str(error)) from error


def _nat(value: object, label: str) -> int:
    try:
        return cold._nat(value, label)
    except Exception as error:
        raise ColdTerminalError(str(error)) from error


def _bytes(value: object, label: str) -> bytes:
    try:
        return cold._bytes(value, label)
    except Exception as error:
        raise ColdTerminalError(str(error)) from error


def _unit(value: object, label: str) -> None:
    try:
        cold._unit(value, label)
    except Exception as error:
        raise ColdTerminalError(str(error)) from error


def _value_ref(value: object) -> tuple[int, int, int]:
    try:
        return cold._parse_value_ref(value)
    except Exception as error:
        raise ColdTerminalError(str(error)) from error


def _guard(value: object) -> dict[str, Any]:
    try:
        return cold._parse_guard(value)
    except Exception as error:
        raise ColdTerminalError(str(error)) from error


def _parse_check(value: object) -> dict[str, Any]:
    algorithm, contract, inputs = _record(value, (0, 1, 2), "Check")
    return {
        "algorithm": _bytes(algorithm, "Check algorithm"),
        "contract": _bytes(contract, "Check contract"),
        "inputs": tuple(_value_ref(item) for item in _sequence(inputs, "Check inputs")),
    }


def _parse_terminal(value: object) -> dict[str, Any]:
    verdict, outputs, checks, reductions, claims = _record(
        value, (0, 1, 2, 3, 4), "expanded Terminal"
    )
    verdict_tag, verdict_payload = _variant(verdict, {0, 1, 2}, "verdict")
    _unit(verdict_payload, "verdict payload")
    result = {
        "verdict": verdict_tag,
        "outputs": tuple(
            _value_ref(item) for item in _sequence(outputs, "Terminal outputs")
        ),
        "checks": tuple(
            _nat(item, "required Check")
            for item in _sequence(checks, "required Checks")
        ),
        "reductions": tuple(
            _nat(item, "required Reduction")
            for item in _sequence(reductions, "required Reductions")
        ),
        "claims": tuple(
            _nat(item, "terminal Claim")
            for item in _sequence(claims, "terminal Claims")
        ),
    }
    for name in ("checks", "reductions", "claims"):
        values = result[name]
        if values != tuple(sorted(set(values))):
            raise ColdTerminalError(f"Terminal {name} are not sorted and unique")
    return result


def _parse_effect(value: object) -> dict[str, Any]:
    tag, payload = _variant(value, set(range(8)), "Core effect")
    if tag == 3:
        return {"tag": tag, "body": value, "check": _nat(payload, "Check backlink")}
    if tag == 4:
        return {
            "tag": tag,
            "body": value,
            "reduction": _nat(payload, "Reduction backlink"),
        }
    if tag == 5:
        return {
            "tag": tag,
            "body": value,
            "terminal": _nat(payload, "Terminal backlink"),
        }
    raise ColdTerminalError(f"effect tag {tag} is outside the B5B2 slice")


def decode_core(domain_body: bytes) -> dict[str, Any]:
    """Decode the complete candidate domain without typed-owner objects."""

    if type(domain_body) is not bytes or not domain_body:
        raise ColdTerminalError("Core domain body is not exact bytes")
    try:
        root = k1.decode_datum(domain_body)
    except Exception as error:
        raise ColdTerminalError(f"Core domain does not decode: {error}") from error
    if k1.encode_datum(root) != domain_body:
        raise ColdTerminalError("Core domain does not round-trip")
    fields = _record(root, tuple(range(14)), "InteractiveCore")
    tables = tuple(
        _sequence(value, f"InteractiveCore field {index}")
        for index, value in enumerate(fields)
    )
    if any(tables[index] for index in (2, 3, 4, 7, 8)):
        raise ColdTerminalError("Core contains another constructor slice")
    public_inputs = tuple(
        {"type": _record(item, (0,), "public input")[0]} for item in tables[1]
    )
    scopes: list[dict[str, int | None]] = []
    for item in tables[5]:
        parent, opening = _record(item, (0, 1), "scope")
        parent_tag, parent_payload = _variant(parent, {0, 1}, "scope parent")
        opening_tag, opening_payload = _variant(opening, {0, 1}, "scope opening")
        if parent_tag == 0:
            _unit(parent_payload, "absent parent")
        if opening_tag == 0:
            _unit(opening_payload, "initial opening")
        scopes.append(
            {
                "parent": None if parent_tag == 0 else _nat(parent_payload, "parent"),
                "opening": None
                if opening_tag == 0
                else _nat(opening_payload, "opening"),
            }
        )
    bindings: list[dict[str, Any]] = []
    for item in tables[6]:
        scope, binding_class, value = _record(item, (0, 1, 2), "binding")
        class_tag, class_payload = _variant(binding_class, {0, 1, 2}, "binding class")
        _unit(class_payload, "binding class payload")
        bindings.append(
            {
                "scope": _nat(scope, "binding scope"),
                "class": class_tag,
                "value": _value_ref(value),
            }
        )
    occurrences = tuple(
        {
            "scope": _nat(
                _record(item, (0, 1, 2), "occurrence")[0], "occurrence scope"
            ),
            "guard": _guard(_record(item, (0, 1, 2), "occurrence")[1]),
            "effect": _parse_effect(_record(item, (0, 1, 2), "occurrence")[2]),
        }
        for item in tables[13]
    )
    return {
        "used_modules": tuple(_bytes(item, "used module") for item in tables[0]),
        "public_inputs": public_inputs,
        "scopes": tuple(scopes),
        "bindings": tuple(bindings),
        "checks": tuple(_parse_check(item) for item in tables[9]),
        "claims": tuple(prior._parse_claim(item) for item in tables[10]),
        "reductions": tuple(prior._parse_reduction(item) for item in tables[11]),
        "terminals": tuple(_parse_terminal(item) for item in tables[12]),
        "occurrences": occurrences,
    }


def _algorithm_reference(preimage: bytes) -> bytes:
    try:
        identifier = k1.content_id(
            k1.PORTABLE_ALGORITHM_KIND,
            preimage,
            semantic_regime=k1.SEMANTIC_REGIME_ID,
        )
    except Exception as error:
        raise ColdTerminalError(
            f"algorithm identity does not reconstruct: {error}"
        ) from error
    return identifier.internal_reference()


def _parse_algorithms(
    preimages: Mapping[bytes, bytes], required: set[bytes]
) -> dict[bytes, dict[str, Any]]:
    if type(preimages) is not dict or set(preimages) != required:
        raise ColdTerminalError("algorithm preimage closure is not exact")
    bool_type = k1.value_type_datum(k1.BOOL)
    result: dict[bytes, dict[str, Any]] = {}
    for reference, raw in preimages.items():
        if type(reference) is not bytes or type(raw) is not bytes or not raw:
            raise ColdTerminalError("algorithm closure has another carrier")
        try:
            datum = k1.decode_datum(raw)
        except Exception as error:
            raise ColdTerminalError(
                f"algorithm preimage does not decode: {error}"
            ) from error
        if k1.encode_datum(datum) != raw or _algorithm_reference(raw) != reference:
            raise ColdTerminalError("algorithm preimage does not authenticate")
        kind, inputs, term, primitives = _record(
            datum, (0, 1, 2, 3), "algorithm preimage"
        )
        if type(kind) is not k1.Symbol:
            raise ColdTerminalError("algorithm kind is not a Symbol")
        input_types = _sequence(inputs, "algorithm input types")
        if not input_types or any(item != bool_type for item in input_types):
            raise ColdTerminalError("algorithm ABI is not nonempty Boolean-to-Boolean")
        if _sequence(primitives, "algorithm primitive closure"):
            raise ColdTerminalError("cold Boolean algorithm has primitive dependencies")
        parsed = {"kind": kind.value, "arity": len(input_types), "term": term}
        for assignment in itertools.product((False, True), repeat=len(input_types)):
            if type(_eval_term(term, assignment)) is not bool:
                raise ColdTerminalError("algorithm does not return an exact Boolean")
        result[reference] = parsed
    return result


def _eval_term(term: object, environment: tuple[bool, ...]) -> bool:
    tag, payload = _variant(term, set(range(15)), "Boolean term")
    bool_type = k1.value_type_datum(k1.BOOL)
    if tag == 0:
        value_type, value = _record(payload, (0, 1), "Boolean literal")
        if value_type != bool_type or type(value) is not bool:
            raise ColdTerminalError("literal is not an exact Boolean")
        return value
    if tag == 1:
        index, value_type = _record(payload, (0, 1), "Boolean variable")
        ordinal = _nat(index, "variable index")
        if value_type != bool_type or not 0 <= ordinal < len(environment):
            raise ColdTerminalError("Boolean variable is ill-typed or unbound")
        return environment[ordinal]
    if tag == 2:
        bound, body = _record(payload, (0, 1), "Boolean Let")
        return _eval_term(body, (_eval_term(bound, environment), *environment))
    if tag == 14:
        condition, when_true, when_false = _record(
            payload, (0, 1, 2), "Boolean Conditional"
        )
        return _eval_term(
            when_true if _eval_term(condition, environment) else when_false,
            environment,
        )
    raise ColdTerminalError(f"term tag {tag} is outside the cold Boolean fragment")


def _eval_algorithm(
    algorithms: Mapping[bytes, dict[str, Any]],
    reference: bytes,
    inputs: tuple[bool, ...],
) -> bool:
    try:
        algorithm = algorithms[reference]
    except KeyError as error:
        raise ColdTerminalError("algorithm reference has no preimage") from error
    if len(inputs) != algorithm["arity"] or any(
        type(item) is not bool for item in inputs
    ):
        raise ColdTerminalError("algorithm invocation differs from its Boolean ABI")
    return _eval_term(algorithm["term"], inputs)


def _type_of(
    core: dict[str, Any],
    outputs: tuple[tuple[object, ...], ...],
    reference: tuple[int, int, int],
) -> object:
    tag, first, second = reference
    try:
        if tag == 0:
            return core["public_inputs"][first]["type"]
        if tag == 4:
            return outputs[first][second]
    except (IndexError, KeyError) as error:
        raise ColdTerminalError("ValueRef is absent") from error
    raise ColdTerminalError("ValueRef belongs to another B5B2 slice")


def _producer(reference: tuple[int, int, int]) -> tuple[int, ...]:
    tag, first, second = reference
    if tag == 0:
        return tag, first
    if tag == 4:
        return 8, first, second
    raise ColdTerminalError("ValueRef has no producer in the B5B2 slice")


def _module_ref_info(value: object) -> tuple[bytes, str, int]:
    tag, payload = _variant(value, {0, 1}, "module declaration reference")
    if tag != 1:
        raise ColdTerminalError("declaration reference is not module-owned")
    owner, kind, ordinal = _record(payload, (0, 1, 2), "module declaration")
    if type(kind) is not k1.Symbol:
        raise ColdTerminalError("declaration kind is not a Symbol")
    return (
        _bytes(owner, "declaration module"),
        kind.value,
        _nat(ordinal, "declaration ordinal"),
    )


def _outputs(core: dict[str, Any]) -> tuple[tuple[object, ...], ...]:
    return tuple(
        (k1.value_type_datum(k1.BOOL),) if item["effect"]["tag"] == 3 else ()
        for item in core["occurrences"]
    )


def _positions(
    core: dict[str, Any], effect_tag: int, table: str, backlink: str
) -> dict[int, int]:
    rows: dict[int, list[int]] = {index: [] for index in range(len(core[table]))}
    for occurrence_ref, occurrence in enumerate(core["occurrences"]):
        effect = occurrence["effect"]
        if effect["tag"] != effect_tag:
            continue
        try:
            rows[effect[backlink]].append(occurrence_ref)
        except KeyError as error:
            raise ColdTerminalError(f"{backlink} backlink is absent") from error
    if any(len(items) != 1 for items in rows.values()):
        raise ColdTerminalError(f"{table} backlinks are not one-to-one")
    return {key: value[0] for key, value in rows.items()}


def _value(
    reference: tuple[int, int, int],
    public_inputs: tuple[bool, ...],
    occurrence_outputs: Mapping[tuple[int, int], bool],
) -> bool:
    tag, first, second = reference
    if tag == 0:
        try:
            return public_inputs[first]
        except IndexError as error:
            raise ColdTerminalError("public input is absent at execution") from error
    if tag == 4:
        try:
            return occurrence_outputs[(first, second)]
        except KeyError as error:
            raise ColdTerminalError(
                "occurrence output is unavailable at execution"
            ) from error
    raise ColdTerminalError("runtime ValueRef is outside the Boolean slice")


def _simulate(
    core: dict[str, Any],
    algorithms: Mapping[bytes, dict[str, Any]],
    facts: dict[str, Any],
) -> dict[str, Any]:
    output_claims = facts["output_claims"]
    initial_claims = {
        index
        for index, claim in enumerate(core["claims"])
        if claim["source"]["tag"] == 0
    }
    verdict_counts = {0: 0, 1: 0, 2: 0}
    paths: list[tuple[int, ...]] = []
    for assignment in itertools.product(
        (False, True), repeat=len(core["public_inputs"])
    ):
        occurrence_outputs: dict[tuple[int, int], bool] = {}
        live = set(initial_claims)
        applied: set[int] = set()
        active_path: list[int] = []
        terminal_seen = False
        for occurrence_ref, occurrence in enumerate(core["occurrences"]):
            guard = occurrence["guard"]
            active = guard["tag"] == 0 or _eval_algorithm(
                algorithms,
                guard["algorithm"],
                tuple(
                    _value(item, assignment, occurrence_outputs)
                    for item in guard["inputs"]
                ),
            )
            if not active:
                continue
            active_path.append(occurrence_ref)
            effect = occurrence["effect"]
            if effect["tag"] == 3:
                check = core["checks"][effect["check"]]
                occurrence_outputs[(occurrence_ref, 0)] = _eval_algorithm(
                    algorithms,
                    check["algorithm"],
                    tuple(
                        _value(item, assignment, occurrence_outputs)
                        for item in check["inputs"]
                    ),
                )
                continue
            if effect["tag"] == 4:
                reduction_ref = effect["reduction"]
                reduction = core["reductions"][reduction_ref]
                for claim_ref in reduction["input_claims"]:
                    if claim_ref not in live:
                        raise ColdTerminalError(
                            "active reduction consumes an unavailable Claim"
                        )
                    if core["claims"][claim_ref]["usage"] == 0:
                        live.remove(claim_ref)
                for output_ordinal in range(len(reduction["output_contracts"])):
                    live.add(output_claims[(reduction_ref, output_ordinal)])
                applied.add(reduction_ref)
                continue
            terminal_ref = effect["terminal"]
            terminal = core["terminals"][terminal_ref]
            for check_ref in terminal["checks"]:
                check_occurrence = facts["check_positions"][check_ref]
                if occurrence_outputs.get((check_occurrence, 0)) is not True:
                    raise ColdTerminalError(
                        "active Terminal does not directly require a true Check output"
                    )
            if not set(terminal["reductions"]) <= applied:
                raise ColdTerminalError(
                    "active Terminal requires an unapplied Reduction"
                )
            if terminal["claims"] != tuple(sorted(live)):
                raise ColdTerminalError(
                    "active Terminal does not name the exact live Claim set"
                )
            verdict_counts[terminal["verdict"]] += 1
            terminal_seen = True
            break
        if not terminal_seen:
            raise ColdTerminalError(
                "one public-input assignment has no active Terminal"
            )
        paths.append(tuple(active_path))
    return {
        "assignments": len(paths),
        "verdict_counts": {
            "Accept": verdict_counts[0],
            "Reject": verdict_counts[1],
            "Abort": verdict_counts[2],
        },
        "paths": tuple(paths),
    }


def _validate(
    core: dict[str, Any],
    algorithm_preimages: Mapping[bytes, bytes],
    evaluation_contract_reference: bytes,
) -> tuple[tuple[tuple[object, ...], ...], dict[str, Any], dict[bytes, dict[str, Any]]]:
    bool_type = k1.value_type_datum(k1.BOOL)
    if (
        not core["public_inputs"]
        or not core["checks"]
        or not core["claims"]
        or not core["reductions"]
        or not core["terminals"]
        or not core["occurrences"]
    ):
        raise ColdTerminalError("candidate omits a required nonempty table")
    if tuple(item["type"] for item in core["public_inputs"]) != (bool_type,) * len(
        core["public_inputs"]
    ):
        raise ColdTerminalError("public-input domain is not exactly Boolean")
    if core["scopes"] != ({"parent": None, "opening": None},):
        raise ColdTerminalError("candidate does not have one exact root scope")
    if type(evaluation_contract_reference) is not bytes:
        raise ColdTerminalError("evaluation-contract reference has another carrier")

    outputs = _outputs(core)
    available: set[tuple[int, int, int]] = {
        (0, index, 0) for index in range(len(core["public_inputs"]))
    }
    algorithm_refs: set[bytes] = set()
    bound_inputs: set[int] = set()
    binding_triples: set[tuple[object, ...]] = set()
    for binding in core["bindings"]:
        if binding["scope"] != 0:
            raise ColdTerminalError("binding is outside the root scope")
        _type_of(core, outputs, binding["value"])
        triple = (binding["scope"], binding["class"], binding["value"])
        if triple in binding_triples:
            raise ColdTerminalError("public binding triple repeats")
        binding_triples.add(triple)
        if binding["value"][0] == 0:
            bound_inputs.add(binding["value"][1])
    if bound_inputs != set(range(len(core["public_inputs"]))):
        raise ColdTerminalError("public-input binding coverage is incomplete")

    for occurrence_ref, occurrence in enumerate(core["occurrences"]):
        if occurrence["scope"] != 0:
            raise ColdTerminalError("occurrence is outside the root scope")
        guard = occurrence["guard"]
        if guard["tag"] == 1:
            algorithm_refs.add(guard["algorithm"])
            if guard["contract"] != evaluation_contract_reference:
                raise ColdTerminalError("guard evaluation contract differs")
            if any(item not in available for item in guard["inputs"]):
                raise ColdTerminalError("guard reads a future or absent value")
            if any(
                _type_of(core, outputs, item) != bool_type for item in guard["inputs"]
            ):
                raise ColdTerminalError("guard input is not Boolean")
        effect = occurrence["effect"]
        if effect["tag"] == 3:
            try:
                check = core["checks"][effect["check"]]
            except IndexError as error:
                raise ColdTerminalError("Check backlink is absent") from error
            algorithm_refs.add(check["algorithm"])
            if check["contract"] != evaluation_contract_reference:
                raise ColdTerminalError("Check evaluation contract differs")
            if any(item not in available for item in check["inputs"]):
                raise ColdTerminalError("Check reads a future or absent value")
            if any(
                _type_of(core, outputs, item) != bool_type for item in check["inputs"]
            ):
                raise ColdTerminalError("Check input is not Boolean")
        elif effect["tag"] == 4:
            if not 0 <= effect["reduction"] < len(core["reductions"]):
                raise ColdTerminalError("Reduction backlink is absent")
        elif effect["tag"] == 5:
            if not 0 <= effect["terminal"] < len(core["terminals"]):
                raise ColdTerminalError("Terminal backlink is absent")
            if any(
                item not in available
                for item in core["terminals"][effect["terminal"]]["outputs"]
            ):
                raise ColdTerminalError("Terminal reads a future or absent value")
        for output_ordinal in range(len(outputs[occurrence_ref])):
            available.add((4, occurrence_ref, output_ordinal))

    algorithms = _parse_algorithms(dict(algorithm_preimages), algorithm_refs)
    for occurrence in core["occurrences"]:
        guard = occurrence["guard"]
        if guard["tag"] == 1 and algorithms[guard["algorithm"]]["arity"] != len(
            guard["inputs"]
        ):
            raise ColdTerminalError("guard algorithm ABI differs")
    for check in core["checks"]:
        if algorithms[check["algorithm"]]["arity"] != len(check["inputs"]):
            raise ColdTerminalError("Check algorithm ABI differs")

    check_positions = _positions(core, 3, "checks", "check")
    reduction_positions = _positions(core, 4, "reductions", "reduction")
    terminal_positions = _positions(core, 5, "terminals", "terminal")

    module_refs: list[object] = []
    output_claims: dict[tuple[int, int], int] = {}
    for claim_ref, claim in enumerate(core["claims"]):
        module_refs.append(claim["contract"])
        _owner, kind, _ordinal = _module_ref_info(claim["contract"])
        if kind != "pir.claim-contract" or claim["scope"] != 0:
            raise ColdTerminalError("Claim contract or scope differs")
        source = claim["source"]
        if source["tag"] == 0:
            binding_ref = source["binding"]
            if not 0 <= binding_ref < len(core["bindings"]):
                raise ColdTerminalError("initial Claim binding is absent")
            if core["bindings"][binding_ref]["class"] != 0:
                raise ColdTerminalError("initial Claim is not Statement-owned")
        else:
            reduction_ref, output_ordinal = source["reduction"], source["output"]
            if not 0 <= reduction_ref < len(core["reductions"]):
                raise ColdTerminalError("Claim source Reduction is absent")
            reduction = core["reductions"][reduction_ref]
            if not 0 <= output_ordinal < len(reduction["output_contracts"]):
                raise ColdTerminalError("Claim source output is absent")
            if claim["contract"] != reduction["output_contracts"][output_ordinal]:
                raise ColdTerminalError("Claim and Reduction output contracts differ")
            coordinate = reduction_ref, output_ordinal
            if coordinate in output_claims:
                raise ColdTerminalError("two Claims share one Reduction output")
            output_claims[coordinate] = claim_ref

    expected_outputs: set[tuple[int, int]] = set()
    claim_uses: dict[int, list[tuple[str, int, int, int]]] = {
        index: [] for index in range(len(core["claims"]))
    }
    for reduction_ref, reduction in enumerate(core["reductions"]):
        module_refs.append(reduction["contract"])
        module_refs.extend(reduction["output_contracts"])
        _owner, kind, _ordinal = _module_ref_info(reduction["contract"])
        if kind != "pir.reduction-contract" or reduction["scope"] != 0:
            raise ColdTerminalError("Reduction contract or scope differs")
        if (
            reduction["side_inputs"]
            or reduction["required_challenges"]
            or reduction["required_publications"]
        ):
            raise ColdTerminalError("Reduction surface is outside B5B2")
        occurrence_ref = reduction_positions[reduction_ref]
        for ordinal, claim_ref in enumerate(reduction["input_claims"]):
            if not 0 <= claim_ref < len(core["claims"]):
                raise ColdTerminalError("Reduction input Claim is absent")
            claim_uses[claim_ref].append(
                ("reduction", occurrence_ref, reduction_ref, ordinal)
            )
        for output_ordinal, contract in enumerate(reduction["output_contracts"]):
            _owner, kind, _ordinal = _module_ref_info(contract)
            if kind != "pir.claim-contract":
                raise ColdTerminalError("Reduction output has another contract kind")
            expected_outputs.add((reduction_ref, output_ordinal))
    if set(output_claims) != expected_outputs:
        raise ColdTerminalError("Reduction outputs and Claims are not a bijection")

    owners = {_module_ref_info(item)[0] for item in module_refs}
    if core["used_modules"] != tuple(sorted(owners)):
        raise ColdTerminalError("used_modules differs from exact declaration owners")

    for terminal_ref, terminal in enumerate(core["terminals"]):
        occurrence_ref = terminal_positions[terminal_ref]
        if any(
            not 0 <= check_ref < len(core["checks"])
            or check_positions[check_ref] >= occurrence_ref
            for check_ref in terminal["checks"]
        ):
            raise ColdTerminalError("Terminal Check is absent or not prior")
        if any(
            not 0 <= reduction_ref < len(core["reductions"])
            or reduction_positions[reduction_ref] >= occurrence_ref
            for reduction_ref in terminal["reductions"]
        ):
            raise ColdTerminalError("Terminal Reduction is absent or not prior")
        for ordinal, claim_ref in enumerate(terminal["claims"]):
            if not 0 <= claim_ref < len(core["claims"]):
                raise ColdTerminalError("Terminal Claim is absent")
            claim_uses[claim_ref].append(
                ("terminal", occurrence_ref, terminal_ref, ordinal)
            )

    facts = {
        "check_positions": check_positions,
        "reduction_positions": reduction_positions,
        "terminal_positions": terminal_positions,
        "output_claims": output_claims,
        "claim_uses": {key: tuple(value) for key, value in claim_uses.items()},
    }
    facts["execution"] = _simulate(core, algorithms, facts)
    return outputs, facts, algorithms


def _pc_value(node: tuple[int, ...]) -> dict[str, Any]:
    tag, *arguments = node
    if tag in (8, 12, 13):
        if len(arguments) != 2:
            raise ColdTerminalError("PCNode output arity differs")
        return cold._v(
            tag,
            {
                0: cold._ordinal("occurrence-ref-body-v0", arguments[0]),
                1: arguments[1],
            },
        )
    compiler = {
        0: "public-input-ref-body-v0",
        4: "scope-ref-body-v0",
        5: "binding-ref-body-v0",
        6: "occurrence-ref-body-v0",
        7: "occurrence-ref-body-v0",
        9: "claim-ref-body-v0",
        10: "reduction-ref-body-v0",
        11: "terminal-ref-body-v0",
    }.get(tag)
    if compiler is None or len(arguments) != 1:
        raise ColdTerminalError("PCNode belongs to another slice")
    return cold._v(tag, cold._ordinal(compiler, arguments[0]))


def _pc_key(node: tuple[int, ...]) -> bytes:
    if not _PC_NODE_SCHEMA:
        raise ColdTerminalError("candidate schema is not configured")
    return codec.encode_value(_PC_NODE_SCHEMA, _pc_value(node))


def _edge_value(pair: tuple[tuple[int, ...], tuple[int, ...]]) -> dict[int, Any]:
    return {0: _pc_value(pair[0]), 1: _pc_value(pair[1])}


def _edge_key(pair: tuple[tuple[int, ...], tuple[int, ...]]) -> bytes:
    if not _PC_EDGE_SCHEMA:
        raise ColdTerminalError("candidate schema is not configured")
    return codec.encode_value(_PC_EDGE_SCHEMA, _edge_value(pair))


def _graph(
    core: dict[str, Any],
    outputs: tuple[tuple[object, ...], ...],
    facts: dict[str, Any],
) -> tuple[dict[int, Any], dict[str, Any]]:
    predecessors: dict[tuple[int, ...], set[tuple[int, ...]]] = {}
    successors: dict[tuple[int, ...], set[tuple[int, ...]]] = {}

    def node(value: tuple[int, ...]) -> tuple[int, ...]:
        predecessors.setdefault(value, set())
        successors.setdefault(value, set())
        return value

    def connect(source: tuple[int, ...], target: tuple[int, ...]) -> None:
        source, target = node(source), node(target)
        predecessors[target].add(source)
        successors[source].add(target)

    for input_ref in range(len(core["public_inputs"])):
        node((0, input_ref))
    node((4, 0))
    for binding_ref, binding in enumerate(core["bindings"]):
        connect((4, binding["scope"]), (5, binding_ref))
        connect(_producer(binding["value"]), (5, binding_ref))

    prior_terminals: list[tuple[int, ...]] = []
    for occurrence_ref, occurrence in enumerate(core["occurrences"]):
        activity = node((6, occurrence_ref))
        effect_node = node((7, occurrence_ref))
        connect((4, occurrence["scope"]), activity)
        for reference in occurrence["guard"]["inputs"]:
            connect(_producer(reference), activity)
        for terminal_node in prior_terminals:
            connect(terminal_node, activity)
        connect(activity, effect_node)
        effect = occurrence["effect"]
        if effect["tag"] == 3:
            for reference in core["checks"][effect["check"]]["inputs"]:
                connect(_producer(reference), effect_node)
        elif effect["tag"] == 4:
            reduction = core["reductions"][effect["reduction"]]
            for claim_ref in reduction["input_claims"]:
                connect((9, claim_ref), effect_node)
            connect(effect_node, (10, effect["reduction"]))
        elif effect["tag"] == 5:
            terminal = core["terminals"][effect["terminal"]]
            for reference in terminal["outputs"]:
                connect(_producer(reference), effect_node)
            for check_ref in terminal["checks"]:
                connect((8, facts["check_positions"][check_ref], 0), effect_node)
            for reduction_ref in terminal["reductions"]:
                connect((10, reduction_ref), effect_node)
            for claim_ref in terminal["claims"]:
                connect((9, claim_ref), effect_node)
            terminal_node = node((11, effect["terminal"]))
            connect(effect_node, terminal_node)
            prior_terminals.append(terminal_node)
        for output_ordinal in range(len(outputs[occurrence_ref])):
            connect(effect_node, (8, occurrence_ref, output_ordinal))

    for claim_ref, claim in enumerate(core["claims"]):
        source = claim["source"]
        if source["tag"] == 0:
            connect((5, source["binding"]), (9, claim_ref))
        else:
            connect((10, source["reduction"]), (9, claim_ref))
    for reduction_ref, occurrence_ref in facts["reduction_positions"].items():
        connect((7, occurrence_ref), (10, reduction_ref))

    remaining = {key: len(value) for key, value in predecessors.items()}
    heap = [(_pc_key(key), key) for key, count in remaining.items() if count == 0]
    heapq.heapify(heap)
    topological: list[tuple[int, ...]] = []
    while heap:
        _key, current = heapq.heappop(heap)
        topological.append(current)
        for child in successors[current]:
            remaining[child] -= 1
            if remaining[child] == 0:
                heapq.heappush(heap, (_pc_key(child), child))
    if len(topological) != len(predecessors):
        raise ColdTerminalError("expanded-Terminal PCGraph is cyclic")
    classes: dict[tuple[int, ...], int] = {}
    for current in topological:
        classes[current] = max(
            (classes[item] for item in predecessors[current]), default=0
        )

    activity_sinks = {(6, index) for index in range(len(core["occurrences"]))}
    check_sinks = {(7, item) for item in facts["check_positions"].values()}
    reduction_sinks = {(10, index) for index in range(len(core["reductions"]))}
    terminal_sinks = {(11, index) for index in range(len(core["terminals"]))}
    sinks = activity_sinks | check_sinks | reduction_sinks | terminal_sinks
    acceptance = (
        check_sinks
        | reduction_sinks
        | {
            (11, terminal_ref)
            for terminal_ref, terminal in enumerate(core["terminals"])
            if terminal["verdict"] == 0
        }
    )
    ordered_nodes = sorted(predecessors, key=_pc_key)
    ordered_edges = sorted(
        {
            (source, target)
            for target, sources in predecessors.items()
            for source in sources
        },
        key=_edge_key,
    )
    graph = {
        0: [_pc_value(item) for item in ordered_nodes],
        1: [_edge_value(item) for item in ordered_edges],
        2: [_pc_value(item) for item in topological],
        3: [{0: _pc_value(item), 1: cold._v(classes[item])} for item in ordered_nodes],
        4: [_pc_value(item) for item in sorted(sinks, key=_pc_key)],
        5: [_pc_value(item) for item in sorted(acceptance, key=_pc_key)],
        6: [],
    }
    return graph, {
        "nodes": len(predecessors),
        "edges": len(ordered_edges),
        "eligible": all(classes[item] in (0, 1) for item in sinks),
        "check_sinks": len(check_sinks),
        "reduction_sinks": len(reduction_sinks),
        "terminal_sinks": len(terminal_sinks),
    }


def _effect_value(effect: dict[str, Any]) -> dict[str, Any]:
    compiler = {
        3: "check-ref-body-v0",
        4: "reduction-ref-body-v0",
        5: "terminal-ref-body-v0",
    }
    key = {3: "check", 4: "reduction", 5: "terminal"}
    if effect["tag"] not in compiler:
        raise ColdTerminalError("effect belongs to another slice")
    return cold._v(
        effect["tag"],
        cold._ordinal(compiler[effect["tag"]], effect[key[effect["tag"]]]),
    )


def _claim_source_value(source: dict[str, Any]) -> dict[str, Any]:
    if source["tag"] == 0:
        return cold._v(0, cold._ordinal("binding-ref-body-v0", source["binding"]))
    return cold._v(
        1,
        {
            0: cold._ordinal("reduction-ref-body-v0", source["reduction"]),
            1: source["output"],
        },
    )


def _claim_creation_value(
    facts: dict[str, Any], source: dict[str, Any]
) -> dict[str, Any]:
    if source["tag"] == 0:
        return cold._v(
            0,
            {
                0: cold._ordinal("binding-ref-body-v0", source["binding"]),
                1: cold._v(0),
            },
        )
    return cold._v(
        1,
        {
            0: cold._ordinal(
                "occurrence-ref-body-v0",
                facts["reduction_positions"][source["reduction"]],
            ),
            1: cold._ordinal("reduction-ref-body-v0", source["reduction"]),
            2: source["output"],
        },
    )


def project(
    core_profiled_body: bytes,
    core_reference: bytes,
    protocol_profiled_body: bytes,
    protocol_reference: bytes,
    algorithm_preimages: Mapping[bytes, bytes],
    evaluation_contract_reference: bytes,
) -> tuple[dict[str, Any], dict[str, Any]]:
    """Authenticate exact bytes, exhaust the finite semantics, and project."""

    if not PROFILE_DIGEST or not VIEW_SCHEMAS:
        raise ColdTerminalError("candidate profile and schema are not configured")
    try:
        core_profile, core_domain = cold._authenticated_subject(
            core_profiled_body,
            core_reference,
            "pir.interactive-core",
            "cold expanded-Terminal Core",
        )
        protocol_profile, protocol_domain = cold._authenticated_subject(
            protocol_profiled_body,
            protocol_reference,
            "pir.protocol",
            "cold expanded-Terminal Protocol",
        )
    except Exception as error:
        raise ColdTerminalError(str(error)) from error
    if core_profile != protocol_profile:
        raise ColdTerminalError("Core and Protocol profiles differ")
    protocol_core, interpretation = _record(
        protocol_domain, (0, 1), "cold Protocol domain"
    )
    if _bytes(protocol_core, "Protocol Core") != core_reference:
        raise ColdTerminalError("Fresh Protocol names another Core")
    interpretation_tag, interpretation_payload = _variant(
        interpretation, {0}, "Fresh interpretation"
    )
    if interpretation_tag != 0:  # pragma: no cover - parser closes this
        raise ColdTerminalError("Protocol is not Fresh")
    _unit(interpretation_payload, "Fresh interpretation payload")

    core = decode_core(k1.encode_datum(core_domain))
    outputs, facts, _algorithms = _validate(
        core, algorithm_preimages, evaluation_contract_reference
    )
    graph, graph_evidence = _graph(core, outputs, facts)
    core_atom = cold._identifier("core-id-body-v0", core_reference)
    protocol_atom = cold._identifier("protocol-id-body-v0", protocol_reference)

    public_binding = {
        0: core_atom,
        1: [
            {
                0: cold._ordinal("scope-ref-body-v0", 0),
                1: cold._v(0),
                2: cold._v(0),
                3: [cold._ordinal("scope-ref-body-v0", 0)],
            }
        ],
        2: [
            {
                0: cold._ordinal("binding-ref-body-v0", binding_ref),
                1: cold._ordinal("scope-ref-body-v0", binding["scope"]),
                2: cold._v(binding["class"]),
                3: cold._value_ref(binding["value"]),
                4: cold._value_type(_type_of(core, outputs, binding["value"])),
            }
            for binding_ref, binding in enumerate(core["bindings"])
        ],
    }
    strategy = {
        0: core_atom,
        1: [],
        2: cold._law("core-admission-v0"),
        3: [],
        4: [],
    }
    public_coin = {
        0: core_atom,
        1: graph,
        2: graph_evidence["eligible"],
        3: [],
        4: [],
    }

    value_rows: list[dict[int, Any]] = [
        {
            0: cold._value_ref((0, input_ref, 0)),
            1: cold._value_type(declaration["type"]),
            2: [],
        }
        for input_ref, declaration in enumerate(core["public_inputs"])
    ]
    occurrence_rows: list[dict[int, Any]] = []
    for occurrence_ref, occurrence in enumerate(core["occurrences"]):
        occurrence_rows.append(
            {
                0: cold._ordinal("occurrence-ref-body-v0", occurrence_ref),
                1: [cold._ordinal("scope-ref-body-v0", 0)],
                2: cold._guard(occurrence["guard"]["body"]),
                3: _effect_value(occurrence["effect"]),
                4: [cold._value_type(item) for item in outputs[occurrence_ref]],
            }
        )
        for output_ordinal, output_type in enumerate(outputs[occurrence_ref]):
            predecessors = (
                core["checks"][occurrence["effect"]["check"]]["inputs"]
                if occurrence["effect"]["tag"] == 3
                else ()
            )
            value_rows.append(
                {
                    0: cold._value_ref((4, occurrence_ref, output_ordinal)),
                    1: cold._value_type(output_type),
                    2: [cold._value_ref(item) for item in predecessors],
                }
            )
    check_rows = [
        {
            0: cold._ordinal("check-ref-body-v0", check_ref),
            1: cold._identifier("algorithm-ref-body-v0", check["algorithm"]),
            2: cold._identifier("evaluation-contract-id-body-v0", check["contract"]),
            3: [cold._value_ref(item) for item in check["inputs"]],
            4: cold._ordinal(
                "occurrence-ref-body-v0", facts["check_positions"][check_ref]
            ),
        }
        for check_ref, check in enumerate(core["checks"])
    ]
    terminal_rows = [
        {
            0: cold._ordinal("terminal-ref-body-v0", terminal_ref),
            1: cold._v(terminal["verdict"]),
            2: [cold._value_ref(item) for item in terminal["outputs"]],
            3: [
                cold._ordinal("check-ref-body-v0", item) for item in terminal["checks"]
            ],
            4: [
                cold._ordinal("reduction-ref-body-v0", item)
                for item in terminal["reductions"]
            ],
            5: [
                cold._ordinal("claim-ref-body-v0", item) for item in terminal["claims"]
            ],
            6: cold._ordinal(
                "occurrence-ref-body-v0", facts["terminal_positions"][terminal_ref]
            ),
        }
        for terminal_ref, terminal in enumerate(core["terminals"])
    ]
    effect_view = {
        0: core_atom,
        1: occurrence_rows,
        2: value_rows,
        3: [],
        4: [],
        5: check_rows,
        6: terminal_rows,
        7: [],
    }

    claim_rows: list[dict[int, Any]] = []
    for claim_ref, claim in enumerate(core["claims"]):
        uses: list[dict[str, Any]] = []
        for kind, occurrence_ref, owner_ref, ordinal in sorted(
            facts["claim_uses"][claim_ref],
            key=lambda item: (item[1], item[0], item[3]),
        ):
            uses.append(
                cold._v(
                    0 if kind == "reduction" else 1,
                    {
                        0: cold._ordinal("occurrence-ref-body-v0", occurrence_ref),
                        1: cold._ordinal(
                            "reduction-ref-body-v0"
                            if kind == "reduction"
                            else "terminal-ref-body-v0",
                            owner_ref,
                        ),
                        2: ordinal,
                    },
                )
            )
        claim_rows.append(
            {
                0: cold._ordinal("claim-ref-body-v0", claim_ref),
                1: cold._module_ref(claim["contract"]),
                2: cold._ordinal("scope-ref-body-v0", claim["scope"]),
                3: cold._v(claim["usage"]),
                4: _claim_source_value(claim["source"]),
                5: _claim_creation_value(facts, claim["source"]),
                6: uses,
            }
        )
    reduction_rows = [
        {
            0: cold._ordinal("reduction-ref-body-v0", reduction_ref),
            1: cold._module_ref(reduction["contract"]),
            2: cold._ordinal("scope-ref-body-v0", reduction["scope"]),
            3: cold._ordinal(
                "occurrence-ref-body-v0",
                facts["reduction_positions"][reduction_ref],
            ),
            4: [
                cold._ordinal("claim-ref-body-v0", item)
                for item in reduction["input_claims"]
            ],
            5: [],
            6: [],
            7: [],
            8: [cold._module_ref(item) for item in reduction["output_contracts"]],
        }
        for reduction_ref, reduction in enumerate(core["reductions"])
    ]
    disposition_rows = [
        {
            0: cold._ordinal(
                "occurrence-ref-body-v0", facts["terminal_positions"][terminal_ref]
            ),
            1: cold._ordinal("terminal-ref-body-v0", terminal_ref),
            2: cold._ordinal("claim-ref-body-v0", claim_ref),
            3: cold._v(0 if terminal["verdict"] == 0 else 1),
        }
        for terminal_ref, terminal in enumerate(core["terminals"])
        for claim_ref in terminal["claims"]
    ]
    requirement_rows = [
        {
            0: cold._ordinal(
                "occurrence-ref-body-v0", facts["terminal_positions"][terminal_ref]
            ),
            1: cold._ordinal("terminal-ref-body-v0", terminal_ref),
            2: [
                cold._ordinal("reduction-ref-body-v0", item)
                for item in terminal["reductions"]
            ],
        }
        for terminal_ref, terminal in enumerate(core["terminals"])
    ]
    claim_reduction = {
        0: core_atom,
        1: claim_rows,
        2: reduction_rows,
        3: disposition_rows,
        4: requirement_rows,
    }

    runtime = {
        0: [
            {
                0: cold._ordinal("occurrence-ref-body-v0", occurrence_ref),
                1: [cold._value_type(item) for item in output_types],
            }
            for occurrence_ref, output_types in enumerate(outputs)
        ],
        1: [],
        2: [],
        3: [
            {
                0: cold._ordinal("terminal-ref-body-v0", terminal_ref),
                1: cold._ordinal(
                    "occurrence-ref-body-v0",
                    facts["terminal_positions"][terminal_ref],
                ),
                2: cold._v(terminal["verdict"]),
                3: [
                    cold._value_type(_type_of(core, outputs, item))
                    for item in terminal["outputs"]
                ],
            }
            for terminal_ref, terminal in enumerate(core["terminals"])
        ],
    }
    execution = {
        0: protocol_atom,
        1: core_atom,
        2: cold._v(0),
        3: cold._law("core-admission-v0"),
        4: [],
        5: cold._law("execution-and-replay-v0"),
        6: runtime,
        7: cold._v(0),
        8: cold._law("execution-and-replay-v0"),
        9: cold._law("run-view-issuance-v0"),
    }
    views = {
        "PublicBindingView": public_binding,
        "StrategyDecisionView": strategy,
        "PublicCoinView": public_coin,
        "EffectView": effect_view,
        "ClaimReductionView": claim_reduction,
        "ExecutionView": execution,
    }
    return views, {
        "occurrences": len(core["occurrences"]),
        "checks": len(core["checks"]),
        "claims": len(core["claims"]),
        "reductions": len(core["reductions"]),
        "terminals": len(core["terminals"]),
        "claim_uses": facts["claim_uses"],
        "terminal_execution": facts["execution"],
        "pc_graph": graph_evidence,
    }


def encode_views(views: dict[str, Any]) -> dict[str, bytes]:
    if not SCHEMA_SOURCE or tuple(views) != tuple(SCHEMA_SOURCE["view_order"]):
        raise ColdTerminalError("cold view table is incomplete or reordered")
    return {
        name: codec.encode_value(VIEW_SCHEMAS[name], value)
        for name, value in views.items()
    }
