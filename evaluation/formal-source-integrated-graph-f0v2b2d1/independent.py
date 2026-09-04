"""Independent canonical-byte PublicCoin projector for F0-V2B2D1.

The module deliberately does not import the typed D1 owner model.  It reuses
only the already-checked B5B2 grammar compiler and cold K1 datum primitives,
then parses the complete integrated carrier and derives its graph from bytes.
"""

from __future__ import annotations

import hashlib
import heapq
import importlib.util
from pathlib import Path
import sys
from types import ModuleType
from typing import Any, Mapping


ROOT = Path(__file__).resolve().parents[2]
B5_COLD = (
    ROOT
    / "evaluation"
    / "formal-source-terminal-owner-projections-f0v2b2c1b5b2"
    / "independent.py"
)

MODULE_MAGIC = "f0v2b2d1.module-effect.v0"
SUPPORTED_DOMAIN_SHA256 = frozenset(
    {
        "6fd764871722c6ed1ddea5c3cc2c706032ad8691f245dab960e2aec06f5d63c0",
        "2458e755d983f7b57065d63fa8638749aa9edab1884a61ecbd685b0905cb06c1",
        "342970628ff1083d074c07d6d3ebec4f301b1d76c0ecead185d18a85f8290196",
        "f5f4d31b67f0ff801c779e080c8d8638c1f54ab98d74c0ed63addc4b6454ab8e",
        "c00bd1c8f7877ab60b72316d248f6223dc10ed43835235ec7c22f542bdfd9c7a",
    }
)
EXPECTED_CENSUS = (4, 1, 2, 3, 2, 5, 3, 3, 1, 3, 2, 3, 23)


class ColdIntegratedError(ValueError):
    """Fail-closed result from the independent D1 path."""


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


schema = _load("_zkc_f0v2b2d1_cold_b5", B5_COLD)
b3cold = schema.prior
oraclecold = b3cold.prior
cold = schema.cold
k1 = cold.k1
codec = cold.codec

VIEW_SCHEMAS: dict[str, Any] = {}
VIEW_SCHEMA_STATS: dict[str, int] = {}
PROFILE_DIGEST = ""
PROFILE_BODY_SHA256 = ""
_PC_NODE_SCHEMA: dict[str, Any] = {}
_PC_EDGE_SCHEMA: dict[str, Any] = {}


def configure(profile_digest: str, profile_body_sha256: str) -> dict[str, Any]:
    """Compile exactly the predecessor B5B2 grammar for this cold path."""

    global PROFILE_DIGEST, PROFILE_BODY_SHA256
    global VIEW_SCHEMAS, VIEW_SCHEMA_STATS, _PC_NODE_SCHEMA, _PC_EDGE_SCHEMA

    evidence = schema.configure(profile_digest, profile_body_sha256)
    PROFILE_DIGEST = profile_digest
    PROFILE_BODY_SHA256 = profile_body_sha256
    VIEW_SCHEMAS = schema.VIEW_SCHEMAS
    VIEW_SCHEMA_STATS = schema.VIEW_SCHEMA_STATS
    graph_schema = schema._schema_field(VIEW_SCHEMAS["PublicCoinView"], 1)
    _PC_NODE_SCHEMA = schema._schema_field(graph_schema, 0)["element"]
    _PC_EDGE_SCHEMA = schema._schema_field(graph_schema, 1)["element"]
    return evidence


def _record(value: object, ordinals: tuple[int, ...], label: str) -> tuple[object, ...]:
    try:
        return cold._record(value, ordinals, label)
    except Exception as error:
        raise ColdIntegratedError(str(error)) from error


def _sequence(value: object, label: str) -> tuple[object, ...]:
    try:
        return cold._sequence(value, label)
    except Exception as error:
        raise ColdIntegratedError(str(error)) from error


def _variant(value: object, cases: set[int], label: str) -> tuple[int, object]:
    try:
        return cold._variant(value, cases, label)
    except Exception as error:
        raise ColdIntegratedError(str(error)) from error


def _nat(value: object, label: str) -> int:
    try:
        return cold._nat(value, label)
    except Exception as error:
        raise ColdIntegratedError(str(error)) from error


def _bytes(value: object, label: str) -> bytes:
    try:
        return cold._bytes(value, label)
    except Exception as error:
        raise ColdIntegratedError(str(error)) from error


def _unit(value: object, label: str) -> None:
    try:
        cold._unit(value, label)
    except Exception as error:
        raise ColdIntegratedError(str(error)) from error


def _symbol(value: object, label: str) -> str:
    if type(value) is not k1.Symbol:
        raise ColdIntegratedError(f"{label} is not a Symbol")
    return value.value


def _bool(value: object, label: str) -> bool:
    tag, payload = _variant(value, {0, 1}, label)
    _unit(payload, f"{label} payload")
    return bool(tag)


def _value_ref(value: object) -> tuple[int, int, int]:
    try:
        return cold._parse_value_ref(value)
    except Exception as error:
        raise ColdIntegratedError(str(error)) from error


def _guard(value: object) -> dict[str, Any]:
    try:
        return cold._parse_guard(value)
    except Exception as error:
        raise ColdIntegratedError(str(error)) from error


def _module_ref(value: object) -> dict[str, Any]:
    tag, payload = _variant(value, {1}, "module declaration reference")
    if tag != 1:  # pragma: no cover - parser set closes this
        raise ColdIntegratedError("module declaration reference differs")
    module, kind, ordinal = _record(payload, (0, 1, 2), "module declaration")
    return {
        "body": value,
        "module": _bytes(module, "module declaration owner"),
        "kind": _symbol(kind, "module declaration kind"),
        "ordinal": _nat(ordinal, "module declaration ordinal"),
    }


def _parse_effect(value: object) -> dict[str, Any]:
    tag, payload = _variant(value, set(range(8)), "Core effect")
    result: dict[str, Any] = {"tag": tag, "body": value}
    if tag == 0:
        channel, payload_type = _record(payload, (0, 1), "Prover message")
        return {**result, "channel": channel, "payload_type": payload_type}
    if tag == 1:
        channel, algorithm, contract, inputs, payload_type = _record(
            payload, (0, 1, 2, 3, 4), "Verifier message"
        )
        return {
            **result,
            "channel": channel,
            "algorithm": _bytes(algorithm, "Verifier-message algorithm"),
            "contract": _bytes(contract, "Verifier-message contract"),
            "inputs": tuple(
                _value_ref(item)
                for item in _sequence(inputs, "Verifier-message inputs")
            ),
            "payload_type": payload_type,
        }
    if tag == 2:
        return {**result, "challenge": _nat(payload, "Challenge backlink")}
    if tag == 3:
        return {**result, "check": _nat(payload, "Check backlink")}
    if tag == 4:
        return {**result, "reduction": _nat(payload, "Reduction backlink")}
    if tag == 5:
        return {**result, "terminal": _nat(payload, "Terminal backlink")}
    if tag == 6:
        try:
            return oraclecold._parse_effect(value)
        except Exception as error:
            raise ColdIntegratedError(str(error)) from error
    module, declaration, module_payload = _record(payload, (0, 1, 2), "module effect")
    (inputs,) = _record(module_payload, (0,), "module payload")
    return {
        **result,
        "module": _bytes(module, "module-effect owner"),
        "declaration": _module_ref(declaration),
        "inputs": tuple(
            _value_ref(item) for item in _sequence(inputs, "module payload inputs")
        ),
    }


def _parse_terminal(value: object) -> dict[str, Any]:
    try:
        return schema._parse_terminal(value)
    except Exception as error:
        raise ColdIntegratedError(str(error)) from error


def _decode_core(domain: object) -> dict[str, Any]:
    fields = _record(domain, tuple(range(14)), "InteractiveCore")
    tables = tuple(
        _sequence(value, f"InteractiveCore field {index}")
        for index, value in enumerate(fields)
    )
    census = tuple(len(tables[index]) for index in range(1, 14))
    if census != EXPECTED_CENSUS:
        raise ColdIntegratedError("integrated Core table census differs")

    def input_row(item: object, label: str) -> dict[str, Any]:
        (value_type,) = _record(item, (0,), label)
        return {"type": value_type}

    constants: list[dict[str, Any]] = []
    for item in tables[3]:
        value_type, datum = _record(item, (0, 1), "typed constant")
        constants.append({"type": value_type, "value": datum})
    derived: list[dict[str, Any]] = []
    for item in tables[4]:
        algorithm, contract, inputs, value_type = _record(
            item, (0, 1, 2, 3), "derived value"
        )
        derived.append(
            {
                "algorithm": _bytes(algorithm, "derived algorithm"),
                "contract": _bytes(contract, "derived contract"),
                "inputs": tuple(
                    _value_ref(value) for value in _sequence(inputs, "derived inputs")
                ),
                "type": value_type,
            }
        )
    scopes: list[dict[str, int | None]] = []
    for item in tables[5]:
        parent, opening = _record(item, (0, 1), "scope")
        parent_tag, parent_payload = _variant(parent, {0, 1}, "scope parent")
        opening_tag, opening_payload = _variant(opening, {0, 1}, "scope opening")
        if parent_tag == 0:
            _unit(parent_payload, "absent scope parent")
        if opening_tag == 0:
            _unit(opening_payload, "initial scope opening")
        scopes.append(
            {
                "parent": None
                if parent_tag == 0
                else _nat(parent_payload, "scope parent"),
                "opening": None
                if opening_tag == 0
                else _nat(opening_payload, "scope opening"),
            }
        )
    bindings: list[dict[str, Any]] = []
    for item in tables[6]:
        scope, binding_class, reference = _record(item, (0, 1, 2), "binding")
        class_tag, class_payload = _variant(binding_class, {0, 1, 2}, "binding class")
        _unit(class_payload, "binding-class payload")
        bindings.append(
            {
                "scope": _nat(scope, "binding scope"),
                "class": class_tag,
                "value": _value_ref(reference),
            }
        )
    occurrences: list[dict[str, Any]] = []
    for item in tables[13]:
        scope, guard, effect = _record(item, (0, 1, 2), "occurrence")
        occurrences.append(
            {
                "scope": _nat(scope, "occurrence scope"),
                "guard": _guard(guard),
                "effect": _parse_effect(effect),
            }
        )
    try:
        challenges = tuple(b3cold._parse_challenge(item) for item in tables[7])
        oracles = tuple(oraclecold._parse_oracle(item) for item in tables[8])
        checks = tuple(schema._parse_check(item) for item in tables[9])
        claims = tuple(b3cold._parse_claim(item) for item in tables[10])
        reductions = tuple(b3cold._parse_reduction(item) for item in tables[11])
    except Exception as error:
        raise ColdIntegratedError(str(error)) from error
    return {
        "used_modules": tuple(_bytes(item, "used module") for item in tables[0]),
        "public_inputs": tuple(input_row(item, "public input") for item in tables[1]),
        "private_inputs": tuple(
            input_row(item, "verifier-private input") for item in tables[2]
        ),
        "constants": tuple(constants),
        "derived": tuple(derived),
        "scopes": tuple(scopes),
        "bindings": tuple(bindings),
        "challenges": challenges,
        "oracles": oracles,
        "checks": checks,
        "claims": claims,
        "reductions": reductions,
        "terminals": tuple(_parse_terminal(item) for item in tables[12]),
        "occurrences": tuple(occurrences),
    }


def _dependency(value: object) -> dict[str, int | None]:
    tag, payload = _variant(value, {0, 1, 2, 3}, "module dependency")
    if tag in (0, 1):
        _unit(payload, "node-local dependency payload")
        return {"tag": tag, "ordinal": None}
    return {"tag": tag, "ordinal": _nat(payload, "module dependency ordinal")}


def _module_output(value: object) -> dict[str, Any]:
    value_type, visibility, transfer, dependencies, sink = _record(
        value, (0, 1, 2, 3, 4), "module output"
    )
    visibility_tag, visibility_payload = _variant(
        visibility, {0, 1, 2, 3}, "module visibility"
    )
    _unit(visibility_payload, "module visibility payload")
    transfer_tag, transfer_payload = _variant(
        transfer, {0, 1, 2}, "module output transfer"
    )
    algorithm: bytes | None = None
    contract: bytes | None = None
    if transfer_tag == 0:
        algorithm_value, contract_value = _record(
            transfer_payload, (0, 1), "module reconstruction"
        )
        algorithm = _bytes(algorithm_value, "reconstruction algorithm")
        contract = _bytes(contract_value, "reconstruction contract")
    else:
        _unit(transfer_payload, "nondeterministic transfer payload")
    return {
        "type": value_type,
        "visibility": visibility_tag,
        "transfer": transfer_tag,
        "dependencies": tuple(
            _dependency(item)
            for item in _sequence(dependencies, "module output dependencies")
        ),
        "algorithm": algorithm,
        "contract": contract,
        "acceptance_relevant": _bool(sink, "module output sink"),
    }


def _module_control(value: object) -> dict[str, Any]:
    dependencies, sink = _record(value, (0, 1), "module control")
    return {
        "dependencies": tuple(
            _dependency(item)
            for item in _sequence(dependencies, "module control dependencies")
        ),
        "acceptance_relevant": _bool(sink, "module control sink"),
    }


def _module_semantics(value: object) -> dict[str, Any]:
    fields = _record(value, tuple(range(11)), "module declaration")
    if _symbol(fields[0], "module declaration magic") != MODULE_MAGIC:
        raise ColdIntegratedError("module declaration selects another schema")
    decision, decision_payload = _variant(fields[2], {0, 1, 2}, "module decision class")
    if decision == 0:
        _unit(decision_payload, "NoProverDecision payload")
        move_type = None
    else:
        move_type = decision_payload
    influence_tag, influence_payload = _variant(
        fields[6], {0, 1}, "module influence output"
    )
    if influence_tag == 0:
        _unit(influence_payload, "absent influence output")
    result = {
        "name": _symbol(fields[1], "module declaration name"),
        "decision": decision,
        "move_type": move_type,
        "payload_types": _sequence(fields[3], "module payload ABI"),
        "outputs": tuple(
            _module_output(item) for item in _sequence(fields[4], "module outputs")
        ),
        "controls": tuple(
            _module_control(item) for item in _sequence(fields[5], "module controls")
        ),
        "influence": None
        if influence_tag == 0
        else _nat(influence_payload, "module influence output"),
        "guard_behavior": _symbol(fields[7], "module guard behavior"),
        "replay_rule": _symbol(fields[8], "module replay rule"),
        "terminal_interaction": _symbol(fields[9], "module terminal interaction"),
        "work_bound": _nat(fields[10], "module work bound"),
    }
    _validate_module_semantics(result)
    return result


def _validate_module_semantics(value: dict[str, Any]) -> None:
    names = (
        "integrated-deterministic-public",
        "integrated-prover-private",
        "integrated-prover-publication",
    )
    try:
        ordinal = names.index(value["name"])
    except ValueError as error:
        raise ColdIntegratedError("module declaration name is unsupported") from error
    output = value["outputs"]
    controls = value["controls"]
    if (
        value["decision"] != ordinal
        or len(value["payload_types"]) != 1
        or len(output) != 1
        or len(controls) != 1
        or value["guard_behavior"] != "inherit-exact-occurrence-guard"
        or value["replay_rule"] != "exact-module-event-replay"
        or value["terminal_interaction"] != "nonterminating"
        or value["work_bound"] != 8
        or output[0]["type"] != value["payload_types"][0]
        or output[0]["visibility"] != (1 if ordinal == 1 else 3)
        or output[0]["transfer"] != (0, 2, 1)[ordinal]
        or tuple((item["tag"], item["ordinal"]) for item in output[0]["dependencies"])
        != ((0, None), (1, None), (2, 0))
        or tuple((item["tag"], item["ordinal"]) for item in controls[0]["dependencies"])
        != ((0, None), (1, None), (3, 0))
        or output[0]["acceptance_relevant"] != (ordinal != 1)
        or (ordinal != 1 and not controls[0]["acceptance_relevant"])
        or value["influence"] != (0 if ordinal == 2 else None)
        or (value["move_type"] is None) != (ordinal == 0)
        or (
            value["move_type"] is not None
            and value["move_type"] != value["payload_types"][0]
        )
    ):
        raise ColdIntegratedError("module declaration differs from exact D1 support")
    if ordinal == 0:
        if output[0]["algorithm"] is None or output[0]["contract"] is None:
            raise ColdIntegratedError(
                "deterministic module output lacks reconstruction"
            )
    elif output[0]["algorithm"] is not None or output[0]["contract"] is not None:
        raise ColdIntegratedError("nondeterministic module output has reconstruction")


def _module_source(reference: bytes, body: bytes) -> dict[str, Any]:
    if type(reference) is not bytes or type(body) is not bytes or not body:
        raise ColdIntegratedError("module source is not exact nonempty bytes")
    try:
        identifier = k1.decode_content_reference(reference)
        decoded = k1.decode_datum(body)
        if k1.encode_datum(decoded) != body:
            raise ColdIntegratedError("module source is not canonical")
        expected = k1.content_id(
            k1.SEMANTIC_MODULE_KIND,
            body,
            semantic_regime=k1.SEMANTIC_REGIME_ID,
        )
    except ColdIntegratedError:
        raise
    except Exception as error:
        raise ColdIntegratedError(f"module source does not decode: {error}") from error
    if (
        identifier.subject_kind != k1.SEMANTIC_MODULE_KIND
        or identifier.semantic_regime != k1.SEMANTIC_REGIME_ID
        or expected.internal_reference() != reference
    ):
        raise ColdIntegratedError("module source and reference do not authenticate")
    imports, declarations, payload = _record(decoded, (0, 1, 2), "semantic module")
    if _sequence(imports, "module imports"):
        raise ColdIntegratedError("supported module imports another module")
    _unit(payload, "module domain payload")
    core_effects: tuple[dict[str, Any], ...] = ()
    for catalog in _sequence(declarations, "module declaration catalogs"):
        kind, local = _record(catalog, (0, 1), "module catalog")
        if _symbol(kind, "module catalog kind") == "pir.core-effect":
            if core_effects:
                raise ColdIntegratedError("duplicate pir.core-effect catalog")
            core_effects = tuple(
                _module_semantics(item)
                for item in _sequence(local, "module effect declarations")
            )
    if core_effects and len(core_effects) != 3:
        raise ColdIntegratedError("module effect declaration closure differs")
    return {"reference": reference, "semantics": core_effects}


def _source_closure(
    used_modules: tuple[bytes, ...], sources: tuple[tuple[bytes, bytes], ...]
) -> dict[bytes, dict[str, Any]]:
    if type(sources) is not tuple or any(
        type(item) is not tuple or len(item) != 2 for item in sources
    ):
        raise ColdIntegratedError("module source closure has another carrier")
    references = tuple(item[0] for item in sources)
    if references != tuple(sorted(set(references))) or used_modules != references:
        raise ColdIntegratedError("module source closure is not exact")
    result = {reference: _module_source(reference, body) for reference, body in sources}
    if sum(bool(item["semantics"]) for item in result.values()) != 1:
        raise ColdIntegratedError("exactly one module must own integrated effects")
    return result


def _module_occurrences(
    core: dict[str, Any], sources: Mapping[bytes, dict[str, Any]]
) -> dict[int, dict[str, Any]]:
    result: dict[int, dict[str, Any]] = {}
    for occurrence_ref, occurrence in enumerate(core["occurrences"]):
        effect = occurrence["effect"]
        if effect["tag"] != 7:
            continue
        declaration = effect["declaration"]
        if (
            effect["module"] != declaration["module"]
            or declaration["kind"] != "pir.core-effect"
        ):
            raise ColdIntegratedError("module effect coordinate differs")
        try:
            semantics = sources[effect["module"]]["semantics"][declaration["ordinal"]]
        except (KeyError, IndexError) as error:
            raise ColdIntegratedError("module effect declaration is absent") from error
        if len(effect["inputs"]) != len(semantics["payload_types"]):
            raise ColdIntegratedError("module payload ABI differs")
        result[occurrence_ref] = semantics
    if tuple(result) != (2, 3, 4):
        raise ColdIntegratedError("module effect occurrence closure differs")
    return result


def _algorithm_closure(
    core: dict[str, Any],
    module_occurrences: Mapping[int, dict[str, Any]],
    preimages: tuple[tuple[bytes, bytes], ...],
    contract_reference: bytes,
) -> None:
    required_algorithms: set[bytes] = set()
    required_contracts: set[bytes] = set()
    for item in core["derived"]:
        required_algorithms.add(item["algorithm"])
        required_contracts.add(item["contract"])
    for item in core["checks"]:
        required_algorithms.add(item["algorithm"])
        required_contracts.add(item["contract"])
    for occurrence in core["occurrences"]:
        guard = occurrence["guard"]
        if guard["tag"] == 1:
            required_algorithms.add(guard["algorithm"])
            required_contracts.add(guard["contract"])
        effect = occurrence["effect"]
        if effect["tag"] == 1:
            required_algorithms.add(effect["algorithm"])
            required_contracts.add(effect["contract"])
    for declaration in core["oracles"]:
        mode = declaration["mode"]
        if mode["tag"] == 1:
            required_algorithms.add(mode["algorithm"])
            required_contracts.add(mode["evaluation"])
    for semantics in module_occurrences.values():
        for output in semantics["outputs"]:
            if output["algorithm"] is not None:
                required_algorithms.add(output["algorithm"])
                required_contracts.add(output["contract"])
    if type(preimages) is not tuple or any(
        type(item) is not tuple or len(item) != 2 for item in preimages
    ):
        raise ColdIntegratedError("algorithm preimage closure has another carrier")
    references = tuple(item[0] for item in preimages)
    if (
        references != tuple(sorted(set(references)))
        or set(references) != required_algorithms
    ):
        raise ColdIntegratedError("algorithm preimage closure is not exact")
    for reference, raw in preimages:
        if type(reference) is not bytes or type(raw) is not bytes or not raw:
            raise ColdIntegratedError("algorithm preimage is not exact bytes")
        try:
            datum = k1.decode_datum(raw)
            canonical = k1.encode_datum(datum)
            reconstructed = schema._algorithm_reference(raw)
        except Exception as error:
            raise ColdIntegratedError(
                f"algorithm preimage does not decode: {error}"
            ) from error
        if canonical != raw or reconstructed != reference:
            raise ColdIntegratedError("algorithm preimage does not authenticate")
    if type(contract_reference) is not bytes or required_contracts != {
        contract_reference
    }:
        raise ColdIntegratedError("evaluation-contract closure differs")


def _producer(reference: tuple[int, int, int]) -> tuple[int, ...]:
    tag, first, second = reference
    if tag in (0, 1, 2, 3):
        return tag, first
    if tag == 4:
        return 8, first, second
    raise ColdIntegratedError("ValueRef has another producer case")


def _pc_value(node: tuple[int, ...]) -> dict[str, Any]:
    tag, *arguments = node
    if tag in (8, 12, 13):
        if len(arguments) != 2:
            raise ColdIntegratedError("indexed PCNode arity differs")
        return cold._v(
            tag,
            {
                0: cold._ordinal("occurrence-ref-body-v0", arguments[0]),
                1: arguments[1],
            },
        )
    compiler = {
        0: "public-input-ref-body-v0",
        1: "verifier-private-input-ref-body-v0",
        2: "constant-ref-body-v0",
        3: "derived-value-ref-body-v0",
        4: "scope-ref-body-v0",
        5: "binding-ref-body-v0",
        6: "occurrence-ref-body-v0",
        7: "occurrence-ref-body-v0",
        9: "claim-ref-body-v0",
        10: "reduction-ref-body-v0",
        11: "terminal-ref-body-v0",
    }.get(tag)
    if compiler is None or len(arguments) != 1:
        raise ColdIntegratedError("PCNode tag or arity differs")
    return cold._v(tag, cold._ordinal(compiler, arguments[0]))


def _pc_key(node: tuple[int, ...]) -> bytes:
    return codec.encode_value(_PC_NODE_SCHEMA, _pc_value(node))


def _edge_value(
    edge: tuple[tuple[int, ...], tuple[int, ...]],
) -> dict[int, Any]:
    return {0: _pc_value(edge[0]), 1: _pc_value(edge[1])}


def _edge_key(edge: tuple[tuple[int, ...], tuple[int, ...]]) -> bytes:
    return codec.encode_value(_PC_EDGE_SCHEMA, _edge_value(edge))


def _join(values: list[int]) -> int:
    for value in (3, 2, 1):
        if value in values:
            return value
    return 0


def _publish(value: int) -> int:
    return 1 if value in (0, 1) else value


def _positions(core: dict[str, Any]) -> dict[str, dict[int, int]]:
    rows: dict[str, dict[int, int]] = {
        "challenge": {},
        "check": {},
        "reduction": {},
        "terminal": {},
        "publication": {},
    }
    for occurrence_ref, occurrence in enumerate(core["occurrences"]):
        effect = occurrence["effect"]
        tag = effect["tag"]
        if tag == 2:
            table, ordinal = "challenge", effect["challenge"]
        elif tag == 3:
            table, ordinal = "check", effect["check"]
        elif tag == 4:
            table, ordinal = "reduction", effect["reduction"]
        elif tag == 5:
            table, ordinal = "terminal", effect["terminal"]
        elif tag == 6 and effect["oracle_tag"] == 0:
            table, ordinal = "publication", effect["oracle"]
        else:
            continue
        if ordinal in rows[table]:
            raise ColdIntegratedError(f"duplicate {table} backlink")
        rows[table][ordinal] = occurrence_ref
    expected = {
        "challenge": len(core["challenges"]),
        "check": len(core["checks"]),
        "reduction": len(core["reductions"]),
        "terminal": len(core["terminals"]),
        "publication": len(core["oracles"]),
    }
    if any(set(rows[name]) != set(range(count)) for name, count in expected.items()):
        raise ColdIntegratedError("declaration backlinks are not exact and total")
    return rows


def _output_arities(
    core: dict[str, Any], modules: Mapping[int, dict[str, Any]]
) -> tuple[int, ...]:
    result: list[int] = []
    for occurrence_ref, occurrence in enumerate(core["occurrences"]):
        effect = occurrence["effect"]
        tag = effect["tag"]
        if tag in (0, 1, 2, 3):
            result.append(1)
        elif tag in (4, 5):
            result.append(0)
        elif tag == 6:
            oracle_tag = effect["oracle_tag"]
            if oracle_tag == 0:
                mode = core["oracles"][effect["oracle"]]["mode"]["tag"]
                result.append(0 if mode == 2 else 1)
            elif oracle_tag == 1:
                result.append(0)
            else:
                result.append(1)
        elif tag == 7:
            result.append(len(modules[occurrence_ref]["outputs"]))
        else:  # pragma: no cover - parser closes this
            raise ColdIntegratedError("unknown effect output rule")
    return tuple(result)


def _module_dependency_node(
    effect: dict[str, Any], dependency: dict[str, int | None], occurrence_ref: int
) -> tuple[int, ...]:
    tag = dependency["tag"]
    ordinal = dependency["ordinal"]
    if tag == 0:
        return 6, occurrence_ref
    if tag == 1:
        return 7, occurrence_ref
    if ordinal is None:
        raise ColdIntegratedError("indexed module dependency lacks an ordinal")
    if tag == 2:
        if not 0 <= ordinal < len(effect["inputs"]):
            raise ColdIntegratedError("module payload dependency is absent")
        return _producer(effect["inputs"][ordinal])
    return 13, occurrence_ref, ordinal


def _descendants(
    source: tuple[int, ...],
    outgoing: Mapping[tuple[int, ...], set[tuple[int, ...]]],
) -> set[tuple[int, ...]]:
    seen = {source}
    pending = [source]
    while pending:
        current = pending.pop()
        for child in outgoing[current]:
            if child not in seen:
                seen.add(child)
                pending.append(child)
    return seen


def _backward_closure(
    source: tuple[int, ...],
    edges: tuple[tuple[tuple[int, ...], tuple[int, ...]], ...],
) -> set[tuple[int, ...]]:
    incoming: dict[tuple[int, ...], set[tuple[int, ...]]] = {}
    for parent, child in edges:
        incoming.setdefault(child, set()).add(parent)
        incoming.setdefault(parent, set())
    seen = {source}
    pending = [source]
    while pending:
        current = pending.pop()
        for parent in incoming.get(current, set()):
            if parent not in seen:
                seen.add(parent)
                pending.append(parent)
    return seen


def _derive_graph(
    core: dict[str, Any], module_occurrences: Mapping[int, dict[str, Any]]
) -> tuple[dict[int, Any], dict[str, Any]]:
    outputs = _output_arities(core, module_occurrences)
    positions = _positions(core)
    incoming: dict[tuple[int, ...], set[tuple[int, ...]]] = {}
    outgoing: dict[tuple[int, ...], set[tuple[int, ...]]] = {}

    def node(value: tuple[int, ...]) -> tuple[int, ...]:
        incoming.setdefault(value, set())
        outgoing.setdefault(value, set())
        return value

    def edge(source: tuple[int, ...], target: tuple[int, ...]) -> None:
        source, target = node(source), node(target)
        incoming[target].add(source)
        outgoing[source].add(target)

    for ordinal in range(len(core["public_inputs"])):
        node((0, ordinal))
    for ordinal in range(len(core["private_inputs"])):
        node((1, ordinal))
    for ordinal in range(len(core["constants"])):
        node((2, ordinal))
    for ordinal, derived in enumerate(core["derived"]):
        target = node((3, ordinal))
        for reference in derived["inputs"]:
            edge(_producer(reference), target)
    for ordinal, scope in enumerate(core["scopes"]):
        target = node((4, ordinal))
        if scope["parent"] is not None:
            edge((4, scope["parent"]), target)
    for ordinal, binding in enumerate(core["bindings"]):
        edge((4, binding["scope"]), (5, ordinal))
        edge(_producer(binding["value"]), (5, ordinal))

    module_outputs: dict[tuple[int, ...], dict[str, Any]] = {}
    module_controls: dict[tuple[int, ...], dict[str, Any]] = {}
    earlier_terminals: list[tuple[int, ...]] = []
    for occurrence_ref, occurrence in enumerate(core["occurrences"]):
        activity = node((6, occurrence_ref))
        effect_node = node((7, occurrence_ref))
        edge((4, occurrence["scope"]), activity)
        if occurrence["guard"]["tag"] == 1:
            for reference in occurrence["guard"]["inputs"]:
                edge(_producer(reference), activity)
        for terminal in earlier_terminals:
            edge(terminal, activity)
        edge(activity, effect_node)
        effect = occurrence["effect"]
        tag = effect["tag"]
        if tag == 1:
            for reference in effect["inputs"]:
                edge(_producer(reference), effect_node)
        elif tag == 2:
            challenge = core["challenges"][effect["challenge"]]
            for condition in challenge["conditions"]:
                edge(_producer(condition), effect_node)
            if challenge["correlation"]["tag"] == 1:
                for prior_member in challenge["correlation"]["prior"]:
                    edge((8, positions["challenge"][prior_member], 0), effect_node)
        elif tag == 3:
            for reference in core["checks"][effect["check"]]["inputs"]:
                edge(_producer(reference), effect_node)
        elif tag == 4:
            reduction = core["reductions"][effect["reduction"]]
            for claim_ref in reduction["input_claims"]:
                edge((9, claim_ref), effect_node)
            for reference in reduction["side_inputs"]:
                edge(_producer(reference), effect_node)
            for challenge_ref in reduction["required_challenges"]:
                edge((8, positions["challenge"][challenge_ref], 0), effect_node)
            for requirement in reduction["required_publications"]:
                edge((7, requirement["publication"]), effect_node)
            edge(effect_node, (10, effect["reduction"]))
        elif tag == 5:
            terminal = core["terminals"][effect["terminal"]]
            for reference in terminal["outputs"]:
                edge(_producer(reference), effect_node)
            for check_ref in terminal["checks"]:
                edge((8, positions["check"][check_ref], 0), effect_node)
            for reduction_ref in terminal["reductions"]:
                edge((10, reduction_ref), effect_node)
            for claim_ref in terminal["claims"]:
                edge((9, claim_ref), effect_node)
            terminal_node = node((11, effect["terminal"]))
            edge(effect_node, terminal_node)
            earlier_terminals.append(terminal_node)
        elif tag == 6 and effect["oracle_tag"] == 1:
            edge((7, positions["publication"][effect["oracle"]]), effect_node)
            edge(_producer(effect["index"]), effect_node)
        elif tag == 6 and effect["oracle_tag"] == 2:
            query = core["occurrences"][effect["query"]]["effect"]
            if query["tag"] != 6 or query["oracle_tag"] != 1:
                raise ColdIntegratedError("Oracle Answer backlink is not a Query")
            edge((7, effect["query"]), effect_node)
            edge((7, positions["publication"][query["oracle"]]), effect_node)
        elif tag == 7:
            semantics = module_occurrences[occurrence_ref]
            for control_ordinal, control in enumerate(semantics["controls"]):
                control_node = node((12, occurrence_ref, control_ordinal))
                module_controls[control_node] = control
                for dependency in control["dependencies"]:
                    edge(
                        _module_dependency_node(effect, dependency, occurrence_ref),
                        control_node,
                    )
            for output_ordinal, output in enumerate(semantics["outputs"]):
                output_node = node((13, occurrence_ref, output_ordinal))
                module_outputs[output_node] = output
                for dependency in output["dependencies"]:
                    edge(
                        _module_dependency_node(effect, dependency, occurrence_ref),
                        output_node,
                    )
                edge(output_node, (8, occurrence_ref, output_ordinal))
        for output_ordinal in range(outputs[occurrence_ref]):
            edge(effect_node, (8, occurrence_ref, output_ordinal))

    for claim_ref, claim in enumerate(core["claims"]):
        source = claim["source"]
        if source["tag"] == 0:
            edge((5, source["binding"]), (9, claim_ref))
        else:
            edge((10, source["reduction"]), (9, claim_ref))

    indegree = {item: len(parents) for item, parents in incoming.items()}
    heap = [(_pc_key(item), item) for item, count in indegree.items() if count == 0]
    heapq.heapify(heap)
    topological: list[tuple[int, ...]] = []
    while heap:
        _encoded, current = heapq.heappop(heap)
        topological.append(current)
        for child in outgoing[current]:
            indegree[child] -= 1
            if indegree[child] == 0:
                heapq.heappush(heap, (_pc_key(child), child))
    if len(topological) != len(incoming):
        raise ColdIntegratedError("integrated PCGraph is cyclic")

    classes: dict[tuple[int, ...], int] = {}
    challenge_validity: dict[int, bool] = {}
    for current in topological:
        tag = current[0]
        joined = _join([classes[item] for item in incoming[current]])
        if tag in (0, 2):
            value = 0
        elif tag == 1:
            value = 2
        elif current in module_outputs:
            transfer = module_outputs[current]["transfer"]
            if transfer == 0:
                value = joined
            elif transfer == 1:
                value = _publish(joined)
            else:
                value = 3
        elif tag == 7:
            effect = core["occurrences"][current[1]]["effect"]
            if (
                effect["tag"] == 6
                and effect["oracle_tag"] == 0
                and core["oracles"][effect["oracle"]]["mode"]["tag"] == 2
            ):
                value = _publish(classes[(6, current[1])])
            elif effect["tag"] == 6 and effect["oracle_tag"] == 1:
                value = (
                    2
                    if effect["visibility"] == 1
                    else _join(
                        [
                            classes[(6, current[1])],
                            classes[_producer(effect["index"])],
                        ]
                    )
                )
            elif effect["tag"] == 6 and effect["oracle_tag"] == 2:
                query = core["occurrences"][effect["query"]]["effect"]
                value = 2 if query["visibility"] == 1 else joined
            else:
                value = joined
        elif tag == 8:
            effect = core["occurrences"][current[1]]["effect"]
            activity_class = classes[(6, current[1])]
            if effect["tag"] == 0:
                value = _publish(activity_class)
            elif effect["tag"] == 1:
                value = _join(
                    [activity_class]
                    + [classes[_producer(item)] for item in effect["inputs"]]
                )
            elif effect["tag"] == 2:
                challenge = core["challenges"][effect["challenge"]]
                condition_classes = [
                    classes[_producer(item)] for item in challenge["conditions"]
                ]
                prior_classes = (
                    [
                        classes[(8, positions["challenge"][item], 0)]
                        for item in challenge["correlation"]["prior"]
                    ]
                    if challenge["correlation"]["tag"] == 1
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
                elif activity_class in (0, 1):
                    value = 1
                else:  # pragma: no cover - closed lattice
                    value = 3
                challenge_validity[effect["challenge"]] = value == 1
            elif effect["tag"] == 6 and effect["oracle_tag"] == 0:
                value = _publish(activity_class)
            elif effect["tag"] == 6 and effect["oracle_tag"] == 2:
                query = core["occurrences"][effect["query"]]["effect"]
                value = 2 if query["visibility"] == 1 else _publish(activity_class)
            else:
                value = joined
        else:
            value = joined
        classes[current] = value

    binding_sinks = {(5, index) for index in range(len(core["bindings"]))}
    public_observations: set[tuple[int, ...]] = set(binding_sinks)
    observation_activities: set[tuple[int, ...]] = set()
    challenge_condition_sinks: set[tuple[int, ...]] = set()
    challenge_sinks: set[tuple[int, ...]] = set()
    check_sinks: set[tuple[int, ...]] = set()
    for occurrence_ref, occurrence in enumerate(core["occurrences"]):
        effect = occurrence["effect"]
        tag = effect["tag"]
        observed: set[tuple[int, ...]] = set()
        if tag in (0, 1):
            observed.update(
                (8, occurrence_ref, output) for output in range(outputs[occurrence_ref])
            )
        elif tag == 2:
            observed.add((8, occurrence_ref, 0))
            challenge_sinks.add((8, occurrence_ref, 0))
            challenge_condition_sinks.update(
                _producer(item)
                for item in core["challenges"][effect["challenge"]]["conditions"]
            )
        elif tag == 3:
            check_sinks.add((7, occurrence_ref))
        elif tag == 6 and effect["oracle_tag"] == 0:
            mode = core["oracles"][effect["oracle"]]["mode"]["tag"]
            if mode == 2:
                observed.add((7, occurrence_ref))
            else:
                observed.update(
                    (8, occurrence_ref, output)
                    for output in range(outputs[occurrence_ref])
                )
        elif tag == 6 and effect["oracle_tag"] == 1:
            if effect["visibility"] == 0:
                observed.add((7, occurrence_ref))
                public_observations.add(_producer(effect["index"]))
        elif tag == 6 and effect["oracle_tag"] == 2:
            query = core["occurrences"][effect["query"]]["effect"]
            if query["visibility"] == 0:
                observed.add((8, occurrence_ref, 0))
        elif tag == 7:
            semantics = module_occurrences[occurrence_ref]
            for output_ordinal, output in enumerate(semantics["outputs"]):
                if output["visibility"] == 3:
                    observed.update(
                        {
                            (13, occurrence_ref, output_ordinal),
                            (8, occurrence_ref, output_ordinal),
                        }
                    )
        if observed:
            public_observations.update(observed)
            observation_activities.add((6, occurrence_ref))

    reduction_sinks = {(10, index) for index in range(len(core["reductions"]))}
    terminal_sinks = {(11, index) for index in range(len(core["terminals"]))}
    terminal_outputs = {
        _producer(reference)
        for terminal in core["terminals"]
        for reference in terminal["outputs"]
    }
    acceptance_module = {
        item
        for item, spec in (*module_outputs.items(), *module_controls.items())
        if spec["acceptance_relevant"]
    }
    sinks = (
        public_observations
        | observation_activities
        | challenge_condition_sinks
        | challenge_sinks
        | check_sinks
        | reduction_sinks
        | terminal_sinks
        | terminal_outputs
        | acceptance_module
    )
    accepting_terminals = {
        (11, index)
        for index, terminal in enumerate(core["terminals"])
        if terminal["verdict"] == 0
    }
    accepting_outputs = {
        _producer(reference)
        for index, terminal in enumerate(core["terminals"])
        if (11, index) in accepting_terminals
        for reference in terminal["outputs"]
    }
    acceptance = (
        check_sinks
        | reduction_sinks
        | accepting_terminals
        | accepting_outputs
        | acceptance_module
    )
    private_predecessors = tuple(
        sorted(
            (
                source
                for source in (
                    (1, index) for index in range(len(core["private_inputs"]))
                )
                if _descendants(source, outgoing) & sinks
            ),
            key=_pc_key,
        )
    )
    logical_cones: dict[int, tuple[tuple[int, ...], ...]] = {}
    logical_intersections: dict[int, tuple[tuple[int, ...], ...]] = {}
    for oracle_ref, declaration in enumerate(core["oracles"]):
        if declaration["mode"]["tag"] != 2:
            continue
        cone = _descendants((7, positions["publication"][oracle_ref]), outgoing)
        intersection = cone & acceptance
        logical_cones[oracle_ref] = tuple(sorted(cone, key=_pc_key))
        logical_intersections[oracle_ref] = tuple(sorted(intersection, key=_pc_key))

    decision_occurrences = {
        index
        for index, occurrence in enumerate(core["occurrences"])
        if occurrence["effect"]["tag"] == 0
        or (
            occurrence["effect"]["tag"] == 6
            and occurrence["effect"]["oracle_tag"] == 0
            and core["oracles"][occurrence["effect"]["oracle"]]["origin"] == 1
        )
        or (index in module_occurrences and module_occurrences[index]["decision"] != 0)
    }
    challenge_order: dict[int, bool] = {}
    for challenge_ref, occurrence_ref in positions["challenge"].items():
        output_node = (8, occurrence_ref, 0)
        descendants = _descendants(output_node, outgoing)
        dependent_decisions = {
            decision
            for decision in decision_occurrences
            if (6, decision) in descendants or (7, decision) in descendants
        }
        challenge_order[challenge_ref] = all(
            occurrence_ref < decision for decision in dependent_decisions
        )

    ordered_nodes = tuple(sorted(incoming, key=_pc_key))
    ordered_edges = tuple(
        sorted(
            (
                (source, target)
                for target, parents in incoming.items()
                for source in parents
            ),
            key=_edge_key,
        )
    )
    ordered_sinks = tuple(sorted(sinks, key=_pc_key))
    ordered_acceptance = tuple(sorted(acceptance, key=_pc_key))
    eligible = (
        all(classes[item] in (0, 1) for item in ordered_sinks)
        and all(
            challenge_validity.get(index, False)
            for index in range(len(core["challenges"]))
        )
        and all(challenge_order.values())
        and not any(logical_intersections.values())
    )
    graph = {
        0: [_pc_value(item) for item in ordered_nodes],
        1: [_edge_value(item) for item in ordered_edges],
        2: [_pc_value(item) for item in topological],
        3: [{0: _pc_value(item), 1: cold._v(classes[item])} for item in ordered_nodes],
        4: [_pc_value(item) for item in ordered_sinks],
        5: [_pc_value(item) for item in ordered_acceptance],
        6: [
            {
                0: cold._ordinal("oracle-ref-body-v0", oracle_ref),
                1: [_pc_value(item) for item in logical_cones[oracle_ref]],
                2: [_pc_value(item) for item in logical_intersections[oracle_ref]],
            }
            for oracle_ref in sorted(logical_cones)
        ],
    }
    evidence = {
        "nodes": ordered_nodes,
        "edges": ordered_edges,
        "topological": tuple(topological),
        "classes": classes,
        "sinks": ordered_sinks,
        "acceptance_sinks": ordered_acceptance,
        "private_predecessors": private_predecessors,
        "logical_cones": logical_cones,
        "logical_intersections": logical_intersections,
        "challenge_validity": challenge_validity,
        "challenge_observation_order": challenge_order,
        "eligible": eligible,
    }
    if {item[0] for item in ordered_nodes} != set(range(14)):
        raise ColdIntegratedError("integrated PCNode coverage differs")
    if set(classes.values()) != {0, 1, 2, 3}:
        raise ColdIntegratedError("integrated PCClass coverage differs")
    return graph, evidence


def project(
    core_profiled_body: bytes,
    core_reference: bytes,
    protocol_profiled_body: bytes,
    protocol_reference: bytes,
    module_sources: tuple[tuple[bytes, bytes], ...],
    algorithm_preimages: tuple[tuple[bytes, bytes], ...],
    evaluation_contract_reference: bytes,
) -> tuple[dict[int, Any], dict[str, Any]]:
    """Authenticate both subjects and derive PublicCoinView independently."""

    try:
        core_profile, core_domain = cold._authenticated_subject(
            core_profiled_body,
            core_reference,
            "pir.interactive-core",
            "cold integrated Core",
        )
        protocol_profile, protocol_domain = cold._authenticated_subject(
            protocol_profiled_body,
            protocol_reference,
            "pir.protocol",
            "cold integrated Fresh Protocol",
        )
    except Exception as error:
        raise ColdIntegratedError(str(error)) from error
    if core_profile != protocol_profile:
        raise ColdIntegratedError("Core and Protocol profiles differ")
    protocol_core, interpretation = _record(protocol_domain, (0, 1), "Fresh Protocol")
    interpretation_tag, interpretation_payload = _variant(
        interpretation, {0}, "Fresh interpretation"
    )
    if interpretation_tag != 0:  # pragma: no cover - parser closes this
        raise ColdIntegratedError("Protocol interpretation differs")
    _unit(interpretation_payload, "Fresh interpretation payload")
    if _bytes(protocol_core, "Fresh Protocol Core") != core_reference:
        raise ColdIntegratedError("Fresh Protocol names another Core")
    domain_body = k1.encode_datum(core_domain)
    if hashlib.sha256(domain_body).hexdigest() not in SUPPORTED_DOMAIN_SHA256:
        raise ColdIntegratedError("Core lies outside five exact D1 carriers")
    core = _decode_core(core_domain)
    sources = _source_closure(core["used_modules"], module_sources)
    module_occurrences = _module_occurrences(core, sources)
    _algorithm_closure(
        core,
        module_occurrences,
        algorithm_preimages,
        evaluation_contract_reference,
    )
    graph, evidence = _derive_graph(core, module_occurrences)
    positions = _positions(core)
    consumers: dict[int, list[int]] = {
        index: [] for index in range(len(core["challenges"]))
    }
    for reduction_ref, reduction in enumerate(core["reductions"]):
        for challenge_ref in reduction["required_challenges"]:
            consumers[challenge_ref].append(reduction_ref)
    challenge_rows: list[dict[int, Any]] = []
    for challenge_ref, challenge in enumerate(core["challenges"]):
        closure = {
            item
            for condition in challenge["conditions"]
            for item in _backward_closure(_producer(condition), evidence["edges"])
        }
        challenge_rows.append(
            {
                0: cold._ordinal("challenge-ref-body-v0", challenge_ref),
                1: cold._ordinal(
                    "occurrence-ref-body-v0",
                    positions["challenge"][challenge_ref],
                ),
                2: cold._ordinal("scope-ref-body-v0", challenge["scope"]),
                3: cold._value_type(challenge["type"]),
                4: cold._module_ref(challenge["domain"]),
                5: cold._module_ref(challenge["fresh_law"]),
                6: b3cold._correlation_value(challenge["correlation"]),
                7: b3cold._reduction_use_value(challenge["reduction_use"]),
                8: [cold._value_ref(item) for item in challenge["conditions"]],
                9: [_pc_value(item) for item in sorted(closure, key=_pc_key)],
                10: [
                    {
                        0: cold._ordinal("reduction-ref-body-v0", reduction_ref),
                        1: cold._ordinal("challenge-ref-body-v0", challenge_ref),
                    }
                    for reduction_ref in consumers[challenge_ref]
                ],
            }
        )
    value = {
        0: cold._identifier("core-id-body-v0", core_reference),
        1: graph,
        2: evidence["eligible"],
        3: [_pc_value(item) for item in evidence["private_predecessors"]],
        4: challenge_rows,
    }
    codec.encode_value(VIEW_SCHEMAS["PublicCoinView"], value)
    return value, evidence


def encode_public_coin(value: dict[int, Any]) -> bytes:
    return codec.encode_value(VIEW_SCHEMAS["PublicCoinView"], value)
