#!/usr/bin/env python3
"""Reference exact-value codec for the F0-V2B2C1 owner-view program.

The B2B package deliberately used JSON only as a diagnostic representation.
This module gives its structural schemas a target-facing interpretation as
exact K1 ``MetaValueV0`` bodies.  It is a research codec, not a published PIR
body compiler or an owner projection.
"""

from __future__ import annotations

import copy
import importlib.util
from pathlib import Path
import sys
from types import ModuleType
from typing import Any


ROOT = Path(__file__).resolve().parents[2]
B2B_MODEL = ROOT / "evaluation/formal-source-view-schema-f0v2b2b/model.py"
OWNER_MODEL = ROOT / "evaluation/formal-source-target-core-f1r1b/reference_model.py"

MAX_CODEC_NODES = 1 << 16
MAX_CODEC_DEPTH = 96
LAW_ORDINALS = {
    "core-admission-v0": 1,
    "execution-and-replay-v0": 2,
    "run-view-issuance-v0": 4,
}


class CodecError(ValueError):
    """The schema/value pair has no exact target-facing body."""


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


b2b = _load("_zkc_f0v2b2c1a_b2b_reference", B2B_MODEL)
owner = _load("_zkc_f0v2b2c1a_owner_reference", OWNER_MODEL)
k1 = owner.k1


def _encoded(value: object) -> str:
    return k1.encode_datum(value).hex()


def _canonical_atom(compiler: str, value: object) -> dict[str, str]:
    return {"compiler": compiler, "body": _encoded(value)}


def _ordinal_atom(compiler: str, value: int = 0) -> dict[str, str]:
    return _canonical_atom(compiler, k1.Nat(value))


def _identifier_atom(compiler: str, identifier: object) -> dict[str, str]:
    return _canonical_atom(compiler, k1.BytesValue(identifier.internal_reference()))


def _codec_module() -> object:
    declaration = k1.DatumRecord(((0, k1.Symbol("codec-only-effect")),))
    catalog = k1.DatumRecord(
        (
            (0, k1.Symbol("pir.core-effect")),
            (1, k1.DatumSeq((declaration,))),
        )
    )
    return k1.SemanticModuleCandidate(
        k1.Symbol("f0v2b2c1a.exact-view-codec"),
        (),
        k1.DatumSeq((catalog,)),
    )


def sample_catalog() -> dict[str, Any]:
    """Return one exact, decodable sample for every B2B semantic atom."""

    fixture = owner.make_fixture()
    module_ref = owner.ModuleDeclarationRef(
        fixture.module.identity, "pir.message-channel", 0
    )
    ordinal_compilers = {
        "binding-ref-body-v0",
        "challenge-ref-body-v0",
        "check-ref-body-v0",
        "claim-ref-body-v0",
        "constant-ref-body-v0",
        "decision-ref-body-v0",
        "derived-value-ref-body-v0",
        "occurrence-ref-body-v0",
        "oracle-ref-body-v0",
        "public-input-ref-body-v0",
        "reduction-ref-body-v0",
        "scope-ref-body-v0",
        "terminal-ref-body-v0",
        "verifier-private-input-ref-body-v0",
    }
    canonical: dict[str, dict[str, str]] = {
        compiler: _ordinal_atom(compiler) for compiler in ordinal_compilers
    }
    canonical.update(
        {
            "algorithm-ref-body-v0": _identifier_atom(
                "algorithm-ref-body-v0", fixture.schnorr_algorithm.identity
            ),
            "core-id-body-v0": _identifier_atom(
                "core-id-body-v0", fixture.core_candidate.asserted_id
            ),
            "evaluation-contract-id-body-v0": _identifier_atom(
                "evaluation-contract-id-body-v0",
                k1.DEFAULT_EVALUATION_CONTRACT.identity,
            ),
            "guard-body-v0": _canonical_atom(
                "guard-body-v0", owner._guard_datum(owner.AlwaysGuard())
            ),
            "module-declaration-ref-body-v0": _canonical_atom(
                "module-declaration-ref-body-v0",
                owner.module_declaration_ref_datum(module_ref),
            ),
            "protocol-id-body-v0": _identifier_atom(
                "protocol-id-body-v0", fixture.protocol_candidate.asserted_id
            ),
            "value-ref-body-v0": _canonical_atom(
                "value-ref-body-v0", owner.value_ref_datum(owner.PublicInputRef(0))
            ),
            "value-type-body-v0": _canonical_atom(
                "value-type-body-v0", k1.value_type_datum(owner.Z3)
            ),
        }
    )
    codec_module = _codec_module()
    effect_ref = owner.ModuleDeclarationRef(codec_module.identity, "pir.core-effect", 0)
    module_effect = {
        "module_body": _encoded(
            k1.BytesValue(codec_module.identity.internal_reference())
        ),
        "declaration_body": _encoded(owner.module_declaration_ref_datum(effect_ref)),
        "payload_body": _encoded(k1.DatumRecord(((0, k1.Symbol("codec-payload")),))),
    }
    return {
        "canonical": canonical,
        "module_effect": module_effect,
        "compiler_count": len(canonical),
        "codec_module": codec_module,
    }


def _strict_datum(raw_hex: object, label: str) -> object:
    if type(raw_hex) is not str or not raw_hex or len(raw_hex) % 2:
        raise CodecError(f"{label} is not nonempty even-length hexadecimal")
    try:
        raw = bytes.fromhex(raw_hex)
    except ValueError as error:
        raise CodecError(f"{label} is not hexadecimal") from error
    if raw.hex() != raw_hex:
        raise CodecError(f"{label} is not canonical lowercase hexadecimal")
    try:
        datum = k1.decode_datum(raw)
    except Exception as error:
        raise CodecError(
            f"{label} is not one complete canonical datum: {error}"
        ) from error
    if k1.encode_datum(datum) != raw:
        raise CodecError(f"{label} does not re-encode byte-identically")
    return datum


def _law_datum(atom: dict[str, Any], value: object) -> object:
    expected = {
        "profile": b2b.PROFILE["profile_digest"],
        "kind": "pir.semantic-law",
        "name": atom["law"],
    }
    if value != expected:
        raise CodecError("exact profile-law value was substituted")
    try:
        ordinal = LAW_ORDINALS[atom["law"]]
    except KeyError as error:  # pragma: no cover - source compiler checks this set
        raise CodecError("exact profile-law body compiler is absent") from error
    return k1.profile_declaration_ref_datum(
        k1.ProfileLocalDeclarationRef("pir.semantic-law", ordinal)
    )


def _module_effect_datum(value: object) -> object:
    if type(value) is not dict or set(value) != {
        "module_body",
        "declaration_body",
        "payload_body",
    }:
        raise CodecError("admitted module-effect atom has another exact shape")
    module = _strict_datum(value["module_body"], "module-effect module body")
    declaration = _strict_datum(
        value["declaration_body"], "module-effect declaration body"
    )
    payload = _strict_datum(value["payload_body"], "module-effect payload body")
    if type(module) is not k1.BytesValue:
        raise CodecError("module-effect owner is not SemanticModuleRefBody")
    try:
        module_id = k1.decode_content_reference(module.value)
    except Exception as error:
        raise CodecError("module-effect owner reference is malformed") from error
    if module_id.subject_kind != k1.SEMANTIC_MODULE_KIND:
        raise CodecError("module-effect owner has another subject kind")
    if (
        type(declaration) is not k1.DatumVariant
        or declaration.case != 1
        or type(declaration.payload) is not k1.DatumRecord
        or tuple(item[0] for item in declaration.payload.fields) != (0, 1, 2)
    ):
        raise CodecError("module-effect declaration has another reference body")
    owner_value, kind, _ordinal = tuple(item[1] for item in declaration.payload.fields)
    if (
        type(owner_value) is not k1.BytesValue
        or owner_value.value != module.value
        or type(kind) is not k1.Symbol
        or kind.value != "pir.core-effect"
    ):
        raise CodecError("module-effect owner and declaration do not pair")
    return k1.DatumRecord(((0, module), (1, declaration), (2, payload)))


def _atom_datum(atom: dict[str, Any], value: object) -> object:
    kind = atom["kind"]
    if kind == "unit":
        if value is not None:
            raise CodecError("Unit atom has a non-Unit value")
        return k1.UNIT
    if kind == "natural":
        if type(value) is not int or not 0 <= value <= atom["max"]:
            raise CodecError("Natural atom is outside its exact bound")
        return k1.Nat(value)
    if kind == "meta-boolean":
        if type(value) is not bool:
            raise CodecError("MetaBoolean atom has another type")
        return value
    if kind == "canonical-body":
        if type(value) is not dict or set(value) != {"compiler", "body"}:
            raise CodecError("canonical-body atom has another exact shape")
        if value["compiler"] != atom["compiler"]:
            raise CodecError("canonical-body compiler was substituted")
        return _strict_datum(value["body"], "canonical-body atom")
    if kind == "exact-profile-law":
        return _law_datum(atom, value)
    if kind == "admitted-module-effect":
        return _module_effect_datum(value)
    raise CodecError("schema contains an unknown atom kind")


def datum_for_value(
    schema: dict[str, Any],
    value: object,
    *,
    depth: int = 0,
    budget: list[int] | None = None,
) -> object:
    """Compile one schema-directed diagnostic value to its exact K1 datum."""

    if budget is None:
        budget = [MAX_CODEC_NODES]
    if depth > MAX_CODEC_DEPTH:
        raise CodecError("view value crosses the codec depth bound")
    budget[0] -= 1
    if budget[0] < 0:
        raise CodecError("view value crosses the codec node bound")
    node = schema.get("node")
    if node == "atom":
        return _atom_datum(schema["atom"], value)
    if node == "record":
        expected = [ordinal for ordinal, _child in schema["fields"]]
        if type(value) is not dict or list(value) != expected:
            raise CodecError("record value has another exact field set or order")
        return k1.DatumRecord(
            tuple(
                (
                    ordinal,
                    datum_for_value(
                        child, value[ordinal], depth=depth + 1, budget=budget
                    ),
                )
                for ordinal, child in schema["fields"]
            )
        )
    if node == "variant":
        if type(value) is not dict or set(value) != {"case", "value"}:
            raise CodecError("variant value has another exact shape")
        selected = [
            child for ordinal, child in schema["cases"] if ordinal == value["case"]
        ]
        if len(selected) != 1:
            raise CodecError("variant selected an absent case")
        return k1.DatumVariant(
            value["case"],
            datum_for_value(
                selected[0], value["value"], depth=depth + 1, budget=budget
            ),
        )
    if node == "sequence":
        if type(value) is not list or not schema["min"] <= len(value) <= schema["max"]:
            raise CodecError("sequence value is outside its exact length interval")
        children = tuple(
            datum_for_value(schema["element"], item, depth=depth + 1, budget=budget)
            for item in value
        )
        if schema["discipline"] == "sorted-unique":
            bodies = tuple(k1.encode_datum(item) for item in children)
            if any(left >= right for left, right in zip(bodies, bodies[1:])):
                raise CodecError(
                    "sorted-unique sequence is not ordered by exact target bodies"
                )
        return k1.DatumSeq(children)
    raise CodecError("schema contains an unknown structural node")


def encode_value(schema: dict[str, Any], value: object) -> bytes:
    return k1.encode_datum(datum_for_value(schema, value))


def materialize(
    schema: dict[str, Any], value: object, samples: dict[str, Any]
) -> object:
    """Replace B2B placeholder atoms with compiler-specific exact samples."""

    node = schema["node"]
    if node == "atom":
        atom = schema["atom"]
        if atom["kind"] == "canonical-body":
            return copy.deepcopy(samples["canonical"][atom["compiler"]])
        if atom["kind"] == "admitted-module-effect":
            return copy.deepcopy(samples["module_effect"])
        if atom["kind"] == "exact-profile-law":
            return {
                "profile": b2b.PROFILE["profile_digest"],
                "kind": "pir.semantic-law",
                "name": atom["law"],
            }
        return copy.deepcopy(value)
    if node == "record":
        return {
            ordinal: materialize(child, value[ordinal], samples)
            for ordinal, child in schema["fields"]
        }
    if node == "variant":
        child = next(
            child for ordinal, child in schema["cases"] if ordinal == value["case"]
        )
        return {
            "case": value["case"],
            "value": materialize(child, value["value"], samples),
        }
    if node == "sequence":
        return [materialize(schema["element"], item, samples) for item in value]
    raise CodecError("materializer reached an unknown structural node")


def record_field(schema: dict[str, Any], ordinal: int) -> dict[str, Any]:
    selected = [child for field, child in schema["fields"] if field == ordinal]
    if len(selected) != 1:
        raise CodecError(f"record has no unique field {ordinal}")
    return selected[0]


def exact_pcnode_order_probe(
    schemas: dict[str, Any], samples: dict[str, Any]
) -> dict[str, Any]:
    public_coin = schemas["PublicCoinView"]
    graph = record_field(public_coin, 1)
    node_sequence = record_field(graph, 0)
    node_schema = node_sequence["element"]
    constant = {
        "case": 2,
        "value": copy.deepcopy(samples["canonical"]["constant-ref-body-v0"]),
    }
    reduction = {
        "case": 10,
        "value": copy.deepcopy(samples["canonical"]["reduction-ref-body-v0"]),
    }
    values = [constant, reduction]
    target_order = sorted(values, key=lambda item: encode_value(node_schema, item))
    diagnostic_order = sorted(values, key=b2b.wire)
    return {
        "sequence_schema": node_sequence,
        "node_schema": node_schema,
        "target": target_order,
        "diagnostic": diagnostic_order,
        "target_cases": [item["case"] for item in target_order],
        "diagnostic_cases": [item["case"] for item in diagnostic_order],
    }
