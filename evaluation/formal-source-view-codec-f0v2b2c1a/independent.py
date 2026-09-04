#!/usr/bin/env python3
"""Iterative independent exact-value codec for F0-V2B2C1A."""

from __future__ import annotations

import importlib.util
from pathlib import Path
import sys
from types import ModuleType
from typing import Any


ROOT = Path(__file__).resolve().parents[2]
B2B_INDEPENDENT = ROOT / "evaluation/formal-source-view-schema-f0v2b2b/independent.py"
K1_MODEL = ROOT / "evaluation/k1-executable-foundations/reference_model.py"
MAX_CODEC_NODES = 1 << 16
MAX_CODEC_DEPTH = 96
LAW_ORDINALS = {
    "core-admission-v0": 1,
    "execution-and-replay-v0": 2,
    "run-view-issuance-v0": 4,
}


class ColdCodecError(ValueError):
    """The cold codec cannot form one exact target-facing body."""


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


b2b = _load("_zkc_f0v2b2c1a_b2b_cold", B2B_INDEPENDENT)
k1 = _load("_zkc_f0v2b2c1a_k1_cold", K1_MODEL)


def _decode_body(value: object, label: str) -> object:
    if type(value) is not str or not value or len(value) % 2:
        raise ColdCodecError(f"{label} is not an exact hexadecimal body")
    try:
        raw = bytes.fromhex(value)
        datum = k1.decode_datum(raw)
    except Exception as error:
        raise ColdCodecError(f"{label} does not decode exactly: {error}") from error
    if raw.hex() != value or k1.encode_datum(datum) != raw:
        raise ColdCodecError(f"{label} is not canonical")
    return datum


def _atom(atom: dict[str, Any], value: object) -> object:
    kind = atom["kind"]
    if kind == "unit":
        if value is not None:
            raise ColdCodecError("cold Unit atom mismatch")
        return k1.UNIT
    if kind == "natural":
        if type(value) is not int or value < 0 or value > atom["max"]:
            raise ColdCodecError("cold Natural atom mismatch")
        return k1.Nat(value)
    if kind == "meta-boolean":
        if type(value) is not bool:
            raise ColdCodecError("cold MetaBoolean atom mismatch")
        return value
    if kind == "canonical-body":
        if (
            type(value) is not dict
            or set(value) != {"compiler", "body"}
            or value["compiler"] != atom["compiler"]
        ):
            raise ColdCodecError("cold canonical-body compiler mismatch")
        return _decode_body(value["body"], "cold canonical-body atom")
    if kind == "exact-profile-law":
        if value != {
            "profile": b2b.PROFILE["profile_digest"],
            "kind": "pir.semantic-law",
            "name": atom["law"],
        }:
            raise ColdCodecError("cold exact profile-law substitution")
        if atom["law"] not in LAW_ORDINALS:
            raise ColdCodecError("cold law compiler is absent")
        return k1.profile_declaration_ref_datum(
            k1.ProfileLocalDeclarationRef("pir.semantic-law", LAW_ORDINALS[atom["law"]])
        )
    if kind == "admitted-module-effect":
        if type(value) is not dict or set(value) != {
            "module_body",
            "declaration_body",
            "payload_body",
        }:
            raise ColdCodecError("cold module-effect shape mismatch")
        module = _decode_body(value["module_body"], "cold module body")
        declaration = _decode_body(value["declaration_body"], "cold declaration body")
        payload = _decode_body(value["payload_body"], "cold payload body")
        if type(module) is not k1.BytesValue:
            raise ColdCodecError("cold module owner is not bytes")
        try:
            identifier = k1.decode_content_reference(module.value)
        except Exception as error:
            raise ColdCodecError("cold module owner is malformed") from error
        if identifier.subject_kind != k1.SEMANTIC_MODULE_KIND:
            raise ColdCodecError("cold module owner kind mismatch")
        if (
            type(declaration) is not k1.DatumVariant
            or declaration.case != 1
            or type(declaration.payload) is not k1.DatumRecord
            or tuple(pair[0] for pair in declaration.payload.fields) != (0, 1, 2)
        ):
            raise ColdCodecError("cold module declaration shape mismatch")
        owner_value, declaration_kind, _ordinal = tuple(
            pair[1] for pair in declaration.payload.fields
        )
        if (
            type(owner_value) is not k1.BytesValue
            or owner_value.value != module.value
            or type(declaration_kind) is not k1.Symbol
            or declaration_kind.value != "pir.core-effect"
        ):
            raise ColdCodecError("cold module owner pairing mismatch")
        return k1.DatumRecord(((0, module), (1, declaration), (2, payload)))
    raise ColdCodecError("cold codec reached an unknown atom")


def encode_value(schema: dict[str, Any], value: object) -> bytes:
    """Compile without recursive descent, using explicit postorder frames."""

    root: tuple[tuple[str, int], ...] = ()
    stack: list[tuple[dict[str, Any], object, tuple[tuple[str, int], ...], bool]] = [
        (schema, value, root, False)
    ]
    built: dict[tuple[tuple[str, int], ...], object] = {}
    visited = 0
    while stack:
        current_schema, current_value, path, finalize = stack.pop()
        if len(path) > MAX_CODEC_DEPTH:
            raise ColdCodecError("cold codec depth bound crossed")
        if not finalize:
            visited += 1
            if visited > MAX_CODEC_NODES:
                raise ColdCodecError("cold codec node bound crossed")
        node = current_schema.get("node")
        if node == "atom":
            if finalize:  # pragma: no cover - atom frames never finalize
                raise ColdCodecError("cold atom received a finalize frame")
            built[path] = _atom(current_schema["atom"], current_value)
            continue
        if not finalize:
            stack.append((current_schema, current_value, path, True))
            if node == "record":
                expected = [field for field, _child in current_schema["fields"]]
                if type(current_value) is not dict or list(current_value) != expected:
                    raise ColdCodecError("cold record field sequence mismatch")
                for field, child in reversed(current_schema["fields"]):
                    stack.append(
                        (child, current_value[field], (*path, ("field", field)), False)
                    )
            elif node == "variant":
                if type(current_value) is not dict or set(current_value) != {
                    "case",
                    "value",
                }:
                    raise ColdCodecError("cold variant shape mismatch")
                selected = [
                    child
                    for case, child in current_schema["cases"]
                    if case == current_value["case"]
                ]
                if len(selected) != 1:
                    raise ColdCodecError("cold variant selected an absent case")
                stack.append(
                    (
                        selected[0],
                        current_value["value"],
                        (*path, ("variant", current_value["case"])),
                        False,
                    )
                )
            elif node == "sequence":
                if (
                    type(current_value) is not list
                    or len(current_value) < current_schema["min"]
                    or len(current_value) > current_schema["max"]
                ):
                    raise ColdCodecError("cold sequence length mismatch")
                for index in reversed(range(len(current_value))):
                    stack.append(
                        (
                            current_schema["element"],
                            current_value[index],
                            (*path, ("sequence", index)),
                            False,
                        )
                    )
            else:
                raise ColdCodecError("cold schema has an unknown structural node")
            continue
        if node == "record":
            built[path] = k1.DatumRecord(
                tuple(
                    (field, built[(*path, ("field", field))])
                    for field, _child in current_schema["fields"]
                )
            )
        elif node == "variant":
            case = current_value["case"]
            built[path] = k1.DatumVariant(case, built[(*path, ("variant", case))])
        elif node == "sequence":
            children = tuple(
                built[(*path, ("sequence", index))]
                for index in range(len(current_value))
            )
            if current_schema["discipline"] == "sorted-unique":
                bodies = tuple(k1.encode_datum(item) for item in children)
                if any(left >= right for left, right in zip(bodies, bodies[1:])):
                    raise ColdCodecError("cold target-body sequence order mismatch")
            built[path] = k1.DatumSeq(children)
        else:  # pragma: no cover - checked before finalization
            raise ColdCodecError("cold finalize reached an unknown node")
    if not built or root not in built:
        raise ColdCodecError("cold codec did not build a root")
    return k1.encode_datum(built[root])
