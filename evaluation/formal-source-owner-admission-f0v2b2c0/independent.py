#!/usr/bin/env python3
"""Cold structural decoder for the B2C0 canonical-byte admission substrate.

This module intentionally does not import ``model.py`` or the F1-R1B owner
model.  It uses only the Foundation datum decoder, begins from canonical bytes,
and derives the comparison summary with an iterative worklist.
"""

from __future__ import annotations

from collections import deque
import hashlib
import importlib.util
from pathlib import Path
import sys
from types import ModuleType


ROOT = Path(__file__).resolve().parents[2]
K1_MODEL = ROOT / "evaluation/k1-executable-foundations/reference_model.py"


class ColdFailure(ValueError):
    """The cold byte parser refused a malformed or differently shaped body."""


def _load_k1() -> ModuleType:
    name = "_zkc_f0v2b2c0_cold_k1"
    if name in sys.modules:
        return sys.modules[name]
    spec = importlib.util.spec_from_file_location(name, K1_MODEL)
    if spec is None or spec.loader is None:  # pragma: no cover - host failure
        raise ImportError(f"cannot load Foundation model at {K1_MODEL}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


k1 = _load_k1()


def _record(value: object, ordinals: tuple[int, ...], label: str) -> tuple[object, ...]:
    if type(value) is not k1.DatumRecord:
        raise ColdFailure(f"{label} is not a record")
    if type(value.fields) is not tuple or any(
        type(entry) is not tuple or len(entry) != 2 for entry in value.fields
    ):
        raise ColdFailure(f"{label} fields are not immutable ordinal pairs")
    if tuple(ordinal for ordinal, _child in value.fields) != ordinals:
        raise ColdFailure(f"{label} has another exact field sequence")
    return tuple(child for _ordinal, child in value.fields)


def _sequence(value: object, label: str) -> tuple[object, ...]:
    if type(value) is not k1.DatumSeq or type(value.values) is not tuple:
        raise ColdFailure(f"{label} is not an immutable sequence")
    if len(value.values) > 1 << 14:
        raise ColdFailure(f"{label} crosses the local sequence bound")
    return value.values


def _variant(value: object, cases: set[int], label: str) -> tuple[int, object]:
    if type(value) is not k1.DatumVariant or value.case not in cases:
        raise ColdFailure(f"{label} has another variant case")
    return value.case, value.payload


def _bytes(value: object, label: str) -> bytes:
    if type(value) is not k1.BytesValue or type(value.value) is not bytes:
        raise ColdFailure(f"{label} is not exact bytes")
    return value.value


def _walk_shape(root: object) -> tuple[int, int, int]:
    """Count nodes, edges, and maximum depth without recursive owner helpers."""

    queue: deque[tuple[object, int]] = deque([(root, 0)])
    nodes = 0
    edges = 0
    maximum_depth = 0
    while queue:
        value, depth = queue.popleft()
        nodes += 1
        maximum_depth = max(maximum_depth, depth)
        if nodes > 1 << 14 or depth > 384:
            raise ColdFailure("canonical datum exceeds the Foundation shape bound")
        children: tuple[object, ...] = ()
        if type(value) is k1.DatumSeq:
            children = _sequence(value, "nested sequence")
        elif type(value) is k1.DatumRecord:
            if type(value.fields) is not tuple:
                raise ColdFailure("nested record fields are mutable")
            ordinals = tuple(item[0] for item in value.fields)
            if ordinals != tuple(sorted(set(ordinals))):
                raise ColdFailure("nested record ordinals are not strict")
            children = tuple(item[1] for item in value.fields)
        elif type(value) is k1.DatumVariant:
            children = (value.payload,)
        elif type(value) not in (
            k1.Unit,
            k1.Nat,
            k1.IntValue,
            k1.BytesValue,
            k1.Symbol,
            bool,
        ):
            raise ColdFailure("cold walk encountered an unknown datum carrier")
        edges += len(children)
        if edges > 1 << 14:
            raise ColdFailure("canonical datum exceeds the Foundation edge bound")
        queue.extend((child, depth + 1) for child in children)
    return nodes, edges, maximum_depth


def inspect_core(profiled_body: bytes) -> dict[str, object]:
    if type(profiled_body) is not bytes or not profiled_body:
        raise ColdFailure("Core body is not nonempty bytes")
    try:
        outer = k1.decode_datum(profiled_body)
    except Exception as error:
        raise ColdFailure(f"strict Core decode failed: {error}") from error
    if k1.encode_datum(outer) != profiled_body:
        raise ColdFailure("Core body does not round-trip byte-identically")
    profile, core = _record(outer, (0, 1), "profiled Core")
    profile_reference = _bytes(profile, "Core profile reference")
    try:
        profile_id = k1.decode_content_reference(profile_reference)
    except Exception as error:
        raise ColdFailure(f"Core profile reference is malformed: {error}") from error
    if profile_id.subject_kind != k1.SEMANTIC_LANGUAGE_PROFILE_KIND:
        raise ColdFailure("Core profile reference has another subject kind")
    fields = _record(core, tuple(range(14)), "InteractiveCore")
    sequences = tuple(
        _sequence(field, f"InteractiveCore field {ordinal}")
        for ordinal, field in enumerate(fields)
    )
    effects: list[int] = []
    guards: list[int] = []
    for occurrence in sequences[13]:
        _scope, guard, effect = _record(occurrence, (0, 1, 2), "occurrence")
        guard_tag, _guard_payload = _variant(guard, {0, 1}, "guard")
        effect_tag, _effect_payload = _variant(effect, set(range(8)), "Core effect")
        guards.append(guard_tag)
        effects.append(effect_tag)
    field_names = (
        "used_modules",
        "public_inputs",
        "verifier_private_inputs",
        "constants",
        "derived_values",
        "scopes",
        "bindings",
        "challenges",
        "oracles",
        "checks",
        "claims",
        "reductions",
        "terminals",
        "occurrences",
    )
    structural_summary = tuple(
        [(name, len(sequence)) for name, sequence in zip(field_names, sequences)]
        + [("effect_tags", tuple(effects))]
    )
    nodes, edges, depth = _walk_shape(outer)
    return {
        "profile_reference": profile_reference,
        "profiled_body_sha256": hashlib.sha256(profiled_body).hexdigest(),
        "domain_body_sha256": hashlib.sha256(k1.encode_datum(core)).hexdigest(),
        "structural_summary": structural_summary,
        "guard_tags": tuple(guards),
        "datum_nodes": nodes,
        "datum_edges": edges,
        "datum_depth": depth,
    }


def inspect_fresh_protocol(profiled_body: bytes) -> dict[str, object]:
    if type(profiled_body) is not bytes or not profiled_body:
        raise ColdFailure("Protocol body is not nonempty bytes")
    try:
        outer = k1.decode_datum(profiled_body)
    except Exception as error:
        raise ColdFailure(f"strict Protocol decode failed: {error}") from error
    if k1.encode_datum(outer) != profiled_body:
        raise ColdFailure("Protocol body does not round-trip byte-identically")
    profile, protocol = _record(outer, (0, 1), "profiled Protocol")
    core, interpretation = _record(protocol, (0, 1), "Fresh Protocol")
    tag, payload = _variant(interpretation, {0}, "Fresh interpretation")
    if tag != 0 or type(payload) is not k1.Unit:
        raise ColdFailure("Fresh interpretation has a non-Unit payload")
    profile_reference = _bytes(profile, "Protocol profile reference")
    core_reference = _bytes(core, "Protocol Core reference")
    try:
        profile_id = k1.decode_content_reference(profile_reference)
        core_id = k1.decode_content_reference(core_reference)
    except Exception as error:
        raise ColdFailure(f"Protocol reference is malformed: {error}") from error
    if profile_id.subject_kind != k1.SEMANTIC_LANGUAGE_PROFILE_KIND:
        raise ColdFailure("Protocol profile reference has another kind")
    if core_id.subject_kind != "pir.interactive-core":
        raise ColdFailure("Protocol Core reference has another kind")
    nodes, edges, depth = _walk_shape(outer)
    return {
        "profile_reference": profile_reference,
        "core_reference": core_reference,
        "profiled_body_sha256": hashlib.sha256(profiled_body).hexdigest(),
        "interpretation_tag": 0,
        "datum_nodes": nodes,
        "datum_edges": edges,
        "datum_depth": depth,
    }
