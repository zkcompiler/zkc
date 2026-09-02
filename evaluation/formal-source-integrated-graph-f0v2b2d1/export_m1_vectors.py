#!/usr/bin/env python3
"""Export the D1 carriers for the M1 mechanized-kernel comparison.

The input side of this export contains only canonical bytes for the admitted
Core domain body and the used semantic-module declarations.  Nodes, edges,
orders, classes, sinks, and cones are expected outputs from D1's owner
derivation; the Lean consumer must not use them to construct its graph.
"""

from __future__ import annotations

import argparse
import importlib.util
import json
from pathlib import Path
import sys
from types import ModuleType
from typing import Any


HERE = Path(__file__).resolve().parent
MODEL = HERE / "model.py"


class ExportFailure(RuntimeError):
    """The D1 model no longer has the bounded shape this export expects."""


def _load(name: str, path: Path) -> ModuleType:
    if name in sys.modules:
        return sys.modules[name]
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:  # pragma: no cover - host failure
        raise ImportError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def _require(condition: bool, detail: str) -> None:
    if not condition:
        raise ExportFailure(detail)


def _node(value: tuple[int, ...]) -> list[int]:
    return list(value)


def _module_declarations(model: ModuleType, core: object, scenario: str) -> list[dict[str, Any]]:
    private_sink = scenario == "invalid-module-control-sink"
    semantics = model.module_semantics(private_sink)
    rows: dict[tuple[bytes, int], dict[str, Any]] = {}
    for occurrence in core.occurrences:
        effect = occurrence.effect
        if type(effect) is not model.ModuleEffectRef:
            continue
        ordinal = effect.declaration.local_ordinal
        _require(0 <= ordinal < len(semantics), "module declaration ordinal is outside the catalog")
        module_ref = effect.module.internal_reference()
        key = module_ref, ordinal
        rows[key] = {
            "module_ref_hex": module_ref.hex(),
            "ordinal": ordinal,
            "body_hex": model.k1.encode_datum(model._semantics_datum(semantics[ordinal])).hex(),
        }
    return [rows[key] for key in sorted(rows)]


def export() -> dict[str, Any]:
    model = _load("_zkc_d1_m1_export_model", MODEL)
    carriers: list[dict[str, Any]] = []
    for name, fixture in model.fixtures().items():
        admitted = model.admit_core(fixture.candidate, fixture.environment)
        _require(admitted.outcome == "Affirmative", f"D1 no longer admits {name}")
        core, scenario = model._retained_core(admitted.handle)
        _require(scenario == name, f"D1 scenario recognition drifted for {name}")
        _, evidence = model.derive_graph(core, scenario)
        carriers.append(
            {
                "carrier": name,
                "input": {
                    "core_domain_hex": model.k1.encode_datum(model.core_domain_datum(core)).hex(),
                    "module_declarations": _module_declarations(model, core, scenario),
                },
                "expected": {
                    "nodes": [_node(item) for item in evidence.nodes],
                    "edges": [[_node(source), _node(target)] for source, target in evidence.edges],
                    "topological": [_node(item) for item in evidence.topological],
                    "classes": [
                        [_node(item), evidence.classes[item]] for item in evidence.nodes
                    ],
                    "sinks": [_node(item) for item in evidence.sinks],
                    "acceptance_sinks": [_node(item) for item in evidence.acceptance_sinks],
                    "private_predecessors": [
                        _node(item) for item in evidence.private_predecessors
                    ],
                    "logical_cones": [
                        [oracle_ref, [_node(item) for item in evidence.logical_cones[oracle_ref]]]
                        for oracle_ref in sorted(evidence.logical_cones)
                    ],
                    "logical_intersections": [
                        [
                            oracle_ref,
                            [_node(item) for item in evidence.logical_intersections[oracle_ref]],
                        ]
                        for oracle_ref in sorted(evidence.logical_intersections)
                    ],
                    "eligible": evidence.eligible,
                },
            }
        )
    return {
        "source": "evaluation/formal-source-integrated-graph-f0v2b2d1",
        "input_boundary": (
            "canonical Core-domain and used semantic-module declaration bytes only; "
            "every graph table is an expected output"
        ),
        "carriers": carriers,
    }


def _scalar(value: Any) -> bool:
    return value is None or isinstance(value, (bool, int, float, str))


def _render(value: Any, indent: int) -> str:
    """Use the compact deterministic layout of the consuming M1 package."""

    pad = " " * indent
    inner = " " * (indent + 1)
    if isinstance(value, dict):
        if not value:
            return "{}"
        items = [
            f"{inner}{json.dumps(key)}: {_render(value[key], indent + 1)}"
            for key in sorted(value)
        ]
        return "{\n" + ",\n".join(items) + "\n" + pad + "}"
    if isinstance(value, list):
        if not value:
            return "[]"
        if all(_scalar(item) for item in value):
            return json.dumps(value, separators=(", ", ": "))
        items = [f"{inner}{_render(item, indent + 1)}" for item in value]
        return "[\n" + ",\n".join(items) + "\n" + pad + "]"
    return json.dumps(value)


def _dump(value: Any) -> str:
    rendered = _render(value, 0) + "\n"
    _require(json.loads(rendered) == value, "vector renderer is not faithful")
    return rendered


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    rendered = _dump(export())
    if args.check:
        if not args.out.is_file() or args.out.read_text(encoding="utf-8") != rendered:
            print(f"vector drift: {args.out}")
            return 1
        print(f"M1 vectors match {args.out}")
        return 0
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(rendered, encoding="utf-8")
    print(f"wrote {args.out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
