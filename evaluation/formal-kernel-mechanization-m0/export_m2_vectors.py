#!/usr/bin/env python3
"""Export the exact M2 portable-term and R1B evaluation vectors.

The two algorithms come from the F1R1B source model.  Their complete K1
preimages, direct primitive references, and all 81 finite Schnorr inputs plus
the two Boolean guard inputs are regenerated at check time.  The K1 evaluator
is the producer of completion bytes and charge records.  This export does not
call those rows an independent oracle: K1's independent oracle has no term
evaluation operation, and that absence is recorded in ``oracle_inventory``.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
from types import ModuleType
from typing import Any


ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
OUT = HERE / "vectors" / "m2-term-calculus.json"
F1 = ROOT / "evaluation/formal-source-target-core-f1r1b/reference_model.py"
ORACLE = ROOT / "evaluation/k1-executable-foundations/oracle/cases"


class ExportError(RuntimeError):
    """A source model no longer yields the frozen M2 export."""


def _require(condition: bool, detail: str) -> None:
    if not condition:
        raise ExportError(detail)


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


def _transport(k1: ModuleType, value: Any) -> Any:
    if type(value) is k1.Unit:
        return {"tag": "unit"}
    if type(value) is bool:
        return {"tag": "bool", "value": value}
    if type(value) is k1.Nat:
        return {"tag": "nat", "value": str(value.value)}
    if type(value) is k1.IntValue:
        return {"tag": "int", "value": str(value.value)}
    if type(value) is k1.BytesValue:
        return {"tag": "bytes", "value": value.value.hex()}
    if type(value) is k1.Symbol:
        return {"tag": "symbol", "value": value.value}
    if type(value) is k1.DatumSeq:
        return {"tag": "seq", "items": [_transport(k1, item) for item in value.values]}
    if type(value) is k1.DatumRecord:
        return {
            "tag": "record",
            "fields": [
                {"ordinal": str(ordinal), "value": _transport(k1, child)}
                for ordinal, child in value.fields
            ],
        }
    if type(value) is k1.DatumVariant:
        return {
            "tag": "variant",
            "case": str(value.case),
            "value": _transport(k1, value.payload),
        }
    raise ExportError(f"unsupported datum carrier {type(value)!r}")


def _result(k1: ModuleType, algorithm: Any, values: tuple[Any, ...], modules: Any) -> dict[str, Any]:
    inputs = tuple(
        k1.admit_value(value_type, k1.Nat(value) if type(value) is int else value)
        for value_type, value in zip(algorithm.inputs, values)
    )
    result = k1.Evaluator().evaluate(algorithm, inputs, modules=modules)
    _require(result.outcome is k1.Outcome.COMPLETED, f"K1 did not complete on {values}: {result}")
    completion = k1.completion_datum(algorithm.function_type, result.completion)
    body = k1.encode_datum(completion)
    return {
        "inputs": [_transport(k1, item.datum) for item in inputs],
        "expected_completion": _transport(k1, completion),
        "expected_completion_hex": body.hex(),
        "expected_charge": {
            "steps": result.charge.steps,
            "iteration_items": result.charge.iteration_items,
            "primitive_work": result.charge.primitive_work,
            "result_bytes": result.charge.result_bytes,
        },
    }


def _algorithm(k1: ModuleType, name: str, algorithm: Any) -> dict[str, Any]:
    preimage = k1.algorithm_preimage(algorithm)
    dependencies = k1.direct_primitive_dependencies(algorithm.term)
    return {
        "name": name,
        "diagnostic_label": algorithm.algorithm_kind.value,
        "identity_digest": algorithm.identity.digest.hex(),
        "preimage_hex": preimage.hex(),
        "preimage_length": len(preimage),
        "preimage_sha256": hashlib.sha256(preimage).hexdigest(),
        "maximum_completion_bytes": k1.maximum_completion_size(algorithm.function_type),
        "primitive_references": [
            {
                "hex": k1.encode_datum(reference.datum()).hex(),
                "value": _transport(k1, reference.datum()),
            }
            for reference in dependencies
        ],
    }


def export() -> dict[str, Any]:
    f1 = _load("_zkc_m2_f1r1b", F1)
    k1 = f1.k1
    check = f1.finite_schnorr_algorithm()
    guard = f1.boolean_identity_algorithm()

    requests = [
        json.loads(line)
        for line in (ORACLE / "requests.jsonl").read_text(encoding="utf-8").splitlines()
        if line
    ]
    operations = sorted({row["op"] for row in requests})
    evaluation_rows = [row for row in requests if row["op"] in ("evaluate", "evaluate_encoded")]
    _require(not evaluation_rows, "K1 oracle unexpectedly acquired term-evaluation vectors")

    check_cases: list[dict[str, Any]] = []
    for y in range(3):
        for commitment in range(3):
            for challenge in range(3):
                for response in range(3):
                    row = _result(
                        k1,
                        check,
                        (y, commitment, challenge, response),
                        k1.FIXTURE_MODULE_PREIMAGES,
                    )
                    row["name"] = f"check/{y}-{commitment}-{challenge}-{response}"
                    row["closed_form"] = response == (commitment + challenge * y) % 3
                    check_cases.append(row)
    guard_cases = []
    for value in (False, True):
        row = _result(k1, guard, (value,), {})
        row["name"] = f"guard/{str(value).lower()}"
        guard_cases.append(row)

    return {
        "source": "evaluation/formal-source-target-core-f1r1b/reference_model.py",
        "oracle_inventory": {
            "requests": len(requests),
            "operations": operations,
            "term_evaluation_requests": len(evaluation_rows),
            "requests_sha256": hashlib.sha256((ORACLE / "requests.jsonl").read_bytes()).hexdigest(),
            "expected_sha256": hashlib.sha256((ORACLE / "expected.jsonl").read_bytes()).hexdigest(),
        },
        "algorithms": {
            "check": _algorithm(k1, "check", check),
            "guard": _algorithm(k1, "guard", guard),
        },
        "check_cases": check_cases,
        "guard_cases": guard_cases,
    }


def _dump(value: Any) -> str:
    return json.dumps(value, indent=2, sort_keys=True) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, default=OUT)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    text = _dump(export())
    if args.check:
        if not OUT.is_file() or OUT.read_text(encoding="utf-8") != text:
            print("M2 vector drift")
            return 1
        print("M2 term-calculus vector matches the regenerated export")
        return 0
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(text, encoding="utf-8")
    print(f"wrote {args.out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
