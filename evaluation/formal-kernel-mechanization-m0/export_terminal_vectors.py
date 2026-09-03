#!/usr/bin/env python3
"""Freeze normalized carriers for the mechanized Terminal-contract check.

The exporter intentionally does not import the historical synthetic-profile
models.  Those models collide with the real manifests on the migration branch.
Instead it reconstructs only the finite coordinates consumed by Section 10:
occurrence order, full structural guard identity, declaration backlinks,
compact guard terms, closed claim sources and consumers, and terminal requirements.  Source files
and predecessor findings are hash-pinned so this normalization cannot silently
outlive its evidence.
"""

from __future__ import annotations

import argparse
from copy import deepcopy
import hashlib
import json
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
OUT = HERE / "vectors" / "terminal-contract.json"
BASE_HEAD = "76f49ec1df3d9b5a241768da2fed8f5d46bd0799"
PROJECTION_EXPECTED = (
    ROOT
    / "evaluation/formal-source-terminal-owner-projections-f0v2b2c1b5b2"
    / "expected-findings.json"
)
INTEGRATED_EXPECTED = (
    ROOT / "evaluation/formal-source-integrated-graph-f0v2b2d1" / "expected-findings.json"
)
HOLDOUT_ADJUDICATION = (
    ROOT / "evaluation/formal-source-holdout-readjudication-f0v2c2" / "adjudication.json"
)

SOURCES = (
    "docs-next/pir/interactive-core.md",
    "docs-next/notes/semantic-revalidation-and-redesign/formal-assurance-research/"
    "f0-v2c-migration-owner-text.md",
    "evaluation/formal-source-terminal-owner-projections-f0v2b2c1b5b2/model.py",
    "evaluation/formal-source-terminal-owner-projections-f0v2b2c1b5b2/run.py",
    "evaluation/formal-source-terminal-owner-projections-f0v2b2c1b5b2/expected-findings.json",
    "evaluation/formal-source-integrated-graph-f0v2b2d1/model.py",
    "evaluation/formal-source-integrated-graph-f0v2b2d1/expected-findings.json",
    "evaluation/formal-source-holdout-readjudication-f0v2c2/adjudication.json",
    "evaluation/formal-source-holdout-readjudication-f0v2c2/expected-findings.json",
)


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _read_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def _predecessor_outcomes() -> tuple[dict[str, str], str, dict[str, str]]:
    projection = _read_json(PROJECTION_EXPECTED)
    projection_outcomes = {
        name: outcome for name, outcome, _code in projection["finding_codes"]
    }
    integrated = _read_json(INTEGRATED_EXPECTED)
    if integrated["aggregate"] != "F0V2B2D1-A-INTEGRATED-PCGRAPH-CLOSURE":
        raise ValueError("integrated predecessor is no longer affirmative")
    holdout = _read_json(HOLDOUT_ADJUDICATION)
    wanted = {
        "WHIR Construction 5.1 with a closed finite query plan",
        "WARPfold finite fold",
    }
    holdout_outcomes = {
        row["name"]: row["verdict"] for row in holdout["rows"] if row["name"] in wanted
    }
    if set(holdout_outcomes) != wanted:
        raise ValueError("representable holdout adjudications are not unique")
    return projection_outcomes, "Affirmative", holdout_outcomes


def _effect(kind: str, reference: int) -> dict[str, Any]:
    return {"kind": kind, "reference": reference}


def _occurrence(
    effect: dict[str, Any], guard: int | None = None, openings: tuple[int, ...] = ()
) -> dict[str, Any]:
    return {"openings_before": list(openings), "guard_atom": guard, "effect": effect}


def _output(occurrence: int, output: int = 0) -> dict[str, Any]:
    return {"kind": "occurrence-output", "occurrence": occurrence, "output": output}


def _other(coordinate: int) -> dict[str, Any]:
    return {"kind": "other", "coordinate": coordinate}


def _identity(input_ordinal: int = 0) -> dict[str, Any]:
    return {"kind": "identity", "input": input_ordinal}


def _conjunction(*inputs: int) -> dict[str, Any]:
    return {"kind": "conjunction", "inputs": list(inputs)}


def _contradiction(input_ordinal: int = 0) -> dict[str, Any]:
    return {"kind": "contradiction", "input": input_ordinal}


def _positions(carrier: dict[str, Any], kind: str, reference: int) -> list[int]:
    return [
        index
        for index, occurrence in enumerate(carrier["schedule"])
        if occurrence["effect"] == _effect(kind, reference)
    ]


def _claims(carrier: dict[str, Any]) -> list[dict[str, Any]]:
    claims: dict[int, dict[str, Any]] = {
        reference: {
            "reference": reference,
            "source": {"kind": "initial"},
            "linear_consumers": [],
        }
        for reference in carrier.get("initial_claims", [])
    }
    reductions = carrier.get("reductions", [])
    for reference, reduction in enumerate(reductions):
        positions = _positions(carrier, "reduction", reference)
        source = positions[0] if len(positions) == 1 else len(carrier["schedule"]) + reference + 1
        for output in reduction["outputs"]:
            claims[output] = {
                "reference": output,
                "source": {"kind": "occurrence", "occurrence": source},
                "linear_consumers": [],
            }
    linear = set(carrier.get("linear_claims", []))
    for occurrence, row in enumerate(carrier.get("schedule", [])):
        effect = row["effect"]
        if effect["kind"] != "reduction" or not 0 <= effect["reference"] < len(reductions):
            continue
        for input_claim in reductions[effect["reference"]]["inputs"]:
            if input_claim in linear and input_claim in claims:
                claims[input_claim]["linear_consumers"].append(occurrence)
    return [claims[reference] for reference in sorted(claims)]


def _close_carrier(carrier: dict[str, Any]) -> dict[str, Any]:
    if not carrier.get("representable", False):
        return carrier
    for terminal in carrier["terminals"]:
        terminal.setdefault(
            "guard_input_is_boolean", [True] * len(terminal["guard_inputs"])
        )
    carrier["claims"] = _claims(carrier)
    return carrier


def _terminal_projection() -> dict[str, Any]:
    accept_atom, abort_atom = 10, 11
    return {
        "name": "terminal-projection-positive",
        "family": "terminal-projection",
        "source_precision": "exact normalized coordinates",
        "predecessor_outcome": "Affirmative",
        "representable": True,
        "initial_claims": [0],
        "linear_claims": [0],
        "reductions": [
            {"inputs": [0], "outputs": [1]},
            {"inputs": [0], "outputs": [2]},
        ],
        "schedule": [
            _occurrence(_effect("check", 0), openings=(0,)),
            _occurrence(_effect("reduction", 0), accept_atom),
            _occurrence(_effect("terminal", 0), accept_atom),
            _occurrence(_effect("reduction", 1)),
            _occurrence(_effect("terminal", 1), abort_atom),
            _occurrence(_effect("terminal", 2)),
        ],
        "terminals": [
            {
                "reference": 0,
                "guard_term": _conjunction(0, 1),
                "guard_inputs": [_output(0), _other(1)],
                "required_checks": [0],
                "required_reductions": [0],
                "terminal_claims": [1],
            },
            {
                "reference": 1,
                "guard_term": _identity(0),
                "guard_inputs": [_other(2)],
                "required_checks": [],
                "required_reductions": [1],
                "terminal_claims": [2],
            },
            {
                "reference": 2,
                "guard_term": None,
                "guard_inputs": [],
                "required_checks": [],
                "required_reductions": [1],
                "terminal_claims": [2],
            },
        ],
    }


def _terminal_projection_mutations() -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []

    def mutate(name: str, action: Any, predecessor: str = "Refused") -> None:
        carrier = deepcopy(_terminal_projection())
        carrier["name"] = f"terminal-projection/{name}"
        carrier["predecessor_outcome"] = predecessor
        action(carrier)
        rows.append(carrier)

    mutate("required-check-reference", lambda c: c["terminals"][0].update(required_checks=[9]))
    mutate("required-check-duplicate", lambda c: c["terminals"][0].update(required_checks=[0, 0]))
    mutate(
        "required-reduction-reference",
        lambda c: c["terminals"][0].update(required_reductions=[9]),
    )
    mutate(
        "required-reduction-duplicate",
        lambda c: c["terminals"][0].update(required_reductions=[0, 0]),
    )
    mutate(
        "required-reduction-unsorted",
        lambda c: c["terminals"][0].update(required_reductions=[1, 0]),
    )
    mutate("terminal-claim-omitted", lambda c: c["terminals"][0].update(terminal_claims=[]))
    mutate("terminal-claim-wrong", lambda c: c["terminals"][0].update(terminal_claims=[2]))
    mutate(
        "terminal-claim-duplicate",
        lambda c: c["terminals"][0].update(terminal_claims=[1, 1]),
    )

    def guard_final(c: dict[str, Any]) -> None:
        c["schedule"][5]["guard_atom"] = 50
        c["terminals"][2]["guard_term"] = _identity(0)
        c["terminals"][2]["guard_inputs"] = [_other(0)]

    mutate("final-fallback-guarded", guard_final)

    def omit_check(c: dict[str, Any]) -> None:
        for index in (1, 2):
            c["schedule"][index]["guard_atom"] = 50
        c["terminals"][0]["guard_term"] = _identity(0)
        c["terminals"][0]["guard_inputs"] = [_other(1)]

    mutate("accept-guard-omits-check", omit_check)
    mutate("check-not-guaranteed", lambda c: c["schedule"][0].update(guard_atom=50))

    def reduction_after(c: dict[str, Any]) -> None:
        c["schedule"][1], c["schedule"][2] = c["schedule"][2], c["schedule"][1]

    mutate("required-reduction-after-terminal", reduction_after)

    def overlap(c: dict[str, Any]) -> None:
        moved = c["schedule"].pop(3)
        c["schedule"].insert(2, moved)

    mutate("linear-consumer-overlap", overlap)
    mutate("missing-terminal-backlink", lambda c: c["schedule"].pop())
    mutate(
        "duplicate-terminal-backlink",
        lambda c: c["schedule"].append(_occurrence(_effect("terminal", 2))),
    )

    for name, predecessor, reason in (
        (
            "check-abi",
            "KindMismatch",
            "Check function typing is decided by Core admission step 4, outside the Terminal contract.",
        ),
        (
            "claim-output-ssa",
            "Refused",
            "Claim-source and Reduction-output bijection is decided before claim-liveness transfer.",
        ),
    ):
        rows.append(
            {
                "name": f"terminal-projection/{name}",
                "family": "terminal-projection",
                "source_precision": "outside the normalized Terminal surface",
                "predecessor_outcome": predecessor,
                "representable": False,
                "cannot_answer": reason,
            }
        )
    return rows


def _integrated(name: str) -> dict[str, Any]:
    logical = name == "logical-reject-preemption"
    schedule = [_occurrence(_effect("other", index), openings=(0, 1) if index == 0 else ())
                for index in range(17)]
    schedule.extend(
        (
            _occurrence(_effect("check", 0)),
            _occurrence(_effect("reduction", 0)),
            _occurrence(_effect("reduction", 1)),
        )
    )
    if logical:
        schedule.extend(
            (
                _occurrence(_effect("terminal", 0), 300),
                _occurrence(_effect("terminal", 1), 201),
                _occurrence(_effect("terminal", 2)),
            )
        )
        terminals = [
            {
                "reference": 0,
                "guard_term": _identity(0),
                "guard_inputs": [_output(13)],
                "required_checks": [],
                "required_reductions": [],
                "terminal_claims": [],
            },
            {
                "reference": 1,
                "guard_term": _identity(0),
                "guard_inputs": [_other(2)],
                "required_checks": [],
                "required_reductions": [1],
                "terminal_claims": [2],
            },
            {
                "reference": 2,
                "guard_term": None,
                "guard_inputs": [],
                "required_checks": [],
                "required_reductions": [0, 1],
                "terminal_claims": [1, 2],
            },
        ]
    else:
        schedule.extend(
            (
                _occurrence(_effect("terminal", 0), 200),
                _occurrence(_effect("terminal", 1), 201),
                _occurrence(_effect("terminal", 2)),
            )
        )
        terminals = [
            {
                "reference": 0,
                "guard_term": _conjunction(0, 1),
                "guard_inputs": [_output(17), _other(1)],
                "required_checks": [0],
                "required_reductions": [0, 1],
                "terminal_claims": [1, 2],
            },
            {
                "reference": 1,
                "guard_term": _identity(0),
                "guard_inputs": [_other(2)],
                "required_checks": [],
                "required_reductions": [1],
                "terminal_claims": [2],
            },
            {
                "reference": 2,
                "guard_term": None,
                "guard_inputs": [],
                "required_checks": [],
                "required_reductions": [1],
                "terminal_claims": [2],
            },
        ]
    return {
        "name": name,
        "family": "integrated-graph",
        "source_precision": "exact normalized coordinates",
        "predecessor_outcome": "Affirmative",
        "representable": True,
        "expected_terminal_outcome": "Refused",
        "expected_difference": (
            "The integrated graph package admitted graph construction without running the repaired "
            "Terminal claim-closure law; reusable initial claim 0 remains live."
        ),
        "initial_claims": [0],
        "linear_claims": [],
        "reductions": [
            {"inputs": [0], "outputs": [1]},
            {"inputs": [0], "outputs": [2]},
        ],
        "schedule": schedule,
        "terminals": terminals,
    }


def _warpfold_shape() -> dict[str, Any]:
    return {
        "name": "holdout/warpfold-finite-terminal-shape",
        "family": "holdout-shape",
        "source_precision": "shape only; no selected source-profile coordinates",
        "predecessor_outcome": "fits",
        "representable": True,
        "expected_terminal_outcome": "Affirmative",
        "initial_claims": [],
        "linear_claims": [],
        "reductions": [],
        "schedule": [
            _occurrence(_effect("check", 0), openings=(0,)),
            _occurrence(_effect("terminal", 0), 900),
            _occurrence(_effect("terminal", 1)),
        ],
        "terminals": [
            {
                "reference": 0,
                "guard_term": _identity(0),
                "guard_inputs": [_output(0)],
                "required_checks": [0],
                "required_reductions": [],
                "terminal_claims": [],
            },
            {
                "reference": 1,
                "guard_term": None,
                "guard_inputs": [],
                "required_checks": [],
                "required_reductions": [],
                "terminal_claims": [],
            },
        ],
    }


def _whir_shape() -> dict[str, Any]:
    accepting_guard = 901
    return {
        "name": "holdout/whir-finite-terminal-shape",
        "family": "holdout-shape",
        "source_precision": "exact normalized terminal coordinates from the frozen adjudication",
        "predecessor_outcome": "fits",
        "representable": True,
        "expected_terminal_outcome": "Affirmative",
        "initial_claims": [0],
        "linear_claims": [0, 1],
        "reductions": [
            {"inputs": [0], "outputs": [1]},
            {"inputs": [1], "outputs": []},
        ],
        "schedule": [
            *(
                _occurrence(_effect("check", reference), openings=(0,) if reference == 0 else ())
                for reference in range(5)
            ),
            _occurrence(_effect("reduction", 0), accepting_guard),
            _occurrence(_effect("reduction", 1), accepting_guard),
            _occurrence(_effect("terminal", 0), accepting_guard),
            _occurrence(_effect("terminal", 1)),
        ],
        "terminals": [
            {
                "reference": 0,
                "guard_term": _conjunction(0, 1, 2, 3, 4),
                "guard_inputs": [_output(reference) for reference in range(5)],
                "required_checks": [0, 1, 2, 3, 4],
                "required_reductions": [0, 1],
                "terminal_claims": [],
            },
            {
                "reference": 1,
                "guard_term": None,
                "guard_inputs": [],
                "required_checks": [],
                "required_reductions": [],
                "terminal_claims": [0],
            },
        ],
    }


def _closed_contract_controls() -> list[dict[str, Any]]:
    unknown = deepcopy(_terminal_projection())
    unknown.update(
        name="closed-contract/unknown-claim-status",
        family="closed-contract-control",
        predecessor_outcome="not-applicable",
        expected_terminal_outcome="Refused",
    )
    unknown["schedule"][2]["guard_atom"] = 12

    contradiction = {
        "name": "closed-contract/contradictory-zero-check-guard",
        "family": "closed-contract-control",
        "source_precision": "package-authored law control",
        "predecessor_outcome": "not-applicable",
        "representable": True,
        "expected_terminal_outcome": "Refused",
        "initial_claims": [],
        "linear_claims": [],
        "reductions": [],
        "schedule": [
            _occurrence(_effect("terminal", 0), 700),
            _occurrence(_effect("terminal", 1)),
        ],
        "terminals": [
            {
                "reference": 0,
                "guard_term": _contradiction(0),
                "guard_inputs": [_other(0)],
                "required_checks": [],
                "required_reductions": [],
                "terminal_claims": [],
            },
            {
                "reference": 1,
                "guard_term": None,
                "guard_inputs": [],
                "required_checks": [],
                "required_reductions": [],
                "terminal_claims": [],
            },
        ],
    }

    non_boolean = {
        "name": "closed-contract/non-boolean-guard-input",
        "family": "closed-contract-control",
        "source_precision": "package-authored law control",
        "predecessor_outcome": "not-applicable",
        "representable": True,
        "expected_terminal_outcome": "Refused",
        "initial_claims": [],
        "linear_claims": [],
        "reductions": [],
        "schedule": [
            _occurrence(_effect("check", 0)),
            _occurrence(_effect("terminal", 0), 701),
            _occurrence(_effect("terminal", 1)),
        ],
        "terminals": [
            {
                "reference": 0,
                "guard_term": _identity(0),
                "guard_inputs": [_output(0)],
                "guard_input_is_boolean": [False],
                "required_checks": [0],
                "required_reductions": [],
                "terminal_claims": [],
            },
            {
                "reference": 1,
                "guard_term": None,
                "guard_inputs": [],
                "required_checks": [],
                "required_reductions": [],
                "terminal_claims": [],
            },
        ],
    }

    impossible_region = {
        "name": "closed-contract/impossible-terminal-region",
        "family": "closed-contract-control",
        "source_precision": "package-authored law control",
        "predecessor_outcome": "not-applicable",
        "representable": True,
        "expected_terminal_outcome": "Refused",
        "initial_claims": [],
        "linear_claims": [],
        "reductions": [],
        "schedule": [
            _occurrence(_effect("terminal", 0), 710),
            _occurrence(_effect("terminal", 1), 710),
            _occurrence(_effect("terminal", 2)),
        ],
        "terminals": [
            {
                "reference": 0,
                "guard_term": {"kind": "true"},
                "guard_inputs": [],
                "required_checks": [],
                "required_reductions": [],
                "terminal_claims": [],
            },
            {
                "reference": 1,
                "guard_term": {"kind": "true"},
                "guard_inputs": [],
                "required_checks": [],
                "required_reductions": [],
                "terminal_claims": [],
            },
            {
                "reference": 2,
                "guard_term": None,
                "guard_inputs": [],
                "required_checks": [],
                "required_reductions": [],
                "terminal_claims": [],
            },
        ],
    }
    return [unknown, contradiction, non_boolean, impossible_region]


def export() -> dict[str, Any]:
    projection_outcomes, integrated_outcome, holdout_outcomes = _predecessor_outcomes()
    carriers = [_terminal_projection(), *_terminal_projection_mutations()]
    carriers.extend(
        _integrated(name)
        for name in (
            "integrated-baseline",
            "private-verifier-output-sink",
            "invalid-module-control-sink",
            "history-challenge-condition",
            "logical-reject-preemption",
        )
    )
    carriers.extend((_warpfold_shape(), _whir_shape(), *_closed_contract_controls()))
    for carrier in carriers:
        if carrier["family"] == "terminal-projection":
            finding = (
                "candidate-core-admission"
                if carrier["name"] == "terminal-projection-positive"
                else carrier["name"].removeprefix("terminal-projection/")
            )
            predecessor_outcome = projection_outcomes.get(finding)
            if predecessor_outcome is None:
                raise ValueError(f"missing terminal-projection predecessor finding {finding}")
            if predecessor_outcome != carrier["predecessor_outcome"]:
                raise ValueError(f"terminal-projection outcome drifted for {finding}")
            carrier["predecessor_outcome"] = predecessor_outcome
        elif carrier["family"] == "integrated-graph":
            carrier["predecessor_outcome"] = integrated_outcome
        elif carrier["family"] == "holdout-shape":
            source_name = (
                "WARPfold finite fold"
                if "warpfold" in carrier["name"]
                else "WHIR Construction 5.1 with a closed finite query plan"
            )
            carrier["predecessor_outcome"] = holdout_outcomes[source_name]
        _close_carrier(carrier)
    return {
        "base_head": BASE_HEAD,
        "owner_lines": {
            "attempt_guards": [1427, 1442],
            "must_env": [1444, 1478],
            "forward_state": [1480, 1503],
            "terminal_contract": [1505, 1519],
        },
        "source_pins": {source: _sha256(ROOT / source) for source in SOURCES},
        "carriers": carriers,
        "unrepresented_holdouts": [
            {
                "name": "Circle STARKs",
                "reason": "The holdout record gives a terminal shape but no exact Check, Reduction, Claim, guard-input, or occurrence coordinates.",
            },
            {
                "name": "virtual multiparty Sumcheck",
                "reason": "The holdout record gives a terminal shape but no exact finite carrier coordinates.",
            },
            {
                "name": "interactive Galois-ring protocol",
                "reason": "The holdout record gives a terminal shape but no exact finite carrier coordinates.",
            },
            {
                "name": "WARPfold broad cross-system application",
                "reason": "The holdout already breaks at cross-execution state and imported challenge authority before a Terminal carrier exists.",
            },
        ],
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
            print("terminal-contract vector drift")
            return 1
        print("terminal-contract vectors match the normalized source reconstruction")
        return 0
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(text, encoding="utf-8")
    print(f"wrote {args.out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
