#!/usr/bin/env python3
"""Independent checker for the provider-observable ledger.

The checker shares no code with ``generator.py``.  It obtains the owner-side
facts it needs, the six view values and the complete active-leaf manifests of
the admitted subject, by loading the F0-V2B1 clean-room path
(``independent.py``) as an owner-side oracle.  It then checks a ledger and the
Lean text it describes for:

- totality: every Core occurrence and every Terminal has an emitted construct;
- injectivity: no two constructs claim one source coordinate;
- coordinate validity: every claimed, consulted, or naming coordinate is an
  active leaf of the six views, and a construct claims only a leaf whose
  boundary can determine a construct of its kind;
- marker consistency: the Lean text carries exactly the ledger's constructs,
  once each, at the recorded lines and in schedule order;
- Fresh realization: the Challenge occurrence is a sample from the declared
  public-coin law parameter, not a constant or a transcript function; and
- the exact enumeration of every typed ``no_source_coordinate`` entry.

A passing ledger is structural evidence about the ledger; the enumerated gaps
are the audit result.  Nothing here interprets the Lean text semantically or
establishes provider correspondence.
"""

from __future__ import annotations

import argparse
import copy
import importlib.util
import json
from pathlib import Path
import re
import sys
from types import ModuleType
from typing import Any


ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
B1_COLD = ROOT / "evaluation/formal-source-view-bodies-f0v2b1/independent.py"
MARKER = re.compile(r"-- \[f2o0:([A-Za-z0-9_.\-]+)\]")

LEDGER_FORMAT = "zkc.formal-provider-observables-f2o0.ledger.v0"
EFFECT_CASES = {0: "ProverMessage", 2: "Challenge", 3: "InvokeCheck", 5: "ReachTerminal"}
VERDICT_CASES = {0: "accept", 1: "reject", 2: "abort"}
INTERPRETATION_CASES = {0: "Fresh"}
GAP_ONLY_KINDS = frozenset(
    (
        "distribution",
        "denotation",
        "outcome-map",
        "relation",
        "honest-strategy",
        "private-type",
    )
)
GAP_CLASSES = frozenset(
    (
        "operational-distribution",
        "operational-denotation",
        "operational-outcome-map",
        "property-premise",
    )
)
SOURCED_KINDS: dict[str, frozenset[str]] = {
    "subject-identity": frozenset(
        ("canonical-body:core-id-body-v0", "canonical-body:protocol-id-body-v0")
    ),
    "value-carrier": frozenset(("canonical-body:value-type-body-v0",)),
    "prover-read": frozenset(
        (
            "canonical-body:public-input-ref-body-v0",
            "canonical-body:binding-ref-body-v0",
            "canonical-body:occurrence-ref-body-v0",
            "canonical-body:decision-ref-body-v0",
        )
    ),
    "prover-decision": frozenset(("canonical-body:decision-ref-body-v0",)),
    "strategy-parameter": frozenset(("exact-profile-law:core-admission-v0",)),
    "terminal-verdict": frozenset(("unit",)),
    "challenge-interpretation": frozenset(("unit",)),
    "public-input": frozenset(("canonical-body:value-ref-body-v0",)),
    "occurrence-step": frozenset(
        (
            "canonical-body:module-declaration-ref-body-v0",
            "canonical-body:challenge-ref-body-v0",
            "canonical-body:check-ref-body-v0",
            "canonical-body:terminal-ref-body-v0",
        )
    ),
    "provider-type-parameter": frozenset(
        ("canonical-body:value-type-body-v0", "unit")
    ),
}
RULE_ORDER = (
    "F2O0-R-LEDGER-SHAPE",
    "F2O0-R-GAP-UNTYPED",
    "F2O0-R-CONSTRUCT-UNSOURCED",
    "F2O0-R-COORDINATE-UNKNOWN",
    "F2O0-R-COORDINATE-ALIAS",
    "F2O0-R-INVENTED-OBSERVABLE",
    "F2O0-R-MARKER-MISSING",
    "F2O0-R-MARKER-UNLEDGERED",
    "F2O0-R-MARKER-DUPLICATE",
    "F2O0-R-MARKER-LINE",
    "F2O0-R-VERDICT-MISMATCH",
    "F2O0-R-EFFECT-MISMATCH",
    "F2O0-R-TERMINAL-UNCOVERED",
    "F2O0-R-OCCURRENCE-UNCOVERED",
    "F2O0-R-SCHEDULE-ORDER",
    "F2O0-R-CHALLENGE-NOT-FRESH",
)
PASS_CODE = "F2O0-A-LEDGER-CHECKED"
AUDIT_CLOSED = ("Affirmative", "F2O0-A-OBSERVABLES-CLOSED")
AUDIT_MISSING = ("CannotAnswer", "F2O0-C-MISSING-OPERATIONAL-OBSERVABLE")


class CheckerError(ValueError):
    """The checker cannot obtain its owner-side facts."""


def _load_module(name: str, path: Path) -> ModuleType:
    if name in sys.modules:
        return sys.modules[name]
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:  # pragma: no cover - host failure
        raise ImportError(f"cannot load module at {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def _canonical(value: Any) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"))


def _path_key(path: list[dict[str, Any]]) -> tuple[tuple[str, int], ...]:
    return tuple((step["step"], step["ordinal"]) for step in path)


def owner_facts() -> dict[str, Any]:
    """Load the B1 clean-room path and read the owner-side facts."""

    cold = _load_module("_zkc_f2o0_checker_b1_cold", B1_COLD)
    core, protocol = cold._admit()
    candidate = cold.build_candidate(core, protocol)
    values = candidate["values"]
    manifests = candidate["requested_manifests"]
    k1 = cold.owner.k1

    def nat(leaf: Any) -> int:
        datum = k1.decode_datum(bytes.fromhex(leaf["body"]))
        if type(datum) is not k1.Nat:
            raise CheckerError("owner ordinal leaf is not a natural datum")
        return datum.value

    effect_view = values["EffectView"]
    occurrences: list[dict[str, Any]] = []
    for ordinal, row in enumerate(effect_view[1]):
        case = row[3]["case"]
        if case not in EFFECT_CASES:
            raise CheckerError("owner effect case is outside the finite slice")
        entry = {"ordinal": ordinal, "effect": EFFECT_CASES[case], "case": case}
        if case != 0:
            entry["target"] = nat(row[3]["value"])
        occurrences.append(entry)
    terminals = []
    for index, row in enumerate(effect_view[6]):
        terminals.append(
            {
                "terminal": nat(row[0]),
                "row": index,
                "verdict_case": row[1]["case"],
                "verdict": VERDICT_CASES[row[1]["case"]],
                "occurrence": nat(row[5]),
            }
        )
    execution_view = values["ExecutionView"]
    interpretation_case = execution_view[2]["case"]
    coordinates: dict[str, dict[tuple[tuple[str, int], ...], str]] = {}
    universe: set[str] = set()
    for view, entries in manifests.items():
        table: dict[tuple[tuple[str, int], ...], str] = {}
        for coordinate in entries:
            key = _path_key(coordinate["path"])
            table[key] = _canonical(coordinate)
            universe.add(_canonical(coordinate))
        coordinates[view] = table
    return {
        "core_id": core.core_id.carrier(),
        "protocol_id": protocol.protocol_id.carrier(),
        "source_digest": candidate["source_digest"],
        "manifests": manifests,
        "universe": universe,
        "coordinate_tables": coordinates,
        "occurrences": occurrences,
        "terminals": terminals,
        "decisions": len(values["StrategyDecisionView"][1]),
        "reads": len(values["StrategyDecisionView"][3]),
        "legal_moves": len(values["StrategyDecisionView"][4]),
        "challenges": len(values["PublicCoinView"][4]),
        "resolvers": len(execution_view[4]),
        "interpretation_case": interpretation_case,
        "interpretation": INTERPRETATION_CASES.get(interpretation_case),
        "leaf_count": sum(len(entries) for entries in manifests.values()),
    }


def _boundary_key(boundary: dict[str, Any]) -> str:
    kind = boundary.get("kind")
    if kind == "canonical-body":
        return f"canonical-body:{boundary.get('compiler')}"
    if kind == "exact-profile-law":
        return f"exact-profile-law:{boundary.get('law')}"
    return str(kind)


class _Report:
    def __init__(self) -> None:
        self.failures: list[dict[str, str]] = []

    def fail(self, code: str, detail: str) -> None:
        self.failures.append({"code": code, "detail": detail})

    def ordered(self) -> list[dict[str, str]]:
        rank = {code: index for index, code in enumerate(RULE_ORDER)}
        return sorted(self.failures, key=lambda item: (rank[item["code"]], item["detail"]))


def check(ledger: Any, lean_text: str, facts: dict[str, Any]) -> dict[str, Any]:
    report = _Report()
    result: dict[str, Any] = {
        "outcome": "Refused",
        "code": None,
        "failures": [],
        "constructs": 0,
        "sourced": 0,
        "gaps": [],
        "coverage": {},
        "audit": {"outcome": None, "code": None},
    }

    # Rule: ledger shape.
    if (
        type(ledger) is not dict
        or ledger.get("format") != LEDGER_FORMAT
        or type(ledger.get("constructs")) is not list
        or not ledger["constructs"]
        or type(ledger.get("subject")) is not dict
    ):
        report.fail("F2O0-R-LEDGER-SHAPE", "ledger root is not the expected record")
        return _finish(result, report)
    subject = ledger["subject"]
    if (
        subject.get("core_id") != facts["core_id"]
        or subject.get("protocol_id") != facts["protocol_id"]
        or subject.get("view_source_digest") != facts["source_digest"]
    ):
        report.fail("F2O0-R-LEDGER-SHAPE", "ledger names another subject or view source")
    constructs: list[dict[str, Any]] = []
    seen_ids: set[str] = set()
    for index, entry in enumerate(ledger["constructs"]):
        if (
            type(entry) is not dict
            or type(entry.get("id")) is not str
            or type(entry.get("kind")) is not str
            or type(entry.get("lean")) is not dict
            or type(entry.get("source")) is not dict
            or type(entry.get("consulted")) is not list
        ):
            report.fail("F2O0-R-LEDGER-SHAPE", f"construct {index} is malformed")
            continue
        if entry["id"] in seen_ids:
            report.fail("F2O0-R-LEDGER-SHAPE", f"construct id repeats: {entry['id']}")
            continue
        seen_ids.add(entry["id"])
        constructs.append(entry)
    if report.failures:
        return _finish(result, report)
    result["constructs"] = len(constructs)
    by_id = {entry["id"]: entry for entry in constructs}

    # Rules: gap typing and sourcing.
    sourced: dict[str, dict[str, Any]] = {}
    gaps: list[dict[str, Any]] = []
    defective: set[str] = set()
    for entry in constructs:
        source = entry["source"]
        has_coordinate = "coordinate" in source
        has_gap = "no_source_coordinate" in source
        if has_coordinate == has_gap or set(source) - {"coordinate", "no_source_coordinate"}:
            report.fail(
                "F2O0-R-CONSTRUCT-UNSOURCED",
                f"{entry['id']} has neither exactly one coordinate nor one typed gap",
            )
            defective.add(entry["id"])
            continue
        if has_gap:
            gap = source["no_source_coordinate"]
            if (
                type(gap) is not dict
                or gap.get("class") not in GAP_CLASSES
                or type(gap.get("reason")) is not str
                or not gap["reason"].strip()
                or type(gap.get("needed_for")) is not str
                or not gap["needed_for"].strip()
                or type(gap.get("lives_in")) is not list
                or not gap["lives_in"]
                or type(gap.get("named_by")) is not list
            ):
                report.fail("F2O0-R-GAP-UNTYPED", f"{entry['id']} gap entry is untyped")
                defective.add(entry["id"])
                continue
            gaps.append(
                {
                    "construct": entry["id"],
                    "kind": entry["kind"],
                    "class": gap["class"],
                    "reason": gap["reason"],
                    "needed_for": gap["needed_for"],
                    "lives_in": list(gap["lives_in"]),
                }
            )
        else:
            sourced[entry["id"]] = source["coordinate"]
    result["sourced"] = len(sourced)
    result["gaps"] = gaps

    # Rule: coordinate validity.
    universe = facts["universe"]

    def valid(coordinate: Any, role: str, construct_id: str) -> bool:
        if type(coordinate) is not dict or _canonical(coordinate) not in universe:
            report.fail(
                "F2O0-R-COORDINATE-UNKNOWN",
                f"{construct_id} {role} coordinate is not an active view leaf",
            )
            return False
        return True

    for entry in constructs:
        construct_id = entry["id"]
        if construct_id in defective:
            continue
        if construct_id in sourced:
            valid(sourced[construct_id], "source", construct_id)
        else:
            for coordinate in entry["source"]["no_source_coordinate"]["named_by"]:
                valid(coordinate, "named_by", construct_id)
        for coordinate in entry["consulted"]:
            valid(coordinate, "consulted", construct_id)

    # Rule: injectivity over claimed coordinates.
    claims: dict[str, list[str]] = {}
    for construct_id, coordinate in sourced.items():
        claims.setdefault(_canonical(coordinate), []).append(construct_id)
    for claimants in claims.values():
        if len(claimants) > 1:
            report.fail(
                "F2O0-R-COORDINATE-ALIAS",
                "one coordinate is claimed by " + ", ".join(sorted(claimants)),
            )

    # Rule: a construct claims only a leaf that can determine its kind.
    for entry in constructs:
        construct_id = entry["id"]
        kind = entry["kind"]
        if construct_id in defective:
            continue
        if construct_id in sourced:
            if kind in GAP_ONLY_KINDS or kind not in SOURCED_KINDS:
                report.fail(
                    "F2O0-R-INVENTED-OBSERVABLE",
                    f"{construct_id} of kind {kind} claims a source coordinate",
                )
                continue
            coordinate = sourced[construct_id]
            if type(coordinate) is dict and type(coordinate.get("boundary")) is dict:
                key = _boundary_key(coordinate["boundary"])
                if key not in SOURCED_KINDS[kind]:
                    report.fail(
                        "F2O0-R-INVENTED-OBSERVABLE",
                        f"{construct_id} of kind {kind} claims a {key} leaf",
                    )
        elif kind not in GAP_ONLY_KINDS:
            report.fail(
                "F2O0-R-INVENTED-OBSERVABLE",
                f"{construct_id} of kind {kind} is recorded as a gap",
            )

    # Rules: markers.
    lines = lean_text.split("\n")
    marker_lines: dict[str, list[int]] = {}
    for number, line in enumerate(lines, start=1):
        for match in MARKER.finditer(line):
            marker_lines.setdefault(match.group(1), []).append(number)
    for construct_id in by_id:
        positions = marker_lines.get(construct_id, [])
        if not positions:
            report.fail("F2O0-R-MARKER-MISSING", f"{construct_id} has no Lean marker")
        elif len(positions) > 1:
            report.fail(
                "F2O0-R-MARKER-DUPLICATE", f"{construct_id} is marked {len(positions)} times"
            )
        elif by_id[construct_id]["lean"].get("line") != positions[0]:
            report.fail(
                "F2O0-R-MARKER-LINE",
                f"{construct_id} ledger line differs from its Lean marker line",
            )
    for marker in marker_lines:
        if marker not in by_id:
            report.fail("F2O0-R-MARKER-UNLEDGERED", f"Lean marker {marker} has no ledger entry")

    def marked_line(construct_id: str) -> str:
        positions = marker_lines.get(construct_id, [])
        if len(positions) != 1:
            return ""
        return MARKER.sub("", lines[positions[0] - 1]).strip()

    # Rule: verdict constructors agree with the owner's Terminal table.
    verdict_constructs = {
        entry["realizes"]["terminal"]: entry
        for entry in constructs
        if entry["kind"] == "terminal-verdict"
        and type(entry.get("realizes")) is dict
        and type(entry["realizes"].get("terminal")) is int
    }
    for terminal in facts["terminals"]:
        entry = verdict_constructs.get(terminal["terminal"])
        if entry is None:
            continue
        declared = entry["realizes"].get("verdict")
        text = marked_line(entry["id"])
        if declared != terminal["verdict"] or text != f"| {declared}":
            report.fail(
                "F2O0-R-VERDICT-MISMATCH",
                f"terminal {terminal['terminal']} is {terminal['verdict']} in the Core, "
                f"{declared!r} in the ledger, and {text!r} in Lean",
            )
        source = sourced.get(entry["id"])
        expected = facts["coordinate_tables"]["EffectView"].get(
            (
                ("field", 6),
                ("sequence", terminal["row"]),
                ("field", 1),
                ("variant", terminal["verdict_case"]),
            )
        )
        if source is not None and _canonical(source) != expected:
            report.fail(
                "F2O0-R-VERDICT-MISMATCH",
                f"terminal {terminal['terminal']} verdict claims another leaf",
            )

    # Rule: occurrence steps agree with the owner's effect table.
    steps: dict[int, list[dict[str, Any]]] = {}
    for entry in constructs:
        if entry["kind"] != "occurrence-step":
            continue
        realizes = entry.get("realizes")
        if type(realizes) is not dict or type(realizes.get("occurrence")) is not int:
            report.fail("F2O0-R-EFFECT-MISMATCH", f"{entry['id']} realizes no occurrence")
            continue
        steps.setdefault(realizes["occurrence"], []).append(entry)
    for occurrence in facts["occurrences"]:
        ordinal = occurrence["ordinal"]
        for entry in steps.get(ordinal, []):
            realizes = entry["realizes"]
            if realizes.get("effect") != occurrence["effect"]:
                report.fail(
                    "F2O0-R-EFFECT-MISMATCH",
                    f"occurrence {ordinal} is {occurrence['effect']} in the Core and "
                    f"{realizes.get('effect')!r} in the ledger",
                )
            source = sourced.get(entry["id"])
            if source is not None and _path_key(source["path"])[:2] != (
                ("field", 1),
                ("sequence", ordinal),
            ):
                report.fail(
                    "F2O0-R-EFFECT-MISMATCH",
                    f"occurrence {ordinal} step claims a leaf outside its schedule row",
                )
            target_key = {
                "Challenge": "challenge",
                "InvokeCheck": "check",
                "ReachTerminal": "terminal",
            }.get(occurrence["effect"])
            if target_key is not None and realizes.get(target_key) != occurrence["target"]:
                report.fail(
                    "F2O0-R-EFFECT-MISMATCH",
                    f"occurrence {ordinal} names {target_key} {realizes.get(target_key)!r}, "
                    f"the Core names {occurrence['target']}",
                )

    # Rule: every Terminal has a verdict constructor and a terminal step.
    terminal_steps = {
        entry["realizes"].get("terminal")
        for ordinal, entries in steps.items()
        for entry in entries
        if entry["realizes"].get("effect") == "ReachTerminal"
    }
    for terminal in facts["terminals"]:
        if terminal["terminal"] not in verdict_constructs:
            report.fail(
                "F2O0-R-TERMINAL-UNCOVERED",
                f"terminal {terminal['terminal']} ({terminal['verdict']}) has no verdict "
                "constructor",
            )
        if terminal["terminal"] not in terminal_steps:
            report.fail(
                "F2O0-R-TERMINAL-UNCOVERED",
                f"terminal {terminal['terminal']} ({terminal['verdict']}) has no step",
            )

    # Rule: every occurrence has at least one step.
    for occurrence in facts["occurrences"]:
        if not steps.get(occurrence["ordinal"]):
            report.fail(
                "F2O0-R-OCCURRENCE-UNCOVERED",
                f"occurrence {occurrence['ordinal']} ({occurrence['effect']}) has no "
                "construct",
            )

    # Rule: schedule order in the Lean text.
    previous = 0
    for occurrence in facts["occurrences"]:
        ordinal = occurrence["ordinal"]
        positions = [
            marker_lines[entry["id"]][0]
            for entry in steps.get(ordinal, [])
            if len(marker_lines.get(entry["id"], [])) == 1
        ]
        if not positions:
            continue
        if min(positions) <= previous:
            report.fail(
                "F2O0-R-SCHEDULE-ORDER",
                f"occurrence {ordinal} is emitted before an earlier occurrence",
            )
        previous = max(previous, min(positions))

    # Rule: Fresh challenge realization.
    interpretation_constructs = [
        entry for entry in constructs if entry["kind"] == "challenge-interpretation"
    ]
    if facts["interpretation"] == "Fresh":
        if not interpretation_constructs:
            report.fail(
                "F2O0-R-CHALLENGE-NOT-FRESH", "no construct carries the Fresh interpretation"
            )
        for entry in interpretation_constructs:
            source = sourced.get(entry["id"])
            expected = facts["coordinate_tables"]["ExecutionView"].get(
                (("field", 2), ("variant", facts["interpretation_case"]))
            )
            if source is None or _canonical(source) != expected:
                report.fail(
                    "F2O0-R-CHALLENGE-NOT-FRESH",
                    f"{entry['id']} does not claim the ExecutionView interpretation leaf",
                )
        for occurrence in facts["occurrences"]:
            if occurrence["effect"] != "Challenge":
                continue
            for entry in steps.get(occurrence["ordinal"], []):
                realizes = entry["realizes"]
                law = by_id.get(str(realizes.get("samples_from")))
                text = marked_line(entry["id"])
                law_name = law["lean"].get("name") if law else None
                pattern = (
                    re.compile(r"^let\s+[A-Za-z0-9_']+\s*←\s*" + re.escape(law_name) + r"$")
                    if law_name
                    else None
                )
                if (
                    realizes.get("realization") != "sample"
                    or law is None
                    or law["kind"] != "distribution"
                    or "no_source_coordinate" not in law["source"]
                    or pattern is None
                    or not pattern.match(text)
                ):
                    report.fail(
                        "F2O0-R-CHALLENGE-NOT-FRESH",
                        f"occurrence {occurrence['ordinal']} is not a sample from a "
                        f"declared public-coin law parameter: {text!r}",
                    )

    result["coverage"] = {
        "occurrences": len(facts["occurrences"]),
        "occurrences_with_steps": sum(
            1 for item in facts["occurrences"] if steps.get(item["ordinal"])
        ),
        "terminals": len(facts["terminals"]),
        "terminals_with_verdicts": sum(
            1 for item in facts["terminals"] if item["terminal"] in verdict_constructs
        ),
        "prover_reads": sum(1 for entry in constructs if entry["kind"] == "prover-read"),
        "prover_decisions": sum(
            1 for entry in constructs if entry["kind"] == "prover-decision"
        ),
        "owner_reads": facts["reads"],
        "owner_decisions": facts["decisions"],
        "claimed_coordinates": len(claims),
        "view_leaves": facts["leaf_count"],
    }
    return _finish(result, report)


def _finish(result: dict[str, Any], report: _Report) -> dict[str, Any]:
    failures = report.ordered()
    result["failures"] = failures
    if failures:
        result["outcome"] = "Refused"
        result["code"] = failures[0]["code"]
        result["audit"] = {"outcome": "Refused", "code": failures[0]["code"]}
        return result
    result["outcome"] = "Affirmative"
    result["code"] = PASS_CODE
    operational = [gap for gap in result["gaps"] if gap["class"].startswith("operational-")]
    outcome, code = AUDIT_MISSING if operational else AUDIT_CLOSED
    result["audit"] = {
        "outcome": outcome,
        "code": code,
        "operational_gaps": [gap["construct"] for gap in operational],
        "property_premise_gaps": [
            gap["construct"] for gap in result["gaps"] if gap["class"] == "property-premise"
        ],
    }
    return result


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--ledger", type=Path, default=HERE / "generated" / "ledger.json")
    parser.add_argument("--lean", type=Path, default=HERE / "generated" / "Schnorr.lean")
    arguments = parser.parse_args()
    try:
        ledger = json.loads(arguments.ledger.read_text(encoding="utf-8"))
        lean_text = arguments.lean.read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        print(f"checker cannot read its inputs: {error}", file=sys.stderr)
        return 2
    report = check(copy.deepcopy(ledger), lean_text, owner_facts())
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0 if report["outcome"] == "Affirmative" else 1


if __name__ == "__main__":
    raise SystemExit(main())
