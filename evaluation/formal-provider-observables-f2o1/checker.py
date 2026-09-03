#!/usr/bin/env python3
"""Independent checker for the F2-O1 generated interaction and ledger.

This module does not import ``generator.py``.  It authenticates and byte-decodes
the D1 Core and Fresh Protocol through D1's cold path, independently derives the
one D1-issued ``PublicCoinView``, enumerates that view's active leaves, and then
checks totality, injection, coordinate validity, gap enumeration, schedule, and
the six required integrated-carrier discriminators.
"""

from __future__ import annotations

import copy
import importlib.util
import json
from pathlib import Path
import re
import sys
from types import ModuleType
from typing import Any


ROOT = Path(__file__).resolve().parents[2]
D1_MODEL = ROOT / "evaluation/formal-source-integrated-graph-f0v2b2d1/model.py"
D1_COLD = ROOT / "evaluation/formal-source-integrated-graph-f0v2b2d1/independent.py"
PROFILE_DIGEST = "9a971206c68eab0b5b5e8124787bfce2f5335467a576b242190750e773941d2f"
PROFILE_BODY_SHA256 = "fbba36f4b0e15dcc55ef60d4d251b0286c9627726c1bf6f827c95784fcd00f70"
LEDGER_FORMAT = "zkc.formal-provider-observables-f2o1.ledger.v0"
MARKER = re.compile(r"-- \[f2o1:([A-Za-z0-9_.\-]+)\]")

EFFECT_CASES = {
    0: "ProverMessage",
    1: "VerifierMessage",
    2: "Challenge",
    3: "InvokeCheck",
    4: "ApplyReduction",
    5: "ReachTerminal",
    7: "ModuleEffect",
}
ORACLE_EFFECT_CASES = {0: "PublishOracle", 1: "QueryOracle", 2: "AnswerOracle"}
ORACLE_MODES = {0: "FullCanonical", 1: "PublicBinding", 2: "LogicalAccess"}
VISIBILITIES = {0: "Public", 1: "VerifierOnly"}
MODULE_DECISIONS = {0: "Deterministic", 1: "ProverPrivate", 2: "ProverPublication"}
GAP_CLASSES = frozenset(
    (
        "operational-owner-view",
        "operational-distribution",
        "operational-denotation",
        "module-effect-denotation",
        "oracle-carrier-representation",
        "operational-outcome-map",
        "property-premise",
    )
)
OPERATIONAL_CLASSES = GAP_CLASSES - {"property-premise"}
RULE_ORDER = (
    "F2O1-R-LEDGER-SHAPE",
    "F2O1-R-CONSTRUCT-TOTALITY",
    "F2O1-R-GAP-UNTYPED",
    "F2O1-R-CONSTRUCT-UNSOURCED",
    "F2O1-R-COORDINATE-UNKNOWN",
    "F2O1-R-COORDINATE-MISMATCH",
    "F2O1-R-COORDINATE-ALIAS",
    "F2O1-R-INVENTED-OBSERVABLE",
    "F2O1-R-SHARED-CHALLENGE-DUPLICATED",
    "F2O1-R-REDUCTION-CHALLENGE-BACKLINK",
    "F2O1-R-ORACLE-MODE-MISMATCH",
    "F2O1-R-QUERY-VISIBILITY",
    "F2O1-R-TERMINAL-PREEMPTION",
    "F2O1-R-EFFECT-MISMATCH",
    "F2O1-R-OCCURRENCE-UNCOVERED",
    "F2O1-R-SCHEDULE-ORDER",
    "F2O1-R-MARKER-MISSING",
    "F2O1-R-MARKER-UNLEDGERED",
    "F2O1-R-MARKER-DUPLICATE",
    "F2O1-R-MARKER-LINE",
    "F2O1-R-GAP-ENUMERATION",
)
PASS_CODE = "F2O1-A-LEDGER-CHECKED"
EXPECTED_OCCURRENCE_TEXT = {
    0: "let _ ← ops.verifierMessage 0",
    1: "let _ ← ops.proverMessage 1",
    2: "let _ ← ops.moduleEffect 0",
    3: "let _ ← ops.moduleEffect 1",
    4: "let _ ← ops.moduleEffect 2",
    5: "let _ ← ops.publishOracle 0",
    6: "let _ ← ops.queryOracle 0 6 false",
    7: "let _ ← ops.answerOracle 6",
    8: "let _ ← ops.publishOracle 1",
    9: "let _ ← ops.queryOracle 1 9 true",
    10: "let _ ← ops.answerOracle 9",
    11: "let _ ← ops.publishOracle 2",
    12: "let _ ← ops.queryOracle 2 12 false",
    13: "let _ ← ops.answerOracle 12",
    14: "let challenge0 ← ops.sampleChallenge 0 []",
    15: "let challenge1 ← ops.sampleChallenge 1 []",
    16: "let challenge2 ← ops.sampleChallenge 2 [challenge1]",
    17: "let _ ← ops.invokeCheck 0",
    18: "let _ ← ops.applyReduction 0 [challenge0, challenge1]",
    19: "let _ ← ops.applyReduction 1 [challenge0, challenge2]",
    20: "let acceptActive ← ops.terminalGuard 0",
    21: "let abortActive ← ops.terminalGuard 1",
    22: "return Verdict.reject",
}


class CheckerError(ValueError):
    """The cold owner-side facts could not be obtained."""


def _load(name: str, path: Path) -> ModuleType:
    if name in sys.modules:
        return sys.modules[name]
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise ImportError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def _canonical(value: Any) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"))


def _boundary(atom: dict[str, Any], value: Any) -> dict[str, Any]:
    kind = atom["kind"]
    if kind == "unit":
        if value is not None:
            raise CheckerError("unit leaf has another carrier")
        return {"kind": "unit"}
    if kind == "natural":
        if type(value) is not int or not 0 <= value <= atom["max"]:
            raise CheckerError("natural leaf is outside its bound")
        return {"kind": "natural", "max": atom["max"]}
    if kind == "meta-boolean":
        if type(value) is not bool:
            raise CheckerError("meta-boolean leaf has another carrier")
        return {"kind": "meta-boolean"}
    if kind == "canonical-body":
        if (
            type(value) is not dict
            or set(value) != {"compiler", "body"}
            or value["compiler"] != atom["compiler"]
        ):
            raise CheckerError("canonical body has another compiler")
        bytes.fromhex(value["body"])
        return {"kind": "canonical-body", "compiler": atom["compiler"]}
    if kind == "exact-profile-law":
        return {"kind": "exact-profile-law", "law": atom["law"]}
    raise CheckerError(f"unknown schema atom {kind}")


def _enumerate(view: str, schema: dict[str, Any], value: Any) -> list[dict[str, Any]]:
    leaves: list[dict[str, Any]] = []

    def walk(node: dict[str, Any], current: Any, path: list[dict[str, int]]) -> None:
        kind = node["node"]
        if kind == "atom":
            leaves.append({"view": view, "path": copy.deepcopy(path), "boundary": _boundary(node["atom"], current)})
        elif kind == "record":
            expected = [ordinal for ordinal, _ in node["fields"]]
            if type(current) is not dict or list(current) != expected:
                raise CheckerError("record differs from the compiled schema")
            for ordinal, child in node["fields"]:
                walk(child, current[ordinal], [*path, {"step": "field", "ordinal": ordinal}])
        elif kind == "variant":
            if type(current) is not dict or set(current) != {"case", "value"}:
                raise CheckerError("variant differs from the compiled schema")
            cases = dict(node["cases"])
            if current["case"] not in cases:
                raise CheckerError("variant selects an absent case")
            walk(cases[current["case"]], current["value"], [*path, {"step": "variant", "ordinal": current["case"]}])
        elif kind == "sequence":
            if type(current) is not list or len(current) > node["max"]:
                raise CheckerError("sequence differs from the compiled schema")
            for ordinal, child in enumerate(current):
                walk(node["element"], child, [*path, {"step": "sequence", "ordinal": ordinal}])
        else:
            raise CheckerError(f"unknown schema node {kind}")

    walk(schema, value, [])
    return leaves


def _algorithm_preimages(model: ModuleType, fixture: object) -> tuple[tuple[bytes, bytes], ...]:
    return tuple(
        sorted(
            (
                (item.identity.internal_reference(), model.k1.algorithm_preimage(item))
                for item in fixture.algorithms
            ),
            key=lambda item: item[0],
        )
    )


def _effect(effect: dict[str, Any]) -> tuple[str, int | None]:
    tag = effect["tag"]
    if tag == 6:
        name = ORACLE_EFFECT_CASES[effect["oracle_tag"]]
        target = effect.get("oracle", effect.get("query"))
        return name, target
    name = EFFECT_CASES[tag]
    if tag == 7:
        return name, effect["declaration"]["ordinal"]
    fields = {
        2: "challenge",
        3: "check",
        4: "reduction",
        5: "terminal",
    }
    return name, effect.get(fields.get(tag, ""))


def owner_facts() -> dict[str, Any]:
    """Authenticate the fixture bytes and derive facts without generator code."""

    model = _load("_zkc_f2o1_checker_fixture", D1_MODEL)
    cold = _load("_zkc_f2o1_checker_cold", D1_COLD)
    cold.configure(PROFILE_DIGEST, PROFILE_BODY_SHA256)
    fixture = model.fixture("integrated-baseline")
    value, evidence = cold.project(
        fixture.candidate.profiled_body,
        fixture.candidate.asserted_id.internal_reference(),
        fixture.protocol_candidate.profiled_body,
        fixture.protocol_candidate.asserted_id.internal_reference(),
        model.raw_module_sources(fixture.environment),
        _algorithm_preimages(model, fixture),
        model.k1.DEFAULT_EVALUATION_CONTRACT.identity.internal_reference(),
    )
    _profile, domain = cold.cold._authenticated_subject(
        fixture.candidate.profiled_body,
        fixture.candidate.asserted_id.internal_reference(),
        "pir.interactive-core",
        "F2-O1 cold Core",
    )
    core = cold._decode_core(domain)
    sources = cold._source_closure(core["used_modules"], model.raw_module_sources(fixture.environment))
    modules = cold._module_occurrences(core, sources)
    manifest = _enumerate("PublicCoinView", cold.VIEW_SCHEMAS["PublicCoinView"], value)
    effects = tuple(_effect(row["effect"]) for row in core["occurrences"])
    oracle_modes = tuple(ORACLE_MODES[item["mode"]["tag"]] for item in core["oracles"])
    query_visibilities = {
        ordinal: VISIBILITIES[row["effect"]["visibility"]]
        for ordinal, row in enumerate(core["occurrences"])
        if row["effect"]["tag"] == 6 and row["effect"]["oracle_tag"] == 1
    }
    module_decisions = tuple(MODULE_DECISIONS[modules[item]["decision"]] for item in (2, 3, 4))
    reductions = {index: tuple(row["required_challenges"]) for index, row in enumerate(core["reductions"])}
    required_edges = (((11, 0), (6, 22)), ((11, 1), (6, 22)))
    if not all(edge in evidence["edges"] for edge in required_edges):
        raise CheckerError("cold graph omitted fallback terminal preemption")
    controls: dict[str, dict[str, Any]] = {}
    for name in (
        "private-verifier-output-sink",
        "invalid-module-control-sink",
        "history-challenge-condition",
        "logical-reject-preemption",
    ):
        control_fixture = model.fixture(name)
        _control_value, control_evidence = cold.project(
            control_fixture.candidate.profiled_body,
            control_fixture.candidate.asserted_id.internal_reference(),
            control_fixture.protocol_candidate.profiled_body,
            control_fixture.protocol_candidate.asserted_id.internal_reference(),
            model.raw_module_sources(control_fixture.environment),
            _algorithm_preimages(model, control_fixture),
            model.k1.DEFAULT_EVALUATION_CONTRACT.identity.internal_reference(),
        )
        _control_profile, control_domain = cold.cold._authenticated_subject(
            control_fixture.candidate.profiled_body,
            control_fixture.candidate.asserted_id.internal_reference(),
            "pir.interactive-core",
            f"F2-O1 cold control {name}",
        )
        control_core = cold._decode_core(control_domain)
        fallback_terminal = control_core["occurrences"][22]["effect"]["terminal"]
        controls[name] = {
            "eligible": control_evidence["eligible"],
            "fallback_verdict": control_core["terminals"][fallback_terminal]["verdict"],
            "preemption": (20, 21),
        }
    return {
        "core_id": fixture.candidate.asserted_id.carrier(),
        "protocol_id": fixture.protocol_candidate.asserted_id.carrier(),
        "effects": effects,
        "oracle_modes": oracle_modes,
        "query_visibilities": query_visibilities,
        "module_decisions": module_decisions,
        "reductions": reductions,
        "terminal_preemption": {22: (20, 21)},
        "controls": controls,
        "manifest": manifest,
        "universe": {_canonical(item) for item in manifest},
    }


def _source_paths() -> dict[str, tuple[tuple[str, int], ...]]:
    def parse(spec: str) -> tuple[tuple[str, int], ...]:
        names = {"f": "field", "s": "sequence", "v": "variant"}
        return tuple((names[token[0]], int(token[1:])) for token in spec.split())

    raw = {"subject.core": "f0"}
    for challenge, occurrence in enumerate((14, 15, 16)):
        prefix = f"f4 s{challenge}"
        raw.update(
            {
                f"occurrence.{occurrence}": f"{prefix} f1",
                f"challenge.{challenge}.scope": f"{prefix} f2",
                f"challenge.{challenge}.value-type": f"{prefix} f3",
                f"challenge.{challenge}.domain": f"{prefix} f4",
                f"challenge.{challenge}.fresh-ref": f"{prefix} f5",
                f"challenge.{challenge}.condition": f"{prefix} f8 s0",
            }
        )
    raw.update(
        {
            "challenge.0.correlation.kind": "f4 s0 f6 v0",
            "challenge.0.reduction-use.contract": "f4 s0 f7 v1",
            "challenge.1.correlation.group": "f4 s1 f6 v1 f0",
            "challenge.1.correlation.index": "f4 s1 f6 v1 f1",
            "challenge.1.reduction-use.kind": "f4 s1 f7 v0",
            "challenge.2.correlation.group": "f4 s2 f6 v1 f0",
            "challenge.2.correlation.index": "f4 s2 f6 v1 f1",
            "challenge.2.correlation.prior.1": "f4 s2 f6 v1 f2 s0",
            "challenge.2.reduction-use.kind": "f4 s2 f7 v0",
            "reduction.0.challenge.0": "f4 s0 f10 s0 f0",
            "reduction.1.challenge.0": "f4 s0 f10 s1 f0",
            "reduction.0.challenge.1": "f4 s1 f10 s0 f0",
            "reduction.1.challenge.2": "f4 s2 f10 s0 f0",
        }
    )
    return {key: parse(value) for key, value in raw.items()}


def _expected_ids() -> set[str]:
    ids = {"subject.core", "subject.protocol"}
    ids.update(f"occurrence.{item}" for item in range(23))
    for module in range(3):
        ids.update((f"module.{module}.decision-class", f"module.{module}.denotation"))
    for oracle in range(3):
        ids.update((f"oracle.{oracle}.mode", f"oracle.{oracle}.carrier"))
    ids.update(f"query.{item}.visibility" for item in (6, 9, 12))
    for challenge in range(3):
        ids.update(
            (
                f"challenge.{challenge}.scope",
                f"challenge.{challenge}.value-type",
                f"challenge.{challenge}.domain",
                f"challenge.{challenge}.fresh-ref",
                f"challenge.{challenge}.law",
                f"challenge.{challenge}.condition",
            )
        )
    ids.update(
        (
            "challenge.0.correlation.kind",
            "challenge.0.reduction-use.contract",
            "challenge.1.correlation.group",
            "challenge.1.correlation.index",
            "challenge.1.reduction-use.kind",
            "challenge.2.correlation.group",
            "challenge.2.correlation.index",
            "challenge.2.correlation.prior.1",
            "challenge.2.reduction-use.kind",
            "reduction.0.challenge.0",
            "reduction.0.challenge.1",
            "reduction.1.challenge.0",
            "reduction.1.challenge.2",
            "check.0.denotation",
            "guard.0.denotation",
            "guard.20.denotation",
            "guard.21.denotation",
            "terminal.22.preemption",
            "control.logical-reject-preemption.terminal.22.preemption",
            "provider.outcome-map",
        )
    )
    for claim in range(3):
        ids.update((f"claim.{claim}.declaration", f"claim.{claim}.premise"))
    for reduction in range(2):
        ids.update(
            (
                f"reduction.{reduction}.declaration",
                f"reduction.{reduction}.denotation",
                f"reduction.{reduction}.premise",
            )
        )
    ids.update(f"terminal.{item}.declaration" for item in range(3))
    return ids


def _gap_class(construct_id: str) -> str:
    if construct_id.endswith(".law"):
        return "operational-distribution"
    if construct_id.startswith("module.") and construct_id.endswith(".denotation"):
        return "module-effect-denotation"
    if construct_id.startswith("oracle.") and construct_id.endswith(".carrier"):
        return "oracle-carrier-representation"
    if construct_id.endswith(".premise"):
        return "property-premise"
    if construct_id.endswith(".denotation"):
        return "operational-denotation"
    if construct_id == "provider.outcome-map":
        return "operational-outcome-map"
    return "operational-owner-view"


class Report:
    def __init__(self) -> None:
        self.failures: list[dict[str, str]] = []

    def fail(self, code: str, detail: str) -> None:
        self.failures.append({"code": code, "detail": detail})

    def ordered(self) -> list[dict[str, str]]:
        rank = {code: index for index, code in enumerate(RULE_ORDER)}
        return sorted(self.failures, key=lambda item: (rank.get(item["code"], len(rank)), item["detail"]))


def check(ledger: Any, lean_text: str, facts: dict[str, Any]) -> dict[str, Any]:
    report = Report()
    result: dict[str, Any] = {"outcome": "Refused", "code": None, "failures": [], "gaps": [], "constructs": 0, "sourced": 0}
    if type(ledger) is not dict or ledger.get("format") != LEDGER_FORMAT or type(ledger.get("constructs")) is not list:
        report.fail("F2O1-R-LEDGER-SHAPE", "ledger outer shape or format differs")
        result["failures"] = report.ordered()
        result["code"] = result["failures"][0]["code"]
        return result
    constructs = ledger["constructs"]
    result["constructs"] = len(constructs)
    entries: dict[str, dict[str, Any]] = {}
    for item in constructs:
        if type(item) is not dict or type(item.get("id")) is not str or item["id"] in entries:
            report.fail("F2O1-R-LEDGER-SHAPE", "construct is malformed or duplicated")
            continue
        entries[item["id"]] = item
    expected_ids = _expected_ids()
    if set(entries) != expected_ids:
        missing = sorted(expected_ids - set(entries))
        extra = sorted(set(entries) - expected_ids)
        report.fail("F2O1-R-CONSTRUCT-TOTALITY", f"missing={missing}; extra={extra}")

    path_table = {
        tuple((step["step"], step["ordinal"]) for step in item["path"]): item
        for item in facts["manifest"]
    }
    source_paths = _source_paths()
    claimed: dict[str, str] = {}
    observed_gaps: list[dict[str, str]] = []
    for construct_id, item in entries.items():
        source = item.get("source")
        if type(source) is not dict:
            report.fail("F2O1-R-CONSTRUCT-UNSOURCED", f"{construct_id} has no source object")
            continue
        has_coordinate = "coordinate" in source
        has_gap = "no_source_coordinate" in source
        if has_coordinate == has_gap:
            report.fail("F2O1-R-CONSTRUCT-UNSOURCED", f"{construct_id} must have exactly one coordinate or gap")
            continue
        if has_coordinate:
            coordinate = source["coordinate"]
            key = _canonical(coordinate)
            if key not in facts["universe"]:
                report.fail("F2O1-R-COORDINATE-UNKNOWN", f"{construct_id} claims an inactive coordinate")
            expected_path = source_paths.get(construct_id)
            actual_path = tuple((step.get("step"), step.get("ordinal")) for step in coordinate.get("path", [])) if type(coordinate) is dict else ()
            if expected_path is None:
                report.fail("F2O1-R-INVENTED-OBSERVABLE", f"{construct_id} claims a leaf although its required owner view or denotation is absent")
            elif actual_path != expected_path or coordinate.get("view") != "PublicCoinView" or coordinate != path_table.get(expected_path):
                report.fail("F2O1-R-COORDINATE-MISMATCH", f"{construct_id} claims another PublicCoin leaf")
            if key in claimed:
                report.fail("F2O1-R-COORDINATE-ALIAS", f"{construct_id} aliases {claimed[key]}")
            claimed[key] = construct_id
        else:
            gap = source["no_source_coordinate"]
            required = {"class", "reason", "needed_for", "named_by", "lives_in"}
            if type(gap) is not dict or set(gap) != required or gap.get("class") not in GAP_CLASSES:
                report.fail("F2O1-R-GAP-UNTYPED", f"{construct_id} has an incomplete typed gap")
                continue
            if construct_id in source_paths:
                report.fail("F2O1-R-CONSTRUCT-UNSOURCED", f"{construct_id} omits its active PublicCoin leaf")
            if gap["class"] != _gap_class(construct_id):
                report.fail("F2O1-R-GAP-UNTYPED", f"{construct_id} uses the wrong gap class")
            for coordinate in gap["named_by"]:
                if _canonical(coordinate) not in facts["universe"]:
                    report.fail("F2O1-R-COORDINATE-UNKNOWN", f"{construct_id} names an inactive coordinate")
            observed_gaps.append({"construct": construct_id, "class": gap["class"], "needed_for": gap["needed_for"]})
    result["sourced"] = len(claimed)
    observed_gaps.sort(key=lambda item: item["construct"])
    result["gaps"] = observed_gaps

    for ordinal, expected in enumerate(facts["effects"]):
        entry = entries.get(f"occurrence.{ordinal}")
        if entry is None:
            report.fail("F2O1-R-OCCURRENCE-UNCOVERED", f"occurrence {ordinal} is absent")
            continue
        realizes = entry.get("realizes", {})
        actual = (realizes.get("effect"), realizes.get("target"))
        if actual != expected:
            report.fail("F2O1-R-EFFECT-MISMATCH", f"occurrence {ordinal}: expected {expected}, got {actual}")
    shared = entries.get("occurrence.14", {}).get("realizes", {})
    if shared.get("sample_count") != 1 or shared.get("shared_value") != "challenge0":
        report.fail("F2O1-R-SHARED-CHALLENGE-DUPLICATED", "shared Challenge 0 is not one sampled value")
    for reduction, expected in facts["reductions"].items():
        realizes = entries.get(f"reduction.{reduction}.declaration", {}).get("realizes", {})
        if tuple(realizes.get("required_challenges", ())) != expected:
            report.fail("F2O1-R-REDUCTION-CHALLENGE-BACKLINK", f"reduction {reduction} challenge backlinks differ")
    for oracle, expected in enumerate(facts["oracle_modes"]):
        actual = entries.get(f"oracle.{oracle}.mode", {}).get("realizes", {}).get("mode")
        if actual != expected:
            report.fail("F2O1-R-ORACLE-MODE-MISMATCH", f"oracle {oracle}: expected {expected}, got {actual}")
    for occurrence, expected in facts["query_visibilities"].items():
        actual = entries.get(f"query.{occurrence}.visibility", {}).get("realizes", {}).get("visibility")
        if actual != expected:
            report.fail("F2O1-R-QUERY-VISIBILITY", f"query occurrence {occurrence}: expected {expected}, got {actual}")
    for module, expected in enumerate(facts["module_decisions"]):
        actual = entries.get(f"module.{module}.decision-class", {}).get("realizes", {}).get("decision_class")
        if actual != expected:
            report.fail("F2O1-R-EFFECT-MISMATCH", f"module effect {module}: expected decision class {expected}, got {actual}")
    for occurrence, expected in facts["terminal_preemption"].items():
        actual = entries.get(f"terminal.{occurrence}.preemption", {}).get("realizes", {}).get("preempted_by")
        if tuple(actual or ()) != expected:
            report.fail("F2O1-R-TERMINAL-PREEMPTION", f"fallback occurrence {occurrence} preemption differs")
    control = entries.get(
        "control.logical-reject-preemption.terminal.22.preemption", {}
    ).get("realizes", {})
    expected_control = facts["controls"]["logical-reject-preemption"]
    if (
        expected_control["fallback_verdict"] != 0
        or control.get("verdict") != "Accept"
        or tuple(control.get("preempted_by", ())) != expected_control["preemption"]
    ):
        report.fail(
            "F2O1-R-TERMINAL-PREEMPTION",
            "logical-reject-preemption fallback Accept dependency differs",
        )

    markers: dict[str, list[int]] = {}
    for line_number, line in enumerate(lean_text.splitlines(), 1):
        for match in MARKER.finditer(line):
            markers.setdefault(match.group(1), []).append(line_number)
    lean_lines = lean_text.splitlines()
    for construct_id, entry in entries.items():
        positions = markers.get(construct_id, [])
        if not positions:
            report.fail("F2O1-R-MARKER-MISSING", f"{construct_id} has no Lean marker")
        elif len(positions) > 1:
            report.fail("F2O1-R-MARKER-DUPLICATE", f"{construct_id} has {len(positions)} Lean markers")
        elif positions[0] != entry.get("lean", {}).get("line"):
            report.fail("F2O1-R-MARKER-LINE", f"{construct_id} marker line differs")
        else:
            actual_text = lean_lines[positions[0] - 1].split("  -- [f2o1:", 1)[0].strip()
            if actual_text != entry.get("lean", {}).get("text"):
                report.fail("F2O1-R-MARKER-LINE", f"{construct_id} Lean text differs from its ledger")
    for construct_id in markers:
        if construct_id not in entries:
            report.fail("F2O1-R-MARKER-UNLEDGERED", f"{construct_id} is not ledgered")
    occurrence_lines = [markers.get(f"occurrence.{item}", [10**9])[0] for item in range(23)]
    if occurrence_lines != sorted(occurrence_lines) or len(set(occurrence_lines)) != 23:
        report.fail("F2O1-R-SCHEDULE-ORDER", "occurrence markers are not in strict Core order")
    for ordinal, expected_text in EXPECTED_OCCURRENCE_TEXT.items():
        positions = markers.get(f"occurrence.{ordinal}", [])
        if len(positions) != 1:
            continue
        actual_text = lean_lines[positions[0] - 1].split("  -- [f2o1:", 1)[0].strip()
        if actual_text == expected_text:
            continue
        if ordinal == 14:
            code = "F2O1-R-SHARED-CHALLENGE-DUPLICATED"
        elif ordinal in (6, 9, 12):
            code = "F2O1-R-QUERY-VISIBILITY"
        elif ordinal in (18, 19):
            code = "F2O1-R-REDUCTION-CHALLENGE-BACKLINK"
        else:
            code = "F2O1-R-EFFECT-MISMATCH"
        report.fail(code, f"occurrence {ordinal} Lean rendering differs")
    terminal_fragment = """  if acceptActive then
    return Verdict.accept
  else
    let abortActive ← ops.terminalGuard 1  -- [f2o1:occurrence.21]
    if abortActive then
      return Verdict.abort
    else
      return Verdict.reject  -- [f2o1:occurrence.22]"""
    if terminal_fragment not in lean_text:
        report.fail("F2O1-R-TERMINAL-PREEMPTION", "baseline first-active terminal rendering differs")

    declared_gaps = ledger.get("gaps")
    expected_declared = sorted(observed_gaps, key=lambda item: item["construct"])
    if type(declared_gaps) is not list or sorted(declared_gaps, key=lambda item: item.get("construct", "")) != expected_declared:
        report.fail("F2O1-R-GAP-ENUMERATION", "top-level gap enumeration differs from construct gaps")

    failures = report.ordered()
    result["failures"] = failures
    if failures:
        result["code"] = failures[0]["code"]
        return result
    result["outcome"] = "Affirmative"
    result["code"] = PASS_CODE
    operational = sorted(item["construct"] for item in observed_gaps if item["class"] in OPERATIONAL_CLASSES)
    result["aggregate"] = {
        "outcome": "Affirmative" if not operational else "CannotAnswer",
        "code": "F2O1-A-OBSERVABLES-CLOSED" if not operational else "F2O1-C-MISSING-OPERATIONAL-OBSERVABLE",
        "missing_operational_observables": operational,
    }
    return result
