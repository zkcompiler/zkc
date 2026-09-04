#!/usr/bin/env python3
"""Untrusted generator for the F2-O1 integrated provider-observable audit."""

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
HERE = Path(__file__).resolve().parent
D1_MODEL = ROOT / "evaluation/formal-source-integrated-graph-f0v2b2d1/model.py"
GENERATED_LEAN = HERE / "generated" / "Integrated.lean"
GENERATED_LEDGER = HERE / "generated" / "ledger.json"

LEDGER_FORMAT = "zkc.formal-provider-observables-f2o1.ledger.v0"
MARKER_PREFIX = "-- [f2o1:"
PROVIDER = {
    "name": "VCVio",
    "revision": "de0a3108140e3e04a7ebf0075aa110b459ee6e8a",
    "toolchain": "leanprover/lean4:v4.33.1",
    "imported_module": "VCVio.OracleComp.ProbComp",
    "interaction_monad": "ProbComp = OracleComp unifSpec",
    "shape": "generic OracleComp/ProbComp do-block",
}
VIEW_ORDER = (
    "PublicBindingView",
    "StrategyDecisionView",
    "PublicCoinView",
    "EffectView",
    "ClaimReductionView",
    "ExecutionView",
)
PROFILE_DIGEST = "0af785eb8159ca2182843c62f72898e3c17266c5a7d9b317cfe2ae463d840474"
PROFILE_BODY_SHA256 = "c2dee0bc0bef91610a16acf8587444c57663ec83a87a948a51f320b194381d4a"
TARGET = "docs-next/pir/interactive-core.md"
D1_SOURCE = "evaluation/formal-source-integrated-graph-f0v2b2d1/model.py"

EFFECTS = (
    ("VerifierMessage", None),
    ("ProverMessage", None),
    ("ModuleEffect", 0),
    ("ModuleEffect", 1),
    ("ModuleEffect", 2),
    ("PublishOracle", 0),
    ("QueryOracle", 0),
    ("AnswerOracle", 6),
    ("PublishOracle", 1),
    ("QueryOracle", 1),
    ("AnswerOracle", 9),
    ("PublishOracle", 2),
    ("QueryOracle", 2),
    ("AnswerOracle", 12),
    ("Challenge", 0),
    ("Challenge", 1),
    ("Challenge", 2),
    ("InvokeCheck", 0),
    ("ApplyReduction", 0),
    ("ApplyReduction", 1),
    ("ReachTerminal", 0),
    ("ReachTerminal", 1),
    ("ReachTerminal", 2),
)
ORACLE_MODES = ("FullCanonical", "PublicBinding", "LogicalAccess")
QUERY_VISIBILITIES = {6: "Public", 9: "VerifierOnly", 12: "Public"}
MODULE_DECISIONS = ("Deterministic", "ProverPrivate", "ProverPublication")
REDUCTION_CHALLENGES = {0: (0, 1), 1: (0, 2)}
TERMINAL_PREEMPTION = {22: (20, 21)}


class GeneratorError(ValueError):
    """The admitted subject no longer supports the frozen finite rendering."""


def _load(name: str, path: Path) -> ModuleType:
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise ImportError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def _boundary(atom: dict[str, Any], value: Any) -> dict[str, Any]:
    kind = atom["kind"]
    if kind == "unit":
        if value is not None:
            raise GeneratorError("unit schema received another carrier")
        return {"kind": "unit"}
    if kind == "natural":
        if type(value) is not int or not 0 <= value <= atom["max"]:
            raise GeneratorError("natural leaf is outside its bound")
        return {"kind": "natural", "max": atom["max"]}
    if kind == "meta-boolean":
        if type(value) is not bool:
            raise GeneratorError("meta-boolean leaf has another carrier")
        return {"kind": "meta-boolean"}
    if kind == "canonical-body":
        if (
            type(value) is not dict
            or set(value) != {"compiler", "body"}
            or value["compiler"] != atom["compiler"]
        ):
            raise GeneratorError("canonical-body leaf has another compiler")
        bytes.fromhex(value["body"])
        return {"kind": "canonical-body", "compiler": atom["compiler"]}
    if kind == "exact-profile-law":
        return {"kind": "exact-profile-law", "law": atom["law"]}
    raise GeneratorError(f"unknown atom kind {kind}")


def _enumerate(view: str, schema: dict[str, Any], value: Any) -> list[dict[str, Any]]:
    leaves: list[dict[str, Any]] = []

    def walk(node: dict[str, Any], current: Any, path: list[dict[str, int]]) -> None:
        kind = node["node"]
        if kind == "atom":
            leaves.append(
                {
                    "view": view,
                    "path": copy.deepcopy(path),
                    "boundary": _boundary(node["atom"], current),
                }
            )
            return
        if kind == "record":
            expected = [ordinal for ordinal, _ in node["fields"]]
            if type(current) is not dict or list(current) != expected:
                raise GeneratorError("record differs from compiled view schema")
            for ordinal, child in node["fields"]:
                walk(child, current[ordinal], [*path, {"step": "field", "ordinal": ordinal}])
            return
        if kind == "variant":
            if type(current) is not dict or set(current) != {"case", "value"}:
                raise GeneratorError("variant differs from compiled view schema")
            cases = dict(node["cases"])
            if current["case"] not in cases:
                raise GeneratorError("variant selects an absent case")
            walk(
                cases[current["case"]],
                current["value"],
                [*path, {"step": "variant", "ordinal": current["case"]}],
            )
            return
        if kind == "sequence":
            if type(current) is not list or len(current) > node["max"]:
                raise GeneratorError("sequence differs from compiled view schema")
            for ordinal, child_value in enumerate(current):
                walk(
                    node["element"],
                    child_value,
                    [*path, {"step": "sequence", "ordinal": ordinal}],
                )
            return
        raise GeneratorError(f"unknown schema node {kind}")

    walk(schema, value, [])
    return leaves


def _steps(spec: str) -> tuple[tuple[str, int], ...]:
    names = {"f": "field", "s": "sequence", "v": "variant"}
    result = []
    for token in spec.split():
        if len(token) < 2 or token[0] not in names or not token[1:].isdigit():
            raise GeneratorError(f"bad coordinate path {spec}")
        result.append((names[token[0]], int(token[1:])))
    return tuple(result)


def _path_key(coordinate: dict[str, Any]) -> tuple[tuple[str, int], ...]:
    return tuple((item["step"], item["ordinal"]) for item in coordinate["path"])


def _public_coin() -> tuple[ModuleType, object, object, dict[int, Any], dict[str, Any]]:
    model = _load("_zkc_f2o1_generator_d1", D1_MODEL)
    fixture = model.fixture("integrated-baseline")
    admitted = model.admit_core(fixture.candidate, fixture.environment)
    if admitted.outcome != "Affirmative" or admitted.handle is None:
        raise GeneratorError("D1 integrated-baseline Core no longer admits")
    protocol = model.admit_fresh_protocol(
        admitted.handle, fixture.protocol_candidate, fixture.environment
    )
    if protocol.outcome != "Affirmative" or protocol.handle is None:
        raise GeneratorError("D1 integrated-baseline Fresh Protocol no longer admits")
    core, scenario = model._retained_core(admitted.handle)
    if scenario != "integrated-baseline":
        raise GeneratorError("D1 authority retained another scenario")
    value, evidence = model.project_public_coin(admitted.handle)
    manifest = _enumerate("PublicCoinView", model.VIEW_SCHEMAS["PublicCoinView"], value)
    return model, fixture, core, value, {"manifest": manifest, "evidence": evidence}


def _coordinate(index: dict[tuple[tuple[str, int], ...], dict[str, Any]], spec: str) -> dict[str, Any]:
    coordinate = index.get(_steps(spec))
    if coordinate is None:
        raise GeneratorError(f"PublicCoinView has no active leaf at {spec}")
    return copy.deepcopy(coordinate)


def _source_paths() -> dict[str, str]:
    paths = {"subject.core": "f0"}
    for challenge, occurrence in enumerate((14, 15, 16)):
        prefix = f"f4 s{challenge}"
        paths.update(
            {
                f"occurrence.{occurrence}": f"{prefix} f1",
                f"challenge.{challenge}.scope": f"{prefix} f2",
                f"challenge.{challenge}.value-type": f"{prefix} f3",
                f"challenge.{challenge}.domain": f"{prefix} f4",
                f"challenge.{challenge}.fresh-ref": f"{prefix} f5",
                f"challenge.{challenge}.condition": f"{prefix} f8 s0",
            }
        )
    paths.update(
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
    return paths


def _expected_extra_ids() -> list[str]:
    ids = ["subject.core", "subject.protocol"]
    for module in range(3):
        ids.extend((f"module.{module}.decision-class", f"module.{module}.denotation"))
    for oracle in range(3):
        ids.extend((f"oracle.{oracle}.mode", f"oracle.{oracle}.carrier"))
    ids.extend(f"query.{item}.visibility" for item in QUERY_VISIBILITIES)
    for challenge in range(3):
        ids.extend(
            (
                f"challenge.{challenge}.scope",
                f"challenge.{challenge}.value-type",
                f"challenge.{challenge}.domain",
                f"challenge.{challenge}.fresh-ref",
                f"challenge.{challenge}.law",
                f"challenge.{challenge}.condition",
            )
        )
    ids.extend(
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
        )
    )
    ids.extend(
        ("reduction.0.challenge.0", "reduction.0.challenge.1", "reduction.1.challenge.0", "reduction.1.challenge.2")
    )
    ids.append("check.0.denotation")
    ids.extend(f"guard.{item}.denotation" for item in (0, 20, 21))
    for claim in range(3):
        ids.extend((f"claim.{claim}.declaration", f"claim.{claim}.premise"))
    for reduction in range(2):
        ids.extend(
            (
                f"reduction.{reduction}.declaration",
                f"reduction.{reduction}.denotation",
                f"reduction.{reduction}.premise",
            )
        )
    for terminal in range(3):
        ids.append(f"terminal.{terminal}.declaration")
    ids.extend(
        (
            "terminal.22.preemption",
            "control.logical-reject-preemption.terminal.22.preemption",
            "provider.outcome-map",
        )
    )
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


def _missing_view(construct_id: str) -> str:
    if construct_id == "subject.protocol":
        return "ExecutionView"
    if construct_id.startswith("module.") and construct_id.endswith("decision-class"):
        return "StrategyDecisionView"
    if construct_id.startswith(("oracle.", "query.", "occurrence.", "terminal.")):
        return "EffectView"
    if construct_id.startswith(("claim.", "reduction.")):
        return "ClaimReductionView"
    return "EffectView"


def _gap(construct_id: str, named_by: list[dict[str, Any]] | None = None) -> dict[str, Any]:
    gap_class = _gap_class(construct_id)
    if gap_class == "operational-owner-view":
        view = _missing_view(construct_id)
        reason = (
            f"D1 derives only PublicCoinView; it does not issue the integrated-baseline "
            f"{view} body whose leaf would determine this construct."
        )
        lives = [
            f"{D1_SOURCE}:2330-2381 implements only project_public_coin",
            f"{TARGET}:2046-2174 specifies six target owner-view bodies but is not an issued D1 body",
        ]
    elif gap_class == "operational-distribution":
        reason = "PublicCoinView names the challenge domain and Fresh law but no leaf denotes its runtime distribution."
        lives = [f"{TARGET}:2079-2088 names challenge references", f"{TARGET}:2143-2154 keeps law leaves nominal"]
    elif gap_class == "module-effect-denotation":
        reason = "The Core and authenticated semantic-module preimage classify this effect, but no issued owner-view leaf denotes its runtime transition."
        lives = [f"{D1_SOURCE}:2330-2381 projects no EffectView", f"{TARGET}:2091-2105 assigns occurrences to EffectView"]
    elif gap_class == "oracle-carrier-representation":
        reason = "The Core names the Oracle publication mode, but no issued owner-view leaf supplies the provider-side carrier representation or lookup behavior."
        lives = [f"{TARGET}:929-1125 declares Oracle modes and effects", f"{D1_SOURCE}:2330-2381 projects no EffectView"]
    elif gap_class == "operational-denotation":
        reason = "The subject carries a nominal algorithm, contract, or declaration, not the operation's denotation in the provider monad."
        lives = [f"{TARGET}:2046-2174 separates exact view leaves from semantic propositions"]
    elif gap_class == "operational-outcome-map":
        reason = "No issued owner view maps all completion, refusal, and noncompletion branches to the generated provider verdict."
        lives = [f"{TARGET}:2121-2131 assigns execution and replay facts to ExecutionView"]
    else:
        reason = "A structural owner-view leaf would not establish the claim or reduction property premise."
        lives = [f"{TARGET}:2172-2174 assigns additional propositions to Relations, Analysis, and OIR"]
    return {
        "class": gap_class,
        "reason": reason,
        "needed_for": f"generated construct {construct_id}",
        "named_by": copy.deepcopy(named_by or []),
        "lives_in": lives,
    }


def _kind(construct_id: str) -> str:
    if construct_id.startswith("occurrence."):
        return "occurrence-step"
    if construct_id.startswith("challenge."):
        return "challenge-observable"
    if construct_id.startswith("reduction.") and ".challenge." in construct_id:
        return "reduction-challenge-backlink"
    if construct_id.startswith("module."):
        return "module-effect-observable"
    if construct_id.startswith("oracle."):
        return "oracle-observable"
    if construct_id.startswith("query."):
        return "query-observable"
    if construct_id.startswith("terminal."):
        return "terminal-observable"
    if construct_id.startswith("claim."):
        return "claim-observable"
    if construct_id.startswith("reduction."):
        return "reduction-observable"
    if construct_id.startswith(("guard.", "check.")):
        return "denotation"
    if construct_id.startswith("subject."):
        return "subject-identity"
    if construct_id.startswith("control."):
        return "control-observable"
    return "outcome-map"


def _realizes(construct_id: str) -> dict[str, Any]:
    if construct_id.startswith("occurrence."):
        ordinal = int(construct_id.split(".")[1])
        effect, target = EFFECTS[ordinal]
        value: dict[str, Any] = {"occurrence": ordinal, "effect": effect}
        if target is not None:
            value["target"] = target
        if ordinal == 14:
            value.update({"sample_count": 1, "shared_value": "challenge0"})
        return value
    match = re.fullmatch(r"module\.(\d+)\.decision-class", construct_id)
    if match:
        ordinal = int(match.group(1))
        return {"occurrence": ordinal + 2, "decision_class": MODULE_DECISIONS[ordinal]}
    match = re.fullmatch(r"oracle\.(\d+)\.mode", construct_id)
    if match:
        ordinal = int(match.group(1))
        return {"oracle": ordinal, "mode": ORACLE_MODES[ordinal]}
    match = re.fullmatch(r"query\.(\d+)\.visibility", construct_id)
    if match:
        occurrence = int(match.group(1))
        return {"occurrence": occurrence, "visibility": QUERY_VISIBILITIES[occurrence]}
    match = re.fullmatch(r"reduction\.(\d+)\.declaration", construct_id)
    if match:
        reduction = int(match.group(1))
        return {"reduction": reduction, "required_challenges": list(REDUCTION_CHALLENGES[reduction])}
    if construct_id == "terminal.22.preemption":
        return {"occurrence": 22, "preempted_by": list(TERMINAL_PREEMPTION[22])}
    if construct_id == "control.logical-reject-preemption.terminal.22.preemption":
        return {
            "scenario": "logical-reject-preemption",
            "occurrence": 22,
            "verdict": "Accept",
            "preempted_by": [20, 21],
        }
    match = re.fullmatch(r"reduction\.(\d+)\.challenge\.(\d+)", construct_id)
    if match:
        return {"reduction": int(match.group(1)), "challenge": int(match.group(2))}
    return {}


class Draft:
    def __init__(self) -> None:
        self.lines: list[str] = []
        self.constructs: list[dict[str, Any]] = []

    def raw(self, line: str = "") -> None:
        self.lines.append(line)

    def add(
        self,
        code: str,
        construct_id: str,
        source: dict[str, Any],
        *,
        layer: str,
        name: str,
        consulted: list[dict[str, Any]] | None = None,
    ) -> None:
        rendered = f"{code}  {MARKER_PREFIX}{construct_id}]"
        self.lines.append(rendered)
        self.constructs.append(
            {
                "id": construct_id,
                "kind": _kind(construct_id),
                "layer": layer,
                "lean": {"line": len(self.lines), "name": name, "text": code.strip()},
                "realizes": _realizes(construct_id),
                "consulted": copy.deepcopy(consulted or []),
                "source": source,
            }
        )


def build() -> tuple[str, dict[str, Any]]:
    model, fixture, core, _value, evidence = _public_coin()
    effect_names = {"Check": "InvokeCheck", "Terminal": "ReachTerminal", "ModuleEffectRef": "ModuleEffect"}
    observed = []
    for item in core.occurrences:
        raw_name = type(item.effect).__name__.removesuffix("Effect")
        name = effect_names.get(raw_name, raw_name)
        target = getattr(
            item.effect,
            "challenge",
            getattr(
                item.effect,
                "check",
                getattr(
                    item.effect,
                    "reduction",
                    getattr(
                        item.effect,
                        "terminal",
                        getattr(item.effect, "oracle", getattr(item.effect, "query", None)),
                    ),
                ),
            ),
        )
        if name == "ModuleEffect":
            target = item.effect.declaration.local_ordinal
        observed.append((name, target))
    normalized = tuple(observed)
    if normalized != EFFECTS:
        raise GeneratorError(f"D1 occurrence schedule drifted: {normalized!r}")
    if len(core.claims) != 3 or len(core.reductions) != 2 or len(core.terminals) != 3:
        raise GeneratorError("D1 integrated carrier table census drifted")
    manifest = evidence["manifest"]
    index = {_path_key(item): item for item in manifest}
    paths = _source_paths()

    def source(construct_id: str) -> dict[str, Any]:
        if construct_id in paths:
            return {"coordinate": _coordinate(index, paths[construct_id])}
        named: list[dict[str, Any]] = []
        law = re.fullmatch(r"challenge\.(\d+)\.law", construct_id)
        if law:
            named = [_coordinate(index, paths[f"challenge.{law.group(1)}.fresh-ref"])]
        return {"no_source_coordinate": _gap(construct_id, named)}

    draft = Draft()
    draft.raw("/-")
    draft.raw("Generated by the untrusted F2-O1 generator from the admitted D1 integrated-baseline")
    draft.raw("Core and Fresh Protocol. The only realized D1 normalized owner view is PublicCoinView;")
    draft.raw("every absent projection or denotation remains an explicit ledger gap.")
    draft.raw("-/")
    draft.raw("import VCVio.OracleComp.ProbComp")
    draft.raw("")
    draft.raw("open OracleComp")
    draft.raw("")
    draft.raw("namespace ZkcF2O1")
    draft.raw("")
    draft.raw("abbrev Z3 : Type := Fin 3")
    draft.raw("")
    draft.raw("inductive Verdict where")
    draft.raw("  | accept | abort | reject")
    draft.raw("  deriving DecidableEq, Repr")
    draft.raw("")
    draft.raw("structure Ops where")
    draft.raw("  verifierMessage : Nat → ProbComp Unit")
    draft.raw("  proverMessage : Nat → ProbComp Unit")
    draft.raw("  moduleEffect : Nat → ProbComp Unit")
    draft.raw("  publishOracle : Nat → ProbComp Unit")
    draft.raw("  queryOracle : Nat → Nat → Bool → ProbComp Unit")
    draft.raw("  answerOracle : Nat → ProbComp Unit")
    draft.raw("  sampleChallenge : Nat → List Z3 → ProbComp Z3")
    draft.raw("  invokeCheck : Nat → ProbComp Unit")
    draft.raw("  applyReduction : Nat → List Z3 → ProbComp Unit")
    draft.raw("  terminalGuard : Nat → ProbComp Bool")
    draft.raw("")
    draft.raw("/- Metadata and explicit parameters: each line is ledgered independently. -/")
    for construct_id in _expected_extra_ids():
        safe = re.sub(r"[^A-Za-z0-9]", "_", construct_id)
        value = json.dumps(_realizes(construct_id), sort_keys=True, separators=(",", ":"))
        escaped = value.replace('\\', '\\\\').replace('"', '\\"')
        draft.add(
            f'def audit_{safe} : String := "{escaped}"',
            construct_id,
            source(construct_id),
            layer="metadata",
            name=f"audit_{safe}",
        )
    draft.raw("")
    draft.raw("/- One monadic operation per Core occurrence, in exact Core order. -/")
    draft.raw("def interaction (ops : Ops) : ProbComp Verdict := do")
    occurrence_code = {
        0: "  let _ ← ops.verifierMessage 0",
        1: "  let _ ← ops.proverMessage 1",
        2: "  let _ ← ops.moduleEffect 0",
        3: "  let _ ← ops.moduleEffect 1",
        4: "  let _ ← ops.moduleEffect 2",
        5: "  let _ ← ops.publishOracle 0",
        6: "  let _ ← ops.queryOracle 0 6 false",
        7: "  let _ ← ops.answerOracle 6",
        8: "  let _ ← ops.publishOracle 1",
        9: "  let _ ← ops.queryOracle 1 9 true",
        10: "  let _ ← ops.answerOracle 9",
        11: "  let _ ← ops.publishOracle 2",
        12: "  let _ ← ops.queryOracle 2 12 false",
        13: "  let _ ← ops.answerOracle 12",
        14: "  let challenge0 ← ops.sampleChallenge 0 []",
        15: "  let challenge1 ← ops.sampleChallenge 1 []",
        16: "  let challenge2 ← ops.sampleChallenge 2 [challenge1]",
        17: "  let _ ← ops.invokeCheck 0",
        18: "  let _ ← ops.applyReduction 0 [challenge0, challenge1]",
        19: "  let _ ← ops.applyReduction 1 [challenge0, challenge2]",
        20: "  let acceptActive ← ops.terminalGuard 0",
        21: "    let abortActive ← ops.terminalGuard 1",
        22: "      return Verdict.reject",
    }
    for ordinal in range(20):
        draft.add(
            occurrence_code[ordinal],
            f"occurrence.{ordinal}",
            source(f"occurrence.{ordinal}"),
            layer="interaction",
            name=f"occurrence{ordinal}",
        )
    draft.add(
        occurrence_code[20],
        "occurrence.20",
        source("occurrence.20"),
        layer="interaction",
        name="occurrence20",
    )
    draft.raw("  if acceptActive then")
    draft.raw("    return Verdict.accept")
    draft.raw("  else")
    draft.add(
        occurrence_code[21],
        "occurrence.21",
        source("occurrence.21"),
        layer="interaction",
        name="occurrence21",
    )
    draft.raw("    if abortActive then")
    draft.raw("      return Verdict.abort")
    draft.raw("    else")
    draft.add(
        occurrence_code[22],
        "occurrence.22",
        source("occurrence.22"),
        layer="interaction",
        name="occurrence22",
    )
    draft.raw("")
    draft.raw("#print axioms interaction")
    draft.raw("")
    draft.raw("end ZkcF2O1")
    lean_text = "\n".join(draft.lines) + "\n"
    gaps = [
        {
            "construct": item["id"],
            "class": item["source"]["no_source_coordinate"]["class"],
            "needed_for": item["source"]["no_source_coordinate"]["needed_for"],
        }
        for item in draft.constructs
        if "no_source_coordinate" in item["source"]
    ]
    ledger = {
        "format": LEDGER_FORMAT,
        "authority": "none; untrusted generator output",
        "marker": "-- [f2o1:<id>]",
        "subject": {
            "core_id": fixture.candidate.asserted_id.carrier(),
            "protocol_id": fixture.protocol_candidate.asserted_id.carrier(),
            "scenario": "integrated-baseline",
            "occurrence_count": len(core.occurrences),
            "view_status": {
                view: (
                    {"status": "realized", "leaf_count": len(manifest), "implementation": f"{D1_SOURCE}:2330-2381"}
                    if view == "PublicCoinView"
                    else {"status": "no_integrated_projection", "implementation_gap": f"{D1_SOURCE}:2330-2381"}
                )
                for view in VIEW_ORDER
            },
        },
        "provider": PROVIDER,
        "rendering_rules": [
            {"id": "one-occurrence-one-bind", "rule": "each Core occurrence renders as exactly one do-block construct in Core order"},
            {"id": "one-construct-one-leaf-or-gap", "rule": "each construct claims exactly one active view leaf, or one typed no_source_coordinate gap"},
            {"id": "challenge-sharing", "rule": "the shared Challenge is sampled once and the resulting value is passed to both consuming Reductions"},
            {"id": "joint-challenges", "rule": "joint member 2 receives exactly the prior joint member 1; the group and index remain separately ledgered"},
            {"id": "oracle-modes", "rule": "Oracle mode and query visibility are parameters unless an issued EffectView leaf determines them"},
            {"id": "first-active-terminal", "rule": "Accept, then Abort, then fallback Reject render as nested first-active branches"},
        ],
        "premises": [
            {"id": "d1-authentication", "statement": "D1 admission authenticates exact Core, Protocol, profile, module, algorithm, and contract bytes before projection."},
            {"id": "view-issuance-boundary", "statement": "B5B2's schema grammar does not itself issue a view body for the D1 authority; only D1 project_public_coin is treated as realized."},
        ],
        "constructs": draft.constructs,
        "gaps": gaps,
    }
    return lean_text, ledger


def write() -> None:
    lean_text, ledger = build()
    GENERATED_LEAN.parent.mkdir(parents=True, exist_ok=True)
    GENERATED_LEAN.write_text(lean_text, encoding="utf-8")
    GENERATED_LEDGER.write_text(json.dumps(ledger, indent=2, sort_keys=True) + "\n", encoding="utf-8")


if __name__ == "__main__":
    write()
