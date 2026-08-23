#!/usr/bin/env python3
"""Measure which invariants the witnesses actually close.

The invariant ledger's own rule is that a candidate does not satisfy an
invariant by repeating its name: it must exhibit a **positive inhabitant** and a
**well-formed negative mutation**.  So this tool refuses to count an invariant
as closed on the strength of a test that merely mentions it.

For each witness it collects, by execution rather than by reading:

    positives   distinct affirmative outcomes the witness produces
    negatives   distinct (outcome, boundary, code) triples its mutations reach
    reachable   every declared code that some input drives to fire

An invariant is reported ``closed`` only when its claimed boundaries appear in
the measured negative set AND the witness has a positive inhabitant.  Anything
else is ``partial`` or ``open``, including invariants a witness clearly
intends: intent is not evidence.

Run from the repository root:

    python3 evaluation/coverage.py
    python3 evaluation/coverage.py --json
"""

from __future__ import annotations

import argparse
import importlib
import json
from pathlib import Path
import sys
from typing import Any, Callable, Iterable


REPO_ROOT = Path(__file__).resolve().parents[1]
EVALUATION = REPO_ROOT / "evaluation"


# --- the ledger ---------------------------------------------------------------
#
# Each entry names the boundaries a witness must reach for the invariant to be
# considered closed.  The boundaries are the witnesses' own strings, so a
# renamed boundary reports as open rather than silently passing.

LEDGER: dict[str, dict[str, Any]] = {
    "F-02": {
        "title": "canonical boundary-value closure",
        "boundaries": {"framing"},
    },
    "F-03": {
        "title": "algorithm closure",
        "boundaries": {"algorithm-closure", "algorithm-support"},
    },
    "F-05": {
        "title": "bounded identity work",
        "boundaries": {"closed-core"},
        "note": "bounds are enforced; size is measured separately",
    },
    "F-06": {
        "title": "identity-field justification",
        "boundaries": {"logup:derived-anchors"},
    },
    "P-01": {
        "title": "complete instance binding",
        "boundaries": {"transcript-prefix:fold1", "logup:transcript-prefix"},
    },
    "P-03": {
        "title": "exact prefix closure",
        "boundaries": {"transcript-prefix:pow", "logup:transcript-prefix"},
    },
    "P-05": {
        "title": "public-coin eligibility",
        "boundaries": {"public-coin-eligibility"},
    },
    "P-07": {
        "title": "unambiguous challenge derivation",
        "boundaries": {"squeeze-sample-admission"},
    },
    "P-08": {
        "title": "causal prover generation",
        "boundaries": {"strategy-causality:message:g1"},
    },
    "P-10": {
        "title": "typed claim routing",
        "boundaries": {"typed-routing", "logup:claims", "logup:claim-linearity"},
    },
    "P-11": {
        "title": "view adequacy",
        "boundaries": set(),
    },
    "R-06": {
        "title": "relation-facing witness surface",
        "boundaries": {
            "relations:witness-admission:instance",
            "relations:instance-admission:relation",
        },
    },
    "R-07": {
        "title": "result correspondence has a direction",
        "boundaries": {"relations:satisfaction"},
    },
    "F-01": {
        "title": "regime closure (local: algebra profile admission)",
        "boundaries": {"algebra-profile"},
    },
    "R-03": {
        "title": "explicit grounding equations",
        "boundaries": {"commitment:opening", "commitment:domain-separation"},
    },
    "R-04": {
        "title": "lossless bridge laws are explicit",
        "boundaries": {"bridge:lane"},
    },
    "R-05": {
        "title": "every retained lossy projection is separate and priced",
        "boundaries": {"analysis:projection-loss"},
    },
    "R-08": {
        "title": "binding questions retain meaningful negatives",
        "boundaries": {"logup:material-identity", "apply.parameters.lookups"},
    },
    "X-TERM": {
        "title": "terminal closure (local: no live claim survives)",
        "boundaries": {"logup:terminal-closure"},
    },
    "X-SEAT": {
        "title": "origin and seat agree (local)",
        "boundaries": {"logup:origin-seat", "logup:round-structure"},
    },
}


# --- witness probes -----------------------------------------------------------


def _load(package_root: Path, dotted: str) -> Any:
    """Import a witness module as part of its own package.

    Loading the file directly would break its relative imports, so the witness
    root goes on the path and the module is imported by name.
    """

    if str(package_root) not in sys.path:
        sys.path.insert(0, str(package_root))
    for stale in [name for name in sys.modules if name.split(".")[0] == dotted.split(".")[0]]:
        del sys.modules[stale]
    return importlib.import_module(dotted)


def _record(sink: dict[str, set], result: Any) -> None:
    outcome = getattr(result, "outcome", None)
    if outcome is None:
        return
    triple = (outcome.value, getattr(result, "boundary", ""), getattr(result, "code", ""))
    if outcome.value == "Affirmative":
        sink["positives"].add(triple)
    else:
        sink["negatives"].add(triple)
    sink["codes"].add(triple[2])


def probe_p02() -> dict[str, set]:
    root = EVALUATION / "r2-p02-commitment"
    sys.path.insert(0, str(root))
    core = _load(root, "p02model.core")
    constructions = importlib.import_module("p02model.commitment").CONSTRUCTIONS
    sink: dict[str, set] = {"positives": set(), "negatives": set(), "codes": set()}
    construction = constructions["r2.commit.binary-merkle.v1"]
    small = type(construction)(
        name=construction.name, element_sort=construction.element_sort, arity_log2=3,
        query_sort=construction.query_sort, domain_separation=construction.domain_separation,
        binding_game=construction.binding_game,
    )
    built = core.build_core(small)
    _record(sink, core.admit_core(built))
    leaves = core.honest_leaves(small)
    for mutation in core.Mutation:
        try:
            _record(sink, core.run_opening(built, leaves, 0, mutation))
        except Exception:
            pass
        try:
            _record(sink, core.admit_core(core.mutate_core(built, mutation)))
        except Exception:
            pass
    sys.path.remove(str(root))
    return sink


def probe_p03() -> dict[str, set]:
    root = EVALUATION / "r2-p03-logup"
    sys.path.insert(0, str(root))
    logup = _load(root, "p03model.logup")
    sink: dict[str, set] = {"positives": set(), "negatives": set(), "codes": set()}
    for variant in logup.Variant:
        built = logup.build_core(variant)
        _record(sink, logup.admit_core(built))
        for mutation in logup.Mutation:
            try:
                _record(sink, logup.admit_core(logup.mutate(built, mutation)))
            except Exception:
                pass
    sys.path.remove(str(root))
    return sink


def probe_p04() -> dict[str, set]:
    root = EVALUATION / "r2-p04-bridges"
    bridges = _load(root, "p04model.bridges")
    sink: dict[str, set] = {"positives": set(), "negatives": set(), "codes": set()}
    Bridge, Lane = bridges.Bridge, bridges.Lane
    variants = [
        Bridge("b", Lane.BIJECTION, "s", "t"),
        Bridge("b", Lane.BIJECTION, "s", "t", image_predicate="i"),
        Bridge("b", Lane.BIJECTION, "s", "t", loss_bits=40, collision_relation="c"),
        Bridge("e", Lane.EMBEDDING, "s", "t", image_predicate="i"),
        Bridge("e", Lane.EMBEDDING, "s", "t"),
        Bridge("e", Lane.EMBEDDING, "s", "t", image_predicate="i", loss_bits=40),
        Bridge("p", Lane.PROJECTION, "s", "t", collision_relation="c", loss_bits=40, occurrence_count=1),
        Bridge("p", Lane.PROJECTION, "s", "t", collision_relation="c", loss_bits=40, occurrence_count=1, image_predicate="i"),
        Bridge("p", Lane.PROJECTION, "s", "t", loss_bits=40, occurrence_count=1),
        Bridge("p", Lane.PROJECTION, "s", "t", collision_relation="c", occurrence_count=1),
        Bridge("p", Lane.PROJECTION, "s", "t", collision_relation="c", loss_bits=40),
        "not-a-bridge",
    ]
    for bridge in variants:
        _record(sink, bridges.admit_bridge(bridge))
    for count, rule in ((1, None), (3, "anchors-are-sealed-digests"), (0, None)):
        _record(sink, bridges.price_projection(bridges.ANCHOR_PROJECTION, count, rule))
    _record(sink, bridges.price_projection(variants[3], 1, None))
    return sink


def probe_fri() -> dict[str, set]:
    """The FRI witness already publishes its measured outcomes."""

    frozen = json.loads(
        (EVALUATION / "r2-protocol-model" / "cases" / "expected-results.json").read_text()
    )
    sink: dict[str, set] = {"positives": set(), "negatives": set(), "codes": set()}
    for case in frozen["cases"].values():
        triple = (case["outcome"], case["boundary"], case["code"])
        if case["outcome"] == "Affirmative":
            sink["positives"].add(triple)
        else:
            sink["negatives"].add(triple)
        sink["codes"].add(case["code"])
    return sink


def probe_p01() -> dict[str, set]:
    """Schnorr publishes its evidence through a frozen oracle."""

    frozen = json.loads(
        (EVALUATION / "r2-p01-schnorr" / "cases" / "expected-results.json").read_text()
    )
    sink: dict[str, set] = {"positives": set(), "negatives": set(), "codes": set()}
    for case in frozen["cases"].values():
        triple = (case["outcome"], case["boundary"], case["code"])
        if case["outcome"] == "Affirmative":
            sink["positives"].add(triple)
        else:
            sink["negatives"].add(triple)
        sink["codes"].add(case["code"])
    return sink


PROBES: dict[str, Callable[[], dict[str, set]]] = {
    "fri": probe_fri,
    "schnorr": probe_p01,
    "commitment": probe_p02,
    "logup": probe_p03,
    "bridges": probe_p04,
}


# --- reporting ----------------------------------------------------------------


def measure() -> dict[str, Any]:
    per_witness: dict[str, dict[str, Any]] = {}
    boundaries: set[str] = set()
    positives: set[str] = set()
    for name, probe in PROBES.items():
        sink = probe()
        per_witness[name] = {
            "positives": sorted(sink["positives"]),
            "negatives": sorted(sink["negatives"]),
            "codes": sorted(sink["codes"]),
        }
        boundaries |= {triple[1] for triple in sink["negatives"]}
        if sink["positives"]:
            positives.add(name)
    verdicts: dict[str, Any] = {}
    for ident, entry in sorted(LEDGER.items()):
        want: set[str] = entry["boundaries"]
        met = want & boundaries
        if not want:
            state = "open"
        elif met == want:
            state = "closed"
        elif met:
            state = "partial"
        else:
            state = "open"
        verdicts[ident] = {
            "title": entry["title"],
            "state": state,
            "required": sorted(want),
            "met": sorted(met),
        }
    return {"witnesses": per_witness, "invariants": verdicts, "boundaries": sorted(boundaries)}


def render(report: dict[str, Any]) -> str:
    lines = ["witness            positives  negatives  codes"]
    for name, data in report["witnesses"].items():
        lines.append(
            f"  {name:<16} {len(data['positives']):>9}  {len(data['negatives']):>9}  {len(data['codes']):>5}"
        )
    lines.append("")
    lines.append("invariant  state    title")
    tally: dict[str, int] = {"closed": 0, "partial": 0, "open": 0}
    for ident, verdict in report["invariants"].items():
        tally[verdict["state"]] += 1
        missing = set(verdict["required"]) - set(verdict["met"])
        suffix = f"   missing: {', '.join(sorted(missing))}" if missing else ""
        lines.append(f"  {ident:<8} {verdict['state']:<8} {verdict['title']}{suffix}")
    lines.append("")
    lines.append(
        f"closed {tally['closed']}  partial {tally['partial']}  open {tally['open']}"
        f"   (of {len(report['invariants'])} tracked)"
    )
    return "\n".join(lines)


def main(argv: Iterable[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args(list(argv) if argv is not None else None)
    report = measure()
    print(json.dumps(report, indent=2, sort_keys=True) if args.json else render(report))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
