#!/usr/bin/env python3
"""Measure which declared outcomes a witness can actually reach.

A witness declares its boundaries and codes in source.  Whether any input drives
them is a separate question, and the gap between the two is where a witness
stops being evidence without looking any different from outside.  Three defects
found on 2026-08-24 shared that shape, and one of them was exactly this: two
judgments in the Schnorr witness carried five named codes and a real
affirmative, and nothing anywhere called them.

So this tool answers the question by running, not by reading:

    declared    every code appearing in a witness's model sources
    fired       every code an actually-constructed result carried while the
                witness's own test suite ran
    unreachable declared minus fired

It works by wrapping the result type each witness builds its judgments through
-- ``Result`` or ``CheckResult`` in the witness's ``terms`` module -- so every
construction is recorded wherever it happens.  Nothing in the witness is edited
and no test is modified; a run that reports nothing fired is a run that failed
to instrument, and says so rather than reporting a clean sweep.

An unreachable code is not automatically a defect.  A witness may declare a
refusal for an input its fixtures cannot currently build, and saying so plainly
is honest.  What is a defect is not knowing which ones those are.

One limit worth stating: only judgment results are instrumented.  A report layer
that publishes a case through its own record type rather than through a judgment
-- ``P01-RPT-100`` is the one current instance -- is invisible here, and should
be, because a declared contract is not a reached boundary.

Run from the repository root:

    python3 evaluation/reachability.py
    python3 evaluation/reachability.py --witness r2-p01-schnorr
    python3 evaluation/reachability.py --json
"""

from __future__ import annotations

import argparse
import importlib
import io
import json
import os
from pathlib import Path
import re
import sys
from typing import Any, Iterable
import unittest


REPO_ROOT = Path(__file__).resolve().parents[1]
EVALUATION = REPO_ROOT / "evaluation"

#: A witness's codes look like ``P01-ALG-003``, ``R2-FS-001``, ``R2-LOGUP-017``, or
#: ``P01-SAT-OK``.  Some witnesses name a section and some go straight to a
#: number, so the part after the prefix cannot be required to start with a
#: letter -- requiring it reported three witnesses as declaring no codes at all
#: while they were plainly firing them.
CODE = re.compile(r'"((?:P\d{2}|R2)-[A-Z0-9]+(?:-[A-Z0-9]+)*)"')

#: Result types are frozen dataclasses, so the recording wrapper goes on the
#: class rather than on any one construction site.
RESULT_TYPES = ("Result", "CheckResult")


def witnesses() -> list[Path]:
    return sorted(
        path
        for path in EVALUATION.iterdir()
        if path.is_dir() and path.name.startswith("r2")
    )


def _model_package(witness: Path) -> Path:
    for child in sorted(witness.iterdir()):
        if child.is_dir() and child.name.endswith("model"):
            return child
    raise RuntimeError(f"{witness.name} has no model package")


def declared_codes(witness: Path) -> dict[str, str]:
    """Every code the witness's model sources name, mapped to its source file.

    Keeping the file makes the result actionable: an unreachable code is much
    easier to act on when the count is grouped by the module that declares it,
    because unreached codes cluster in unreached modules rather than scattering.
    """

    package = _model_package(witness)
    found: dict[str, str] = {}
    for source in sorted(package.glob("*.py")):
        for code in CODE.findall(source.read_text()):
            found.setdefault(code, source.name)
    return found


def _import_fresh(witness: Path, dotted: str) -> Any:
    """Import a witness module as part of its own package.

    Each witness owns a package name of its own, but they share module names
    inside it, so anything previously imported under that root is dropped first.
    """

    if str(witness) not in sys.path:
        sys.path.insert(0, str(witness))
    root = dotted.split(".")[0]
    for stale in [name for name in sys.modules if name.split(".")[0] == root]:
        del sys.modules[stale]
    return importlib.import_module(dotted)


def _instrument(terms: Any, sink: list[tuple[str, str, str]]) -> int:
    """Record every result the witness constructs.  Returns how many types were wrapped."""

    wrapped = 0
    for name in RESULT_TYPES:
        result_type = getattr(terms, name, None)
        if result_type is None or not isinstance(result_type, type):
            continue
        original = result_type.__init__

        def recording(self: Any, *args: Any, __original: Any = original, **kwargs: Any) -> None:
            __original(self, *args, **kwargs)
            outcome = getattr(self, "outcome", None)
            sink.append(
                (
                    getattr(outcome, "value", str(outcome)),
                    str(getattr(self, "boundary", "")),
                    str(getattr(self, "code", "")),
                )
            )

        result_type.__init__ = recording  # type: ignore[method-assign]
        wrapped += 1
    return wrapped


def _run_tests(witness: Path) -> tuple[int, int]:
    """Run the witness's own suite in this process.  Returns (run, failures).

    Discovery mirrors how each witness runs itself -- ``unittest discover -s
    tests`` from the witness root -- because the suites resolve fixture paths
    relative to that directory and put their own package on ``sys.path``.
    """

    previous = Path.cwd()
    tests = witness / "tests"
    try:
        os.chdir(witness)
        loader = unittest.TestLoader()
        suite = loader.discover(start_dir=str(tests), top_level_dir=str(tests))
        runner = unittest.TextTestRunner(stream=io.StringIO(), verbosity=0)
        outcome = runner.run(suite)
    finally:
        os.chdir(previous)
    return outcome.testsRun, len(outcome.failures) + len(outcome.errors)


def _build_report(witness: Path, package: str) -> bool:
    """Drive the witness's report layer, where it has one.

    Two witnesses publish their evidence through a frozen oracle rather than
    through their tests alone, so a judgment can be reached by the report and by
    nothing else.  Counting only the suite would report those as unreachable.
    """

    if not (witness / package / "report.py").exists():
        return False
    previous = Path.cwd()
    try:
        os.chdir(witness)
        report_module = importlib.import_module(f"{package}.report")
        report_module.build_report(REPO_ROOT)
    except Exception:  # noqa: BLE001 - a report that cannot build is a finding
        return False
    finally:
        os.chdir(previous)
    return True


def measure(witness: Path) -> dict[str, Any]:
    package = _model_package(witness).name
    sink: list[tuple[str, str, str]] = []
    terms = _import_fresh(witness, f"{package}.terms")
    wrapped = _instrument(terms, sink)
    if not wrapped:
        raise RuntimeError(f"{witness.name}: no result type to instrument")

    reported = _build_report(witness, package)
    tests_run, failures = _run_tests(witness)
    fired = {triple[2] for triple in sink if triple[2]}
    declared = declared_codes(witness)
    unreachable = sorted(set(declared) - fired)
    by_source: dict[str, int] = {}
    for code in unreachable:
        by_source[declared[code]] = by_source.get(declared[code], 0) + 1
    return {
        "witness": witness.name,
        "report_built": reported,
        "tests_run": tests_run,
        "test_failures": failures,
        "results_constructed": len(sink),
        "declared": sorted(declared),
        "fired": sorted(fired),
        "unreachable_by_source": dict(sorted(by_source.items(), key=lambda kv: -kv[1])),
        # A code fired but never declared in the model sources means a code
        # built somewhere other than the model -- in a test, say -- which is a
        # different defect and worth seeing.
        "fired_but_undeclared": sorted(fired - set(declared)),
        "unreachable": unreachable,
        "boundaries": sorted({triple[1] for triple in sink if triple[1]}),
    }


def report(names: Iterable[str] | None = None) -> dict[str, Any]:
    selected = [w for w in witnesses() if names is None or w.name in set(names)]
    if not selected:
        raise RuntimeError("no witness selected")
    return {"witnesses": [measure(w) for w in selected]}


def render(data: dict[str, Any]) -> str:
    lines = [
        f"{'witness':<22}{'tests':>6}{'results':>9}{'declared':>10}"
        f"{'fired':>7}{'unreachable':>13}"
    ]
    total_declared = total_fired = 0
    for entry in data["witnesses"]:
        total_declared += len(entry["declared"])
        total_fired += len(entry["fired"])
        flag = "  FAILURES" if entry["test_failures"] else ""
        lines.append(
            f"{entry['witness']:<22}{entry['tests_run']:>6}"
            f"{entry['results_constructed']:>9}{len(entry['declared']):>10}"
            f"{len(entry['fired']):>7}{len(entry['unreachable']):>13}{flag}"
        )
    lines.append("")
    for entry in data["witnesses"]:
        if entry["unreachable_by_source"]:
            worst = ", ".join(
                f"{name} {count}" for name, count in entry["unreachable_by_source"].items()
            )
            lines.append(f"  {entry['witness']}: unreachable by source -- {worst}")
    lines.append("")
    for entry in data["witnesses"]:
        if entry["fired_but_undeclared"]:
            lines.append(
                f"{entry['witness']}: fired but not declared in the model -- "
                + ", ".join(entry["fired_but_undeclared"])
            )
    share = (100 * total_fired / total_declared) if total_declared else 0.0
    lines.append(
        f"declared {total_declared}  fired {total_fired}  "
        f"unreachable {total_declared - total_fired}  ({share:.0f}% reached)"
    )
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--witness", action="append", dest="witness")
    parser.add_argument("--json", action="store_true")
    parser.add_argument(
        "--list-unreachable",
        action="store_true",
        help="print every unreachable code rather than only the count",
    )
    args = parser.parse_args(argv)

    data = report(args.witness)
    if args.json:
        print(json.dumps(data, indent=2, sort_keys=True))
        return 0
    print(render(data))
    if args.list_unreachable:
        for entry in data["witnesses"]:
            if entry["unreachable"]:
                print(f"\n{entry['witness']} ({len(entry['unreachable'])} unreachable):")
                for code in entry["unreachable"]:
                    print(f"  {code}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
