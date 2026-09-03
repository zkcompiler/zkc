#!/usr/bin/env python3
"""Regenerate the read-only index of open items from the public sources.

An open item is anything the repository has recorded as unanswered or
unresolved in a ledger that has an owner and a closure rule:

- a ``CannotAnswer`` finding in a research package's frozen findings, which
  the package gate keeps until the package is refrozen with another outcome;
  and
- a reopening record under ``docs-next/notes``, which the v0 design program's
  change control keeps until its decision gate changes an owner page or
  rejects the reopening.

This module does not decide anything and closes nothing. It emits one JSON
report and one Markdown index so that the complete open set can be read in
one place without editing any ledger by hand. The private tracking ledgers
are merged by a separate script outside the public tree.
"""

from __future__ import annotations

import argparse
from collections.abc import Iterable, Mapping
import json
from pathlib import Path
import re
from typing import Any

from checks import run


ROOT = run.ROOT
DEFAULT_EVALUATION = ROOT / "evaluation"
DEFAULT_NOTES = ROOT / "docs-next" / "notes"
FINDINGS_FILE = "expected-findings.json"
CODE_PATTERN = re.compile(r"\A[A-Z0-9]+(?:-[A-Z0-9]+)+\Z")
REOPENING_GLOB = "**/*-reopening-*.md"
STATE_PREFIX = "> **State:**"


class OpenItemsError(ValueError):
    """A public open-item source is malformed."""


def _strict_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise OpenItemsError(f"duplicate JSON key: {key!r}")
        result[key] = value
    return result


OUTCOMES = frozenset(
    {
        "Affirmative",
        "Negative",
        "Unsupported",
        "MissingDependency",
        "CannotAnswer",
        "Refused",
        "KindMismatch",
        "Malformed",
        "DeterministicLimitExceeded",
        "CheckerFailure",
    }
)


def _walk(node: Any, path: tuple[str, ...], rows: list[tuple[str, str, str]]) -> None:
    """Collect every finding in a frozen findings tree, whatever its layout.

    A finding is an object carrying string ``outcome`` and ``code`` fields with
    the outcome drawn from the owner-defined partition, or a bare
    ``[name, outcome, code]`` / ``[outcome, code]`` list; the packages froze
    their findings in several such layouts and the index reads them all
    without preferring one.
    """

    if isinstance(node, dict):
        outcome, code = node.get("outcome"), node.get("code")
        if isinstance(outcome, str) and isinstance(code, str) and outcome in OUTCOMES:
            name = node.get("name") or node.get("id") or node.get("case")
            if not isinstance(name, str) or not name:
                name = path[-1] if path else code
            rows.append((name, outcome, code))
        for key, value in node.items():
            _walk(value, path + (str(key),), rows)
    elif isinstance(node, list):
        if (
            2 <= len(node) <= 3
            and all(isinstance(item, str) and item for item in node)
            and node[-2] in OUTCOMES
        ):
            if len(node) == 3:
                rows.append((node[0], node[1], node[2]))
            else:
                rows.append((node[1], node[0], node[1]))
            return
        for index, item in enumerate(node):
            _walk(item, path + (str(index),), rows)


def _load_findings(path: Path) -> list[tuple[str, str, str]]:
    try:
        raw = json.loads(path.read_bytes(), object_pairs_hook=_strict_object)
    except (OSError, json.JSONDecodeError) as error:
        raise OpenItemsError(f"cannot load {path}: {error}") from error
    rows: list[tuple[str, str, str]] = []
    _walk(raw, (), rows)
    if not rows:
        raise OpenItemsError(f"{path}: no findings found (no outcome/code pairs)")
    unique: list[tuple[str, str, str]] = []
    seen: set[tuple[str, str, str]] = set()
    for row in rows:
        if row not in seen:
            seen.add(row)
            unique.append(row)
    return unique


def _source(path: Path, root: Path) -> str:
    try:
        return str(path.relative_to(ROOT))
    except ValueError:
        return str(path.relative_to(root))


def collect_cannot_answer(evaluation: Path = DEFAULT_EVALUATION) -> list[dict[str, str]]:
    items: list[dict[str, str]] = []
    for path in sorted(evaluation.glob(f"*/{FINDINGS_FILE}")):
        package = path.parent.name
        for name, outcome, code in _load_findings(path):
            if outcome != "CannotAnswer":
                continue
            items.append(
                {
                    "kind": "cannot-answer",
                    "package": package,
                    "finding": name,
                    "code": code,
                    "source": _source(path, evaluation),
                }
            )
    return items


def _state_of(text: str) -> str:
    lines = text.splitlines()
    for index, line in enumerate(lines):
        if line.startswith(STATE_PREFIX):
            parts = [line[len(STATE_PREFIX) :].strip()]
            for later in lines[index + 1 :]:
                if not later.startswith("> ") or later.startswith("> **"):
                    break
                parts.append(later[2:].strip())
            return " ".join(part for part in parts if part)
    return ""


def collect_reopening_records(notes: Path = DEFAULT_NOTES) -> list[dict[str, str]]:
    items: list[dict[str, str]] = []
    for path in sorted(notes.glob(REOPENING_GLOB)):
        try:
            text = path.read_text(encoding="utf-8")
        except OSError as error:
            raise OpenItemsError(f"cannot read {path}: {error}") from error
        title = next(
            (line[2:].strip() for line in text.splitlines() if line.startswith("# ")),
            path.stem,
        )
        items.append(
            {
                "kind": "reopening-record",
                "title": title,
                "state": _state_of(text),
                "source": _source(path, notes),
            }
        )
    return items


def audit(
    cannot_answer: Iterable[Mapping[str, str]],
    reopening_records: Iterable[Mapping[str, str]],
) -> list[dict[str, str]]:
    """Return structural findings.

    Findings with ``blocking`` true make the check fail: a malformed code or a
    reopening record without a state. A code shared by two findings of one
    package is reported without blocking, because the code still names one
    open item; the index then shows two evidence rows for it.
    """

    findings: list[dict[str, str]] = []
    seen: dict[tuple[str, str], str] = {}
    for item in cannot_answer:
        code = item["code"]
        if not CODE_PATTERN.match(code):
            findings.append(
                {
                    "kind": "malformed-code",
                    "blocking": True,
                    "detail": f"{item['source']}: {item['finding']!r} has code {code!r}",
                }
            )
        key = (item["package"], code)
        if item["finding"] == "aggregate":
            # A package's aggregate reuses the code of the finding that decides
            # it; that shared code is the design, not a collision.
            continue
        if key in seen and seen[key] != item["finding"]:
            findings.append(
                {
                    "kind": "duplicate-code",
                    "blocking": False,
                    "detail": f"{item['source']}: code {code!r} is shared by "
                    f"{seen[key]!r} and {item['finding']!r}",
                }
            )
        seen.setdefault(key, item["finding"])
    for record in reopening_records:
        if not record["state"]:
            findings.append(
                {
                    "kind": "missing-state",
                    "blocking": True,
                    "detail": f"{record['source']}: no `> **State:**` line",
                }
            )
    return findings


def build_report(
    evaluation: Path = DEFAULT_EVALUATION, notes: Path = DEFAULT_NOTES
) -> dict[str, Any]:
    cannot_answer = collect_cannot_answer(evaluation)
    records = collect_reopening_records(notes)
    findings = audit(cannot_answer, records)
    blocking = [finding for finding in findings if finding["blocking"]]
    packages = sorted({item["package"] for item in cannot_answer})
    return {
        "schema_version": 1,
        "outcome": "pass" if not blocking else "fail",
        "findings": findings,
        "summary": {
            "cannot_answer_items": len(cannot_answer),
            "packages_with_cannot_answer": len(packages),
            "reopening_records": len(records),
        },
        "cannot_answer": cannot_answer,
        "reopening_records": records,
    }


def render_markdown(report: Mapping[str, Any]) -> str:
    lines = [
        "# Open items (generated)",
        "",
        "This index is regenerated by `checks.open_items`; do not edit it. Every",
        "row belongs to the ledger named in its source column and closes only",
        "there.",
        "",
        "## Reopening records",
        "",
        "| Record | State | Source |",
        "|---|---|---|",
    ]
    for record in report["reopening_records"]:
        lines.append(f"| {record['title']} | {record['state']} | `{record['source']}` |")
    lines += ["", "## `CannotAnswer` findings by package", ""]
    by_package: dict[str, list[Mapping[str, str]]] = {}
    for item in report["cannot_answer"]:
        by_package.setdefault(item["package"], []).append(item)
    for package in sorted(by_package):
        lines.append(f"### `{package}`")
        lines.append("")
        lines.append("| Finding | Code |")
        lines.append("|---|---|")
        for item in by_package[package]:
            lines.append(f"| {item['finding']} | `{item['code']}` |")
        lines.append("")
    summary = report["summary"]
    lines += [
        "## Summary",
        "",
        f"- `CannotAnswer` findings: {summary['cannot_answer_items']} across "
        f"{summary['packages_with_cannot_answer']} packages",
        f"- reopening records: {summary['reopening_records']}",
        "",
    ]
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="exit 1 on findings")
    parser.add_argument("--output", type=Path, help="write the JSON report here")
    parser.add_argument(
        "--markdown", type=Path, help="write the Markdown index here (default: beside --output)"
    )
    args = parser.parse_args(argv)
    try:
        report = build_report()
    except OpenItemsError as error:
        print(f"open items error: {error}")
        return 1
    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
        markdown = args.markdown or args.output.with_suffix(".md")
        markdown.write_text(render_markdown(report))
    summary = report["summary"]
    print(
        f"open items: {summary['cannot_answer_items']} CannotAnswer findings in "
        f"{summary['packages_with_cannot_answer']} packages, "
        f"{summary['reopening_records']} reopening records, "
        f"{len(report['findings'])} structural findings "
        f"({sum(1 for f in report['findings'] if f['blocking'])} blocking)"
    )
    for finding in report["findings"]:
        marker = "blocking" if finding["blocking"] else "observation"
        print(f"  - {finding['kind']} ({marker}): {finding['detail']}")
    if args.check and report["outcome"] != "pass":
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
