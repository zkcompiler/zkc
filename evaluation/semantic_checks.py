#!/usr/bin/env python3
"""Run the bounded semantic-redesign validation tiers without time caps."""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time


ROOT = Path(__file__).resolve().parents[1]


@dataclass(frozen=True)
class Gate:
    label: str
    runner: str
    arguments: tuple[str, ...] = ("--check",)
    fast: bool = False
    output_flag: str | None = None


GATES = (
    Gate("semantic closure", "evaluation/semantic-closure/run.py", fast=True),
    Gate(
        "published semantic profiles",
        "evaluation/semantic-profile-publication/run.py",
        fast=True,
    ),
    Gate(
        "recursive composition boundary",
        "evaluation/recursive-composition-boundary/run.py",
        fast=True,
    ),
    Gate("executable foundations", "evaluation/k1-executable-foundations/run.py"),
    Gate(
        "interactive protocol and Fiat--Shamir",
        "evaluation/k2-protocol-fiat-shamir/run.py",
        fast=True,
    ),
    Gate(
        "dependent Interface, Plan, and Relations surfaces",
        "evaluation/k3-dependent-surfaces/run.py",
        fast=True,
    ),
    Gate("indexed Core elaboration", "evaluation/indexed-core-elaboration/run.py"),
    Gate(
        "Plan continuation semantics",
        "evaluation/plan-continuation-semantics/run.py",
    ),
    Gate(
        "duplex transcript construction",
        "evaluation/duplex-sponge-transcript/run.py",
        output_flag="--output",
    ),
    Gate(
        "native FRI and logical Oracle",
        "evaluation/native-fri-ior/run.py",
        output_flag="--output",
    ),
    Gate(
        "property Analysis",
        "evaluation/k3-analysis-closure/run.py",
        arguments=("--check",),
    ),
    Gate("endpoint projection", "evaluation/k3-oir-projection/run.py"),
    Gate("joined semantic boundary", "evaluation/k3-integrated-closure/run.py"),
    Gate(
        "retained Schnorr witness",
        "evaluation/r2-p01-schnorr/run.py",
        output_flag="--output",
    ),
)


def selected_gates(tier: str) -> tuple[Gate, ...]:
    if tier == "fast":
        return tuple(gate for gate in GATES if gate.fast)
    return GATES


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--tier", choices=("fast", "full"), default="fast")
    parser.add_argument(
        "--keep-going",
        action="store_true",
        help="run later gates after a failure while retaining a failing result",
    )
    parser.add_argument("--list", action="store_true", help="list the selected gates")
    args = parser.parse_args(argv)

    gates = selected_gates(args.tier)
    if args.list:
        for gate in gates:
            print(gate.label)
        return 0

    environment = os.environ.copy()
    environment["PYTHONDONTWRITEBYTECODE"] = "1"
    failures: list[str] = []
    overall_started = time.perf_counter()
    with tempfile.TemporaryDirectory(prefix="zkc-semantic-checks-") as raw_temp:
        temp = Path(raw_temp)
        for ordinal, gate in enumerate(gates, start=1):
            print(
                f"[{ordinal}/{len(gates)}] {gate.label}",
                flush=True,
            )
            command = [
                sys.executable,
                "-B",
                str(ROOT / gate.runner),
                *gate.arguments,
            ]
            if gate.output_flag is not None:
                command.extend((gate.output_flag, str(temp / f"report-{ordinal}.json")))
            started = time.perf_counter()
            completed = subprocess.run(
                command,
                cwd=ROOT,
                env=environment,
                check=False,
                capture_output=True,
                text=True,
            )
            elapsed = time.perf_counter() - started
            if completed.returncode == 0:
                summaries = tuple(
                    line.strip()
                    for line in completed.stdout.splitlines()
                    if line.strip()
                )
                detail = f" — {summaries[-1]}" if summaries else ""
                print(
                    f"PASS {gate.label} ({elapsed:.3f}s){detail}",
                    flush=True,
                )
                continue
            failures.append(gate.label)
            if completed.stdout:
                print(completed.stdout, file=sys.stderr, end="")
            if completed.stderr:
                print(completed.stderr, file=sys.stderr, end="")
            print(
                f"FAIL {gate.label} with exit {completed.returncode} ({elapsed:.3f}s)",
                file=sys.stderr,
                flush=True,
            )
            if not args.keep_going:
                break

    elapsed = time.perf_counter() - overall_started
    if failures:
        print(
            "Semantic checks failed: " + ", ".join(failures),
            file=sys.stderr,
        )
        return 1
    print(
        f"Semantic {args.tier} tier passed {len(gates)}/{len(gates)} gates "
        f"in {elapsed:.3f}s"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
