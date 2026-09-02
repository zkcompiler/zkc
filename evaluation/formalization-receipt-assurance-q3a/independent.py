#!/usr/bin/env python3
"""Black-box mutation path for the production receipt driver."""

from __future__ import annotations

import copy
from dataclasses import dataclass
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile
from typing import Any, Callable

from model import AuditFailure, DRIVER, Finding, SIGNATURE, read_json, require


Mutator = Callable[[dict[str, Any]], None]


@dataclass(frozen=True)
class Mutation:
    name: str
    outcome: str
    code: str
    accepted: bool
    mutate: Mutator
    expected_checkable: int | None = None


@dataclass(frozen=True)
class MutationResult:
    finding: Finding
    accepted: bool
    checkable: int | None


def _receipt(signature: dict[str, Any], declaration: str) -> dict[str, Any]:
    for annotation in signature["annotations"].values():
        for receipt in annotation.get("formalization", []):
            if receipt.get("declaration") == declaration:
                return receipt
    raise AuditFailure(f"missing mutation target {declaration}")


MECHANIZED = "RandomQuery.oracleReduction_completeness"
PROOF_INCOMPLETE = "Sumcheck.Spec.reduction_perfectCompleteness"
SUBJECT_INCOMPLETE = "OracleVerifier.seqCompose_rbrSoundness"


def _set(declaration: str, field: str, value: Any) -> Mutator:
    def apply(signature: dict[str, Any]) -> None:
        _receipt(signature, declaration)[field] = value
    return apply


def _delete(declaration: str, field: str) -> Mutator:
    def apply(signature: dict[str, Any]) -> None:
        _receipt(signature, declaration).pop(field, None)
    return apply


def _mechanized_sorry(signature: dict[str, Any]) -> None:
    receipt = _receipt(signature, MECHANIZED)
    receipt["axioms"] = [*receipt["axioms"], "sorryAx"]


def _incomplete_without_sorry(signature: dict[str, Any]) -> None:
    receipt = _receipt(signature, PROOF_INCOMPLETE)
    receipt["axioms"] = [axiom for axiom in receipt["axioms"] if axiom != "sorryAx"]


def _replace_non_sorry_axiom(signature: dict[str, Any]) -> None:
    receipt = _receipt(signature, MECHANIZED)
    receipt["axioms"] = [
        "Q3A.syntheticAssumption" if axiom == "propext" else axiom
        for axiom in receipt["axioms"]
    ]


def cases() -> tuple[Mutation, ...]:
    return (
        Mutation("offline-baseline", "Affirmative", "Q3A-A-OFFLINE-BASELINE", True,
                 lambda _: None, 6),
        Mutation("empty-declaration", "Refused", "Q3A-R-DECLARATION-EMPTY", False,
                 _set(MECHANIZED, "declaration", "")),
        Mutation("wrong-arklib-pin", "Refused", "Q3A-R-PIN-MISMATCH", False,
                 _set(MECHANIZED, "revision", "0" * 40)),
        Mutation("empty-covers", "Refused", "Q3A-R-COVERS-EMPTY", False,
                 _set(MECHANIZED, "covers", "")),
        Mutation("mechanized-with-sorry", "Refused", "Q3A-R-MECHANIZED-SORRY", False,
                 _mechanized_sorry),
        Mutation("incomplete-without-sorry", "Refused", "Q3A-R-INCOMPLETE-NO-SORRY", False,
                 _incomplete_without_sorry),
        Mutation("proof-to-subject-relabel", "CannotAnswer", "Q3A-C-INCOMPLETENESS-CLASS", True,
                 _set(PROOF_INCOMPLETE, "state", "subject_incomplete"), 6),
        Mutation("subject-to-proof-relabel", "CannotAnswer", "Q3A-C-INCOMPLETENESS-CLASS-REVERSE", True,
                 _set(SUBJECT_INCOMPLETE, "state", "proof_incomplete"), 6),
        Mutation("covers-text-substitution", "CannotAnswer", "Q3A-C-COVERS-MEANING", True,
                 _set(MECHANIZED, "covers", "syntactically nonempty but unrelated text"), 6),
        Mutation("does-not-cover-deletion", "CannotAnswer", "Q3A-C-EXCLUSION-MEANING", True,
                 _delete(MECHANIZED, "does_not_cover"), 6),
        Mutation("offline-statement-substitution", "CannotAnswer", "Q3A-C-OFFLINE-STATEMENT", True,
                 _set(MECHANIZED, "statement", "@Synthetic.unrelated : True"), 6),
        Mutation("offline-nonsorry-axiom-substitution", "CannotAnswer", "Q3A-C-OFFLINE-AXIOM-SET", True,
                 _replace_non_sorry_axiom, 6),
        Mutation("unknown-incomplete-state", "CannotAnswer", "Q3A-C-DRIVER-STATE-ENUM", True,
                 _set(PROOF_INCOMPLETE, "state", "synthetic_incomplete"), 6),
        Mutation("arklib-statement-deletion", "CannotAnswer", "Q3A-C-CHECKABILITY-DOWNGRADE", True,
                 _set(MECHANIZED, "statement", ""), 5),
    )


def run_mutations() -> list[MutationResult]:
    baseline = read_json(SIGNATURE)
    results: list[MutationResult] = []
    for case in cases():
        candidate = copy.deepcopy(baseline)
        case.mutate(candidate)
        with tempfile.TemporaryDirectory(prefix="zkc-q3a-") as directory:
            path = Path(directory) / "signature.json"
            path.write_text(json.dumps(candidate), encoding="utf-8")
            completed = subprocess.run(
                [sys.executable, "-B", str(DRIVER), str(path)],
                cwd=DRIVER.parents[3],
                capture_output=True,
                text=True,
                check=False,
            )
        accepted = completed.returncode == 0
        output = completed.stdout + completed.stderr
        match = re.search(r"formalization receipts: (\d+) checkable", output)
        checkable = int(match.group(1)) if match else None
        require(
            accepted == case.accepted,
            f"mutation {case.name}: expected accepted={case.accepted}, "
            f"got rc={completed.returncode}: {output[-500:]}",
        )
        if case.expected_checkable is not None:
            require(
                checkable == case.expected_checkable,
                f"mutation {case.name}: expected {case.expected_checkable} checkable, "
                f"got {checkable}",
            )
        results.append(
            MutationResult(Finding(case.name, case.outcome, case.code), accepted, checkable)
        )
    return results


if __name__ == "__main__":
    for result in run_mutations():
        print(
            f"{result.finding.name}: {result.finding.outcome}/{result.finding.code} "
            f"accepted={result.accepted} checkable={result.checkable}"
        )
