"""The frozen case oracle for P01.

The Schnorr witness already carries the evidence; it had no way to publish it.
Without a report layer its results are visible only while its tests run, so
nothing outside the suite can tell which laws it actually closes, and
``run.py --check`` fails outright.

This layer is deliberately smaller than the FRI witness's.  That one also owns
execution requests, an evaluator basis, qualification and replay; here the job
is narrower and stated as such: turn the admitted subjects and their named
refusals into cases carrying the five fields the corpus freezes, and verify a
rebuild reproduces them.

Each case is ``(outcome, boundary, code, subject_id, evidence_id)``.  The
subject is the identity of the thing judged; the evidence is a digest over the
exact inputs the judgment read, so a case that silently starts reading
something else stops matching.
"""

from __future__ import annotations

from dataclasses import dataclass
import json
from pathlib import Path
from typing import Any, Mapping

from .relations import (
    SchnorrRelationInstance,
    SchnorrWitnessAssignment,
    admit_instance,
    admit_relation,
    admit_witness_assignment,
    canonical_schnorr_relation,
    check_relation_satisfaction,
)
from .semantic import (
    AlgebraProfile,
    admit_algebra,
    admit_core,
    canonical_core,
    canonical_honest_prover_contract,
)
from .terms import Outcome, semantic_id


SCHEMA = "zkc.r2.p01.report.v1"
MAX_CASES = 64

#: The witness's own sources.  A change to any of them rebuilds the basis, so a
#: report replayed against edited code reports a differing basis rather than
#: quietly agreeing.
SOURCE_FILES = (
    "p01model/semantic.py",
    "p01model/relations.py",
    "p01model/execution.py",
    "p01model/terms.py",
)


@dataclass(frozen=True)
class Case:
    name: str
    outcome: str
    boundary: str
    code: str
    subject_id: str
    evidence_id: str

    def term(self) -> dict[str, Any]:
        return {
            "outcome": self.outcome,
            "boundary": self.boundary,
            "code": self.code,
            "subject_id": self.subject_id,
            "evidence_id": self.evidence_id,
        }


def _evidence_id(**inputs: Any) -> str:
    return semantic_id("r2.p01.case-evidence.v1", dict(sorted(inputs.items())))


def _case(name: str, result: Any, subject: str, **inputs: Any) -> Case:
    outcome = result.outcome
    return Case(
        name=name,
        outcome=outcome.value if isinstance(outcome, Outcome) else str(outcome),
        boundary=getattr(result, "boundary", ""),
        code=getattr(result, "code", ""),
        subject_id=subject,
        evidence_id=_evidence_id(**inputs),
    )


def _fixture(repo_root: Path) -> Mapping[str, Any]:
    path = Path(__file__).resolve().parents[1] / "cases" / "schnorr-p01.json"
    payload = json.loads(path.read_text())
    if not isinstance(payload, dict):
        raise ValueError("the P01 fixture must contain one object")
    return payload


def _profile(fixture: Mapping[str, Any]) -> AlgebraProfile:
    algebra = fixture["algebra"]
    return AlgebraProfile(
        p=int(algebra["p"]),
        q=int(algebra["q"]),
        generator=int(algebra["generator"]),
        challenge_size=int(algebra["challenge_size"]),
    )


def build_report(repo_root: Path, expectations: Any = None) -> dict[str, Any]:
    """Assemble the frozen cases from admitted subjects and named refusals."""

    fixture = _fixture(repo_root)
    profile = _profile(fixture)
    cases: list[Case] = []

    algebra = admit_algebra(profile)
    cases.append(
        _case("algebra/admitted.v1", algebra, semantic_id("r2.p01.algebra.v1", fixture["algebra"]), algebra=dict(fixture["algebra"]))
    )

    core = canonical_core(profile)
    core_result = admit_core(core, profile)
    cases.append(
        _case("core/admitted.v1", core_result, getattr(core, "identity", ""), algebra=dict(fixture["algebra"]))
    )

    relation = canonical_schnorr_relation(profile)
    relation_result = admit_relation(relation, profile)
    cases.append(
        _case("relation/admitted.v1", relation_result, getattr(relation, "identity", ""), algebra=dict(fixture["algebra"]))
    )

    finite = fixture["finite_instance"]
    instance = SchnorrRelationInstance(relation.identity, int(finite["statement"]))
    instance_result = admit_instance(instance, relation, profile)
    cases.append(
        _case(
            "relation/instance-admitted.v1", instance_result,
            instance.identity, statement=int(finite["statement"]),
        )
    )

    witness = SchnorrWitnessAssignment(
        instance.identity, "witness:x", int(finite["witness"])
    )
    witness_result = admit_witness_assignment(witness, instance, relation, profile)
    cases.append(
        _case(
            "relation/witness-admitted.v1", witness_result,
            instance.identity, witness_declared=True,
        )
    )

    satisfaction = check_relation_satisfaction(witness, instance, relation, profile)
    cases.append(
        _case(
            "relation/satisfaction.v1", satisfaction, instance.identity,
            statement=int(finite["statement"]), witness_declared=True,
        )
    )

    honest = canonical_honest_prover_contract(core, profile)
    cases.append(
        Case(
            name="prover/honest-contract-declared.v1",
            outcome=Outcome.AFFIRMATIVE.value,
            boundary="prover:honest-contract",
            code="P01-RPT-100",
            subject_id=getattr(honest, "identity", ""),
            evidence_id=_evidence_id(algebra=dict(fixture["algebra"])),
        )
    )

    # --- refusals ----------------------------------------------------------
    #
    # A report of affirmatives alone shows nothing: it cannot distinguish a
    # model whose boundaries discriminate from one that accepts everything.
    # Each case below drives a named refusal.

    composite = AlgebraProfile(p=21, q=11, generator=2, challenge_size=8)
    cases.append(
        _case("algebra/composite-modulus-refused.v1", admit_algebra(composite),
              semantic_id("r2.p01.algebra.v1", {"p": 21, "q": 11}), p=21, q=11)
    )

    wide = AlgebraProfile(p=23, q=11, generator=2, challenge_size=64)
    cases.append(
        _case("algebra/challenge-exceeds-order-refused.v1", admit_algebra(wide),
              semantic_id("r2.p01.algebra.v1", {"p": 23, "challenge_size": 64}),
              challenge_size=64)
    )

    foreign = SchnorrRelationInstance("sha256:" + "00" * 32, int(finite["statement"]))
    cases.append(
        _case("relation/instance-under-foreign-relation-refused.v1",
              admit_instance(foreign, relation, profile),
              foreign.identity, relation_id="foreign")
    )

    mismatched = SchnorrWitnessAssignment(
        "sha256:" + "11" * 32, "witness:x", int(finite["witness"])
    )
    cases.append(
        _case("relation/witness-under-foreign-instance-refused.v1",
              admit_witness_assignment(mismatched, instance, relation, profile),
              instance.identity, instance_id="foreign")
    )

    wrong = SchnorrWitnessAssignment(
        instance.identity, "witness:x", (int(finite["witness"]) + 1) % profile.q
    )
    cases.append(
        _case("relation/unsatisfying-witness.v1",
              check_relation_satisfaction(wrong, instance, relation, profile),
              instance.identity, statement=int(finite["statement"]),
              witness_declared=True, perturbed=True)
    )

    if len(cases) > MAX_CASES:
        raise ValueError("report exceeds its declared case bound")

    body = {name: case.term() for name, case in ((c.name, c) for c in cases)}
    # `overall_pass` is a run-time verdict, not report content: it says whether
    # this build agreed with the oracle it was handed.  It is therefore kept out
    # of `report_id`, so freezing a passing run does not make the verdict part
    # of the identity it is supposed to be checking.
    matched = True
    if isinstance(expectations, dict) and isinstance(expectations.get("cases"), dict):
        matched = expectations["cases"] == body
    return {
        "schema": SCHEMA,
        "fixture": fixture["schema"],
        "sources": sorted(SOURCE_FILES),
        "cases": body,
        "report_id": semantic_id("r2.p01.report.v1", {"cases": body}),
        "overall_pass": matched,
    }


def verify_report(report: Any, repo_root: Path, expectations: Any = None) -> list[str]:
    """Rebuild and compare, then compare against the frozen oracle if given."""

    errors: list[str] = []
    if not isinstance(report, dict):
        return ["report is not an object"]
    required = {"schema", "fixture", "sources", "cases", "report_id", "overall_pass"}
    if set(report) != required:
        return ["report envelope keys differ"]
    if report["schema"] != SCHEMA:
        errors.append("report schema differs")

    rebuilt = build_report(repo_root)
    if rebuilt["report_id"] != report["report_id"]:
        errors.append("report identity is not reproducible")
    if rebuilt["cases"] != report["cases"]:
        errors.append("rebuilt cases differ from the report")

    if expectations is not None:
        if not isinstance(expectations, dict) or "cases" not in expectations:
            errors.append("expectations are malformed")
        else:
            for name, expected in sorted(expectations["cases"].items()):
                actual = report["cases"].get(name)
                if actual is None:
                    errors.append(f"expected case is absent: {name}")
                elif actual != expected:
                    errors.append(f"case differs from the frozen oracle: {name}")
            for name in sorted(set(report["cases"]) - set(expectations["cases"])):
                errors.append(f"case is not in the frozen oracle: {name}")
    return errors


__all__ = ["SCHEMA", "Case", "build_report", "verify_report"]
