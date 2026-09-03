#!/usr/bin/env python3
"""Independent checker for the finite Schnorr provider interpretation.

This program does not import the generator.  It re-derives the six views by
the cold canonical-byte path, checks the three certificate maps, executes the
portable-term evaluator and the pinned provider with Lean, and compares every
finite input and generated trace.  Its Python terminal projection is the
temporary reading required while the separate terminal mechanization is
absent.
"""

from __future__ import annotations

import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import time
from types import ModuleType
from typing import Any


ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
CERTIFICATE = HERE / "generated/certificate.json"
PROVIDER_MODULE = HERE / "generated/SchnorrProvider.lean"
TERM_PROBE = HERE / "TermEvaluatorProbe.lean"
SCHNORR_COLD_VIEWS = (
    ROOT / "evaluation/formal-source-view-bodies-f0v2b1/independent.py"
)
TERM_KERNEL = ROOT / "evaluation/formal-kernel-mechanization-m0/lean"
TERM_VECTORS = (
    ROOT / "evaluation/formal-kernel-mechanization-m0/vectors/m2-term-calculus.json"
)
INTEGRATED_VIEW_FINDINGS = (
    ROOT
    / "evaluation/formal-source-integrated-views-f0v2b2d3/expected-findings.json"
)
PREMISE_NOTE = (
    ROOT
    / "docs-next/notes/semantic-revalidation-and-redesign/formal-assurance-research"
    / "analysis-named-premise-intake.md"
)
INTERACTIVE_CORE = ROOT / "docs-next/pir/interactive-core.md"

CERTIFICATE_FORMAT = "zkc.formal-provider-interpretation.certificate.v0"
PROVIDER_REVISION = "de0a3108140e3e04a7ebf0075aa110b459ee6e8a"
PROVIDER_DEFAULT = Path("/tmp/zkc-f0-sources.b66lUO/VCVio")
LEAN_VERSION = "4.33.1"
TIMEOUT = 180


class CheckerError(RuntimeError):
    """The independent correspondence check could not complete exactly."""


def _load(name: str, path: Path) -> ModuleType:
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:  # pragma: no cover - host failure
        raise ImportError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def _require(condition: bool, detail: str) -> None:
    if not condition:
        raise CheckerError(detail)


def _canonical(value: Any) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode("utf-8")


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _run(
    argv: list[str], cwd: Path, *, env: dict[str, str] | None = None
) -> tuple[subprocess.CompletedProcess[str], float]:
    started = time.perf_counter()
    completed = subprocess.run(
        argv,
        cwd=cwd,
        env=env,
        check=False,
        capture_output=True,
        text=True,
        timeout=TIMEOUT,
    )
    return completed, time.perf_counter() - started


def _cold_source() -> dict[str, Any]:
    cold = _load("_provider_checker_cold_views", SCHNORR_COLD_VIEWS)
    core, protocol = cold._admit()
    candidate = cold.build_candidate(core, protocol)
    views = candidate["values"]
    manifests = candidate["requested_manifests"]
    return {
        "cold": cold,
        "core": core,
        "protocol": protocol,
        "views": views,
        "source_digest": candidate["source_digest"],
        "body_sha256": {
            name: hashlib.sha256(_canonical(body)).hexdigest()
            for name, body in views.items()
        },
        "active_leaf_counts": {name: len(manifests[name]) for name in views},
    }


def _natural(cold: ModuleType, leaf: Any) -> int:
    value = cold.owner.k1.decode_datum(bytes.fromhex(leaf["body"]))
    _require(type(value) is cold.owner.k1.Nat, "owner ordinal is not a natural")
    return value.value


def _check_certificate(certificate: dict[str, Any], source: dict[str, Any]) -> dict[str, Any]:
    _require(certificate.get("format") == CERTIFICATE_FORMAT, "certificate format drifted")
    subject = certificate.get("subject")
    _require(type(subject) is dict, "certificate subject is absent")
    _require(
        subject
        == {
            "source_digest": source["source_digest"],
            "body_sha256": source["body_sha256"],
            "active_leaf_counts": source["active_leaf_counts"],
            "core_id": source["core"].core_id.carrier(),
            "protocol_id": source["protocol"].protocol_id.carrier(),
        },
        "certificate names another admitted source or six-view body set",
    )
    provider = certificate.get("provider")
    _require(
        provider
        == {
            "name": "VCVio",
            "revision": PROVIDER_REVISION,
            "toolchain": "leanprover/lean4:v4.33.1",
            "module": "Examples.Schnorr.SigmaProtocol",
            "definition": "Schnorr.sigma",
        },
        "certificate provider pin drifted",
    )
    _require(
        certificate.get("lean_sha256") == _sha256(PROVIDER_MODULE),
        "certificate does not bind the provider module",
    )

    integrated_digest = _sha256(INTEGRATED_VIEW_FINDINGS)
    _require(
        certificate["inputs"]["integrated_six_view_findings_sha256"]
        == integrated_digest,
        "integrated six-view input drifted",
    )
    vectors = json.loads(TERM_VECTORS.read_text(encoding="utf-8"))
    for name in ("check", "guard"):
        expected = vectors["algorithms"][name]
        observed = certificate["inputs"]["algorithms"][name]
        _require(
            observed["preimage_sha256"] == expected["preimage_sha256"]
            and observed["preimage_length"] == expected["preimage_length"],
            f"{name} algorithm preimage drifted",
        )

    candidate = certificate["inputs"]["candidates"]
    _require(candidate["protocol_id"] == subject["protocol_id"], "candidate binds another Protocol")
    _require(
        candidate["algebra"]["scalar_modulus"] == 3
        and candidate["algebra"]["group_order"] == 3
        and candidate["algebra"]["generator"] == 1
        and candidate["algebra"]["relation"] == "Y = x . G",
        "relation candidate has another finite algebra",
    )
    _require(
        candidate["plan"]
        == {
            "decision_order": [0, 2],
            "commit": {
                "formula": "A := r",
                "input_kinds": ["PrivateRandomness"],
                "state_binding": "ReplaceState",
            },
            "respond": {
                "formula": "z := r + c*x mod 3",
                "input_kinds": ["StateBefore", "PlanRead", "PrivateMaterial"],
                "challenge_occurrence": 1,
                "state_binding": "KeepState",
            },
        },
        "Plan candidate has another recipe or order",
    )
    return vectors


def _check_maps(certificate: dict[str, Any], source: dict[str, Any]) -> dict[str, Any]:
    cold = source["cold"]
    views = source["views"]
    effect_names = {0: "ProverMessage", 2: "Challenge", 3: "Check", 5: "Terminal"}
    occurrences = [
        {
            "occurrence": _natural(cold, row[0]),
            "effect": effect_names[row[3]["case"]],
        }
        for row in views["EffectView"][1]
    ]
    mapping = certificate.get("occurrence_to_step")
    _require(type(mapping) is list and len(mapping) == len(occurrences) == 6, "schedule map is not total")
    _require(
        [row["occurrence"] for row in mapping] == list(range(6))
        and len({row["step"] for row in mapping}) == 6,
        "schedule map aliases or reorders occurrences",
    )
    _require(
        all(
            row["occurrence"] == occurrence["occurrence"]
            and row["effect"] == occurrence["effect"]
            for row, occurrence in zip(mapping, occurrences)
        ),
        "schedule map changes an owner occurrence kind",
    )
    decisions = {
        _natural(cold, row[0]) for row in views["StrategyDecisionView"][1]
    }
    prover_steps = {row["occurrence"] for row in mapping if row["actor"] == "Prover"}
    _require(decisions == prover_steps == {0, 2}, "Prover step map differs from StrategyDecisionView")

    expected_type_map = [
        ("PublicBindingView.public_inputs[0]", "Stmt", "ZMod 3"),
        ("RelationInterface.private_witness[0]", "Wit", "ZMod 3"),
        ("EffectView.occurrences[0].outputs[0]", "Commit", "ZMod 3"),
        ("ProverPlan.persistent_state[0]", "PrvState", "ZMod 3"),
        ("PublicCoinView.challenges[0].value_type", "Chal", "ZMod 3"),
        ("EffectView.occurrences[2].outputs[0]", "Resp", "ZMod 3"),
        ("EffectView.occurrences[3].outputs[0]", "verify result", "Bool"),
    ]
    observed_type_map = [
        (row.get("source"), row.get("provider"), row.get("carrier"))
        for row in certificate.get("type_map", [])
    ]
    _require(observed_type_map == expected_type_map, "type map is incomplete or reordered")
    effect_rows = views["EffectView"][1]
    challenge_rows = views["PublicCoinView"][4]
    _require(len(challenge_rows) == 1, "source has another challenge cardinality")
    z3_bodies = [effect_rows[index][4][0]["body"] for index in (0, 1, 2)]
    _require(
        len(set(z3_bodies + [challenge_rows[0][3]["body"]])) == 1,
        "message and challenge source types differ",
    )
    _require(effect_rows[3][4][0]["body"] != z3_bodies[0], "Check output is not distinct Bool")

    execution = views["ExecutionView"][6]
    execution_outputs = [
        (_natural(cold, row[0]), len(row[1])) for row in execution[0]
    ]
    _require(
        execution_outputs == [(0, 1), (1, 1), (2, 1), (3, 1), (4, 0), (5, 0)],
        "ExecutionView has another completed-record output schema",
    )
    execution_challenges = [
        (_natural(cold, row[0]), _natural(cold, row[1]), row[2]["body"])
        for row in execution[1]
    ]
    _require(
        execution_challenges == [(0, 1, challenge_rows[0][3]["body"])],
        "ExecutionView challenge receipt does not name the public-coin site",
    )
    _require(execution[2] == [], "finite Fresh subject unexpectedly has Oracle receipts")
    execution_terminals = [
        (
            _natural(cold, row[0]),
            _natural(cold, row[1]),
            row[2]["case"],
            len(row[3]),
        )
        for row in execution[3]
    ]
    _require(
        execution_terminals == [(0, 4, 0, 0), (1, 5, 1, 0)],
        "ExecutionView has another ordered first-active terminal schema",
    )
    provider_text = PROVIDER_MODULE.read_text(encoding="utf-8")
    for fragment in (
        "abbrev Z3 : Type := ZMod 3",
        "Schnorr.sigma Z3 Z3 generator",
        "def freshChallenge : ProbComp Z3 := $ᵗ Z3",
        "def candidateCommit (nonce : Z3) : Z3 := nonce",
        "nonce + challenge * witness",
    ):
        _require(fragment in provider_text, f"provider artifact omits {fragment!r}")

    lane_map = certificate.get("lane_map")
    _require(
        type(lane_map) is list
        and [row.get("lane") for row in lane_map]
        == ["Accepted", "Rejected", "OperationalNoncompletion"],
        "reachable lane map is not total in source order",
    )
    _require(
        lane_map[0].get("image") == "true"
        and lane_map[1].get("image") == "false"
        and lane_map[2].get("image") is None,
        "lane-map evidence has another Boolean boundary",
    )
    premise_text = PREMISE_NOTE.read_text(encoding="utf-8")
    owner_text = INTERACTIVE_CORE.read_text(encoding="utf-8")
    _require(
        "Missing provider images\nare `CannotAnswer`, not collapse to `false`, `None`, or `Rejected`."
        in premise_text,
        "named-premise non-collapse rule drifted",
    )
    _require(
        "no lane is\nrelabeled as another" in owner_text,
        "PIR outcome-carrier non-collapse rule drifted",
    )
    return {
        "occurrences": occurrences,
        "decisions": sorted(decisions),
        "execution_output_occurrences": [
            occurrence for occurrence, arity in execution_outputs if arity
        ],
        "execution_terminals": execution_terminals,
        "mapped_lanes": sum(row.get("image") is not None for row in lane_map),
        "reachable_lanes": len(lane_map),
    }


def _parse_rows(
    output: str, prefix: str, fields: int, key_fields: int | None = None
) -> dict[tuple[int, ...], tuple[int, ...]]:
    rows: dict[tuple[int, ...], tuple[int, ...]] = {}
    for line in output.splitlines():
        parts = line.split("\t")
        if not parts or parts[0] != prefix:
            continue
        _require(len(parts) == fields + 1, f"{prefix} row has another arity")
        values = tuple(int(item) for item in parts[1:])
        key = values[: fields - 1 if key_fields is None else key_fields]
        _require(key not in rows, f"{prefix} row repeats an input")
        rows[key] = values
    return rows


def _run_term_evaluator() -> tuple[dict[tuple[int, ...], int], dict[int, int], dict[str, float]]:
    lake = str(Path.home() / ".elan/bin/lake")
    build, build_seconds = _run([lake, "build", "M0"], TERM_KERNEL)
    _require(build.returncode == 0, f"term-kernel build failed: {build.stdout}{build.stderr}")
    probe, probe_seconds = _run([lake, "env", "lean", str(TERM_PROBE)], TERM_KERNEL)
    _require(probe.returncode == 0, f"term-evaluator probe failed: {probe.stdout}{probe.stderr}")
    terms = _parse_rows(probe.stdout, "TERM", 5)
    guards = _parse_rows(probe.stdout, "GUARD", 2)
    _require(len(terms) == 81, "term evaluator did not cover all 81 inputs")
    _require(len(guards) == 2, "term evaluator did not cover both guard inputs")
    return (
        {key: row[-1] for key, row in terms.items()},
        {key[0]: row[-1] for key, row in guards.items()},
        {"term_build_seconds": build_seconds, "term_probe_seconds": probe_seconds},
    )


def _overlay_mathlib(provider: Path, overlay: Path) -> Path:
    original = provider / ".lake/packages/mathlib/.lake/build/lib/lean/Mathlib"
    _require(original.is_dir(), "provider Mathlib build is absent")
    destination = overlay / "Mathlib"
    destination.mkdir()
    for child in original.iterdir():
        if child.name != "Algebra":
            os.symlink(child, destination / child.name)
    algebra = destination / "Algebra"
    algebra.mkdir()
    for child in (original / "Algebra").iterdir():
        if child.name != "Field":
            os.symlink(child, algebra / child.name)
    field = algebra / "Field"
    field.mkdir()
    for child in (original / "Algebra/Field").iterdir():
        if not child.name.startswith("ZMod"):
            os.symlink(child, field / child.name)
    return field / "ZMod.olean"


def _run_provider() -> tuple[dict[tuple[int, ...], int], dict[tuple[int, ...], tuple[int, ...]], dict[str, Any]]:
    provider = Path(os.environ.get("ZKC_VCVIO_ROOT", str(PROVIDER_DEFAULT))).resolve()
    _require(provider.is_dir(), f"pinned provider tree is absent: {provider}")
    revision, revision_seconds = _run(["git", "rev-parse", "HEAD"], provider)
    _require(
        revision.returncode == 0 and revision.stdout.strip() == PROVIDER_REVISION,
        "provider revision differs from the pin",
    )
    lake = str(Path.home() / ".elan/bin/lake")
    version, version_seconds = _run([lake, "env", "lean", "--version"], provider)
    _require(
        version.returncode == 0 and f"version {LEAN_VERSION}" in version.stdout,
        "provider Lean toolchain differs from the pin",
    )
    with tempfile.TemporaryDirectory(
        prefix=".provider-overlay-", dir=HERE
    ) as temporary:
        overlay = Path(temporary)
        field_output = _overlay_mathlib(provider, overlay)
        field_source = provider / ".lake/packages/mathlib/Mathlib/Algebra/Field/ZMod.lean"
        field_build, field_seconds = _run(
            [lake, "env", "lean", "-o", str(field_output), str(field_source)], provider
        )
        _require(
            field_build.returncode == 0,
            f"provider field support build failed: {field_build.stdout}{field_build.stderr}",
        )
        search, search_seconds = _run([lake, "env", "printenv", "LEAN_PATH"], provider)
        _require(search.returncode == 0, "provider Lean search path is unavailable")
        environment = dict(os.environ)
        environment["LEAN_PATH"] = str(overlay) + os.pathsep + search.stdout.strip()
        lean = str(Path.home() / ".elan/bin/lean")
        execution, execution_seconds = _run(
            [lean, str(PROVIDER_MODULE)], provider, env=environment
        )
    _require(
        execution.returncode == 0,
        f"provider module failed: {execution.stdout}{execution.stderr}",
    )
    _require("sorryAx" not in execution.stdout, "provider module depends on a sorry axiom")
    for declaration in ("commitMatchesCandidate", "respondMatchesCandidate"):
        _require(
            f"'ZkcProviderInterpretation.{declaration}' depends on axioms:" in execution.stdout,
            f"provider artifact did not kernel-check {declaration}",
        )
    checks = _parse_rows(execution.stdout, "CHECK", 5)
    runs = _parse_rows(execution.stdout, "RUN", 8, key_fields=4)
    _require(len(checks) == 81, "provider verifier did not cover all 81 inputs")
    _require(len(runs) == 81, "provider execution did not cover all 81 inputs")
    return (
        {key: row[-1] for key, row in checks.items()},
        runs,
        {
            "provider_root": str(provider),
            "provider_revision": revision.stdout.strip(),
            "lean_version": version.stdout.strip(),
            "provider_axiom_lines": [
                line for line in execution.stdout.splitlines() if "depends on axioms" in line
            ],
            "revision_seconds": revision_seconds,
            "version_seconds": version_seconds,
            "field_support_seconds": field_seconds,
            "search_path_seconds": search_seconds,
            "provider_execution_seconds": execution_seconds,
        },
    )


def _compare(
    terms: dict[tuple[int, ...], int],
    guards: dict[int, int],
    provider_checks: dict[tuple[int, ...], int],
    provider_runs: dict[tuple[int, ...], tuple[int, ...]],
    certificate: dict[str, Any],
    maps: dict[str, Any],
) -> dict[str, Any]:
    domain = {
        (statement, commitment, challenge, response)
        for statement in range(3)
        for commitment in range(3)
        for challenge in range(3)
        for response in range(3)
    }
    _require(set(terms) == set(provider_checks) == domain, "Check domains differ")
    for key in sorted(domain):
        statement, commitment, challenge, response = key
        closed = int(response == (commitment + challenge * statement) % 3)
        _require(
            terms[key] == provider_checks[key] == closed,
            f"Check disagreement at {key}",
        )
    _require(guards == {0: 0, 1: 1}, "guard is not the term evaluator's identity")

    step_for = {row["occurrence"]: row["step"] for row in certificate["occurrence_to_step"]}
    record_occurrences = maps["execution_output_occurrences"]
    terminal_occurrence = {
        terminal_case: occurrence
        for _terminal_ref, occurrence, terminal_case, _public_outputs
        in maps["execution_terminals"]
    }
    _require(record_occurrences == [0, 1, 2, 3], "completed-record order drifted")
    _require(terminal_occurrence == {0: 4, 1: 5}, "terminal case map drifted")
    accepted = 0
    rejected = 0
    traces = 0
    for key, row in sorted(provider_runs.items()):
        _require(len(key) == 4, "provider run key has another shape")
        statement, witness, nonce, challenge = key
        commitment, response, verdict = row[4:7]
        last_occurrence = row[-1]
        expected_commitment = nonce
        expected_response = (nonce + challenge * witness) % 3
        expected_verdict = int(
            expected_response == (expected_commitment + challenge * statement) % 3
        )
        expected_terminal = terminal_occurrence[0 if expected_verdict else 1]
        _require(
            commitment == expected_commitment
            and response == expected_response
            and verdict == expected_verdict
            and last_occurrence == expected_terminal,
            f"Plan, verifier, or first-active terminal disagrees at {(statement, witness, nonce, challenge)}",
        )
        output_for_occurrence = {
            0: commitment,
            1: challenge,
            2: response,
            3: verdict,
        }
        source_trace = [
            (occurrence, output_for_occurrence[occurrence])
            for occurrence in record_occurrences
        ] + [(expected_terminal, verdict)]
        provider_trace = [
            (step_for[0], commitment),
            (step_for[1], challenge),
            (step_for[2], response),
            (step_for[3], verdict),
            (step_for[expected_terminal], verdict),
        ]
        _require(
            [value for _occurrence, value in source_trace]
            == [value for _step, value in provider_trace],
            "completed source record and provider trace differ",
        )
        _require(
            [step_for[occurrence] for occurrence, _value in source_trace]
            == [step for step, _value in provider_trace],
            "trace step map does not preserve occurrence order",
        )
        traces += 1
        accepted += expected_verdict
        rejected += 1 - expected_verdict
    _require(traces == 81, "trace comparison is not total")
    return {
        "check_inputs": len(domain),
        "guard_inputs": len(guards),
        "plan_runs": len(provider_runs),
        "accepted_runs": accepted,
        "rejected_runs": rejected,
        "trace_comparisons": traces,
    }


def check() -> dict[str, Any]:
    certificate = json.loads(CERTIFICATE.read_text(encoding="utf-8"))
    source = _cold_source()
    vectors = _check_certificate(certificate, source)
    maps = _check_maps(certificate, source)
    terms, guards, term_timings = _run_term_evaluator()
    provider_checks, provider_runs, provider = _run_provider()
    comparisons = _compare(
        terms, guards, provider_checks, provider_runs, certificate, maps
    )
    vector_closed = {
        tuple(int(part) for part in row["name"].split("/")[1].split("-")): int(row["closed_form"])
        for row in vectors["check_cases"]
    }
    _require(vector_closed == terms, "term probe differs from the frozen finite vectors")

    terminal_mechanizations = list(ROOT.glob("evaluation/*terminal*mechanization*"))
    _require(not terminal_mechanizations, "a terminal mechanization landed; replace the pending reading")

    findings = [
        ["schedule-clause", "Affirmative", "F2O2-A-SCHEDULE"],
        ["values-clause", "Affirmative", "F2O2-A-VALUES"],
        ["checks-and-guards-clause", "Affirmative", "F2O2-A-CHECKS-GUARDS"],
        ["terminals-clause", "CannotAnswer", "F2O2-C-TERMINALS-CLAUSE-4"],
        ["traces-clause", "Affirmative", "F2O2-A-TRACES"],
        ["terminal-mechanized-reading", "CannotAnswer", "F2O2-C-TERMINAL-MECHANIZATION-PENDING"],
        ["residual-provider-trust-listed", "Affirmative", "F2O2-A-RESIDUAL-PROVIDER-TRUST"],
        ["residual-evaluator-differential-listed", "Affirmative", "F2O2-A-RESIDUAL-DIFFERENTIAL"],
        ["residual-premises-listed", "Affirmative", "F2O2-A-RESIDUAL-PREMISES"],
        ["residual-checker-adapter-listed", "Affirmative", "F2O2-A-RESIDUAL-ADAPTER"],
        ["complete-schnorr-correspondence", "CannotAnswer", "F2O2-C-TERMINALS-CLAUSE-4"],
    ]
    return {
        "aggregate": "CannotAnswer/F2O2-C-TERMINALS-CLAUSE-4",
        "finding_codes": findings,
        "blocker": {
            "clause": "entry contract Section 4 clause 4, lines 71-75",
            "outcome": "CannotAnswer",
            "code": "F2O2-C-TERMINALS-CLAUSE-4",
            "reason": "OperationalNoncompletion is reachable but the specified Boolean verifier carrier has no non-collapsing image.",
            "owner_basis": "docs-next/pir/interactive-core.md lines 1990-2003 and analysis named-premise text lines 2246-2253 on the inspected branch; the tracked research note mirrors the rule at lines 425-430",
        },
        "subject": certificate["subject"],
        "provider": provider,
        "measurements": {
            "views": len(source["views"]),
            "active_view_leaves": sum(source["active_leaf_counts"].values()),
            **maps,
            **comparisons,
        },
        "timings": term_timings,
        "residual_trust": [
            "Lean kernel and VCVio OracleComp semantics",
            "finite differential evidence between the portable-term evaluator and Python",
            "Fresh distribution premise and provider outcome-carrier premise",
            "unproved checker adapter",
        ],
        "nonclaims": [
            "No protocol or cryptographic property is established.",
            "No theorem applicability is established.",
            "No correspondence is established for another subject or provider.",
        ],
    }


def main() -> int:
    try:
        report = check()
    except (CheckerError, OSError, ValueError, KeyError, subprocess.TimeoutExpired) as error:
        print(f"provider interpretation check failed: {error}", file=sys.stderr)
        return 1
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
