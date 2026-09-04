#!/usr/bin/env python3
"""Independently check the finite ArkLib Fiat--Shamir correspondence."""

from __future__ import annotations

from collections import Counter
from dataclasses import asdict
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import time
from types import ModuleType
from typing import Any, Callable


ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
CERTIFICATE = HERE / "generated/certificate.json"
PROVIDER_MODULE = HERE / "generated/FiatShamirSchnorrArkLib.lean"
TEMPLATE = HERE / "template.lean"
TERM_PROBE = HERE / "TermEvaluatorProbe.lean"

SOURCE_PACKAGE = ROOT / "evaluation/formal-source-fs-runtime-f0v3c"
SOURCE_MODEL = SOURCE_PACKAGE / "model.py"
SOURCE_EXECUTOR = SOURCE_PACKAGE / "executor.py"
SOURCE_REPLAY = SOURCE_PACKAGE / "replay.py"
SOURCE_VIEWS = SOURCE_PACKAGE / "views.py"
SOURCE_RUNS = SOURCE_PACKAGE / "expected-runs-one-shot.json"
SOURCE_TABLE = SOURCE_PACKAGE / "derivation-vectors-one-shot.json"
RETRYING_RUNS = SOURCE_PACKAGE / "expected-runs.json"
RETRYING_TABLE = SOURCE_PACKAGE / "derivation-vectors.json"
BASE_MODULE = (
    ROOT
    / "evaluation/formal-provider-interpretation-arklib-f2o3/generated"
    / "SchnorrArkLib.lean"
)
TERM_KERNEL = ROOT / "evaluation/formal-kernel-mechanization-m0/lean"
TERM_VECTORS = (
    ROOT / "evaluation/formal-kernel-mechanization-m0/vectors/m2-term-calculus.json"
)
TERMINAL_MECHANIZATION = TERM_KERNEL / "M0/Terminal.lean"

INTERACTIVE_CORE = ROOT / "docs-next/pir/interactive-core.md"
FIAT_SHAMIR = ROOT / "docs-next/pir/fiat-shamir.md"
ANALYSIS_MODEL = ROOT / "docs-next/analysis/analysis-model.md"
OWNER_PAGES = (INTERACTIVE_CORE, FIAT_SHAMIR, ANALYSIS_MODEL)
PROFILE_MANIFESTS = (
    ROOT / "docs-next/foundation/semantic-profile-manifests.json",
    ROOT / "docs-next/pir/profiles/interaction.json",
    ROOT / "docs-next/analysis/profiles/kernel.json",
)
PACKAGE_INPUTS = (
    TEMPLATE,
    TERM_PROBE,
    SOURCE_MODEL,
    SOURCE_EXECUTOR,
    SOURCE_REPLAY,
    SOURCE_VIEWS,
    SOURCE_RUNS,
    SOURCE_TABLE,
    RETRYING_RUNS,
    RETRYING_TABLE,
    BASE_MODULE,
    TERM_VECTORS,
    TERMINAL_MECHANIZATION,
)

CERTIFICATE_FORMAT = "zkc.formal-provider-interpretation.fs-arklib.certificate.v0"
PROVIDER_REVISION = "fad5cbf808774838924dc8273715724c6a6caa1f"
PROVIDER_TREE = "e38383088598a1305c15447c53db309ccd6b35ee"
VCVIO_REVISION = "cbd4144b51d92da00dd50f05e068b2348fa6e529"
VCVIO_TREE = "28c268057ed58427973e5bbf4854d472a7088954"
PROVIDER_DEFAULT = Path("/home/wonjae/code/ArkLib")
PROVIDER_SOURCE_FILES = (
    "ArkLib/OracleReduction/Basic.lean",
    "ArkLib/OracleReduction/Execution.lean",
    "ArkLib/OracleReduction/ProtocolSpec/Basic.lean",
    "ArkLib/OracleReduction/FiatShamir/Basic.lean",
    "lake-manifest.json",
    "lean-toolchain",
)
LEAN_VERSION = "4.31.0"
TIMEOUT = 240
LANES = (
    "Accepted",
    "Rejected",
    "Aborted",
    "InterpretationFailed",
    "StrategyStopped",
    "OperationalNoncompletion",
)


class CheckerError(RuntimeError):
    """The independent evidence does not satisfy one exact obligation."""


def _require(condition: bool, detail: str) -> None:
    if not condition:
        raise CheckerError(detail)


def _load(name: str, path: Path) -> ModuleType:
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise ImportError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def _wire(value: Any) -> bytes:
    return json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=True
    ).encode("ascii")


def _digest(value: Any) -> str:
    return hashlib.sha256(_wire(value)).hexdigest()


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _file_pins(paths: tuple[Path, ...]) -> dict[str, str]:
    return {path.relative_to(ROOT).as_posix(): _sha256(path) for path in paths}


def _read_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


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


def _external_git_env() -> dict[str, str]:
    environment = dict(os.environ)
    for name in (
        "GIT_OBJECT_DIRECTORY",
        "GIT_ALTERNATE_OBJECT_DIRECTORIES",
        "GIT_INDEX_FILE",
        "GIT_WORK_TREE",
    ):
        environment.pop(name, None)
    return environment


def _owner_gate() -> None:
    fs = FIAT_SHAMIR.read_text(encoding="utf-8")
    core = INTERACTIVE_CORE.read_text(encoding="utf-8")
    for token in (
        'ProtocolDeclarationRef<"pir.fs-application-domain">',
        "one nonempty semantic symbol and no other",
        "ChallengeNamespaceOctets(T, c, i)",
        "FS replay recomputes initialization, every frame, namespace",
        "CanonicalFramedExecutionViewBody = {",
    ):
        _require(token in fs, f"canonical-framed owner clause drifted: {token}")
    _require(
        "NominalProtocolDeclarationBody = MetaRecord {" in core,
        "nominal declaration body drifted",
    )
    _require(
        "no lane is\nrelabeled as another" in core,
        "outcome-carrier non-collapse rule drifted",
    )


def _cold_source() -> dict[str, Any]:
    model = _load("_fs_provider_checker_model", SOURCE_MODEL)
    previous_model = sys.modules.get("model")
    sys.modules["model"] = model
    try:
        executor = _load("_fs_provider_checker_executor", SOURCE_EXECUTOR)
        replay = _load("_fs_provider_checker_replay", SOURCE_REPLAY)
        views = _load("_fs_provider_checker_views", SOURCE_VIEWS)
    finally:
        if previous_model is None:
            sys.modules.pop("model", None)
        else:
            sys.modules["model"] = previous_model

    subject = model.make_subject("one-shot")
    _require(
        subject.admission_outcome == "Affirmative"
        and subject.admission_code == "F0V3C-A-OWNER-ADMISSION",
        "cold one-shot source admission failed",
    )
    _require(
        subject.construction.challenge_rules[0].maximum_draws == 1,
        "cold one-shot source has another draw bound",
    )
    view_digests = views.validate_against_predecessor(subject)
    execution_view = views.execution_view(subject)

    frozen_runs = _read_json(SOURCE_RUNS)
    _require(
        frozen_runs.get("format")
        == "zkc.formal-source-fs-runtime.expected-runs.v1"
        and len(frozen_runs.get("records", [])) == 54,
        "one-shot frozen run corpus is malformed",
    )
    frozen_by_name = {row[0]: row for row in frozen_runs["records"]}
    _require(len(frozen_by_name) == 54, "one-shot frozen run names alias")

    results = []
    replay_matches = 0
    for case in executor.all_cases():
        result = executor.execute(subject, case)
        replay_lane, transitions = replay.replay(
            subject, asdict(case), result.record
        )
        _require(replay_lane == result.lane, f"cold replay lane differs for {case.name}")
        _require(
            transitions == result.transition_receipts,
            f"cold replay transitions differ for {case.name}",
        )
        summary = [
            case.name,
            result.lane,
            executor.record_digest(result.record),
            _digest(result.transcript_prefix),
            result.derived,
        ]
        _require(
            frozen_by_name.get(case.name) == summary,
            f"cold run differs from the frozen record for {case.name}",
        )
        replay_matches += 1
        results.append(result)

    lanes = Counter(result.lane for result in results)
    lane_counts = {lane: lanes.get(lane, 0) for lane in LANES}
    _require(
        lane_counts
        == {
            "Accepted": 20,
            "Rejected": 34,
            "Aborted": 0,
            "InterpretationFailed": 0,
            "StrategyStopped": 0,
            "OperationalNoncompletion": 0,
        },
        "one-shot lane counts drifted",
    )

    table = _read_json(SOURCE_TABLE)
    entries = table.get("entries")
    _require(type(entries) is list and len(entries) == 9, "source table is not nine rows")
    table_by_point: dict[tuple[int, int], dict[str, Any]] = {}
    result_by_point: dict[tuple[int, int], Any] = {}
    for result in results:
        key = (result.case.statement, result.case.commitment)
        previous = result_by_point.setdefault(key, result)
        _require(
            previous.derived == result.derived
            and previous.transcript_prefix == result.transcript_prefix,
            "one source oracle point has multiple derivations",
        )
    for entry in entries:
        point = entry.get("input", {})
        key = (point.get("statement"), point.get("commitment"))
        _require(
            point.get("challenge") == 0 and key not in table_by_point,
            "source table point aliases or names another challenge",
        )
        result = result_by_point.get(key)
        _require(result is not None, f"source table point is outside the run corpus: {key}")
        _require(
            point.get("transcript_prefix_sha256") == _digest(result.transcript_prefix),
            f"source table prefix is not authenticated by its frozen runs: {key}",
        )
        _require(
            entry.get("output")
            == {
                "kind": "value",
                "value": result.derived["value"],
                "draw_count": result.derived["draws"],
            },
            f"source table answer is not authenticated by its frozen runs: {key}",
        )
        table_by_point[key] = entry
    _require(
        set(table_by_point)
        == {(statement, commitment) for statement in range(3) for commitment in range(3)},
        "source table domain differs from the finite domain",
    )

    prefix = table.get("prefix_encoding", {})
    for key, entry in table_by_point.items():
        statement, commitment = key
        assembled = (
            tuple(prefix["fixed_frames"])
            + (prefix["statement_frames"][str(statement)],)
            + (prefix["commitment_frames"][str(commitment)],)
        )
        _require(
            _digest(assembled) == entry["input"]["transcript_prefix_sha256"],
            f"factored source prefix does not reconstruct table point {key}",
        )

    retrying_runs = _read_json(RETRYING_RUNS)
    retrying_lanes = Counter(row[1] for row in retrying_runs.get("records", []))
    _require(
        len(retrying_runs.get("records", [])) == 54
        and retrying_lanes["InterpretationFailed"] == 0,
        "retrying frozen corpus no longer reports zero exhaustion runs",
    )
    return {
        "model": model,
        "subject": subject,
        "results": results,
        "table": table,
        "table_by_point": table_by_point,
        "lane_counts": lane_counts,
        "retrying_exhaustions": retrying_lanes["InterpretationFailed"],
        "replay_matches": replay_matches,
        "view_digests": view_digests,
        "execution_view_sha256": _digest(execution_view),
    }


def _provider_root() -> Path:
    return Path(
        os.environ.get("ZKC_ARKLIB_ROOT", str(PROVIDER_DEFAULT))
    ).resolve()


def _git_pair(path: Path) -> tuple[str, str]:
    completed, _seconds = _run(
        ["git", "rev-parse", "HEAD", "HEAD^{tree}"],
        path,
        env=_external_git_env(),
    )
    values = completed.stdout.split()
    _require(
        completed.returncode == 0 and len(values) == 2,
        f"cannot resolve source pin at {path}",
    )
    return values[0], values[1]


def _provider_pins(provider: Path) -> dict[str, Any]:
    revision, tree = _git_pair(provider)
    dependency_revision, dependency_tree = _git_pair(
        provider / ".lake/packages/VCVio"
    )
    _require(
        (revision, tree) == (PROVIDER_REVISION, PROVIDER_TREE),
        "provider revision or tree differs from the pin",
    )
    _require(
        (dependency_revision, dependency_tree) == (VCVIO_REVISION, VCVIO_TREE),
        "provider dependency revision or tree differs from the pin",
    )
    return {
        "git_tree": tree,
        "dependency_revision": dependency_revision,
        "dependency_tree": dependency_tree,
        "source_sha256": {
            name: _sha256(provider / name) for name in PROVIDER_SOURCE_FILES
        },
    }


def _finite_rows(source: dict[str, Any]) -> list[dict[str, int]]:
    return [
        {
            "statement": statement,
            "commitment": commitment,
            "answer": source["table_by_point"][(statement, commitment)]["output"][
                "value"
            ],
        }
        for statement in range(3)
        for commitment in range(3)
    ]


def _expected_maps() -> tuple[list[dict[str, Any]], list[dict[str, str]], list[dict[str, Any]]]:
    schedule = [
        {"occurrence": 0, "kind": "ProverMessage", "step": "proof.commitment"},
        {"occurrence": 1, "kind": "Challenge", "step": "oracle.query.round-one"},
        {"occurrence": 2, "kind": "ProverMessage", "step": "proof.response"},
        {"occurrence": 3, "kind": "Check", "step": "verifier.check"},
        {"occurrence": 4, "kind": "Terminal", "step": "verifier.accept"},
        {"occurrence": 5, "kind": "Terminal", "step": "verifier.reject"},
    ]
    types = [
        {"source": "public statement", "provider": "StmtIn", "carrier": "ZMod 3"},
        {"source": "private witness", "provider": "WitIn", "carrier": "ZMod 3"},
        {"source": "commitment", "provider": "proof round zero", "carrier": "ZMod 3"},
        {"source": "challenge", "provider": "oracle answer", "carrier": "ZMod 3"},
        {"source": "response", "provider": "proof round two", "carrier": "ZMod 3"},
        {"source": "check", "provider": "verifier predicate", "carrier": "Bool"},
        {"source": "terminal", "provider": "verifier result", "carrier": "Option Unit"},
    ]
    lanes = [
        {"lane": "Accepted", "provider_lane_image": {"case": "Image", "value": "some ()"}},
        {"lane": "Rejected", "provider_lane_image": {"case": "Image", "value": "none"}},
        {"lane": "Aborted", "provider_lane_image": {"case": "Unmodelled"}},
        {"lane": "InterpretationFailed", "provider_lane_image": {"case": "Unmodelled"}},
        {"lane": "StrategyStopped", "provider_lane_image": {"case": "Unmodelled"}},
        {"lane": "OperationalNoncompletion", "provider_lane_image": {"case": "Unmodelled"}},
    ]
    return schedule, types, lanes


def _check_certificate(
    certificate: dict[str, Any], source: dict[str, Any], provider: Path
) -> dict[str, Any]:
    model = source["model"]
    subject = source["subject"]
    _require(
        certificate.get("format") == CERTIFICATE_FORMAT,
        "certificate format drifted",
    )
    expected_subject = {
        "core_id": model.identifier_text(subject.construction.core_id),
        "transcript_construction_id": model.identifier_text(
            subject.construction.identifier
        ),
        "fs_protocol_id": model.identifier_text(subject.fs_protocol.identifier),
        "maximum_draws": 1,
        "finite_table": _finite_rows(source),
        "run_count": 54,
    }
    _require(
        certificate.get("subject") == expected_subject,
        "certificate names another admitted source subject",
    )
    expected_provider = {
        "name": "ArkLib",
        "revision": PROVIDER_REVISION,
        "toolchain": "leanprover/lean4:v4.31.0",
        "module": "ArkLib.OracleReduction.FiatShamir.Basic",
        "definition": "Reduction.fiatShamir",
        "closed_carrier": {
            "schema": "Option Unit",
            "canonical_values": ["none", "some ()"],
        },
        "modelled_lanes": ["Accepted", "Rejected"],
        **_provider_pins(provider),
    }
    _require(
        certificate.get("provider") == expected_provider,
        "certificate provider pin or carrier drifted",
    )
    inputs = certificate.get("inputs", {})
    _require(
        inputs.get("owner_pages") == _file_pins(OWNER_PAGES),
        "owner-page pins drifted",
    )
    _require(
        inputs.get("profile_manifests") == _file_pins(PROFILE_MANIFESTS),
        "profile-manifest pins drifted",
    )
    package_pins = inputs.get("package_inputs")
    _require(
        package_pins == _file_pins(PACKAGE_INPUTS),
        "package-input pins drifted",
    )
    _require(
        all(not name.endswith(".md") for name in package_pins)
        and all("expected-findings" not in name for name in package_pins),
        "certificate package inputs include a research note or sibling findings",
    )
    _require(
        certificate.get("source_table_sha256") == _sha256(SOURCE_TABLE)
        and certificate.get("source_runs_sha256") == _sha256(SOURCE_RUNS),
        "certificate does not separately bind source runs and table",
    )
    _require(
        certificate.get("lean_sha256") == _sha256(PROVIDER_MODULE),
        "certificate does not bind the generated Lean module",
    )
    schedule, types, lanes = _expected_maps()
    _require(
        certificate.get("occurrence_to_step") == schedule,
        "schedule map is incomplete, aliased, or reordered",
    )
    _require(
        len({row["step"] for row in schedule}) == 6,
        "schedule map is not injective",
    )
    _require(certificate.get("type_map") == types, "value-carrier map drifted")
    _require(certificate.get("lane_map") == lanes, "six-lane map drifted")
    return {
        "schedule": schedule,
        "type_map": types,
        "lane_map": lanes,
        "modelled_lanes": certificate["provider"]["modelled_lanes"],
    }


def _provider_execution_model(provider: Path) -> dict[str, Any]:
    basic = (provider / "ArkLib/OracleReduction/Basic.lean").read_text(
        encoding="utf-8"
    )
    execution = (provider / "ArkLib/OracleReduction/Execution.lean").read_text(
        encoding="utf-8"
    )
    transform = (
        provider / "ArkLib/OracleReduction/FiatShamir/Basic.lean"
    ).read_text(encoding="utf-8")
    generated = PROVIDER_MODULE.read_text(encoding="utf-8")
    base = BASE_MODULE.read_text(encoding="utf-8")
    _require(
        "verify : StmtIn → FullTranscript pSpec → OptionT (OracleComp oSpec) StmtOut"
        in basic,
        "provider verifier carrier drifted",
    )
    _require(
        "def Reduction.verdict" in execution
        and "OptionT (OracleComp" in execution,
        "provider verdict carrier drifted",
    )
    _require(
        "def Reduction.fiatShamir" in transform
        and "prover := R.prover.fiatShamir" in transform
        and "verifier := R.verifier.fiatShamir" in transform
        and "messages.deriveTranscriptFS" in transform,
        "provider Fiat-Shamir transform shape drifted",
    )
    _require(
        "Reduction.fiatShamir (reduction nonce)" in generated,
        "generated module does not transform the prior reduction",
    )
    for fragment in (
        "def reduction (nonce : Z3) : Reduction",
        "def candidateCommit (nonce : Z3) : Z3 := nonce",
        "nonce + challenge * witness",
    ):
        _require(fragment in base, f"prior generated reduction omits {fragment!r}")
    _require(
        "def finiteTableLookup" in generated
        and '| _, _ => none' in generated
        and 'panic! "finite table lookup outside admitted domain"' in generated,
        "generated table lookup does not expose an outside-domain refusal",
    )
    return {
        "verdict_carrier": "Option Unit",
        "modelled_lanes": ["Accepted", "Rejected"],
        "unmodelled_lanes": [
            "Aborted",
            "InterpretationFailed",
            "StrategyStopped",
            "OperationalNoncompletion",
        ],
    }


def _parse_rows(
    output: str, prefix: str, field_count: int, key_fields: int
) -> dict[tuple[int, ...], tuple[int, ...]]:
    rows: dict[tuple[int, ...], tuple[int, ...]] = {}
    for line in output.splitlines():
        parts = line.split("\t")
        if not parts or parts[0] != prefix:
            continue
        _require(
            len(parts) == field_count + 1,
            f"{prefix} row has another arity",
        )
        values = tuple(int(item) for item in parts[1:])
        key = values[:key_fields]
        _require(key not in rows, f"{prefix} row repeats an input")
        rows[key] = values
    return rows


def _run_term_evaluator() -> tuple[dict[tuple[int, ...], int], dict[int, int], dict[str, float]]:
    lake = str(Path.home() / ".elan/bin/lake")
    build, build_seconds = _run([lake, "build", "M0"], TERM_KERNEL)
    _require(
        build.returncode == 0,
        f"term-kernel build failed: {build.stdout}{build.stderr}",
    )
    probe, probe_seconds = _run(
        [lake, "env", "lean", str(TERM_PROBE)], TERM_KERNEL
    )
    _require(
        probe.returncode == 0,
        f"term-evaluator probe failed: {probe.stdout}{probe.stderr}",
    )
    terms = _parse_rows(probe.stdout, "TERM", 5, 4)
    terminals = _parse_rows(probe.stdout, "TERMINAL", 4, 1)
    _require(len(terms) == 81, "term evaluator did not cover all 81 inputs")
    _require(set(terminals) == {(0,), (1,)}, "terminal probe omitted a verdict")
    selected: dict[int, int] = {}
    for (verdict,), row in terminals.items():
        accept_attempted, reject_attempted, occurrence = row[1:]
        _require(
            accept_attempted + reject_attempted == 1
            and occurrence == (4 if verdict else 5),
            f"first-active terminal differs for verdict {verdict}",
        )
        selected[verdict] = occurrence

    vectors = _read_json(TERM_VECTORS)
    vector_terms = {
        tuple(int(part) for part in row["name"].split("/")[1].split("-")): int(
            row["closed_form"]
        )
        for row in vectors["check_cases"]
    }
    observed_terms = {key: row[-1] for key, row in terms.items()}
    _require(vector_terms == observed_terms, "Lean term probe differs from frozen vectors")
    return observed_terms, selected, {
        "term_build_seconds": build_seconds,
        "term_probe_seconds": probe_seconds,
    }


def _run_provider(provider: Path) -> tuple[dict[str, Any], dict[str, float]]:
    _require(provider.is_dir(), f"pinned provider tree is absent: {provider}")
    lake = str(Path.home() / ".elan/bin/lake")
    environment = _external_git_env()
    version, version_seconds = _run(
        [lake, "env", "lean", "--version"], provider, env=environment
    )
    _require(
        version.returncode == 0 and f"version {LEAN_VERSION}" in version.stdout,
        "provider Lean toolchain differs from the pin",
    )
    required = (
        provider
        / ".lake/build/lib/lean/ArkLib/OracleReduction/FiatShamir/Basic.olean",
        provider
        / ".lake/build/lib/lean/ArkLib/OracleReduction/Execution.olean",
        provider
        / ".lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Algebra/Field/ZMod.olean",
    )
    _require(
        all(path.is_file() for path in required),
        "a pinned provider dependency is not built",
    )

    overlay = HERE / "target/arklib-overlay"
    overlay.mkdir(parents=True, exist_ok=True)
    base_object = overlay / "SchnorrArkLib.olean"
    base_build, base_seconds = _run(
        [
            lake,
            "env",
            "lean",
            "-R",
            str(BASE_MODULE.parent),
            "-o",
            str(base_object),
            str(BASE_MODULE),
        ],
        provider,
        env=environment,
    )
    _require(
        base_build.returncode == 0 and base_object.is_file(),
        f"package-local prior-module overlay failed: {base_build.stdout}{base_build.stderr}",
    )

    lean_environment = dict(environment)
    prior_path = lean_environment.get("LEAN_PATH", "")
    lean_environment["LEAN_PATH"] = (
        str(overlay) if not prior_path else f"{overlay}:{prior_path}"
    )
    execution, execution_seconds = _run(
        [
            lake,
            "env",
            "lean",
            "-R",
            str(PROVIDER_MODULE.parent),
            str(PROVIDER_MODULE),
        ],
        provider,
        env=lean_environment,
    )
    _require(
        execution.returncode == 0,
        f"transformed provider module failed: {execution.stdout}{execution.stderr}",
    )
    _require(
        "sorryAx" not in execution.stdout,
        "transformed provider module depends on a sorry axiom",
    )
    _require(
        "HONEST-QUERY-COUNT-FAILURE" not in execution.stdout
        and "VERIFIER-QUERY-COUNT-FAILURE" not in execution.stdout,
        "provider execution issued another oracle-query cardinality",
    )
    for declaration in (
        "transformedReduction",
        "tableImpl",
        "executeProver",
        "executeVerifier",
    ):
        _require(
            f"'ZkcArkLibFiatShamirInterpretation.{declaration}' depends on axioms:"
            in execution.stdout,
            f"provider did not print the axiom closure for {declaration}",
        )
    honest = _parse_rows(execution.stdout, "HONEST", 14, 3)
    verifier = _parse_rows(execution.stdout, "VERIFIER", 8, 3)
    _require(len(honest) == 27, "provider omitted an honest execution")
    _require(len(verifier) == 27, "provider omitted a verifier-input execution")
    return {
        "honest": honest,
        "verifier": verifier,
        "provider_revision": PROVIDER_REVISION,
        "provider_tree": PROVIDER_TREE,
        "dependency_revision": VCVIO_REVISION,
        "dependency_tree": VCVIO_TREE,
        "lean_version": version.stdout.strip(),
        "required_objects": [str(path) for path in required],
        "overlay_object": str(base_object),
        "overlay_build_performed": True,
        "axiom_lines": [
            line for line in execution.stdout.splitlines() if "depends on axioms" in line
        ],
    }, {
        "version_seconds": version_seconds,
        "overlay_build_seconds": base_seconds,
        "provider_execution_seconds": execution_seconds,
    }


def _query(round_: int, statement: int, commitment: int, answer: int) -> dict[str, int]:
    return {
        "round": round_,
        "statement": statement,
        "commitment": commitment,
        "answer": answer,
    }


def _source_point(source: dict[str, Any], statement: int, commitment: int) -> dict[str, Any]:
    entry = source["table_by_point"][(statement, commitment)]
    return {
        "challenge": 0,
        "statement": statement,
        "commitment": commitment,
        "transcript_prefix_sha256": entry["input"]["transcript_prefix_sha256"],
        "answer": entry["output"]["value"],
    }


def _compare_query_sequence(
    expected: list[dict[str, int]], observed: list[dict[str, int]], label: str
) -> None:
    _require(expected == observed, f"oracle query sequence differs for {label}")


def _expect_negative(action: Callable[[], Any], label: str) -> None:
    try:
        action()
    except CheckerError:
        return
    raise CheckerError(f"oracle-point negative control was accepted: {label}")


def _oracle_mutations() -> int:
    point = [_query(1, 0, 0, 2)]
    _expect_negative(
        lambda: _compare_query_sequence(point, point + point, "superfluous"),
        "superfluous query",
    )
    _expect_negative(
        lambda: _compare_query_sequence(point, [], "missing"),
        "missing query",
    )
    altered = [_query(1, 0, 1, 2)]
    _expect_negative(
        lambda: _compare_query_sequence(point, altered, "differently framed"),
        "differently framed query",
    )
    return 3


def _outside_table_refusals(source: dict[str, Any]) -> int:
    domain = set(source["table_by_point"])
    probes = ((-1, 0), (0, -1), (3, 0), (0, 3), (3, 3))
    _require(
        all(point not in domain for point in probes),
        "outside-domain table probe entered the finite domain",
    )
    return len(probes)


def _compare(
    source: dict[str, Any],
    terms: dict[tuple[int, ...], int],
    terminals: dict[int, int],
    provider: dict[str, Any],
) -> dict[str, Any]:
    source_by_name = {result.case.name: result for result in source["results"]}
    oracle_sequences: list[dict[str, Any]] = []
    trace_count = 0
    terminal_count = 0
    lane_counts: Counter[str] = Counter()

    for key, row in sorted(provider["honest"].items()):
        statement, witness, nonce = key
        (
            _s,
            _w,
            _n,
            commitment,
            response,
            verdict,
            p_round,
            p_statement,
            p_commitment,
            p_answer,
            v_round,
            v_statement,
            v_commitment,
            v_answer,
        ) = row
        result = source_by_name[f"honest-s{statement}-w{witness}-n{nonce}"]
        challenge = result.derived["value"]
        expected_verdict = terms[(statement, commitment, challenge, response)]
        expected_lane = "Accepted" if expected_verdict else "Rejected"
        expected_query = [_query(1, statement, commitment, challenge)]
        prover_query = [_query(p_round, p_statement, p_commitment, p_answer)]
        verifier_query = [_query(v_round, v_statement, v_commitment, v_answer)]
        _compare_query_sequence(expected_query, prover_query, f"honest prover {key}")
        _compare_query_sequence(expected_query, verifier_query, f"honest verifier {key}")
        _require(
            commitment == nonce
            and response == (nonce + challenge * witness) % 3,
            f"provider proof values differ from the source trace for {key}",
        )
        _require(
            verdict == expected_verdict
            and result.lane == expected_lane
            and terminals[verdict] == (4 if result.lane == "Accepted" else 5),
            f"provider check, terminal, or lane differs for {key}",
        )
        source_trace = [commitment, challenge, response, expected_verdict, terminals[verdict]]
        provider_trace = [commitment, p_answer, response, verdict, terminals[verdict]]
        _require(source_trace == provider_trace, f"mapped trace differs for {key}")
        oracle_sequences.append(
            {
                "case": result.case.name,
                "source": [_source_point(source, statement, commitment)],
                "provider_prover": prover_query,
                "provider_verifier": verifier_query,
            }
        )
        lane_counts[result.lane] += 1
        trace_count += 1
        terminal_count += 1

    for key, row in sorted(provider["verifier"].items()):
        statement, commitment, response = key
        (
            _s,
            _a,
            _z,
            verdict,
            v_round,
            v_statement,
            v_commitment,
            v_answer,
        ) = row
        result = source_by_name[
            f"verifier-s{statement}-a{commitment}-z{response}"
        ]
        challenge = result.derived["value"]
        expected_verdict = terms[(statement, commitment, challenge, response)]
        expected_lane = "Accepted" if expected_verdict else "Rejected"
        expected_query = [_query(1, statement, commitment, challenge)]
        verifier_query = [_query(v_round, v_statement, v_commitment, v_answer)]
        _compare_query_sequence(
            expected_query, verifier_query, f"verifier input {key}"
        )
        _require(
            verdict == expected_verdict
            and result.lane == expected_lane
            and terminals[verdict] == (4 if result.lane == "Accepted" else 5),
            f"provider verifier check, terminal, or lane differs for {key}",
        )
        source_trace = [commitment, challenge, response, expected_verdict, terminals[verdict]]
        provider_trace = [commitment, v_answer, response, verdict, terminals[verdict]]
        _require(source_trace == provider_trace, f"mapped verifier trace differs for {key}")
        oracle_sequences.append(
            {
                "case": result.case.name,
                "source": [_source_point(source, statement, commitment)],
                "provider_verifier": verifier_query,
            }
        )
        lane_counts[result.lane] += 1
        trace_count += 1
        terminal_count += 1

    _require(
        trace_count == terminal_count == 54,
        "provider comparison did not cover every source run",
    )
    _require(
        dict(lane_counts) == {"Accepted": 20, "Rejected": 34},
        "provider outcome counts differ from the source lanes",
    )
    return {
        "run_count": trace_count,
        "trace_comparisons": trace_count,
        "terminal_comparisons": terminal_count,
        "lane_counts": dict(lane_counts),
        "oracle_sequences": oracle_sequences,
    }


def check() -> dict[str, Any]:
    _owner_gate()
    certificate = _read_json(CERTIFICATE)
    provider_root = _provider_root()
    source = _cold_source()
    maps = _check_certificate(certificate, source, provider_root)
    execution_model = _provider_execution_model(provider_root)
    terms, terminals, term_timings = _run_term_evaluator()
    provider, provider_timings = _run_provider(provider_root)
    comparison = _compare(source, terms, terminals, provider)
    oracle_mutations = _oracle_mutations()
    outside_refusals = _outside_table_refusals(source)

    findings = [
        ["source-certificate-and-cold-admission", "Affirmative", "F2O4-A-SOURCE-AUTHENTICATED"],
        ["schedule-clause", "Affirmative", "F2O4-A-SCHEDULE"],
        ["values-clause", "Affirmative", "F2O4-A-VALUES"],
        ["oracle-points-clause", "Affirmative", "F2O4-A-ORACLE-POINTS"],
        ["checks-and-terminals-clause", "Affirmative", "F2O4-A-CHECKS-TERMINALS"],
        ["traces-clause", "Affirmative", "F2O4-A-TRACES"],
        ["provider-carrier-determinate", "Affirmative", "F2O4-A-CARRIER-DETERMINATE"],
        ["retrying-exhaustion-unmodelled", "Affirmative", "F2O4-A-EXHAUSTION-UNMODELLED"],
        ["superfluous-oracle-query", "Negative", "F2O4-N-SUPERFLUOUS-ORACLE-QUERY"],
        ["missing-oracle-query", "Negative", "F2O4-N-MISSING-ORACLE-QUERY"],
        ["differently-framed-oracle-query", "Negative", "F2O4-N-DIFFERENTLY-FRAMED-ORACLE-QUERY"],
        ["outside-finite-table", "Refused", "F2O4-R-OUTSIDE-FINITE-TABLE"],
        ["residual-trust-listed", "Affirmative", "F2O4-A-RESIDUAL-TRUST"],
        ["finite-fiat-shamir-correspondence", "Affirmative", "F2O4-A-FS-FINITE-CORRESPONDENCE"],
    ]
    return {
        "aggregate": "Affirmative/F2O4-A-FS-FINITE-CORRESPONDENCE",
        "finding_codes": findings,
        "subject": certificate["subject"],
        "provider": {
            key: value
            for key, value in provider.items()
            if key not in {"honest", "verifier"}
        },
        "measurements": {
            "source_replay_matches": source["replay_matches"],
            "source_lane_counts": source["lane_counts"],
            "retrying_exhaustions_reported_unmodelled": source[
                "retrying_exhaustions"
            ],
            "derivation_table_points": len(source["table_by_point"]),
            "term_inputs": len(terms),
            "oracle_point_negative_controls": oracle_mutations,
            "outside_table_refusals": outside_refusals,
            "construction_view_sha256": source["view_digests"],
            "execution_view_sha256": source["execution_view_sha256"],
            **maps,
            **execution_model,
            **comparison,
        },
        "timings": {**term_timings, **provider_timings},
        "residual_trust": [
            "Lean kernel and the pinned ArkLib and VCVio oracle-computation semantics",
            "the complete finite domain",
            "the independent checker adapter",
            "the portable-term evaluator with its frozen Lean differential",
        ],
        "nonclaims": [
            "No protocol or cryptographic security property is established.",
            "No theorem or random-oracle result is established.",
            "No arbitrary-domain or duplex-sponge correspondence is established.",
            "No owner-page or provider-map premise is published.",
        ],
    }


def main() -> int:
    try:
        report = check()
    except (
        CheckerError,
        OSError,
        ValueError,
        KeyError,
        TypeError,
        subprocess.TimeoutExpired,
    ) as error:
        print(f"Fiat-Shamir provider interpretation check failed: {error}", file=sys.stderr)
        return 1
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
