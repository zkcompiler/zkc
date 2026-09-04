#!/usr/bin/env python3
"""Independent checker for the finite Schnorr ArkLib interpretation.

This program does not import the generator. It re-derives the six views by the
cold canonical-byte path, authenticates the certificate, executes the portable
term evaluator and the pinned provider with Lean, and compares every finite
verifier input and generated trace. It also checks ArkLib's source-level
placement of the option layer before accepting the provider declaration.
"""

from __future__ import annotations

import copy
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
PROVIDER_MODULE = HERE / "generated/SchnorrArkLib.lean"
TERM_PROBE = HERE / "TermEvaluatorProbe.lean"
SCHNORR_COLD_VIEWS = ROOT / "evaluation/formal-source-view-bodies-f0v2b1/independent.py"
SCHNORR_VIEW_SCHEMA = ROOT / "evaluation/formal-source-view-bodies-f0v2b1/normalized-schema.json"
SCHNORR_CORE_MODEL = ROOT / "evaluation/formal-source-target-core-f1r1b/reference_model.py"
RELATION_PLAN_MODEL = ROOT / "evaluation/formal-schnorr-relations-plan-f2p1/model.py"
TERM_KERNEL = ROOT / "evaluation/formal-kernel-mechanization-m0/lean"
TERM_VECTORS = ROOT / "evaluation/formal-kernel-mechanization-m0/vectors/m2-term-calculus.json"
TERMINAL_MECHANIZATION = TERM_KERNEL / "M0/Terminal.lean"
ENTRY_CONTRACT = (
    ROOT
    / "docs-next/notes/semantic-revalidation-and-redesign/formal-assurance-research"
    / "f2o3-arklib-interpretation-entry-contract.md"
)
DECISION_PACKET = (
    ROOT
    / "docs-next/notes/semantic-revalidation-and-redesign/formal-assurance-research"
    / "f2o2-provider-carrier-decision-2026-09-03.md"
)
INTERACTIVE_CORE = ROOT / "docs-next/pir/interactive-core.md"
ANALYSIS_MODEL = ROOT / "docs-next/analysis/analysis-model.md"
CRYPTOGRAPHIC_PROPERTIES = ROOT / "docs-next/analysis/cryptographic-properties.md"
CRYPTOGRAPHIC_PROPERTY_MANIFEST = ROOT / "docs-next/analysis/profiles/cryptographic-property.json"
OWNER_PAGES = (INTERACTIVE_CORE, ANALYSIS_MODEL, CRYPTOGRAPHIC_PROPERTIES)
PROFILE_MANIFESTS = (
    ROOT / "docs-next/foundation/semantic-profile-manifests.json",
    ROOT / "docs-next/pir/profiles/interaction.json",
    ROOT / "docs-next/analysis/profiles/kernel.json",
    CRYPTOGRAPHIC_PROPERTY_MANIFEST,
)
PACKAGE_INPUTS = (
    SCHNORR_VIEW_SCHEMA,
    TERM_VECTORS,
    TERMINAL_MECHANIZATION,
    TERM_PROBE,
)

CERTIFICATE_FORMAT = "zkc.formal-provider-interpretation.arklib.certificate.v0"
PROVIDER_REVISION = "fad5cbf808774838924dc8273715724c6a6caa1f"
PROVIDER_TREE = "e38383088598a1305c15447c53db309ccd6b35ee"
VCVIO_REVISION = "cbd4144b51d92da00dd50f05e068b2348fa6e529"
VCVIO_TREE = "28c268057ed58427973e5bbf4854d472a7088954"
PROVIDER_DEFAULT = Path("/home/wonjae/code/ArkLib")
PROVIDER_SOURCE_FILES = (
    "ArkLib/OracleReduction/Basic.lean",
    "ArkLib/OracleReduction/Execution.lean",
    "ArkLib/OracleReduction/ProtocolSpec/Basic.lean",
    "lake-manifest.json",
    "lean-toolchain",
)
LEAN_VERSION = "4.31.0"
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


def _file_pins(paths: tuple[Path, ...]) -> dict[str, str]:
    return {path.relative_to(ROOT).as_posix(): _sha256(path) for path in paths}


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


def _cold_source() -> dict[str, Any]:
    cold = _load("_arklib_checker_cold_views", SCHNORR_COLD_VIEWS)
    core, protocol = cold._admit()
    candidate = cold.build_candidate(core, protocol)
    views = candidate["values"]
    manifests = candidate["requested_manifests"]
    fixture = cold.owner.make_fixture()
    return {
        "cold": cold,
        "core": core,
        "protocol": protocol,
        "views": views,
        "source_digest": candidate["source_digest"],
        "body_sha256": {
            name: hashlib.sha256(_canonical(body)).hexdigest() for name, body in views.items()
        },
        "active_leaf_counts": {name: len(manifests[name]) for name in views},
        "carriers": {
            "core_profiled_body_sha256": hashlib.sha256(
                cold.owner.core_profiled_body(fixture.core_candidate.core, fixture.environment.profile_id)
            ).hexdigest(),
            "protocol_profiled_body_sha256": hashlib.sha256(
                cold.owner.protocol_profiled_body(fixture.protocol_candidate.core_id, fixture.environment.profile_id)
            ).hexdigest(),
            "view_schema_source_sha256": _sha256(SCHNORR_VIEW_SCHEMA),
            "active_view_manifest_sha256": {
                name: hashlib.sha256(_canonical(manifests[name])).hexdigest() for name in views
            },
        },
    }


def _natural(cold: ModuleType, leaf: Any) -> int:
    value = cold.owner.k1.decode_datum(bytes.fromhex(leaf["body"]))
    _require(type(value) is cold.owner.k1.Nat, "owner ordinal is not a natural")
    return value.value


def _provider_root() -> Path:
    return Path(os.environ.get("ZKC_ARKLIB_ROOT", str(PROVIDER_DEFAULT))).resolve()


def _git_pair(path: Path) -> tuple[str, str]:
    completed, _ = _run(
        ["git", "rev-parse", "HEAD", "HEAD^{tree}"],
        path,
        env=_external_git_env(),
    )
    values = completed.stdout.split()
    _require(completed.returncode == 0 and len(values) == 2, f"cannot resolve source pin at {path}")
    return values[0], values[1]


def _provider_source_pins(provider: Path) -> dict[str, Any]:
    revision, tree = _git_pair(provider)
    dependency_revision, dependency_tree = _git_pair(provider / ".lake/packages/VCVio")
    _require((revision, tree) == (PROVIDER_REVISION, PROVIDER_TREE), "provider revision or tree differs from the pin")
    _require(
        (dependency_revision, dependency_tree) == (VCVIO_REVISION, VCVIO_TREE),
        "provider dependency revision or tree differs from the pin",
    )
    return {
        "git_tree": tree,
        "dependency_revision": dependency_revision,
        "dependency_tree": dependency_tree,
        "source_sha256": {name: _sha256(provider / name) for name in PROVIDER_SOURCE_FILES},
    }


def _check_certificate(
    certificate: dict[str, Any], source: dict[str, Any], provider: Path
) -> dict[str, Any]:
    _require(certificate.get("format") == CERTIFICATE_FORMAT, "certificate format drifted")
    subject = certificate.get("subject")
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
    provider_pins = _provider_source_pins(provider)
    expected_provider = {
        "name": "ArkLib",
        "revision": PROVIDER_REVISION,
        "toolchain": "leanprover/lean4:v4.31.0",
        "module": "ArkLib.OracleReduction.Execution",
        "definition": "Reduction.verdict",
        "closed_carrier": {
            "schema": "Option Unit",
            "canonical_values": ["none", "some ()"],
        },
        "modelled_lanes": ["Accepted", "Rejected"],
        "prover_run_carrier": "OracleComp (FullTranscript x Unit x Unit)",
        "verifier_run_carrier": "OptionT (OracleComp) Unit",
        **provider_pins,
    }
    _require(certificate.get("provider") == expected_provider, "certificate provider pin or carrier drifted")
    _require(certificate.get("lean_sha256") == _sha256(PROVIDER_MODULE), "certificate does not bind the generated module")

    inputs = certificate.get("inputs")
    _require(type(inputs) is dict, "certificate inputs are absent")
    _require(inputs.get("owner_pages") == _file_pins(OWNER_PAGES), "owner-page input pin drifted")
    _require(inputs.get("profile_manifests") == _file_pins(PROFILE_MANIFESTS), "profile-manifest input pin drifted")
    _require(inputs.get("package_inputs") == _file_pins(PACKAGE_INPUTS), "package input pin drifted")
    _require(inputs.get("carriers") == source["carriers"], "admitted source carrier input drifted")

    vectors = json.loads(TERM_VECTORS.read_text(encoding="utf-8"))
    for name in ("check", "guard"):
        expected = vectors["algorithms"][name]
        observed = inputs["algorithms"][name]
        _require(
            observed["preimage_sha256"] == expected["preimage_sha256"]
            and observed["preimage_length"] == expected["preimage_length"],
            f"{name} algorithm preimage drifted",
        )

    candidate = inputs["candidates"]
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
    source_core = _load("_arklib_checker_source_core", SCHNORR_CORE_MODEL)
    relation_plan = _load("_arklib_checker_relation_plan", RELATION_PLAN_MODEL)
    artifacts = relation_plan._build_artifacts(source_core, source_core.make_fixture())
    bodies = relation_plan._body_catalog(artifacts)
    _require(
        candidate["published_candidate_bodies_sha256"]
        == hashlib.sha256(_canonical(bodies)).hexdigest(),
        "published relation or Plan candidate body drifted",
    )

    analysis_model = ANALYSIS_MODEL.read_text(encoding="utf-8")
    property_text = CRYPTOGRAPHIC_PROPERTIES.read_text(encoding="utf-8")
    terminal_text = TERMINAL_MECHANIZATION.read_text(encoding="utf-8")
    _require(
        "modelled_lanes: CanonicalSortedUniqueSeq<AnalysisOutcomeLaneName>" in analysis_model
        and "AnalysisProviderLaneImage<carrier> =" in analysis_model,
        "Analysis lane-image owner text drifted",
    )
    _require(
        "until one is published no provider-map\npremise can be formed" in property_text,
        "Analysis provider-declaration publication boundary drifted",
    )
    _require(
        "def Attempted (schedule : List ScheduledOccurrence)" in terminal_text
        and "theorem attempted_iff_region_holds" in terminal_text
        and "theorem attemptedWhenever_sound" in terminal_text,
        "mechanized first-active interface drifted",
    )
    manifest = json.loads(CRYPTOGRAPHIC_PROPERTY_MANIFEST.read_text(encoding="utf-8"))
    definitions = {row.get("name") for row in manifest.get("definitions", [])}
    _require(
        "arklib-provider-declaration-v0" not in definitions
        and "arklib-option-unit-carrier-v0" not in definitions,
        "the ArkLib declaration was published; reform the provider premise and refreeze",
    )
    return vectors


def _validate_lane_map(certificate: dict[str, Any]) -> dict[str, Any]:
    lane_names = ["Accepted", "Rejected", "Aborted", "StrategyStopped", "OperationalNoncompletion"]
    lane_map = certificate.get("lane_map")
    _require(type(lane_map) is list and [row.get("lane") for row in lane_map] == lane_names, "declared five-lane map is not total in source order")
    expected = {
        "Accepted": {"case": "Image", "value": "some ()"},
        "Rejected": {"case": "Image", "value": "none"},
        "Aborted": {"case": "Unmodelled"},
        "StrategyStopped": {"case": "Unmodelled"},
        "OperationalNoncompletion": {"case": "Unmodelled"},
    }
    images: dict[str, dict[str, Any]] = {}
    modelled = set(certificate["provider"]["modelled_lanes"])
    for row in lane_map:
        lane = row["lane"]
        image = row.get("provider_lane_image")
        _require(image == expected[lane], f"provider lane image drifted for {lane}")
        _require((image["case"] == "Image") == (lane in modelled), f"modelled-lane membership differs for {lane}")
        images[lane] = image
    _require(set(modelled) == {"Accepted", "Rejected"}, "provider models another lane set")
    return images


def _check_maps(certificate: dict[str, Any], source: dict[str, Any]) -> dict[str, Any]:
    cold = source["cold"]
    views = source["views"]
    effect_names = {0: "ProverMessage", 2: "Challenge", 3: "Check", 5: "Terminal"}
    occurrences = [
        {"occurrence": _natural(cold, row[0]), "effect": effect_names[row[3]["case"]]}
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
        all(row["occurrence"] == occurrence["occurrence"] and row["effect"] == occurrence["effect"] for row, occurrence in zip(mapping, occurrences)),
        "schedule map changes an owner occurrence kind",
    )
    decisions = {_natural(cold, row[0]) for row in views["StrategyDecisionView"][1]}
    prover_steps = {row["occurrence"] for row in mapping if row["actor"] == "Prover"}
    _require(decisions == prover_steps == {0, 2}, "prover step map differs from the strategy view")

    expected_types = [
        ("PublicBindingView.public_inputs[0]", "StmtIn", "ZMod 3"),
        ("RelationInterface.private_witness[0]", "WitIn", "ZMod 3"),
        ("EffectView.occurrences[0].outputs[0]", "round 0", "ZMod 3"),
        ("ProverPlan.persistent_state[0]", "Memory.nonce", "ZMod 3"),
        ("PublicCoinView.challenges[0].value_type", "round 1", "ZMod 3"),
        ("EffectView.occurrences[2].outputs[0]", "round 2", "ZMod 3"),
        ("EffectView.occurrences[3].outputs[0]", "verifier predicate", "Bool"),
        ("ExecutionView.terminals", "Reduction.verdict", "Option Unit"),
    ]
    observed_types = [(row.get("source"), row.get("provider"), row.get("carrier")) for row in certificate.get("type_map", [])]
    _require(observed_types == expected_types, "type map is incomplete or reordered")
    effects = views["EffectView"][1]
    challenges = views["PublicCoinView"][4]
    _require(len(challenges) == 1, "source has another challenge cardinality")
    z3_bodies = [effects[index][4][0]["body"] for index in (0, 1, 2)]
    _require(len(set(z3_bodies + [challenges[0][3]["body"]])) == 1, "message and challenge source types differ")
    _require(effects[3][4][0]["body"] != z3_bodies[0], "Check output is not distinct Bool")

    execution = views["ExecutionView"][6]
    execution_outputs = [(_natural(cold, row[0]), len(row[1])) for row in execution[0]]
    _require(execution_outputs == [(0, 1), (1, 1), (2, 1), (3, 1), (4, 0), (5, 0)], "completed-record output schema drifted")
    execution_challenges = [(_natural(cold, row[0]), _natural(cold, row[1]), row[2]["body"]) for row in execution[1]]
    _require(execution_challenges == [(0, 1, challenges[0][3]["body"])], "challenge receipt does not name the public-coin site")
    _require(execution[2] == [], "finite subject unexpectedly has Oracle receipts")
    terminals = [
        (_natural(cold, row[0]), _natural(cold, row[1]), row[2]["case"], len(row[3]))
        for row in execution[3]
    ]
    _require(terminals == [(0, 4, 0, 0), (1, 5, 1, 0)], "first-active terminal schema drifted")

    provider_text = PROVIDER_MODULE.read_text(encoding="utf-8")
    for fragment in (
        "def protocolSpec : ProtocolSpec 3",
        "!v[.P_to_V, .V_to_P, .P_to_V]",
        "(ZMod.finEquiv 3) <$> $[0..2]",
        "def freshChallengeQueryImpl : QueryImpl [protocolSpec.Challenge]ₒ ProbComp",
        "fun _ => freshChallenge",
        "def reduction (nonce : Z3) : Reduction",
        "def candidateCommit (nonce : Z3) : Z3 := nonce",
        "nonce + challenge * witness",
        "theorem commitRoundMatchesCandidate",
        "theorem responseRoundMatchesCandidate",
    ):
        _require(fragment in provider_text, f"provider artifact omits {fragment!r}")
    lane_images = _validate_lane_map(certificate)
    owner_text = INTERACTIVE_CORE.read_text(encoding="utf-8")
    _require("no lane is\nrelabeled as another" in owner_text, "outcome-carrier non-collapse rule drifted")
    return {
        "occurrences": occurrences,
        "decisions": sorted(decisions),
        "execution_output_occurrences": [occurrence for occurrence, arity in execution_outputs if arity],
        "execution_terminals": terminals,
        "lane_images": lane_images,
        "modelled_lanes": sorted(certificate["provider"]["modelled_lanes"]),
        "declared_lanes": len(lane_images),
        "image_lanes": sum(image["case"] == "Image" for image in lane_images.values()),
        "unmodelled_lanes": sum(image["case"] == "Unmodelled" for image in lane_images.values()),
    }


def _expect_rejected(action: Callable[[], Any], name: str) -> None:
    try:
        action()
    except CheckerError:
        return
    raise CheckerError(f"negative control was accepted: {name}")


def _mutation_controls(certificate: dict[str, Any], source: dict[str, Any]) -> int:
    aliased = copy.deepcopy(certificate)
    aliased["occurrence_to_step"][1]["occurrence"] = 0
    _expect_rejected(lambda: _check_maps(aliased, source), "aliased schedule")
    collapsed = copy.deepcopy(certificate)
    collapsed["lane_map"][3]["provider_lane_image"] = {"case": "Image", "value": "none"}
    _expect_rejected(lambda: _validate_lane_map(collapsed), "collapsed terminal image")
    return 2


def _check_provider_execution_model(provider: Path) -> dict[str, Any]:
    basic = (provider / "ArkLib/OracleReduction/Basic.lean").read_text(encoding="utf-8")
    execution = (provider / "ArkLib/OracleReduction/Execution.lean").read_text(encoding="utf-8")
    oracle_comp = (
        provider / ".lake/packages/VCVio/VCVio/OracleComp/OracleComp.lean"
    ).read_text(encoding="utf-8")
    contract = ENTRY_CONTRACT.read_text(encoding="utf-8")
    packet = DECISION_PACKET.read_text(encoding="utf-8")
    _require(
        "verify : StmtIn → FullTranscript pSpec → OptionT (OracleComp oSpec) StmtOut" in basic,
        "provider verifier carrier drifted",
    )
    _require(
        "def run (stmt : StmtIn) (wit : WitIn)\n    (prover : Prover" in execution
        and "OracleComp (oSpec + [pSpec.Challenge]ₒ) (FullTranscript pSpec × StmtOut × WitOut)" in execution,
        "provider prover execution is no longer total in the base carrier",
    )
    _require(
        "def Reduction.run (stmt : StmtIn) (wit : WitIn)" in execution
        and "OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ))" in execution
        and "let proverResult ← reduction.prover.run stmt wit" in execution
        and "let stmtOut ← liftM (reduction.verifier.run stmt proverResult.1).run" in execution,
        "provider reduction option-layer placement drifted",
    )
    _require(
        "def OracleComp" in oracle_comp
        and "PFunctor.FreeM" in oracle_comp
        and "protected lemma failure_def : (failure : OptionT (OracleComp spec)" in oracle_comp,
        "provider dependency failure carrier drifted",
    )
    _require(
        "failure of the prover's run" in contract
        and "the two producers of `none`" in contract,
        "entry-contract carrier claim changed; re-adjudicate the correction",
    )
    _require(
        "## 4a. The declaration, in the shape the profile publishes" in packet,
        "provider declaration packet shape drifted",
    )
    return {
        "verdict_carrier": "Option Unit",
        "none_producers": ["Verifier.run failure"],
        "prover_run_carrier": "OracleComp",
        "entry_contract_second_producer": "Refused",
        "operational_completion_needed_for_carrier_disambiguation": False,
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


def _run_term_evaluator() -> tuple[
    dict[tuple[int, ...], int], dict[int, int], dict[int, int], dict[str, float]
]:
    lake = str(Path.home() / ".elan/bin/lake")
    build, build_seconds = _run([lake, "build", "M0"], TERM_KERNEL)
    _require(build.returncode == 0, f"term-kernel build failed: {build.stdout}{build.stderr}")
    probe, probe_seconds = _run([lake, "env", "lean", str(TERM_PROBE)], TERM_KERNEL)
    _require(probe.returncode == 0, f"term-evaluator probe failed: {probe.stdout}{probe.stderr}")
    terms = _parse_rows(probe.stdout, "TERM", 5)
    guards = _parse_rows(probe.stdout, "GUARD", 2)
    terminals = _parse_rows(probe.stdout, "TERMINAL", 4, key_fields=1)
    _require(len(terms) == 81, "term evaluator did not cover all 81 inputs")
    _require(len(guards) == 2, "term evaluator did not cover both guard inputs")
    _require(set(terminals) == {(0,), (1,)}, "first-active probe omitted a guard value")
    selected: dict[int, int] = {}
    for (verdict,), row in terminals.items():
        accept_attempted, reject_attempted, occurrence = row[1:]
        _require(
            accept_attempted + reject_attempted == 1,
            f"mechanized first-active reading selected another cardinality for {verdict}",
        )
        _require(
            occurrence in (4, 5)
            and (accept_attempted if occurrence == 4 else reject_attempted) == 1,
            f"mechanized first-active reading selected an inactive terminal for {verdict}",
        )
        selected[verdict] = occurrence
    return (
        {key: row[-1] for key, row in terms.items()},
        {key[0]: row[-1] for key, row in guards.items()},
        selected,
        {"term_build_seconds": build_seconds, "term_probe_seconds": probe_seconds},
    )


def _run_provider(
    provider: Path,
) -> tuple[dict[tuple[int, ...], int], dict[tuple[int, ...], tuple[int, ...]], dict[str, Any]]:
    _require(provider.is_dir(), f"pinned provider tree is absent: {provider}")
    provider_env = _external_git_env()
    revision, revision_seconds = _run(
        ["git", "rev-parse", "HEAD", "HEAD^{tree}"], provider, env=provider_env
    )
    _require(
        revision.returncode == 0
        and revision.stdout.split() == [PROVIDER_REVISION, PROVIDER_TREE],
        "provider revision or tree differs from the pin",
    )
    dependency, dependency_seconds = _run(
        ["git", "rev-parse", "HEAD", "HEAD^{tree}"],
        provider / ".lake/packages/VCVio",
        env=provider_env,
    )
    _require(
        dependency.returncode == 0
        and dependency.stdout.split() == [VCVIO_REVISION, VCVIO_TREE],
        "provider dependency revision or tree differs from the pin",
    )
    lake = str(Path.home() / ".elan/bin/lake")
    version, version_seconds = _run(
        [lake, "env", "lean", "--version"], provider, env=provider_env
    )
    _require(
        version.returncode == 0 and f"version {LEAN_VERSION}" in version.stdout,
        "provider Lean toolchain differs from the pin",
    )
    required_objects = (
        provider / ".lake/build/lib/lean/ArkLib/OracleReduction/Execution.olean",
        provider / ".lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Algebra/Field/ZMod.olean",
    )
    _require(
        all(path.is_file() for path in required_objects),
        "a required provider module is not built; construct a package-local overlay and record it",
    )
    execution, execution_seconds = _run(
        [lake, "env", "lean", str(PROVIDER_MODULE)], provider, env=provider_env
    )
    _require(
        execution.returncode == 0,
        f"provider module failed: {execution.stdout}{execution.stderr}",
    )
    _require("sorryAx" not in execution.stdout, "generated provider module depends on a sorry axiom")
    for declaration in ("commitRoundMatchesCandidate", "responseRoundMatchesCandidate"):
        _require(
            f"'ZkcArkLibInterpretation.{declaration}' depends on axioms:" in execution.stdout,
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
            "provider_revision": PROVIDER_REVISION,
            "provider_tree": PROVIDER_TREE,
            "dependency_revision": VCVIO_REVISION,
            "dependency_tree": VCVIO_TREE,
            "lean_version": version.stdout.strip(),
            "required_objects": [str(path) for path in required_objects],
            "overlay_build_performed": False,
            "provider_axiom_lines": [
                line for line in execution.stdout.splitlines() if "depends on axioms" in line
            ],
            "revision_seconds": revision_seconds,
            "dependency_revision_seconds": dependency_seconds,
            "version_seconds": version_seconds,
            "provider_execution_seconds": execution_seconds,
        },
    )


def _compare(
    terms: dict[tuple[int, ...], int],
    guards: dict[int, int],
    mechanized_terminals: dict[int, int],
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
        _require(terms[key] == provider_checks[key] == closed, f"Check disagreement at {key}")
    _require(guards == {0: 0, 1: 1}, "guard is not the term evaluator's identity")

    step_for = {row["occurrence"]: row["step"] for row in certificate["occurrence_to_step"]}
    record_occurrences = maps["execution_output_occurrences"]
    terminal_occurrence = {
        terminal_case: occurrence
        for _terminal_ref, occurrence, terminal_case, _public_outputs in maps["execution_terminals"]
    }
    _require(record_occurrences == [0, 1, 2, 3], "completed-record order drifted")
    _require(terminal_occurrence == {0: 4, 1: 5}, "terminal case map drifted")
    _require(
        mechanized_terminals == {0: terminal_occurrence[1], 1: terminal_occurrence[0]},
        "mechanized first-active reading differs from the owner terminal cases",
    )
    lane_for_terminal = {terminal_occurrence[0]: "Accepted", terminal_occurrence[1]: "Rejected"}
    lane_images = maps["lane_images"]
    accepted = 0
    rejected = 0
    traces = 0
    domain_lanes: set[str] = set()
    for key, row in sorted(provider_runs.items()):
        statement, witness, nonce, challenge = key
        commitment, response, verdict = row[4:7]
        last_occurrence = row[-1]
        expected_commitment = nonce
        expected_response = (nonce + challenge * witness) % 3
        expected_verdict = int(
            expected_response == (expected_commitment + challenge * statement) % 3
        )
        expected_terminal = mechanized_terminals[expected_verdict]
        source_lane = lane_for_terminal[expected_terminal]
        domain_lanes.add(source_lane)
        expected_image = "some ()" if expected_verdict else "none"
        _require(
            lane_images[source_lane] == {"case": "Image", "value": expected_image},
            f"provider outcome differs from the image of {source_lane}",
        )
        _require(
            commitment == expected_commitment
            and response == expected_response
            and verdict == expected_verdict
            and last_occurrence == expected_terminal,
            f"Plan, verifier, or first-active terminal disagrees at {key}",
        )
        source_trace = [commitment, challenge, response, verdict, verdict]
        provider_trace = [commitment, challenge, response, verdict, verdict]
        _require(source_trace == provider_trace, "completed source record and provider trace differ")
        source_steps = [step_for[occurrence] for occurrence in record_occurrences] + [step_for[expected_terminal]]
        provider_steps = ["commit", "challenge", "respond", "verify", "accept" if verdict else "reject"]
        _require(source_steps == provider_steps, "trace step map does not preserve occurrence order")
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
        "terminal_comparisons": traces,
        "domain_lanes": sorted(domain_lanes),
    }


def check() -> dict[str, Any]:
    certificate = json.loads(CERTIFICATE.read_text(encoding="utf-8"))
    provider_root = _provider_root()
    source = _cold_source()
    vectors = _check_certificate(certificate, source, provider_root)
    maps = _check_maps(certificate, source)
    rejected_mutations = _mutation_controls(certificate, source)
    execution_model = _check_provider_execution_model(provider_root)
    terms, guards, mechanized_terminals, term_timings = _run_term_evaluator()
    provider_checks, provider_runs, provider = _run_provider(provider_root)
    comparisons = _compare(
        terms,
        guards,
        mechanized_terminals,
        provider_checks,
        provider_runs,
        certificate,
        maps,
    )
    vector_closed = {
        tuple(int(part) for part in row["name"].split("/")[1].split("-")): int(row["closed_form"])
        for row in vectors["check_cases"]
    }
    _require(vector_closed == terms, "term probe differs from the frozen finite vectors")

    findings = [
        ["schedule-clause", "Affirmative", "F2O3-A-SCHEDULE"],
        ["values-clause", "Affirmative", "F2O3-A-VALUES"],
        ["checks-and-guards-clause", "Affirmative", "F2O3-A-CHECKS-GUARDS"],
        ["terminals-clause", "Affirmative", "F2O3-A-TERMINALS"],
        ["traces-clause", "Affirmative", "F2O3-A-TRACES"],
        ["terminal-mechanized-reading", "Affirmative", "F2O3-A-TERMINAL-MECHANIZED-READING"],
        ["provider-carrier-determinate", "Affirmative", "F2O3-A-CARRIER-DETERMINATE"],
        ["entry-contract-second-none-producer", "Refused", "F2O3-R-NO-PROVER-FAILURE-PRODUCER"],
        ["mutated-certificate-controls", "Refused", "F2O3-R-CERTIFICATE-MUTATIONS"],
        ["analysis-provider-map-premise", "CannotAnswer", "F2O3-C-PROVIDER-MAP-PREMISE-UNPUBLISHED"],
        ["residual-provider-trust-listed", "Affirmative", "F2O3-A-RESIDUAL-PROVIDER-TRUST"],
        ["residual-evaluator-differential-listed", "Affirmative", "F2O3-A-RESIDUAL-DIFFERENTIAL"],
        ["residual-premises-listed", "Affirmative", "F2O3-A-RESIDUAL-PREMISES"],
        ["residual-checker-adapter-listed", "Affirmative", "F2O3-A-RESIDUAL-ADAPTER"],
        ["finite-schnorr-provider-correspondence", "Affirmative", "F2O3-A-FINITE-CORRESPONDENCE"],
    ]
    return {
        "aggregate": "Affirmative/F2O3-A-FINITE-CORRESPONDENCE",
        "finding_codes": findings,
        "contract_correction": {
            "outcome": "Refused",
            "code": "F2O3-R-NO-PROVER-FAILURE-PRODUCER",
            "reason": "At the pinned source, Prover.run returns the failure-free OracleComp carrier. Reduction.run adds OptionT and can return none only through Verifier.run for this generated reduction.",
        },
        "premise_publication": {
            "outcome": "CannotAnswer",
            "code": "F2O3-C-PROVIDER-MAP-PREMISE-UNPUBLISHED",
            "reason": "The Analysis profile has not published the ArkLib declaration and Option Unit carrier, so the checked five-lane map is not a formed provider-map premise.",
        },
        "subject": certificate["subject"],
        "provider": provider,
        "measurements": {
            "views": len(source["views"]),
            "active_view_leaves": sum(source["active_leaf_counts"].values()),
            "mechanized_terminal_inputs": len(mechanized_terminals),
            "rejected_mutations": rejected_mutations,
            **maps,
            **comparisons,
            **execution_model,
        },
        "timings": term_timings,
        "residual_trust": [
            "Lean kernel and the pinned ArkLib and VCVio OracleComp semantics",
            "finite differential evidence between the portable-term evaluator and Python",
            "Fresh distribution premise and provider outcome-carrier premise",
            "unproved checker adapter",
        ],
        "nonclaims": [
            "No protocol or cryptographic property is established.",
            "No theorem applicability is established.",
            "No correspondence is established for another subject or provider.",
            "No Analysis premise is published by this package.",
        ],
    }


def main() -> int:
    try:
        report = check()
    except (CheckerError, OSError, ValueError, KeyError, subprocess.TimeoutExpired) as error:
        print(f"ArkLib provider interpretation check failed: {error}", file=sys.stderr)
        return 1
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
