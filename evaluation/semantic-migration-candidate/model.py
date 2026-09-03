"""Direct, non-publishing audit of the migrated semantic-profile sources."""

from __future__ import annotations

import hashlib
import importlib.util
import json
from pathlib import Path
import sys
from types import ModuleType
from typing import Any


ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
CONTRACT = HERE / "candidate-contract.json"
PUBLISHED = ROOT / "docs-next/pir/profiles/published-identities.json"
REFERENCE_COMPILER = ROOT / "evaluation/semantic-profile-publication/reference_model.py"
COLD_COMPILER = ROOT / "evaluation/semantic-profile-publication/independent.py"


class CandidateError(RuntimeError):
    """The migrated direct-source rehearsal no longer closes."""


def _load(name: str, path: Path) -> ModuleType:
    if name in sys.modules:
        return sys.modules[name]
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise CandidateError(f"cannot load {path.relative_to(ROOT)}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def _strict_json(path: Path) -> Any:
    def object_pairs(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        result: dict[str, Any] = {}
        for key, value in pairs:
            if key in result:
                raise CandidateError(f"duplicate key {key!r} in {path}")
            result[key] = value
        return result

    try:
        return json.loads(path.read_bytes(), object_pairs_hook=object_pairs)
    except (OSError, json.JSONDecodeError) as error:
        raise CandidateError(f"cannot read {path}: {error}") from error


def _sha256(path: Path) -> str:
    try:
        return hashlib.sha256(path.read_bytes()).hexdigest()
    except OSError as error:
        raise CandidateError(f"cannot hash {path}") from error


def contract() -> dict[str, Any]:
    value = _strict_json(CONTRACT)
    if type(value) is not dict or set(value) != {
        "format",
        "baseline_identity_pin",
        "publication",
        "owner_pages",
        "profile_manifests",
        "gate_packages",
    }:
        raise CandidateError("rehearsal contract has another outer shape")
    if (
        value["format"] != "zkc.semantic-refreeze-rehearsal.v0"
        or value["publication"] != "forbidden"
    ):
        raise CandidateError("rehearsal contract format or publication policy differs")
    if len(value["owner_pages"]) != 6 or len(value["profile_manifests"]) != 8:
        raise CandidateError("rehearsal contract does not pin six pages and eight manifests")
    return value


def _source_inventory(value: dict[str, Any]) -> dict[str, Any]:
    paths: set[str] = set()
    pages: list[dict[str, str]] = []
    manifests: list[dict[str, str]] = []
    for kind, rows, output in (
        ("owner page", value["owner_pages"], pages),
        ("profile manifest", value["profile_manifests"], manifests),
    ):
        for row in rows:
            expected = {"path", "sha256"} | ({"key"} if kind == "profile manifest" else set())
            if type(row) is not dict or set(row) != expected:
                raise CandidateError(f"{kind} pin has another shape")
            path = row["path"]
            if path in paths:
                raise CandidateError(f"source path {path} is repeated")
            paths.add(path)
            observed = _sha256(ROOT / path)
            if observed != row["sha256"]:
                raise CandidateError(f"source pin drifted for {path}")
            output.append(dict(row))
    return {"owner_pages": pages, "profile_manifests": manifests}


def _publication_report(value: dict[str, Any]) -> dict[str, Any]:
    reference = _load("_zkc_migration_direct_publication", REFERENCE_COMPILER)
    cold = _load("_zkc_migration_direct_cold_publication", COLD_COMPILER)
    reference_table = reference.identity_table(reference.compile_repository())
    cold_table = cold.identity_table(cold.compile_repository())
    if reference_table != cold_table:
        raise CandidateError("publication compilers disagree on the migrated tree")

    baseline_path = ROOT / value["baseline_identity_pin"]
    baseline = _strict_json(baseline_path)
    if baseline.get("source_commit") != "9c05fd5b89f1c84a4ce7530d924a2ff0e4a786d5":
        raise CandidateError("pre-migration identity pin names another source commit")
    if set(baseline["profiles"]) != set(reference_table["profiles"]):
        raise CandidateError("pre-migration and current profile sets differ")
    rotated = [
        key
        for key, row in reference_table["profiles"].items()
        if row["profile_digest"] != baseline["profiles"][key]
    ]
    stable = [key for key in reference_table["profiles"] if key not in rotated]
    if len(rotated) != 17 or stable != ["analysis-kernel"]:
        raise CandidateError("migrated tree does not reproduce the expected 17/1 rotation")

    published = _strict_json(PUBLISHED)
    if not set(published["profiles"]) < set(reference_table["profiles"]):
        raise CandidateError("legacy publication is not a strict subset of current profiles")
    legacy_controls = {
        key: published["profiles"][key]["profile_digest"]
        != reference_table["profiles"][key]["profile_digest"]
        for key in published["profiles"]
    }
    if not all(legacy_controls.values()):
        raise CandidateError("one legacy published profile was accepted as current")
    return {
        "compiler_agreement": True,
        "candidate_identity_table": reference_table,
        "baseline_source_commit": baseline["source_commit"],
        "baseline_identity_pin_sha256": _sha256(baseline_path),
        "rotated_profiles": rotated,
        "stable_profiles": stable,
        "legacy_profile_refusals": legacy_controls,
    }


def _gate_report(value: dict[str, Any]) -> dict[str, Any]:
    packages = value["gate_packages"]
    if set(packages) != {
        "target_basis",
        "target_core",
        "owner_views",
        "terminal_contract",
    }:
        raise CandidateError("prerequisite gate inventory differs")

    basis = _load("_zkc_migration_target_basis", ROOT / packages["target_basis"])
    basis_results, basis_evidence = basis.evaluate()
    if not basis_results:
        raise CandidateError("target-basis gate returned no boundary results")

    core = _load("_zkc_migration_target_core", ROOT / packages["target_core"])
    core_report = core.run_gate()
    if core_report["passed"] != core_report["total"]:
        raise CandidateError("target-core gate did not close")

    views = _load("_zkc_migration_owner_views", ROOT / packages["owner_views"])
    view_report = views.run_gate()
    if view_report["passed"] != view_report["total"]:
        raise CandidateError("owner-view gate did not close")

    terminal = _load(
        "_zkc_migration_terminal_contract", ROOT / packages["terminal_contract"]
    )
    terminal_findings, terminal_metrics = terminal.evaluate()
    terminal_cases = {item.name: (item.outcome, item.code) for item in terminal_findings}
    if terminal_cases.get("migrated-terminal-contract-source") != (
        "Affirmative",
        "F0V2B2C1B5B1-A-MIGRATED-OWNER-CONTRACT",
    ):
        raise CandidateError("terminal gate did not admit the migrated owner shape")
    if terminal_cases.get("implicit-terminal-gating", (None,))[0] != "Refused":
        raise CandidateError("terminal gate did not refuse hidden gating")

    return {
        "target_basis": {
            "results": len(basis_results),
            "target_profile_digest": basis_evidence["target_interaction"][
                "profile_digest"
            ],
        },
        "target_core": {
            "passed": core_report["passed"],
            "total": core_report["total"],
            "identities": core_report["identities"],
        },
        "owner_views": {
            "passed": view_report["passed"],
            "total": view_report["total"],
            "aggregate": view_report["aggregate"],
            "law_field_selection": view_report["evidence"]["law_field_selection"],
        },
        "terminal_contract": {
            "findings": len(terminal_findings),
            "hidden_gating_counterexample": terminal_metrics[
                "hidden_gating_counterexample"
            ],
        },
    }


def build_report() -> dict[str, Any]:
    value = contract()
    published_before = _sha256(PUBLISHED)
    sources = _source_inventory(value)
    publication = _publication_report(value)
    gates = _gate_report(value)
    published_after = _sha256(PUBLISHED)
    if published_before != published_after:
        raise CandidateError("rehearsal modified the published identity table")
    return {
        "format": "zkc.semantic-refreeze-rehearsal.report.v0",
        "source_inventory": sources,
        "publication": publication,
        "prerequisite_gates": gates,
        "published_identity_sha256_before": published_before,
        "published_identity_sha256_after": published_after,
        "identity_finalization": "not-performed",
        "publication_disposition": "Hold",
        "nonclaims": [
            "publication or finalization of any candidate identity",
            "implementation or provider correspondence",
            "a protocol theorem, security property, or production claim",
        ],
    }
