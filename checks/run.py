#!/usr/bin/env python3
"""Run repository checks from the declared evidence manifest.

This module is deliberately limited to orchestration and provenance.  It does
not reinterpret a check result as a semantic, security, or theorem claim.
"""

from __future__ import annotations

import argparse
from collections import Counter
from collections.abc import Iterable, Mapping, Sequence
from dataclasses import dataclass
from datetime import UTC, datetime
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import platform
import re
import shutil
import subprocess
import sys
import time
from typing import Any, NoReturn


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_MANIFEST = Path(__file__).with_name("manifest.json")
ID_PATTERN = re.compile(r"[a-z][a-z0-9]*(?:[.-][a-z0-9]+)*\Z")

TOP_LEVEL_FIELDS = frozenset(("schema_version", "tiers", "checks"))
TIER_FIELDS = frozenset(("title", "purpose"))
CHECK_FIELDS = frozenset(
    (
        "id",
        "title",
        "subject",
        "claim",
        "classification",
        "methods",
        "source_paths",
        "tiers",
        "cost",
        "environment",
        "shardability",
        "blocking",
        "nonclaims",
        "execution",
    )
)
COMMAND_EXECUTION_FIELDS = frozenset(("kind", "argv", "cwd", "requires", "artifacts"))
EXTERNAL_EXECUTION_FIELDS = frozenset(("kind", "workflow", "event"))

CLASSIFICATIONS = frozenset(
    (
        "control-plane",
        "repository-policy",
        "static-quality",
        "durable-conformance",
        "implementation-regression",
        "research-falsifier",
        "external-correspondence",
        "diagnostic",
    )
)
METHODS = frozenset(
    (
        "policy",
        "static-analysis",
        "unit",
        "known-answer",
        "negative",
        "roundtrip",
        "differential",
        "property",
        "metamorphic",
        "mutation",
        "bounded-exhaustive",
        "translation-validation",
        "fuzz",
        "sanitizer",
        "upstream-replay",
        "formal-reading",
        "diagnostic",
    )
)
COSTS = frozenset(("instant", "short", "medium", "long", "very-long", "external"))
ENVIRONMENTS = frozenset(
    (
        "source-only",
        "python-stdlib",
        "locked-python",
        "rust-toolchain",
        "configured-native-build",
        "network-resolved-tool",
        "pinned-external-checkout",
    )
)
SHARDABILITY = frozenset(("none", "case", "fixture-group", "target", "external"))
PLACEHOLDERS = frozenset(("repo", "python", "build_dir", "artifacts"))


class ManifestError(ValueError):
    """The check manifest is malformed or internally inconsistent."""


@dataclass(frozen=True)
class Manifest:
    raw: Mapping[str, Any]
    digest: str
    path: Path

    @property
    def tiers(self) -> Mapping[str, Mapping[str, str]]:
        return self.raw["tiers"]

    @property
    def checks(self) -> tuple[Mapping[str, Any], ...]:
        return tuple(self.raw["checks"])


class _StrictObject(dict[str, Any]):
    """Marker type used only to make duplicate-key errors precise."""


def _fail(message: str) -> NoReturn:
    raise ManifestError(message)


def _strict_object(pairs: list[tuple[str, Any]]) -> _StrictObject:
    result: _StrictObject = _StrictObject()
    for key, value in pairs:
        if key in result:
            _fail(f"duplicate JSON key: {key!r}")
        result[key] = value
    return result


def _expect_object(value: Any, context: str) -> Mapping[str, Any]:
    if not isinstance(value, dict):
        _fail(f"{context} must be an object")
    return value


def _expect_exact_fields(
    value: Mapping[str, Any], expected: frozenset[str], context: str
) -> None:
    actual = frozenset(value)
    missing = sorted(expected - actual)
    extra = sorted(actual - expected)
    if missing or extra:
        details: list[str] = []
        if missing:
            details.append("missing " + ", ".join(missing))
        if extra:
            details.append("unexpected " + ", ".join(extra))
        _fail(f"{context} has invalid fields ({'; '.join(details)})")


def _expect_string(value: Any, context: str) -> str:
    if not isinstance(value, str) or not value.strip():
        _fail(f"{context} must be a non-empty string")
    return value


def _expect_string_list(value: Any, context: str) -> tuple[str, ...]:
    if not isinstance(value, list) or not value:
        _fail(f"{context} must be a non-empty array")
    result = tuple(
        _expect_string(item, f"{context}[{index}]") for index, item in enumerate(value)
    )
    if len(result) != len(set(result)):
        _fail(f"{context} must not contain duplicates")
    return result


def _expect_enum(value: Any, allowed: frozenset[str], context: str) -> str:
    result = _expect_string(value, context)
    if result not in allowed:
        _fail(f"{context} has unsupported value {result!r}")
    return result


def _validate_relative_path(value: Any, context: str) -> str:
    result = _expect_string(value, context)
    path = PurePosixPath(result)
    if path.is_absolute() or ".." in path.parts or result != path.as_posix():
        _fail(f"{context} must be a normalized repository-relative path")
    return result


def _validate_template(value: str, context: str) -> None:
    fields = re.findall(r"\{([^{}]+)\}", value)
    unknown = sorted(set(fields) - PLACEHOLDERS)
    if unknown:
        _fail(f"{context} uses unknown placeholders: {', '.join(unknown)}")
    residual = re.sub(r"\{[^{}]+\}", "", value)
    if "{" in residual or "}" in residual:
        _fail(f"{context} has malformed placeholder syntax")


def _validate_execution(value: Any, context: str) -> None:
    execution = _expect_object(value, context)
    kind = _expect_string(execution.get("kind"), f"{context}.kind")
    if kind == "command":
        _expect_exact_fields(execution, COMMAND_EXECUTION_FIELDS, context)
        argv = _expect_string_list(execution["argv"], f"{context}.argv")
        cwd = _validate_relative_path(execution["cwd"], f"{context}.cwd")
        requires = _expect_string_list(execution["requires"], f"{context}.requires")
        artifacts = execution["artifacts"]
        if not isinstance(artifacts, list):
            _fail(f"{context}.artifacts must be an array")
        artifact_names = tuple(
            _validate_relative_path(item, f"{context}.artifacts[{index}]")
            for index, item in enumerate(artifacts)
        )
        if len(artifact_names) != len(set(artifact_names)):
            _fail(f"{context}.artifacts must not contain duplicates")
        for index, argument in enumerate(argv):
            _validate_template(argument, f"{context}.argv[{index}]")
        _validate_template(cwd, f"{context}.cwd")
        for index, requirement in enumerate(requires):
            _validate_template(requirement, f"{context}.requires[{index}]")
        return
    if kind == "external-workflow":
        _expect_exact_fields(execution, EXTERNAL_EXECUTION_FIELDS, context)
        _validate_relative_path(execution["workflow"], f"{context}.workflow")
        _expect_string(execution["event"], f"{context}.event")
        return
    _fail(f"{context}.kind has unsupported value {kind!r}")


def _validate_manifest(raw: Any) -> None:
    manifest = _expect_object(raw, "manifest")
    _expect_exact_fields(manifest, TOP_LEVEL_FIELDS, "manifest")
    if manifest["schema_version"] != 1:
        _fail("manifest.schema_version must be 1")

    tiers = _expect_object(manifest["tiers"], "manifest.tiers")
    if not tiers:
        _fail("manifest.tiers must not be empty")
    for tier_id, tier_value in tiers.items():
        if not isinstance(tier_id, str) or not ID_PATTERN.fullmatch(tier_id):
            _fail(f"invalid tier identifier: {tier_id!r}")
        tier = _expect_object(tier_value, f"manifest.tiers.{tier_id}")
        _expect_exact_fields(tier, TIER_FIELDS, f"manifest.tiers.{tier_id}")
        _expect_string(tier["title"], f"manifest.tiers.{tier_id}.title")
        _expect_string(tier["purpose"], f"manifest.tiers.{tier_id}.purpose")

    checks = manifest["checks"]
    if not isinstance(checks, list) or not checks:
        _fail("manifest.checks must be a non-empty array")
    seen_ids: set[str] = set()
    for index, check_value in enumerate(checks):
        context = f"manifest.checks[{index}]"
        check = _expect_object(check_value, context)
        _expect_exact_fields(check, CHECK_FIELDS, context)
        check_id = _expect_string(check["id"], f"{context}.id")
        if not ID_PATTERN.fullmatch(check_id):
            _fail(f"{context}.id is not a stable lowercase identifier")
        if check_id in seen_ids:
            _fail(f"duplicate check identifier: {check_id}")
        seen_ids.add(check_id)
        _expect_string(check["title"], f"{context}.title")
        _expect_string(check["subject"], f"{context}.subject")
        _expect_string(check["claim"], f"{context}.claim")
        _expect_enum(
            check["classification"], CLASSIFICATIONS, f"{context}.classification"
        )
        methods = _expect_string_list(check["methods"], f"{context}.methods")
        for method_index, method in enumerate(methods):
            _expect_enum(method, METHODS, f"{context}.methods[{method_index}]")
        source_paths = _expect_string_list(
            check["source_paths"], f"{context}.source_paths"
        )
        for source_index, source_path in enumerate(source_paths):
            normalized = _validate_relative_path(
                source_path, f"{context}.source_paths[{source_index}]"
            )
            if not (ROOT / normalized).exists():
                _fail(
                    f"{context}.source_paths[{source_index}] does not exist: {normalized}"
                )
        check_tiers = _expect_string_list(check["tiers"], f"{context}.tiers")
        unknown_tiers = sorted(set(check_tiers) - set(tiers))
        if unknown_tiers:
            _fail(f"{context}.tiers contains unknown tiers: {', '.join(unknown_tiers)}")
        _expect_enum(check["cost"], COSTS, f"{context}.cost")
        _expect_enum(check["environment"], ENVIRONMENTS, f"{context}.environment")
        _expect_enum(check["shardability"], SHARDABILITY, f"{context}.shardability")
        if not isinstance(check["blocking"], bool):
            _fail(f"{context}.blocking must be a boolean")
        _expect_string_list(check["nonclaims"], f"{context}.nonclaims")
        _validate_execution(check["execution"], f"{context}.execution")


def load_manifest(path: Path = DEFAULT_MANIFEST) -> Manifest:
    """Load and strictly validate a manifest, rejecting duplicate JSON keys."""

    resolved = path.resolve()
    try:
        encoded = resolved.read_bytes()
    except OSError as error:
        raise ManifestError(f"cannot read manifest {resolved}: {error}") from error
    try:
        raw = json.loads(encoded, object_pairs_hook=_strict_object)
    except json.JSONDecodeError as error:
        raise ManifestError(f"invalid JSON in {resolved}: {error}") from error
    _validate_manifest(raw)
    return Manifest(raw=raw, digest=hashlib.sha256(encoded).hexdigest(), path=resolved)


def select_checks(
    manifest: Manifest,
    tier_ids: Sequence[str],
    check_ids: Sequence[str],
) -> tuple[Mapping[str, Any], ...]:
    """Select the stable manifest order union of tiers and explicit IDs."""

    known_tiers = set(manifest.tiers)
    unknown_tiers = sorted(set(tier_ids) - known_tiers)
    if unknown_tiers:
        raise ManifestError(f"unknown tier(s): {', '.join(unknown_tiers)}")
    by_id = {check["id"]: check for check in manifest.checks}
    unknown_checks = sorted(set(check_ids) - set(by_id))
    if unknown_checks:
        raise ManifestError(f"unknown check(s): {', '.join(unknown_checks)}")
    selected_ids = set(check_ids)
    for check in manifest.checks:
        if set(tier_ids).intersection(check["tiers"]):
            selected_ids.add(check["id"])
    return tuple(check for check in manifest.checks if check["id"] in selected_ids)


def _utc_now() -> str:
    return datetime.now(UTC).isoformat(timespec="seconds")


def _default_artifacts_dir() -> Path:
    stamp = datetime.now(UTC).strftime("%Y%m%dT%H%M%SZ")
    return ROOT / "target" / "checks" / stamp


def _git_value(arguments: Sequence[str]) -> str | None:
    completed = subprocess.run(
        ("git", *arguments),
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
    )
    if completed.returncode != 0:
        return None
    return completed.stdout.strip()


def _provenance() -> dict[str, Any]:
    revision = _git_value(("rev-parse", "HEAD"))
    dirty_output = _git_value(("status", "--porcelain"))
    return {
        "revision": revision,
        "worktree": "unknown"
        if dirty_output is None
        else ("dirty" if dirty_output else "clean"),
        "python": sys.version.split()[0],
        "platform": platform.platform(),
    }


def _resolved_context(build_dir: Path, artifacts_dir: Path) -> dict[str, str]:
    return {
        "repo": str(ROOT),
        "python": sys.executable,
        "build_dir": str(build_dir.resolve()),
        "artifacts": str(artifacts_dir.resolve()),
    }


def _format_template(value: str, context: Mapping[str, str]) -> str:
    try:
        return value.format_map(context)
    except (KeyError, ValueError) as error:
        raise ManifestError(
            f"cannot resolve command template {value!r}: {error}"
        ) from error


def _missing_requirements(
    requirements: Iterable[str], context: Mapping[str, str]
) -> tuple[str, ...]:
    missing: list[str] = []
    for raw_requirement in requirements:
        requirement = _format_template(raw_requirement, context)
        if "/" in requirement:
            if not Path(requirement).exists():
                missing.append(requirement)
        elif shutil.which(requirement) is None:
            missing.append(requirement)
    return tuple(missing)


def _safe_directory_name(check_id: str) -> str:
    return check_id.replace(".", "-")


def _write_json(path: Path, value: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(
        json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    temporary.replace(path)


def _base_result(check: Mapping[str, Any]) -> dict[str, Any]:
    return {
        "id": check["id"],
        "title": check["title"],
        "classification": check["classification"],
        "methods": check["methods"],
        "blocking": check["blocking"],
        "status": "not-run",
        "started_at": None,
        "duration_seconds": 0.0,
        "returncode": None,
        "command": None,
        "working_directory": None,
        "stdout_log": None,
        "stderr_log": None,
        "message": None,
        "declared_artifacts": [],
    }


def _run_check(
    check: Mapping[str, Any],
    *,
    build_dir: Path,
    artifacts_dir: Path,
    dry_run: bool,
) -> dict[str, Any]:
    result = _base_result(check)
    execution = check["execution"]
    if execution["kind"] == "external-workflow":
        result["status"] = "external"
        result["message"] = (
            f"owned by {execution['workflow']} ({execution['event']}); "
            "no local pass is inferred"
        )
        return result

    check_dir = artifacts_dir / _safe_directory_name(check["id"])
    context = _resolved_context(build_dir, check_dir)
    command = [_format_template(argument, context) for argument in execution["argv"]]
    working_directory = Path(_format_template(execution["cwd"], context)).resolve()
    declared_artifacts = [
        str((check_dir / artifact).resolve()) for artifact in execution["artifacts"]
    ]
    result["command"] = command
    result["working_directory"] = str(working_directory)
    result["declared_artifacts"] = declared_artifacts
    missing = _missing_requirements(execution["requires"], context)
    if missing:
        result["status"] = "cannot-run"
        result["message"] = "missing requirement(s): " + ", ".join(missing)
        return result
    if not working_directory.is_dir():
        result["status"] = "cannot-run"
        result["message"] = f"working directory does not exist: {working_directory}"
        return result
    if dry_run:
        result["status"] = "dry-run"
        result["message"] = "command resolved but was not executed"
        return result

    check_dir.mkdir(parents=True, exist_ok=True)
    stdout_path = check_dir / "stdout.log"
    stderr_path = check_dir / "stderr.log"
    environment = os.environ.copy()
    environment["PYTHONDONTWRITEBYTECODE"] = "1"
    environment["ZKC_CHECK_ARTIFACTS"] = str(check_dir.resolve())
    result["started_at"] = _utc_now()
    started = time.perf_counter()
    try:
        with (
            stdout_path.open("w", encoding="utf-8") as stdout,
            stderr_path.open("w", encoding="utf-8") as stderr,
        ):
            completed = subprocess.run(
                command,
                cwd=working_directory,
                env=environment,
                check=False,
                stdout=stdout,
                stderr=stderr,
                text=True,
            )
    except OSError as error:
        result["duration_seconds"] = round(time.perf_counter() - started, 6)
        result["status"] = "cannot-run"
        result["message"] = str(error)
        return result
    result["duration_seconds"] = round(time.perf_counter() - started, 6)
    result["returncode"] = completed.returncode
    result["stdout_log"] = str(stdout_path.resolve())
    result["stderr_log"] = str(stderr_path.resolve())
    if completed.returncode == 0:
        missing_artifacts = [
            path for path in declared_artifacts if not Path(path).is_file()
        ]
        if missing_artifacts:
            result["status"] = "fail"
            result["message"] = "declared artifact(s) were not produced: " + ", ".join(
                missing_artifacts
            )
        else:
            result["status"] = "pass"
        return result
    result["status"] = "fail"
    result["message"] = f"command exited with status {completed.returncode}"
    return result


def _outcome(results: Sequence[Mapping[str, Any]], dry_run: bool) -> str:
    if dry_run:
        return "dry-run"
    if any(result["blocking"] and result["status"] == "fail" for result in results):
        return "failed"
    if any(
        result["status"] in {"cannot-run", "external", "not-run"} for result in results
    ):
        return "incomplete"
    if any(result["status"] == "fail" for result in results):
        return "passed-with-observations"
    return "passed"


def _exit_code(outcome: str) -> int:
    if outcome == "failed":
        return 1
    if outcome == "incomplete":
        return 2
    return 0


def _print_check(check: Mapping[str, Any]) -> None:
    methods = ",".join(check["methods"])
    tiers = ",".join(check["tiers"])
    print(
        f"{check['id']:<48} {check['cost']:<10} {check['classification']:<26} "
        f"[{tiers}] {methods}"
    )


def _selection_arguments(parser: argparse.ArgumentParser) -> None:
    parser.add_argument(
        "--tier", action="append", default=[], help="select a declared tier"
    )
    parser.add_argument(
        "--check",
        action="append",
        default=[],
        dest="check_ids",
        help="select one stable check ID",
    )


def _parse_arguments(argv: Sequence[str] | None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    subparsers = parser.add_subparsers(dest="operation", required=True)

    subparsers.add_parser("validate", help="strictly validate the manifest")

    list_parser = subparsers.add_parser("list", help="list checks without running them")
    _selection_arguments(list_parser)
    list_parser.add_argument("--json", action="store_true")

    run_parser = subparsers.add_parser("run", help="run a tier or stable check IDs")
    _selection_arguments(run_parser)
    run_parser.add_argument("--build-dir", type=Path, default=ROOT / "build")
    run_parser.add_argument("--artifacts-dir", type=Path)
    run_parser.add_argument("--result", type=Path)
    run_parser.add_argument("--keep-going", action="store_true")
    run_parser.add_argument("--dry-run", action="store_true")
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    arguments = _parse_arguments(argv)
    try:
        manifest = load_manifest(arguments.manifest)
        if arguments.operation == "validate":
            print(
                f"Manifest {manifest.path} is valid: "
                f"{len(manifest.checks)} checks, {len(manifest.tiers)} tiers, "
                f"sha256:{manifest.digest}"
            )
            return 0

        tier_ids = tuple(arguments.tier)
        check_ids = tuple(arguments.check_ids)
        if not tier_ids and not check_ids:
            tier_ids = ("developer",)
        checks = select_checks(manifest, tier_ids, check_ids)
        if not checks:
            raise ManifestError("selection is empty")
        if arguments.operation == "list":
            if arguments.json:
                print(json.dumps(checks, indent=2))
            else:
                for check in checks:
                    _print_check(check)
            return 0

        artifacts_dir = (arguments.artifacts_dir or _default_artifacts_dir()).resolve()
        result_path = (arguments.result or artifacts_dir / "result.json").resolve()
        started_at = _utc_now()
        overall_started = time.perf_counter()
        results: list[dict[str, Any]] = []
        stop = False
        for ordinal, check in enumerate(checks, start=1):
            if stop:
                results.append(_base_result(check))
                continue
            print(
                f"[{ordinal}/{len(checks)}] {check['id']}: {check['title']}", flush=True
            )
            result = _run_check(
                check,
                build_dir=arguments.build_dir,
                artifacts_dir=artifacts_dir,
                dry_run=arguments.dry_run,
            )
            results.append(result)
            print(
                f"{result['status'].upper():<10} {check['id']} "
                f"({result['duration_seconds']:.3f}s)",
                flush=True,
            )
            if (
                result["status"] == "fail"
                and result["blocking"]
                and not arguments.keep_going
            ):
                stop = True
        outcome = _outcome(results, arguments.dry_run)
        counts = Counter(result["status"] for result in results)
        report = {
            "schema_version": 1,
            "manifest": {
                "path": str(manifest.path),
                "sha256": manifest.digest,
            },
            "selection": {"tiers": list(tier_ids), "checks": list(check_ids)},
            "provenance": _provenance(),
            "started_at": started_at,
            "finished_at": _utc_now(),
            "duration_seconds": round(time.perf_counter() - overall_started, 6),
            "outcome": outcome,
            "summary": dict(sorted(counts.items())),
            "results": results,
        }
        _write_json(result_path, report)
        print(
            f"Outcome: {outcome}; {len(results)} checks; result: {result_path}",
            flush=True,
        )
        return _exit_code(outcome)
    except ManifestError as error:
        print(f"check manifest error: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
