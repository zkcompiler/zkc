#!/usr/bin/env python3
"""Audit evaluation package ownership and declared lifecycle dispositions."""

from __future__ import annotations

import argparse
from collections import Counter
from collections.abc import Mapping, Sequence
import json
from pathlib import Path, PurePosixPath
import re
import subprocess
from typing import Any

from checks import run


ROOT = run.ROOT
DEFAULT_CATALOG = ROOT / "evaluation" / "lifecycle.json"
TOP_FIELDS = frozenset(("schema_version", "groups", "assets"))
GROUP_FIELDS = frozenset(("id", "disposition", "purpose", "exit_rule", "checks"))
ASSET_FIELDS = frozenset(("path", "role", "disposition", "exit_rule"))
DISPOSITIONS = frozenset(("retain", "promote-then-retire", "active-sequence"))
ID_PATTERN = re.compile(r"[a-z][a-z0-9]*(?:-[a-z0-9]+)*\Z")


class LifecycleError(ValueError):
    """The lifecycle catalog is malformed or inconsistent with the tree."""


def _strict_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise LifecycleError(f"duplicate JSON key: {key!r}")
        result[key] = value
    return result


def _exact_fields(
    value: Mapping[str, Any], expected: frozenset[str], where: str
) -> None:
    missing = sorted(expected - set(value))
    extra = sorted(set(value) - expected)
    if missing or extra:
        raise LifecycleError(f"{where} has missing={missing} unexpected={extra}")


def _nonempty_string(value: Any, where: str) -> str:
    if not isinstance(value, str) or not value.strip():
        raise LifecycleError(f"{where} must be a non-empty string")
    return value


def _string_list(value: Any, where: str) -> tuple[str, ...]:
    if not isinstance(value, list) or not value:
        raise LifecycleError(f"{where} must be a non-empty array")
    result = tuple(
        _nonempty_string(item, f"{where}[{index}]") for index, item in enumerate(value)
    )
    if len(result) != len(set(result)):
        raise LifecycleError(f"{where} must not contain duplicates")
    return result


def load_catalog(path: Path = DEFAULT_CATALOG) -> Mapping[str, Any]:
    try:
        raw = json.loads(path.read_bytes(), object_pairs_hook=_strict_object)
    except (OSError, json.JSONDecodeError) as error:
        raise LifecycleError(
            f"cannot load lifecycle catalog {path}: {error}"
        ) from error
    if not isinstance(raw, dict):
        raise LifecycleError("lifecycle catalog must be an object")
    _exact_fields(raw, TOP_FIELDS, "catalog")
    if raw["schema_version"] != 1:
        raise LifecycleError("catalog.schema_version must be 1")
    if not isinstance(raw["groups"], list) or not raw["groups"]:
        raise LifecycleError("catalog.groups must be a non-empty array")
    if not isinstance(raw["assets"], list):
        raise LifecycleError("catalog.assets must be an array")

    group_ids: set[str] = set()
    check_ids: set[str] = set()
    for index, group in enumerate(raw["groups"]):
        where = f"catalog.groups[{index}]"
        if not isinstance(group, dict):
            raise LifecycleError(f"{where} must be an object")
        _exact_fields(group, GROUP_FIELDS, where)
        group_id = _nonempty_string(group["id"], f"{where}.id")
        if not ID_PATTERN.fullmatch(group_id) or group_id in group_ids:
            raise LifecycleError(f"{where}.id is invalid or duplicated: {group_id!r}")
        group_ids.add(group_id)
        if group["disposition"] not in DISPOSITIONS:
            raise LifecycleError(f"{where}.disposition is unsupported")
        _nonempty_string(group["purpose"], f"{where}.purpose")
        _nonempty_string(group["exit_rule"], f"{where}.exit_rule")
        for check_id in _string_list(group["checks"], f"{where}.checks"):
            if check_id in check_ids:
                raise LifecycleError(f"check is assigned more than once: {check_id}")
            check_ids.add(check_id)

    asset_paths: set[str] = set()
    for index, asset in enumerate(raw["assets"]):
        where = f"catalog.assets[{index}]"
        if not isinstance(asset, dict):
            raise LifecycleError(f"{where} must be an object")
        _exact_fields(asset, ASSET_FIELDS, where)
        path = _nonempty_string(asset["path"], f"{where}.path")
        normalized = PurePosixPath(path)
        if len(normalized.parts) != 1 or path != normalized.as_posix():
            raise LifecycleError(f"{where}.path must name one evaluation package")
        if path in asset_paths:
            raise LifecycleError(f"asset path is assigned more than once: {path}")
        asset_paths.add(path)
        _nonempty_string(asset["role"], f"{where}.role")
        if asset["disposition"] not in DISPOSITIONS:
            raise LifecycleError(f"{where}.disposition is unsupported")
        _nonempty_string(asset["exit_rule"], f"{where}.exit_rule")
    return raw


def _package_for_check(check: Mapping[str, Any]) -> str | None:
    candidates: set[str] = set()
    values = list(check["source_paths"])
    if check["execution"]["kind"] == "command":
        values.extend(check["execution"]["argv"])
    for value in values:
        path = PurePosixPath(value)
        if len(path.parts) >= 3 and path.parts[0] == "evaluation":
            package = path.parts[1]
            if (ROOT / "evaluation" / package).is_dir():
                candidates.add(package)
    if not candidates:
        return None
    if len(candidates) != 1:
        raise LifecycleError(
            f"check {check['id']} reaches multiple evaluation packages: {sorted(candidates)}"
        )
    return next(iter(candidates))


def _tracked_files() -> tuple[str, ...]:
    completed = subprocess.run(
        ("git", "ls-files", "evaluation"),
        cwd=ROOT,
        check=True,
        capture_output=True,
        text=True,
    )
    return tuple(line for line in completed.stdout.splitlines() if line)


def _metrics(package: str, tracked: Sequence[str]) -> dict[str, int]:
    prefix = f"evaluation/{package}/"
    files = [ROOT / path for path in tracked if path.startswith(prefix)]
    byte_count = 0
    line_count = 0
    for path in files:
        encoded = path.read_bytes()
        byte_count += len(encoded)
        line_count += encoded.count(b"\n") + bool(
            encoded and not encoded.endswith(b"\n")
        )
    return {
        "tracked_files": len(files),
        "tracked_bytes": byte_count,
        "tracked_lines": line_count,
    }


def audit(manifest: run.Manifest, catalog: Mapping[str, Any]) -> dict[str, Any]:
    findings: list[dict[str, Any]] = []
    by_id = {check["id"]: check for check in manifest.checks}
    research_ids = {
        check["id"]
        for check in manifest.checks
        if check["classification"] == "research-falsifier"
    }
    assigned_ids = {
        check_id for group in catalog["groups"] for check_id in group["checks"]
    }
    if research_ids != assigned_ids:
        findings.append(
            {
                "kind": "research-check-coverage",
                "missing": sorted(research_ids - assigned_ids),
                "unexpected": sorted(assigned_ids - research_ids),
            }
        )

    tracked = _tracked_files()
    tracked_packages = {
        PurePosixPath(path).parts[1]
        for path in tracked
        if len(PurePosixPath(path).parts) >= 3
    }
    assets = {asset["path"]: asset for asset in catalog["assets"]}
    package_records: list[dict[str, Any]] = []
    mapped_packages: set[str] = set(assets)
    dispositions: Counter[str] = Counter(
        asset["disposition"] for asset in assets.values()
    )

    for group in catalog["groups"]:
        dispositions[group["disposition"]] += len(group["checks"])
        for check_id in group["checks"]:
            check = by_id.get(check_id)
            if check is None:
                continue
            try:
                package = _package_for_check(check)
            except LifecycleError as error:
                findings.append(
                    {
                        "kind": "check-package-routing",
                        "check": check_id,
                        "message": str(error),
                    }
                )
                continue
            if package is None:
                findings.append(
                    {
                        "kind": "check-package-routing",
                        "check": check_id,
                        "message": "no evaluation package found",
                    }
                )
                continue
            if package in mapped_packages:
                findings.append(
                    {
                        "kind": "package-assigned-more-than-once",
                        "package": package,
                        "check": check_id,
                    }
                )
                continue
            mapped_packages.add(package)
            package_records.append(
                {
                    "package": package,
                    "check": check_id,
                    "group": group["id"],
                    "disposition": group["disposition"],
                    "cost": check["cost"],
                    "methods": check["methods"],
                    **_metrics(package, tracked),
                }
            )

    if tracked_packages != mapped_packages:
        findings.append(
            {
                "kind": "tracked-package-coverage",
                "missing": sorted(tracked_packages - mapped_packages),
                "unexpected": sorted(mapped_packages - tracked_packages),
            }
        )
    for package, asset in assets.items():
        package_records.append(
            {
                "package": package,
                "check": None,
                "group": asset["role"],
                "disposition": asset["disposition"],
                "cost": None,
                "methods": [],
                **_metrics(package, tracked),
            }
        )

    package_records.sort(key=lambda item: item["package"])
    return {
        "schema_version": 1,
        "manifest_sha256": manifest.digest,
        "outcome": "pass" if not findings else "fail",
        "summary": {
            "packages": len(package_records),
            "research_checks": len(research_ids),
            "tracked_files": sum(item["tracked_files"] for item in package_records),
            "tracked_bytes": sum(item["tracked_bytes"] for item in package_records),
            "tracked_lines": sum(item["tracked_lines"] for item in package_records),
            "dispositions": dict(sorted(dispositions.items())),
            "findings": len(findings),
        },
        "largest_packages": sorted(
            package_records,
            key=lambda item: (-item["tracked_lines"], item["package"]),
        )[:10],
        "packages": package_records,
        "findings": findings,
    }


def _write_json(path: Path, report: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    temporary.replace(path)


def _parse_arguments(argv: Sequence[str] | None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, default=run.DEFAULT_MANIFEST)
    parser.add_argument("--catalog", type=Path, default=DEFAULT_CATALOG)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--check", action="store_true")
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    arguments = _parse_arguments(argv)
    try:
        manifest = run.load_manifest(arguments.manifest)
        catalog = load_catalog(arguments.catalog)
        report = audit(manifest, catalog)
    except (run.ManifestError, LifecycleError, subprocess.SubprocessError) as error:
        print(f"evaluation lifecycle error: {error}")
        return 2
    if arguments.output:
        _write_json(arguments.output.resolve(), report)
    summary = report["summary"]
    print(
        "Evaluation lifecycle: "
        f"{summary['packages']} packages, {summary['research_checks']} research checks, "
        f"{summary['tracked_lines']} tracked lines, {summary['findings']} findings"
    )
    if arguments.output:
        print(f"Report: {arguments.output.resolve()}")
    if arguments.check and report["outcome"] != "pass":
        for finding in report["findings"]:
            print(f"FAIL {finding['kind']}")
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
