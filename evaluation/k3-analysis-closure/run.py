#!/usr/bin/env python3
"""Run the bounded Analysis semantic-closure research gate."""

from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass
import json
import os
from pathlib import Path
import subprocess
import sys
import time
import unittest


ROOT = Path(__file__).resolve().parent


class TimingTextTestResult(unittest.TextTestResult):
    """Record bounded per-test latency without changing unittest semantics."""

    def __init__(
        self,
        stream: object,
        descriptions: bool,
        verbosity: int,
    ) -> None:
        super().__init__(stream, descriptions, verbosity)
        self.timings: list[dict[str, object]] = []
        self._started_at = 0.0
        self._status = "unknown"

    def startTest(self, test: unittest.TestCase) -> None:
        self._started_at = time.perf_counter()
        self._status = "unknown"
        super().startTest(test)

    def stopTest(self, test: unittest.TestCase) -> None:
        self.timings.append(
            {
                "id": test.id(),
                "class": f"{type(test).__module__}.{type(test).__qualname__}",
                "status": self._status,
                "elapsed_seconds": time.perf_counter() - self._started_at,
            }
        )
        super().stopTest(test)

    def addSuccess(self, test: unittest.TestCase) -> None:
        self._status = "pass"
        super().addSuccess(test)

    def addFailure(
        self,
        test: unittest.TestCase,
        err: tuple[type[BaseException], BaseException, object],
    ) -> None:
        self._status = "fail"
        super().addFailure(test, err)

    def addError(
        self,
        test: unittest.TestCase,
        err: tuple[type[BaseException], BaseException, object],
    ) -> None:
        self._status = "error"
        super().addError(test, err)

    def addSkip(self, test: unittest.TestCase, reason: str) -> None:
        self._status = "skip"
        super().addSkip(test, reason)

    def addExpectedFailure(
        self,
        test: unittest.TestCase,
        err: tuple[type[BaseException], BaseException, object],
    ) -> None:
        self._status = "expected-failure"
        super().addExpectedFailure(test, err)

    def addUnexpectedSuccess(self, test: unittest.TestCase) -> None:
        self._status = "unexpected-success"
        super().addUnexpectedSuccess(test)


@dataclass(frozen=True)
class IsolatedGroupResult:
    test_ids: tuple[str, ...]
    completed: subprocess.CompletedProcess[str]
    elapsed_seconds: float


def _cases(suite: unittest.TestSuite) -> list[unittest.TestCase]:
    result: list[unittest.TestCase] = []
    for child in suite:
        if isinstance(child, unittest.TestSuite):
            result.extend(_cases(child))
        else:
            result.append(child)
    return result


def _test_groups(suite: unittest.TestSuite, jobs: int) -> tuple[tuple[str, ...], ...]:
    test_ids = tuple(sorted(case.id() for case in _cases(suite)))
    group_count = min(jobs, len(test_ids))
    groups: list[list[str]] = [[] for _ in range(group_count)]
    for index, test_id in enumerate(test_ids):
        groups[index % group_count].append(test_id)
    return tuple(tuple(group) for group in groups)


def _run_isolated_group(test_ids: tuple[str, ...]) -> IsolatedGroupResult:
    environment = os.environ.copy()
    environment["PYTHONDONTWRITEBYTECODE"] = "1"
    started = time.perf_counter()
    completed = subprocess.run(
        [sys.executable, "-B", "-m", "unittest", "-v", *test_ids],
        cwd=ROOT / "tests",
        env=environment,
        check=False,
        capture_output=True,
        text=True,
    )
    return IsolatedGroupResult(
        test_ids,
        completed,
        time.perf_counter() - started,
    )


def _class_timings(tests: list[dict[str, object]]) -> list[dict[str, object]]:
    classes: dict[str, dict[str, object]] = {}
    for test in tests:
        class_name = str(test["class"])
        aggregate = classes.setdefault(
            class_name,
            {
                "class": class_name,
                "test_count": 0,
                "elapsed_seconds": 0.0,
                "statuses": {},
            },
        )
        aggregate["test_count"] = int(aggregate["test_count"]) + 1
        aggregate["elapsed_seconds"] = float(aggregate["elapsed_seconds"]) + float(
            test["elapsed_seconds"]
        )
        statuses = aggregate["statuses"]
        assert isinstance(statuses, dict)
        status = str(test["status"])
        statuses[status] = int(statuses.get(status, 0)) + 1
    return sorted(
        classes.values(),
        key=lambda item: (-float(item["elapsed_seconds"]), str(item["class"])),
    )


def _write_telemetry(path: Path, payload: dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--check",
        action="store_true",
        help="run the frozen bounded gate (also the default operation)",
    )
    parser.add_argument(
        "--jobs",
        type=int,
        default=1,
        help=(
            "run test cases in this many isolated processes; one retains the "
            "original single-process gate"
        ),
    )
    parser.add_argument(
        "--list-tests",
        action="store_true",
        help="list the exact discovered test IDs without executing them",
    )
    parser.add_argument(
        "--telemetry",
        type=Path,
        help="write non-authoritative timing and outcome telemetry as JSON",
    )
    args = parser.parse_args(argv)
    if args.jobs < 1:
        parser.error("--jobs must be positive")
    overall_started = time.perf_counter()
    discovery_started = time.perf_counter()
    suite = unittest.TestLoader().discover(
        str(ROOT / "tests"), top_level_dir=str(ROOT / "tests")
    )
    discovery_seconds = time.perf_counter() - discovery_started
    count = suite.countTestCases()
    test_ids = tuple(sorted(case.id() for case in _cases(suite)))
    if args.list_tests:
        print("\n".join(test_ids))
        return 0
    print(f"Analysis semantic closure: {count} tests")
    execution_started = time.perf_counter()
    test_timings: list[dict[str, object]] = []
    group_timings: list[dict[str, object]] = []
    if args.jobs == 1:
        result = unittest.TextTestRunner(
            verbosity=2,
            resultclass=TimingTextTestResult,
        ).run(suite)
        successful = result.wasSuccessful()
        test_timings = result.timings
    else:
        groups = _test_groups(suite, args.jobs)
        with ThreadPoolExecutor(max_workers=len(groups)) as executor:
            results = tuple(executor.map(_run_isolated_group, groups))
        successful = True
        for result in results:
            completed = result.completed
            if completed.stdout:
                print(completed.stdout, end="")
            if completed.stderr:
                print(completed.stderr, file=sys.stderr, end="")
            successful = successful and completed.returncode == 0
            group_timings.append(
                {
                    "test_ids": result.test_ids,
                    "test_count": len(result.test_ids),
                    "elapsed_seconds": result.elapsed_seconds,
                    "return_code": completed.returncode,
                }
            )
    execution_seconds = time.perf_counter() - execution_started
    if args.telemetry is not None:
        _write_telemetry(
            args.telemetry,
            {
                "schema_version": 1,
                "runner": "analysis-semantic-closure",
                "execution_mode": (
                    "one-process" if args.jobs == 1 else "isolated-processes"
                ),
                "jobs": args.jobs,
                "discovered_test_count": count,
                "discovery_seconds": discovery_seconds,
                "execution_seconds": execution_seconds,
                "total_seconds": time.perf_counter() - overall_started,
                "passed": successful,
                "tests": test_timings,
                "classes": _class_timings(test_timings),
                "groups": group_timings,
                "nonclaims": [
                    "Timing telemetry is not semantic, security, theorem, or conformance evidence.",
                    "Relative timings are host- and cache-state-dependent.",
                ],
            },
        )
    if successful:
        print(f"Analysis semantic closure: {count}/{count} tests passed")
        return 0
    print("Analysis semantic closure: FAILED", file=sys.stderr)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
