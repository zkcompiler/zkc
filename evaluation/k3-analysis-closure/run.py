#!/usr/bin/env python3
"""Run the bounded Analysis semantic-closure research gate."""

from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor
import os
from pathlib import Path
import subprocess
import sys
import unittest


ROOT = Path(__file__).resolve().parent


def _cases(suite: unittest.TestSuite) -> list[unittest.TestCase]:
    result: list[unittest.TestCase] = []
    for child in suite:
        if isinstance(child, unittest.TestSuite):
            result.extend(_cases(child))
        else:
            result.append(child)
    return result


def _test_groups(
    suite: unittest.TestSuite, jobs: int
) -> tuple[tuple[str, ...], ...]:
    test_ids = tuple(sorted(case.id() for case in _cases(suite)))
    group_count = min(jobs, len(test_ids))
    groups: list[list[str]] = [[] for _ in range(group_count)]
    for index, test_id in enumerate(test_ids):
        groups[index % group_count].append(test_id)
    return tuple(tuple(group) for group in groups)


def _run_isolated_group(test_ids: tuple[str, ...]) -> subprocess.CompletedProcess[str]:
    environment = os.environ.copy()
    environment["PYTHONDONTWRITEBYTECODE"] = "1"
    return subprocess.run(
        [sys.executable, "-B", "-m", "unittest", "-v", *test_ids],
        cwd=ROOT / "tests",
        env=environment,
        check=False,
        capture_output=True,
        text=True,
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
    args = parser.parse_args(argv)
    if args.jobs < 1:
        parser.error("--jobs must be positive")
    suite = unittest.TestLoader().discover(
        str(ROOT / "tests"), top_level_dir=str(ROOT / "tests")
    )
    count = suite.countTestCases()
    print(f"Analysis semantic closure: {count} tests")
    if args.jobs == 1:
        successful = unittest.TextTestRunner(verbosity=2).run(suite).wasSuccessful()
    else:
        groups = _test_groups(suite, args.jobs)
        with ThreadPoolExecutor(max_workers=len(groups)) as executor:
            results = tuple(executor.map(_run_isolated_group, groups))
        successful = True
        for result in results:
            if result.stdout:
                print(result.stdout, end="")
            if result.stderr:
                print(result.stderr, file=sys.stderr, end="")
            successful = successful and result.returncode == 0
    if successful:
        print(f"Analysis semantic closure: {count}/{count} tests passed")
        return 0
    print("Analysis semantic closure: FAILED", file=sys.stderr)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
