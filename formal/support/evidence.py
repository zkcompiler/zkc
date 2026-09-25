"""Where a check leaves what it found, named after the check.

The other three suites already work this way: `compiler/test/support/tools.py`
and `crates/zkc-test-support` both name a test's directory after the test
rather than taking a path, so there is no convention to remember and none to
get wrong. These drivers took `--output` instead, which meant the runner had
to know each one's name and spell its destination -- a list, and lists fall
behind.

`--output` stays, because the specification publishes some of these as
commands a reader runs with a path of their own. It is the default that
changes: a driver run with no path writes under the reports directory, beside
everything else the tests keep.
"""

import os
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]


def records(name, suffix=""):
    """The directory, or file, this check writes to when nothing said where."""
    if "ZKC_TEST_RECORDS" in os.environ:
        raise ValueError("ZKC_TEST_RECORDS was removed; use ZKC_REPORTS_DIR without /tests")
    chosen = os.environ.get("ZKC_REPORTS_DIR", "build/reports")
    if not chosen.strip():
        raise ValueError("ZKC_REPORTS_DIR must be a nonempty path")
    path = Path(chosen)
    if not path.is_absolute():
        path = ROOT / path
    return path.resolve() / "formal" / f"{name}{suffix}"
