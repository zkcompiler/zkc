"""Negative controls for the merge gate; skipped work is not completed work."""

import json
import os
import subprocess
import sys

import pytest

from harness import ROOT


SCRIPT = ROOT / ".github/scripts/require-checks.py"


def check(needs, event="pull_request", scope=""):
    return subprocess.run(
        [sys.executable, SCRIPT], capture_output=True, text=True,
        env=os.environ | {"CI_NEEDS": json.dumps(needs), "CI_EVENT": event,
                          "CI_SCOPE": scope})


@pytest.mark.parametrize("result", ["failure", "cancelled", "skipped", "timed_out", "neutral", ""])
@pytest.mark.parametrize("name", ["quick", "native"])
def test_required_jobs_must_succeed(name, result):
    needs = {"quick": {"result": "success"}, "native": {"result": "success"}}
    needs[name]["result"] = result
    run = check(needs)
    assert run.returncode == 1
    assert f"{name}: {result}; success required" in run.stdout


def test_missing_required_job_refuses():
    run = check({"quick": {"result": "success"}})
    assert run.returncode == 1
    assert "native: missing" in run.stdout


@pytest.mark.parametrize("event", ["pull_request", "push"])
def test_automatic_success_with_unselected_manual_jobs(event):
    needs = {"quick": {"result": "success"}, "native": {"result": "success"},
             "main": {"result": "skipped"}, "optional": {"result": "skipped"},
             "fresh": {"result": "skipped"}}
    assert check(needs, event).returncode == 0


@pytest.mark.parametrize("scope,jobs", [
    ("quick", ["quick"]), ("main", ["main"]), ("cache", ["main"]),
    ("optional", ["optional"]), ("fresh", ["fresh"]),
    ("all", ["quick", "main", "optional", "fresh"]),
    ("compiler-cache", ["compiler_cache"]),
])
def test_manual_scope_requires_its_whole_selection(scope, jobs):
    needs = {name: {"result": "success"} for name in jobs}
    assert check(needs, "workflow_dispatch", scope).returncode == 0
    for job in jobs:
        incomplete = needs | {job: {"result": "skipped"}}
        assert check(incomplete, "workflow_dispatch", scope).returncode == 1


@pytest.mark.parametrize("event,scope", [("workflow_dispatch", "unknown"), ("unknown", "")])
def test_unknown_selection_refuses(event, scope):
    assert check({}, event, scope).returncode == 1
