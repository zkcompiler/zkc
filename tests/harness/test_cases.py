"""CTest's grouped cases must run independently and propagate failed status."""

import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]


def run(program):
    return subprocess.run([sys.executable, "-c", program], text=True, capture_output=True,
                          env=dict(os.environ, PYTHONPATH=str(ROOT / "compiler/test/support")),
                          timeout=10)


def test_failures_are_aggregated_without_hiding_later_cases():
    result = run("""
from cases import case
with case('first failure'):
    assert False, 'first diagnostic'
with case('later success'):
    print('later case ran')
with case('second failure'):
    raise ValueError('second diagnostic')
""")
    assert result.returncode == 1
    assert "later case ran" in result.stdout
    assert "2 of 3 cases failed" in result.stderr
    assert "first diagnostic" in result.stderr and "second diagnostic" in result.stderr


def test_successful_cases_do_not_fail_at_process_exit():
    result = run("from cases import case\nwith case('ok'):\n    assert 1 + 1 == 2\n")
    assert result.returncode == 0 and not result.stderr


def test_explicit_exit_is_not_swallowed_by_a_case():
    result = run("from cases import case\nwith case('stop'):\n    raise SystemExit(7)\nprint('unreachable')")
    assert result.returncode == 7 and "unreachable" not in result.stdout
