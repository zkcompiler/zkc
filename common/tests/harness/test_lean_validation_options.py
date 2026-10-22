"""Assurance checks must survive optimized Python and enforce package options."""

import ast
import os
from pathlib import Path
import subprocess
import sys

import pytest

ROOT = Path(__file__).resolve().parents[3]


@pytest.mark.parametrize("optimize", [False, True])
def test_incomplete_package_targets_are_refused_even_under_optimization(tmp_path, optimize):
    (tmp_path / "lean-toolchain").write_text("test-toolchain\n")
    (tmp_path / "lake-manifest.json").write_text('{"packages": []}')
    (tmp_path / "lakefile.toml").write_text(
        'defaultTargets=[]\n[[lean_lib]]\nname="UnbuiltSecurity"\n')
    script = """
from pathlib import Path
from checks import check_library as audit
audit.ROOT = Path(__import__('sys').argv[1])
audit.PACKAGES = {'main': (audit.ROOT, [])}
audit.select_packages = lambda _: ['main']
audit.check_closure = lambda *_: None
audit.check([], 'lake')
"""
    result = subprocess.run([sys.executable, *(["-O"] if optimize else []), "-c", script, str(tmp_path)],
                            env=os.environ | {"PYTHONPATH": str(ROOT / "lean")},
                            capture_output=True, text=True)
    assert result.returncode > 0
    assert "default targets omit maintained code" in result.stderr


def test_assurance_drivers_have_no_optimization_sensitive_assertions():
    for directory in (ROOT / "lean/checks", ROOT / "lean/bridges"):
        for path in directory.rglob("*.py"):
            assert not any(isinstance(node, ast.Assert) for node in ast.walk(ast.parse(path.read_text()))), path
