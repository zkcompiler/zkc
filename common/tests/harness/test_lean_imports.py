"""Synthetic Lean workspaces must not change later real-source imports."""

import importlib
import sys

import pytest

from harness import ROOT, lean_imports


def test_synthetic_imports_restore_modules_and_paths_even_after_failure(tmp_path):
    original_path = sys.path[:]
    with lean_imports():
        real = importlib.import_module('support.packages')
        real_support = sys.modules['support']
        workspace_path = sys.path[:]
        support = tmp_path / 'support'
        support.mkdir()
        (support / 'packages.py').write_text('SYNTHETIC = True\n')
        (support / 'temporary.py').write_text('SYNTHETIC = True\n')
        with pytest.raises(RuntimeError, match='synthetic failure'):
            with lean_imports(tmp_path):
                synthetic = importlib.import_module('support.packages')
                importlib.import_module('support.temporary')
                assert synthetic.SYNTHETIC
                assert synthetic is not real
                raise RuntimeError('synthetic failure')
        assert sys.path == workspace_path
        assert sys.modules['support'] is real_support
        assert importlib.import_module('support.packages') is real
        assert 'support.temporary' not in sys.modules
        assert real.LEAN == ROOT / 'lean'
    assert sys.path == original_path


def test_real_policy_import_after_a_synthetic_workspace(tmp_path):
    support = tmp_path / 'support'
    support.mkdir()
    (support / 'packages.py').write_text('SYNTHETIC = True\n')
    with lean_imports(tmp_path):
        assert importlib.import_module('support.packages').SYNTHETIC
    with lean_imports():
        policy = importlib.import_module('support.dependencies')
        assert policy.POLICY['exceptions'] == []
        assert policy.POLICY_SOURCE.is_relative_to(ROOT / 'lean/program')
