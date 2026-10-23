"""Offline validation must reject inconclusive tools and unreplayed models."""
import importlib.util
from pathlib import Path
import subprocess
from types import SimpleNamespace

import pytest

SPEC = importlib.util.spec_from_file_location(
    'arithmetic_checks', Path(__file__).resolve().parents[1] / 'check_arithmetic.py')
CHECKS = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CHECKS)


@pytest.mark.parametrize('output,expected', [
    ('unknown\n', 'unsat'), ('timeout\n', 'unsat'), ('', 'unsat'),
    ('sat\n', 'unsat'), ('unsat\n', 'sat'), ('unsat\n(error "bad")\n', 'unsat'),
])
def test_unexpected_solver_results_never_pass(tmp_path, monkeypatch, output, expected):
    checks = CHECKS.Checks(Path('solver'), Path('translator'), tmp_path)
    monkeypatch.setattr(checks, 'run', lambda *args: output)
    with pytest.raises(CHECKS.ValidationError):
        checks.solve('control', '(assert true)', expected)
    assert checks.records == []


@pytest.mark.parametrize('failure', ['exit', 'timeout'])
def test_process_failure_cannot_become_a_solver_result(tmp_path, monkeypatch, failure):
    def run(*args, **kwargs):
        if failure == 'timeout':
            raise subprocess.TimeoutExpired('solver', 15)
        return SimpleNamespace(returncode=1, stdout='unsat\n', stderr='failed')
    monkeypatch.setattr(CHECKS.subprocess, 'run', run)
    checks = CHECKS.Checks(Path('solver'), Path('translator'), tmp_path)
    with pytest.raises(CHECKS.ValidationError):
        checks.solve('failed', '(assert true)', 'unsat')
    assert checks.records == []


@pytest.mark.parametrize('model', [
    '', '(define-fun x () Int 0)', '(define-fun x () Int 19)',
    '(define-fun x () Int (- 19))',
])
def test_crt_counterexample_requires_premises_and_disagreement(model):
    with pytest.raises(CHECKS.ValidationError):
        CHECKS.replay_crt(model, 35, 11, 18)


def test_positive_and_negative_crt_models_replay_with_integer_arithmetic():
    for x, text in [(18, '18'), (-18, '(- 18)')]:
        result = CHECKS.replay_crt(f'(define-fun x () Int {text})', 35, 11, 18)
        assert result['x'] == x
        assert result['lifted'] == (-17 if x > 0 else 17)


@pytest.mark.parametrize('q,c', [(1, 0), (17, 17), (17, 0), (2**64-1, 2**64-1)])
def test_word_counterexample_rejects_invalid_or_agreeing_values(q, c):
    model = f'(define-fun q () (_ BitVec 64) (_ bv{q} 64))\n'
    model += f'(define-fun c () (_ BitVec 64) (_ bv{c} 64))'
    with pytest.raises(CHECKS.ValidationError):
        CHECKS.replay_word(model)


def test_full_word_overflow_counterexample_replays():
    model = '(define-fun q () (_ BitVec 64) (_ bv18446744073709551615 64))\n'
    model += '(define-fun c () (_ BitVec 64) (_ bv0 64))'
    assert CHECKS.replay_word(model) == {'q': 2**64-1, 'c': 0}


def test_exported_model_is_requested_before_solver_reset(tmp_path, monkeypatch):
    checks = CHECKS.Checks(Path('solver'), Path('translator'), tmp_path)
    monkeypatch.setattr(checks, 'run', lambda *args: 'sat\n(model)\n')
    checks.solve('exported', '(check-sat)\n(reset)\n', 'sat', model=True, exported=True)
    text = (tmp_path / 'exported.smt2').read_text()
    assert text.index('(check-sat)') < text.index('(get-model)') < text.index('(reset)')
    with pytest.raises(CHECKS.ValidationError, match='unexpected SMT export scope'):
        checks.solve('bad-export', '(check-sat)\n', 'sat', model=True, exported=True)


def test_wrong_tool_version_refuses_before_any_query(tmp_path, monkeypatch):
    checks = CHECKS.Checks(Path('solver'), Path('translator'), tmp_path)
    monkeypatch.setattr(checks, 'run', lambda *args: 'Z3 version 0.0.0')
    with pytest.raises(CHECKS.ValidationError, match='unsupported solver version'):
        checks.validate({'z3': {'version': '5.3.1'}, 'llvm': {'version': '23.1.3'}})
    assert checks.records == []


def test_cli_retains_failure_and_never_overwrites_an_existing_report(tmp_path):
    import json
    import sys
    output = tmp_path / 'report'
    command = [sys.executable, str(SPEC.origin), '--solver', str(tmp_path / 'missing-solver'),
               '--mlir-translate', str(tmp_path / 'missing-translator'), '--output', str(output)]
    first = subprocess.run(command, capture_output=True, text=True, timeout=15)
    assert first.returncode == 1
    report = output / 'report.json'
    original = report.read_bytes()
    assert json.loads(original)['status'] == 'failed'
    assert json.loads(original)['queries'] == []
    second = subprocess.run(command, capture_output=True, text=True, timeout=15)
    assert second.returncode == 1
    assert report.read_bytes() == original
