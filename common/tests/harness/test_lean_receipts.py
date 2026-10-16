"""Structured proof errors refuse promptly; success still waits for completion."""
import json
from pathlib import Path
import sys

import pytest

from harness import load


@pytest.fixture
def driver(monkeypatch):
    root = Path(__file__).resolve().parents[3]
    monkeypatch.syspath_prepend(str(root / 'lean/bridges/constructed'))
    return load('constructed_verification_driver', 'lean/bridges/constructed/verification.py')


def run(driver, tmp_path, code, timeout=5):
    return driver.execute([sys.executable, '-c', code], tmp_path, 'lean', timeout)


def test_lean_error_stops_later_elaboration(driver, tmp_path):
    code = ('import json,time; '
            'print(json.dumps({"severity":"error","data":"wrong equation"}),flush=True); '
            'time.sleep(30)')
    with pytest.raises(driver.Unresolved) as result:
        run(driver, tmp_path, code)
    assert result.value.code == 'tool-failed'
    diagnostic = json.loads((tmp_path / 'lean.log').read_text().splitlines()[0])
    assert diagnostic['data'] == 'wrong equation'


@pytest.mark.parametrize('newline', [True, False])
def test_reported_error_cannot_succeed_on_zero_exit(driver, tmp_path, newline):
    code = ('import sys; sys.stdout.write(\'{"severity":"error","data":"wrong proof"}\' + '
            + repr('\n' if newline else '') + ')')
    with pytest.raises(driver.Unresolved) as result:
        run(driver, tmp_path, code)
    assert result.value.code == 'tool-failed'


def test_fragmented_diagnostics_preserve_utf8_and_nonerrors(driver, tmp_path):
    diagnostic = json.dumps({'severity': 'information', 'data': 'checked λ'}, ensure_ascii=False)
    code = ('import os; data=' + repr((diagnostic + '\n').encode()) + '; '
            '[os.write(1, bytes([byte])) for byte in data]')
    assert run(driver, tmp_path, code) == diagnostic + '\n'


def test_information_does_not_replace_successful_completion(driver, tmp_path):
    code = ('import sys; print(\'{"severity":"information","data":"PASS"}\'); '
            'sys.exit(2)')
    with pytest.raises(driver.Unresolved) as result:
        run(driver, tmp_path, code)
    assert result.value.code == 'tool-failed'


def test_timeout_retains_output_and_remains_distinct(driver, tmp_path):
    code = 'import time; print("partial output",flush=True); time.sleep(30)'
    with pytest.raises(driver.Unresolved) as result:
        run(driver, tmp_path, code, timeout=1)
    assert result.value.code == 'tool-timeout'
    assert (tmp_path / 'lean.log').read_text() == 'partial output\n'
