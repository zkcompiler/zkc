"""A broken test helper must not turn a crash or lost evidence into a pass."""

import json
from pathlib import Path
import signal
import subprocess
import sys

import pytest

from differential import Run
from journal import Journal, Refused


def command(program):
    return [sys.executable, "-c", program]


def records(directory):
    return [json.loads(line) for line in (directory / "commands.jsonl").read_text().splitlines()]


@pytest.mark.parametrize("refuses", [True, "", "expected-reason"])
def test_a_signal_is_not_an_expected_refusal(tmp_path, refuses):
    journal = Journal(tmp_path)
    with pytest.raises(Refused, match="signal"):
        journal.run(command("import os, signal; print('expected-reason', flush=True); "
                            "os.kill(os.getpid(), signal.SIGTERM)"), refuses=refuses)
    saved = records(tmp_path)
    assert saved[0]["returncode"] == -signal.SIGTERM
    assert Path(saved[0]["output"]).read_text() == "expected-reason\n"


def test_refusal_requires_the_named_reason_and_a_failure_status(tmp_path):
    journal = Journal(tmp_path)
    rejected = command("import sys; print('wrong-reason', file=sys.stderr); sys.exit(1)")
    with pytest.raises(Refused, match="not with"):
        journal.run(rejected, refuses="required-reason")
    with pytest.raises(Refused, match="expected to refuse"):
        journal.run(command("print('required-reason')"), refuses="required-reason")
    assert journal.run(rejected, refuses="wrong-reason") == ""
    saved = records(tmp_path)
    assert [row["returncode"] for row in saved] == [1, 0, 1]
    assert Path(saved[1]["output"]).read_text() == "required-reason\n"


def test_timeout_keeps_partial_stdout_stderr_and_does_not_reuse_previous_output(tmp_path):
    journal = Journal(tmp_path)
    journal.run(command("print('previous command')"))
    with pytest.raises(subprocess.TimeoutExpired):
        journal.attempt(command("import sys, time; print('partial output', flush=True); "
                                "print('partial diagnostic', file=sys.stderr, flush=True); time.sleep(30)"),
                        timeout=1)
    saved = records(tmp_path)
    assert [row["returncode"] for row in saved] == [0, "timeout"]
    assert saved[-1]["stderr"] == "partial diagnostic\n"
    assert Path(saved[-1]["output"]).read_text() == "partial output\n"
    assert saved[-1]["wall_seconds"] > 0


def test_spawn_failure_is_recorded_without_old_output(tmp_path):
    journal = Journal(tmp_path)
    journal.run(command("print('unrelated successful output')"))
    with pytest.raises(FileNotFoundError):
        journal.attempt([tmp_path / "no-executable"])
    saved = records(tmp_path)
    assert saved[-1]["returncode"] == "not-run"
    assert saved[-1]["stderr"]
    assert "output" not in saved[-1]


def test_completed_commands_are_appended_once(tmp_path, monkeypatch):
    journal = Journal(tmp_path)
    serialized = []
    encode = json.dumps

    def counted(value, *args, **kwargs):
        serialized.append(value)
        return encode(value, *args, **kwargs)

    monkeypatch.setattr(json, "dumps", counted)
    for index in range(12):
        journal.run(command(f"print({index})"))
    assert len(serialized) == 12, "completed history must not be serialized again for each command"
    assert len(records(tmp_path)) == 12
    assert all(row["returncode"] == 0 and row["wall_seconds"] is not None for row in records(tmp_path))


def test_binary_output_and_non_utf8_diagnostics_are_retained(tmp_path):
    journal = Journal(tmp_path)
    result = journal.attempt(command("import sys; sys.stdout.buffer.write(b'\\xff'); "
                                     "sys.stderr.buffer.write(b'\\xfe'); sys.exit(1)"), text=False)
    assert result.stdout == b"\xff"
    saved = records(tmp_path)[0]
    assert saved["stderr"] == "\ufffd"
    assert Path(saved["output"]).read_text() == "\ufffd"


def test_differential_report_rejects_a_crash_after_valid_json(tmp_path):
    # The report boundary itself needs no compiler or Lean installation.
    run = object.__new__(Run)
    run.directory = tmp_path
    run.journal = Journal(tmp_path)
    with pytest.raises(Refused, match="signal"):
        run.report("native", *command("import os, signal; print('{}', flush=True); "
                                      "os.kill(os.getpid(), signal.SIGTERM)"))
