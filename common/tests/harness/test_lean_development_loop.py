"""Native admission has one lane; removed proof-generator options cannot revive it."""

import sys

import pytest

from harness import load


@pytest.mark.parametrize("arguments", [
    ["--subject", "schnorr"], ["--stage", "reports"], ["--fresh-bodies"],
])
def test_removed_generator_options_run_nothing(monkeypatch, tmp_path, arguments):
    api = load("development_loop", "common/tests/run.py")
    calls = []
    monkeypatch.setattr(api, "run", lambda command, **_: calls.append(command))
    monkeypatch.setenv("ZKC_REPORTS_DIR", str(tmp_path / "reports"))
    monkeypatch.setattr(sys, "argv", ["run.py", "lean-native", *arguments])
    with pytest.raises(SystemExit):
        api.main()
    assert calls == []


def test_native_scope_checks_actual_admission_once(monkeypatch, tmp_path):
    api = load("development_loop", "common/tests/run.py")
    calls = []
    monkeypatch.setattr(api, "run", lambda command, **_: calls.append(list(map(str, command))))
    monkeypatch.setenv("ZKC_REPORTS_DIR", str(tmp_path / "reports"))
    monkeypatch.setattr(sys, "argv", ["run.py", "lean-native", "--compiler-build", str(tmp_path / "compiler")])
    api.main()
    assert len(calls) == 1
    command = calls[0]
    assert command[1].endswith("lean/checks/check_source_admission.py")
    assert command[command.index("--compiler") + 1] == str(tmp_path / "compiler/zkc-compile")
    assert all(path.name != "check_source_admission.py" for path in api.lean_checks())


def test_core_lane_does_not_load_optional_adapter_records_or_clients(monkeypatch, tmp_path):
    api = load("development_loop", "common/tests/run.py")
    calls = []
    monkeypatch.setattr(api, "run", lambda command, **_: calls.append(list(map(str, command))))
    monkeypatch.setenv("ZKC_REPORTS_DIR", str(tmp_path / "reports"))
    monkeypatch.setattr(sys, "argv", ["run.py", "lean"])
    api.main()
    selected = [c for c in calls if c[1].endswith(("check_records.py", "check_clients.py"))]
    assert len(selected) == 2
    assert all("--core-only" in command for command in selected)
