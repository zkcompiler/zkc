"""Native admission has one lane; removed proof-generator options cannot revive it."""

from pathlib import Path
import sys

import pytest

from harness import lean_imports, load


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
    assert all(path.name != "check_source_admission.py"
               for path in api.lean_checks())


def test_core_lane_does_not_load_optional_adapter_records_or_clients(monkeypatch, tmp_path):
    api = load("development_loop", "common/tests/run.py")
    calls, tests = [], []

    def record(command, cwd=None, **_):
        command = list(map(str, command))
        calls.append(command)
        if command[:2] == ["lake", "test"]:
            tests.append((command, Path(cwd).name))

    monkeypatch.setattr(api, "run", record)
    monkeypatch.setattr(api, "reference_arguments", lambda: ["--", "--without-reference"])
    monkeypatch.setenv("ZKC_REPORTS_DIR", str(tmp_path / "reports"))
    monkeypatch.setattr(sys, "argv", ["run.py", "lean"])
    api.main()
    selected = [c for c in calls if c[1].endswith(("check_records.py", "check_clients.py"))]
    assert len(selected) == 2
    assert all("--core-only" in command for command in selected)
    # The dependency-free packages are checked on their own, without records or clients.
    for name in ("core", "frontend", "formal"):
        own = [c for c in calls if c[-2:] == ["--package", name]]
        assert sorted(Path(c[1]).name for c in own) == [
            "audit_imports.py", "check_library.py", "check_package_ownership.py"]
    # The test drivers of the packages that have one run in their own directories.
    assert (["lake", "test", "--", "--without-reference"], "frontend") in tests
    assert (["lake", "test"], "formal") in tests
    # Their declaration audits run in consumer workspaces that also require Program.
    assert [c for c in calls if c[1].endswith("check_consumer_audit.py")] == [
        [sys.executable, str(api.ROOT / "lean/checks/check_consumer_audit.py")]]
    assert any(c[1].endswith("lean/frontend/scripts/generate_unicode_tables.py") and c[2:] == ["--check"]
               for c in calls)


def test_frontend_driver_reads_the_reference_of_the_repository_or_the_named_one(tmp_path):
    api = load("development_loop", "common/tests/run.py")
    without = ["--", "--without-reference"]
    # A tree without the reference, such as a copy of the packages alone.
    assert api.reference_arguments(tmp_path, {}) == without
    assert api.reference_arguments(tmp_path, {"ZKC_LANGUAGE_REFERENCE": "/reference"}) == []
    (tmp_path / "language/conformance").mkdir(parents=True)
    assert api.reference_arguments(tmp_path, {}) == []


def test_dependency_free_packages_are_the_inventory_packages_outside_the_auditor():
    api = load("development_loop", "common/tests/run.py")
    with lean_imports():
        from support.packages import PACKAGES, audited
        expected = tuple(name for name in PACKAGES if not audited(name))
    assert api.DEPENDENCY_FREE == expected
