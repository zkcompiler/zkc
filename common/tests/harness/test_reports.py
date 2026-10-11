"""Report allocation must preserve evidence from parallel and repeated runs."""

import json
import os
from pathlib import Path
import subprocess
import sys

import pytest

from reporting import new_directory, run_report
import toolchain
import workspace

ROOT = Path(__file__).resolve().parents[3]


def test_same_label_different_identity_and_repeated_calls_never_overwrite(tmp_path):
    identities = ["a/test_case.py::test_name[a_b]", "a/test_case.py::test_name[a-b]",
                  "b/test_case.py::test_name[a_b]", "../../outside", "x" * 500]
    paths = [new_directory(tmp_path, identity) for identity in identities * 2]
    assert len(set(paths)) == len(paths)
    assert all(path.parent == tmp_path and len(path.name) < 100 for path in paths)
    for index, path in enumerate(paths):
        (path / "record").write_text(str(index))
    assert [(path / "record").read_text() for path in paths] == list(map(str, range(len(paths))))


def test_toolchain_records_share_only_the_same_caller_and_case(monkeypatch, tmp_path):
    monkeypatch.setenv("ZKC_REPORTS_DIR", str(tmp_path))
    def invoke(origin, case):
        namespace = {"__file__": str(origin), "records": toolchain.records, "case": case}
        exec("result = records(case)", namespace)
        return namespace["result"]
    first = invoke(ROOT / "common/tests/a/test_same.py", "x")
    (first / "retained").touch()
    assert invoke(ROOT / "common/tests/a/test_same.py", "x") == first
    assert invoke(ROOT / "common/tests/b/test_same.py", "x") != first
    assert invoke(ROOT / "common/tests/a/test_same.py", "../x") != first
    assert (first / "retained").exists()


def test_real_pytest_invocations_preserve_colliding_case_names(tmp_path):
    # Load the actual repository fixtures into a tiny synthetic suite.
    suite = tmp_path / "suite"
    suite.mkdir()
    (suite / "conftest.py").write_text(f'''import importlib.util, sys
sys.path.insert(0, {str(ROOT / "common/tests/support")!r})
spec = importlib.util.spec_from_file_location("repository_fixtures", {str(ROOT / "common/tests/conftest.py")!r})
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)
records, directory = module.records, module.directory
''')
    for folder in ("a", "b"):
        (suite / folder).mkdir()
        (suite / folder / "test_same.py").write_text('''import pytest
@pytest.mark.parametrize("name", ["a_b", "a-b"])
def test_same(directory, request, name):
    (directory / "identity").write_text(request.node.nodeid)
''')
    environment = {**os.environ, "ZKC_REPORTS_DIR": str(tmp_path / "reports")}
    commands = [subprocess.Popen([sys.executable, "-m", "pytest", "-q", "--import-mode=importlib",
                                  "-n", "2", str(suite)], cwd=suite, env=environment,
                                 stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
                for _ in range(2)]
    try:
        for process in commands:
            output = process.communicate(timeout=30)[0]
            assert process.returncode == 0, output.decode()
    finally:
        for process in commands:
            if process.poll() is None:
                process.kill()
                process.communicate(timeout=5)
    records = list((tmp_path / "reports/tests").glob("*/identity"))
    assert len(records) == 8
    assert len({path.read_text() for path in records}) == 4


def test_explicit_cleanup_refuses_build_root_and_symlink(monkeypatch, tmp_path):
    root = tmp_path / "repo"
    (root / "build").mkdir(parents=True)
    monkeypatch.setattr(workspace, "ROOT", root)
    (root / "build/binary").touch()
    with pytest.raises(ValueError, match="refusing"):
        workspace.clear_report_directory(root / "build")
    external = tmp_path / "external"
    external.mkdir()
    (external / "keep").touch()
    link = root / "build/reports"
    link.symlink_to(external, target_is_directory=True)
    with pytest.raises(ValueError, match="symlink"):
        workspace.clear_report_directory(link)
    assert (root / "build/binary").exists() and (external / "keep").exists()


def test_normal_full_suite_does_not_invoke_cleanup():
    result = subprocess.run(["just", "--justfile", str(ROOT / "justfile"), "--dry-run", "test"],
                            capture_output=True, text=True, check=True, timeout=10)
    commands = result.stdout + result.stderr
    assert "common/tests/run.py" in commands
    assert "clean-reports" not in commands


@pytest.mark.parametrize("outcome", [None, ValueError("failed check"), KeyboardInterrupt()])
@pytest.mark.parametrize("previous", [None, "previous reports"])
def test_run_report_records_lifecycle_and_restores_caller(outcome, previous, monkeypatch, tmp_path):
    if previous is None:
        monkeypatch.delenv("ZKC_REPORTS_DIR", raising=False)
    else:
        monkeypatch.setenv("ZKC_REPORTS_DIR", previous)

    def invoke():
        with run_report(tmp_path, "outer", ["runner", "outer"]) as outer:
            manifest = outer / "run.json"
            assert json.loads(manifest.read_text())["status"] == "running"
            with run_report(outer, "inner", ["runner", "inner"]) as inner:
                assert os.environ["ZKC_REPORTS_DIR"] == str(inner)
            assert os.environ["ZKC_REPORTS_DIR"] == str(outer)
            if outcome is not None:
                raise outcome

    if outcome is None:
        invoke()
    else:
        with pytest.raises(type(outcome)):
            invoke()
    assert os.environ.get("ZKC_REPORTS_DIR") == previous
    manifest, = (tmp_path / "runs").glob("*/run.json")
    record = json.loads(manifest.read_text())
    assert record["status"] == ("pass" if outcome is None else
                                "interrupted" if isinstance(outcome, KeyboardInterrupt) else "failed")
    assert record["argv"] == ["runner", "outer"]
    assert record["started_utc"] <= record["finished_utc"]
