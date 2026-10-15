"""Report lifecycle and source retention controls without native or Lean builds."""

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tarfile

import pytest

from harness import ROOT, executable, load

BRIDGE = ROOT / "lean/bridges/structured"


@pytest.fixture
def bridge(monkeypatch):
    monkeypatch.syspath_prepend(str(BRIDGE))
    for name in ("snapshot", "evidence", "check"):
        module = load(name, BRIDGE / f"{name}.py")
        monkeypatch.setitem(sys.modules, name, module)
    return module


@pytest.fixture
def source_tree(tmp_path):
    root = tmp_path / "source"
    root.mkdir()
    files = {".gitignore": "ignored/\n", "lean/Proof.lean": "import Dependency\n",
             "lean/Dependency.lean": "def value := 1\n", "fixture.zkc": "original\n",
             "lean/lake-manifest.json": '{"packages": []}\n', "removed": "old\n"}
    for name, text in files.items():
        path = root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
    subprocess.run(["git", "init", "-q", root], check=True)
    subprocess.run(["git", "add", "."], cwd=root, check=True)
    subprocess.run(["git", "-c", "user.name=Harness", "-c", "user.email=harness@example.invalid",
                    "commit", "-qm", "fixture"], cwd=root, check=True)
    (root / "fixture.zkc").write_bytes(b"modified\r\nexact bytes\x00\n")
    (root / "lean/Untracked.lean").write_text("import Proof\n-- untracked proof\n")
    (root / "removed").unlink()
    (root / "ignored").mkdir()
    (root / "ignored/cache").write_text("not source")
    return root


def arguments(tmp_path):
    tool = executable(tmp_path / "input/tool")
    return argparse.Namespace(report=tmp_path / "reports/latest.json", seed=1, cases=1,
                              compiler=tool, reference=tool, lean=tool, runtime=None)


def successful_run(bridge, args):
    suite = bridge.Suite(args)
    assert suite.run(lambda s: s.case("control", lambda: None)) == 0
    report = json.loads(args.report.read_text())
    assert report["status"] == "pass"
    return report


@pytest.mark.parametrize("failure", ["compiler", "optimizer", "version-exit", "version-missing", "cases"])
def test_cli_setup_failure_replaces_success_and_preserves_old_archive(
        bridge, source_tree, tmp_path, monkeypatch, failure):
    monkeypatch.setattr(bridge, "ROOT", source_tree)
    args = arguments(tmp_path)
    previous = successful_run(bridge, args)
    old_report = (Path(previous["directory"]) / "report.json").read_bytes()
    old_tool = Path(previous["tools"]["compiler"]["path"]).read_bytes()
    args.compiler.write_text("#!/bin/sh\n# changed tool for the next run\nexit 0\n")
    assert args.compiler.read_bytes() != old_tool
    lake = executable(tmp_path / "lake")
    lake.write_text("#!/bin/sh\nexit 19\n")
    driver = "check" if failure == "compiler" else "inlining"
    command = [sys.executable, "-c",
        f"import sys; sys.path.insert(0, {str(BRIDGE)!r}); import check; "
        f"check.ROOT = __import__('pathlib').Path({str(source_tree)!r}); "
        f"import {driver}; sys.exit({driver}.main())",
        "--report", str(args.report), "--compiler",
        str(tmp_path / "missing" if failure == "compiler" else args.compiler),
        "--reference", str(args.reference), "--lean", str(args.lean)]
    if driver == "inlining":
        command += ["--optimizer", str(tmp_path / "missing" if failure == "optimizer" else args.compiler),
                    "--lake", str(tmp_path / "missing-lake" if failure == "version-missing" else lake)]
    if failure == "cases":
        command += ["--cases", "0"]
    result = subprocess.run(command, capture_output=True, text=True, timeout=15)
    assert result.returncode == 1, result.stderr
    report = json.loads(args.report.read_text())
    assert report["status"] == "failed"
    assert report["run"] != previous["run"]
    assert any(not item["passed"] for item in report["checks"])
    assert json.loads((Path(report["directory"]) / "report.json").read_text()) == report
    assert (Path(previous["directory"]) / "report.json").read_bytes() == old_report
    assert Path(previous["tools"]["compiler"]["path"]).read_bytes() == old_tool
    if failure.startswith("version"):
        assert report["commands"][-1]["label"] == "lean-version"
        assert report["commands"][-1]["exit"] == (19 if failure == "version-exit" else None)


@pytest.mark.parametrize("step", ["allocation", "copy", "interrupt"])
def test_running_marker_precedes_setup_and_failure_is_finalized(
        bridge, source_tree, tmp_path, monkeypatch, step):
    monkeypatch.setattr(bridge, "ROOT", source_tree)
    args = arguments(tmp_path)
    previous = successful_run(bridge, args)

    def fail(*_args, **_kwargs):
        current = json.loads(args.report.read_text())
        assert current["status"] == "running" and current["run"] != previous["run"]
        if step == "interrupt":
            raise KeyboardInterrupt()
        raise OSError("injected setup failure")

    if step == "allocation":
        monkeypatch.setattr(bridge, "new_directory", fail)
    elif step == "copy":
        monkeypatch.setattr(bridge.shutil, "copy2", fail)
    suite = bridge.Suite(args)
    assert suite.run(fail) == 1
    report = json.loads(args.report.read_text())
    assert report["status"] == ("interrupted" if step == "interrupt" else "failed")


def test_archive_retains_working_bytes_untracked_proofs_and_local_imports(
        bridge, source_tree, tmp_path, monkeypatch):
    monkeypatch.setattr(bridge, "ROOT", source_tree)
    args = arguments(tmp_path)
    args.write_fixtures = True
    suite = bridge.Suite(args)

    def regenerate(s):
        (source_tree / "fixture.zkc").write_bytes(b"regenerated\r\n")
        s.case("regeneration", lambda: None)

    assert suite.run(regenerate) == 0
    report = json.loads(args.report.read_text())
    for stage, expected in [("before", b"modified\r\nexact bytes\x00\n"), ("after", b"regenerated\r\n")]:
        record = report["sourceArchives"][stage]
        archive = Path(record["path"])
        assert hashlib.sha256(archive.read_bytes()).hexdigest() == record["sha256"]
        manifest = json.loads(Path(record["manifest"]).read_text())
        assert manifest["deletedTrackedPaths"] == ["removed"]
        with tarfile.open(archive) as retained:
            assert retained.extractfile("fixture.zkc").read() == expected
            for name in ("lean/Proof.lean", "lean/Untracked.lean", "lean/Dependency.lean",
                         "lean/lake-manifest.json"):
                assert retained.extractfile(name).read() == (source_tree / name).read_bytes()
            assert set(retained.getnames()) == set(manifest["files"])
            assert "ignored/cache" not in retained.getnames()
            for name, entry in manifest["files"].items():
                assert hashlib.sha256(retained.extractfile(name).read()).hexdigest() == entry["sha256"]
