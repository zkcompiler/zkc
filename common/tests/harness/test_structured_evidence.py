"""Report lifecycle and source retention controls without native or Lean builds."""

import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
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
                              compiler=tool, reference=tool, lean=tool, runtime=None,
                              native_only=False, write_fixtures=False)


@pytest.fixture
def repeats(bridge, monkeypatch):
    for name in ("open_protocol", "repeats"):
        module = load(name, BRIDGE / f"{name}.py")
        monkeypatch.setitem(sys.modules, name, module)
    return module


@pytest.fixture
def repeat_tree(repeats, bridge, monkeypatch, tmp_path):
    """A Git-free package with real driver imports and tiny owned source trees."""
    root = tmp_path / "repeat-source"
    files = {
        "lean/lakefile.toml": (ROOT / "lean/lakefile.toml").read_text() +
            '\n[[lean_lib]]\nname = "FutureOwner"\n',
        "lean/lean-toolchain": "leanprover/lean4:test\n",
        "lean/lake-manifest.json": '{"packages": []}',
        "lean/Zkc.lean": "import Zkc.Dependency\n",
        "lean/Zkc/Dependency.lean": "def value := 1\n",
        "lean/ZkcTools/StructuredSource.lean": "import ZkcTools.StructuredSource.OpenEvaluation\n",
        "lean/ZkcTools/CommonSource.lean": "-- other executable root\n",
        "lean/ZkcTools/ImportHeaders.lean": "-- import auditing executable\n",
        "lean/ZkcTools/StructuredSource/OpenEvaluation.lean":
            "import ZkcTools.StructuredSource.Bounds\nimport ZkcTools.JsonSupport\n",
        "lean/ZkcTools/StructuredSource/Bounds.lean": "def bound := 1\n",
        "lean/ZkcTools/JsonSupport.lean": "-- observer support\n",
        "lean/FutureOwner/Dependency.lean": "-- newly declared namespace\n",
        "lean/Tests/Checks.lean": "-- local test namespace\n",
        "lean/checks/check_structured_renderer.py": "import support.lake\n",
        "lean/support/lake.py": "# renderer dependency\n",
        "lean/ZkcExamples/Structured/RepeatData.lean": "-- retained subject\n",
        "lean/bridges/structured/fixtures/repeat.json": "[]\n",
        "lean/bridges/structured/fixtures/repeat.mlir": "// retained source\n",
        "lean/bridges/structured/README.md": "source owners\n",
        "compiler/include/zkc/Support/Json.h": "// native header\n",
        "compiler/lib/Compiler/StructuredSource.cpp": "// exporter\n",
        "compiler/tools/zkc-compile.cpp": "// frontend\n",
        "compiler/test/structured_reference.cpp": "// SSA observer\n",
        "compiler/cmake/Components.cmake": "# native owners\n",
        "compiler/CMakeLists.txt": "# native package\n",
        "compiler/CMakePresets.json": "{}\n",
        "common/tests/run.py": "import reporting\n",
        "common/unicode/manifest.json": "{}\n",
        "pyproject.toml": "[project]\nname = 'fixture'\n",
        "uv.lock": "version = 1\n", "flake.nix": "{}\n", "flake.lock": "{}\n",
        "examples/project/zkc.toml":
            '[modules]\nexample = "main.zkc"\n[dependencies]\nlib = "../../libraries/lib"\n',
        "examples/project/main.zkc": "// authored subject\n",
        "libraries/lib/zkc.toml": '[modules]\nlib = "lib.zkc"\n',
        "libraries/lib/lib.zkc": "// transitive authored module\n",
        "docs/private/secret.md": "private\n",
        "build/experiments/private.py": "private\n",
        "lean/.lake/packages/external/Dependency.lean": "external\n",
        "lean/Zkc/private/Experiment.lean": "private\n",
        "scripts/__pycache__/ignored.py": "cache\n",
    }
    for name in ("snapshot", "check", "evidence", "open_protocol", "repeats"):
        files[f"lean/bridges/structured/{name}.py"] = (BRIDGE / f"{name}.py").read_text()
    for name in ("scripts/reporting.py", "common/tests/support/project.py"):
        files[name] = (ROOT / name).read_text()
    for name, value in files.items():
        path = root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(value)
    monkeypatch.setattr(bridge, "ROOT", root)
    monkeypatch.setattr(repeats, "ROOT", root)
    monkeypatch.setattr(repeats, "SUBJECTS", [
        ("repeat", "Repeat", "example::Demo", "examples/project/zkc.toml")])
    return root


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


@pytest.mark.parametrize("output", [b"partial\xff\n", "partial \u27e8value\u27e9\n", None])
def test_timeout_retains_partial_streams_and_failed_report(
        bridge, source_tree, tmp_path, monkeypatch, output):
    monkeypatch.setattr(bridge, "ROOT", source_tree)
    args = arguments(tmp_path)
    suite = bridge.Suite(args)

    def invoke(s):
        def timeout(argv, **_kwargs):
            raise subprocess.TimeoutExpired(argv, 60, output=output, stderr=output)

        monkeypatch.setattr(bridge.subprocess, "run", timeout)
        s.command("timed-out", [s.tools["compiler"]])

    assert suite.run(invoke) == 1
    report = json.loads(args.report.read_text())
    assert report["status"] == "failed"
    command = report["commands"][-1]
    assert command["exit"] is None and command["error"].startswith("TimeoutExpired:")
    prefix = Path(command["output"])
    expected = output if isinstance(output, bytes) else (output or "").encode("utf-8")
    assert prefix.with_suffix(".stdout").read_bytes() == expected
    assert prefix.with_suffix(".stderr").read_bytes() == expected


def terminal_report(args, status):
    report = json.loads(args.report.read_text())
    assert report["status"] == status
    assert "finishedUtc" in report
    if report["directory"] is not None:
        assert json.loads((Path(report["directory"]) / "report.json").read_text()) == report
    return report


@pytest.mark.parametrize("native_only", [False, True])
@pytest.mark.parametrize("mutation", ["deleted", "unreadable", "changed", "added"])
def test_actual_repeat_source_failure_is_terminal_and_preserves_prior_run(
        repeats, repeat_tree, tmp_path, monkeypatch, native_only, mutation):
    args = arguments(tmp_path)
    args.native_only = native_only
    if native_only:
        args.lean = tmp_path / "unavailable-formal-cli"
    assert repeats.RepeatSuite(args).run(lambda s: s.case("control", lambda: None)) == 0
    previous = terminal_report(args, "native-only" if native_only else "pass")
    old_directory = Path(previous["directory"])
    retained = {path: path.read_bytes() for path in old_directory.rglob("*") if path.is_file()}
    name = "lean/ZkcTools/StructuredSource/Bounds.lean"
    source = repeat_tree / name
    before = source.read_bytes()
    read_bytes = Path.read_bytes

    def mutate(suite):
        suite.case("control", lambda: None)
        if mutation == "deleted":
            source.unlink()
        elif mutation == "unreadable":
            def denied(path):
                if path == source:
                    raise PermissionError("captured observer is unreadable")
                return read_bytes(path)
            monkeypatch.setattr(Path, "read_bytes", denied)
        elif mutation == "changed":
            source.write_bytes(before + b"-- changed\r\n")
        else:
            source.with_name("NewDependency.lean").write_text("-- new dependency\n")

    assert repeats.RepeatSuite(args).run(mutate) == 1
    report = terminal_report(args, "failed")
    stability = next(item for item in report["checks"] if item["name"] == "source-stability")
    assert not stability["passed"]
    if mutation in ("deleted", "unreadable"):
        assert stability["errors"][name].startswith(
            "FileNotFoundError:" if mutation == "deleted" else "PermissionError:")
    elif mutation == "changed":
        assert name in stability["changed"]
    else:
        assert "lean/ZkcTools/StructuredSource/NewDependency.lean" in stability["added"]
    with tarfile.open(report["sourceArchives"]["before"]["path"]) as archive:
        assert archive.extractfile(name).read() == before
    assert report["run"] != previous["run"]
    assert all(path.read_bytes() == data for path, data in retained.items())


@pytest.mark.parametrize("native_only", [False, True])
@pytest.mark.parametrize("failure", ["missing-source", "unreadable-source", "tool", "allocation",
                                     "interrupt-setup", "interrupt-action", "interrupt-finish",
                                     "finish", "override-finish", "case", "no-checks"])
def test_actual_repeat_shared_lifecycle_failures(
        repeats, bridge, repeat_tree, tmp_path, monkeypatch, native_only, failure):
    args = arguments(tmp_path)
    args.native_only = native_only
    suite = repeats.RepeatSuite(args)

    def interrupt(*_args, **_kwargs):
        raise KeyboardInterrupt("interrupted control")

    def denied(*_args, **_kwargs):
        raise PermissionError("injected lifecycle failure")

    if failure == "missing-source":
        (repeat_tree / "lean/bridges/structured/fixtures/repeat.json").unlink()
    elif failure == "unreadable-source":
        source = repeat_tree / "lean/ZkcTools/StructuredSource/Bounds.lean"
        original = Path.read_bytes
        def unreadable(path):
            return denied() if path == source else original(path)
        monkeypatch.setattr(Path, "read_bytes", unreadable)
    elif failure == "tool":
        args.compiler = tmp_path / "missing-tool"
    elif failure == "allocation":
        monkeypatch.setattr(bridge, "new_directory", denied)
    elif failure == "interrupt-setup":
        monkeypatch.setattr(bridge, "archive_sources", interrupt)
    elif failure == "override-finish":
        monkeypatch.setattr(suite, "finish", denied)

    def action(s):
        if failure == "no-checks":
            return
        s.case("control", denied if failure == "case" else lambda: None)
        if failure == "interrupt-action":
            interrupt()
        if failure in ("interrupt-finish", "finish"):
            monkeypatch.setattr(bridge, "check_sources", interrupt if failure.startswith("interrupt") else denied)

    assert suite.run(action) == 1
    report = terminal_report(args, "interrupted" if failure.startswith("interrupt") else "failed")
    assert any(not check["passed"] for check in report["checks"])
    assert report["revision"] is None


@pytest.mark.parametrize("driver", ["shared", "repeat"])
@pytest.mark.parametrize("destination", ["selected", "retained"])
def test_terminal_publication_failure_attempts_both_reports(
        bridge, repeats, source_tree, repeat_tree, tmp_path, monkeypatch, driver, destination):
    args = arguments(tmp_path)
    if driver == "shared":
        monkeypatch.setattr(bridge, "ROOT", source_tree)
    suite = (bridge.Suite if driver == "shared" else repeats.RepeatSuite)(args)
    publish = bridge.atomic_json
    failed = []

    def fail_once(path, report):
        selected = path == args.report
        if report["status"] != "running" and selected == (destination == "selected") and not failed:
            failed.append(path)
            raise PermissionError("terminal destination temporarily unavailable")
        publish(path, report)

    monkeypatch.setattr(bridge, "atomic_json", fail_once)
    assert suite.run(lambda s: s.case("control", lambda: None)) == 1
    report = terminal_report(args, "failed")
    assert failed and report["checks"][-1]["name"] == "report-publication"


def test_repeat_inventory_captures_owners_and_runs_from_git_free_archive(
        repeats, repeat_tree, tmp_path, monkeypatch):
    args = arguments(tmp_path)
    args.native_only = True
    args.lean = tmp_path / "missing-formal-cli"
    # No inventory, revision or finalization operation may invoke Git.
    def no_git(*_args, **_kwargs):
        raise AssertionError("Git used by Git-free repeat evidence")
    monkeypatch.setattr(subprocess, "check_output", no_git)
    payload = b"exact authored bytes\r\n\x00\xff\n"
    (repeat_tree / "examples/project/main.zkc").write_bytes(payload)
    assert repeats.RepeatSuite(args).run(lambda s: s.case("control", lambda: None)) == 0
    report = terminal_report(args, "native-only")
    assert "lean" not in report["tools"] and report["revision"] is None
    record = report["sourceArchives"]["before"]
    manifest = json.loads(Path(record["manifest"]).read_text())
    assert "Git-free" in record["scope"]
    assert manifest["deletedTrackedPaths"] == []
    assert {
        "lean/ZkcTools/StructuredSource.lean", "lean/ZkcTools/StructuredSource/OpenEvaluation.lean",
        "lean/ZkcTools/StructuredSource/Bounds.lean", "lean/ZkcTools/JsonSupport.lean",
        "lean/FutureOwner/Dependency.lean", "scripts/reporting.py", "common/tests/support/project.py",
        "lean/support/lake.py", "libraries/lib/lib.zkc", "libraries/lib/zkc.toml",
        "compiler/include/zkc/Support/Json.h", "compiler/lib/Compiler/StructuredSource.cpp",
        "compiler/test/structured_reference.cpp",
        "common/unicode/manifest.json",
    } <= manifest["files"].keys()
    restored = tmp_path / "restored"
    with tarfile.open(record["path"]) as archive:
        assert set(archive.getnames()) == set(manifest["files"])
        assert archive.extractfile("examples/project/main.zkc").read() == payload
        for name, entry in manifest["files"].items():
            assert hashlib.sha256(archive.extractfile(name).read()).hexdigest() == entry["sha256"]
        assert all(not any(part in name for part in ("private", "experiments", ".lake", "__pycache__"))
                   for name in archive.getnames())
        archive.extractall(restored, filter="data")
    # Only archived Python sources are importable from the restored tree.
    restored_args = arguments(tmp_path / "restored-tools")
    command = [sys.executable, "-I", "-c", f'''
import argparse, pathlib, subprocess, sys
sys.path.insert(0, {str(restored / "lean/bridges/structured")!r})
import repeats
repeats.SUBJECTS = {repeats.SUBJECTS!r}
def no_git(*args, **kwargs):
    raise AssertionError("Git is unavailable")
subprocess.check_output = no_git
args = argparse.Namespace(report=pathlib.Path({str(restored_args.report)!r}), seed=1, cases=1,
    compiler=pathlib.Path({str(restored_args.compiler)!r}),
    reference=pathlib.Path({str(restored_args.reference)!r}), lean=None, runtime=None,
    native_only=True, write_fixtures=False)
sys.exit(repeats.RepeatSuite(args).run(lambda s: s.case("restored", lambda: None)))
''']
    result = subprocess.run(command, cwd=restored, capture_output=True, text=True, timeout=15)
    assert result.returncode == 0, result.stdout + result.stderr
    terminal_report(restored_args, "native-only")


def test_live_repeat_inventory_covers_main_lean_imports_and_python_owners(repeats, tmp_path):
    inventory = set(repeats.RepeatSuite(arguments(tmp_path)).source_inventory())
    for path in inventory:
        if path.suffix != ".lean":
            continue
        for module in re.findall(r"^\s*(?:public\s+)?import\s+(?:all\s+)?([\w.]+)",
                                 path.read_text(), flags=re.MULTILINE):
            dependency = ROOT / "lean" / (module.replace(".", "/") + ".lean")
            if dependency.exists():
                assert dependency in inventory, (path, dependency)
    for tree in ("scripts", "common/tests/support", "lean/bridges/structured"):
        assert set((ROOT / tree).glob("*.py")) <= inventory
    assert ROOT / "lean/ZkcTools/StructuredSource/Bounds.lean" in inventory
    assert set((ROOT / "common/unicode").rglob("*.txt")) <= inventory


@pytest.mark.parametrize("driver", ["shared", "repeat"])
def test_captured_tool_changes_fail_in_shared_setup(
        bridge, repeats, source_tree, repeat_tree, tmp_path, monkeypatch, driver):
    args = arguments(tmp_path)
    if driver == "shared":
        monkeypatch.setattr(bridge, "ROOT", source_tree)
    copy = shutil.copy2

    def changed(source, target):
        result = copy(source, target)
        if source == args.compiler:
            source.write_bytes(b"changed executable after copy\n")
        return result

    monkeypatch.setattr(shutil, "copy2", changed)
    suite = (bridge.Suite if driver == "shared" else repeats.RepeatSuite)(args)
    assert suite.run(lambda s: s.case("unreachable", lambda: None)) == 1
    report = terminal_report(args, "failed")
    assert "tool changed during capture" in report["checks"][0]["error"]


@pytest.mark.parametrize("failure", ["namespace", "executable", "directory-link", "file-link",
                                     "unreadable-directory"])
def test_repeat_inventory_refusals_are_terminal(
        repeats, repeat_tree, tmp_path, monkeypatch, failure):
    args = arguments(tmp_path)
    owner = repeat_tree / "lean/ZkcTools/StructuredSource"
    if failure == "namespace":
        shutil.rmtree(repeat_tree / "lean/FutureOwner")
    elif failure == "executable":
        (repeat_tree / "lean/ZkcTools/StructuredSource.lean").unlink()
    elif failure == "directory-link":
        (owner / "External").symlink_to(tmp_path, target_is_directory=True)
    elif failure == "file-link":
        (owner / "External.lean").symlink_to(repeat_tree / "lean/Zkc.lean")
    else:
        import os
        scandir = os.scandir
        def denied(path):
            if Path(path) == owner:
                raise PermissionError("observer source directory is unreadable")
            return scandir(path)
        monkeypatch.setattr(os, "scandir", denied)
    assert repeats.RepeatSuite(args).run(lambda s: s.case("unreachable", lambda: None)) == 1
    report = terminal_report(args, "failed")
    expected = ("FileNotFoundError:" if failure in ("namespace", "executable") else
                "PermissionError:" if failure == "unreadable-directory" else "ValueError:")
    assert report["checks"][0]["error"].startswith(expected)


@pytest.mark.parametrize("path", ["../private", ".", "/outside/project"])
def test_shared_explicit_inventory_refuses_paths_outside_root(bridge, tmp_path, path):
    with pytest.raises(ValueError):
        bridge.archive_sources(tmp_path, tmp_path / "source", inventory=[path])
    assert not (tmp_path / "source.tar.gz").exists()


@pytest.mark.parametrize("step", ["initial-publication", "after-archive"])
def test_shared_publication_and_regeneration_setup_finish_failures(
        bridge, source_tree, tmp_path, monkeypatch, step):
    monkeypatch.setattr(bridge, "ROOT", source_tree)
    args = arguments(tmp_path)
    previous = successful_run(bridge, args)
    old_report = (Path(previous["directory"]) / "report.json").read_bytes()
    if step == "initial-publication":
        publish = bridge.atomic_json
        failed = []
        def fail_once(path, report):
            if not failed:
                failed.append(path)
                raise PermissionError("initial running marker failed")
            publish(path, report)
        monkeypatch.setattr(bridge, "atomic_json", fail_once)
    else:
        args.write_fixtures = True

    def action(s):
        s.case("control", lambda: None)
        def denied(*_args, **_kwargs):
            raise PermissionError("after archive is unreadable")
        monkeypatch.setattr(bridge, "archive_sources", denied)

    assert bridge.Suite(args).run(action) == 1
    report = terminal_report(args, "failed")
    assert report["run"] != previous["run"]
    assert (Path(previous["directory"]) / "report.json").read_bytes() == old_report


@pytest.mark.parametrize("destination", ["selected", "retained"])
def test_permanently_unwritable_report_still_finalizes_other_destination(
        repeats, bridge, repeat_tree, tmp_path, monkeypatch, destination):
    args = arguments(tmp_path)
    publish = bridge.atomic_json
    def deny_terminal(path, report):
        if report["status"] != "running" and (path == args.report) == (destination == "selected"):
            raise PermissionError("report remains unwritable")
        publish(path, report)
    monkeypatch.setattr(bridge, "atomic_json", deny_terminal)
    suite = repeats.RepeatSuite(args)
    assert suite.run(lambda s: s.case("control", lambda: None)) == 1
    path = args.report if destination == "retained" else suite.directory / "report.json"
    report = json.loads(path.read_text())
    assert report["status"] == "failed" and report["checks"][-1]["name"] == "report-publication"


def test_source_deleted_at_capture_must_remain_absent(bridge, source_tree, tmp_path, monkeypatch):
    monkeypatch.setattr(bridge, "ROOT", source_tree)
    args = arguments(tmp_path)

    def restore(suite):
        (source_tree / "removed").write_text("restored during execution")
        suite.case("control", lambda: None)

    assert bridge.Suite(args).run(restore) == 1
    report = terminal_report(args, "failed")
    check = next(row for row in report["checks"] if row["name"] == "source-stability")
    assert check["restored"] == ["removed"] and not check["passed"]
