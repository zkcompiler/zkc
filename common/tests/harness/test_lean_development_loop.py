"""Selected validation remains explicit; body replay is only a Lake build."""

import json
from pathlib import Path
import shutil
import sys

import pytest

from harness import load

ROOT = Path(__file__).resolve().parents[3]


def runner(monkeypatch, tmp_path, arguments):
    api = load("development_loop", "common/tests/run.py")
    calls = []
    monkeypatch.setattr(api, "run", lambda command, **_: calls.append(list(map(str, command))))
    monkeypatch.setenv("ZKC_REPORTS_DIR", str(tmp_path / "reports"))
    monkeypatch.setattr(sys, "argv", ["run.py", "lean-native", *arguments])
    return api, calls


def test_subject_selection_keeps_runtime_and_reports_partial_coverage(monkeypatch, tmp_path):
    api, calls = runner(monkeypatch, tmp_path, ["--stage", "subjects", "--subject", "schnorr"])
    api.main()
    assert len(calls) == 2
    assert calls[0][-1] == "--preflight"
    assert "--runtime" in calls[1] and calls[1][-2:] == ["--subject", "schnorr"]
    selection, = (tmp_path / "reports").rglob("selection.json")
    data = json.loads(selection.read_text())
    assert data["coverage"] == "partial"
    assert data["completed"] == ["preflight", "subjects"]
    assert data["subjects"] == ["schnorr"]


@pytest.mark.parametrize("arguments", [
    ["--subject", "schnorr"], ["--stage", "reports"],
    ["--stage", "bridges", "--fresh-bodies"], ["--stage", "subjects", "--stage", "subjects"],
])
def test_invalid_selection_runs_nothing(monkeypatch, tmp_path, arguments):
    api, calls = runner(monkeypatch, tmp_path, arguments)
    with pytest.raises(SystemExit):
        api.main()
    assert calls == []


def test_preflight_failure_stops_before_expensive_work(monkeypatch, tmp_path):
    api, calls = runner(monkeypatch, tmp_path, [])

    def fail(command, **_):
        calls.append(command)
        raise ValueError("changed dependency")

    monkeypatch.setattr(api, "run", fail)
    with pytest.raises(ValueError, match="changed dependency"):
        api.main()
    assert len(calls) == 1 and calls[0][-1] == "--preflight"
    selection, = (tmp_path / "reports").rglob("selection.json")
    data = json.loads(selection.read_text())
    assert data["failed"] == "preflight" and data["completed"] == []


def test_selected_reports_follow_fresh_selected_subjects(monkeypatch, tmp_path):
    api, calls = runner(monkeypatch, tmp_path,
                        ["--stage", "subjects", "--stage", "reports", "--subject", "schnorr"])
    api.main()
    assert len(calls) == 3
    assert calls[1][-2:] == calls[2][-2:] == ["--subject", "schnorr"]
    output = calls[1][calls[1].index("--output") + 1]
    assert calls[2][calls[2].index("--evidence") + 1] == str(Path(output) / "evidence")


def test_later_failure_retains_completed_stages(monkeypatch, tmp_path):
    api, calls = runner(monkeypatch, tmp_path, ["--stage", "subjects", "--stage", "reports"])

    def fail_report(command, **_):
        calls.append(command)
        if "--evidence" in command:
            raise ValueError("report failure")

    monkeypatch.setattr(api, "run", fail_report)
    with pytest.raises(ValueError, match="report failure"):
        api.main()
    selection, = (tmp_path / "reports").rglob("selection.json")
    data = json.loads(selection.read_text())
    assert data["completed"] == ["preflight", "subjects"] and data["failed"] == "reports"


def test_lake_printer_replay_tracks_source_private_proofs_and_printer(monkeypatch, tmp_path):
    if not shutil.which("lake"):
        pytest.skip("Lake is not installed")
    monkeypatch.syspath_prepend(str(ROOT / "lean"))
    from bridges.structured import printer_build as api
    from bridges.common.lean_render import Runner, CheckFailed

    root = tmp_path / "lean"
    root.mkdir()
    (root / "lean-toolchain").write_bytes((ROOT / "lean/lean-toolchain").read_bytes())
    (root / "lakefile.toml").write_text('name = "zkc"\n[[lean_lib]]\nname = "Datum"\n'
                                      'globs = ["Datum", "Provider"]\n')
    (root / "lake-manifest.json").write_text(json.dumps(dict(
        version="1.2.0", name="zkc", packagesDir=".lake/packages", packages=[], lakeDir=".lake")))
    monkeypatch.setattr(api, "LEAN", root)
    source = root / "Datum.lean"
    provider = root / "Provider.lean"
    provider.write_text("module\npublic theorem fact : True := True.intro\n")
    def write(value):
        source.write_text(f"module\npublic import Provider\n@[expose] public section\n"
                          f"def value : Nat := {value}\n")
    write(2)
    program = ('import Datum\n#eval IO.println "ZKC_BODY_OUTPUT_BEGIN"\n'
               '#eval IO.println value\n#print axioms fact\n'
               '#eval IO.println "ZKC_BODY_OUTPUT_END"\n')
    driver = Runner()
    with api.workspace("Datum") as directory:
        def run(text=program):
            return api.elaborate(driver, directory, "Inventory", text, "Datum", "lake")
        first = run()
        artifact = directory / ".lake/build/lib/lean/Inventory.olean"
        timestamp = artifact.stat().st_mtime_ns
        assert run() == first and artifact.stat().st_mtime_ns == timestamp
        write(3)
        assert run().startswith("3\n")
        # A theorem's statement is unchanged, but the legacy printer import
        # includes private proof artifacts. Replay must observe the new axiom.
        unchanged = source.read_bytes(), (directory / "Inventory.lean").read_bytes()
        provider.write_text("module\npublic theorem fact : True := Classical.choice ⟨True.intro⟩\n")
        assert "Classical.choice" in run()
        assert unchanged == (source.read_bytes(), (directory / "Inventory.lean").read_bytes())
        assert run(program.replace("IO.println value", "IO.println (value + 1)")).startswith("4\n")
        artifact.unlink()
        assert run().startswith("3\n") and artifact.exists()
        with pytest.raises(CheckFailed, match="building body printer"):
            run(program + "\nthis is invalid Lean\n")
        assert run().startswith("3\n")
    with pytest.raises(CheckFailed, match="unique message frame"):
        api.messages("corrupted output")
    # No declaration or assurance status is stored by the printer workspace.
    assert not list((root / ".lake/body-printers").rglob("*.jsonl"))


def test_selected_report_comparison_rejects_regressions_and_keeps_open_subjects(monkeypatch, tmp_path):
    api = load("selected_record_reports", "lean/checks/check_records.py")
    monkeypatch.setattr(api, "ROOT", tmp_path)
    document = tmp_path / "support.md"
    header = "| Subject | Status |\n|---|---|\n"
    expected = header + "| certified | established |\n| open | unresolved |\n"
    document.write_text(api.ledger.replace_region(
        f"{api.ledger.begin('subject-rows')}\n{api.ledger.end('subject-rows')}\n", "subject-rows", expected))
    for subject, outcome in [("certified", "established"), ("open", "unresolved")]:
        failures, notes = [], []
        api.compare(document, "subject-rows", header + f"| {subject} | {outcome} |\n",
                    False, failures, notes, subjects={subject})
        assert failures == []
    failures = []
    api.compare(document, "subject-rows", header + "| certified | unresolved |\n",
                False, failures, [], subjects={"certified"})
    assert failures and "stale" in failures[0]
