"""Refusal and residual-state controls for the optional participant bridge."""

import copy
import importlib.util
from pathlib import Path
import sys

import pytest

BRIDGE = Path(__file__).resolve().parents[3] / "lean/bridges/structured"
sys.path.insert(0, str(BRIDGE))
spec = importlib.util.spec_from_file_location("participant_comparison", BRIDGE / "participant.py")
comparison = importlib.util.module_from_spec(spec)
spec.loader.exec_module(comparison)
sys.path.remove(str(BRIDGE))


def test_missing_reply_is_pending_but_explicit_incomplete_is_not():
    request = ["receive", "message", "P", "V", ["field", "bls12-381.fr"]]
    missing = ["zkc.structured-open-result/0", ["stopped", "incomplete", "message"],
               [["request", 0, request], ["stop", "incomplete", "message", 0]], 0]
    native = dict(format="zkc.participant-observation/0", status="Pass", outcome=["pending", "message"], events=missing[2][:-1], consumed=0)
    comparison.compare_result(missing, native)
    explicit = copy.deepcopy(missing)
    explicit[2].insert(1, ["reply", 0, ["stop", "incomplete"]]); explicit[3] = 1
    assert not comparison.pending(explicit)
    with pytest.raises(comparison.Mismatch): comparison.compare_result(explicit, native)


@pytest.mark.parametrize("status", ["Unsupported", "Mismatch", "HarnessFailure"])
def test_nonpassing_native_status_cannot_pass(status):
    with pytest.raises(getattr(comparison, status)):
        comparison.compare_result(None, dict(format="zkc.participant-observation/0", status=status))


@pytest.mark.parametrize("observation", [
    dict(format="zkc.participant-observation/0", status="HarnessFailure"),
    dict(format="zkc.participant-observation/0", status="Unsupported"),
    dict(format="wrong", status="Mismatch"),
    None,
    dict(format="zkc.participant-observation/0", status="Mismatch", detail="query original root binding"),
    dict(format="zkc.participant-observation/0", status="Mismatch", reason="value-relation", detail='{"actual":"00","mapped":"00"}'),
])
def test_arithmetic_control_rejects_unrelated_failures(observation):
    with pytest.raises(comparison.HarnessFailure): comparison.compare_arithmetic_mutation(observation)


def test_post_consume_exhaustion_and_cancellation_have_different_residuals():
    providers = [dict(handle="17", budget=1, tape=["3", "8"])]
    draw = ["draw", "first", "P", "random.bls12-381.fr/0", "17", "bls12-381.fr"]
    good = ["reply", draw, ["value", "3"]]
    exhausted = comparison.provider_expected(providers, [good, ["reply", draw, ["stop", "exhausted"]]], False)
    cancelled = comparison.provider_expected(providers, [good, ["reply", draw, ["stop", "abort"]]], False)
    assert exhausted["17"] == dict(generation=2, draws=2, budget=0, poisoned=True, leased=False)
    assert cancelled["17"] == dict(generation=1, draws=1, budget=0, poisoned=False, leased=False)
    observed = {"17":dict(completion_known=True, poisoned=True, leased=False,
                          state=dict(generation=2, draws=2, budget=0, stage="rng"))}
    comparison.compare_providers(observed, exhausted)
    with pytest.raises(comparison.Mismatch): comparison.compare_providers(observed, cancelled)
    observed["17"]["completion_known"] = False
    with pytest.raises(comparison.Mismatch): comparison.compare_providers(observed, exhausted)


def test_projection_indices_are_read_and_checked_against_scopes():
    snapshot = ["zkc.structured-source/0", "original", "sha256:unused", "main", [], [], [], [
        ["function", "main", "protocol", "public", [["apply", "bool", []], ["service", "random.bls12-381.fr/0"]],
         [["apply", "bool", []]], ["protocol", ["V"], [["V"], ["V"]], [["V"]]], [], [],
         ["block", [[["draw", "V", "bls12-381.fr"], [1], [["apply", "field", [["domain", "Field", "bls12-381.fr"]]]], [], "draw"]], ["return", [0]]]]], [["main", []]]]
    projection = ('"protocol.projection"() {source = "main", actions = [{kind = "protocol.query", '
                  'service = 1 : i64, site = "draw"}], participants = [{inputs = [0], outputs = [0], '
                  'participant = @arbitrary, role = "V", service_inputs = [1]}]}')
    binding = comparison.projection_binding(projection, snapshot)["V"]
    assert binding["participant"] == "arbitrary" and binding["service_inputs"] == [1]
    assert binding["queries"] == {"draw": 1}
    with pytest.raises(comparison.Mismatch):
        comparison.projection_binding(projection.replace("service_inputs = [1]", "service_inputs = [0]"), snapshot)
    with pytest.raises(comparison.Unsupported): comparison.projection_binding("", snapshot)


def test_copied_provenance_cannot_bind_changed_source_or_snapshot(tmp_path):
    original = tmp_path / "source.mlir"
    original.write_text("original operand")
    retained = ["format", "original", "sha256:" + comparison.digest(original), "body"]
    comparison.bind_snapshot(original, retained, copy.deepcopy(retained))
    changed = copy.deepcopy(retained); changed[3] = "different body"
    with pytest.raises(comparison.Mismatch): comparison.bind_snapshot(original, changed, retained)
    original.write_text("mutated operand")
    with pytest.raises(comparison.Mismatch): comparison.bind_snapshot(original, retained, retained)


@pytest.mark.parametrize("failure", ["missing-tool", "allocation", "interrupt"])
def test_shared_lifecycle_replaces_selected_success_without_mutating_old_run(tmp_path, monkeypatch, failure):
    import argparse
    import json
    import subprocess

    shared = comparison.structured
    combined = comparison.Suite
    root = tmp_path / "source"; root.mkdir(); (root / "input.zkc").write_text("source")
    subprocess.run(["git", "init", "-q", root], check=True)
    subprocess.run(["git", "add", "."], cwd=root, check=True)
    subprocess.run(["git", "-c", "user.name=Test", "-c", "user.email=test@example.invalid",
                    "commit", "-qm", "source"], cwd=root, check=True)
    revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=root, text=True).strip()
    monkeypatch.setattr(shared, "ROOT", root)
    tool = tmp_path / "tool"; tool.write_text("#!/bin/sh\nexit 0\n"); tool.chmod(0o755)
    args = argparse.Namespace(report=tmp_path / "selected.json", seed=0, cases=1,
        compiler=tool, optimizer=tool, reference=tool, lean=tool, runtime=tool,
        compiler_source=root, lean_source=root, compiler_revision=revision, lean_revision=revision)
    assert combined(args).run(lambda suite: suite.checks.append(dict(name="control", passed=True))) == 0
    previous = json.loads(args.report.read_text())
    old_report = Path(previous["directory"]) / "report.json"; old_bytes = old_report.read_bytes()
    old_tool = Path(previous["tools"]["runtime"]["path"]); old_tool_bytes = old_tool.read_bytes()

    def fail(*_args):
        current = json.loads(args.report.read_text())
        assert current["status"] == "running" and current["run"] != previous["run"]
        if failure == "interrupt": raise KeyboardInterrupt()
        raise OSError("allocation failure")

    def action(_): pass
    if failure == "missing-tool": args.runtime = tmp_path / "missing"
    elif failure == "allocation": monkeypatch.setattr(shared, "new_directory", fail)
    else: action = fail
    assert combined(args).run(action) == 1
    current = json.loads(args.report.read_text())
    assert current["status"] == ("interrupted" if failure == "interrupt" else "failed")
    assert any(not check["passed"] for check in current["checks"])
    if current["directory"]:
        assert json.loads((Path(current["directory"]) / "report.json").read_text()) == current
    assert old_report.read_bytes() == old_bytes and old_tool.read_bytes() == old_tool_bytes


def test_malformed_observation_is_harness_failure():
    with pytest.raises(comparison.HarnessFailure):
        comparison.compare_result(None, dict(status="Pass", format="wrong"))


@pytest.mark.parametrize("failure", [
    "none", "changed-harness", "deleted-harness", "restored-harness",
    "changed-external", "deleted-external", "detail-publication", "selected-publication", "interrupt",
    "detail-read-once", "detail-read-persistent", "detail-read-interrupt-persistent", "interrupt-detail-write",
])
def test_terminal_detail_and_selected_source_roots_agree(tmp_path, monkeypatch, failure):
    import argparse
    import json
    import subprocess

    def repository(name):
        root = tmp_path / name
        root.mkdir()
        (root / "input.zkc").write_text("original")
        (root / "restored.lean").write_text("def restored := 1\n")
        subprocess.run(["git", "init", "-q", root], check=True)
        subprocess.run(["git", "add", "."], cwd=root, check=True)
        subprocess.run(["git", "-c", "user.name=Test", "-c", "user.email=test@example.invalid",
                        "commit", "-qm", "source"], cwd=root, check=True)
        revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=root, text=True).strip()
        return root, revision

    root, _ = repository("harness")
    external, revision = repository("build-source")
    shared = comparison.structured
    monkeypatch.setattr(shared, "ROOT", root)
    tool = tmp_path / "tool"
    tool.write_text("#!/bin/sh\nexit 0\n")
    tool.chmod(0o755)
    args = argparse.Namespace(report=tmp_path / "selected.json", seed=0, cases=1,
        compiler=tool, optimizer=tool, reference=tool, lean=tool, runtime=tool,
        compiler_source=external, lean_source=external,
        compiler_revision=revision, lean_revision=revision)
    if failure == "restored-harness":
        (root / "restored.lean").unlink()

    def action(suite):
        suite.checks.append(dict(name="comparison", passed=True))
        if failure == "interrupt":
            raise KeyboardInterrupt()
        if failure.startswith(("changed-", "deleted-")):
            source = (external if failure.endswith("external") else root) / "input.zkc"
            if failure.startswith("changed-"):
                source.write_text("changed")
            else:
                source.unlink()
        elif failure == "restored-harness":
            (root / "restored.lean").write_text("def restored := 1\n")
        elif failure.endswith("publication") or failure == "interrupt-detail-write":
            detail_failure = failure != "selected-publication"
            owner = suite.evidence if detail_failure else shared
            publish = owner.atomic_json
            failed = []

            def fail_once(path, report):
                selected = path.name == "participant.json" if detail_failure else path == args.report
                if selected and report["status"] != "running" and (not failed or failure == "interrupt-detail-write"):
                    failed.append(path)
                    raise PermissionError("terminal publication failed")
                publish(path, report)

            monkeypatch.setattr(owner, "atomic_json", fail_once)
            if failure == "interrupt-detail-write":
                raise KeyboardInterrupt()
        elif failure.startswith("detail-read-"):
            read_bytes = Path.read_bytes
            failed = []

            def fail_detail_read(path):
                if path.name == "participant.json" and (not failed or failure.endswith("persistent")):
                    failed.append(path)
                    if "interrupt" in failure:
                        raise KeyboardInterrupt()
                    raise PermissionError("terminal detail read failed")
                return read_bytes(path)

            monkeypatch.setattr(Path, "read_bytes", fail_detail_read)

    suite = comparison.Suite(args)
    assert suite.run(action) == (0 if failure == "none" else 1)
    report = json.loads(args.report.read_text())
    detail_path = suite.directory / "participant.json"
    detail = json.loads(detail_path.read_text())
    status = "pass" if failure == "none" else "interrupted" if "interrupt" in failure else "failed"
    assert report["status"] == status
    assert report["finishedUtc"]
    # An unwritable detail may retain its old contents, but must be unreferenced.
    assert detail["status"] == ("running" if failure == "interrupt-detail-write" else status)
    assert json.loads((suite.directory / "report.json").read_text()) == report
    retained = [row for row in report["sources"] if row["name"] == "participant-observations"]
    if failure.endswith("persistent") or failure == "interrupt-detail-write":
        assert not retained
    else:
        assert len(retained) == 1 and retained[0]["sha256"] == comparison.digest(detail_path)
    if failure in ("changed-external", "deleted-external"):
        checks = {row["name"]: row for row in report["checks"]}
        assert checks["source-stability"]["passed"]
        assert not checks["compiler-source-stability"]["passed"]
        assert not checks["lean-source-stability"]["passed"]
    if failure == "restored-harness":
        check = next(row for row in report["checks"] if row["name"] == "source-stability")
        assert check["restored"] == ["restored.lean"] and not check["passed"]
