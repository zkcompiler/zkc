"""Build ordering of the Lean subject driver, without Lean or a compiler."""

import argparse
import json
from types import SimpleNamespace

import pytest

from harness import load


@pytest.fixture
def driver_module():
    return load("subject_driver", "lean/bridges/subject.py")


def recording(driver_module, tmp_path, outputs=None, write=False):
    """A driver whose commands are recorded, with `outputs` as the standard output
    of the evaluations they name."""
    driver = driver_module.Driver(argparse.Namespace(lake="lake", output=tmp_path / "evidence", write=write))
    calls = []

    def run(arguments, *, cwd=None, expect=0, name=None):
        calls.append(([str(argument) for argument in arguments], str(cwd)))
        return SimpleNamespace(stdout=(outputs or {}).get(name, ""), returncode=0)

    driver.run = run
    return driver, calls


def test_evaluation_builds_its_imports_first(driver_module, tmp_path):
    driver, calls = recording(driver_module, tmp_path)
    path = tmp_path / "Fresh.lean"
    driver.evaluate(path, "import Example.Charges\nimport Example.Glue\n\n#eval 1\n", cwd=tmp_path, name="fresh")
    assert calls == [(["lake", "build", "Example.Charges", "Example.Glue"], str(tmp_path)),
                     (["lake", "env", "lean", str(path)], str(tmp_path))]
    # Built modules are not rebuilt by a later evaluation in the same package, but
    # are in another package.
    calls.clear()
    driver.evaluate(path, "import Example.Glue\n", cwd=tmp_path, name="again")
    other = tmp_path / "integration"
    driver.evaluate(path, "import Example.Glue\n", cwd=other, name="elsewhere")
    assert calls == [(["lake", "env", "lean", str(path)], str(tmp_path)),
                     (["lake", "build", "Example.Glue"], str(other)),
                     (["lake", "env", "lean", str(path)], str(other))]


def test_rewritten_module_invalidates_builds(driver_module, tmp_path, monkeypatch):
    monkeypatch.setattr(driver_module, "ROOT", tmp_path)
    driver, calls = recording(driver_module, tmp_path, write=True)
    module = tmp_path / "Generated.lean"
    subject = SimpleNamespace(name="example", generated=lambda key: module)
    record = {"generated": {}}
    module.write_text("unchanged\n")
    driver.evaluate(tmp_path / "Fresh.lean", "import Example.Proof\n", cwd=tmp_path, name="first")
    # An unchanged module keeps the builds; a changed one makes the next
    # evaluation rebuild what it imports.
    driver.generated(subject, "program", "unchanged\n", record)
    driver.evaluate(tmp_path / "Fresh.lean", "import Example.Proof\n", cwd=tmp_path, name="second")
    driver.generated(subject, "program", "changed\n", record)
    driver.evaluate(tmp_path / "Fresh.lean", "import Example.Proof\n", cwd=tmp_path, name="third")
    builds = [arguments for arguments, _ in calls if arguments[:2] == ["lake", "build"]]
    assert builds == [["lake", "build", "Example.Proof"]] * 2
    assert module.read_text() == "changed\n"


def test_threshold_is_evaluated_after_the_generated_facts(driver_module, tmp_path, monkeypatch):
    monkeypatch.setattr(driver_module, "ROOT", tmp_path)
    public = tmp_path / "public.json"
    public.write_text(json.dumps({"rounds": "2"}))
    settings = {("executable", "charge"): "Example.Charges.charge",
                ("executable", "charge_arguments"): ["rounds"],
                ("executable", "completeness_module"): "Example.Completeness",
                ("entries", "proof"): "example::Proof"}
    subject = SimpleNamespace(
        name="example", get=lambda table, key, default=None: settings.get((table, key), default),
        module_name=lambda key: f"Example.{key.capitalize()}", generated=lambda key: tmp_path / f"{key}.lean",
        inputs=lambda entry, kind: public)
    entry = SimpleNamespace(names=[], types=[])
    record = {"generated": {}, "kernel": {}}

    def lowering_rule(subject, artifacts, entry, record):
        # The rule's own evaluation reads only the generated glue and the rules.
        driver.lean(subject, "FreshLowering.lean", "import Example.Glue\n")
        record["kernel"]["lowering"] = {"threshold": None}
        return {"total": None}

    monkeypatch.setattr(driver_module.executable, "render", lambda deployment, namespace: "program\n")
    monkeypatch.setattr(driver_module.glue, "facts_module", lambda *arguments: "facts\n")
    driver, calls = recording(driver_module, tmp_path, outputs={"example:FreshCharge.lean": "charge 186\n"},
                              write=True)
    monkeypatch.setattr(driver, "lowering_rule", lowering_rule)
    facts = driver.executable(subject, {"deployment": None}, entry, record)
    commands = [arguments[1:] if arguments[1] == "build" else arguments[1:3] + [arguments[3].rsplit("/", 1)[-1]]
                for arguments, _ in calls]
    assert commands == [["build", "Example.Program"],
                        ["build", "Example.Glue"], ["env", "lean", "FreshLowering.lean"],
                        ["build", "Example.Facts"],
                        ["build", "Example.Completeness"], ["env", "lean", "FreshCharge.lean"]]
    assert facts["threshold"] == record["kernel"]["lowering"]["threshold"] == 186
