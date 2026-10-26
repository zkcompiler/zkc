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


def test_evaluation_uses_lake_package_options_and_import_builds(driver_module, tmp_path):
    driver, calls = recording(driver_module, tmp_path)
    path = tmp_path / "Fresh.lean"
    driver.evaluate(path, "import Example.Charges\nimport Example.Glue\n\n#eval 1\n",
                    cwd=tmp_path, name="fresh")
    assert calls == [(["lake", "lean", str(path)], str(tmp_path))]
    other = tmp_path / "integration"
    driver.evaluate(path, "import Example.Glue\n", cwd=other, name="elsewhere")
    assert calls[-1] == (["lake", "lean", str(path)], str(other))


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
    assert not builds  # lake lean owns import rebuilding, including rewritten imports.
    assert module.read_text() == "changed\n"


@pytest.mark.parametrize("write", [False, True])
def test_normal_forms_require_a_fresh_module_build(driver_module, tmp_path, monkeypatch, write):
    monkeypatch.setattr(driver_module, "ROOT", tmp_path)
    monkeypatch.setattr(driver_module, "LEAN", tmp_path / "lean")
    output = tmp_path / "lean/Example/NormalForms.lean"
    output.parent.mkdir(parents=True)
    output.write_text("module\n")
    request = tmp_path / "request.toml"
    request.write_text('output = "lean/Example/NormalForms.lean"\n')
    subject = SimpleNamespace(name="example", get=lambda *_: "request.toml")
    driver, calls = recording(driver_module, tmp_path, write=write)
    driver.built.add((str(driver_module.LEAN), "Example.NormalForms"))
    record = {"generated": {}, "checks": []}
    driver.normal_forms(subject, record)
    assert calls[0][0][-1] == (str(request) if write else "--check")
    assert calls[-1][0] == ["lake", "build", "Example.NormalForms"]
    assert record["generated"]["lean/Example/NormalForms.lean"]["sha256"] == driver_module.file_digest(output)
    assert record["checks"][0]["outcome"] == "accepted"


def test_normal_forms_build_failure_cannot_record_acceptance(driver_module, tmp_path, monkeypatch):
    monkeypatch.setattr(driver_module, "ROOT", tmp_path)
    monkeypatch.setattr(driver_module, "LEAN", tmp_path / "lean")
    (tmp_path / "request.toml").write_text('output = "lean/Example/NormalForms.lean"\n')
    subject = SimpleNamespace(name="example", get=lambda *_: "request.toml")
    driver, _ = recording(driver_module, tmp_path)

    def fail(*_args, **_kwargs):
        raise driver_module.Refused("generated theorem did not elaborate")

    monkeypatch.setattr(driver, "build", fail)
    record = {"generated": {}, "checks": []}
    with pytest.raises(driver_module.Refused, match="did not elaborate"):
        driver.normal_forms(subject, record)
    assert record == {"generated": {}, "checks": []}


def test_threshold_is_evaluated_after_the_generated_facts(driver_module, tmp_path, monkeypatch):
    monkeypatch.setattr(driver_module, "ROOT", tmp_path)
    public = tmp_path / "public.json"
    public.write_text(json.dumps({"rounds": "2"}))
    settings = {("executable", "charge"): "Example.Charges.charge",
                ("executable", "charge_arguments"): ["rounds"],
                ("executable", "completeness_module"): "Example.Completeness",
                ("entries", "proof"): "example::Proof"}
    subject = SimpleNamespace(
        name="example", construction_namespace="Example.Glue",
        get=lambda table, key, default=None: settings.get((table, key), default),
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
    commands = [arguments[1:] if arguments[1] == "build" else [arguments[1], arguments[2].rsplit("/", 1)[-1]]
                for arguments, _ in calls]
    assert commands == [["build", "Example.Program"], ["lean", "FreshLowering.lean"],
                        ["build", "Example.Facts"],
                        ["lean", "FreshCharge.lean"]]
    assert facts["threshold"] == record["kernel"]["lowering"]["threshold"] == 186


@pytest.mark.parametrize("status,definitions,attempts", [
    ("incomplete", ["registered model definition"], []),
    ("refused", [], [{"status": "refused", "reason": "unknown version"}]),
    ("open", [], []),
])
@pytest.mark.parametrize("explicit_entries", [False, True])
def test_claim_records_preserve_semantic_status_and_every_source_node(
        driver_module, tmp_path, monkeypatch, status, definitions, attempts, explicit_entries):
    """Automation failure must not invent missing definitions or a receipt."""
    settings = {("lean", "namespace"): "Example", ("executable", "namespace"): None}
    subject = SimpleNamespace(
        name="example", construction_namespace="Example.Glue",
        get=lambda table, key, default=None: settings.get((table, key), default),
        profile=lambda key: False, module_name=lambda key: "Example." + key.capitalize(),
        generated=lambda key: tmp_path / (key.capitalize() + ".lean"),
        generated_package=lambda key: tmp_path)
    claims = [{"attachment": {"node": {"owner": "proof", "claim": 0}}, "request_digest": "proof"}]
    interactive_claims = [{"attachment": {"node": {"owner": "interactive", "claim": 0}},
                           "request_digest": "interactive"}]
    artifacts = {"source_claims": {"entry": "example::Proof", "claims": claims}}
    interactive = {"source_claims": {"entry": "example::Interactive", "claims": interactive_claims}}
    inventory = [{"node": claim["attachment"]["node"]} for claim in claims + interactive_claims]
    artifacts["source_claim_inventory"] = inventory
    interactive["source_claim_inventory"] = inventory
    resolution = {"status": status, "definitions": definitions, "diagnostic": "automation or resolver detail"}
    messages = [dict(request="Example.request0Data", receipt="Example.request0Receipt", attempts=[]),
                dict(request="Example.request1Data", receipt=None, resolution=resolution, attempts=attempts)]
    stdout = "\n".join("SOURCE_CLAIM_RESULT " + json.dumps(value) for value in messages)
    driver, _ = recording(driver_module, tmp_path, outputs={"example:claims-build": stdout})
    if explicit_entries:
        driver.args.claim_entry = ["example::Proof", "example::Interactive"]
    monkeypatch.setattr(driver_module.evidence, "artifacts_module", lambda *args: "artifacts")
    monkeypatch.setattr(driver_module.evidence, "claims_module", lambda *args: "wire data")
    monkeypatch.setattr(driver, "generated", lambda *args: None)
    record = {"checks": []}
    driver.claims(subject, artifacts, None, record, interactive)
    expected_entries = ["example::Proof", "example::Interactive"] if explicit_entries else ["example::Proof"]
    assert record["source_claims"]["entries"] == expected_entries
    assert [row["selection"] for row in record["source_claim_inventory"]] == [
        "selected", "selected" if explicit_entries else "unselected-subject"]
    if explicit_entries:
        assert len(record["claim_receipts"]) == 2
        failed = record["claim_receipts"][1]
        assert not record["source_claim_trials"]
    else:
        assert len(record["claim_receipts"]) == 1
        trial, = record["source_claim_trials"]
        assert trial["entry"] == "example::Interactive"
        assert trial["claims"] == interactive_claims
        failed, = trial["claim_receipts"]
    assert failed["resolution"] == resolution
    assert failed["attempts"] == attempts
    assert failed["receipt_declaration"] is None
    assert [value for value in record["checks"] if value["name"] == "claim-receipt"] == [
        {"name": "claim-receipt", "outcome": "accepted", "module": "Example.Claims",
         "request": "Example.request0Data", "receipt": "Example.request0Receipt"}]


def test_security_registry_does_not_import_the_optional_integration(driver_module, tmp_path):
    driver, calls = recording(driver_module, tmp_path, outputs={
        "registry:security": "ENTRY\tgeneric\tmodel\tstatement\n",
        "registry:arklib": "ENTRY\toptional\tmodel\tstatement\n"})
    driver.output.mkdir()
    assert set(driver.registry()) == {"generic"}
    source = (driver.output / "Registry-security.lean").read_text()
    assert "import ZkcSecurity.Registry" in source
    assert "ZkcArkLib" not in source
    assert all("arklib" not in cwd for _, cwd in calls)
    assert set(driver.registry("arklib")) == {"optional"}
    assert "import ZkcArkLib.Registry" in (driver.output / "Registry-arklib.lean").read_text()


def test_missing_physical_configuration_retains_open_source_requests(driver_module, tmp_path):
    driver, calls = recording(driver_module, tmp_path)
    subject = SimpleNamespace(get=lambda *args: None)
    claim = {"attachment": {"node": {"owner": "entry", "claim": 0}}, "request_digest": "source"}
    record = {}
    driver.claims(subject, {"source_claims": {"claims": [claim]},
                            "source_claim_inventory": [{"node": claim["attachment"]["node"]}]}, None, record)
    assert not calls
    row, = record["claim_receipts"]
    assert row["node"] == claim["attachment"]["node"]
    assert row["request_declaration"] is None
    assert row["receipt_declaration"] is None
    assert row["resolution"]["status"] == "open"
    assert row["resolution"]["definitions"] == []
    assert row["attempts"][0]["status"] == "unsupported"


def test_structured_only_subject_preserves_unselected_claim_inventory(driver_module, tmp_path, monkeypatch):
    monkeypatch.setattr(driver_module, "ROOT", tmp_path)
    manifest = tmp_path / "subject.toml"
    manifest.write_text("source fixture")
    subject = SimpleNamespace(
        name="structured", path=manifest, modules={},
        profile=lambda name: name == "structured", table=lambda name: {},
        get=lambda table, key, default=None: default)
    inventory = [{"node": {"kind": "source-claim", "owner": "library::Run", "block": 0, "claim": 0}}]
    driver, _ = recording(driver_module, tmp_path)
    monkeypatch.setattr(driver, "interactive", lambda subject, record:
                        {"source_claim_inventory": inventory})
    driver.subject(subject)
    record = json.loads(driver.write_evidence(subject.name).read_text())
    assert record["source_claim_inventory"] == [dict(inventory[0], selection="unselected-subject")]
    assert "claim_receipts" not in record


def test_construction_regeneration_preserves_the_maintained_endpoint(driver_module, tmp_path, monkeypatch):
    """Admission regeneration must never replace an authored source connection."""
    monkeypatch.setattr(driver_module, "ROOT", tmp_path)
    driver, _ = recording(driver_module, tmp_path, write=True)
    endpoint = tmp_path / "Connection.lean"
    metadata = tmp_path / "AdmissionData.lean"
    endpoint.write_text("maintained actual Domain connection\n")
    subject = SimpleNamespace(
        name="arbitrary-entry", generated=lambda key: metadata,
        get=lambda table, key, default=None: default)
    record = {"generated": {}}
    driver.generated(subject, "glue", "generated static admission\n", record)
    assert endpoint.read_text() == "maintained actual Domain connection\n"
    assert metadata.read_text() == "generated static admission\n"
    assert set(record["generated"]) == {"AdmissionData.lean"}


def test_byte_evidence_regeneration_preserves_source_artifacts(driver_module, tmp_path, monkeypatch):
    """A byte proof dependency must not be reintroduced into source metadata."""
    monkeypatch.setattr(driver_module, "ROOT", tmp_path)
    driver, _ = recording(driver_module, tmp_path, write=True)
    artifact = tmp_path / "Artifacts.lean"
    artifact.write_text("fixed artifact and checked source connection\n")
    subject = SimpleNamespace(name="arbitrary-entry", generated=lambda key:
                              tmp_path / "Lowering.lean" if key == "lowering" else artifact)
    record = {"generated": {}}
    driver.generated(subject, "lowering", "actual byte-to-Domain transport\n", record)
    assert artifact.read_text() == "fixed artifact and checked source connection\n"
    assert (tmp_path / "Lowering.lean").read_text() == "actual byte-to-Domain transport\n"
    assert set(record["generated"]) == {"Lowering.lean"}


@pytest.mark.parametrize("evaluated", ["true", "false"])
def test_receipt_process_equations_are_attribution_only(driver_module, tmp_path, monkeypatch, evaluated):
    driver, _ = recording(driver_module, tmp_path)
    theorem = "Example.receipt"
    equation = "ZkcExamples.ValidConnection"
    values = {("receipt", "theorem"): theorem, ("receipt", "chain"): [theorem],
              ("receipt", "security_module"): "Example"}
    subject = SimpleNamespace(name="example", table=lambda key: {"theorem": theorem},
                              get=lambda table, key, default=None: values.get((table, key), default))
    monkeypatch.setattr(driver_module, "printed_axioms", lambda _: {theorem: []})
    driver.evaluate = lambda *args, **kwargs: SimpleNamespace(stdout=(
        "control-equation ZkcExamples.ClassificationControl.compiled evaluated=true compiled=true\n"
        f"process-equation {theorem} {equation} evaluated={evaluated} compiled=true\n"))
    report = driver.receipt_axioms([subject])["example"]
    assert report["compiled_stage_equations"] == [equation]
    assert report["evaluated_compiled_stage_equations"] == ([equation] if evaluated == "true" else [])


def test_receipt_attribution_does_not_relax_axiom_check(driver_module, tmp_path, monkeypatch):
    from bridges.common.lean_render import CheckFailed
    driver, _ = recording(driver_module, tmp_path)
    values = {("receipt", "theorem"): "Example.receipt", ("receipt", "chain"): ["Example.receipt"],
              ("receipt", "security_module"): "Example"}
    subject = SimpleNamespace(name="example", table=lambda key: values,
                              get=lambda table, key, default=None: values.get((table, key), default))
    driver.evaluate = lambda *args, **kwargs: SimpleNamespace(stdout="")
    monkeypatch.setattr(driver_module, "printed_axioms", lambda _: {"Example.receipt": ["sorryAx"]})
    with pytest.raises(CheckFailed, match="axioms:Example.receipt"):
        driver.receipt_axioms([subject])
