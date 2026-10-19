"""Negative controls for the ledger check and the report generator.

Each control builds a small synthetic input, changes one thing, and requires
the documented reaction: a stale or changed headline fails the ledger check,
a theorem that depends on `sorryAx` is unresolved, and an omitted premise, a
mismatched artifact or an unsupported endpoint claim make a report
`unresolved`. A control that would pass on the unchanged input is checked on
that input too, so a control cannot pass vacuously.
"""

import copy
import hashlib
import json
from pathlib import Path
import tempfile

from . import ledger, reports
from .declarations import Records

PROPERTY = "soundness"
THEOREM = "Sample.Endpoint.soundness"
INSTANCE = "Sample.Examples.evidence"
SCHEMA = "Sample.Links.AcceptanceInclusion"


def record(name, *, kind="theorem", axioms=("propext",), premises=(), detail=None, hashes=("1", "2")):
    value = {"name": name, "module": name.rsplit(".", 1)[0], "kind": kind,
             "statement": {"structural": hashes[0], "explicit": hashes[1]},
             "axioms": list(axioms), "doc": None, "tags": [], "package": "sample"}
    if premises:
        value["premises"] = list(premises)
    if detail is not None:
        value["detail"] = detail
    return value


def registry_entries():
    links = [(identifier, f"Sample.Links.{index}") for index, identifier in
             enumerate(sorted({i for ids in reports.REQUIRED_LINKS.values() for i in ids}))]
    entries = [{"identifier": identifier, "category": "trusted-link", "schema": schema, "statement": identifier}
               for identifier, schema in links]
    entries += [{"identifier": "sample.acceptance", "category": "trusted-link", "schema": SCHEMA,
                 "statement": "acceptance inclusion"},
                {"identifier": "sample.model", "category": "model", "schema": "Sample.Model.oracle",
                 "statement": "an oracle model"},
                {"identifier": "sample.budget", "category": "budget", "schema": "Sample.Budget.bound",
                 "statement": "a query bound"}]
    return entries


def records(*, endpoint_axioms=("propext",), instance_premises=None, extra=()):
    endpoint_detail = {"statement": "∀ e, bound", "premises": ["Evidence", "budget"],
                       "premise_telescope": [{"binder": "explicit", "premise": False},
                                             {"binder": "explicit", "premise": True, "head": "Sample.Budget.bound"}],
                       "registered": ["Sample.Model.oracle"]}
    premises = instance_premises if instance_premises is not None else [
        {"binder": "explicit", "premise": False},
        {"binder": "explicit", "premise": True, "head": SCHEMA}]
    instance_detail = {"statement": "Evidence art endpoint prop relation regime",
                       "premises": ["runtime", "AcceptanceInclusion runtime host"] + ["extra"] * 4,
                       "premise_telescope": premises, "registered": []}
    declarations = [record(THEOREM, axioms=endpoint_axioms, detail=endpoint_detail),
                    record(INSTANCE, kind="definition", detail=instance_detail)] + list(extra)
    header = {"format": "zkc.declarations/0", "toolchain": "sample", "registry": registry_entries(),
              "endpoints": [{"endpoint": "executable-bytes", "property": PROPERTY, "statement": "fixed",
                             "theorem": THEOREM}]}
    return Records({"sample": header}, declarations)


def subject(directory, *, endpoint="executable-bytes", recorded=None, evidence_digest=None,
            checks=(("construction", "accepted"),), evidence=True):
    """A manifest, one generated module and the pipeline's evidence."""
    directory = Path(directory)
    digest = "a" * 64
    module = directory / "SampleData.lean"
    module.write_text(f'def snapshot : String := "x"\n  source := "sha256:{recorded or digest}"\n')
    manifest = directory / "sample.toml"
    manifest.write_text(
        'schema = "zkc.subject/0"\nname = "sample"\n[entries]\nproof = "example::Proof"\n'
        f'[generated]\ndata = "{module}"\n[family]\ninstance = "{INSTANCE}"\nkind = "certificate"\n'
        f'[claims]\nendpoint = "{endpoint}"\nproperties = ["{PROPERTY}"]\nstatement = "fixed"\n'
        'regime = "exact"\nunknown_future_field = 1\n[assumptions]\nrequested = ["sample.acceptance"]\n')
    folder = directory / "evidence"
    folder.mkdir(exist_ok=True)
    if evidence:
        (folder / "sample.json").write_text(json.dumps({
            "format": reports.EVIDENCE_FORMAT, "subject": "sample",
            "manifest_sha256": hashlib.sha256(manifest.read_bytes()).hexdigest(),
            "artifacts": {"source": f"sha256:{evidence_digest or digest}"},
            "generated": {str(module): {"sha256": hashlib.sha256(module.read_bytes()).hexdigest()}},
            "checks": [{"name": name, "outcome": outcome} for name, outcome in checks]}))
    return manifest, folder


def report(directory, data, **options):
    manifest, folder = subject(directory, **options)
    return reports.build(manifest, data, evidence_directory=folder)


def mentions(report_value, text):
    return any(text in reason for item in report_value["claims"] for reason in item["reasons"]) or \
        any(text in reason for reason in report_value["reasons"])


def run():
    rows = []

    def expect(name, condition, detail=""):
        if not condition:
            raise AssertionError(f"records control {name} failed {detail}")
        rows.append(name)

    with tempfile.TemporaryDirectory(prefix="zkc-records-controls-") as temporary:
        base = Path(temporary)

        def fresh(name):
            path = base / name
            path.mkdir()
            return path

        accepted = report(fresh("accepted"), records())
        expect("report-established", accepted["outcome"] == "established", accepted)
        identifiers = {row["id"] for row in accepted["claims"][0]["assumptions"]}
        expect("report-lists-assumptions", {"sample.acceptance", "sample.budget"} <= identifiers and
               set(reports.REQUIRED_LINKS["executable-bytes"]) <= identifiers, identifiers)
        expect("report-records-models", [m["id"] for m in accepted["claims"][0]["models"]] == ["sample.model"])
        omitted = report(fresh("omitted"), records(instance_premises=[
            {"binder": "explicit", "premise": True, "head": SCHEMA},
            {"binder": "instance", "premise": True, "head": "Sample.Unregistered"}]))
        expect("report-omitted-premise", omitted["outcome"] == "unresolved" and
               mentions(omitted, "omitted premise: instance premise"), omitted)
        mismatched = report(fresh("mismatched"), records(), evidence_digest="b" * 64)
        expect("report-mismatched-artifact", mismatched["outcome"] == "unresolved" and
               mentions(mismatched, "mismatched artifact") and
               mismatched["artifacts"]["connected"]["status"] == "mismatched", mismatched)
        unsupported = report(fresh("unsupported"), records(), endpoint="interactive-model")
        expect("report-unsupported-endpoint", unsupported["outcome"] == "unresolved" and
               mentions(unsupported, "unsupported endpoint claim"), unsupported)
        unregistered = copy.deepcopy(records())
        unregistered.headers["sample"]["endpoints"] = []
        unregistered_report = report(fresh("unregistered"), unregistered)
        expect("report-unregistered-endpoint", unregistered_report["outcome"] == "unresolved" and
               mentions(unregistered_report, "no registered endpoint"), unregistered_report)
        sorry = report(fresh("sorry"), records(endpoint_axioms=("propext", "sorryAx")))
        expect("report-sorry-unresolved", sorry["outcome"] == "unresolved" and mentions(sorry, "sorryAx"))
        absent = report(fresh("absent"), records(), evidence=False)
        expect("report-without-evidence", absent["outcome"] == "unresolved" and
               mentions(absent, "no pipeline evidence"))
        refused = report(fresh("refused"), records(), checks=(("construction", "refused"),))
        expect("report-refused", refused["outcome"] == "refused")

    # The ledger: a renamed headline, a changed statement and a theorem that
    # depends on sorryAx each fail; the unchanged ledger passes.
    claims = {"schema": ledger.LEDGER_SCHEMA, "proved": [
        {"subject": "Sample", "result": "A result", "owners": [["Spec", "docs/spec.md"]],
         "theorems": ["Sample.headline"]}]}
    current = Records({"sample": {"format": "zkc.declarations/0"}}, [record("Sample.headline")])
    lock = ledger.write_lock(claims, {}, current)
    findings, _, _ = ledger.check(claims, lock, current)
    expect("ledger-current", findings == [], findings)
    renamed = Records({"sample": {"format": "zkc.declarations/0"}}, [record("Sample.headline_renamed")])
    findings, _, _ = ledger.check(claims, lock, renamed)
    expect("ledger-renamed-headline", any(f.startswith("stale theorem name") for f in findings), findings)
    changed = Records({"sample": {}}, [record("Sample.headline", hashes=("1", "3"))])
    findings, _, _ = ledger.check(claims, lock, changed)
    expect("ledger-changed-statement", any(f.startswith("statement changed") for f in findings), findings)
    sorry = Records({"sample": {}}, [record("Sample.headline", axioms=("sorryAx",))])
    findings, _, _ = ledger.check(claims, lock, sorry)
    expect("ledger-sorry-unresolved", any(f.startswith("unresolved") for f in findings), findings)
    table = ledger.render_proved(claims)
    document = f"text\n{ledger.begin('what-is-proved')}\n{table}{ledger.end('what-is-proved')}\n"
    expect("region-current", ledger.region(document, "what-is-proved") == table)
    stale = document.replace("A result", "An older result")
    expect("region-stale", ledger.region(stale, "what-is-proved") != table)
    return rows
