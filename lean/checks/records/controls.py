"""Negative controls for the ledger check and the report generator.

Each control builds a small synthetic input, changes one thing, and requires
the documented reaction: a stale or changed headline, or a stale name cited in
a document, fails the check,
a theorem that depends on `sorryAx` is unresolved, and an omitted premise, a
mismatched artifact or an unsupported endpoint claim make a report
`unresolved`, as do an application of the endpoint to valid evidence of another
subject, an application stated at other artifacts or another relation, an
application of another theorem, a named hypothesis whose claim is not an
instance of its entry's schema, and a parameter of the evidence that is neither
a type, an allowed instance nor a registered premise. A control that would pass
on the unchanged input is checked on that input too, so a control cannot pass
vacuously.
"""

import copy
import hashlib
import json
from pathlib import Path
import tempfile

from . import ledger, reports
from .declarations import Records

PROPERTY = "soundness"
EVIDENCE = "ZkcSecurity.Endpoint.SoundnessEvidence"
THEOREM = "Sample.Endpoint.soundness"
CLAIM = "Sample.Endpoint.Soundness"
APPLICATION = "Sample.Examples.claim"
INSTANCE = "Sample.Examples.evidence"
ARTIFACTS = "Sample.Examples.artifacts"
CONTRACT = "Sample.Examples.Contract.falseStatement"
REGIME = "ZkcSecurity.Endpoint.Regime.exact"
SCHEMA = "Sample.Links.AcceptanceInclusion"
TYPES = [{"binder": "implicit", "premise": False, "type_head": "sort"},
         {"binder": "instance", "premise": False, "type_head": "Field"}]


def arguments(*names):
    return [{"head": name, "text": name} for name in names]


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


def records(*, endpoint_axioms=("propext",), instance_premises=None, extra=(), application=None,
            instance=None, hypotheses=None):
    """The registered endpoint, the subject's application and its evidence.
    `application` and `instance` override fields of their details."""
    endpoint_detail = {"statement": "∀ e, Sample.Endpoint.Soundness e", "premises": ["Evidence"],
                       "premise_telescope": [{"binder": "explicit", "premise": False}],
                       "binders": [{"binder": "explicit", "premise": False, "type_head": EVIDENCE}],
                       "type_head": CLAIM, "type_arguments": arguments(None), "value_head": None,
                       "registered": ["Sample.Model.oracle"]}
    application_detail = {"statement": f"{CLAIM} {INSTANCE}", "premises": ["F", "Field F"],
                          "premise_telescope": [{"binder": "implicit", "premise": False},
                                                {"binder": "instance", "premise": False}],
                          "binders": TYPES, "type_head": CLAIM,
                          "type_arguments": arguments(ARTIFACTS, CONTRACT, REGIME, INSTANCE),
                          "value_head": THEOREM, "value_arguments": arguments(INSTANCE),
                          "property": {"statement": "∀ prover cost, bound prover cost → Pr ≤ cost",
                                       "premise_telescope": [
                                           {"binder": "explicit", "premise": False},
                                           {"binder": "explicit", "premise": True, "head": "Sample.Budget.bound"}]},
                          "registered": []}
    application_detail.update(application or {})
    premises = instance_premises if instance_premises is not None else [
        {"binder": "implicit", "premise": False},
        {"binder": "explicit", "premise": True, "head": SCHEMA}]
    instance_detail = {"statement": f"{EVIDENCE} {ARTIFACTS} {CONTRACT} {REGIME}",
                       "premises": ["F", "AcceptanceInclusion runtime host"] + ["extra"] * 4,
                       "premise_telescope": premises,
                       "binders": [TYPES[0]] + [dict(binder, type_head=binder.get("head"))
                                                for binder in premises[1:]],
                       "type_head": EVIDENCE, "type_arguments": arguments(ARTIFACTS, CONTRACT, REGIME),
                       "value_head": "Sample.Examples.soundness", "value_arguments": arguments(None),
                       "hypotheses": hypotheses if hypotheses is not None else [
                           {"identifier": "sample.acceptance", "category": "trusted-link", "claim_head": SCHEMA,
                            "claim_head_reducible": SCHEMA, "claim_arguments": arguments(None),
                            "claim": "AcceptanceInclusion runtime host", "status": {"kind": "premise"}}],
                       "registered": []}
    instance_detail.update(instance or {})
    declarations = [record(THEOREM, axioms=endpoint_axioms, detail=endpoint_detail),
                    record(APPLICATION, detail=application_detail),
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
        f'regime = "exact-uniform challenges"\napplication = "{APPLICATION}"\nartifacts = "{ARTIFACTS}"\n'
        f'contract = "{CONTRACT}"\nunknown_future_field = 1\n[assumptions]\nrequested = ["sample.acceptance"]\n')
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
        expect("report-renders-bound", accepted["claims"][0]["bound"]["property"] ==
               "∀ prover cost, bound prover cost → Pr ≤ cost", accepted["claims"][0]["bound"])
        other = report(fresh("wrong-evidence"), records(application={
            "type_arguments": arguments(ARTIFACTS, CONTRACT, REGIME, "Sample.Other.evidence"),
            "value_arguments": arguments("Sample.Other.evidence")}))
        expect("report-wrong-evidence", other["outcome"] == "unresolved" and mentions(other, "wrong evidence"),
               other)
        moved = report(fresh("wrong-artifacts"), records(application={
            "type_arguments": arguments("Sample.Other.artifacts", CONTRACT, REGIME, INSTANCE)}))
        expect("report-wrong-artifacts", moved["outcome"] == "unresolved" and
               mentions(moved, "mismatched artifact: application"), moved)
        substituted = report(fresh("substituted"), records(application={
            "type_arguments": arguments(ARTIFACTS, "Sample.Examples.Contract.never", REGIME, INSTANCE)}))
        expect("report-substituted-relation", substituted["outcome"] == "unresolved" and
               mentions(substituted, "substituted relation"), substituted)
        retargeted = report(fresh("wrong-endpoint"), records(application={"value_head": "Sample.Other.theorem"}))
        expect("report-wrong-endpoint", retargeted["outcome"] == "unresolved" and
               mentions(retargeted, "is not the registered endpoint"), retargeted)
        schema = report(fresh("wrong-schema"), records(hypotheses=[
            {"identifier": "sample.acceptance", "category": "trusted-link", "claim_head": "Sample.Links.0",
             "claim_head_reducible": "Sample.Links.0", "claim_arguments": [], "claim": "another link",
             "status": {"kind": "premise"}}]))
        expect("report-wrong-schema", schema["outcome"] == "unresolved" and mentions(schema, "wrong schema"),
               schema)
        hidden = report(fresh("hidden"), records(instance={"binders": [
            TYPES[0], {"binder": "explicit", "premise": False, "type_head": "Sample.Examples.Assumptions"}]}))
        expect("report-hidden-assumption", hidden["outcome"] == "unresolved" and
               mentions(hidden, "hidden parameter"), hidden)
        unnamed = report(fresh("unnamed"), records(hypotheses=[]))
        expect("report-unnamed-assumption", unnamed["outcome"] == "unresolved" and
               mentions(unnamed, "omitted assumption"), unnamed)

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
    # A qualified name cited in prose must still name a declaration.
    with tempfile.TemporaryDirectory(prefix="zkc-records-documents-") as temporary:
        root = Path(temporary)
        (root / "docs").mkdir()
        (root / "docs/status.md").write_text("Cites `Zkc.Sample.present` and `Zkc.Sample.renamed`.\n")
        cited = Records({"main": {}}, [dict(record("Zkc.Sample.present"), package="main")])
        findings, checked, _ = ledger.check_documents(cited, root)
        expect("document-stale-name", checked == 2 and len(findings) == 1 and "Zkc.Sample.renamed" in findings[0],
               findings)
    return rows
