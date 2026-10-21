"""Negative controls for the ledger check and the report generator.

Each control builds a small synthetic input, changes one thing, and requires
the documented reaction: a stale or changed headline, or a stale name cited in
a document, fails the check,
a theorem that depends on `sorryAx` is unresolved, and an omitted premise, a
mismatched artifact or an unsupported endpoint claim make a report
`unresolved`, as do an application of the endpoint to valid evidence of another
subject, an application stated at other artifacts or another relation, an
application of another theorem, a named hypothesis whose claim is not an
instance of its entry's schema, a parameter of the evidence that is neither
a type, an allowed instance nor a registered premise, a premise of the
application itself, a manifest field that names a declaration outside the
claims namespace, a claims namespace of another subject, an application declared
outside the subject's generated claims module, evidence without the
pipeline's claim-application check, and declaration records reused from a saved
directory. `run_emitted` applies the same application audit to declarations Lean
emitted (`TestsSecurity.ReportControls`). A control that would pass
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
NAMESPACE = "Sample.Examples"
APPLICATION = "Sample.Examples.fixed_soundness_bytes"
INSTANCE = "Sample.Examples.evidence"
ARTIFACTS = "Sample.Examples.artifacts"
CONTRACT = "Sample.Examples.Contract.falseStatement"
REGIME = "ZkcSecurity.Endpoint.Regime.exact"
SCHEMA = "Sample.Links.AcceptanceInclusion"
TYPES = [{"binder": "implicit", "premise": False, "type_head": "sort"},
         {"binder": "instance", "premise": False, "type_head": "Field", "model_instance": True}]


def arguments(*names):
    return [{"head": name, "text": name} for name in names]


def record(name, *, kind="theorem", axioms=("propext",), premises=(), detail=None, hashes=("1", "2"),
           module=None):
    value = {"name": name, "module": module or name.rsplit(".", 1)[0], "kind": kind,
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
            instance=None, hypotheses=None, module=f"{NAMESPACE}.Claims"):
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
                    record(APPLICATION, detail=application_detail, module=module),
                    record(INSTANCE, kind="definition", detail=instance_detail, module=module)] + list(extra)
    header = {"format": "zkc.declarations/0", "toolchain": "sample", "registry": registry_entries(),
              "endpoints": [{"endpoint": "executable-bytes", "property": PROPERTY, "statement": "fixed",
                             "theorem": THEOREM}]}
    return Records({"sample": header}, declarations)


def subject(directory, *, endpoint="executable-bytes", recorded=None, evidence_digest=None,
            checks=(("construction", "accepted"),), evidence=True, namespace=NAMESPACE, overrides="",
            claim_application=True):
    """A manifest, its generated data, artifacts and claims modules, and the
    pipeline's evidence. The generated claims modules lie at the path of the
    `Sample.Examples` namespace; `namespace` is what the manifest names."""
    directory = Path(directory)
    digest = "a" * 64
    module = directory / "SampleData.lean"
    module.write_text(f'def snapshot : String := "x"\n  source := "sha256:{recorded or digest}"\n')
    folder_path = directory.joinpath(*NAMESPACE.split("."))
    folder_path.mkdir(parents=True, exist_ok=True)
    artifacts_module, claims_module = folder_path / "Artifacts.lean", folder_path / "Claims.lean"
    artifacts_module.write_text("def artifacts : Nat := 0\n")
    claims_module.write_text("theorem fixed_soundness_bytes : True := trivial\n")
    manifest = directory / "sample.toml"
    manifest.write_text(
        'schema = "zkc.subject/0"\nname = "sample"\n[entries]\nproof = "example::Proof"\n'
        f'[generated]\ndata = "{module}"\nartifacts = "{artifacts_module}"\nclaims = "{claims_module}"\n'
        '[family]\nkind = "certificate"\n'
        f'[claims]\nnamespace = "{namespace}"\nendpoint = "{endpoint}"\nproperties = ["{PROPERTY}"]\n'
        f'statement = "fixed"\nregime = "exact-uniform challenges"\n{overrides}unknown_future_field = 1\n'
        '[assumptions]\nrequested = ["sample.acceptance"]\n')
    folder = directory / "evidence"
    folder.mkdir(exist_ok=True)
    if evidence:
        rows = [{"name": name, "outcome": outcome} for name, outcome in checks]
        if claim_application:
            rows.append({"name": "claim-application", "outcome": "accepted", "module": f"{NAMESPACE}.Claims",
                         "application": APPLICATION})
        (folder / "sample.json").write_text(json.dumps({
            "format": reports.EVIDENCE_FORMAT, "subject": "sample",
            "manifest_sha256": hashlib.sha256(manifest.read_bytes()).hexdigest(),
            "artifacts": {"source": f"sha256:{evidence_digest or digest}"},
            "generated": {str(path): {"sha256": hashlib.sha256(path.read_bytes()).hexdigest()}
                          for path in (module, artifacts_module, claims_module)},
            "checks": rows}))
    return manifest, folder


def report(directory, data, **options):
    manifest, folder = subject(directory, **options)
    return reports.endpoint_audit_report(manifest, data, evidence_directory=folder)


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
        assumed = report(fresh("application-premise"), records(application={
            "premises": ["F", "Field F", "h : False"],
            "premise_telescope": [{"binder": "implicit", "premise": False},
                                  {"binder": "instance", "premise": False},
                                  {"binder": "explicit", "premise": True, "head": "False"}],
            "binders": TYPES + [{"binder": "explicit", "premise": True, "type_head": "False"}]}))
        expect("report-application-premise", assumed["outcome"] == "unresolved" and
               mentions(assumed, "omitted premise: explicit premise h : False of application"), assumed)
        overridden = report(fresh("override"), records(), overrides='application = "Sample.Other.claim"\n')
        expect("report-conflicting-override", overridden["outcome"] == "unresolved" and
               mentions(overridden, "conflicting override: claims.application"), overridden)
        # Another subject's application, evidence, artifacts and contract, each
        # consistent with the others and kernel-checked, named through the claims
        # namespace of a manifest whose own generated modules are this subject's.
        other = "Sample.Other"
        renamed = {APPLICATION: f"{other}.fixed_soundness_bytes", INSTANCE: f"{other}.evidence",
                   ARTIFACTS: f"{other}.artifacts", CONTRACT: f"{other}.Contract.falseStatement"}
        substituted_records = records(module=f"{other}.Claims", application={
            "type_arguments": arguments(renamed[ARTIFACTS], renamed[CONTRACT], REGIME, renamed[INSTANCE]),
            "value_arguments": arguments(renamed[INSTANCE])}, instance={
            "type_arguments": arguments(renamed[ARTIFACTS], renamed[CONTRACT], REGIME)})
        for declaration in substituted_records.declarations:
            declaration["name"] = renamed.get(declaration["name"], declaration["name"])
        substituted_records = Records(substituted_records.headers, substituted_records.declarations)
        crossed = report(fresh("cross-subject"), substituted_records, namespace=other)
        expect("report-cross-subject-substitution", crossed["outcome"] == "unresolved" and
               mentions(crossed, "mismatched artifact: the manifest's generated claims module") and
               mentions(crossed, "no accepted claim-application check"), crossed)
        elsewhere = report(fresh("elsewhere"), records(module="Sample.Elsewhere"))
        expect("report-application-elsewhere", elsewhere["outcome"] == "unresolved" and
               mentions(elsewhere, "is declared in Sample.Elsewhere"), elsewhere)
        manifest, folder = subject(fresh("reused"))
        reused = reports.endpoint_audit_report(manifest, records(), evidence_directory=folder, reused_records="saved-records")
        row = reports.render_subjects([reused]).splitlines()[-1]
        expect("report-reused-records", reused["outcome"] == "unresolved" and reused["claims"] and
               all(item["outcome"] == "unresolved" and
                   any("the declaration records were reused" in reason for reason in item["reasons"])
                   for item in reused["claims"]) and
               "unresolved: the declaration records were reused" in row and "established" not in row,
               reused)
        unbuilt = report(fresh("unbuilt"), records(), claim_application=False)
        expect("report-without-claim-application", unbuilt["outcome"] == "unresolved" and
               mentions(unbuilt, "no accepted claim-application check"), unbuilt)

    run_ledger_controls(rows, expect)

    return rows


# Applications in `TestsSecurity.ReportControls`: the registered knowledge
# endpoint applied to the Schnorr subject's evidence, with no premise of its own
# or with one premise the registry does not know, and the binder of that premise.
EMITTED_APPLICATIONS = {
    "TestsSecurity.ReportControls.clean": None,
    "TestsSecurity.ReportControls.explicit_false": "explicit",
    "TestsSecurity.ReportControls.implicit_false": "implicit",
    "TestsSecurity.ReportControls.instance_premise": "instance",
}

# Real evidence records, so binder-dependence classification is tested through
# the Lean emitter rather than through synthetic JSON alone.
EMITTED_HYPOTHESES = {
    "TestsSecurity.ReportControls.proved_binding": "proof",
    "TestsSecurity.ReportControls.assumed_binding": "premise",
    "TestsSecurity.ReportControls.unused_assumption_binding": "proof",
    "TestsSecurity.ReportControls.fact_binding": "premise",
    "TestsSecurity.ReportControls.inhabited_false_binding": "premise",
    "TestsSecurity.ReportControls.inhabited_proof_binding": "premise",
    "TestsSecurity.ReportControls.lifted_proof_binding": "premise",
}


def run_emitted(data):
    """The report's audit of an application's own telescope, on declarations Lean
    emitted: the application without a premise passes, and each added premise is
    reported as omitted with its binder."""
    entries, endpoints = data.registry()
    registry = reports.Registry(entries, endpoints)
    rows, failures = [], []
    for name, binder in EMITTED_APPLICATIONS.items():
        record = data.get(name)
        if record is None or not record.get("detail"):
            failures.append(f"records control emitted-{name} failed: the declaration was not emitted in detail")
            continue
        _, reasons = reports.telescope(record, registry, "application")
        reasons += reports.binder_reasons(record, "application")
        if binder is None:
            passed = reasons == []
        else:
            passed = any(reason.startswith(f"omitted premise: {binder} premise") for reason in reasons)
        label = "emitted-" + name.rsplit(".", 1)[1].replace("_", "-")
        if passed:
            rows.append(label)
        else:
            failures.append(f"records control {label} failed: {reasons}")
    for name, expected in EMITTED_HYPOTHESES.items():
        record = data.get(name)
        hypotheses = (record or {}).get("detail", {}).get("hypotheses")
        actual = [item.get("status", {}).get("kind") for item in hypotheses or []]
        label = "emitted-" + name.rsplit(".", 1)[1].replace("_", "-")
        if actual == [expected]:
            rows.append(label)
        else:
            failures.append(f"records control {label} failed: expected {[expected]}, got {actual}")
    # Exercise the downstream report too: a status-string control alone cannot
    # show that a proof-carrying instance is refused as an unregistered context.
    for short in ("inhabited_false_binding", "inhabited_proof_binding", "lifted_proof_binding"):
        name = "TestsSecurity.ReportControls." + short
        record = data.get(name)
        reasons = reports.binder_reasons(record or {}, "evidence")
        if not any(reason.startswith("hidden parameter:") for reason in reasons):
            failures.append(f"records control hidden-{short} failed: {reasons}")
        else:
            rows.append("hidden-" + short)
    return rows, failures


def run_ledger_controls(rows, expect):
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


EMITTED_RECEIPTS = {
    "Tests.ClaimReporting.clean": None,
    "Tests.ClaimReporting.explicitFalse": "omitted premise",
    "Tests.ClaimReporting.implicitFalse": "omitted premise",
    "Tests.ClaimReporting.inhabitedFalse": "hidden parameter",
    "Tests.ClaimReporting.liftedFalse": "hidden parameter",
    "Tests.ClaimReporting.forgedDischarger": "forged discharger",
    "Tests.ClaimReporting.forgedDependency": "forged dependency",
    "Tests.ClaimReporting.forgedRoute": "forged route",
    "Tests.ClaimReporting.omittedLink": "unproved registered obligation",
    "Tests.ClaimReporting.provedLink": None,
    "Tests.ClaimReporting.wrongType": "proof type mismatch",
}

EMITTED_STAGE_RECEIPTS = {
    "ProjectedCarrier.directReceipt": ("manualData", "unregistered.projected.carrier"),
    "ProjectedCarrier.carrierReceipt": ("manualData", "unregistered.projected.carrier"),
    "ProjectedCarrier.opaqueReceipt": ("manualData", "unregistered.projected.carrier"),
    "ProjectedCarrier.positiveReceipt": ("manualData", None),
    "ProjectedCarrier.blockedReceipt": ("manualData", "unresolved Evidence-bearing projected function"),
    "HigherOrder.directReceipt": ("idealData", "unregistered.higherorder.control"),
    "HigherOrder.wrappedReceipt": ("idealData", "unregistered.higherorder.control"),
    "HigherOrder.positiveReceipt": ("idealData", None),
    "manualReceipt": ("manualData", None),
    "appliedEvidenceReceipt": ("idealData", None),
    "manualBareReceipt": ("manualData", "missing typed security model admission"),
    "wrongTargetReceipt": ("wrongTargetData", "Subject.check did not admit"),
    "wrongAcceptanceReceipt": ("wrongAcceptanceData", "Subject.check did not admit"),
    "undefinedModelReceipt": ("undefinedModelData", "model resolution is registered-undefined"),
    "malformedModelReceipt": ("malformedModelData", "model resolution is refused"),
    "wrongModelVersionReceipt": ("wrongModelVersionData", "model resolution is refused"),
    "idealReceipt": ("idealData", None),
    "bytesReceipt": ("bytesData", None),
    "extendedReceipt": ("idealData", None),
    "bothExtendedReceipt": ("idealData", None),
    "replacedReceipt": ("idealData", "unrecognized property/model registry"),
    "replacedModelReceipt": ("idealData", "unrecognized property/model registry"),
    "chargedExtensionReceipt": ("chargedExtensionData", "no recognized checked consumer"),
    "parameterReceipt": ("applicationData", None),
    "prefixReceipt": ("applicationData", "application coverage"),
    "constantReceipt": ("applicationData", "application coverage"),
    "unrelatedReceipt": ("applicationData", "application coverage"),
    "fixedReceipt": ("applicationData", None),
    "falselyFixedReceipt": ("applicationData", "application coverage"),
    "omittedReceipt": ("idealData", "missing required interpreted-stage link"),
    "bytesOmittedReceipt": ("bytesData", "missing required interpreted-stage link"),
    "trueReceipt": ("extensionIdealData", "wrong actual subject or goal"),
    "foreignReceipt": ("extensionIdealData", "wrong actual subject or goal"),
    "otherArtifactsReceipt": ("extensionIdealData", "wrong actual subject or goal"),
    "nativeSchemaReceipt": ("extensionIdealData", "wrong actual subject or goal"),
    "constructionOnlyReceipt": ("extensionBytesData", "missing required interpreted-stage link"),
    "conditionalReceipt": ("idealData", "unproved registered obligation"),
    "explicitFalse": ("idealData", "omitted premise"),
    "implicitFalse": ("idealData", "omitted premise"),
    "factFalse": ("idealData", "omitted premise"),
    "inhabitedFalse": ("idealData", "hidden parameter"),
    "liftedFalse": ("idealData", "hidden parameter"),
}


def run_emitted_stage_receipts(data):
    """Actual admitted interpreted endpoints must pass before refusals count."""
    registry = reports.Registry(*data.registry())
    rows, failures = [], []
    for short, (request_short, diagnostic) in EMITTED_STAGE_RECEIPTS.items():
        name = "TestsSecurity.ClaimReporting." + short
        record = data.get(name)
        request = data.get("TestsSecurity.ClaimReporting." + request_short)
        wire = (((request or {}).get("detail") or {}).get("claim_data") or {}).get("wire_request")
        if not record or not wire:
            failures.append(f"interpreted receipt control {name}: missing fresh request/receipt extraction")
            continue
        _, _, _, reasons = reports.audit_receipt(record, request, wire, registry, data, [])
        passed = not reasons if diagnostic is None else any(diagnostic in reason for reason in reasons)
        extracted = ((record.get("detail") or {}).get("claim_data") or {}).get("receipt") or {}
        if short in {"manualReceipt", "appliedEvidenceReceipt"}:
            admission = extracted.get("admission") or {}
            passed = passed and admission.get("association") == "typed-certificate" and admission.get("model_status") == "admitted" and admission.get("certificate_checked") is True
        if short == "appliedEvidenceReceipt":
            evidence = extracted.get("evidence_audit") or {}
            passed = passed and evidence.get("checked") is True and bool(evidence.get("applications"))
        if short.startswith("HigherOrder."):
            evidence = extracted.get("evidence_audit") or {}
            applications = evidence.get("applications") or []
            passed = passed and evidence.get("checked") is True and bool(applications)
            if diagnostic:
                passed = passed and any(hypothesis.get("identifier") == diagnostic
                    for application in applications for hypothesis in application.get("hypotheses") or [])
            if short == "HigherOrder.wrappedReceipt":
                names = {row.get("name") for row in extracted.get("proof_dependencies") or []}
                passed = passed and {"TestsSecurity.ClaimReporting.HigherOrder.invoke",
                    "TestsSecurity.ClaimReporting.HigherOrder.labeledEvidence"} <= names
        if short.startswith("ProjectedCarrier.") and short != "ProjectedCarrier.blockedReceipt":
            admission = extracted.get("admission") or {}
            evidence = extracted.get("evidence_audit") or {}
            applications = evidence.get("applications") or []
            passed = passed and admission.get("certificate_checked") is True and admission.get("model_status") == "admitted"
            passed = passed and evidence.get("checked") is True and bool(applications)
            if diagnostic:
                passed = passed and any(hypothesis.get("identifier") == diagnostic
                    for application in applications for hypothesis in application.get("hypotheses") or [])
            names = {row.get("name") for row in extracted.get("proof_dependencies") or []}
            namespace = "TestsSecurity.ClaimReporting.ProjectedCarrier."
            expected = {namespace + ("validCallback" if diagnostic is None else "callback")}
            if short != "ProjectedCarrier.directReceipt":
                expected.add(namespace + "runner")
            if short == "ProjectedCarrier.opaqueReceipt":
                expected.add(namespace + "hiddenRunner")
            if diagnostic:
                expected.add("TestsSecurity.ClaimReporting.HigherOrder.labeledEvidence")
            passed = passed and expected <= names
        if short == "ProjectedCarrier.blockedReceipt":
            claim_data = (record.get("detail") or {}).get("claim_data") or {}
            passed = passed and "unresolved Evidence-bearing projected function" in claim_data.get("extraction_error", "")
        if short in {"wrongTargetReceipt", "wrongAcceptanceReceipt"}:
            passed = passed and (extracted.get("admission") or {}).get("subject_checked") is False
        if short == "chargedExtensionReceipt":
            passed = passed and extracted.get("quantity_kind") == "charged" and not extracted.get("exported_capabilities")
        if short == "parameterReceipt":
            coverage = extracted.get("application_coverage") or {}
            passed = passed and coverage.get("value_is_binder") is True and coverage.get("designated_binder", {}).get("name") == "application"
        if short == "fixedReceipt":
            coverage = extracted.get("application_coverage") or {}
            passed = passed and coverage.get("mode") == "fixed" and coverage.get("fixed_value") == "deployment-a"
        if passed:
            rows.append("emitted-interpreted-" + short)
        else:
            failures.append(f"interpreted receipt control {name}: {reasons}")
    return rows, failures


def run_emitted_receipts(data):
    """Exercise the downstream reader on kernel-emitted request/receipt values."""
    entries, endpoints = data.registry()
    registry = reports.Registry(entries, endpoints)
    request = data.get("Tests.ClaimReporting.request0Data")
    wire = ((request or {}).get("detail", {}).get("claim_data") or {}).get("wire_request")
    rows, failures = [], []
    if not wire:
        return [], ["receipt controls: actual Wire.Request was not emitted"]
    imported = ((data.get("Tests.ClaimReporting.importedData") or {}).get("detail", {}).get("claim_data") or {})
    expected_target = {"protocol": "test", "language": {"kind": "application",
        "name": "languages.reporting_control", "version": 3,
        "arguments": [{"label": "parameter", "value": {"kind": "natural", "value": "7"}}]}}
    if (imported.get("wire_request") or {}).get("target") == expected_target:
        rows.append("emitted-request-imported-language")
    else:
        failures.append("receipt controls: imported-language protocol/application was not preserved")
    for name, diagnostic in EMITTED_RECEIPTS.items():
        record = data.get(name)
        if record is None:
            failures.append(f"receipt control {name} was not emitted")
            continue
        _, _, _, reasons = reports.audit_receipt(record, request, wire, registry, data)
        passed = not reasons if diagnostic is None else any(diagnostic in reason for reason in reasons)
        label = "emitted-receipt-" + name.rsplit(".", 1)[1]
        if passed:
            rows.append(label)
        else:
            failures.append(f"receipt control {label} failed: {reasons}")
    if "security" in data.packages():
        stage_rows, stage_failures = run_emitted_stage_receipts(data)
        rows += stage_rows
        failures += stage_failures
    return rows, failures
