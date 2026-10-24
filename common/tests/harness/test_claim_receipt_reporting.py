"""Request/receipt joins and Lean-owned assurance reporting controls."""
from copy import deepcopy
import json
from pathlib import Path
import subprocess

import pytest
from harness import load


# Mocked exported metadata for reporter unit tests, not a production policy.
# Lean controls check the real closed authority, telescope and subject links.
EXPORTED_STAGE_LINKS = {
    "interactive": ("fixture.interactive-link",),
    "compiled-ideal": ("construction.checked",),
    "executable-bytes": ("construction.checked", "lowering.interpreted_bytes"),
}


@pytest.fixture(scope="module")
def pure_classifier():
    """Run the actual Lean policy on mock exports, without claiming provenance."""
    root = Path(__file__).resolve().parents[3] / "lean"
    process = subprocess.Popen(["lake", "env", "lean", "--run", "Tests/ReceiptStatus.lean"], cwd=root,
                               stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)

    def invoke(payload, _packages):
        process.stdin.write(json.dumps(payload) + "\n")
        process.stdin.flush()
        line = process.stdout.readline()
        # #print axioms is emitted by the test driver before its JSON loop.
        while line and not line.startswith("{"):
            line = process.stdout.readline()
        assert line, process.stderr.read()
        result = json.loads(line)
        assert "error" not in result, result
        return result

    yield invoke
    process.stdin.close()
    process.wait(timeout=15)
    assert process.returncode == 0, process.stderr.read()


@pytest.fixture
def api(monkeypatch, pure_classifier):
    api = load("receipt_reporting_cli", "lean/checks/check_records.py").reports
    monkeypatch.setattr(api, "_invoke_receipt_classifier", pure_classifier)
    return api


@pytest.fixture
def receipt_case(api):
    declarations = load("receipt_reporting_declarations", "lean/checks/records/declarations.py")
    request = {"subject": {"unit": "sha256:unit", "entry": "demo::Proof", "stage": "interactive", "artifacts": [{"role": "fixture-input", "digest": "sha256:unit"}]},
               "property": {"name": "user.identity", "version": 0, "parameters": None},
               "model": {"kind": "application", "name": "models.identity", "version": 0, "arguments": []},
               "target": {"protocol": "demo", "clause": 0, "name": "identity"},
               "accept": {"output": True, "port": 0, "role": 0, "path": []},
               "quantity": {"kind": "scalar", "expression": {"kind": "natural", "value": "0"}},
               "capabilities": []}
    base = {"module": "ZkcExamples.Request", "kind": "definition", "axioms": [],
            "statement": {"structural": "1", "explicit": "2"}, "tags": []}
    detail = {"binders": [], "premise_telescope": [], "premises": []}
    data = dict(base, name="Demo.request0Data", detail=dict(detail, type_head=api.REQUEST_TYPE,
                claim_data={"wire_request": deepcopy(request), "telescope": {"accepted": True}}))
    proof = {"wire_request": deepcopy(request), "request_head": data["name"], "indices_checked": True,
             "proof_type_matches": True, "root_route": "theorem", "discharger": "True.intro",
             "evidence_attribution": {"scope": "referenced-evidence", "declarations": []},
             "proposition": "True", "dependencies": [{"name": "True.intro", "module": "Init.Prelude", "owned": False}],
             "required_links": [], "registered_property": {"name": "user.identity", "version": 0}, "provenance": {"root": "Zkc.Claims.Route.theorem", "discharger": "True.intro",
                "dependencies": [], "premises": [], "method": {"name": "identity", "version": 0}}}
    receipt = dict(base, name="Demo.request0Receipt", detail=dict(detail, type_head=api.RECEIPT_TYPE,
                   claim_data={"receipt": proof}))
    records = declarations.Records({"main": {"axiom_provenance": "resolved-constant-info/0",
                                            "reference_provenance": "checked-stored-module/0"}}, [data, receipt])
    proof.update(authority={"kind": "author", "checked": True},
                 telescope={"accepted": True, "binders": [], "conditions": []})
    case = (request, data, receipt, proof, records)
    interpreted_stage(api, case, "interactive")
    return case


def audit(api, case):
    request, data, receipt, _, records = case
    return api.audit_receipt(receipt, data, request, api.Registry([], []), records)


def interpreted_stage(api, case, stage):
    request, data, _, proof, _ = case
    for wire in (request, data["detail"]["claim_data"]["wire_request"], proof["wire_request"]):
        wire["subject"]["stage"] = stage
    proof["required_links"] = [{"index": index, "identifier": name, "proved": True, "conditional": False}
                               for index, name in enumerate(EXPORTED_STAGE_LINKS[stage])]
    proof["stage_links"] = {"recognized_subject": True, "stage": stage,
        "covered_endpoint": "ideal-meaning" if stage == "compiled-ideal" else "interpreted-executable-bytes",
        "artifact_roles": [{"role": "fixture-input", "pipeline_artifact": "interactive_export"}],
        "obligations": [{"identifier": name, "matches": [{"index": index, "goal_defeq": True, "subject_matches": True}]}
                        for index, name in enumerate(EXPORTED_STAGE_LINKS[stage])]}


@pytest.mark.parametrize("stage", ["compiled-ideal", "executable-bytes"])
def test_interpreted_stage_links_can_discharge_without_native_closure(api, receipt_case, stage):
    interpreted_stage(api, receipt_case, stage)
    _, _, discharged, reasons = audit(api, receipt_case)
    assert reasons == []
    assert [row["id"] for row in discharged] == list(EXPORTED_STAGE_LINKS[stage])


@pytest.mark.parametrize("comparison", ["goal_defeq", "subject_matches"])
def test_stage_link_needs_actual_goal_and_same_subject(api, receipt_case, comparison):
    interpreted_stage(api, receipt_case, "compiled-ideal")
    receipt_case[3]["stage_links"]["obligations"][0]["matches"][0][comparison] = False
    assert any("wrong actual subject or goal" in reason for reason in audit(api, receipt_case)[3])


@pytest.mark.parametrize("change", ["omitted", "unrecognized", "missing-lowering", "wrong-stage"])
def test_byte_interpretation_requires_both_checked_links(api, receipt_case, change):
    interpreted_stage(api, receipt_case, "executable-bytes")
    proof = receipt_case[3]
    if change == "omitted":
        proof["required_links"].pop()
    elif change == "unrecognized":
        proof["stage_links"]["recognized_subject"] = False
    elif change == "missing-lowering":
        proof["stage_links"]["obligations"][-1]["matches"] = []
    else:
        proof["stage_links"]["stage"] = "compiled-ideal"
    assert audit(api, receipt_case)[3]


def test_receipt_control_has_positive_baseline(api, receipt_case):
    _, assumptions, _, reasons = audit(api, receipt_case)
    assert reasons == []
    assert [row["id"] for row in assumptions] == ["source.correspondence"]


@pytest.mark.parametrize("part,key,value", [
    ("subject", "entry", "other::Proof"), ("subject", "stage", "executable-bytes"),
    ("subject", "unit", "sha256:other"), ("subject", "artifacts", [{"role": "verifier-program", "digest": "other"}]),
    ("property", "version", 9), ("property", "name", "completeness"),
    ("model", "version", 9), ("target", "name", "other"), ("target", "clause", 9),
    ("accept", "role", 9), ("quantity", "expression", {"kind": "natural", "value": "1"}),
])
def test_emitted_request_cannot_be_substituted(api, receipt_case, part, key, value):
    receipt_case[0][part][key] = value
    assert any("wrong request" in reason for reason in audit(api, receipt_case)[3])


@pytest.mark.parametrize("field,value", [
    ("protocol", "other"), ("version", 4),
    ("arguments", [{"label": "parameter", "value": {"kind": "natural", "value": "7"}}]),
])
def test_imported_language_request_is_compared_without_erasure(api, receipt_case, field, value):
    target = {"protocol": "demo", "language": {"kind": "application", "name": "languages.identity",
                                               "version": 0, "arguments": []}}
    request, data, _, proof, _ = receipt_case
    for wire in (request, data["detail"]["claim_data"]["wire_request"], proof["wire_request"]):
        wire["target"] = deepcopy(target)
    assert not audit(api, receipt_case)[3]
    changed = request["target"] if field == "protocol" else request["target"]["language"]
    changed[field] = value
    assert any("wrong request" in reason for reason in audit(api, receipt_case)[3])


@pytest.mark.parametrize("field,value,diagnostic", [
    ("proof_type_matches", False, "proof type mismatch"),
    ("indices_checked", False, "proof type mismatch"),
])
def test_actual_receipt_facts_are_checked(api, receipt_case, field, value, diagnostic):
    receipt_case[3][field] = value
    assert any(diagnostic in reason for reason in audit(api, receipt_case)[3])


def test_unverifiable_provenance_is_unattributed(api, receipt_case):
    receipt_case[3]["provenance"]["dependencies"] = ["False.elim"]
    result, assumptions, _, reasons = audit(api, receipt_case)
    assert reasons == []
    assert result["root_route"] == "unattributed"
    assert [row["id"] for row in assumptions] == ["source.correspondence"]


@pytest.mark.parametrize("binder", [
    {"binder": "explicit", "type_head": "PLift", "premise": False},
    {"binder": "instance", "type_head": "Inhabited", "premise": False, "model_instance": False},
    {"binder": "instance", "type_head": "Inhabited", "premise": False},
    {"binder": "implicit", "type_head": "False", "premise": True},
])
def test_receipt_context_cannot_hide_assumptions(api, receipt_case, binder):
    detail = receipt_case[2]["detail"]
    detail["binders"] = [binder]
    detail["premise_telescope"] = [dict(binder, head=binder["type_head"])]
    receipt_case[3]["telescope"] = {"accepted": False, "binders": [
        {"classification": "refused", "reason": "unauthorized premise",
         "binder": binder["binder"], "type": binder["type_head"]}]}
    assert audit(api, receipt_case)[3]


def test_omitting_required_links_cannot_certify(api, receipt_case):
    for value in (receipt_case[0], receipt_case[1]["detail"]["claim_data"]["wire_request"],
                  receipt_case[3]["wire_request"]):
        value["subject"]["stage"] = "executable-bytes"
    interpreted_stage(api, receipt_case, "executable-bytes")
    receipt_case[3]["required_links"] = []
    reasons = audit(api, receipt_case)[3]
    assert all(any(identifier in reason for reason in reasons) for identifier in EXPORTED_STAGE_LINKS["executable-bytes"])


def test_body_change_invalidates_semantic_digest_with_same_statement(api, tmp_path, monkeypatch):
    source = tmp_path / "Meaning.lean"
    monkeypatch.setattr(api, "ROOT", tmp_path)
    monkeypatch.setattr(api, "owned_module_path", lambda _: source)
    closure = [{"name": "Meaning.predicate", "module": "Meaning", "owned": True, "statement": "same"}]
    source.write_text("def predicate : Prop := True\n")
    before, reasons = api.semantic_dependencies(closure, None, {})
    assert not reasons
    source.write_text("def predicate : Prop := False\n")
    after, reasons = api.semantic_dependencies(closure, None, {})
    assert not reasons
    assert before["declarations"] == after["declarations"]
    assert before["digest"] != after["digest"]


def test_conflicting_registry_schema_is_refused(api):
    first = {"identifier": "first", "schema": "Same", "category": "model", "statement": "First"}
    with pytest.raises(ValueError, match="conflicting registry schema"):
        api.Registry([first, dict(first, identifier="second")], [])


def test_public_report_identity_and_stale_semantic_cache(api, receipt_case, tmp_path, monkeypatch):
    request, data, receipt, proof, records = receipt_case
    generated = tmp_path / "Request.lean"
    generated.write_text("-- generated request and receipt\n")
    meaning = tmp_path / "Meaning.lean"
    meaning.write_text("def predicate : Prop := True\n")
    monkeypatch.setattr(api, "ROOT", tmp_path)
    monkeypatch.setattr(api, "owned_module_path", lambda module: meaning if module == "Meaning" else generated)
    monkeypatch.setattr(api, "verified_environment", lambda *_: ({}, []))
    proof["dependencies"].append({"name": "Meaning.predicate", "module": "Meaning", "owned": True,
                                  "statement": "same theorem type"})
    manifest = tmp_path / "control.toml"
    manifest.write_text('name="control"\n[entries]\nproof="demo::Proof"\n[generated]\nclaims="Request.lean"\n')
    digest = api.data_digest(request)
    node = {"kind": "source-claim", "owner": "Demo", "block": 0, "claim": 0}
    source = {"request": request, "request_digest": digest, "attachment": {"node": node, "label": "before"}}
    mapping = {"node": node, "request_digest": digest,
               "request_declaration": data["name"], "receipt_declaration": receipt["name"]}
    evidence = {"format": api.EVIDENCE_FORMAT, "subject": "control", "manifest_sha256": api.sha256(manifest),
        "source_claim_scope": {"entries": ["demo::Proof"], "selection": "proof-entry"},
        "artifacts": {"interactive_export": request["subject"]["unit"]},
        "generated": {"Request.lean": {"sha256": api.sha256(generated)}},
        "source_claims": {"format": api.BOUND_CLAIMS_FORMAT, "entry": "demo::Proof", "claims": [source]},
        "claim_receipts": [mapping], "checks": [{"name": "claim-receipt", "outcome": "accepted",
            "module": receipt["module"], "request": data["name"], "receipt": receipt["name"]}]}
    monkeypatch.setattr(api, "load_evidence", lambda *_: evidence)
    report = api.build(manifest, records)
    assert report["status"] == "no-claim"
    assert report["author_claims"][0]["outcome"] == "established", report["claims"][0]["reasons"]
    source["attachment"]["label"] = "after"
    source["method"] = {"name": "different", "version": 99}
    assert api.build(manifest, records)["author_claims"][0]["outcome"] == "established"
    mapping["resolution"] = {"status": "incomplete", "kind": "registered-undefined", "definitions": ["missing model"]}
    assert api.build(manifest, records)["claims"][0]["status"] == "open"
    del mapping["resolution"]
    mapping["semantic_dependency_digest"] = report["claims"][0]["semantic_dependencies"]["digest"]
    meaning.write_text("def predicate : Prop := False\n")
    changed = api.build(manifest, records)
    assert changed["claims"][0]["status"] == "open"
    assert any("stale semantic dependency digest" in reason for reason in changed["claims"][0]["reasons"])


def test_legacy_security_controls_still_pass():
    cli = load("receipt_reporting_controls", "lean/checks/check_records.py")
    assert len(cli.controls.run()) >= 31


@pytest.mark.parametrize("detail", [
    {},
    {"hypotheses": None, "hypotheses_error": "unresolved list in declaration data"},
    {"hypotheses": "unreadable", "hypotheses_error": "unresolved list in declaration data"},
])
def test_legacy_unreadable_hypotheses_are_not_empty(api, detail):
    found, discharged, reasons = api.hypotheses({"name": "Demo.withNotes", "detail": detail}, api.Registry([], []))
    assert found == discharged == []
    assert reasons == ["the named hypotheses of Demo.withNotes were not recorded"]


def test_optional_hypotheses_diagnostic_does_not_refuse_receipt(api, receipt_case):
    receipt_case[2]["detail"].update(hypotheses=None, hypotheses_error="unresolved list in declaration data")
    assert audit(api, receipt_case)[3] == []


def test_all_source_claims_survive_incomplete_and_failed_attempts(api, receipt_case, tmp_path, monkeypatch):
    request, _, _, _, records = receipt_case
    manifest = tmp_path / "sample.toml"
    manifest.write_text('name="sample"\n[entries]\nproof="demo::Proof"\n')
    node = {"kind": "source-claim", "owner": "Demo", "block": 0, "claim": 0}
    first = {"request": request, "request_digest": api.data_digest(request), "attachment": {"node": node}}
    second = deepcopy(first)
    second["attachment"]["node"]["claim"] = 1
    second["request"]["subject"]["entry"] = "demo::Interactive"
    second["request_digest"] = api.data_digest(second["request"])
    evidence = {"format": api.EVIDENCE_FORMAT, "subject": "sample", "artifacts": {"interactive_export": "sha256:unit"},
                "source_claim_scope": {"entries": ["demo::Proof", "demo::Interactive"], "selection": "explicit"},
                "checks": [{"name": "source-compilation", "outcome": "accepted"}],
                "source_claims": {"format": api.BOUND_CLAIMS_FORMAT, "entry": "demo::Proof",
                                  "entries": ["demo::Proof", "demo::Interactive"], "claims": [first, second]},
                "claim_receipts": [{"node": node, "request_digest": first["request_digest"],
                    "resolution": {"status": "incomplete", "kind": "registered-undefined", "definitions": ["interactive model"]},
                    "attempts": [{"method": "unknown", "result": "unsupported"}]}]}
    monkeypatch.setattr(api, "load_evidence", lambda *_: evidence)
    monkeypatch.setattr(api, "verified_environment", lambda *_: ({}, []))
    report = api.build(manifest, records)
    assert len(report["claims"]) == 2
    assert [row["status"] for row in report["claims"]] == ["incomplete", "open"]
    assert report["outcome"] == "unresolved"
    assert report["claims"][0]["attempts"][0]["result"] == "unsupported"
    assert "| `demo::Interactive` |" in api.render_subjects([report])
    assert not any("wrong subject" in reason for row in report["claims"] for reason in row["reasons"])
    evidence["source_claims"]["entries"].pop()
    assert any("wrong subject" in reason for reason in api.build(manifest, records)["claims"][1]["reasons"])
    evidence["source_claims"]["claims"] = []
    evidence["claim_receipts"] = []
    report = api.build(manifest, records)
    assert report["status"] == "no-claim"
    assert report["outcome"] != "established"


def test_registry_owned_obligation_is_not_optional(api, receipt_case):
    receipt_case[3]["required_links"] = [{"identifier": "registered.required", "proved": False}]
    assert any("unproved registered obligation" in reason for reason in audit(api, receipt_case)[3])


@pytest.mark.parametrize("quantity,exported,diagnostic", [
    ("charged", [], "missing charged reduction capability"),
    ("scalar", ["capabilities.charged_reduction@0"], "scalar request cannot export"),
])
def test_capability_exports_follow_actual_quantity(api, receipt_case, quantity, exported, diagnostic):
    request, data, _, proof, _ = receipt_case
    for wire in (request, data["detail"]["claim_data"]["wire_request"], proof["wire_request"]):
        wire["property"]["name"] = "soundness"
        wire["quantity"]["kind"] = quantity
    proof.update(registered_property={"name": "soundness", "version": 0}, authority={"kind": "canonical", "checked": True},
                 quantity_kind=quantity, exported_capabilities=exported, capability_consumer="soundness@0",
                 registry_checks={key: True for key in ("lookup", "property_definition", "property_export", "model_export")},
                 application_coverage={"mode": "fixed-statement", "checked": True})
    assert any(diagnostic in reason for reason in audit(api, receipt_case)[3])


@pytest.mark.parametrize("capability", ["capabilities.charged_reduction", "user.capability"])
def test_extension_requires_checked_capability_consumer(api, receipt_case, capability):
    request, data, _, proof, _ = receipt_case
    for wire in (request, data["detail"]["claim_data"]["wire_request"], proof["wire_request"]):
        wire["capabilities"] = [{"name": capability, "version": 0, "arguments": []}]
    proof.update(quantity_kind="charged", exported_capabilities=[capability + "@0"])
    reasons = audit(api, receipt_case)[3]
    assert any("no recognized checked consumer" in reason for reason in reasons)
    assert any("unsupported capability export" in reason for reason in reasons)


@pytest.mark.parametrize("resolution,expected", [
    ({"status": "open", "kind": "normalization-failure", "definitions": ["maximum recursion depth exceeded"]}, "open"),
    ({"status": "refused", "kind": "resolution-refusal", "definitions": ["unknown model version"]}, "open"),
    ({"status": "incomplete", "kind": "normalization-failure", "definitions": ["diagnostic with inconsistent classification"]}, "open"),
    ({"status": "incomplete", "definitions": ["registered property definition"]}, "incomplete"),
    ({"status": "incomplete", "kind": "registered-undefined", "definitions": []}, "open"),
    ({"status": "incomplete", "kind": "registered-undefined", "definitions": ["interactive completeness meaning"]}, "incomplete"),
])
def test_only_structured_registered_undefined_is_incomplete(api, receipt_case, tmp_path, resolution, expected):
    request, _, _, _, records = receipt_case
    item = {"request": request, "request_digest": api.data_digest(request), "attachment": {"node": {"claim": 0}}}
    mapping = {"node": {"claim": 0}, "request_digest": item["request_digest"], "resolution": resolution,
               "attempts": [{"result": "refused"}, {"result": "timeout", "partial": True}]}
    claim = api.requested_claim(item, [mapping], records, api.Registry([], []), [],
        {"source_claims": {"entry": request["subject"]["entry"]}}, {"outcome": "accepted"}, [], {}, [], None)
    assert claim["status"] == expected
    assert claim["resolution"] == resolution
    assert claim["attempts"] == mapping["attempts"]


@pytest.mark.parametrize("authority", [
    {"kind": "reserved", "checked": False},
    {"kind": "canonical", "checked": False},
    {},
])
def test_legacy_registry_flags_cannot_replace_checked_authority(api, receipt_case, authority):
    security_admission(api, receipt_case)
    assert audit(api, receipt_case)[3] == []
    proof = receipt_case[3]
    proof.update(canonical_registry=True, capability_consumer="soundness@0",
                 registry_checks={key: True for key in
                                  ("lookup", "property_definition", "property_export", "model_export")})
    proof["authority"] = authority
    assert any("unrecognized property/model registry" in reason for reason in audit(api, receipt_case)[3])


@pytest.mark.parametrize("comparison", ["checked", "context_matches", "reference_matches", "model_value_matches", "value_is_binder"])
def test_parameter_coverage_requires_all_emitted_comparisons(api, receipt_case, comparison):
    request, data, _, proof, _ = receipt_case
    for wire in (request, data["detail"]["claim_data"]["wire_request"], proof["wire_request"]):
        wire["property"]["name"] = "soundness"
    coverage = {"checked": True, "mode": "parameter", "context_matches": True, "reference_matches": True,
                "model_value_matches": True, "value_is_binder": True, "designated_binder": {"name": "application", "index": 0}}
    coverage[comparison] = False
    proof.update(registered_property={"name": "soundness", "version": 0}, authority={"kind": "canonical", "checked": True},
                 capability_consumer="soundness@0", quantity_kind="scalar",
                 registry_checks={key: True for key in ("lookup", "property_definition", "property_export", "model_export")},
                 application_coverage=coverage)
    assert any("application" in reason and ("coverage" in reason or "designated" in reason)
               for reason in audit(api, receipt_case)[3])


def security_admission(api, case):
    interpreted_stage(api, case, "compiled-ideal")
    case[2]["detail"]["type_head"] = api.ADMITTED_RECEIPT_TYPE
    case[3]["subject"] = {"artifacts_head": "Demo.artifacts"}
    case[3]["admission"] = {"security_subject": True, "associated": True,
        "association": "typed-certificate", "certificate_checked": True,
        "subject_checked": True, "model_status": "admitted"}


def test_manual_extension_admission_has_a_positive_baseline(api, receipt_case):
    security_admission(api, receipt_case)
    assert audit(api, receipt_case)[3] == []


@pytest.mark.parametrize("field,value,diagnostic", [
    ("associated", False, "missing typed security model admission"),
    ("subject_checked", False, "Subject.check did not admit"),
    ("model_status", "registered-undefined", "model resolution is registered-undefined"),
    ("model_status", "refused", "model resolution is refused"),
    ("model_status", "open", "model resolution is open"),
    ("certificate_checked", False, "certificate does not match"),
])
def test_security_admission_requires_actual_checked_facts(api, receipt_case, field, value, diagnostic):
    security_admission(api, receipt_case)
    receipt_case[3]["admission"][field] = value
    assert any(diagnostic in reason for reason in audit(api, receipt_case)[3])


def test_generic_evidence_telescope_is_not_a_receipt_premise(api, receipt_case):
    declarations = load("applied_evidence_declarations", "lean/checks/records/declarations.py")
    generic = {"name": "Demo.genericEvidence", "module": "ZkcSecurity.Examples.Subjects.Demo.Evidence",
        "kind": "definition", "axioms": [], "tags": [], "statement": {"structural": "1", "explicit": "2"}, "detail": {
            "type_head": "ZkcSecurity.Endpoint.KnowledgeEvidence", "binders": [
                {"binder": "explicit", "type_head": "ZkcSecurity.Endpoint.Semantics", "premise": False}],
            "premise_telescope": [{"binder": "explicit", "premise": False}], "hypotheses": []}}
    receipt_case[3]["dependencies"].append({"name": generic["name"], "module": generic["module"], "owned": True})
    receipt_case[3]["evidence_attribution"]["applications"] = [
        {"name": generic["name"], "application": "genericEvidence idealMeaning", "hypotheses": []}]
    records = receipt_case[4]
    case = (*receipt_case[:4], declarations.Records(records.headers, [*records.declarations, generic]))
    assert audit(api, case)[3] == []
    case[2]["detail"]["binders"] = generic["detail"]["binders"]
    case[3]["telescope"] = {"accepted": False, "binders": [
        {"classification": "refused", "reason": "hidden parameter",
         "binder": "explicit", "type": "ZkcSecurity.Endpoint.Semantics"}]}
    assert any("hidden parameter" in reason for reason in audit(api, case)[3])


def test_internal_evidence_notes_are_not_receipt_assumptions(api, receipt_case):
    receipt_case[3]["evidence_attribution"]["applications"] = [{"name": "Demo.actualEvidence", "hypotheses": [
        {"identifier": "unregistered.premise", "claim_head": "True", "status": {"kind": "assumed"}}]}]
    _, assumptions, _, reasons = audit(api, receipt_case)
    assert reasons == []
    assert [row["id"] for row in assumptions] == ["source.correspondence"]


def test_optional_evidence_attribution_may_be_missing(api, receipt_case):
    receipt_case[3].pop("evidence_attribution")
    assert audit(api, receipt_case)[3] == []


@pytest.mark.parametrize("field", ["axiom_provenance", "reference_provenance"])
def test_receipt_refuses_legacy_unchecked_provenance(api, receipt_case, field):
    receipt_case[4].headers["main"].pop(field)
    assert any("actual-axiom provenance" in reason for reason in audit(api, receipt_case)[3])


@pytest.fixture
def scoped_report(api, receipt_case, tmp_path, monkeypatch):
    request, data, receipt, proof, records = receipt_case
    generated = tmp_path / "Request.lean"
    generated.write_text("-- scoped report fixture\n")
    manifest = tmp_path / "control.toml"
    manifest.write_text('name="control"\n[entries]\nproof="demo::Proof"\n[generated]\nclaims="Request.lean"\n')
    monkeypatch.setattr(api, "ROOT", tmp_path)
    monkeypatch.setattr(api, "owned_module_path", lambda _: generated)
    monkeypatch.setattr(api, "verified_environment", lambda *_: ({}, []))
    proof["dependencies"].append({"name": "Meaning.predicate", "module": "Meaning", "owned": True})
    node = {"kind": "source-claim", "owner": "Demo", "block": 0, "claim": 0}
    claim = {"request": request, "request_digest": api.data_digest(request), "attachment": {"node": node}}
    mapping = {"node": node, "request_digest": claim["request_digest"],
               "request_declaration": data["name"], "receipt_declaration": receipt["name"]}
    trial = deepcopy(claim)
    trial["request"]["subject"]["entry"] = "demo::Interactive"
    trial["attachment"]["node"]["block"] = 1
    trial["request_digest"] = api.data_digest(trial["request"])
    trial_mapping = {"node": trial["attachment"]["node"], "request_digest": trial["request_digest"],
                     "request_declaration": "Demo.trialData", "receipt_declaration": None,
                     "resolution": {"status": "incomplete", "kind": "registered-undefined",
                                    "definitions": ["completeness@0"]},
                     "attempts": [{"result": "timeout", "partial": True}]}
    trial_data = deepcopy(data)
    trial_data["name"] = "Demo.trialData"
    trial_data["detail"]["claim_data"]["wire_request"] = trial["request"]
    records.by_name[trial_data["name"]] = trial_data
    evidence = {"format": api.EVIDENCE_FORMAT, "subject": "control", "manifest_sha256": api.sha256(manifest),
        "artifacts": {"interactive_export": request["subject"]["unit"]},
        "generated": {"Request.lean": {"sha256": api.sha256(generated)}},
        "source_claim_scope": {"entries": ["demo::Proof"], "selection": "proof-entry"},
        "source_claims": {"format": api.BOUND_CLAIMS_FORMAT, "entry": "demo::Proof",
                          "entries": ["demo::Proof"], "claims": [claim]},
        "claim_receipts": [mapping],
        "source_claim_trials": [{"entry": "demo::Interactive", "claims": [trial], "claim_receipts": [trial_mapping]}],
        "checks": [{"name": "claim-receipt", "outcome": "accepted", "module": receipt["module"],
                    "request": data["name"], "receipt": receipt["name"]}]}
    monkeypatch.setattr(api, "load_evidence", lambda *_: evidence)
    return manifest, records, evidence


def test_public_report_keeps_selected_scope_and_incomplete_trial(api, scoped_report):
    manifest, records, evidence = scoped_report
    evidence["source_claim_inventory"] = [{"declaration": "library::Unused",
                                           "selection": "unselected-subject"}]
    report = api.build(manifest, records)
    assert report["status"] == "no-claim"
    assert report["author_claims"][0]["outcome"] == "established", (report["reasons"], report["claims"])
    assert report["source_claim_scope"] == evidence["source_claim_scope"]
    assert report["source_claim_inventory"] == evidence["source_claim_inventory"]
    trial = report["source_claim_trials"][0]
    assert trial["status"] == "incomplete"
    assert trial["audit_status"] == "checked"
    assert trial["bound_claims"] == evidence["source_claim_trials"][0]["claims"]
    assert trial["claim_receipts"] == evidence["source_claim_trials"][0]["claim_receipts"]
    assert trial["claims"][0]["attempts"] == [{"result": "timeout", "partial": True}]


def test_explicit_empty_entry_cannot_be_hidden_by_another_certified_entry(api, scoped_report):
    manifest, records, evidence = scoped_report
    evidence["source_claim_scope"] = {"entries": ["demo::Proof", "demo::WrongSpecialization"],
                                      "selection": "explicit"}
    evidence["source_claims"]["entries"] = evidence["source_claim_scope"]["entries"]
    report = api.build(manifest, records)
    assert report["outcome"] == "unresolved"
    assert "requested Entry has no matching source claims: demo::WrongSpecialization" in report["reasons"]


def test_trial_without_emitted_records_is_visible_unaudited_open(api, scoped_report):
    manifest, records, _ = scoped_report
    del records.by_name["Demo.trialData"]
    report = api.build(manifest, records)
    assert report["status"] == "no-claim"
    assert report["author_claims"][0]["outcome"] == "established"
    trial = report["source_claim_trials"][0]
    assert trial["audit_status"] == "unaudited"
    assert trial["status"] == trial["claims"][0]["status"] == "open"
    assert trial["claims"][0]["resolution"]["definitions"] == ["completeness@0"]


def test_explicit_interactive_selection_audits_the_whole_entry(api, scoped_report):
    manifest, records, evidence = scoped_report
    trial = evidence["source_claim_trials"].pop()
    evidence["source_claim_scope"] = {"entries": [trial["entry"]], "selection": "explicit"}
    evidence["source_claims"].update(entries=[trial["entry"]], claims=trial["claims"])
    evidence["claim_receipts"] = trial["claim_receipts"]
    report = api.build(manifest, records)
    assert report["status"] == "incomplete"
    assert report["source_claim_scope"] == evidence["source_claim_scope"]
    assert report["claims"][0]["request"]["subject"]["entry"] == trial["entry"]


@pytest.mark.parametrize("change", ["missing", "entries", "selection", "request", "default"])
def test_inconsistent_selected_entry_scope_cannot_certify(api, scoped_report, change):
    manifest, records, evidence = scoped_report
    if change == "missing":
        evidence.pop("source_claim_scope")
    elif change == "entries":
        evidence["source_claim_scope"]["entries"] = ["other::Proof"]
    elif change == "selection":
        evidence["source_claim_scope"]["selection"] = "some-property"
    elif change == "request":
        evidence["source_claims"]["claims"][0]["request"]["subject"]["entry"] = "other::Proof"
    else:
        manifest.write_text(manifest.read_text().replace('proof="demo::Proof"', 'proof="other::Proof"'))
        evidence["manifest_sha256"] = api.sha256(manifest)
    report = api.build(manifest, records)
    assert report["outcome"] == "unresolved"
    assert report["claims"][0]["outcome"] == "unresolved"
    assert any("scope" in reason or "selection" in reason for reason in report["reasons"])


@pytest.mark.parametrize("metadata", [
    {"root_route": "endpoint"},
    {"discharger": "False.elim"},
    {"provenance": None, "provenance_error": "unresolved optional string"},
    {"provenance": "malformed optional attribution"},
    {"provenance": {"dependencies": 17}},
    {"evidence_attribution": {"diagnostic": "best-effort attribution failed"}},
])
def test_optional_attribution_never_refuses_fixed_meaning(api, receipt_case, metadata):
    receipt_case[3].update(metadata)
    assert audit(api, receipt_case)[3] == []


def test_internal_link_proof_occurrence_is_not_a_condition(api, receipt_case):
    interpreted_stage(api, receipt_case, "executable-bytes")
    receipt_case[3]["required_links"][1]["conditional"] = True
    assert audit(api, receipt_case)[3] == []


def test_provenance_premise_strings_never_become_assumptions(api, receipt_case):
    receipt_case[3]["provenance"]["premises"] = [
        {"identifier": {"name": "unregistered.note", "version": 0}}]
    _, assumptions, _, reasons = audit(api, receipt_case)
    assert reasons == []
    assert [row["id"] for row in assumptions] == ["source.correspondence"]



def test_registered_provenance_note_does_not_invent_assumptions(api, receipt_case):
    request, data, record, proof, records = receipt_case
    entry = {"identifier": "model.note", "category": "model", "schema": "Demo.model", "statement": "note"}
    proof["proof_dependencies"] = [{"name": "True.intro"}, {"name": "Demo.model"}]
    proof["provenance"]["premises"] = [{"identifier": {"name": "model.note", "version": 0}}]
    _, assumptions, _, reasons = api.audit_receipt(record, data, request, api.Registry([entry], []), records)
    assert reasons == []
    assert [row["id"] for row in assumptions] == ["source.correspondence"]


def test_fixed_meaning_still_refuses_nonstandard_axioms(api, receipt_case):
    receipt_case[2]["axioms"].append("Demo.unprovedAxiom")
    assert any("Demo.unprovedAxiom" in reason for reason in audit(api, receipt_case)[3])


@pytest.mark.parametrize("change,diagnostic", [
    ("wrong-model", "wrong request"),
    ("unknown-property", "wrong registered property"),
    ("missing-link", "unproved registered obligation"),
])
def test_lean_policy_refuses_changed_meaning_controls(api, receipt_case, change, diagnostic):
    if change == "wrong-model":
        receipt_case[3]["wire_request"]["model"]["version"] = 99
    elif change == "unknown-property":
        receipt_case[3]["registered_property"] = {"name": "unknown.property", "version": 0}
    else:
        receipt_case[3]["required_links"][0]["proved"] = False
    assert any(diagnostic in reason for reason in audit(api, receipt_case)[3])


@pytest.mark.parametrize("change,diagnostic", [
    ("missing", "source-node association"), ("duplicate-mapping", "source-node association"),
    ("duplicate-source", "duplicate bound source claim node"),
    ("wrong-artifact", "differs from pipeline bytes"),
])
def test_lean_scope_refuses_exact_association_controls(api, scoped_report, change, diagnostic):
    manifest, records, evidence = scoped_report
    if change == "missing":
        evidence["claim_receipts"] = []
    elif change == "duplicate-mapping":
        evidence["claim_receipts"] *= 2
    elif change == "duplicate-source":
        evidence["source_claims"]["claims"] *= 2
    else:
        evidence["artifacts"]["interactive_export"] = "sha256:other"
    report = api.build(manifest, records)
    assert all(row["status"] != "certified" for row in report["claims"])
    assert any(diagnostic in reason for row in report["claims"] for reason in row["reasons"])


@pytest.mark.parametrize("failure", ["missing", "corrupt", "duplicate", "wrong-node", "missing-audit"])
def test_transport_failure_never_falls_back_to_resolution(api, scoped_report, monkeypatch, failure):
    manifest, records, evidence = scoped_report
    invoke = api._invoke_receipt_classifier

    def broken(payload, packages):
        if failure in {"missing", "corrupt"}:
            raise api.ReceiptTransportError(f"{failure} Lean export")
        export = invoke(payload, packages)
        if failure == "duplicate":
            export["claims"] *= 2
        elif failure == "wrong-node":
            export["claims"][0]["node"] = {"wrong": True}
        else:
            export["claims"][0].pop("audit")
        return export

    monkeypatch.setattr(api, "_invoke_receipt_classifier", broken)
    report = api.build(manifest, records)
    # The visible trial has a registered-undefined resolution. A failed Lean
    # export must still be a transport failure, never an incomplete fallback.
    assert report["status"] == "transport-failure"
    assert report["source_claim_trials"][0]["status"] == "transport-failure"
    assert all(row["status"] == "transport-failure" for row in report["claims"])
    assert "transport failure" in report["reasons"][0]


@pytest.fixture(scope="module")
def kernel_records(tmp_path_factory):
    """Capture only the affected Lean control module, without a package build."""
    root = Path(__file__).resolve().parents[3] / "lean"
    subprocess.run(["lake", "build", "declaration-records", "+Tests.ClaimReporting"], cwd=root,
                   check=True, capture_output=True, text=True)
    path = tmp_path_factory.mktemp("receipt-kernel") / "main.jsonl"
    subprocess.run(["lake", "env", str(root / ".lake/build/bin/declaration-records"),
                    str(path), "Tests/ClaimReporting.lean"], cwd=root,
                   check=True, capture_output=True, text=True)
    declarations = load("kernel_receipt_declarations", "lean/checks/records/declarations.py")
    return declarations.Records.load({"main": path})


@pytest.mark.parametrize("name,diagnostic", [
    ("clean", None), ("genericDirect", None), ("provedLink", None),
    ("forgedDischarger", None), ("forgedDependency", None), ("forgedRoute", None),
    ("explicitFalse", "omitted premise"), ("implicitFalse", "omitted premise"),
    ("inhabitedFalse", "hidden parameter"), ("liftedFalse", "hidden parameter"),
    ("omittedLink", "unproved registered obligation"),
])
def test_production_classifier_reextracts_kernel_receipts(kernel_records, name, diagnostic):
    api = load("production_receipt_cli", "lean/checks/check_records.py").reports
    request_record = kernel_records.get("Tests.ClaimReporting.request0Data")
    request = request_record["detail"]["claim_data"]["wire_request"]
    record = kernel_records.get("Tests.ClaimReporting." + name)
    _, _, _, reasons = api.audit_receipt(record, request_record, request, api.Registry([], []), kernel_records)
    if diagnostic is None:
        assert reasons == []
    else:
        assert any(diagnostic in reason for reason in reasons), reasons


def test_python_verified_flag_cannot_override_kernel_audit(kernel_records):
    api = load("production_receipt_flags", "lean/checks/check_records.py").reports
    request_record = kernel_records.get("Tests.ClaimReporting.request0Data")
    record = deepcopy(kernel_records.get("Tests.ClaimReporting.explicitFalse"))
    record["detail"]["claim_data"]["receipt"].update(
        verified=True, telescope={"accepted": True, "binders": [], "conditions": []})
    declarations = load("kernel_receipt_corruption", "lean/checks/records/declarations.py")
    modified = declarations.Records(kernel_records.headers, [request_record, record])
    _, _, _, reasons = api.audit_receipt(record, request_record,
        request_record["detail"]["claim_data"]["wire_request"], api.Registry([], []), modified)
    assert any("transport failure" in reason and "corrupt kernel export" in reason for reason in reasons)


@pytest.fixture(scope="module")
def security_kernel_records(tmp_path_factory):
    root = Path(__file__).resolve().parents[3] / "lean"
    subprocess.run(["lake", "build", "+TestsSecurity.ClaimReporting"], cwd=root / "security",
                   check=True, capture_output=True, text=True)
    prefix = "TestsSecurity.ClaimReporting."
    names = ["idealData", "HigherOrder.unattributedReceipt", "Canonical.checkedReceipt",
             "HigherOrder.extraPremiseReceipt", "omittedReceipt", "replacedModelReceipt", "artifacts"]
    payload = {"format": "zkc.receipt-audit-input/0", "operation": "extract",
               "records": [{"name": prefix + name, "module": "TestsSecurity.ClaimReporting"} for name in names]}
    result = subprocess.run(["lake", "env", str(root / ".lake/build/bin/declaration-records"),
                             "--receipt-status"], cwd=root / "security", input=json.dumps(payload) + "\n",
                            check=True, capture_output=True, text=True)
    export = json.loads(result.stdout)
    assert export["format"] == "zkc.receipt-kernel-export/0"
    declarations = load("security_kernel_receipt_declarations", "lean/checks/records/declarations.py")
    return declarations.Records({"security": export["headers"][0]}, export["records"])



@pytest.mark.parametrize("name,diagnostic", [
    ("HigherOrder.unattributedReceipt", None), ("Canonical.checkedReceipt", None),
    ("HigherOrder.extraPremiseReceipt", "omitted premise"),
    ("omittedReceipt", "missing required interpreted-stage link"),
    ("replacedModelReceipt", "unrecognized property/model registry"),
])
def test_production_security_kernel_controls(security_kernel_records, name, diagnostic):
    api = load("production_security_receipt_cli", "lean/checks/check_records.py").reports
    record = security_kernel_records.get("TestsSecurity.ClaimReporting." + name)
    assert record
    request_record = security_kernel_records.get("TestsSecurity.ClaimReporting.idealData")
    request = request_record["detail"]["claim_data"]["wire_request"]
    _, _, _, reasons = api.audit_receipt(record, request_record, request, api.Registry([], []), security_kernel_records)
    if diagnostic is None:
        assert reasons == []
    else:
        assert any(diagnostic in reason for reason in reasons), reasons


def test_production_report_consumes_final_lean_scope_status(security_kernel_records, tmp_path, monkeypatch):
    api = load("production_final_scope_cli", "lean/checks/check_records.py").reports
    records = security_kernel_records
    request_record = records.get("TestsSecurity.ClaimReporting.idealData")
    record = records.get("TestsSecurity.ClaimReporting.HigherOrder.unattributedReceipt")
    proof = record["detail"]["claim_data"]["receipt"]
    request = request_record["detail"]["claim_data"]["wire_request"]
    module_path = api.owned_module_path(record["module"])
    relative = str(module_path.relative_to(api.ROOT))
    entry = request["subject"]["entry"]
    manifest = tmp_path / "control.toml"
    manifest.write_text(f'name="control"\n[entries]\nproof={json.dumps(entry)}\n[generated]\nclaims={json.dumps(relative)}\n')
    node = {"owner": "kernel-report-control", "claim": 0}
    digest = api.data_digest(request)
    item = {"request": request, "request_digest": digest, "attachment": {"node": node}}
    mapping = {"node": node, "request_digest": digest, "request_declaration": request_record["name"],
               "receipt_declaration": record["name"]}
    typed = proof["subject"]
    artifacts = {"original_export": request["subject"]["unit"], "source": typed["original_source"],
                 "constructed_candidate": typed["participant_candidate"]}
    for role in proof["stage_links"]["artifact_roles"]:
        artifacts[role["pipeline_artifact"]] = next(
            row["digest"] for row in request["subject"]["artifacts"] if row["role"] == role["role"])
    evidence = {"format": api.EVIDENCE_FORMAT, "subject": "control", "manifest_sha256": api.sha256(manifest),
        "artifacts": artifacts, "generated": {relative: {"sha256": api.sha256(module_path)}},
        "source_claim_scope": {"entries": [entry], "selection": "proof-entry"},
        "source_claims": {"format": api.BOUND_CLAIMS_FORMAT, "entries": [entry], "claims": [item]},
        "claim_receipts": [mapping], "checks": [{"name": "claim-receipt", "outcome": "accepted",
            "module": record["module"], "request": request_record["name"], "receipt": record["name"]}]}
    monkeypatch.setattr(api, "load_evidence", lambda *_: evidence)
    # These are explicit external fixture admissions. Kernel extraction and the
    # complete final Lean classifier remain the production path.
    monkeypatch.setattr(api, "verified_environment", lambda *_: ({"fixture_admission": True}, []))
    report = api.build(manifest, records)
    assert report["status"] == "certified", report
    assert report["claims"][0]["root_route"] == "unattributed"
    assert report["claims"][0]["audit_checks"]
    mapping["resolution"] = {"status": "incomplete", "kind": "registered-undefined", "definitions": ["meaning"]}
    changed = api.build(manifest, records)
    assert changed["status"] == "open"
    assert "inconsistent resolution" in " ".join(changed["claims"][0]["reasons"])
    # A current invocation can still carry a corrupt outer status. Preserve
    # its nonce and real positive item while making the scope unaudited.
    mapping.pop("resolution")
    invoke = api._invoke_receipt_classifier

    def unaudited_item(*args):
        exported = invoke(*args)
        assert exported["claims"][0]["audit"]["status"] == "certified"
        exported.update(status="open", outcome="unresolved", audit_status="unaudited")
        return exported

    monkeypatch.setattr(api, "_invoke_receipt_classifier", unaudited_item)
    refused = api.build(manifest, records)
    assert refused["status"] == "transport-failure"
    assert refused["claims"][0]["status"] == "transport-failure"


def test_production_optional_attribution_never_vetoes_receipt(kernel_records):
    api = load("production_optional_notes", "lean/checks/check_records.py").reports
    request_record = kernel_records.get("Tests.ClaimReporting.request0Data")
    record = deepcopy(kernel_records.get("Tests.ClaimReporting.genericDirect"))
    proof = record["detail"]["claim_data"]["receipt"]
    for key in ("provenance", "provenance_error", "root_route", "discharger", "evidence_attribution", "proof_dependencies"):
        proof.pop(key, None)
    result, _, _, reasons = api.audit_receipt(record, request_record,
        request_record["detail"]["claim_data"]["wire_request"], api.Registry([], []), kernel_records)
    assert reasons == []
    assert result["root_route"] == "unattributed"


def test_transport_response_is_bound_to_each_invocation(monkeypatch):
    api = load("receipt_exchange_cli", "lean/checks/check_records.py").reports
    saved = []

    def subprocess_result(command, **kwargs):
        if "printenv" in command:
            return subprocess.CompletedProcess(command, 0, ".lake/build/lib/lean\n", "")
        if "--receipt-status" not in command:
            return subprocess.CompletedProcess(command, 0, "", "")
        payload = json.loads(kwargs["input"])
        if not saved:
            saved.append({"format": "zkc.receipt-status/0", "authority": "fresh-kernel-audit/0",
                          "exchange": payload["exchange"]})
        return subprocess.CompletedProcess(command, 0, json.dumps(saved[0]), "")

    monkeypatch.setattr(api.subprocess, "run", subprocess_result)
    api._invoke_receipt_classifier({"operation": "scope", "reasons": []}, {"main"})
    with pytest.raises(api.ReceiptTransportError, match="another audit invocation"):
        api._invoke_receipt_classifier({"operation": "scope", "reasons": ["changed dependency"]}, {"main"})


def test_rendering_retains_the_audited_dependency_observation(api, scoped_report, monkeypatch):
    manifest, records, _evidence = scoped_report
    actual = api.semantic_dependencies
    observations = []

    def observe(*args):
        value, reasons = actual(*args)
        value = {**value, "observation": len(observations)}
        observations.append(value)
        return value, reasons

    monkeypatch.setattr(api, "semantic_dependencies", observe)
    report = api.build(manifest, records)
    rows = [*report["claims"], *(row for trial in report["source_claim_trials"] for row in trial["claims"])]
    assert len(observations) == len(rows)
    assert [row["semantic_dependencies"] for row in rows] == observations


def test_unaudited_positive_status_is_a_transport_failure(api, scoped_report, monkeypatch):
    manifest, records, _ = scoped_report
    invoke = api._invoke_receipt_classifier

    def corrupt(*args):
        result = invoke(*args)
        result.update(status="certified", outcome="established", audit_status="unaudited")
        result["claims"][0]["claim_kind"] = "canonical"
        return result

    monkeypatch.setattr(api, "_invoke_receipt_classifier", corrupt)
    report = api.build(manifest, records)
    assert report["status"] == "transport-failure"


def test_request_identity_is_independent_of_extra_registry_imports(kernel_records, security_kernel_records):
    api = load("mixed_registry_receipt_cli", "lean/checks/check_records.py").reports
    original = kernel_records.get("Tests.ClaimReporting.request0Data")
    extra = security_kernel_records.get("TestsSecurity.ClaimReporting.idealData")
    assert original["detail"]["claim_data"]["claim_kind"] == "generic"
    payload = {"format": "zkc.receipt-audit-input/0", "operation": "scope",
               "records": [original, extra], "source": {"claims": []},
               "mappings": [{"request_declaration": row["name"]} for row in [original, extra]]}
    result = api._invoke_receipt_classifier(payload, {"main", "security"})
    assert result["status"] == "open"
    assert result["authority"] == "fresh-kernel-audit/0"


@pytest.mark.parametrize("modules,expected", [
    (["TestsSecurity.ClaimReporting"], {"main", "security"}),
    (["ZkcClean", "TestsSecurity.ClaimReporting"], {"main", "clean", "security"}),
])
def test_receipt_search_paths_follow_actual_providers(modules, expected, monkeypatch):
    api = load("receipt_provider_cli", "lean/checks/check_records.py").reports
    declarations = load("receipt_provider_declarations", "lean/checks/records/declarations.py")
    # Use actual library source providers; the Clean package need not be built.
    if "ZkcClean" in modules:
        clean = next(path for path in (api.LEAN / "integrations/clean/ZkcClean").rglob("*.lean"))
        modules = [str(clean.relative_to(api.LEAN / "integrations/clean").with_suffix("")).replace("/", ".")
                   if module == "ZkcClean" else module for module in modules]
    rows = [{"name": f"root{index}", "module": module} for index, module in enumerate(modules)]
    payload = {"operation": "scope", "records": rows,
               "mappings": [{"request_declaration": row["name"]} for row in rows]}
    assert set(api._receipt_provider_groups(payload)) | {"main"} == expected
    assert set(declarations.PACKAGES) >= expected
