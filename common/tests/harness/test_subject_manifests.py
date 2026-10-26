"""Manifest configuration cannot create or select source claim semantics."""

from copy import deepcopy

import pytest
from harness import load


def manifests():
    return load("source_subject_manifests", "lean/bridges/pipeline/manifest.py")


def test_all_subject_manifests_drop_semantic_tables():
    subjects = manifests().load_all()
    assert subjects
    for subject in subjects:
        assert "claims" not in subject.data
        assert "family" not in subject.data
        if subject.generated("claims"):
            assert subject.get("lean", "imports")
            assert subject.get("lean", "namespace")


@pytest.mark.parametrize("table", ["claims", "family"])
def test_old_semantic_tables_are_rejected(table):
    loader = manifests()
    data = {"schema": loader.SCHEMA, "name": "test", table: {}}
    with pytest.raises(loader.Refused, match="unknown table"):
        loader._validate(data, "test.toml")


def test_targetless_unclaimed_subjects_have_no_generated_source_authority():
    for subject in manifests().load_all(["gkr", "deferred-rounds"]):
        assert subject.generated("claims") is None
        assert subject.get("lean", "namespace") is None


def test_no_manifest_property_fallback_in_generator():
    renderer = load("source_subject_evidence", "lean/bridges/pipeline/evidence.py")
    subject = manifests().load_all(["schnorr"])[0]
    # An empty actual source export emits no receipt even for the historical
    # Schnorr manifest and maintained endpoint clients.
    generated = renderer.claims_module(subject, {"claims": []})
    assert "claim_request" not in generated
    assert "KnowledgeSoundness" not in generated
    assert "Endpoints" in generated
    changed = deepcopy(subject)
    changed.data["claims"] = {"properties": ["forged"]}
    assert renderer.claims_module(changed, {"claims": []}) == generated


def test_metadata_namespace_and_connection_have_separate_owners():
    for subject in manifests().load_all():
        if subject.generated("claims"):
            assert subject.generated("glue").stem.endswith("Artifact")
            assert subject.module_name("glue") != subject.construction_namespace
            assert subject.get("construction", "connection") == subject.construction_namespace
        elif subject.name == "deferred-rounds":
            assert subject.construction_namespace == subject.module_name("glue")


@pytest.mark.parametrize("replacement,diagnostic", [
    ('', 'requires a maintained construction.connection'),
    ('connection = "ZkcExamples.Construction.SchnorrArtifact"', 'must differ'),
    ('connection = "bad-name"', 'must be a Lean name'),
])
def test_claim_metadata_requires_a_distinct_connection(tmp_path, replacement, diagnostic):
    loader = manifests()
    subject = loader.load_all(["schnorr"])[0]
    source = subject.path.read_text().replace(
        'connection = "ZkcExamples.Construction.SchnorrProof"', replacement)
    path = tmp_path / "schnorr.toml"
    path.write_text(source)
    with pytest.raises(loader.Refused, match=diagnostic):
        loader.load(path)


def test_executable_facts_import_metadata_and_reference_its_namespace():
    renderer = load("subject_glue_ownership", "lean/bridges/pipeline/glue.py")
    result = renderer.facts_module("Client.ByteFacts", {
        "names": [], "types": [], "glue": "Client.Protocol", "module": "Generated.Admission"
    }, "Generated.Program", {"helpers": "[]", "calls": 0}, "values")
    assert 'public import Generated.Admission' in result
    assert 'public import Client.Protocol' not in result
    assert 'Client.Protocol.participant' in result
    assert 'Client.Protocol.inputs' in result


@pytest.mark.parametrize("replacement,diagnostic", [
    ("", "executable claims require generated.lowering"),
    ('lowering = "lean/security/ZkcSecurity/Examples/Subjects/Schnorr/Artifacts.lean"',
     "generated output paths must be distinct"),
])
def test_byte_evidence_has_an_explicit_distinct_destination(tmp_path, replacement, diagnostic):
    loader = manifests()
    subject = loader.load_all(["schnorr"])[0]
    source = subject.path.read_text().replace(
        'lowering = "lean/security/ZkcSecurity/Examples/Subjects/Schnorr/Lowering.lean"', replacement)
    path = tmp_path / "schnorr.toml"
    path.write_text(source)
    with pytest.raises(loader.Refused, match=diagnostic):
        loader.load(path)
