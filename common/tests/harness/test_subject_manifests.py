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
    for subject in manifests().load_all(["deferred-rounds"]):
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
    assert "Endpoints" not in generated
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


@pytest.mark.parametrize("spelling", [
    "lean/ZkcExamples/./Construction/SchnorrProofData.lean",
    "lean/ZkcExamples//Construction/SchnorrProofData.lean",
])
def test_distinct_outputs_compare_destinations_not_spelling(tmp_path, spelling):
    loader = manifests()
    subject = loader.load_all(["schnorr"])[0]
    source = subject.path.read_text().replace(
        'glue = "lean/ZkcExamples/Construction/SchnorrArtifact.lean"',
        f'glue = "{spelling}"')
    path = tmp_path / "schnorr.toml"
    path.write_text(source)
    with pytest.raises(loader.Refused, match="generated output paths must be distinct"):
        loader.load(path)


@pytest.mark.parametrize("outside", [False, True])
def test_generated_symlinks_cannot_alias_or_escape(tmp_path, monkeypatch, outside):
    loader = manifests()
    root = tmp_path / "repo"
    directory = root / "lean" / "ZkcExamples"
    directory.mkdir(parents=True)
    target = (tmp_path if outside else directory) / "Data.lean"
    target.write_text("maintained data\n")
    (directory / "Glue.lean").symlink_to(target)
    monkeypatch.setattr(loader, "ROOT", root)
    monkeypatch.setattr(loader, "PACKAGES", {"main": (root / "lean", ("ZkcExamples",))})
    path = root / "probe.toml"
    path.write_text('schema = "zkc.subject/0"\nname = "probe"\n[generated]\n'
                    'data = "lean/ZkcExamples/Data.lean"\n'
                    'glue = "lean/ZkcExamples/Glue.lean"\n')
    diagnostic = "must resolve inside" if outside else "generated output paths must be distinct"
    with pytest.raises(loader.Refused, match=diagnostic):
        loader.load(path)
    assert target.read_text() == "maintained data\n"



def test_generated_symlink_cannot_replace_maintained_connection(tmp_path, monkeypatch):
    loader = manifests()
    directory = tmp_path / "lean" / "ZkcExamples"
    directory.mkdir(parents=True)
    proof = directory / "Proof.lean"
    proof.write_text("maintained connection\n")
    (directory / "Generated.lean").symlink_to(proof)
    monkeypatch.setattr(loader, "ROOT", tmp_path)
    monkeypatch.setattr(loader, "PACKAGES", {"main": (tmp_path / "lean", ("ZkcExamples",))})
    path = tmp_path / "probe.toml"
    path.write_text('schema = "zkc.subject/0"\nname = "probe"\n[generated]\n'
                    'glue = "lean/ZkcExamples/Generated.lean"\n[construction]\n'
                    'connection = "ZkcExamples.Proof"\n')
    with pytest.raises(loader.Refused, match="construction.connection must differ"):
        loader.load(path)
    assert proof.read_text() == "maintained connection\n"


def test_typed_library_owns_its_artifacts_without_a_uniform_adapter():
    renderer = load("source_subject_library_evidence", "lean/bridges/pipeline/evidence.py")
    subject = manifests().load_all(["gkr"])[0]
    assert subject.generated("artifacts") is None
    assert subject.get("lean", "library")
    generated = renderer.claims_module(subject, {"claims": []})
    assert "SubjectSoundnessRegistration" in generated
    assert "Endpoints" not in generated
    assert "Artifacts" not in generated
    assert "claim_request" not in generated


@pytest.mark.parametrize("library", ["bad-name", "Library\naxiom injected : False"])
def test_typed_library_declaration_name_is_validated(tmp_path, library):
    import json
    loader = manifests()
    subject = loader.load_all(["gkr"])[0]
    old = subject.get("lean", "library")
    text = subject.path.read_text().replace(f'library = "{old}"', 'library = ' + json.dumps(library))
    path = tmp_path / "gkr.toml"
    path.write_text(text)
    with pytest.raises(loader.Refused, match="lean.library must be a Lean declaration name"):
        loader.load(path)
