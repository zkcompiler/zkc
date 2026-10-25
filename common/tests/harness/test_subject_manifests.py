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
