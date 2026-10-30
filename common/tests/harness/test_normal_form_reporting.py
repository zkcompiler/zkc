"""Generated proof acceptance remains bound to the checked output bytes."""

import pytest

from harness import load


@pytest.fixture
def case(tmp_path, monkeypatch):
    api = load("normal_form_reporting", "lean/checks/check_records.py").reports
    monkeypatch.setattr(api, "ROOT", tmp_path)
    (tmp_path / "data.lean").write_text("module\n")
    selection = "Gkr"
    views = ["lean/" + module.replace(".", "/") + ".lean"
             for module in api.source_view_modules(selection)]
    for relative in views:
        output = tmp_path / relative
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text("module\n-- checked source view\n")
    output = tmp_path / views[-1]
    path = tmp_path / "subject.toml"
    path.write_text('name = "example"\n')
    manifest = {"name": "example", "generated": {"data": "data.lean"},
                "source_views": {"selections": [selection]}}
    evidence = {"subject": "example", "manifest_sha256": api.sha256(path), "artifacts": {},
                "generated": {name: {"sha256": api.sha256(tmp_path / name)}
                              for name in ("data.lean", *views)}}
    return api, manifest, path, evidence, output


def test_source_selection_owns_every_checked_output_path(case):
    api, manifest, path, evidence, _ = case
    modules = api.attached(manifest)
    assert {module["path"] for module in modules} == set(evidence["generated"])
    assert len(modules) == 7
    result, reasons = api.connection(manifest, path, modules, evidence)
    assert result["status"] == "connected"
    assert not reasons


@pytest.mark.parametrize("mutation,expected", [
    ("changed", "mismatched"), ("deleted", "mismatched"), ("unrecorded", "unresolved"),
])
def test_changed_missing_or_unchecked_source_view_breaks_the_join(case, mutation, expected):
    api, manifest, path, evidence, output = case
    if mutation == "changed":
        output.write_text("module\n-- substituted output\n")
    elif mutation == "deleted":
        output.unlink()
    else:
        del evidence["generated"][str(output.relative_to(api.ROOT))]
    result, reasons = api.connection(manifest, path, api.attached(manifest), evidence)
    assert result["status"] == expected
    assert any(str(output.relative_to(api.ROOT)) in reason for reason in reasons)
