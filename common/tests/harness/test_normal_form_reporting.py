"""Generated proof acceptance remains bound to the checked output bytes."""

import pytest

from harness import load


@pytest.fixture
def case(tmp_path, monkeypatch):
    api = load("normal_form_reporting", "lean/checks/check_records.py").reports
    monkeypatch.setattr(api, "ROOT", tmp_path)
    (tmp_path / "data.lean").write_text("module\n")
    output = tmp_path / "normal.lean"
    output.write_text("module\n-- checked normal form\n")
    (tmp_path / "request.toml").write_text('output = "normal.lean"\n')
    path = tmp_path / "subject.toml"
    path.write_text('name = "example"\n')
    manifest = {"name": "example", "generated": {"data": "data.lean"},
                "normal_forms": {"request": "request.toml"}}
    evidence = {"subject": "example", "manifest_sha256": api.sha256(path), "artifacts": {},
                "generated": {name: {"sha256": api.sha256(tmp_path / name)}
                              for name in ("data.lean", "normal.lean")}}
    return api, manifest, path, evidence, output


def test_normal_form_request_owns_the_checked_output_path(case):
    api, manifest, path, evidence, _ = case
    modules = api.attached(manifest)
    assert {module["path"] for module in modules} == {"data.lean", "normal.lean"}
    result, reasons = api.connection(manifest, path, modules, evidence)
    assert result["status"] == "connected"
    assert not reasons


@pytest.mark.parametrize("mutation,expected", [
    ("changed", "mismatched"), ("deleted", "mismatched"), ("unrecorded", "unresolved"),
])
def test_changed_missing_or_unchecked_normal_form_breaks_the_join(case, mutation, expected):
    api, manifest, path, evidence, output = case
    if mutation == "changed":
        output.write_text("module\n-- substituted output\n")
    elif mutation == "deleted":
        output.unlink()
    else:
        del evidence["generated"]["normal.lean"]
    result, reasons = api.connection(manifest, path, api.attached(manifest), evidence)
    assert result["status"] == expected
    assert any("normal.lean" in reason for reason in reasons)
