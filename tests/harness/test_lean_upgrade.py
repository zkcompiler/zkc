"""Coordinated upgrades edit named requirements and verify actual resolutions."""

import json

import pytest

from harness import load


OLD, NEW = "a" * 40, "b" * 40


def manifest(**revisions):
    return {"packages": [{"type": "git", "name": name, "rev": rev}
                         for name, rev in revisions.items()]}


def test_revision_edit_targets_requirement_not_namesake_library(tmp_path):
    upgrade = load("lean_upgrade", "scripts/update-lean-pins.py")
    path = tmp_path / "lakefile.toml"
    text = ('name = "mathlib"\n\n[[lean_lib]]\nname = "mathlib"\n\n'
            '[[require]]\nname = "mathlib"\ngit = "https://example.invalid/mathlib"\n'
            f'rev = "{OLD}" # selected commit\n\n[[lean_lib]]\nname = "Other"\n')
    path.write_text(text)
    assert upgrade.required(path, "mathlib") == ("https://example.invalid/mathlib", OLD)
    upgrade.set_required_rev(path, "mathlib", OLD, NEW)
    assert path.read_text() == text.replace(OLD, NEW)
    with pytest.raises(ValueError, match="cannot find"):
        upgrade.set_required_rev(path, "mathlib", OLD, NEW)
    assert path.read_text() == text.replace(OLD, NEW)


def test_duplicate_requirement_is_not_silently_selected(tmp_path):
    upgrade = load("lean_upgrade", "scripts/update-lean-pins.py")
    path = tmp_path / "lakefile.toml"
    path.write_text('[[require]]\nname = "mathlib"\n' * 2)
    with pytest.raises(ValueError, match="expected one"):
        upgrade.required(path, "mathlib")


@pytest.mark.parametrize("defect", [None, "missing", "wrong-mathlib", "wrong-arklib", "toolchain"])
def test_resolution_checks_the_selected_graph(tmp_path, monkeypatch, defect):
    upgrade = load("lean_upgrade", "scripts/update-lean-pins.py")
    main, integration = tmp_path / "main", tmp_path / "integration"
    monkeypatch.setattr(upgrade, "MAIN", main)
    monkeypatch.setattr(upgrade, "INTEGRATION", integration)
    toolchain = "leanprover/lean4:v4.33.1"
    for package in (main, integration):
        package.mkdir()
        (package / "lean-toolchain").write_text(toolchain)
        revisions = {"mathlib": OLD}
        if package == integration:
            revisions.update(Arklib=NEW, batteries=OLD)
        (package / "lake-manifest.json").write_text(json.dumps(manifest(**revisions)))
    if defect == "toolchain":
        (main / "lean-toolchain").write_text("different")
    elif defect:
        revisions = {"mathlib": OLD, "Arklib": NEW, "batteries": OLD}
        if defect == "missing":
            revisions.pop("batteries")
        elif defect == "wrong-mathlib":
            revisions["mathlib"] = NEW
        else:
            revisions["Arklib"] = OLD
        (integration / "lake-manifest.json").write_text(json.dumps(manifest(**revisions)))
    upstream = manifest(mathlib=OLD, batteries=OLD)
    if defect:
        with pytest.raises(ValueError):
            upgrade.check(toolchain, upstream, NEW)
    else:
        upgrade.check(toolchain, upstream, NEW)


@pytest.mark.parametrize("defect", ["duplicate", "unresolved"])
def test_manifest_requires_unique_resolved_revisions(defect):
    upgrade = load("lean_upgrade", "scripts/update-lean-pins.py")
    value = manifest(mathlib=OLD)
    if defect == "duplicate":
        value["packages"] *= 2
    else:
        value["packages"][0]["rev"] = "main"
    with pytest.raises(ValueError):
        upgrade.git_revisions(value)
