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


@pytest.mark.parametrize("defect", [None, "missing", "mathlib", "Arklib", "Clean", "shared", "url", "toolchain"])
def test_resolution_checks_all_packages_and_shared_dependencies(tmp_path, monkeypatch, defect):
    upgrade = load("lean_upgrade", "scripts/update-lean-pins.py")
    main, security, arklib, clean = (tmp_path / name for name in ("main", "security", "arklib", "clean"))
    monkeypatch.setattr(upgrade, "MAIN", main)
    monkeypatch.setattr(upgrade, "SECURITY", main / "security")
    monkeypatch.setattr(upgrade, "INTEGRATIONS", {"Arklib": arklib, "Clean": clean})
    monkeypatch.setattr(upgrade, "SECURITY", security)
    toolchain = "leanprover/lean4:v4.34.1"
    selected = {"mathlib": OLD, "Arklib": NEW, "Clean": NEW}
    for directory, name in [(main, "mathlib"), (security, "mathlib"), (arklib, "Arklib"), (clean, "Clean")]:
        directory.mkdir()
        (directory / "lean-toolchain").write_text(toolchain)
        revisions = {"mathlib": OLD, "batteries": OLD, name: selected[name]}
        if directory != main:
            revisions["CompPoly"] = OLD
        if directory == clean:
            if defect == "missing":
                revisions.pop("batteries")
            elif defect in ("mathlib", "Clean"):
                revisions[defect] = NEW if defect == "mathlib" else OLD
            elif defect == "shared":
                revisions["CompPoly"] = NEW
            elif defect == "toolchain":
                (directory / "lean-toolchain").write_text("different")
        if directory == arklib and defect == "Arklib":
            revisions["Arklib"] = OLD
        value = manifest(**revisions)
        if directory == clean and defect == "url":
            value["packages"][0]["url"] = "https://example.invalid/different"
        (directory / "lake-manifest.json").write_text(json.dumps(value))
    if defect:
        with pytest.raises(ValueError):
            upgrade.check(toolchain, selected)
    else:
        upgrade.check(toolchain, selected)


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


def test_upgrade_resolves_manifests_with_the_selected_formal_toolchain(tmp_path, monkeypatch):
    import sys

    upgrade = load("lean_upgrade", "scripts/update-lean-pins.py")
    main = tmp_path / "lean"
    integrations = {name: main / "integrations" / name.lower() for name in ("Arklib", "Clean")}
    toolchain = "leanprover/lean4:v4.34.1"
    packages = {"mathlib": main, "security": main / "security", **integrations}
    for name, directory in packages.items():
        directory.mkdir(parents=True, exist_ok=True)
        (directory / "lakefile.toml").write_text(
            f'[[require]]\nname = "{name}"\ngit = "https://example.invalid/{name}"\nrev = "{OLD}"\n')
        if name != "mathlib":
            with (directory / "lakefile.toml").open("a") as file:
                file.write(f'\n[[require]]\nname = "mathlib"\ngit = "https://example.invalid/mathlib"\nrev = "{OLD}"\n')
    monkeypatch.setattr(upgrade, "ROOT", tmp_path)
    monkeypatch.setattr(upgrade, "MAIN", main)
    monkeypatch.setattr(upgrade, "SECURITY", main / "security")
    monkeypatch.setattr(upgrade, "INTEGRATIONS", integrations)
    monkeypatch.setattr(upgrade, "upstream_toolchain", lambda *_: toolchain)
    monkeypatch.setattr(upgrade, "lean_archive_hash", lambda _: "selected-hash")
    events = []
    monkeypatch.setattr(upgrade, "record_lean_hash", lambda *args: events.append(("hash", args)))

    def run(arguments):
        assert arguments[:2] == ["nix", "develop"]
        if arguments[4] == "bash":
            assert arguments[2] == f"{tmp_path}#lean"
            assert "--keep-toolchain" in arguments[-1]
            for name, directory in packages.items():
                assert (directory / "lean-toolchain").read_text().strip() == toolchain
                revisions = {"mathlib": NEW, name: NEW if name != "Clean" else OLD}
                (directory / "lake-manifest.json").write_text(json.dumps(manifest(**revisions)))
            events.append("resolve")
        else:
            assert arguments[2] == f"{tmp_path}#maintenance"
            assert arguments[4:6] == ["python3", tmp_path / "scripts/update-nix-sources.py"]
            events.append("transport")

    monkeypatch.setattr(upgrade, "run", run)
    monkeypatch.setattr(sys, "argv", ["update-lean-pins.py", "--mathlib", NEW, "--arklib", NEW])
    upgrade.main()
    assert events == [("hash", ("4.34.1", "selected-hash")), "resolve", "transport"]
    assert upgrade.required(main / "lakefile.toml", "mathlib")[1] == NEW
    assert upgrade.required(integrations["Arklib"] / "lakefile.toml", "Arklib")[1] == NEW
    assert upgrade.required(integrations["Clean"] / "lakefile.toml", "Clean")[1] == OLD


def test_update_detaches_cache_links_without_modifying_shared_sources(tmp_path, monkeypatch):
    upgrade = load("lean_upgrade", "scripts/update-lean-pins.py")
    source = tmp_path / "main/.lake/packages/mathlib"
    source.mkdir(parents=True)
    (source / "source.lean").write_text("-- shared source\n")
    integration = tmp_path / "integration"
    packages = integration / ".lake/packages"
    packages.mkdir(parents=True)
    (packages / "mathlib").symlink_to(source)
    (packages / "missing").symlink_to(tmp_path / "absent")
    (packages / "owned").mkdir()
    monkeypatch.setattr(upgrade, "INTEGRATIONS", {"Arklib": integration})
    monkeypatch.setattr(upgrade, "SECURITY", tmp_path / "security")
    upgrade.detach_dependency_links()
    assert (source / "source.lean").read_text() == "-- shared source\n"
    assert sorted(path.name for path in packages.iterdir()) == ["owned"]
