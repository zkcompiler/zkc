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


@pytest.fixture
def maintained(tmp_path, monkeypatch):
    upgrade = load("lean_upgrade", "scripts/update-lean-pins.py")
    packages = {name: (tmp_path / "lean" / directory, ()) for name, directory in {
        "program": "program", "ir": "ir", "protocol": "protocol", "verification": "verification",
        "arklib": "adapters/arklib", "clean": "adapters/clean", "applications": "applications",
        "core": "core", "frontend": "frontend", "formal": "formal"}.items()}
    for directory, _ in packages.values():
        directory.mkdir(parents=True)
    monkeypatch.setattr(upgrade, "ROOT", tmp_path)
    monkeypatch.setattr(upgrade, "LEAN", tmp_path / "lean")
    monkeypatch.setattr(upgrade, "PACKAGES", packages)
    monkeypatch.setattr(upgrade, "select_packages", lambda: list(packages))
    return upgrade, {name: directory for name, (directory, _) in packages.items()}


@pytest.mark.parametrize("defect", [None, "missing", "mathlib", "Arklib", "Clean", "shared", "url", "toolchain",
                                    "undeclared", "unresolved"])
def test_resolution_checks_all_packages_and_shared_dependencies(maintained, defect):
    upgrade, packages = maintained
    toolchain = "leanprover/lean4:v4.35.0"
    selected = {"mathlib": OLD, "Arklib": NEW, "Clean": NEW}
    for name, directory in packages.items():
        (directory / "lean-toolchain").write_text(toolchain)
        if name in ("core", "frontend", "formal"):
            # A package that declares no dependency is checked for its toolchain only.
            requirement = '[[require]]\nname = "mathlib"\ngit = "x"\nrev = "' + OLD + '"\n'
            (directory / "lakefile.toml").write_text(
                'name = "zkc_core"\n' + (requirement if defect == "unresolved" else ""))
            locked = manifest(mathlib=OLD) if defect == "undeclared" else {"packages": []}
            if defect == "undeclared":
                locked["packages"][0]["rev"] = NEW
            (directory / "lake-manifest.json").write_text(json.dumps(locked))
            continue
        revisions = {"mathlib": OLD, "batteries": OLD}
        if name in ("protocol", "verification", "arklib", "clean", "applications"):
            revisions["CompPoly"] = OLD
        if name in ("arklib", "applications"):
            revisions["Arklib"] = NEW
        if name in ("clean", "applications"):
            revisions["Clean"] = NEW
        if name == "applications":
            if defect == "missing": revisions.pop("batteries")
            elif defect in ("mathlib", "Arklib", "Clean"):
                revisions[defect] = NEW if defect == "mathlib" else OLD
            elif defect == "shared": revisions["CompPoly"] = NEW
            elif defect == "toolchain": (directory / "lean-toolchain").write_text("different")
        value = manifest(**revisions)
        if name == "applications" and defect == "url":
            value["packages"][0]["url"] = "https://example.invalid/different"
        (directory / "lake-manifest.json").write_text(json.dumps(value))
    if defect:
        with pytest.raises(ValueError): upgrade.check(toolchain, selected)
    else: upgrade.check(toolchain, selected)


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


def test_upgrade_resolves_manifests_with_the_selected_formal_toolchain(maintained, monkeypatch):
    import sys

    upgrade, packages = maintained
    toolchain = "leanprover/lean4:v4.35.0"
    for package, directory in packages.items():
        requirements = {"mathlib": OLD} if package in ("program", "protocol", "arklib", "clean") else {}
        if package in ("arklib", "clean"):
            requirements["Arklib" if package == "arklib" else "Clean"] = OLD
        (directory / "lakefile.toml").write_text('name = "fixture"\n' + ''.join(
            f'[[require]]\nname = "{name}"\ngit = "https://example.invalid/{name}"\nrev = "{rev}"\n'
            for name, rev in requirements.items()))
    monkeypatch.setattr(upgrade, "upstream_toolchain", lambda *_: toolchain)
    monkeypatch.setattr(upgrade, "lean_archive_hash", lambda _: "selected-hash")
    events = []
    monkeypatch.setattr(upgrade, "record_lean_hash", lambda *args: events.append(("hash", args)))

    def run(arguments):
        assert arguments[:2] == ["nix", "develop"]
        if arguments[4] == "bash":
            assert arguments[2] == f"{upgrade.ROOT}#lean"
            positions = []
            for directory in packages.values():
                positions.append(arguments[-1].index(str(directory)))
                assert (directory / "lean-toolchain").read_text().strip() == toolchain
                (directory / "lake-manifest.json").write_text(json.dumps(manifest(
                    mathlib=NEW, Arklib=NEW, Clean=OLD)))
            assert positions == sorted(positions)
            assert arguments[-1].count("lake --keep-toolchain update") == len(packages)
            events.append("resolve")
        else:
            assert arguments[2] == f"{upgrade.ROOT}#maintenance"
            assert arguments[4:6] == ["python3", upgrade.ROOT / "scripts/update-nix-sources.py"]
            events.append("transport")

    monkeypatch.setattr(upgrade, "run", run)
    monkeypatch.setattr(sys, "argv", ["update-lean-pins.py", "--mathlib", NEW, "--arklib", NEW])
    upgrade.main()
    assert events == [("hash", ("4.35.0", "selected-hash")), "resolve", "transport"]
    for name in ("program", "protocol", "arklib", "clean"):
        assert upgrade.required(packages[name] / "lakefile.toml", "mathlib")[1] == NEW
    assert upgrade.required(packages["arklib"] / "lakefile.toml", "Arklib")[1] == NEW
    assert upgrade.required(packages["clean"] / "lakefile.toml", "Clean")[1] == OLD


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
    monkeypatch.setattr(upgrade, "PACKAGES", {"arklib": (integration, ())})
    upgrade.detach_dependency_links()
    assert (source / "source.lean").read_text() == "-- shared source\n"
    assert sorted(path.name for path in packages.iterdir()) == ["owned"]
