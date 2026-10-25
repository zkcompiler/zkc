"""Controls for conservative ownership used by migration and edit accounting."""

from importlib import import_module
from pathlib import Path
import sys
import subprocess
import json

import pytest


def classifier():
    root = Path(__file__).resolve().parents[3]
    sys.path.insert(0, str(root / "lean"))
    return import_module("support.responsibility")


@pytest.mark.parametrize("path, layer", [
    ("lean/integrations/arklib/ZkcSecurity/Examples/Subjects/Sumcheck/Evidence.lean", "security-subjects"),
    ("lean/integrations/arklib/ZkcArkLib/Examples/Subjects/Sumcheck/Evidence.lean", "optional-subjects"),
    ("lean/security/ZkcSecurity/Examples/Subjects/Schnorr/Evidence.lean", "security-subjects"),
])
def test_subject_location_does_not_decide_mathematics_or_glue(path, layer):
    row = classifier().classify(path)
    assert row.responsibility is None
    assert row.edit_candidates == ("M", "I")
    assert row.dependency_layer == layer


def test_new_domain_provider_is_not_automatically_a_domain_installation():
    for path in ("compiler/examples/domain/lib/Provider.cpp", "crates/zkc-backend/src/domains/new_provider.rs"):
        row = classifier().classify(path)
        assert row.edit_candidates == ("X",)
        assert "D" not in row.edit_candidates


def test_unreviewed_integration_remains_unclassified():
    row = classifier().classify("lean/integrations/new/Proof.lean")
    assert row.responsibility is None
    assert row.module is None
    assert row.edit_candidates == ()


def test_package_move_does_not_change_logical_responsibility():
    old = classifier().classify("lean/integrations/arklib/ZkcSecurity/Stage/Relation.lean")
    new = classifier().classify("lean/security/ZkcSecurity/Stage/Relation.lean")
    assert old == new


def test_label_like_directory_prefix_cannot_match_owner():
    row = classifier().classify("lean/ZkcSecurityExtra/Endpoint.lean")
    assert row.responsibility is None


def test_sealed_protocol_paths_have_no_classification():
    row = classifier().classify("docs/private/held-out.zkc")
    assert row.responsibility is None
    assert row.edit_candidates == ()


@pytest.mark.parametrize("path", ["", "/lean/Zkc/Foo.lean", "lean/../secret", "lean//Foo.lean", "./lean/Foo.lean", "lean\\Foo.lean", "lean/\0secret"])
def test_noncanonical_paths_are_rejected(path):
    with pytest.raises(ValueError, match="repository-relative"):
        classifier().classify(path)


def test_deleted_path_can_still_be_classified():
    row = classifier().classify("compiler/lib/Compiler/Removed.cpp")
    assert row.responsibility == "language-and-compiler"


def test_family_investment_is_not_silently_counted_as_instantiation():
    row = classifier().classify("lean/integrations/arklib/ZkcSecurity/Families/Schnorr.lean")
    assert row.edit_candidates == ("M", "S")
    assert "I" not in row.edit_candidates


def test_standalone_lean_tools_do_not_become_unowned_modules():
    for path in ("lean/checks/DeclarationRecords.lean", "lean/clients/Core.lean"):
        row = classifier().classify(path)
        assert row.responsibility == "support-infrastructure"
        assert row.module is None


def test_inventory_uses_tracked_working_bytes_and_does_not_follow_symlinks(tmp_path):
    root = Path(__file__).resolve().parents[3]
    subprocess.run(["git", "init", "-q", str(tmp_path)], check=True)
    files = {"lean/Zkc/Old.lean": "old", "compiler/lib/Edited.cpp": "before",
             "docs/private/held-out.zkc": "sealed"}
    for name, contents in files.items():
        path = tmp_path / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(contents)
    (tmp_path / "lean/Zkc/Link.lean").symlink_to("missing-external-file")
    subprocess.run(["git", "add", "."], cwd=tmp_path, check=True)
    subprocess.run(["git", "-c", "user.name=Test", "-c", "user.email=test@example.invalid",
                    "-c", "commit.gpgsign=false", "commit", "-qm", "fixture"], cwd=tmp_path, check=True)
    (tmp_path / "lean/Zkc/Old.lean").unlink()
    (tmp_path / "compiler/lib/Edited.cpp").write_text("after")
    (tmp_path / "lean/Zkc/Untracked.lean").write_text("not inventoried")
    result = subprocess.run([sys.executable, str(root / "lean/checks/source_responsibility.py"),
                             "--root", str(tmp_path)], text=True, capture_output=True, check=True)
    record = json.loads(result.stdout)
    paths = {row["path"]: row for row in record["paths"]}
    assert set(paths) == {"lean/Zkc/Old.lean", "lean/Zkc/Link.lean", "compiler/lib/Edited.cpp"}
    assert paths["lean/Zkc/Old.lean"]["kind"] == "deleted"
    assert paths["lean/Zkc/Old.lean"]["sha256"] is None
    assert paths["lean/Zkc/Link.lean"]["kind"] == "symlink"
    from hashlib import sha256
    assert paths["lean/Zkc/Link.lean"]["sha256"] == sha256(b"missing-external-file").hexdigest()
    assert paths["compiler/lib/Edited.cpp"]["sha256"] == sha256(b"after").hexdigest()
    assert "untracked" in record["scope"]
    assert "content hashes" in record["policy_source"]
