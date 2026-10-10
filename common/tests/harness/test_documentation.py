"""The public reference checker covers both owners and excludes private material."""

import os

import pytest

from harness import load


@pytest.fixture
def reference(tmp_path, monkeypatch):
    checker = load("documentation_checker", "common/tests/check_docs.py")
    monkeypatch.setattr(checker, "ROOT", tmp_path)

    def write(name, content):
        path = tmp_path / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content)
        return path

    write("README.md", "# Project\n")
    write("docs/README.md", "# Native\n")
    write("lean/README.md", "# Formal package\n")
    write("lean/docs/README.md", "# Formal reference\n")
    return checker, write


def test_formal_reference_links_and_fragments_are_checked(reference):
    checker, write = reference
    write("lean/docs/README.md", "# Formal\n\n[Model](spec/model.md#execution)\n")
    write("lean/docs/spec/model.md", "# Model\n\n## Execution\n")
    assert checker.check()["status"] == "pass"
    write("lean/docs/spec/model.md", "# Model\n\n[Missing](absent.md)\n")
    errors = checker.check()["errors"]
    assert ["lean/docs/README.md", "spec/model.md#execution", "fragment"] in errors
    assert ["lean/docs/spec/model.md", "absent.md", "missing"] in errors


@pytest.mark.parametrize("owner,other", [("docs", "lean/docs"), ("lean/docs", "docs")])
def test_reference_requires_its_own_reading_path(reference, owner, other):
    checker, write = reference
    page = write(f"{owner}/orphan.md", "# Orphan\n")
    other_index = write(f"{other}/README.md", "# Other\n")
    other_index.write_text(f"# Other\n\n[Cross link]({os.path.relpath(page, other_index.parent)})\n")
    assert [f"{owner}/orphan.md", f"unreachable from {owner}/README.md"] in checker.check()["errors"]
    write(f"{owner}/README.md", "# Owner\n\n[Page](orphan.md)\n")
    assert checker.check()["status"] == "pass"


@pytest.mark.parametrize("symlink", [False, True])
def test_existing_private_targets_are_refused(reference, tmp_path, symlink):
    checker, write = reference
    private = write("docs/private/notes.md", "# Private\n")
    if symlink:
        (tmp_path / "docs/alias.md").symlink_to(private)
        target = "alias.md"
    else:
        target = "private/notes.md"
    write("docs/README.md", f"# Native\n\n[Private]({target})\n")
    assert ["docs/README.md", target, "outside public repository"] in checker.check()["errors"]


@pytest.mark.parametrize("directory", ["crates/example", "common/unicode", "common/tests"])
def test_component_guides_remain_in_full_scope(reference, directory):
    checker, write = reference
    write(f"{directory}/README.md", "# Component\n\n[Missing](absent.md)\n")
    assert checker.check()["status"] == "pass"
    assert [f"{directory}/README.md", "absent.md", "missing"] in checker.check(True)["errors"]


def test_private_page_alias_is_never_read_or_hashed(reference, tmp_path):
    checker, write = reference
    private = write("docs/private/notes.md", "")
    private.write_bytes(b"\xff")  # Reading this as a public Markdown page would fail.
    (tmp_path / "docs/alias.md").symlink_to(private)
    result = checker.check()
    assert ["docs/alias.md", "outside public repository"] in result["errors"]
    assert "docs/alias.md" not in result["page_sha256"]


def test_existing_link_outside_repository_is_refused(reference, tmp_path):
    checker, write = reference
    outside = tmp_path.parent / "outside.md"
    outside.write_text("# Outside\n")
    write("docs/README.md", "# Native\n\n[Outside](../../outside.md)\n")
    assert ["docs/README.md", "../../outside.md", "outside public repository"] in checker.check()["errors"]
