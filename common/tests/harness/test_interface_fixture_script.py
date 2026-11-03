"""The interface fixture script records the bytes it regenerated and needs a named build."""

import hashlib
import sys

import pytest

from harness import load

SCRIPT = "scripts/regenerate-interface-fixtures.py"


def sha(data):
    return hashlib.sha256(data).hexdigest()


def test_recorded_digests_follow_the_regenerated_bytes(tmp_path):
    script = load("interface_fixture_script", SCRIPT)
    checker = load("documentation_checker", "common/tests/check_docs.py")
    (tmp_path / "a.json").write_text('{"toolchain":"new"}')
    (tmp_path / "b.mlir").write_text("module {}\n")
    stale, regenerated, current = "0" * 64, sha(b'{"toolchain":"new"}'), sha(b"module {}\n")
    fenced = f"```md\n## Current fixture SHA-256\n| `a.json` | `{stale}` |\n```\n"
    text = (f"# Fixtures\n\n{fenced}\n## Current fixture SHA-256\n\n| File | SHA-256 |\n|---|---|\n"
            f"| `a.json` | `{stale}` |\n| `b.mlir` | `{current}` |\n\nProse after the table.\n")
    guide = tmp_path / "README.md"
    guide.write_text(text)
    assert script.record_digests(guide) == [tmp_path / "a.json"]
    # Only the stale row changes; the fenced example and the prose keep their bytes.
    assert guide.read_text() == text.replace(f"| `a.json` | `{stale}` |\n| `b.mlir`",
                                             f"| `a.json` | `{regenerated}` |\n| `b.mlir`")
    assert checker.fixture_digest_errors(guide, "README.md", lambda path: True) == ([], 2)


@pytest.mark.parametrize("table", ["", "| File | SHA-256 |\n|---|---|\n| a.json | 0 |\n"])
def test_unrecorded_or_malformed_tables_are_refused(tmp_path, table):
    script = load("interface_fixture_script", SCRIPT)
    (tmp_path / "a.json").write_text("{}")
    guide = tmp_path / "README.md"
    heading = "## Current fixture SHA-256\n\n" if table else ""
    guide.write_text(f"# Fixtures\n\n{heading}{table}")
    with pytest.raises(ValueError, match="fixture digest"):
        script.record_digests(guide)


def test_regeneration_requires_a_built_compiler(tmp_path, monkeypatch, capsys):
    script = load("interface_fixture_script", SCRIPT)
    build = tmp_path / "build"
    (build / "test").mkdir(parents=True)
    (build / "zkc-compile").write_text("")
    monkeypatch.setattr(sys, "argv", [SCRIPT, str(build)])
    with pytest.raises(SystemExit) as stopped:
        script.main()
    assert stopped.value.code == 2
    message = capsys.readouterr().err
    assert "build the compiler and its tests first" in message
    assert "zkc-common_interface-test" in message and "zkc-compile," not in message
