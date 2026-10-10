"""CI selection exercises real Git changes without building native tools."""

import os
from pathlib import Path
import subprocess
import sys

import pytest

from harness import ROOT


SCRIPT = ROOT / ".github/scripts/select-native-changes.py"


def git(repo, *args):
    return subprocess.check_output([
        "git", "-c", "user.name=CI test", "-c", "user.email=ci@example.invalid",
        "-c", "commit.gpgsign=false", "-c", "core.hooksPath=/dev/null", *args,
    ], cwd=repo, text=True).strip()


def select(repo, base, output):
    output.write_text("existing=value\n")
    subprocess.run([sys.executable, SCRIPT], cwd=repo, check=True,
                   env=os.environ | {"BASE": base, "HEAD": "HEAD", "GITHUB_OUTPUT": str(output)})
    return output.read_text()


@pytest.mark.parametrize("path,remove,expected", [
    ("common/unicode/17.0.0/UnicodeData.txt", False, True),
    ("common/unicode/17.0.0/NormalizationTest.txt", False, True),
    ("common/unicode/manifest.json", False, True),
    ("common/unicode/manifest.json", True, True),
    ("common/tests/run.py", False, True),
    ("lean/Zkc.lean", False, False),
    ("compiler/CMakeLists.txt", False, True),
    ("crates/zkc-tools/build.rs", False, True),
    ("common/unicode/README.md", False, False),
    ("docs/README.md", False, False),
])
def test_native_selection_from_changes(tmp_path, path, remove, expected):
    repo = tmp_path / "repo"
    repo.mkdir()
    git(repo, "init", "--quiet")
    changed = repo / path
    changed.parent.mkdir(parents=True, exist_ok=True)
    changed.write_text("before\n")
    git(repo, "add", ".")
    git(repo, "commit", "--quiet", "-m", "base")
    base = git(repo, "rev-parse", "HEAD")
    if remove:
        changed.unlink()
    else:
        changed.write_text("after\n")
    git(repo, "add", "-A")
    git(repo, "commit", "--quiet", "-m", "change")
    assert select(repo, base, tmp_path / "output") == f"existing=value\nnative={str(expected).lower()}\n"


@pytest.mark.parametrize("base", ["", "0" * 40])
@pytest.mark.parametrize("path,expected", [("common/unicode/manifest.json", True), ("README.md", False)])
def test_missing_base_uses_tracked_sources(tmp_path, base, path, expected):
    git(tmp_path, "init", "--quiet")
    tracked = tmp_path / path
    tracked.parent.mkdir(parents=True, exist_ok=True)
    tracked.write_text("tracked\n")
    git(tmp_path, "add", str(Path(path)))
    assert select(tmp_path, base, tmp_path / "output") == f"existing=value\nnative={str(expected).lower()}\n"
