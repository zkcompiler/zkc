"""Rust selection compares real Git revisions and fail-closed Nix identities."""

import os
import subprocess
import sys

import pytest

from harness import ROOT


SCRIPT = ROOT / ".github/scripts/select-rust-check.py"


def git(repo, *args):
    return subprocess.check_output([
        "git", "-c", "user.name=CI test", "-c", "user.email=ci@example.invalid",
        "-c", "commit.gpgsign=false", "-c", "core.hooksPath=/dev/null", *args,
    ], cwd=repo, text=True).strip()


@pytest.fixture
def repository(tmp_path):
    git(tmp_path, "init", "--quiet")
    file = tmp_path / "compiler/lib/Example.cpp"
    file.parent.mkdir(parents=True)
    file.write_text("before\n")
    git(tmp_path, "add", ".")
    git(tmp_path, "commit", "--quiet", "-m", "base")
    base = git(tmp_path, "rev-parse", "HEAD")
    file.write_text("after\n")
    git(tmp_path, "commit", "--quiet", "-am", "change")
    return tmp_path, base


def run_selection(repository, monkeypatch, *, mode="same", base=None, head="HEAD"):
    root, original_base = repository
    binary = root / "fake-tools"
    binary.mkdir(exist_ok=True)
    nix = binary / "nix"
    nix.write_text(f"#!{sys.executable}\n" + r'''
import os
import sys
with open(os.environ["NIX_CALLS"], "a") as log:
    log.write(sys.argv[-1] + "\n")
mode = os.environ["NIX_MODE"]
if mode == "failure":
    sys.exit(1)
if mode == "malformed":
    print("not-a-derivation")
    sys.exit(0)
is_base = "rev=" + os.environ["COMPARISON_BASE"] + "#" in sys.argv[-1]
is_shell = "#devShells." in sys.argv[-1]
changed = not is_base and ((mode == "rust" and not is_shell) or (mode == "shell" and is_shell))
print("/nix/store/" + ("changed" if changed else "same") + ("-shell.drv" if is_shell else "-rust.drv"))
''')
    nix.chmod(0o755)
    output, calls = root / "output", root / "calls"
    monkeypatch.setenv("PATH", str(binary) + os.pathsep + os.environ["PATH"])
    run = subprocess.run([sys.executable, SCRIPT], cwd=root, text=True, capture_output=True,
                         env=os.environ | {"BASE": original_base if base is None else base,
                                           "HEAD": head, "GITHUB_OUTPUT": str(output),
                                           "COMPARISON_BASE": original_base,
                                           "NIX_MODE": mode, "NIX_CALLS": str(calls)})
    assert run.returncode == 0, run.stderr
    return output.read_text(), calls.read_text().splitlines() if calls.exists() else []


def test_identical_rust_and_tool_inputs_skip_only_rust(repository, monkeypatch):
    output, calls = run_selection(repository, monkeypatch)
    assert output == "needed=false\n"
    assert len(calls) == 4
    assert sum("#devShells." in c for c in calls) == 2


@pytest.mark.parametrize("mode", ["rust", "shell", "failure", "malformed"])
def test_changed_or_unknown_inputs_run_rust(repository, monkeypatch, mode):
    output, calls = run_selection(repository, monkeypatch, mode=mode)
    assert output == "needed=true\n"
    assert calls


@pytest.mark.parametrize("base", ["", "0" * 40])
def test_missing_base_runs_without_guessing(repository, monkeypatch, base):
    output, calls = run_selection(repository, monkeypatch, base=base)
    assert output == "needed=true\n" and not calls


def test_unresolved_head_runs_without_guessing(repository, monkeypatch):
    output, calls = run_selection(repository, monkeypatch, head="missing-head")
    assert output == "needed=true\n" and not calls


@pytest.mark.parametrize("path", [".github/workflows/ci.yml", ".github/scripts/check-rust-incremental.sh",
                                  ".github/runner/install.sh", ".github/scripts/select-rust-check.py"])
def test_ci_execution_changes_always_run_rust(repository, monkeypatch, path):
    root, _ = repository
    file = root / path
    file.parent.mkdir(parents=True, exist_ok=True)
    file.write_text("changed\n")
    git(root, "add", path)
    git(root, "commit", "--quiet", "-m", "execution change")
    output, calls = run_selection(repository, monkeypatch)
    assert output == "needed=true\n" and not calls
