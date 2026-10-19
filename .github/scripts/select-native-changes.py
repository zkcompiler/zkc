"""Select native CI from changed paths, including shared build inputs."""

import os
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path[:0] = [str(ROOT / 'common/tests'), str(ROOT / 'common/tests/support')]
from smoke import select_families  # noqa: E402


def main():
    base = os.environ["BASE"]
    exists = base and subprocess.run(
        ["git", "cat-file", "-e", base + "^{commit}"],
        stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL).returncode == 0
    if not exists:
        paths = subprocess.check_output(["git", "ls-files"], text=True).splitlines()
    else:
        paths = subprocess.check_output(
            ["git", "diff", "--name-only", base, os.environ["HEAD"]], text=True).splitlines()
    selected = any((not path.endswith(".md") or path.startswith(('examples/', 'libraries/'))) and re.match(
        r"^(compiler/|crates/|libraries/|examples/|common/|nix/|scripts/|Cargo\.|rust-toolchain|pyproject\.toml|uv\.lock|flake\.|justfile|\.clang-format|\.github/)", path)
        for path in paths)
    with open(os.environ["GITHUB_OUTPUT"], "a") as output:
        output.write(f"native={str(selected).lower()}\n")
        families = select_families(paths if exists else None) if selected else set()
        output.write('smoke=' + ' '.join(f'.#checks.x86_64-linux.smoke-{name}' for name in sorted(families)) + '\n')


if __name__ == "__main__":
    main()
