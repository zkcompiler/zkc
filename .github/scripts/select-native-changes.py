"""Select native CI from changed paths, including shared build inputs."""

import os
import re
import subprocess


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
    selected = any(not path.endswith(".md") and re.match(
        r"^(compiler/|crates/|libraries/|examples/|support/|nix/|scripts/|tests/|Cargo\.|rust-toolchain|flake\.|justfile|\.clang-format|\.github/)", path)
        for path in paths)
    with open(os.environ["GITHUB_OUTPUT"], "a") as output:
        output.write(f"native={str(selected).lower()}\n")


if __name__ == "__main__":
    main()
