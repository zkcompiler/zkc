"""Reuse Rust validation only when its declared build inputs are unchanged."""

import os
from pathlib import Path
import subprocess


INPUTS = ("checks.x86_64-linux.rust.drvPath", "devShells.x86_64-linux.default.drvPath")


def git(*args):
    return subprocess.check_output(["git", *args], text=True, stderr=subprocess.PIPE).strip()


def inputs_at(root, revision):
    reference = f"git+{root.as_uri()}?rev={revision}"
    inputs = []
    for attribute in INPUTS:
        value = subprocess.check_output(
            ["nix", "eval", "--raw", "--no-write-lock-file", f"{reference}#{attribute}"],
            text=True, stderr=subprocess.PIPE, timeout=60).strip()
        if not value.startswith("/nix/store/") or not value.endswith(".drv"):
            raise ValueError("Nix did not return a derivation identity")
        inputs.append(value)
    return inputs


def selection(base, head):
    if not base:
        return True, "No comparison base; run Rust checks."
    try:
        base = git("rev-parse", "--verify", "--end-of-options", base + "^{commit}")
        head = git("rev-parse", "--verify", "--end-of-options", head + "^{commit}")
        changed = git("diff", "--name-only", "--no-renames", base, head).splitlines()
        # The checkout runner is outside the Nix check derivation. Changes to
        # its invocation and service environment must validate it afresh.
        if any(path.startswith(".github/") for path in changed):
            return True, "CI execution or selection changed; run Rust checks."
        root = Path(git("rev-parse", "--show-toplevel")).resolve()
        before, after = inputs_at(root, base), inputs_at(root, head)
        if before != after:
            return True, "Rust check or development-tool inputs changed."
        return False, "Rust check and development-tool inputs are identical to the base."
    except (OSError, subprocess.SubprocessError, ValueError):
        # An unavailable old revision/toolchain is not proof of equivalence.
        return True, "Input comparison unavailable; run Rust checks conservatively."


def main():
    needed, reason = selection(os.environ.get("BASE", ""), os.environ["HEAD"])
    print(reason)
    with open(os.environ["GITHUB_OUTPUT"], "a") as output:
        output.write(f"needed={str(needed).lower()}\n")


if __name__ == "__main__":
    main()
