"""Measure real one-file compiler changes without changing the checked-out PR."""

import json
import os
from pathlib import Path
import subprocess
import tempfile
import time


ROOT = Path(__file__).resolve().parents[2]
REPORTS = ROOT / "build/reports/compiler-cache"


def git(root, *args):
    return subprocess.check_output([
        "git", "-c", "user.name=CI cache probe", "-c", "user.email=ci@example.invalid",
        "-c", "commit.gpgsign=false", "-c", "core.hooksPath=/dev/null", *args,
    ], cwd=root, text=True).strip()


def measured(root, name, command, **kwargs):
    start = time.monotonic()
    with (REPORTS / f"{name}.log").open("w") as log:
        completed = subprocess.run(command, cwd=root, stdout=log, stderr=subprocess.STDOUT, **kwargs)
    seconds = round(time.monotonic() - start, 2)
    print(f"{name}: exit {completed.returncode}, {seconds:.2f}s", flush=True)
    completed.check_returncode()
    return seconds


def main():
    if "ZKC_CI_ROOT" not in os.environ:
        raise SystemExit("Run in the dedicated CI service.")
    REPORTS.mkdir(parents=True, exist_ok=True)
    baseline = git(ROOT, "rev-parse", "HEAD")
    measured(ROOT, "cache-controls", ["nix", "build", "-L", "--no-link", ".#compiler-cache-check"])
    # Populate the object cache even when an identical package output already
    # exists; this is an explicit benchmark, not an automatic PR obligation.
    measured(ROOT, "compiler-baseline", ["nix", "build", "-L", "--no-link", ".#compiler"])
    measured(ROOT, "cache-prime", ["nix", "build", "-L", "--no-link", "--rebuild", ".#compiler"])
    results = {"baseline": baseline, "samples": []}
    with tempfile.TemporaryDirectory(prefix="zkc-compiler-cache-") as temporary:
        checkout = Path(temporary) / "source"
        git(ROOT, "worktree", "add", "--quiet", "--detach", str(checkout), baseline)
        try:
            original = (checkout / "compiler/lib/Support/Refusal.cpp").read_text()
            marker = "char Refusal::ID = 0;"
            if original.count(marker) != 1:
                raise RuntimeError("The benchmark mutation needs review after Refusal.cpp changed.")
            for value in (1, 2):
                name = f"change-{value}"
                # LLVM error identification uses this object's address. Varying
                # its byte changes a real translation unit without changing
                # the source programs or the expected protocol outcomes.
                (checkout / "compiler/lib/Support/Refusal.cpp").write_text(
                    original.replace(marker, f"char Refusal::ID = {value};"))
                git(checkout, "add", "compiler/lib/Support/Refusal.cpp")
                git(checkout, "commit", "--quiet", "-m", "compiler cache measurement")
                revision = git(checkout, "rev-parse", "HEAD")
                selection = REPORTS / f"{name}-rust-selection.txt"
                measured(checkout, f"{name}-selection", ["python3", str(ROOT / ".github/scripts/select-rust-check.py")],
                         env=os.environ | {"BASE": baseline, "HEAD": revision, "GITHUB_OUTPUT": str(selection)})
                if selection.read_text() != "needed=false\n":
                    raise RuntimeError("A compiler-only mutation unnecessarily selected Rust tests.")
                compiler_seconds = measured(checkout, f"{name}-compiler",
                                            ["nix", "build", "-L", "--no-link", ".#compiler"])
                smoke = json.loads((checkout / "common/tests/smoke.json").read_text())
                checks = ["application", "compiler-consumer", "rust-consumer", "sdk", "sources", "format"]
                checks += [f"smoke-{family}" for family in sorted(smoke)]
                validation_seconds = measured(checkout, f"{name}-validation", [
                    "nix", "build", "-L", "--keep-going", "--no-link",
                    *(f".#checks.x86_64-linux.{check}" for check in checks)])
                sample = {"revision": revision, "compiler_seconds": compiler_seconds,
                          "validation_seconds": validation_seconds}
                if value == 1:
                    expression = ('(builtins.getFlake (builtins.getEnv "ZKC_CACHE_BENCH_SOURCE"))'
                                  '.packages.x86_64-linux.compiler.overrideAttrs { CCACHE_DISABLE = "1"; }')
                    sample["uncached_compiler_seconds"] = measured(
                        checkout, "uncached-compiler", ["nix", "build", "-L", "--no-link", "--impure",
                                                       "--expr", expression],
                        env=os.environ | {"ZKC_CACHE_BENCH_SOURCE": f"git+{checkout.as_uri()}?rev={revision}"})
                results["samples"].append(sample)
                (REPORTS / "summary.json").write_text(json.dumps(results, indent=2) + "\n")
        finally:
            git(ROOT, "worktree", "remove", "--force", str(checkout))
    print(json.dumps(results, indent=2))


if __name__ == "__main__":
    main()
