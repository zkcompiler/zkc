#!/usr/bin/env python3
"""Build selected sandboxed checks and retain timing, lock and check reports."""

import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts"))
from processes import Interrupted, checked  # noqa: E402
from reporting import run_report  # noqa: E402
from workspace import reports_root  # noqa: E402


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("targets", nargs="*")
    parser.add_argument("--all-checks", action="store_true")
    parser.add_argument("--compiler-cache", type=Path,
                        help="restore and refresh an explicit sandboxed C++ cache seed")
    args = parser.parse_args()
    if bool(args.targets) == args.all_checks:
        parser.error("select targets or --all-checks")
    with run_report(reports_root(), "nix", sys.argv) as output:
        shutil.copy2(ROOT / "flake.lock", output / "flake.lock")
        targets = args.targets
        if args.all_checks:
            names = checked(["nix", "eval", "--json", ".#checks.x86_64-linux",
                             "--apply", "builtins.attrNames"], cwd=ROOT,
                            text=True, capture_output=True)
            targets = [f".#checks.x86_64-linux.{name}" for name in json.loads(names.stdout)]
        (output / "selection.json").write_text(json.dumps({
            "revision": os.environ.get("GITHUB_SHA"), "targets": targets,
        }, indent=2) + "\n")
        build_options = []
        if args.compiler_cache:
            cache = args.compiler_cache.resolve()
            cache.mkdir(parents=True, exist_ok=True)
            seed = checked(["nix", "store", "add-path", "--name", "zkc-compilation-cache", str(cache)],
                           cwd=ROOT, text=True, capture_output=True).stdout.strip()
            build_options = ["--impure", "--file", "nix/ci.nix", "--argstr", "root", str(ROOT),
                             "--argstr", "seed", seed]
            prefix = ".#checks.x86_64-linux."
            if any(not target.startswith(prefix) for target in targets):
                parser.error("--compiler-cache requires local x86_64-linux check targets")
            targets = ["checks." + target.removeprefix(prefix) for target in targets]
            targets.append("packages.compiler.compilationCache")
            if "checks.compiler-consumer" in targets:
                targets.append("checks.compiler-consumer.compilationCache")
        with (output / "outputs.json").open("w") as result:
            checked(["nix", "build", "-L", "--keep-going", "--no-link", "--json",
                     *build_options, *targets], cwd=ROOT, stdout=result)
        results = json.loads((output / "outputs.json").read_text())
        if os.environ.get("ZKC_NIX_CACHE_ROOTS"):
            checked([sys.executable, str(ROOT / ".github/scripts/retain-nix-cache.py"),
                     *(result["drvPath"] for result in results)], cwd=ROOT)
        if args.compiler_cache:
            # Refresh only after every selected check succeeds. Keep cache data
            # separate from store snapshots and retain statistics as evidence.
            with tempfile.TemporaryDirectory(prefix="zkc-compilation-cache-") as temporary:
                staged = Path(temporary)
                for result in results:
                    if path := result["outputs"].get("compilationCache"):
                        name = "consumer" if "compiler-consumer" in result["drvPath"] else "compiler"
                        destination = staged / name
                        if not destination.exists():
                            destination.mkdir()
                            for filename in ("cache.tar.zst", "stats.json"):
                                shutil.copyfile(Path(path) / filename, destination / filename)
                            shutil.copy2(destination / "stats.json", output / f"{name}-cache.json")
                for source in staged.iterdir():
                    destination = cache / source.name
                    if destination.exists():
                        shutil.rmtree(destination)
                    shutil.copytree(source, destination)
        for result in results:
            for path in result["outputs"].values():
                source = Path(path) / "reports"
                if source.is_dir():
                    destination = output / "checks" / Path(path).name
                    if not destination.exists():
                        shutil.copytree(source, destination)
    if summary := os.environ.get("GITHUB_STEP_SUMMARY"):
        record = json.loads((output / "run.json").read_text())
        with open(summary, "a") as stream:
            stream.write(f"Nix checks completed in {record['elapsed_seconds']:.1f}s. "
                         "The artifact retains the selected lock, outputs and check reports.\n")


if __name__ == "__main__":
    try:
        main()
    except Interrupted as error:
        sys.exit(128 + error.signum)
    except subprocess.CalledProcessError as error:
        sys.exit(error.returncode if error.returncode >= 0 else 128 - error.returncode)
