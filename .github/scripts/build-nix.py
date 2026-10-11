#!/usr/bin/env python3
"""Build selected sandboxed checks and retain timing, lock and check reports."""

import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts"))
from processes import Interrupted, checked  # noqa: E402
from reporting import run_report  # noqa: E402
from workspace import reports_root  # noqa: E402


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("targets", nargs="*")
    parser.add_argument("--all-checks", action="store_true")
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
        with (output / "outputs.json").open("w") as result:
            checked(["nix", "build", "-L", "--keep-going", "--no-link", "--json", *targets],
                    cwd=ROOT, stdout=result)
        for result in json.loads((output / "outputs.json").read_text()):
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
