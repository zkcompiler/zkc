#!/usr/bin/env python3
"""Check cache invalidation against real source edits in an isolated snapshot.

No packages are built. Equal derivation paths require identical declared
inputs; a positive control also checks that relevant edits invalidate checks.
"""

import json
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


def identities(directory):
    expression = '''let
      flake = builtins.getFlake %s;
      packages = flake.packages.x86_64-linux;
      checks = flake.checks.x86_64-linux;
    in {
      compiler = packages.compiler.drvPath;
      nativeSnapshot = packages.ci-native-dependencies.drvPath;
      rustSnapshot = packages.ci-rust-dependencies.drvPath;
      tools = packages.tools.drvPath;
      productDependencies = packages.tools.dependencies.drvPath;
      rust = checks.rust.drvPath;
      testDependencies = checks.rust.dependencies.drvPath;
      core = checks.core.drvPath;
    }''' % json.dumps(str(directory))
    result = checked(["nix", "eval", "--impure", "--json", "--expr", expression],
                     cwd=directory, text=True, capture_output=True)
    return json.loads(result.stdout)


def main():
    with run_report(reports_root(), "nix-inputs", sys.argv) as output, tempfile.TemporaryDirectory() as temporary:
        directory = Path(temporary) / "source"
        tracked = checked(["git", "ls-files", "-z"], cwd=ROOT, capture_output=True).stdout
        for name in tracked.decode().split("\0"):
            if not name:
                continue
            target = directory / name
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(ROOT / name, target, follow_symlinks=False)
        baseline = identities(directory)
        cases = [
            ("README.md", "\n<!-- cache boundary control -->\n", set()),
            ("libraries/zkc/finite.zkc", "\n// cache boundary control\n", {"core"}),
            ("compiler/lib/Support/Input.cpp", "\n// cache boundary control\n", {"compiler", "core"}),
            ("crates/zkc-tools/src/lib.rs", "\n// cache boundary control\n", {"tools", "rust", "core"}),
            ("Cargo.toml", None, {"tools", "rust", "core", "productDependencies", "testDependencies", "nativeSnapshot", "rustSnapshot"}),
        ]
        records = []
        for name, suffix, expected in cases:
            path = directory / name
            original = path.read_bytes()
            if suffix is None:
                # A manifest edition change must invalidate compiled Cargo
                # dependencies. Evaluation does not compile this control tree.
                modified = original.replace(b'edition = "2024"', b'edition = "2021"')
                if modified == original:
                    raise ValueError("Cargo manifest control did not change its input")
            else:
                modified = original + suffix.encode()
            path.write_bytes(modified)
            try:
                actual = identities(directory)
            finally:
                path.write_bytes(original)
            changed = {key for key in baseline if actual[key] != baseline[key]}
            records.append({"path": name, "expected": sorted(expected), "changed": sorted(changed)})
            (output / "invalidation.json").write_text(json.dumps(records, indent=2) + "\n")
            if changed != expected:
                raise ValueError(f"{name}: expected {sorted(expected)}, changed {sorted(changed)}")
            print(f"{name}: {', '.join(sorted(changed)) or 'no package invalidation'}", flush=True)


if __name__ == "__main__":
    try:
        main()
    except Interrupted as error:
        sys.exit(128 + error.signum)
    except subprocess.CalledProcessError as error:
        print(error.stderr or error, file=sys.stderr)
        sys.exit(error.returncode if error.returncode >= 0 else 128 - error.returncode)
