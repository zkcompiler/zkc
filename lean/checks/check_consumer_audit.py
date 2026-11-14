#!/usr/bin/env python3
"""Run the declaration audit of a package outside Program's closure in a consumer workspace.

The declaration auditor is a Program tool, which a package outside Program's closure cannot
import, so audit_imports.py keeps only such a package's inventory in its tree. For each selected
package this check creates a Lake workspace that requires zkc_program, the package and the
packages it requires by path, writes into it the declaration audit and the command audits that
audit_imports.py generates for the package, builds them, and requires `<OWNER>-AUDIT-PASS`, the
dependency audit of every audit and the command audit of every executable of the package. Program's dependencies must already be
resolved; the auditor itself imports only Lean, so nothing of Mathlib is built.
"""

import argparse
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import support.evidence  # noqa: E402
import support.lake  # noqa: E402
from checks import audit_imports  # noqa: E402
from support.packages import (LEAN, NAMES, OWNERS, PACKAGES, audited,  # noqa: E402
                              package_directory, selected)

DEPENDENCY_FREE = tuple(name for name in PACKAGES if not audited(name))
MARKER = re.compile(r"^info: (\S+?\.lean):\d+:\d+: ([A-Z][A-Z-]*-AUDIT-PASS) "
                    r"declarations=(\d+) theorems=(\d+)$|"
                    r"^info: (\S+?\.lean):\d+:\d+: DEPENDENCY-AUDIT-PASS modules=(\d+)", re.M)


def workspace(name, target, root=LEAN):
    """Write the consumer workspace; return the audit modules and the expected markers."""
    program, package = package_directory("program", root), package_directory(name, root)
    # The package's own path dependencies are required by the workspace too, so that its
    # manifest locks every package that the build reaches.
    providers = [("program", program)] + [(member, package_directory(member, root))
                                          for member in selected([name])]
    tests = package.joinpath(*f"Zkc.Tests.{OWNERS[name]}".split("."))
    kept = audit_imports.expected(name, root)
    modules, required = [], {}
    for path, text in audit_imports.generated(name, root).items():
        if path in kept:
            continue
        relative = path.relative_to(tests)
        destination = target / relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_text(text)
        module = ".".join(relative.with_suffix("").parts)
        modules.append(module)
        marker = "COMMAND-AUDIT-PASS" if relative.parts[0] == "CommandAudits" else f"{name.upper()}-AUDIT-PASS"
        required[str(relative)] = [marker, "DEPENDENCY-AUDIT-PASS"]
    # The pin is shared by every maintained package; the audited package's copy selects it.
    shutil.copy2(package / "lean-toolchain", target / "lean-toolchain")
    (target / "lakefile.toml").write_text(
        f'name = "zkc_{name}_audit"\ndefaultTargets = ["Audits"]\n\n'
        + "".join(f'[[require]]\nname = {json.dumps(NAMES[provider])}\npath = {json.dumps(str(directory))}\n\n'
                  for provider, directory in providers)
        + f'[[lean_lib]]\nname = "Audits"\nroots = {json.dumps(sorted(modules))}\nallowNonModules = true\n')
    manifest = json.loads((program / "lake-manifest.json").read_text())
    manifest["name"] = f"zkc_{name}_audit"
    for provider, directory in providers:
        manifest["packages"].append({"type": "path", "name": NAMES[provider], "dir": str(directory),
                                     "inherited": False, "manifestFile": "lake-manifest.json",
                                     "configFile": "lakefile.toml"})
    packages = target / ".lake/packages"
    packages.mkdir(parents=True)
    for dependency in manifest["packages"]:
        if dependency["type"] != "git":
            continue
        dependency_name = dependency["name"].removeprefix("«").removesuffix("»")
        source = program / ".lake/packages" / dependency_name
        if not source.is_dir():
            raise ValueError(f"Program's dependency is not resolved: {source}")
        (packages / dependency_name).symlink_to(source.resolve())
    (target / "lake-manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    return sorted(modules), required


def check(names, output, lake="lake", root=LEAN):
    lake = str(Path(support.lake.resolve(lake)).absolute())
    environment = dict(os.environ)
    for key in ("LEAN_PATH", "LEAN_SRC_PATH", "LEAN_SYSROOT", "LAKE_HOME"):
        environment.pop(key, None)
    output.mkdir(parents=True, exist_ok=False)
    results = {}
    for name in names:
        if audited(name):
            raise ValueError(f"{name} reaches Program: its own build runs its declaration audit")
        target = output / name
        target.mkdir()
        modules, required = workspace(name, target, root)
        log_path = output / f"{name}.log"
        with log_path.open("w") as log:
            build = subprocess.run([lake, "--no-cache", "build"], cwd=target, env=environment,
                                   stdout=log, stderr=subprocess.STDOUT)
        found = {}
        for match in MARKER.finditer(log_path.read_text()):
            if match.group(1):
                found.setdefault(match.group(1), {})[match.group(2)] = {
                    "declarations": int(match.group(3)), "theorems": int(match.group(4))}
            else:
                found.setdefault(match.group(5), {})["DEPENDENCY-AUDIT-PASS"] = {"modules": int(match.group(6))}
        missing = [f"{module}: {marker}" for module, markers in required.items()
                   for marker in markers if marker not in found.get(module, {})]
        results[name] = {
            "status": "pass" if build.returncode == 0 and not missing else "fail",
            "exit_code": build.returncode, "audits": modules, "markers": found, "missing": missing,
            "log_sha256": support.lake.sha(log_path),
        }
    record = {"format": "zkc.consumer-audits.v0", "packages": results,
              "status": "pass" if all(result["status"] == "pass" for result in results.values()) else "fail",
              "scope": "all stored declarations of the selected packages, including private bodies, "
                       "audited through a workspace that also requires Program"}
    (output / "result.json").write_text(json.dumps(record, indent=2) + "\n")
    return record


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--package", action="append", choices=DEPENDENCY_FREE,
                        help="audit one package; repeat (default: every package outside Program's closure)")
    parser.add_argument("--output", type=Path, default=support.evidence.records("consumer-audits", ""))
    parser.add_argument("--lake", default="lake")
    args = parser.parse_args()
    record = check(args.package or list(DEPENDENCY_FREE), args.output.resolve(), args.lake)
    print(json.dumps(record, indent=2))
    raise SystemExit(0 if record["status"] == "pass" else 1)


if __name__ == "__main__":
    main()
