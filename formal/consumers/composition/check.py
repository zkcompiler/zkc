#!/usr/bin/env python3
"""Build and audit design experiments as a fresh independent Lake consumer.

Existing dependency objects may be reused. This checks current source inputs;
it does not overwrite or repin either historical formal review package.
"""

import argparse
import hashlib
import importlib.util
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
import support.evidence  # noqa: E402
import re
import shutil
import subprocess
import time


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
MODULES = ("Multilinear", "Claims", "Machine", "Controls")


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def inputs(formal):
    spec = importlib.util.spec_from_file_location("formal_reproduce", formal / "reproduce.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    result = {str(formal / path): digest for path, digest in module.build_inputs(formal).items()}
    for path in [HERE / "check.py", *(HERE / f"{name}.lean" for name in MODULES)]:
        result[str(path)] = sha(path)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=support.evidence.records("composition", ""))
    parser.add_argument("--formal", type=Path, default=ROOT / "formal")
    parser.add_argument("--lake", default="lake")
    args = parser.parse_args()
    formal = args.formal.resolve()
    lake = shutil.which(args.lake)
    if lake is None:
        raise SystemExit("selected Lake executable is unavailable")
    lake = str(Path(lake).absolute())
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    before = inputs(formal)
    (output / "inputs.json").write_text(json.dumps(before, indent=2) + "\n")
    client = output / "client"
    sources = client / "Composition"
    sources.mkdir(parents=True)
    for name in MODULES:
        shutil.copy2(HERE / f"{name}.lean", sources / f"{name}.lean")
    (sources / "Audit.lean").write_text(
        "".join(f"import Composition.{name}\n" for name in MODULES)
        + "import Tools.DeclarationAudit\n\n"
        + 'run_cmd Tools.DeclarationAudit.check [`Composition] "COMPOSITION-AUDIT-PASS"\n'
    )
    shutil.copy2(formal / "lean-toolchain", client / "lean-toolchain")
    (client / "lakefile.toml").write_text(
        'name = "zkc_composition"\ndefaultTargets = ["Composition"]\n\n'
        '[leanOptions]\nautoImplicit = false\nwarningAsError = true\n\n'
        '[[require]]\nname = "zkc"\npath = ' + json.dumps(str(formal)) + '\n\n'
        '[[lean_lib]]\nname = "Composition"\nglobs = ["Composition.+"]\n'
    )
    manifest = json.loads((formal / "lake-manifest.json").read_text())
    manifest["name"] = "zkc_composition"
    packages = client / ".lake/packages"
    packages.mkdir(parents=True)
    for package in manifest["packages"]:
        if package["type"] != "git":
            raise SystemExit("expected exact Git dependencies in the main manifest")
        name = package["name"].removeprefix("«").removesuffix("»")
        (packages / name).symlink_to((formal / ".lake/packages" / name).resolve())
    manifest["packages"].append({
        "type": "path", "name": "zkc", "dir": str(formal), "inherited": False,
        "manifestFile": "lake-manifest.json", "configFile": "lakefile.toml",
    })
    (client / "lake-manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    version = subprocess.check_output([lake, "env", "lean", "--version"], cwd=client, text=True).strip()
    started = time.monotonic()
    command = [lake, "--no-cache", "build"]
    log = output / "build.log"
    with log.open("w") as stream:
        run = subprocess.run(command, cwd=client, stdout=stream, stderr=subprocess.STDOUT, check=False)
    audit = re.search(r"COMPOSITION-AUDIT-PASS declarations=(\d+) theorems=(\d+)", log.read_text())
    after = inputs(formal)
    drift = [path for path in before.keys() | after.keys() if before.get(path) != after.get(path)]
    copied_drift = [name for name in MODULES
                    if sha(sources / f"{name}.lean") != before[str(HERE / f"{name}.lean")]]
    passed = run.returncode == 0 and audit is not None and not drift and not copied_drift
    record = {
        "format": "zkc.formal-composition.v1", "status": "pass" if passed else "fail",
        "command": command, "exit_code": run.returncode, "lean_version": version,
        "elapsed_seconds": round(time.monotonic() - started, 3),
        "modules": list(MODULES), "input_files": len(before),
        "source_drift": drift, "copied_source_drift": copied_drift,
        "audit": {"declarations": int(audit[1]), "theorems": int(audit[2])} if audit else None,
        "authored_theorems": sum(len(re.findall(r"^theorem ", (sources / f"{name}.lean").read_text(), re.M))
                                 for name in MODULES),
        "allowed_axioms": ["propext", "Classical.choice", "Quot.sound"],
        "log_sha256": sha(log), "inputs_sha256": sha(output / "inputs.json"),
        "scope": "design experiments against current source; dependency objects may be reused; "
                 "no production artifact, native correspondence, PCS or zkVM security claim",
    }
    (output / "result.json").write_text(json.dumps(record, indent=2) + "\n")
    print(json.dumps(record, indent=2))
    raise SystemExit(0 if passed else 1)


if __name__ == "__main__":
    main()
