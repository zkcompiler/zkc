#!/usr/bin/env python3
"""Regenerate or exactly compare the registered full GKR connections.

Run from any directory. Uses the checkout's prepared Lake providers and outputs;
never copies objects from another checkout. Receipts account for source syntax,
not proof validity: build the named certificate/consumer targets independently.
"""
from argparse import ArgumentParser
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[3]
PACKAGE = ROOT / "lean/security"
BASELINE = PACKAGE / "checks/gkr-connection-baseline.json"
OWNER = "lean/security/checks/generate_gkr_connections.py"
OWNERSHIP = PACKAGE / "checks/gkr-connection-ownership.json"
INVENTORY = PACKAGE / "checks/gkr-connection-inventory.json"


def sha(data):
    return hashlib.sha256(data).hexdigest()


def record(path):
    data = path.read_bytes()
    return {"path": path.relative_to(ROOT).as_posix(), "sha256": sha(data),
            "bytes": len(data), "lines": len(data.splitlines())}


def imports(path):
    for line in path.read_text().splitlines():
        match = re.match(r"(?:(?:public|meta) )*import (?:all )?([A-Za-z0-9_.]+)$", line)
        if match:
            for base in (ROOT / "lean", PACKAGE):
                candidate = base.joinpath(*match[1].split(".")).with_suffix(".lean")
                if candidate.is_file():
                    yield candidate
                    break


def input_closure(seeds, outputs):
    found, todo = set(), list(seeds)
    while todo:
        path = todo.pop()
        if path in found or path in outputs:
            continue
        found.add(path)
        if path.suffix == ".lean":
            todo.extend(imports(path))
    return [record(path) for path in sorted(found)]


def inventory(outputs):
    baseline = json.loads(BASELINE.read_text())
    entries = []
    for row in baseline["paths"]:
        name = row["path"]
        path = ROOT / name
        entries.append({"path": name, "before_lines": row["lines"],
                        "before_sha256": row["sha256"], **{"after_" + k: v for k, v in
                        record(path).items() if k != "path"},
                        "after_owner": OWNER if path in outputs else "authored-library",
                        "disposition": "generated-concrete-installation" if path in outputs else
                        "retained-mathematics-source-presentation-or-import"})
    authored = [ROOT / name for name in [OWNER, "lean/security/checks/GenerateGkrConnections.lean",
        "lean/ZkcTools/ConstructionBindings/Common.lean",
        "lean/ZkcTools/ConstructionBindings/Analysis.lean",
        "lean/ZkcTools/ConstructionBindings/Frames.lean",
        "lean/Zkc/Construction/OriginalParticipant.lean",
        "lean/security/ZkcSecurity/Generation/GkrConnections.lean",
        "lean/security/ZkcSecurity/Generation/GkrConnectionTemplates.lean",
        "lean/security/ZkcSecurity/Realizations/Gkr/ConnectionTactics.lean",
        "lean/security/ZkcSecurity/Realizations/Gkr/OutputTemplate.lean",
        "lean/security/ZkcSecurity/Realizations/Gkr/LayoutVariant.lean",
        "lean/security/TestsSecurity/GkrStructuralGeneration.lean",
        "lean/security/TestsSecurity/ConstructionBindingsCertificates.lean",
        "lean/security/ZkcSecurity/Realizations/Gkr/README.md",
        "lean/docs/spec/fiat-shamir-security.md"]]
    return {"format": "zkc.gkr-connection-inventory/1", "baseline": baseline["source_revision"],
            "historical_baseline": record(BASELINE),
            "measurement": "Raw text lines, including whitespace and comments; not effort estimates.",
            "interpretation": "The original 2709 lines include legitimate mathematics and reusable rules. "
            "Generated schemas and shared tactics remain authored library work and are counted explicitly; "
            "this is a rebinding/ownership result, not a claim of zero family-specific code or reduced total LOC.",
            "before_linkage_files": len(entries),
            "before_linkage_lines": sum(entry["before_lines"] for entry in entries),
            "after_generated_linkage_lines": sum(entry["after_lines"] for entry in entries
                                                  if entry["after_owner"] == OWNER),
            "after_retained_authored_linkage_lines": sum(entry["after_lines"] for entry in entries
                                                          if entry["after_owner"] != OWNER),
            "paths": entries, "authored_installation_rules_controls_and_docs": [record(path) for path in authored],
            "generated_outputs_including_rebinding": [record(path) for path in sorted(outputs)]}


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="update owned files and committed manifests")
    parser.add_argument("--lake", default="lake", help="Lake executable for this checkout's toolchain")
    parser.add_argument("--receipts", type=Path, default=ROOT / "build/experiments/component-generation/regeneration")
    args = parser.parse_args()
    lake = shutil.which(str(args.lake))
    if lake is None:
        parser.error(f"selected Lake executable is unavailable: {args.lake}")
    lake = str(Path(lake).absolute())
    receipts = args.receipts.resolve()
    receipts.mkdir(parents=True, exist_ok=True)
    commands = []
    env = {**os.environ, "LEAN_NUM_THREADS": os.environ.get("LEAN_NUM_THREADS", "4")}

    def run(label, argv):
        log = receipts / (label + ".log")
        with log.open("w") as stream:
            result = subprocess.run([lake, *map(str, argv)], cwd=PACKAGE, env=env,
                                    stdout=stream, stderr=subprocess.STDOUT, check=False)
        commands.append({"argv": [lake, *map(str, argv)], "cwd": str(PACKAGE),
                         "LEAN_NUM_THREADS": env["LEAN_NUM_THREADS"], "exit_code": result.returncode,
                         "log": str(log), "log_sha256": sha(log.read_bytes())})
        (receipts / "commands.json").write_text(json.dumps(commands, indent=2) + "\n")
        if result.returncode:
            raise SystemExit(f"{label} failed; see {log}")

    run("prepare", ["build", "ZkcSecurity.Generation.GkrConnections",
                    "ZkcSecurity.Realizations.Gkr.ConnectionTactics",
                    "ZkcSecurity.Realizations.Gkr.OutputTemplate",
                    "ZkcSecurity.Realizations.Gkr.LayoutVariant", "Zkc.Construction.OriginalParticipant"])
    with tempfile.TemporaryDirectory(prefix="gkr-connections-", dir=receipts) as directory:
        generated = Path(directory)
        run("emit", ["env", "lean", "--run", "checks/GenerateGkrConnections.lean", generated])
        proposals = sorted(generated.rglob("*.lean"))
        if len(proposals) != 24:
            raise SystemExit(f"expected 24 views/connections, got {len(proposals)}")
        outputs, differences = set(), []
        for source in proposals:
            target = PACKAGE / source.relative_to(generated)
            outputs.add(target)
            if args.write:
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(source, target)
            if not target.is_file() or target.read_bytes() != source.read_bytes():
                differences.append(str(target.relative_to(ROOT)))
        if differences:
            raise SystemExit("generated source mismatch: " + ", ".join(differences))
        seeds = [PACKAGE / "checks/GenerateGkrConnections.lean",
                 PACKAGE / "ZkcSecurity/Realizations/Gkr/ConnectionTactics.lean",
                 PACKAGE / "ZkcSecurity/Realizations/Gkr/OutputTemplate.lean",
                 ROOT / "lean/Zkc/Construction/OriginalParticipant.lean", ROOT / OWNER, BASELINE]
        # The schema's explicit imports are proof dependencies as well as printer inputs.
        for source in outputs:
            seeds.extend(imports(source))
        ownership = {"format": "zkc.generator-ownership/1", "owner": OWNER,
                     "command": "python3 " + OWNER + " --write",
                     "comparison_command": "python3 " + OWNER,
                     "scope": "24 exact syntax outputs: two full installations and four whole artifact views. "
                     "Kernel checking is a separate required build, not implied by this comparison.",
                     "generated": [record(path)["path"] for path in sorted(outputs)],
                     "files": {record(path)["path"]: {"sha256": record(path)["sha256"],
                               "owners": [OWNER]} for path in sorted(outputs)},
                     "inputs": input_closure(seeds, outputs),
                     "outputs": [{**record(path), "owner": OWNER} for path in sorted(outputs)]}
        for path, value in [(OWNERSHIP, ownership), (INVENTORY, inventory(outputs))]:
            text = json.dumps(value, indent=2) + "\n"
            if args.write:
                path.write_text(text)
            elif not path.is_file() or path.read_text() != text:
                raise SystemExit(f"stale ownership/inventory: {path}; regenerate with --write")
        (receipts / "exact-comparison.json").write_text(json.dumps(
            {"passed": True, "exact_outputs": len(outputs), "ownership_sha256": sha(OWNERSHIP.read_bytes()),
             "inventory_sha256": sha(INVENTORY.read_bytes()),
             "descriptors": json.loads((generated / "descriptors.json").read_text())}, indent=2) + "\n")
        print(f"PASS: {len(outputs)} exact outputs; current ownership and authored inventory")


if __name__ == "__main__":
    main()
