#!/usr/bin/env python3
"""Emit measurement accounts from the installed roots' checked proof bodies.

Uses the existing isolated Lean overlay. Dependencies must already be built.
The inventory pins project import sources and their directly encountered
objects, including external imports; it does not traverse the external
packages' transitive object closure. This is attribution, not receipt
acceptance or a replacement for the package build.
"""
from argparse import ArgumentParser
import hashlib
import json
from pathlib import Path
import sys

LEAN = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(LEAN))
from bridges.structured.generate_component_roots import Generation  # noqa: E402
from support.evidence import records  # noqa: E402
from support.lean_headers import HeaderParser  # noqa: E402


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def inputs(generation, entry):
    """Lean parses import headers; Python only records paths and byte hashes."""
    pending = [entry]
    sources = {}
    objects = {}
    with HeaderParser(lean=generation.lean) as parser:
        while pending:
            path = pending.pop()
            if path in sources:
                continue
            sources[path] = digest(path)
            for module in parser.imports(path.read_text(), path):
                source = generation.module_path(module)
                if source.is_file():
                    pending.append(source)
                # Pin external objects too, without treating their source as
                # project-owned or traversing a second package's source tree.
                for suffix in (".olean", ".olean.private", ".ir"):
                    artifact = generation.output.joinpath(*module.split(".")).with_suffix(suffix)
                    if artifact.is_file():
                        objects[artifact] = digest(artifact)
    for package in (LEAN, generation.package):
        for name in ("lean-toolchain", "lakefile.toml", "lake-manifest.json"):
            path = package / name
            if path.is_file():
                sources[path] = digest(path)
    for path in (Path(__file__).resolve(),
                 LEAN / "bridges/structured/generate_component_roots.py",
                 LEAN / "support/lean_headers.py"):
        sources[path] = digest(path)
    return sources, objects


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=records("derivation-accounts"))
    parser.add_argument("--dependency-path", type=Path, action="append", default=[])
    args = parser.parse_args()
    args.check = False
    generation = Generation(args)
    entry = generation.package / "checks/DerivationAccounts.lean"
    report = {"format": "zkc.derivation-account-check/0", "status": "failed",
              "acceptance_authority": False,
              "dependency_policy": "existing checked objects; project import sources and directly encountered objects pinned; transitive external objects not inventoried"}
    destination = generation.directory / "validation.json"
    try:
        for module in ("ZkcTools.ProofAccount", "Tests.ProofAccount",
                       "ZkcSecurity.Generation.SumcheckAccounts"):
            generation.compile(module)
        sources, objects = inputs(generation, entry)
        output = generation.directory / "accounts.json"
        generation.execute([generation.lean, "--run", entry, output], generation.package)
        if any(digest(path) != pin for path, pin in (sources | objects).items()):
            raise ValueError("a source or checked object changed during measurement")
        accounts = json.loads(output.read_text())
        report.update(status="pass", accounts={"path": str(output), "sha256": digest(output)},
                      sources={str(path): pin for path, pin in sources.items()},
                      objects={str(path): pin for path, pin in objects.items()},
                      counts=[{"root": row["root"], "occurrences": len(row["source_occurrences"]),
                               "obligations": len(row["obligations"]),
                               "shared_proof_bindings": len(row["proof_bindings"])} for row in accounts])
    except Exception as error:
        report["error"] = str(error)
        raise
    finally:
        report["commands"] = generation.commands
        destination.write_text(json.dumps(report, indent=2) + "\n")
    print(f"Derivation measurement passed: {destination}")


if __name__ == "__main__":
    main()
