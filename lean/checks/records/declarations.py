"""Run the declaration-record emitter and read its output.

The emitter (`lean/checks/DeclarationRecords.lean`) writes one JSON line per
declaration written in the source of a package's module families, after a
header line. A package is selected by name; its families mirror the
declaration audit's scopes.
"""

import json
from pathlib import Path
import subprocess

LEAN = Path(__file__).resolve().parents[2]
EMITTER = LEAN / "checks/DeclarationRecords.lean"
ALLOWED_AXIOMS = ("propext", "Classical.choice", "Quot.sound")
FORMAT = "zkc.declarations/0"

# Each package: its directory and the source directories or files it owns,
# as the declaration audit selects them. Executable roots, which define
# `main`, are selected by their library directories.
PACKAGES = {
    "main": (LEAN, ["Zkc", "ZkcExamples", "Tests", "ZkcTools/CommonSource/Reference.lean",
                    "ZkcTools/JsonSupport.lean", "ZkcTools/ProofAccount.lean",
                    "ZkcTools/StructuredSource",
                    "ZkcTools/ConstructionBindings"]),
    "security": (LEAN / "security", ["ZkcSecurity", "TestsSecurity"]),
    "arklib": (LEAN / "integrations/arklib", ["ZkcArkLib", "TestsArkLib"]),
    "clean": (LEAN / "integrations/clean", ["ZkcClean", "TestsClean"]),
}
# The registry tables the emitter evaluates where the package defines them.
REGISTRY = {"security": ("ZkcSecurity.Registry.table", "ZkcSecurity.Registry.endpoints"),
            "arklib": ("ZkcArkLib.Registry.reportTable", "ZkcArkLib.Registry.reportEndpoints")}


def emit(package, output, *, lake="lake", baseline=None, details=(), log=None):
    """Run the emitter for one package; return the completed process."""
    directory, sources = PACKAGES[package]
    # Lake invalidates the tool when its sources or imports change. Its output
    # is never cached: each invocation reads the actual stored proof bodies in
    # the audited package's environment, including private/opaque declarations.
    built = subprocess.run([lake, "build", "declaration-records"], cwd=LEAN,
                           stdout=log, stderr=subprocess.STDOUT if log else None, text=True)
    success = built.returncode == 0
    if not success:
        return built
    # Dynamic imports are outside the executable's own import graph. Refresh
    # the audited package as well, so fresh records cannot describe stale proofs.
    built = subprocess.run([lake, "build"], cwd=directory, stdout=log,
                           stderr=subprocess.STDOUT if log else None, text=True)
    success = built.returncode == 0
    if not success:
        return built
    command = [lake, "env", str(LEAN / ".lake/build/bin/declaration-records")]
    if baseline is not None:
        command += ["--check", str(baseline)]
    if package in REGISTRY:
        table, endpoints = REGISTRY[package]
        command += ["--registry", table, "--endpoints", endpoints]
    for name in details:
        command += ["--detail", name]
    command += [str(output), *sources]
    output.parent.mkdir(parents=True, exist_ok=True)
    return subprocess.run(command, cwd=directory, stdout=log, stderr=subprocess.STDOUT if log else None,
                          text=True)


class Records:
    """The emitted records of one or more packages, indexed by name."""

    def __init__(self, headers=None, declarations=None):
        self.headers = headers or {}
        self.declarations = declarations or []
        self.by_name = {}
        for record in self.declarations:
            if "private" not in record.get("tags", []):
                self.by_name.setdefault(record["name"], record)

    @classmethod
    def load(cls, paths):
        headers, declarations = {}, []
        for package, path in paths.items():
            lines = Path(path).read_text().splitlines()
            header = json.loads(lines[0])
            if header.get("format") != FORMAT:
                raise ValueError(f"{path}: not a {FORMAT} document")
            headers[package] = header
            for line in lines[1:]:
                record = json.loads(line)
                record["package"] = package
                declarations.append(record)
        return cls(headers, declarations)

    def get(self, name):
        return self.by_name.get(name)

    def packages(self):
        return set(self.headers)

    def registry(self):
        """Combine compatible registry metadata from every emitted package."""
        entries, schemas, endpoints = {}, {}, {}
        found = False
        for header in self.headers.values():
            registry = header.get("registry")
            if registry is None:
                continue
            found = True
            for entry in registry:
                identifier = entry["identifier"]
                if identifier in entries and entries[identifier] != entry:
                    raise ValueError(f"conflicting registry identifier: {identifier}")
                schema = entry.get("schema")
                if schema and schema in schemas and schemas[schema] != entry:
                    raise ValueError(f"conflicting registry schema: {schema}")
                if schema:
                    schemas[schema] = entry
                entries[identifier] = entry
            for entry in header.get("endpoints") or []:
                key = (entry["endpoint"], entry["property"], entry["statement"])
                if key in endpoints and endpoints[key] != entry:
                    raise ValueError(f"conflicting registered endpoint: {key}")
                endpoints[key] = entry
        return (list(entries.values()) if found else None), list(endpoints.values())



def forbidden_axioms(record):
    return [name for name in record.get("axioms", []) if name not in ALLOWED_AXIOMS]
