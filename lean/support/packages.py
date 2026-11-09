"""Owned package roots and exact local dependency graph."""
from pathlib import Path
import json
import tomllib

LEAN = Path(__file__).resolve().parents[1]
PACKAGES = {
    "program": (LEAN / "program", ("ZkcProgram",)),
    "main": (LEAN, ("Zkc", "ZkcExamples", "ZkcTools", "Tests")),
    "proof": (LEAN / "proof", ("ProtocolProof", "ProtocolProofExamples", "ProtocolProofChecks")),
    "security": (LEAN / "security", ("ZkcSecurity", "ZkcSecurityTools", "ZkcSecurityExamples", "TestsSecurity")),
    "arklib": (LEAN / "integrations/arklib", ("ZkcArkLib", "ZkcArkLibExamples", "TestsArkLib")),
    "clean": (LEAN / "integrations/clean", ("ZkcClean", "TestsClean", "CleanExamples", "CleanExamplesAudit")),
}
NAMES = {"program": "zkc_program", "main": "zkc", "proof": "protocol_proof",
         "security": "zkc_security", "arklib": "zkc_arklib", "clean": "zkc_clean"}
OPTIONAL = ("proof", "security", "arklib", "clean")
FORBIDDEN_DEPENDENCIES = {
    'program': {'mathlib', 'VCVio', 'PolyFun', 'CompPoly', 'Arklib', 'Clean',
                'zkc', 'protocol_proof', 'zkc_security', 'zkc_arklib', 'zkc_clean'},
    'main': {'Arklib', 'zkc_arklib', 'VCVio', 'Clean', 'PolyFun', 'CompPoly',
             'zkc_security', 'protocol_proof'},
    'proof': {'zkc', 'zkc_security', 'Arklib', 'zkc_arklib', 'Clean', 'zkc_clean'},
    'security': {'Arklib', 'zkc_arklib', 'Clean'},
    'arklib': {'Clean', 'zkc_clean'},
    'clean': {'Arklib', 'zkc_arklib', 'VCVio', 'PolyFun', 'zkc_security', 'protocol_proof'},
}

def is_owned_module(module):
    """Whether a module belongs to a maintained package rather than a provider."""
    root = module.split(".", 1)[0]
    return any(root in roots for _, roots in PACKAGES.values())


def module_package(module):
    """Resolve a maintained module through the shared ownership inventory."""
    root = module.split(".", 1)[0]
    owners = [directory for directory, roots in PACKAGES.values() if root in roots]
    if len(owners) != 1:
        raise ValueError(f"module has no unique maintained package: {module}")
    return owners[0]


def selected(integrations):
    result = ["program", "main"]
    if any(name in integrations for name in ("proof", "security", "arklib")):
        result.append("proof")
    if "security" in integrations or "arklib" in integrations:
        result.append("security")
    return result + [name for name in integrations if name not in result]

def closure(directory, ancestors=()):
    """Check every manifest path against its provider and every direct requirement against its lock."""
    directory = directory.resolve()
    if directory in ancestors:
        raise ValueError(f"cyclic path dependency: {directory}")
    manifest = json.loads((directory / "lake-manifest.json").read_text())
    config = tomllib.loads((directory / "lakefile.toml").read_text())
    if manifest['name'] != config['name']:
        raise ValueError(f"manifest package mismatch: {directory}")
    locks = {entry["name"]: entry for entry in manifest["packages"]}
    if len(locks) != len(manifest["packages"]):
        raise ValueError(f"duplicate locked dependency in {directory}")
    for dep in config.get("require", []):
        locked = locks.get(dep["name"])
        if locked is None:
            raise ValueError(f"missing locked dependency: {directory}: {dep['name']}")
        if "path" in dep:
            target = (directory / dep["path"]).resolve()
            if locked["type"] != "path" or (directory / locked["dir"]).resolve() != target:
                raise ValueError(f"path dependency mismatch: {dep['name']}")
            provider = tomllib.loads((target / "lakefile.toml").read_text())
            if provider["name"] != dep["name"]:
                raise ValueError(f"path provider mismatch: {dep['name']}")
        elif locked["type"] != "git" or locked["rev"] != dep["rev"]:
            raise ValueError(f"pin mismatch: {dep['name']}")
    names = set(locks)
    for dep in manifest["packages"]:
        if dep["type"] == "path":
            target = (directory / dep["dir"]).resolve()
            provider = tomllib.loads((target / "lakefile.toml").read_text())
            if provider['name'] != dep['name']:
                raise ValueError(f"locked path provider mismatch: {dep['name']}")
            names |= closure(target, (*ancestors, directory))
    return names


def check_closure(package, directory):
    """Reject forbidden dependencies even when no source currently imports them."""
    reached = closure(directory)
    if package == 'program' and reached:
        raise ValueError(f'program: the Lean/Std foundation must have no package dependencies: {sorted(reached)}')
    forbidden = FORBIDDEN_DEPENDENCIES[package]
    if reached & forbidden:
        raise ValueError(f'{package}: prohibited package closure: {sorted(reached & forbidden)}')
    return reached
