"""Owned package roots and exact local dependency graph."""
from pathlib import Path
import json
import tomllib

LEAN = Path(__file__).resolve().parents[1]
PACKAGES = {
    "main": (LEAN, ("Zkc", "ZkcExamples", "ZkcTools", "Tests")),
    "security": (LEAN / "security", ("ZkcSecurity", "TestsSecurity")),
    "arklib": (LEAN / "integrations/arklib", ("ZkcArkLib", "TestsArkLib")),
    "clean": (LEAN / "integrations/clean", ("ZkcClean", "TestsClean", "CleanExamples", "CleanExamplesAudit")),
}
NAMES = {"main": "zkc", "security": "zkc_security", "arklib": "zkc_arklib", "clean": "zkc_clean"}
FORBIDDEN_DEPENDENCIES = {
    'main': {'Arklib', 'zkc_arklib', 'VCVio', 'Clean', 'PolyFun', 'CompPoly', 'zkc_security'},
    'security': {'Arklib', 'zkc_arklib', 'Clean'},
    'arklib': {'Clean', 'zkc_clean'},
    'clean': {'Arklib', 'zkc_arklib', 'VCVio', 'PolyFun', 'zkc_security'},
}

def selected(integrations):
    result = ["main"]
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
    locks = {entry["name"]: entry for entry in manifest["packages"]}
    if len(locks) != len(manifest["packages"]):
        raise ValueError(f"duplicate locked dependency in {directory}")
    for dep in config.get("require", []):
        locked = locks[dep["name"]]
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
            names |= closure(target, (*ancestors, directory))
    return names


def check_closure(package, directory):
    """Reject forbidden dependencies even when no source currently imports them."""
    reached = closure(directory)
    forbidden = FORBIDDEN_DEPENDENCIES[package]
    if reached & forbidden:
        raise ValueError(f'{package}: prohibited package closure: {sorted(reached & forbidden)}')
    return reached
