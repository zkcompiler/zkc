#!/usr/bin/env python3
"""Update the maintained Lean packages as one compatible dependency set.

Select an exact Mathlib commit and, when needed, exact ArkLib/Clean commits.
Mathlib selects the Lean release; each package keeps its own Lake manifest.
Resolve all four packages with that toolchain, verify common revisions, and
refresh Nix source hashes. Builds and proof audits remain separate checks.
A failed resolution leaves its edits available for inspection.
"""

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import tempfile
import tomllib
import urllib.request

ROOT = Path(__file__).resolve().parents[1]
MAIN = ROOT / "lean"
INTEGRATIONS = {"Arklib": MAIN / "integrations/arklib", "Clean": MAIN / "integrations/clean"}
SECURITY = MAIN / "security"
NIX_LEAN = ROOT / "nix/lean-toolchain.nix"
TOOLCHAIN = re.compile(r"leanprover/lean4:v(\d+\.\d+\.\d+(?:-rc\d+)?)")


def run(arguments, cwd=ROOT):
    print("+ " + " ".join(map(str, arguments)), flush=True)
    subprocess.run(list(map(str, arguments)), cwd=cwd, check=True)


REQUIREMENT = re.compile(r"^\[\[require\]\][^\n]*\n.*?(?=^\[|\Z)", re.M | re.S)


def requirement_block(text, name):
    """Locate one requirement without mistaking a library's name for it."""
    matches = [match for match in REQUIREMENT.finditer(text)
               if tomllib.loads(match.group())["require"][0].get("name") == name]
    if len(matches) != 1:
        raise ValueError(f"expected one git requirement named {name}, found {len(matches)}")
    return matches[0]


def required(lakefile, name):
    block = requirement_block(lakefile.read_text(), name).group()
    entry = tomllib.loads(block)["require"][0]
    if not entry.get("git") or not re.fullmatch(r"[0-9a-f]{40}", entry.get("rev", "")):
        raise ValueError(f"{lakefile}: {name} must select a full Git revision")
    return entry["git"], entry["rev"]


def set_required_rev(lakefile, name, old, new):
    text = lakefile.read_text()
    match = requirement_block(text, name)
    pattern = re.compile(rf'^(\s*rev\s*=\s*)"{re.escape(old)}"', re.M)
    block, count = pattern.subn(lambda m: f'{m[1]}"{new}"', match.group())
    if count != 1:
        raise ValueError(f"{lakefile}: cannot find the {name} revision {old}")
    lakefile.write_text(text[:match.start()] + block + text[match.end():])


def upstream_toolchain(url, rev):
    """Read the upstream toolchain at exactly the selected commit."""
    with tempfile.TemporaryDirectory(prefix="zkc-lean-upgrade-") as directory:
        subprocess.run(["git", "init", "-q", directory], check=True)
        subprocess.run(["git", "-C", directory, "fetch", "-q", "--depth", "1", url, rev], check=True)
        fetched = subprocess.run(["git", "-C", directory, "rev-parse", "FETCH_HEAD"],
                                 check=True, capture_output=True, text=True).stdout.strip()
        if fetched != rev:
            raise ValueError(f"fetched {fetched}, not the requested {rev}")

        def show(path):
            return subprocess.run(["git", "-C", directory, "show", f"FETCH_HEAD:{path}"],
                                  check=True, capture_output=True, text=True).stdout
        return show("lean-toolchain").strip()


def lean_archive_hash(version):
    url = (f"https://github.com/leanprover/lean4/releases/download/v{version}/"
           f"lean-{version}-linux.tar.zst")
    digest = hashlib.sha256()
    with urllib.request.urlopen(url, timeout=120) as response:
        for chunk in iter(lambda: response.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


def record_lean_hash(version, digest):
    text = NIX_LEAN.read_text()
    pattern = re.compile(r"(  hashes = \{\n)(.*?)(\n  \};)", re.S)
    if not pattern.search(text):
        raise ValueError(f"{NIX_LEAN} has no hashes attribute set to update")
    entry = f'    "{version}" = "sha256:{digest}";'
    NIX_LEAN.write_text(pattern.sub(lambda m: m.group(1) + entry + m.group(3), text, count=1))


def git_revisions(manifest):
    revisions = {}
    for package in manifest["packages"]:
        if package["type"] != "git":
            continue
        name, rev = package["name"], package["rev"]
        if name in revisions or not re.fullmatch(r"[0-9a-f]{40}", rev):
            raise ValueError(f"manifest has a duplicate or invalid revision for {name}")
        revisions[name] = rev
    return revisions


def check(toolchain, selected):
    main_pins = git_revisions(json.loads((MAIN / "lake-manifest.json").read_text()))
    shared = {}
    origins = {}
    for directory, expected in [(MAIN, {"mathlib": selected["mathlib"]}),
                                (SECURITY, {"mathlib": selected["mathlib"]}),
                                *((path, {name: selected[name], "mathlib": selected["mathlib"]})
                                  for name, path in INTEGRATIONS.items())]:
        if (directory / "lean-toolchain").read_text().strip() != toolchain:
            raise ValueError(f"{directory}: toolchain differs from the selected Mathlib release")
        manifest = json.loads((directory / "lake-manifest.json").read_text())
        resolved = git_revisions(manifest)
        for package in manifest["packages"]:
            if package["type"] != "git":
                continue
            name, url = package["name"], package.get("url")
            if name in origins and origins[name] != url:
                raise ValueError(f"{directory}: incompatible shared source URL: {name}")
            origins[name] = url
        for name, rev in expected.items():
            if resolved.get(name) != rev:
                raise ValueError(f"{directory}: {name} did not resolve to {rev}")
        missing = main_pins.keys() - resolved.keys()
        if missing:
            raise ValueError(f"{directory}: missing main dependencies: {sorted(missing)}")
        for name, rev in resolved.items():
            if name in shared and shared[name] != rev:
                raise ValueError(f"{directory}: incompatible shared dependency: {name}")
            shared[name] = rev
    print("all maintained Lean packages resolved consistently to the selected revisions")


def detach_dependency_links():
    """Lake update replaces changed checkouts; do not let it traverse shared sources."""
    for directory in [SECURITY, *INTEGRATIONS.values()]:
        packages = directory / ".lake/packages"
        if packages.is_dir():
            for package in packages.iterdir():
                if package.is_symlink():
                    package.unlink()


def main():
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--mathlib", required=True, help="full Mathlib commit; selects the Lean release")
    parser.add_argument("--arklib", help="full ArkLib commit (default: current requirement)")
    parser.add_argument("--clean", help="full Clean commit (default: current requirement)")
    args = parser.parse_args()
    selected = {"mathlib": args.mathlib, "Arklib": args.arklib, "Clean": args.clean}
    packages = {"mathlib": MAIN, **INTEGRATIONS}
    requirements = {name: required(path / "lakefile.toml", name) for name, path in packages.items()}
    for name, rev in selected.items():
        if rev is None:
            selected[name] = requirements[name][1]
        elif not re.fullmatch(r"[0-9a-f]{40}", rev):
            parser.error(f"{name} requires a full 40-character commit, not a branch or tag")
    toolchain = upstream_toolchain(requirements["mathlib"][0], selected["mathlib"])
    version = TOOLCHAIN.fullmatch(toolchain)
    if version is None:
        raise ValueError(f"unexpected Mathlib toolchain: {toolchain}")
    record_lean_hash(version.group(1), lean_archive_hash(version.group(1)))
    for name, directory in packages.items():
        (directory / "lean-toolchain").write_text(toolchain + "\n")
        set_required_rev(directory / "lakefile.toml", name, requirements[name][1], selected[name])
    for directory in [SECURITY, *INTEGRATIONS.values()]:
        (directory / "lean-toolchain").write_text(toolchain + "\n")
        lakefile = directory / "lakefile.toml"
        _, old_mathlib = required(lakefile, "mathlib")
        set_required_rev(lakefile, "mathlib", old_mathlib, selected["mathlib"])
    detach_dependency_links()
    run(["nix", "develop", f"{ROOT}#lean", "--command", "bash", "-e", "-c",
         "export MATHLIB_NO_CACHE_ON_UPDATE=1; "
         "cd lean; lake --keep-toolchain update; "
         "cd security; lake --keep-toolchain update; "
         "cd ../integrations/arklib; lake --keep-toolchain update; "
         "cd ../clean; lake --keep-toolchain update"])
    check(toolchain, selected)
    run(["nix", "develop", f"{ROOT}#maintenance", "--command",
         "python3", ROOT / "scripts/update-nix-sources.py", "--root", ROOT])


if __name__ == "__main__":
    main()
