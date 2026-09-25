#!/usr/bin/env python3
"""Select every Lean dependency revision from one ArkLib commit.

The main formal package and the optional ArkLib integration share Lean,
Mathlib and Mathlib's own dependencies; `formal/checks/check_library.py`
refuses differences in their shared dependencies. This coordinated upgrade
starts from one ArkLib commit: its `lean-toolchain` and
`lake-manifest.json` decide the Lean release, the Mathlib revision the main
package requires, and every revision the integration resolves.

In order, each step checked before the next:

1. read ArkLib's toolchain and manifest at the commit;
2. record the Lean release archive hash in nix/lean-toolchain.nix, so the Nix
   development shell can provide that release;
3. write both lean-toolchain files, the main package's Mathlib revision and
   the integration's ArkLib revision;
4. resolve both Lake manifests again (`lake update`) inside the development
   shell of the new release;
5. refresh the Nix transport hashes (scripts/update-nix-sources.py in the
   maintenance shell);
6. check that the shared revisions are the ones ArkLib's manifest selects.

Building and testing stay separate: validate the formal package and the
ArkLib integration after reviewing the resulting diff. Selecting compatible
dependencies does not establish that the project's proofs still build. Run
from any shell that has Nix; a failed resolution leaves its edits for review.
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
MAIN = ROOT / "formal"
INTEGRATION = MAIN / "integrations/arklib"
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


def upstream_files(url, rev):
    """ArkLib's lean-toolchain and lake-manifest.json at exactly this commit."""
    with tempfile.TemporaryDirectory(prefix="zkc-arklib-") as directory:
        subprocess.run(["git", "init", "-q", directory], check=True)
        subprocess.run(["git", "-C", directory, "fetch", "-q", "--depth", "1", url, rev], check=True)
        fetched = subprocess.run(["git", "-C", directory, "rev-parse", "FETCH_HEAD"],
                                 check=True, capture_output=True, text=True).stdout.strip()
        if fetched != rev:
            raise ValueError(f"fetched {fetched}, not the requested {rev}")

        def show(path):
            return subprocess.run(["git", "-C", directory, "show", f"FETCH_HEAD:{path}"],
                                  check=True, capture_output=True, text=True).stdout
        return show("lean-toolchain").strip(), json.loads(show("lake-manifest.json"))


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


def check(upstream_toolchain, upstream, arklib):
    wanted = git_revisions(upstream)
    for package in (MAIN, INTEGRATION):
        if (package / "lean-toolchain").read_text().strip() != upstream_toolchain:
            raise ValueError(f"{package / 'lean-toolchain'} differs from ArkLib's")
        resolved = git_revisions(json.loads((package / "lake-manifest.json").read_text()))
        required_names = {"mathlib"} if package == MAIN else set(wanted) | {"Arklib"}
        missing = required_names - resolved.keys()
        if missing:
            raise ValueError(f"{package}: missing resolved dependencies: {sorted(missing)}")
        if package == INTEGRATION and resolved["Arklib"] != arklib:
            raise ValueError(f"{package}: resolved ArkLib is not the selected commit")
        differing = {name: (rev, wanted[name]) for name, rev in resolved.items()
                     if name in wanted and wanted[name] != rev}
        if differing:
            raise ValueError(f"{package}: revisions differ from ArkLib's manifest: {differing}")
    print("every shared revision is the one ArkLib selects")


def main():
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--arklib", required=True, help="the full ArkLib commit to select from")
    args = parser.parse_args()
    if not re.fullmatch(r"[0-9a-f]{40}", args.arklib):
        parser.error("--arklib takes a full 40-character commit, not a branch or tag")

    url, current = required(INTEGRATION / "lakefile.toml", "Arklib")
    _, main_mathlib = required(MAIN / "lakefile.toml", "mathlib")
    toolchain, upstream = upstream_files(url, args.arklib)
    version = TOOLCHAIN.fullmatch(toolchain)
    if version is None:
        raise ValueError(f"unexpected ArkLib toolchain: {toolchain}")
    mathlib = git_revisions(upstream).get("mathlib")
    if mathlib is None:
        raise ValueError("ArkLib's manifest selects no Mathlib revision")

    record_lean_hash(version.group(1), lean_archive_hash(version.group(1)))
    for package in (MAIN, INTEGRATION):
        (package / "lean-toolchain").write_text(toolchain + "\n")
    set_required_rev(MAIN / "lakefile.toml", "mathlib", main_mathlib, mathlib)
    set_required_rev(INTEGRATION / "lakefile.toml", "Arklib", current, args.arklib)

    run(["nix", "develop", ROOT, "--command", "bash", "-c",
         "cd formal && lake update && cd integrations/arklib && lake update"])
    run(["nix", "develop", f"{ROOT}#maintenance", "--command",
         "python3", ROOT / "scripts/update-nix-sources.py", "--root", ROOT])
    check(toolchain, upstream, args.arklib)


if __name__ == "__main__":
    main()
