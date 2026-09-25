#!/usr/bin/env python3
"""Fetch only the Mathlib cache roots reached by maintained package sources.

Uses the selected Lean header parser and Lake source search path, traversing
optional upstream imports until a Mathlib boundary. Lake still builds every
declared target and any uncached dependencies. This is a cache optimization,
not an admission or proof check. --dry-run skips compiled-cache downloads;
Lake may still resolve missing pinned source dependencies.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path

import support.lake
import subprocess

from support.lean_headers import HeaderParser


ROOT = Path(__file__).resolve().parent


def share_dependencies(main, optional):
    """Share exact common sources/objects and keep standalone main clients usable."""
    base = json.loads((main / "lake-manifest.json").read_text())
    extra = json.loads((optional / "lake-manifest.json").read_text())
    shared = {p["name"]: p for p in base["packages"] if p["type"] == "git"}
    links = []
    for package in extra["packages"]:
        if package["type"] != "git" or package["name"] not in shared:
            continue
        if package["rev"] != shared[package["name"]]["rev"]:
            raise ValueError(f"incompatible shared dependency: {package['name']}")
        name = package["name"].removeprefix("«").removesuffix("»")
        source = main / base["packagesDir"] / name
        if not source.is_dir():
            raise ValueError(f"main dependency was not resolved: {name}")
        links.append((optional / extra["packagesDir"] / name, source))
    for target, source in links:
        if not target.exists() and not target.is_symlink():
            target.parent.mkdir(parents=True, exist_ok=True)
            target.symlink_to(source.resolve())


def collect(headers, seeds, search):
    pending = list(seeds)
    seen = {}
    mathlib = set()
    while pending:
        path = pending.pop().resolve()
        if str(path) in seen:
            continue
        source = path.read_text()
        seen[str(path)] = hashlib.sha256(path.read_bytes()).hexdigest()
        for name in headers.imports(source, path):
            if name == "Mathlib" or name.startswith("Mathlib."):
                mathlib.add(name)
            elif name.split(".")[0] not in ("Init", "Lean", "Std", "Lake"):
                relative = Path(*name.split(".")).with_suffix(".lean")
                target = next((base / relative for base in search if (base / relative).is_file()), None)
                if target is None:
                    raise ValueError(f"cannot resolve source import {name} from {path}")
                pending.append(target)
    return sorted(mathlib), seen


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--with-arklib", action="store_true")
    parser.add_argument("--dry-run", action="store_true")
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--lake", default="lake")
    args = parser.parse_args()
    try:
        lake = support.lake.resolve(args.lake)
    except support.lake.Unavailable as absent:
        raise SystemExit(str(absent)) from None
    lake = str(Path(lake).absolute())
    work = ROOT
    raw = subprocess.check_output([lake, "env", "printenv", "LEAN_SRC_PATH"], cwd=work, text=True).strip()
    if args.with_arklib:
        work = ROOT / "integrations/arklib"
        share_dependencies(ROOT, work)
        raw = subprocess.check_output([lake, "env", "printenv", "LEAN_SRC_PATH"], cwd=work, text=True).strip()
    search = [(work / path).resolve() for path in raw.split(os.pathsep) if path]
    seeds = [ROOT / "Zkc.lean", ROOT / "clients/Main.lean"]
    for directory in ("Zkc", "Tests", "Examples", "Tools"):
        seeds.extend((ROOT / directory).rglob("*.lean"))
    if args.with_arklib:
        seeds.append(ROOT / "clients/ArkLib.lean")
        for directory in ("ZkcArkLib", "TestsArkLib"):
            entry = work / f"{directory}.lean"
            if entry.is_file():
                seeds.append(entry)
            seeds.extend((work / directory).rglob("*.lean"))
    with HeaderParser(root=work, lake=lake) as headers:
        roots, sources = collect(headers, seeds, search)
    # Never turn an empty selection into Mathlib's implicit "download all".
    command = [lake, "exe", "cache", "get", *roots] if roots else None
    exit_code = 0
    if command and not args.dry_run:
        exit_code = subprocess.run(command, cwd=work, check=False).returncode
    drift = [path for path, digest in sources.items()
             if not Path(path).is_file() or hashlib.sha256(Path(path).read_bytes()).hexdigest() != digest]
    record = {
        "status": "pass" if exit_code == 0 and not drift else "fail",
        "with_arklib": args.with_arklib, "dry_run": args.dry_run,
        "command": command, "mathlib_roots": roots, "parsed_sources": sources,
        "source_drift": drift, "exit_code": exit_code,
        "scope": "cache root selection only; builds and proof audits remain separate",
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(record, indent=2) + "\n")
    print(json.dumps({"status": record["status"], "mathlib_roots": len(roots),
                      "parsed_sources": len(sources), "dry_run": args.dry_run}))
    raise SystemExit(0 if record["status"] == "pass" else 1)


if __name__ == "__main__":
    main()
