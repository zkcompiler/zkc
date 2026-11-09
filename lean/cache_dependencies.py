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
from support.compatibility import prepare
import subprocess

from support.lean_headers import HeaderParser
from support.packages import (LEAN, PACKAGES, add_selection, selection, package_modules,
                              selected, is_owned_module, module_owner)


def share_dependencies(main, optional):
    """Share only common Git providers with the same source identity and pin."""
    base = json.loads((main / "lake-manifest.json").read_text())
    extra = json.loads((optional / "lake-manifest.json").read_text())
    shared = {p["name"]: p for p in base["packages"] if p["type"] == "git"}
    links = []
    for package in extra["packages"]:
        if package["type"] != "git" or package["name"] not in shared:
            continue
        provider = shared[package["name"]]
        if (package["rev"] != provider["rev"] or
                package["url"].removesuffix(".git") != provider["url"].removesuffix(".git")):
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


def client_sources(headers, package):
    """Retain standalone consumers in a package that supplies all their imports."""
    available = set(selected([package]))
    result = []
    for path in sorted((LEAN / 'clients').glob('*.lean')):
        owners = {module_owner(module) for module in headers.imports(path.read_text(), path)
                  if is_owned_module(module)}
        if owners and owners <= available:
            result.append(path)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    add_selection(parser)
    parser.add_argument("--dry-run", action="store_true")
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--lake", default="lake")
    args = parser.parse_args()
    try:
        lake = support.lake.resolve(args.lake)
    except support.lake.Unavailable as absent:
        raise SystemExit(str(absent)) from None
    lake = str(Path(lake).absolute())
    packages = selection(args)
    roots, sources, runs, resolved = set(), {}, [], []
    exit_code = 0
    with HeaderParser(lake=lake) as headers:
        for name in packages:
            work = PACKAGES[name][0]
            for provider in resolved:
                share_dependencies(provider, work)
            raw = subprocess.check_output([lake, "env", "printenv", "LEAN_SRC_PATH"], cwd=work, text=True).strip()
            prepare(work)
            resolved.append(work)
            search = [(work / path).resolve() for path in raw.split(os.pathsep) if path]
            seeds = [*package_modules(name).values(), *client_sources(headers, name)]
            reached, parsed = collect(headers, seeds, search)
            roots.update(reached)
            for path, digest in parsed.items():
                if path in sources and sources[path] != digest:
                    raise ValueError(f"source changed during cache root selection: {path}")
                sources[path] = digest
            # Each package resolves its own upstream providers. A sibling's Lake
            # search path cannot stand in for this package's declared closure.
            command = [lake, "exe", "cache", "get", *reached] if reached else None
            code = subprocess.run(command, cwd=work, check=False).returncode if command and not args.dry_run else 0
            runs.append({"package": name, "directory": str(work), "command": command,
                         "mathlib_roots": reached, "exit_code": code})
            if code and not exit_code:
                exit_code = code
    drift = [path for path, digest in sources.items()
             if not Path(path).is_file() or hashlib.sha256(Path(path).read_bytes()).hexdigest() != digest]
    record = {
        "status": "pass" if exit_code == 0 and not drift else "fail",
        "packages": packages, "dry_run": args.dry_run, "runs": runs,
        "mathlib_roots": sorted(roots), "parsed_sources": sources,
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
