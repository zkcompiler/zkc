#!/usr/bin/env python3
"""Every statement of an upstream revision says the registered one.

A revision cannot be stated only once. A Cargo manifest reads no file, a
captured fixture carries the revision it was captured against, and a
third-party notice has to name what it notices. So the revision is
decided in one registry, and the restatements are held to it.

What this does *not* do is keep a list of the places that restate it.
A list has to be remembered, and a site nobody remembered is a site the
check silently passes over — which is the failure mode a check like
this usually dies of. Instead:

  * Every `rev = "..."` in every Cargo manifest is found, wherever the
    manifest is, and must name a registered revision. That is where the
    restatements concentrate and where new ones appear, and it needs no
    list at all.
  * Every registered revision must be reached by one of those, so an
    entry for an upstream nothing depends on fails rather than lingers.
    Not every upstream is a Cargo dependency — the formalization corpus
    is a Lean project — so a marker counts as a dependant too.
  * Anything else that wants to be checked says so itself, by carrying
    `upstream-pin: <name>` on the line or in the file. The site
    registers itself; nobody maintains a register of sites.

Usage: upstream-pins.py [REPO_ROOT]
"""

import json
import re
import sys
from pathlib import Path

CARGO_REVISION = re.compile(r'\brev\s*=\s*"([0-9a-f]{40})"')
MARKER = re.compile(r"upstream-pin:\s*([a-z0-9_-]+)")
SKIP = {".git", "build", "target", "node_modules", ".claude", "generated"}

root = Path(sys.argv[1] if len(sys.argv) > 1 else ".")
registry = json.loads((root / "registry" / "upstreams.json").read_text())
if registry.get("schema") != "zkc.upstream_pins":
    raise SystemExit("registry/upstreams.json is not an upstream-pin registry")

revisions = {}
for name, entry in registry["upstreams"].items():
    revision = entry.get("revision", "")
    if not re.fullmatch(r"[0-9a-f]{40}", revision):
        raise SystemExit(f"upstream {name!r} records no revision")
    revisions[name] = revision
known = set(revisions.values())

failures = []
reached = set()
checked = 0


def walk(directory):
    for path in sorted(directory.iterdir()):
        if path.name in SKIP:
            continue
        if path.is_dir():
            yield from walk(path)
        elif path.is_file():
            yield path


for path in walk(root):
    where = path.relative_to(root).as_posix()
    if path.name == "Cargo.lock":
        continue
    try:
        text = path.read_text(encoding="utf-8")
    except (UnicodeDecodeError, OSError):
        continue

    if path.name == "Cargo.toml":
        for revision in CARGO_REVISION.findall(text):
            checked += 1
            if revision in known:
                reached.add(revision)
            else:
                failures.append(
                    f"{where}: depends on revision {revision}, which "
                    "registry/upstreams.json does not record")

    for line in text.splitlines():
        marker = MARKER.search(line)
        if not marker:
            continue
        name = marker.group(1)
        if name not in revisions:
            failures.append(
                f"{where}: claims the pin of upstream {name!r}, which is not "
                "registered")
            continue
        checked += 1
        if revisions[name] in text:
            reached.add(revisions[name])
        else:
            failures.append(
                f"{where}: claims the {name} pin and does not carry it")

for name, revision in revisions.items():
    if revision not in reached:
        failures.append(
            f"upstream {name!r} is registered and nothing depends on it: no "
            "Cargo manifest names its revision and no file claims its pin")

if failures:
    for line in failures:
        print(line)
    raise SystemExit(1)
print(f"{checked} statements agree with {len(revisions)} registered upstreams")
