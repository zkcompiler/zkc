#!/usr/bin/env python3
"""Every statement of an upstream revision says the pinned one.

A revision this repository builds against is recorded once, in a pin
file, and then restated wherever a manifest, a fixture, a constant, or
a sentence needs it. Those restatements cannot all be removed — a Cargo
manifest reads no file, and a fixture carries the revision it was
captured against — so what is checked instead is that they agree, and
that each site is still there to agree.

Both directions matter. A site that stops carrying the pin has quietly
dropped out of the set the pin governs; a site that carries some other
revision is the drift the pin exists to prevent.

Usage: upstream-pins.py [REPO_ROOT]
"""

import re
import sys
from pathlib import Path

# Each pin file, the upstream it names, and every path that restates it.
PINS = {
    "arklib-pin.txt": (
        "ArkLib",
        [
            "registry/soundness-signature.json",
            "THIRD_PARTY.md",
        ],
    ),
    "plonky3-pin.txt": (
        "Plonky3",
        [
            "emit/Cargo.toml",
            "evaluation/fri-bench/Cargo.toml",
            "evaluation/upstream/plonky3-replay/Cargo.toml",
            "evaluation/upstream/plonky3-replay/README.md",
            "evaluation/upstream/plonky3-replay/src/lib.rs",
            "evaluation/upstream/plonky3-replay/src/bin/trace.rs",
            "evaluation/upstream/plonky3-replay/fixtures/duplex_babybear.json",
            "evaluation/upstream/plonky3-replay/fixtures/fib_babybear.json",
            "reference/oracle/babybear.py",
            "THIRD_PARTY.md",
        ],
    ),
}

root = Path(sys.argv[1] if len(sys.argv) > 1 else ".")
failures = []
stated = 0
# A file may state more than one upstream — the third-party notice
# states them all — so what is refused is a revision belonging to no
# pin, not a revision belonging to another one.
known = set()
for pin_name in PINS:
    revision = (root / pin_name).read_text(encoding="utf-8").strip()
    if re.fullmatch(r"[0-9a-f]{40}", revision):
        known.add(revision)
for pin_name, (subject, sites) in PINS.items():
    pin = (root / pin_name).read_text(encoding="utf-8").strip()
    if not re.fullmatch(r"[0-9a-f]{40}", pin):
        failures.append(f"{pin_name} does not hold a revision")
        continue
    for site in sites:
        path = root / site
        if not path.exists():
            failures.append(f"{site}: named as a pin site and absent")
            continue
        text = path.read_text(encoding="utf-8", errors="replace")
        if pin not in text:
            failures.append(f"{site}: does not carry the {subject} pin")
            continue
        stated += 1
        unpinned = sorted({rev for rev in re.findall(r"\b[0-9a-f]{40}\b", text)
                           if rev not in known})
        if unpinned:
            failures.append(
                f"{site}: states a revision no pin file records: "
                + ", ".join(unpinned))

if failures:
    for line in failures:
        print(line)
    raise SystemExit(1)
print(f"{stated} pin statements agree")
