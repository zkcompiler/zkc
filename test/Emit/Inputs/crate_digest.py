"""Digest every file the emitter wrote into a crate.

The emitter walk's characterization gate: a refactor of the walk must
leave the emitted bytes identical, and an intended emitter change
re-mints the pin deliberately. Enumerating a couple of files by name
would leave the rest of the walk's output ungated, so this walks the
tree and states its exclusions instead:

  - `target/` and `Cargo.lock` are cargo's, written when the emitted
    crate's own conformance suite runs, not by the emitter;
  - the manifest's `zkc-rt` path is where the runtime happens to live on
    the machine that ran the emitter, so it is normalized rather than
    dropped — everything else in the manifest (crate name, edition,
    feature selection) is emitter output worth pinning.

Prints `<sha256>  <relative path>` per file, ordered by path, which is
what the pin files hold. Ordering by path rather than by digest keeps a
content change to one file a one-line diff instead of a reordering.
"""

import hashlib
import re
import sys
from pathlib import Path

# Written by cargo, not by the emitter.
EXCLUDED_DIRS = {"target"}
EXCLUDED_FILES = {"Cargo.lock"}

# The one machine-dependent field the emitter writes.
RT_PATH = re.compile(rb'path = "[^"]*"')


def normalized(path: Path, relative: str) -> bytes:
    payload = path.read_bytes()
    if relative == "Cargo.toml":
        payload = RT_PATH.sub(b'path = "<rt>"', payload)
    return payload


def main() -> None:
    if len(sys.argv) != 2:
        raise SystemExit("usage: crate_digest.py CRATE_DIR")
    root = Path(sys.argv[1])
    if not root.is_dir():
        raise SystemExit(f"{root} is not a directory")
    rows = []
    for path in root.rglob("*"):
        if not path.is_file():
            continue
        relative = path.relative_to(root)
        # Directory components only: a file that happened to be named
        # `target` is emitter output like any other.
        if EXCLUDED_DIRS.intersection(relative.parts[:-1]):
            continue
        if relative.name in EXCLUDED_FILES:
            continue
        key = relative.as_posix()
        digest = hashlib.sha256(normalized(path, key)).hexdigest()
        rows.append((key, digest))
    if not rows:
        raise SystemExit(f"{root} holds no emitted files")
    print("\n".join(f"{digest}  {key}" for key, digest in sorted(rows)))


if __name__ == "__main__":
    main()
