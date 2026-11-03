#!/usr/bin/env python3
"""Regenerate the compiler-produced interface fixtures from one compiler build.

The language-interface, Entry component and common-input fixtures under
compiler/test/fixtures, and the FRI interface read by the Rust SDK tests, are
compiler output. Each JSON interface records the producing build's toolchain
identity. Structural consumers take that identity as a fixture parameter, so a
compiler edit that changes only the identity needs no regeneration. Regenerate
when the interface schema, the native printing or a fixture's construction
changes.

Build the named compiler and its tests, then run from the checkout inside
nix develop:

    python3 scripts/regenerate-interface-fixtures.py build/compiler

Each compiler producer is a CTest executable that runs its cases and writes its
fixtures into the directory it is given. The SHA-256 tables of the fixture
guides are then recomputed from the written bytes; `just test-docs` compares
them with the files.
"""

import argparse
import hashlib
from pathlib import Path
import subprocess
import sys

from workspace import ROOT, checkout_path

sys.path.insert(0, str(ROOT / "common/tests"))
sys.path.insert(0, str(ROOT / "common/tests/support"))
from check_docs import fixture_digest_row, fixture_digest_tables  # noqa: E402
from project import project_arguments  # noqa: E402

PRODUCERS = {
    "compiler/test/fixtures/common-inputs": "zkc-common_interface-test",
    "compiler/test/fixtures/language-interface": "zkc-language_recursive_interface-test",
    "compiler/test/fixtures/entry-components": "zkc-language_entry_components_interface-test",
}
FRI = Path("crates/zkc/src/entry/interface/tests/fixtures/fri-interface.json")
FRI_PROJECT = Path("examples/projects/fri/zkc.toml")


def regenerate(build):
    for directory, producer in PRODUCERS.items():
        subprocess.run([build / "test" / producer, ROOT / directory], cwd=ROOT, check=True)
    command = [build / "zkc-compile", "language-interface", "--source-format=zkc",
               "--entry=example::Proof", *project_arguments(ROOT / FRI_PROJECT)]
    interface = subprocess.run(command, cwd=ROOT, check=True, stdout=subprocess.PIPE).stdout
    (ROOT / FRI).write_bytes(interface)


def record_digests(guide):
    """Rewrite every row of the guide's fixture digest tables from the bytes.

    Return the files whose recorded digest changed.
    """
    lines = guide.read_text().split("\n")
    tables = fixture_digest_tables(lines)
    if not tables:
        raise ValueError(f"{guide} has no fixture digest table")
    changed = []
    for _, rows in tables:
        for index, name, recorded in rows:
            if name is None:
                raise ValueError(f"{guide}:{index + 1}: malformed fixture digest row")
            digest = hashlib.sha256((guide.parent / name).read_bytes()).hexdigest()
            if digest != recorded:
                changed.append(guide.parent / name)
            lines[index] = fixture_digest_row(name, digest)
    guide.write_text("\n".join(lines))
    return changed


def main():
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("build", help="compiler build directory, such as build/compiler")
    args = parser.parse_args()
    build = checkout_path(args.build)
    tools = [build / "zkc-compile", *(build / "test" / name for name in PRODUCERS.values())]
    missing = [str(tool) for tool in tools if not tool.is_file()]
    if missing:
        parser.error("build the compiler and its tests first; missing " + ", ".join(missing))
    regenerate(build)
    for directory in [*map(Path, PRODUCERS), FRI.parent]:
        for path in record_digests(ROOT / directory / "README.md"):
            print(f"changed: {path.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
