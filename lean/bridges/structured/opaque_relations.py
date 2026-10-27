#!/usr/bin/env python3
"""Regenerate and check the generic opaque source boundary without provider builds."""

import argparse
import json
from pathlib import Path
import re
import subprocess
import tempfile

import snapshot

ROOT = Path(__file__).resolve().parents[3]
FIXTURES = ROOT / "lean/bridges/structured/fixtures"
DATA = ROOT / "lean/Tests/Generated/GenericOpaqueData.lean"


def run(command, *, cwd=ROOT):
    return subprocess.run(command, cwd=cwd, check=True, text=True, capture_output=True).stdout


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--compiler", type=Path, required=True)
    parser.add_argument("--write-fixtures", action="store_true")
    args = parser.parse_args()
    compiler = args.compiler.resolve()
    original = run([
        str(compiler), "language-emit", "--source-format=zkc",
        f"--module=opaque_example={FIXTURES / 'generic-opaque.zkc'}",
        "--subject=opaque_example::Run",
    ])
    symbols = re.findall(r'"protocol\.func"\(\) <\{.*?sym_name = "([^"]+)"', original, re.DOTALL)
    if len(symbols) != 1:
        raise ValueError("expected one retained source protocol")
    with tempfile.TemporaryDirectory(prefix="zkc-opaque-") as directory:
        path = Path(directory) / "original.mlir"
        path.write_text(original)
        exported = run([str(compiler), "protocol-structured", str(path), f"--symbol={symbols[0]}"])
    value = json.loads(exported)
    generated = snapshot.render(value, "Tests.Generated.GenericOpaqueData")
    for path, content in [
        (FIXTURES / "generic-opaque.mlir", original),
        (FIXTURES / "generic-opaque.json", exported),
        (DATA, generated),
    ]:
        if args.write_fixtures:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(content)
        elif not path.is_file() or path.read_text() != content:
            raise ValueError(f"stale opaque fixture: {path.relative_to(ROOT)}")
    print("generic opaque source export and constructor data agree")


if __name__ == "__main__":
    main()
