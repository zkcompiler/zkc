#!/usr/bin/env python3
"""Replace the stored artifact id without changing the bytecode length."""

from pathlib import Path
import sys


if len(sys.argv) != 3:
    raise SystemExit("usage: rewrite-id.py INPUT.mlirbc OUTPUT.mlirbc")

source = Path(sys.argv[1])
destination = Path(sys.argv[2])
artifact_id = source.name.removesuffix(".mlirbc")
if len(artifact_id) != 64 or any(c not in "0123456789abcdef" for c in artifact_id):
    raise SystemExit("input filename must be the current 64-hex artifact id")

data = source.read_bytes()
old = artifact_id.encode()
if data.count(old) != 1:
    raise SystemExit("artifact bytecode must contain its current id exactly once")
destination.write_bytes(data.replace(old, b"a" * 64))
