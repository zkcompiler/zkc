#!/usr/bin/env python3
"""Rewrite the one PIR 0.0 dialect-version payload to 0.1."""

from pathlib import Path
import sys


if len(sys.argv) != 3:
    raise SystemExit("usage: rewrite-pir-minor.py INPUT OUTPUT")

source, destination = map(Path, sys.argv[1:])
data = source.read_bytes()

# Nested dialect-version section: kind 7, two-byte payload, then the MLIR
# one-byte varints for major 0 and minor 0. The fixture references only PIR as
# a versioned dialect, so requiring exactly one occurrence also protects this
# test from silently rewriting the wrong section after a bytecode-format change.
version_0_0 = b"\x07\x05\x01\x01"
version_0_1 = b"\x07\x05\x01\x03"
if data.count(version_0_0) != 1:
    raise SystemExit("expected exactly one PIR 0.0 dialect-version payload")
destination.write_bytes(data.replace(version_0_0, version_0_1))
