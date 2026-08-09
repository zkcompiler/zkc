#!/usr/bin/env python3
"""Rewrite the single stored PIR artifact id to an explicit value."""

from pathlib import Path
import re
import sys


if len(sys.argv) != 4:
    raise SystemExit("usage: rewrite-pir-id.py INPUT OUTPUT ID")

artifact_id = sys.argv[3]
if not re.fullmatch(r"[0-9a-f]{64}", artifact_id):
    raise SystemExit("replacement id must be exactly 64 lowercase hex digits")

source = Path(sys.argv[1]).read_text(encoding="utf-8")
rewritten, count = re.subn(
    r'(?m)(^\s*pir\.sealed\b[^\n]*\bid ")[0-9a-f]{64}(")',
    lambda match: match.group(1) + artifact_id + match.group(2),
    source,
    count=1,
)
if count != 1:
    raise SystemExit("input must contain exactly one rewriteable PIR id")
Path(sys.argv[2]).write_text(rewritten, encoding="utf-8")
