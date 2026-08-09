#!/usr/bin/env python3
"""Rewrite the single stored OIR id to an explicit id or id-file value."""

from pathlib import Path
import re
import sys


if len(sys.argv) != 4:
    raise SystemExit("usage: rewrite-oir-id.py INPUT OUTPUT ID-OR-ID-FILE")

source = Path(sys.argv[1])
destination = Path(sys.argv[2])
id_arg = Path(sys.argv[3])
artifact_id = (
    id_arg.read_text(encoding="utf-8").strip()
    if id_arg.is_file()
    else sys.argv[3]
)
if not re.fullmatch(r"[0-9a-f]{64}", artifact_id):
    raise SystemExit("replacement id must be exactly 64 lowercase hex digits")

text = source.read_text(encoding="utf-8")
rewritten, count = re.subn(
    r'(?m)(^\s*oir\.artifact\b[^\n]*\bid ")[0-9a-f]{64}(")',
    lambda match: match.group(1) + artifact_id + match.group(2),
    text,
    count=1,
)
if count != 1:
    raise SystemExit("input must contain exactly one rewriteable OIR id")
destination.write_text(rewritten, encoding="utf-8")
