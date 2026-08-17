#!/usr/bin/env python3
"""Rewrite the single stored artifact id in a textual module.

Both carriers store an identity the same way — a `sealed`/`artifact`
line naming a digest — so both are rewritten the same way, and the op
whose line is meant is the argument rather than the script. The
replacement may be given directly or as a file containing it, which is
what a test that just computed an id has in hand.

Usage: rewrite-artifact-id.py OP INPUT OUTPUT (ID | ID_FILE)
  OP is `pir.sealed` or `oir.artifact`.
"""

from pathlib import Path
import re
import sys

if len(sys.argv) != 5:
    raise SystemExit(__doc__)

op, source, destination = sys.argv[1], Path(sys.argv[2]), Path(sys.argv[3])
if op not in ("pir.sealed", "oir.artifact"):
    raise SystemExit(f"unknown carrier op {op!r}")

given = Path(sys.argv[4])
artifact_id = (
    given.read_text(encoding="utf-8").strip() if given.is_file() else sys.argv[4]
)
if not re.fullmatch(r"[0-9a-f]{64}", artifact_id):
    raise SystemExit("replacement id must be exactly 64 lowercase hex digits")

rewritten, count = re.subn(
    r'(?m)(^\s*' + re.escape(op) + r'\b[^\n]*\bid ")[0-9a-f]{64}(")',
    lambda match: match.group(1) + artifact_id + match.group(2),
    source.read_text(encoding="utf-8"),
    count=1,
)
if count != 1:
    raise SystemExit(f"input must contain exactly one rewriteable {op} id")
destination.write_text(rewritten, encoding="utf-8")
