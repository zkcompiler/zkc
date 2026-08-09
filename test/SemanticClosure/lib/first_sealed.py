#!/usr/bin/env python3
"""Print the first `pir.sealed` container from a multi-protocol module.

A fixture that seals two protocols to compare their identities produces one
module holding both. A parity leg needs exactly one container, so this cuts at
the next container's own header rather than balancing braces — the header is
unambiguous, while a sealed op's first brace group is its kappa dictionary and
not its region.
"""

import sys
from pathlib import Path

text = Path(sys.argv[1]).read_text()
first = text.find("pir.sealed")
if first < 0:
    raise SystemExit("no pir.sealed container in the module")
second = text.find("pir.sealed", first + 1)
print(text[first:second if second >= 0 else len(text)].rstrip())
