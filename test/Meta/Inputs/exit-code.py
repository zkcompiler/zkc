#!/usr/bin/env python3
"""Run a command and require an exact exit status.

lit's `not` accepts any non-zero status, which is the distinction the
tools' exit codes exist to make: 1 says the subject was examined and
refused, 2 says the invocation never reached it. A check that accepts
either cannot see the two swap.

Usage: exit-code.py EXPECTED COMMAND [ARG...]
"""

import subprocess
import sys

expected = int(sys.argv[1])
command = sys.argv[2:]
if not command:
    raise SystemExit("exit-code.py: no command given")

result = subprocess.run(command, capture_output=True, text=True)
if result.returncode == expected:
    sys.exit(0)

print(
    "exit-code: %s\n  expected status %d, got %d"
    % (" ".join(command), expected, result.returncode),
    file=sys.stderr,
)
for stream, text in (("stdout", result.stdout), ("stderr", result.stderr)):
    if text.strip():
        print("  %s: %s" % (stream, text.strip().splitlines()[0]), file=sys.stderr)
sys.exit(1)
