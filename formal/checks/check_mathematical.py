#!/usr/bin/env python3
"""Check mathematical canonical bytes against independent Lean encoding."""

from pathlib import Path
import subprocess
import sys


if __name__ == "__main__":
    root = Path(__file__).resolve().parents[2]
    subprocess.run([sys.executable, str(root / "tests/fixtures/mathematical/check.py"), "--lean"],
                   cwd=root, check=True)
