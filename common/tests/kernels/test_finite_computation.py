"""Handwritten finite IR through independent compilation and native execution."""
import sys
from pathlib import Path


def test_finite_computations(toolchain, journal, directory):
    root = Path(__file__).resolve().parents[3]
    journal.run([
        sys.executable, root / 'compiler/test/support/finite_runtime.py',
        '--compiler', toolchain.compiler, '--runtime', toolchain.runtime,
        '--output', directory / 'finite', '--checked-access',
    ], timeout=600)
