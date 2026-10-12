"""Explicit source-library dependencies for protocol test adapters."""

from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]


def finite_modules():
    """Capture the finite library closure used by AIR and FRI source modules."""
    names = ('accumulation', 'curve', 'finite', 'finite_domain', 'finite_math',
             'indices', 'sequence', 'vector')
    return [f'--module=zkc::{name}={ROOT}/libraries/zkc/{name}.zkc' for name in names]
