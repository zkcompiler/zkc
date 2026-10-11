"""Independent accumulator-machine reference and reduction helpers."""
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[3]
ADAPTER = ROOT / 'compiler/adapters/accumulator-machine'
sys.path.insert(0, str(ADAPTER))

import accumulator_machine as machine  # noqa: E402
import interaction_reductions as reductions  # noqa: E402
import regenerate  # noqa: E402
from ring_arena import (  # noqa: E402
    BASE, EXTENSION, ONE, P, Refusal,
    add, compact, decode, encode, inverses,
    mul, scalar, sub,
)


__all__ = [
    'ADAPTER', 'machine', 'reductions', 'regenerate', 'BASE',
    'EXTENSION', 'ONE', 'P', 'Refusal', 'add',
    'compact', 'decode', 'encode', 'inverses', 'mul',
    'scalar', 'sub',
]
