#!/usr/bin/env python3
"""Write or check Bundle fixtures from freshly extracted Clean sources.

Run CleanExamples.lean first. The native compiler and proof runtime require
only the resulting Bundle and data carriers, never the Lean environment.
"""

import argparse
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from ring_arena import compact  # noqa: E402
from adapter import export  # noqa: E402


def generate(source):
    files = {}
    for path in sorted(source.glob('*.json')):
        document = json.loads(path.read_text())
        documents = {'source.json': document, **export(document).documents()}
        for name, value in documents.items():
            files[f'{path.stem}/{name}'] = compact(value) + '\n'
    if not files:
        raise ValueError('no extracted Clean sources')
    return files


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command', choices=['write', 'check'])
    parser.add_argument('source', type=Path)
    parser.add_argument('destination', type=Path)
    args = parser.parse_args()
    files = generate(args.source)
    if args.command == 'write':
        if args.destination.exists():
            parser.error('destination already exists')
        for name, text in files.items():
            path = args.destination / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)
        return 0
    present = {str(p.relative_to(args.destination)) for p in args.destination.rglob('*') if p.is_file()}
    changed = sorted(present ^ files.keys())
    changed += sorted(name for name in present & files.keys()
                      if (args.destination / name).read_text() != files[name])
    for name in changed:
        print(f'fixture differs: {name}', file=sys.stderr)
    return int(bool(changed))


if __name__ == '__main__':
    sys.exit(main())
