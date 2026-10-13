"""Regenerate the maintained input examples from the external AIR fixtures."""
import argparse
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
PROJECT = Path(__file__).resolve().parent


def documents():
    result = {}
    for adapter, entry, prefix in [('clean', 'CleanProof', ''), ('plonky3', 'Plonky3Proof', 'bundle-')]:
        fixture = ROOT / 'compiler/adapters' / adapter / 'fixtures/fibonacci'
        public = json.loads((fixture / f'{prefix}instance.json').read_text())[2]
        trace = json.loads((fixture / f'{prefix}witness.json').read_text())[2][0][0]
        result[f'example.{entry}/public.json'] = dict(zip(
            ('initial_x', 'initial_y', 'final_x', 'final_y'), public, strict=True))
        result[f'example.{entry}/witness.json'] = {'trace': trace}
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    for name, value in documents().items():
        path = PROJECT / 'inputs' / name
        text = json.dumps(value, indent=2) + '\n'
        if args.check:
            if not path.exists() or path.read_text() != text:
                raise SystemExit(f'input differs: {path}')
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)


if __name__ == '__main__':
    main()
