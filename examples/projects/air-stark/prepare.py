"""Prepare this example's proof inputs from the retained upstream AIR run."""
import argparse
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
FIXTURE = ROOT / 'compiler/adapters/plonky3/fixtures/recurrence/source-trace-honest.json'


def inputs():
    data = json.loads(FIXTURE.read_text())
    x0, y0, final = data['public_data']
    public = {'configuration': data['configuration'],
              'x0': x0, 'y0': y0, 'final_acc': final, 'shift': '3',
              'round_count': '3', 'query_count': '8', 'attempt_count': '8'}
    return public, {'trace': data['trace']}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path, help='directory for the public and witness input files')
    output = parser.parse_args().output
    output.mkdir(parents=True, exist_ok=True)
    for name, request in zip(('public', 'witness'), inputs(), strict=True):
        (output / f'{name}.json').write_text(json.dumps(request, indent=2) + '\n')


if __name__ == '__main__':
    main()
