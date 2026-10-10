"""Prepare this example's proof requests from the retained upstream AIR run."""
import argparse
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
FIXTURE = ROOT / 'compiler/adapters/plonky3/fixtures/recurrence/source-trace-honest.json'


def requests():
    data = json.loads(FIXTURE.read_text())['roles']['Evaluator']['inputs']
    values = bytes.fromhex(data['public_data'])
    if values[:10] != b'ZKCV\x00\x14\x03\x00\x00\x00' or len(values) != 22:
        raise ValueError('expected the recurrence AIR\'s three KoalaBear public values')

    def scalar(value):
        return (b'ZKCV\x00\x13' + value).hex()

    public = {'configuration': data['configuration'],
              'x0': scalar(values[10:14]), 'y0': scalar(values[14:18]),
              'final_acc': scalar(values[18:22]), 'shift': scalar((3).to_bytes(4, 'little')),
              'round_count': 3, 'query_count': 8, 'attempt_count': 8}
    return ({'format': 'zkc.entry-proof/0', 'public': public, 'inputs': {'trace': data['trace']}},
            {'format': 'zkc.entry-proof/0', 'public': public, 'inputs': {}})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path, help='directory for the two proof request files')
    output = parser.parse_args().output
    output.mkdir(parents=True, exist_ok=True)
    for name, request in zip(('prover', 'verifier'), requests(), strict=True):
        (output / f'{name}.json').write_text(json.dumps(request, indent=2) + '\n')


if __name__ == '__main__':
    main()
