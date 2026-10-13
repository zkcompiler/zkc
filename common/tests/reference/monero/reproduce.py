"""Regenerate independent fixtures with the pinned upstream executable."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile

REVISION = '4f92268d7c16741cfb41e5bbe2aa46cc260a9ea5'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source', type=Path, required=True)
    parser.add_argument('--reference', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    head = subprocess.check_output(['git', '-C', args.source, 'rev-parse', 'HEAD'], text=True).strip()
    if head != REVISION or subprocess.check_output(['git', '-C', args.source, 'diff', 'HEAD']):
        parser.error('reference sources must be the unmodified pinned Monero revision')
    reference = args.reference.resolve()
    cases = []
    with tempfile.TemporaryDirectory() as tmp:
        for count in range(1, 17):
            for pattern in ['zero', 'max', 'mixed', 'random']:
                name = f'{count}-{pattern}'
                prefix = Path(tmp) / name
                control = json.loads(subprocess.check_output(
                    [reference, 'prove', str(count), prefix, pattern], text=True))
                rounds = 6 + (count-1).bit_length()
                assert control == {'accepted': True, 'coins': 2*rounds+5}
                cases.append({
                    'name': name,
                    'commitments': prefix.with_suffix('.commitments').read_bytes().hex(),
                    'values': list(map(int, prefix.with_suffix('.values').read_text().splitlines())),
                    'masks': [str(i+17) for i in range(count)],
                    'coins': [str(i) for i in range(1, control['coins']+1)],
                    'proof': prefix.with_suffix('.proof').read_bytes().hex(),
                })
    args.output.mkdir(parents=True, exist_ok=True)
    (args.output / 'corpus.json').write_text(json.dumps({'revision': REVISION, 'cases': cases}, indent=2)+'\n')
    values = [0, 2**256-1, 1, 2, 2**255-20, 2**255-19, 2**255-18, 2**255, 2**256-38]
    inputs = [n.to_bytes(32, 'little').hex() for n in values]
    inputs += [hashlib.sha256(str(i).encode()).hexdigest() for i in range(128)]
    outputs = subprocess.check_output([reference, 'map'], input='\n'.join(inputs)+'\n', text=True).splitlines()
    assert len(outputs) == len(inputs)
    (args.output / 'edwards-map.json').write_text(json.dumps(list(zip(inputs, outputs, strict=True)), indent=2)+'\n')


if __name__ == '__main__':
    main()
