"""Generate a deterministic degree-seven word on the 32-point example coset."""
import argparse
import json
from pathlib import Path

P = 2130706433


def inputs():
    root = pow(1791270792, (1 << 24) // 32, P)
    assert pow(root, 32, P) == 1 and pow(root, 16, P) == P - 1
    word = []
    for i in range(32):
        x = 3 * pow(root, i, P) % P
        value = sum((degree+1) * pow(x, degree, P) for degree in range(8)) % P
        word.append([str(value), *(['0']*7)])
    public = {'shift': ['3', *(['0']*7)], 'round_count': '3', 'query_count': '8'}
    return {'public': public, 'witness': {'word': word}, 'P': public | {'word': word}, 'V': public}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=Path('build/inputs'))
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    for name, value in inputs().items():
        (args.output / f'{name}.json').write_text(json.dumps(value, indent=2) + '\n')


if __name__ == '__main__':
    main()
