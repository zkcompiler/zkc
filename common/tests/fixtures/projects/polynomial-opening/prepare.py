"""Generate a small natural-order polynomial word without using zkc kernels."""
import json
from pathlib import Path
import sys

P = 2130706433

def scalar(value):
    return [str(value % P)] + ['0'] * 7

def evaluate(x):
    return (1 + x * (2 + x * (3 + x * 4))) % P

def main():
    target = Path(sys.argv[1]) if len(sys.argv) > 1 else Path(__file__).parent / 'inputs/example.Proof'
    target.mkdir(parents=True, exist_ok=True)
    root = pow(1791270792, (1 << 24) // 32, P)
    public = {'shift': scalar(3), 'point': scalar(7), 'value': scalar(evaluate(7))}
    witness = {'word': [scalar(evaluate(3 * pow(root, i, P) % P)) for i in range(32)]}
    for name, value in [('public', public), ('witness', witness)]:
        (target / f'{name}.json').write_text(json.dumps(value, indent=2) + '\n')

if __name__ == '__main__':
    main()
