"""Regenerate the maintained proof inputs from the Clean Bundle carriers."""
import argparse
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
PROJECT = Path(__file__).resolve().parent


def documents():
    fixture = ROOT / 'compiler/adapters/clean/fixtures/femtocairo'
    bundle, configuration, instance, witness = [json.loads((fixture / f'{name}.json').read_text())
        for name in ('bundle', 'configuration', 'instance', 'witness')]
    heights = [table[2][1] for table in bundle[3]]

    def rows(table, purpose, groups):
        widths = [group[3] for group in bundle[3][table][4] if group[1] == purpose]
        # Native carriers store each group separately. The STARK API combines
        # groups across each row, preserving the Bundle's group declaration order.
        return [value for row in range(heights[table])
                for width, values in zip(widths, groups, strict=True)
                for value in values[row * width:(row + 1) * width]]

    statement = {'tables': [{'present': True, 'height': str(heights[t]),
        'configuration': rows(t, 'config', configuration[2][t][1]),
        'public_columns': rows(t, 'public', instance[3][t][2])} for t in range(3)],
        'public_data': instance[2], 'shift': '3'}
    return {'public.json': {'statement': statement},
            'witness.json': {'witness': [rows(t, 'witness', witness[2][t]) for t in range(3)]}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    for name, value in documents().items():
        path = PROJECT / 'inputs/example.Proof' / name
        text = json.dumps(value, indent=2) + '\n'
        if args.check:
            if not path.exists() or path.read_text() != text:
                raise SystemExit(f'input differs: {path}')
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)


if __name__ == '__main__':
    main()
