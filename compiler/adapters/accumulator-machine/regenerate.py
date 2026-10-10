#!/usr/bin/env python3
"""Write or check the accumulator-machine fixtures.

    regenerate.py write NEW_DIRECTORY
    regenerate.py check FIXTURE_DIRECTORY

`write` refuses an existing directory. `check` requires exactly the generated
file set, each file byte for byte. Every file is one compact JSON line. The
staged assignments use fixed test challenges from `fixture_challenges`; they
are reproducible values, not challenges drawn by any protocol transcript.
"""

import argparse
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))

from accumulator_machine import carriers, execute, layout, machine_bundle, run_document  # noqa: E402
from interaction_reductions import LOGUP, PRODUCT, Reduction, fixture_challenges  # noqa: E402
from ring_arena import P, compact  # noqa: E402

# Interleaved stores, loads and arithmetic, including a read of a cell that was
# never written, KoalaBear wraparound and a read directly after a write.
STORE_LOAD = [
    ('add-immediate', 5), ('store', 0), ('load', 1), ('set-immediate', 7),
    ('store', 1), ('load', 0), ('add-immediate', 3), ('store', 0),
    ('load', 1), ('add-immediate', P - 2), ('store', 1), ('load', 0),
    ('add-immediate', 100), ('store', 1), ('load', 1), ('halt', 0),
]
# No memory instruction, so the optional memory table is absent. The explicit
# AddImmediate 0 is authored padding to an exact power-of-two execution.
ARITHMETIC_ONLY = [('add-immediate', 10), ('add-immediate', P - 1), ('add-immediate', 0), ('halt', 0)]

RUNS = {
    'store-load': (STORE_LOAD, 0),
    'store-load-initial-seven': (STORE_LOAD, 7),
    'arithmetic-only': (ARITHMETIC_ONLY, 3),
}
PRESENCE = {'with-memory': [True, True, True], 'without-memory': [True, True, False]}


def line(document):
    return compact(document) + '\n'


def generate():
    """Relative path -> exact text of every fixture file."""
    bundle, _ = machine_bundle()
    files = {'bundle.json': line(bundle)}
    reductions = {}
    for kind in (LOGUP, PRODUCT):
        for label, presence in PRESENCE.items():
            reduction = Reduction(kind, bundle, presence)
            reductions[kind, tuple(presence)] = reduction
            files[f'{kind}-{label}.json'] = line(reduction.program)
    for name, (program, initial) in RUNS.items():
        rows = layout(execute(program, initial))
        configuration, instance, witness = carriers(bundle, rows)
        files[f'{name}/run.json'] = line(run_document(program, initial))
        files[f'{name}/bundle-configuration.json'] = line(configuration)
        files[f'{name}/bundle-instance.json'] = line(instance)
        files[f'{name}/bundle-witness.json'] = line(witness)
        presence = tuple(entry[0] == 'present' for entry in instance[3])
        for kind in (LOGUP, PRODUCT):
            reduction = reductions[kind, presence]
            challenges = fixture_challenges(f'{name}/{kind}', len(reduction.challenge_names))
            files[f'{name}/{kind}-assignment.json'] = line(
                reduction.assign(configuration, instance, witness, challenges))
    return files


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('command', choices=['write', 'check'])
    parser.add_argument('directory', type=Path)
    args = parser.parse_args()
    files = generate()
    if args.command == 'write':
        if args.directory.exists():
            parser.error(f'{args.directory} already exists')
        for name, text in files.items():
            path = args.directory / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)
        return 0
    present = {str(p.relative_to(args.directory)) for p in args.directory.rglob('*') if p.is_file()}
    differences = sorted(present ^ files.keys())
    differences += sorted(n for n in files.keys() & present if (args.directory / n).read_text() != files[n])
    for name in differences:
        print(f'fixture differs: {name}', file=sys.stderr)
    return 1 if differences else 0


if __name__ == '__main__':
    sys.exit(main())
