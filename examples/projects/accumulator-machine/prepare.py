"""Prepare this example's proof inputs from an external accumulator-machine run.

The external adapter executes the run and lays it out as relation-bundle
carriers. This script maps those carriers to the relation's derived formals,
in the Bundle's ABI order, and writes public and witness input files.
"""
import argparse
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[3]
ADAPTER = ROOT / 'compiler/adapters/accumulator-machine'
sys.path.insert(0, str(ADAPTER))

import accumulator_machine as machine  # noqa: E402

# MachineRelation's formal names, in the order the Bundle derives them.
FORMALS = ('initial', 'final', 'cpu_height', 'cpu', 'program_height', 'instructions', 'usage',
           'memory_present', 'memory_height', 'schedule', 'cells')
# The example's static profile: MaxLogHeight 5, eight queries and attempts,
# and the Bundle's two channels.
SCHEDULE = {'shift': 3, 'round_count': 5, 'query_count': 8, 'attempt_count': 8,
            'channel_count': 2}


def scalar(value):
    return str(int(value) % machine.P)


def vector(values):
    return [scalar(v) for v in values]


def formals(bundle, configuration, instance, witness):
    """(purpose, value) per derived formal: publics, then per table presence,
    height and groups. Values keep the carriers' exact elements and heights."""
    result = [('statement', scalar(v)) for v in instance[2]]
    for t, table in enumerate(bundle[3]):
        _, presence, height, _, groups = table[:5]
        configured_height, configured = configuration[2][t]
        entry = instance[3][t]
        present = entry[0] == 'present'
        if presence == 'optional':
            result.append(('statement', present))
        if height[0] == 'config':
            result.append(('parameter', str(configured_height)))
        elif height[0] == 'instance':
            result.append(('statement', str(entry[1] if present else 0)))
        sources = {'config': iter(configured), 'public': iter(entry[2] if present else []),
                   'witness': iter(witness[2][t] or [])}
        for group in groups:
            purpose = {'config': 'parameter', 'public': 'statement', 'witness': 'witness'}[group[1]]
            result.append((purpose, vector(next(sources[group[1]], []))))
    return result


def inputs(bundle, configuration, instance, witness, **schedule):
    """Public and witness inputs for the example's proof Entries."""
    values = formals(bundle, configuration, instance, witness)
    if len(values) != len(FORMALS):
        raise ValueError('the Bundle does not derive MachineRelation\'s formals')
    public, private = {}, {}
    for name, (purpose, value) in zip(FORMALS, values, strict=True):
        (private if purpose == 'witness' else public)[name] = value
    settings = SCHEDULE | schedule
    public |= {name: scalar(value) if name == 'shift' else str(value) for name, value in settings.items()}
    return public, private


def run_inputs(document, memory_clocks=None, memory_present=None):
    program, initial = machine.read_run(document)
    rows = machine.layout(machine.execute(program, initial), memory_clocks, memory_present)
    bundle, _ = machine.machine_bundle()
    return inputs(bundle, *machine.carriers(bundle, rows))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('run', type=Path, help='a zkc.accumulator-machine-run/0 document')
    parser.add_argument('output', type=Path, help='directory for the public and witness input files')
    parser.add_argument('--memory-clocks', type=int, help='schedule length, if longer than the run')
    parser.add_argument('--memory-present', action=argparse.BooleanOptionalAction,
                        help='override whether the memory table is present')
    args = parser.parse_args()
    pair = run_inputs(json.loads(args.run.read_text()), args.memory_clocks, args.memory_present)
    args.output.mkdir(parents=True, exist_ok=True)
    for name, request in zip(('public', 'witness'), pair, strict=True):
        (args.output / f'{name}.json').write_text(json.dumps(request, indent=2) + '\n')


if __name__ == '__main__':
    main()
