"""Prepare this example's proof requests from an external accumulator-machine run.

The external adapter executes the run and lays it out as relation-bundle
carriers. This script maps those carriers to the relation's derived formals,
in the Bundle's ABI order, and writes prover and verifier requests.
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
    return (b'ZKCV\x00\x13' + (int(value) % machine.P).to_bytes(4, 'little')).hex()


def vector(values):
    return (b'ZKCV\x00\x14' + len(values).to_bytes(4, 'little')
            + b''.join((int(v) % machine.P).to_bytes(4, 'little') for v in values)).hex()


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
            result.append(('parameter', configured_height))
        elif height[0] == 'instance':
            result.append(('statement', entry[1] if present else 0))
        sources = {'config': iter(configured), 'public': iter(entry[2] if present else []),
                   'witness': iter(witness[2][t] or [])}
        for group in groups:
            purpose = {'config': 'parameter', 'public': 'statement', 'witness': 'witness'}[group[1]]
            result.append((purpose, vector(next(sources[group[1]], []))))
    return result


def requests(bundle, configuration, instance, witness, **schedule):
    """Prover and verifier requests for the example's proof Entries."""
    values = formals(bundle, configuration, instance, witness)
    if len(values) != len(FORMALS):
        raise ValueError('the Bundle does not derive MachineRelation\'s formals')
    public, private = {}, {}
    for name, (purpose, value) in zip(FORMALS, values, strict=True):
        (private if purpose == 'witness' else public)[name] = value
    settings = SCHEDULE | schedule
    public |= {name: scalar(value) if name == 'shift' else value for name, value in settings.items()}
    return ({'format': 'zkc.entry-proof/0', 'public': public, 'inputs': private},
            {'format': 'zkc.entry-proof/0', 'public': public, 'inputs': {}})


def run_requests(document, memory_clocks=None, memory_present=None):
    program, initial = machine.read_run(document)
    rows = machine.layout(machine.execute(program, initial), memory_clocks, memory_present)
    bundle, _ = machine.machine_bundle()
    return requests(bundle, *machine.carriers(bundle, rows))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('run', type=Path, help='a zkc.accumulator-machine-run/0 document')
    parser.add_argument('output', type=Path, help='directory for the two proof request files')
    parser.add_argument('--memory-clocks', type=int, help='schedule length, if longer than the run')
    parser.add_argument('--memory-present', action=argparse.BooleanOptionalAction,
                        help='override whether the memory table is present')
    args = parser.parse_args()
    pair = run_requests(json.loads(args.run.read_text()), args.memory_clocks, args.memory_present)
    args.output.mkdir(parents=True, exist_ok=True)
    for name, request in zip(('prover', 'verifier'), pair, strict=True):
        (args.output / f'{name}.json').write_text(json.dumps(request, indent=2) + '\n')


if __name__ == '__main__':
    main()
