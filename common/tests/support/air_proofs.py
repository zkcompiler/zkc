"""A captured external AIR proved by the ordinary STARK/FRI source libraries.

The AIR fixture comes from direct upstream execution. Tests exercise the full
proof path and adversarial obligations, without asserting a soundness bound.
"""

from input_files import input_files
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[3]
EXAMPLE = ROOT / 'examples/projects/air-stark/main.zkc'
TABLE = ROOT / 'libraries/air/table.zkc'
STARK = ROOT / 'libraries/air/stark.zkc'
FIXTURE = ROOT / 'compiler/adapters/plonky3/fixtures/recurrence'
P = 2130706433


def scalar(value):
    return str(value)


def vector(values):
    return [str(v) for v in values]


def unpack(value):
    return [int(v) for v in value]


def inputs():
    original = json.loads((FIXTURE / 'source-trace-honest.json').read_text())
    data = original
    x0, y0, final = unpack(data['public_data'])
    return ({'configuration': data['configuration'], 'x0': scalar(x0),
             'y0': scalar(y0), 'final_acc': scalar(final), 'shift': scalar(3),
             'round_count': 3, 'query_count': 8, 'attempt_count': 8},
            {'trace': data['trace']})


def compile_entry(toolchain, journal, directory, *, log_size=5, queries=8,
                  flags=(), entry='Proof', source=None, table=TABLE, stark=STARK, compiled_projects=None):
    package = directory / f'{entry}.zkpkg'
    if source is None and log_size == 5 and queries == 8 and table == TABLE and stark == STARK:
        if compiled_projects is not None:
            return compiled_projects.compile(EXAMPLE.with_name('zkc.toml'), f'air_stark_example::{entry}', flags, journal)
        report = journal.json([toolchain.runtime, '--json', 'compile', f'--compiler={toolchain.compiler}',
                               f'--project={EXAMPLE.parent}/zkc.toml',
                               f'air_stark_example::{entry}', f'--output={package}', *flags])
        return package, report['package_sha256']
    source = EXAMPLE.read_text() if source is None else source
    source = source.replace('TableArgument<0,Recurrence,3,5,8,8>',
                            f'TableArgument<0,Recurrence,3,{log_size},{queries},8>')
    path = directory / 'main.zkc'
    path.write_text(source)
    command = [toolchain.runtime, '--json', 'compile', f'--compiler={toolchain.compiler}',
               f'--module=air_stark_example={path}',
               f'--module=air_stark={stark}',
               f'--module=air_table={table}',
               f'--module=air_polynomial={ROOT}/libraries/air/polynomial.zkc',
               f'--module=fri={ROOT}/libraries/fri/lib.zkc',
               f'--asset=recurrence=relation-bundle-json={FIXTURE}/bundle.json',
               f'air_stark_example::{entry}', f'--output={package}', *flags]
    report = journal.json(command)
    return package, report['package_sha256']


def request(journal, name, public, private=None):
    return input_files(journal, name + '.json', public=public, witness=private or {})


def frames(proof):
    offset, result = 40, []
    while offset < len(proof):
        count = int.from_bytes(proof[offset:offset + 8], 'little')
        result.append(proof[offset + 8:offset + 8 + count])
        offset += count + 8
    assert offset == len(proof)
    return result


def replace_frame(proof, position, value):
    messages = frames(proof)
    messages[position] = value
    return proof[:40] + b''.join(len(m).to_bytes(8, 'little') + m for m in messages)
