"""Total shape descriptors and unchanged-source executable realization."""
import json
from pathlib import Path

from cases import case, counted
from commands import Commands
from entry_artifacts import compile_run_package
from tools import compiler, records

commands = Commands(records())
fixture = Path(__file__).parent / 'fixtures/structured-source/shape.zkc'
flags = ['--source-format=zkc', '--entry=sample::Demo', f'--module=sample={fixture}']
child = compile_run_package(commands, *flags)
source = child['original']
interface = json.loads(child['interface'])
symbol = interface['protocol']
snapshot = json.loads(commands.source('protocol-structured', source, '--symbol=' + symbol))
reference = Path(compiler).parent / 'test/zkc-structured_reference-test'
path = commands.directory / 'shape.mlir'
path.write_text(source)
serial = 0


def run(values, n, r, capacity=1000000, refusal=None):
    global serial
    serial += 1
    request = commands.write(f'shape-{serial}.json', ['zkc.structured-open-request/0',
        'role00000000', [values, str(n), str(r)], [], capacity])
    output = commands.run([reference, 'open', path, symbol, request], refuses=refusal)
    return None if refusal else json.loads(output)[1]


with case('typed-protocol-origin-and-total-math-descriptors'):
    defs = [row for row in snapshot[7] if row[0] == 'function']
    protocol = next(row for row in defs if row[1] == symbol)
    assert protocol[8] == ['sample::Run', []]
    descriptors = [i[0] for row in defs for i in row[9][1]]
    assert ['index.less'] in descriptors
    assert ['index.power_of_two'] in descriptors
    assert ['vector.length', 'bls12-381.fr'] in descriptors
    assert all(row[8] == [] for row in defs if row[2] == 'math')

with case('natural-shape-and-bound-boundaries'):
    for r in range(6):
        values = ['0'] * (2 ** r)
        assert run(values, 2 ** r, r) == ['returned', [True, str(len(values)), 2 ** r < r, r <= 4]]
        assert run(values[:-1], 2 ** r - 1, r) == ['returned', [False, str(len(values)-1), 2 ** r - 1 < r, False]]
    for n, r in [(0, 0), (1, 0), (2 ** 63, 63), (0, 64), (1, 64), (2 ** 64 - 1, 2 ** 64 - 1)]:
        expected = r < 64 and n == 2 ** r
        assert run([], n, r) == ['returned', [expected, '0', n < r, False]]

with case('math-source-success-and-observer-capacity-refusal'):
    assert run(['1', '2'], 2, 1)[0] == 'returned'
    run(['1', '2'], 2, 1, capacity=1, refusal='structured-reference-capacity')
    # This is observer capacity evidence. Actual compiled-target exhaustion is
    # checked separately in common/tests/protocol/test_shape_math.py.

commands.save()
print(f'source-shape: {counted()} cases; evidence: {commands.directory}')
