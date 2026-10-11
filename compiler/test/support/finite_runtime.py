"""Execute handwritten finite IR through the compiler and authenticated native Host.

Run explicitly with --compiler and --runtime; no frontend or native source edits
are needed. The large case changes only the native element capacity.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--compiler', required=True, type=Path)
parser.add_argument('--runtime', required=True, type=Path)
parser.add_argument('--output', required=True, type=Path)
parser.add_argument('--checked-access', action='store_true', help='Require native matrix.get and field_array.get integration')
args = parser.parse_args()
args.output.mkdir(parents=True, exist_ok=True)
fixtures = Path(__file__).parents[1] / 'fixtures' / 'finite'
checks = []
bundles = {}


def wire(tag, payload):
    return ['wire', (b'ZKCV' + bytes([0, tag]) + payload).hex()]


def field(value):
    return wire(1, value.to_bytes(32, 'little'))


def array(values):
    return wire(64, b''.join(value.to_bytes(32, 'little') for value in values))


def vector(values):
    return wire(66, len(values).to_bytes(4, 'little') + b''.join(
        value.to_bytes(32, 'little') for value in values))


def boolean(value):
    return wire(5, bytes([bool(value)]))


def index(value):
    return wire(31, value.to_bytes(8, 'little'))


def indices(values):
    return wire(68, len(values).to_bytes(4, 'little') + b''.join(
        value.to_bytes(8, 'little') for value in values))


def matrix(rows, columns, entries):
    header = b''.join(n.to_bytes(4, 'little') for n in [rows, columns, len(entries)])
    body = b''.join(r.to_bytes(4, 'little') + c.to_bytes(4, 'little') + v.to_bytes(32, 'little')
                    for r, c, v in entries)
    return wire(23, header + body)


def compile_fixture(name, optimized):
    key = name, optimized
    if key not in bundles:
        path = args.output / f'{name}-{"bulk" if optimized else "loop"}.bundle'
        command = [args.compiler, 'protocol-bundle', fixtures / f'{name}.mlir']
        if not optimized:
            command.append('--no-simplify')
        result = subprocess.run(command, capture_output=True, text=True)
        (args.output / f"{name}-{optimized}-compile.json").write_text(json.dumps(
            dict(command=[str(v) for v in command], returncode=result.returncode, stderr=result.stderr), indent=2))
        assert result.returncode == 0, f"compiler exit {result.returncode}: {result.stderr}"
        path.write_text(result.stdout)
        carrier = json.loads(json.loads(result.stdout)['candidate'])
        bundles[key] = path, carrier[3][0][4]
    return bundles[key]


def execute(name, optimized, values, capacity=None):
    bundle, ports = compile_fixture(name, optimized)
    data = ['zkc.bundle-inputs/0', 'finite', [['P', [
        [str(i), port[1], value] for i, (port, value) in enumerate(zip(ports, values))
    ], []]], []]
    path = args.output / f'case-{len(checks) + 1}-inputs.json'
    path.write_text(json.dumps(data))
    command = [args.runtime, '--json', 'run-bundle', bundle,
               hashlib.sha256(bundle.read_bytes()).hexdigest(), path]
    if capacity:
        command.append('--capacity=' + str(capacity))
    result = subprocess.run(command, capture_output=True, text=True)
    report = json.loads(result.stdout)
    (args.output / f'case-{len(checks) + 1}-result.json').write_text(result.stdout)
    (args.output / f'case-{len(checks) + 1}-command.json').write_text(json.dumps(
        dict(command=[str(v) for v in command], returncode=result.returncode, stderr=result.stderr), indent=2))
    assert report.get('format') == 'zkc.bundle-result/0', report
    assert all(r['active_frames'] == r['live_resource_units'] == 0
               for r in report.get('roles', [])), report
    return report


def check(name, body):
    try:
        record = body() or {}
        checks.append(dict(name=name, passed=True, **record))
    except Exception as error:
        checks.append(dict(name=name, passed=False, error=str(error)))
        print(f'{name}: {error}', file=sys.stderr)


def completed(report, expected):
    assert report.get('outcome') == ['completed'], report.get('failure') or report
    assert [p[2] for p in report['roles'][0]['outputs']] == [p[1] for p in expected]
    return dict(usage=report['roles'][0]['usage'])


def stopped(report, code):
    assert report.get('outcome') and report['outcome'] != ['completed'], report
    cause = report['roles'][0]['after'][1]['cause']
    assert code in json.dumps(cause), cause
    return dict(cause=cause, usage=report['roles'][0]['usage'])


for optimized in [False, True]:
    mode = 'bulk' if optimized else 'loop'
    check(f'sum {mode}', lambda: completed(execute('sum', optimized, [vector([2, 3, 5]), field(7)]), [field(17)]))
    check(f'empty fold {mode}', lambda: completed(execute('sum', optimized, [vector([]), field(7)]), [field(7)]))
    check(f'unit state empty {mode}', lambda: completed(execute('unit-state', optimized, [vector([]), boolean(True)]), [boolean(True)]))
    check(f'unit state filtered {mode}', lambda: completed(execute('unit-state', optimized, [vector([2, 3]), boolean(False)]), [boolean(False)]))
    check(f'unit state stop retained {mode}', lambda: stopped(execute('unit-state', optimized, [vector([2]), boolean(True)]), 'abort'))
    check(f'dot {mode}', lambda: completed(execute('dot', optimized, [vector([2, 3]), vector([5, 7]), vector([0, 0]), field(11)]), [field(42)]))
    check(f'collect {mode}', lambda: completed(execute('collect', optimized, [vector([2, 3, 5])]), [vector([4, 9, 25])]))
    check(f'zero trips total state {mode}', lambda: completed(execute('total-state', optimized, [vector([]), field(7), field(11)]), [field(7), field(11)]))
    check(f'repeated total state {mode}', lambda: completed(execute('total-state', optimized, [vector([2, 3, 5]), field(7), field(11)]), [field(3), field(5)]))
    for name in ['dot', 'filter']:
        for data in [([2], [3], []), ([], [], [4])]:
            check(f'{name} ignored strict zip {mode} {data}', lambda name=name, data=data: stopped(execute(name, optimized, [*[vector(v) for v in data], field(7)]), 'rejected:require'))
    check(f'filter before stopping body {mode}', lambda: completed(execute('filter', optimized, [vector([2]), vector([3]), vector([4]), field(7)]), [field(7)]))
    check(f'predicate stop first {mode}', lambda: stopped(execute('predicate-stop', optimized, [vector([2]), vector([3]), vector([4]), field(7)]), 'reject'))
    check(f'empty independent product admission {mode}', lambda: stopped(execute('independent', optimized, [vector([]), vector([3]), vector([]), field(7)]), 'rejected:require'))
    check(f'empty dependent outer {mode}', lambda: completed(execute('dependent', optimized, [vector([]), vector([3]), vector([]), field(7)]), [field(7)]))
    check(f'entered dependent inner admission {mode}', lambda: stopped(execute('dependent', optimized, [vector([2]), vector([3]), vector([]), field(7)]), 'rejected:require'))
    check(f'all stopping branches {mode}', lambda: stopped(execute('stopping-branches', optimized, [vector([2]), field(7)]), 'abort'))
    check(f'all stopping branches empty {mode}', lambda: completed(execute('stopping-branches', optimized, [vector([]), field(7)]), [field(7)]))

    check(f'match inside step {mode}', lambda: completed(execute('match', optimized, [vector([2, 3, 5]), field(7)]), [field(17)]))
    check(f'realized total helper {mode}', lambda: completed(execute('realized-total', optimized, [vector([2, 3]), field(7)]), [field(17)]))
    check(f'fixed collection {mode}', lambda: completed(execute('fixed-collect', optimized, [field(7)]), [array([7, 7])]))
    check(f'total predicate filtering {mode}', lambda: completed(execute('total-predicate', optimized, [vector([2, 3, 2]), field(2)]), [vector([6, 6])]))
    check(f'eager operand stop before domain mismatch {mode}', lambda: stopped(execute('eager', optimized, [vector([]), vector([1]), vector([]), field(7)]), 'reject'))
    check(f'total proven zip {mode}', lambda: completed(execute('total-zip', optimized, [vector([2, 3]), field(7)]), [vector([11, 16])]))
    for name, expected in [('coordinates-row', [0, 1, 2, 10, 11, 12]), ('coordinates-column', [0, 10, 1, 11, 2, 12])]:
        check(f'{name} includes sparse zeros {mode}', lambda name=name, expected=expected: completed(execute(name, optimized, [matrix(2, 3, [(1, 1, 5)]), index(10)]), [indices(expected)]))
        check(f'{name} empty {mode}', lambda name=name: completed(execute(name, optimized, [matrix(0, 3, []), index(10)]), [indices([])]))
    check(f'dead domain admission {mode}', lambda: stopped(execute('dead-domain', optimized, [vector([]), vector([1]), vector([]), field(7)]), 'rejected:require'))
    check(f'product {mode}', lambda: completed(execute('product', optimized, [vector([2, 3, 5]), field(7)]), [field(210)]))
    check(f'product empty {mode}', lambda: completed(execute('product', optimized, [vector([]), field(7)]), [field(7)]))
    check(f'empty MSM preserves group init {mode}', lambda: completed(execute('msm-direct', optimized, [wire(67, bytes(4)), vector([]), field(7), field(7)]), [boolean(True)]))
    check(f'MSM {mode}', lambda: completed(execute('msm', optimized, [vector([2, 3]), field(7), field(12)]), [boolean(True)]))
    check(f'MSM shape failure {mode}', lambda: stopped(execute('msm', optimized, [vector([]), field(7), field(12)]), 'rejected:require'))
    check(f'mixed sequence field state {mode}', lambda: completed(execute('mixed-sequence', optimized, [boolean(False), boolean(True), field(7), field(11)]), [field(18)]))
    check(f'product lexicographic order {mode}', lambda: completed(execute('order', optimized, [vector([1, 2]), index(3), index(6), index(10)]), [indices([3, 4, 5, 13, 14, 15])]))
    check(f'reversed range {mode}', lambda: completed(execute('order', optimized, [vector([1, 2]), index(6), index(3), index(10)]), [indices([])]))
    check(f'aliased predicate arguments {mode}', lambda: completed(execute('aliased-predicate', optimized, [vector([1, 2]), index(3), index(6), index(10)]), [indices([0, 11])]))
    check(f'nested total {mode}', lambda: completed(execute('nested-total', optimized, [vector([2, 3]), field(7)]), [field(17)]))
    check(f'total materialization {mode}', lambda: completed(execute('total-collect', optimized, [vector([2, 3]), field(5)]), [vector([15, 20])]))
    check(f'materialized body before reducer {mode}', lambda: stopped(execute('materialized', optimized, [vector([2]), field(7)]), 'abort'))
    check(f'materialized empty still calls reducer {mode}', lambda: stopped(execute('materialized', optimized, [vector([]), field(7)]), 'reject'))

for name, operand, selected, expected in [('matrix-row', [5, 7, 11], 1, 54), ('matrix-column', [5, 7], 2, 34)]:
    m = matrix(2, 3, [(0, 0, 2), (0, 2, 3), (1, 1, 5)])
    check(f'{name} native contraction', lambda name=name, operand=operand, selected=selected, expected=expected: completed(execute(name, True, [m, vector(operand), vector([0]*len(operand)), index(selected), field(19)]), [field(expected)]))
    check(f'{name} ignored zip', lambda name=name, operand=operand, selected=selected: stopped(execute(name, True, [m, vector(operand), vector([]), index(selected), field(19)]), 'rejected:require'))
for name, shape in [('matrix-row', (2, 0)), ('matrix-column', (0, 2))]:
    check(f'{name} valid empty view', lambda name=name, shape=shape: completed(execute(name, True, [matrix(*shape, []), vector([]), vector([]), index(1), field(19)]), [field(19)]))
    check(f'{name} invalid selector on empty view', lambda name=name, shape=shape: stopped(execute(name, True, [matrix(*shape, []), vector([]), vector([]), index(2), field(19)]), 'rejected:require'))

if args.checked_access:
    for optimized in [False, True]:
        mode = 'bulk' if optimized else 'loop'
        check(f'fixed array elements {mode}', lambda: completed(execute('fixed-elements', optimized, [array([2, 3]), field(7)]), [field(12)]))
        for name in ['matrix-values', 'total-matrix-values']:
            check(f'{name} sparse zero values {mode}', lambda name=name: completed(execute(name, optimized, [matrix(2, 3, [(0, 0, 2), (0, 2, 3), (1, 1, 5)])]), [vector([2, 0, 3, 0, 5, 0])]))
            check(f'{name} zero dimension {mode}', lambda name=name: completed(execute(name, optimized, [matrix(2, 0, [])]), [vector([])]))
        check(f'bilinear values {mode}', lambda: completed(execute('bilinear', optimized, [matrix(2, 3, [(0, 0, 2), (0, 2, 3), (1, 1, 5)]), vector([2, 3]), vector([5, 7, 11]), field(19)]), [field(210)]))
        check(f'bilinear empty factor mismatch {mode}', lambda: stopped(execute('bilinear', optimized, [matrix(0, 3, []), vector([]), vector([]), field(19)]), 'rejected:require'))
        for shape, left, right in [((0, 3), [], [1, 2, 3]), ((2, 0), [2, 3], [])]:
            check(f'bilinear valid empty {mode} {shape}', lambda shape=shape, left=left, right=right: completed(execute('bilinear', optimized, [matrix(*shape, []), vector(left), vector(right), field(19)]), [field(19)]))
        for name, operand, selected, expected in [('matrix-row', [5, 7, 11], 1, 54), ('matrix-column', [5, 7], 2, 34)]:
            check(f'{name} access differential {mode}', lambda name=name, operand=operand, selected=selected, expected=expected: completed(execute(name, optimized, [matrix(2, 3, [(0, 0, 2), (0, 2, 3), (1, 1, 5)]), vector(operand), vector([0]*len(operand)), index(selected), field(19)]), [field(expected)]))
        for name, shape in [('matrix-row', (2, 0)), ('matrix-column', (0, 2))]:
            check(f'{name} empty differential {mode}', lambda name=name, shape=shape: completed(execute(name, optimized, [matrix(*shape, []), vector([]), vector([]), index(1), field(19)]), [field(19)]))
            check(f'{name} empty invalid selector differential {mode}', lambda name=name, shape=shape: stopped(execute(name, optimized, [matrix(*shape, []), vector([]), vector([]), index(2), field(19)]), 'rejected:require'))

    check('2^17 logical cells bulk bilinear', lambda: completed(execute('bilinear', True, [matrix(512, 256, [(0, 0, 2), (511, 255, 3)]), vector([1]*512), vector([1]*256), field(7)]), [field(12)]))

capacity = args.output / 'capacity.json'
capacity.write_text(json.dumps(['zkc.native-capacity/0', '131072', '4096', '16777216', '67108864',
                               ['1000000', '100000', '4294967296'], ['67108864', '268435456']]))
check('2^17 bulk sum', lambda: completed(execute('sum', True, [vector([1] * 131072), field(7)], capacity), [field(131079)]))
check('2^17 generic loop retains resource ceiling', lambda: stopped(execute('sum', False, [vector([1] * 131072), field(7)], capacity), 'limit'))
check('2^17 elementwise materialization', lambda: completed(execute('collect', True, [vector([2] * 131072)], capacity), [vector([4] * 131072)]))
check('2^17 bulk dot', lambda: completed(execute('dot-large', True, [vector([2]*131072), field(3), field(7)], capacity), [field(786439)]))
check('2^17 bulk product', lambda: completed(execute('product', True, [vector([1]*131072), field(7)], capacity), [field(7)]))
(args.output / 'results.json').write_text(json.dumps(checks, indent=2) + '\n')
failures = sum(not record['passed'] for record in checks)
print(f'{len(checks)} cases, {failures} failures')
sys.exit(bool(failures))
