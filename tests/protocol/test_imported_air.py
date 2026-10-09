"""An imported Plonky3 AIR arena through ordinary .zkc source and the Entry Host.

The adapter's closed view prepared every maintained request from the recurrence
fixture's export, an instance selecting it and a trace. The expectations beside
them come from direct `Air::eval`, not from the arena. These tests read the
committed fixtures and never build the optional adapter; its fixture check
regenerates the same files from the pinned upstream AIR.
"""
import json
import re
from hashlib import sha256
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
PROJECT = ROOT / 'examples/projects/imported-air'
FIXTURES = ROOT / 'compiler/adapters/plonky3/fixtures'
RECURRENCE = FIXTURES / 'recurrence'
# Manifest paths resolve from the Host's working directory, the repository root.
ASSETS = 'compiler/adapters/plonky3/fixtures/recurrence/ring-assets.json'
P = 2130706433
EXPECTED = json.loads((RECURRENCE / 'source-expected.json').read_text())
EXPORT = json.loads((RECURRENCE / 'export.json').read_text())
ARENA = json.loads((RECURRENCE / 'arena.json').read_text())
ASSERTIONS = len(EXPORT['assertions'])
SLOTS = len(EXPORT['slots'])


def frame(values, extension=False):
    words = [w for v in values for w in v] if extension else values
    return (b'ZKCV\0' + bytes([27 if extension else 20]) + len(values).to_bytes(4, 'little')
            + b''.join(w.to_bytes(4, 'little') for w in words)).hex()


def unframe(text, extension=False):
    data = bytes.fromhex(text)
    assert data[:6] == b'ZKCV\0' + bytes([27 if extension else 20])
    count = int.from_bytes(data[6:10], 'little')
    assert len(data) == 10 + count * (32 if extension else 4)
    words = [int.from_bytes(data[i:i + 4], 'little') for i in range(10, len(data), 4)]
    assert all(w < P for w in words)
    return [words[i:i + 8] for i in range(0, len(words), 8)] if extension else words


def numbers(value):
    return [numbers(v) for v in value] if isinstance(value, list) else int(value)


def output_width(width):
    """The provider's rule: one plus the largest output degree, with every
    input weighted `width - 1`."""
    degrees = []
    for kind, *operands in ARENA[2]:
        if kind == 'constant':
            degrees.append(0)
        elif kind == 'input':
            degrees.append(width - 1)
        elif kind == 'add':
            degrees.append(max(degrees[operands[0]], degrees[operands[1]]))
        elif kind == 'mul':
            degrees.append(degrees[operands[0]] + degrees[operands[1]])
        else:
            degrees.append(degrees[operands[-1]])
    return 1 + max((degrees[o] for o in ARENA[3]), default=0)


def evaluate(coefficients, point):
    value = 0
    for coefficient in reversed(coefficients):
        value = (value * point + coefficient) % P
    return value


def maintained(case):
    return json.loads((RECURRENCE / f'source-{case}.json').read_text())


class Client:
    """One compiled Entry of the source client, run from the repository root."""

    def __init__(self, toolchain, journal, directory, entry, flags=()):
        self.tools, self.journal, self.directory = toolchain, journal, directory
        self.package = directory / f'{entry}.entry'
        report = journal.json([toolchain.runtime, 'compile', f'--compiler={toolchain.compiler}',
                               f'--module=imported_air={PROJECT}/main.zkc',
                               f'--entry=imported_air::{entry}', f'--output={self.package}', *flags])
        self.pin = report['package_sha256']

    def run(self, name, request, assets=ASSETS, refuses=None):
        path = self.journal.write(f'{name}.request.json', request)
        output = self.directory / f'{name}.outputs.json'
        command = [self.tools.runtime, 'run', self.package, self.pin, path, f'--results={output}']
        if assets is not None:
            command.append(f'--evaluators={assets}')
        report = self.journal.json(command, cwd=ROOT, refuses=refuses)
        if refuses:
            assert report['status'] == 'refused'
            assert not output.exists(), 'a refused run published outputs'
            return report
        assert report['status'] == 'executed'
        return json.loads(output.read_text())['roles']['Evaluator']


def stopped(report):
    """The backend cause that stopped the only participant."""
    (role,) = report['execution']['roles']
    state, detail = role['after']
    assert state == 'stopped' and detail['cause'][0] == 'backend'
    return detail['cause'][1]['text']


def test_source_binds_the_exported_arena():
    digests = set(re.findall(r'"([0-9a-f]{64})"', (PROJECT / 'main.zkc').read_text()))
    arena = (RECURRENCE / 'arena.json').read_bytes()
    instance = json.loads((RECURRENCE / 'instance.json').read_text())
    manifest = json.loads((ROOT / ASSETS).read_text())
    assert digests == {EXPORT['arena_sha256']} == {sha256(arena).hexdigest()}
    arena_path = str(RECURRENCE.relative_to(ROOT) / 'arena.json')
    assert manifest == ['zkc.ring-assets/0', [[EXPORT['arena_sha256'], arena_path]]]
    assert instance['export_sha256'] == sha256((RECURRENCE / 'export.json').read_bytes()).hexdigest()
    assert len(ARENA[1]) == SLOTS and len(ARENA[3]) == ASSERTIONS


def check_rows(journal, name, expected, actual):
    residuals = unframe(actual['residuals'])
    journal.check(f'{name}: residuals equal Air::eval', residuals == numbers(expected['residuals']))
    nonzero = [[i // ASSERTIONS, i % ASSERTIONS] for i, r in enumerate(residuals) if r]
    journal.check(f'{name}: nonzero cells are the upstream failures', nonzero == expected['upstream_failures'])
    journal.check(f'{name}: satisfied iff every residual is zero', actual['satisfied'] is (not nonzero))


def check_coefficients(journal, name, expected, actual, width):
    coefficients = unframe(actual['residuals'])
    outputs = output_width(width)
    points = numbers(expected['points'])
    # Agreement at `outputs` distinct points fixes a polynomial with that many coefficients.
    assert len(coefficients) == ASSERTIONS * outputs
    assert len(set(points)) == len(points) >= outputs
    for point, evaluations in zip(points, numbers(expected['evaluations'])):
        actual_values = [evaluate(coefficients[a * outputs:(a + 1) * outputs], point)
                         for a in range(ASSERTIONS)]
        journal.check(f'{name}: residual polynomials at {point} equal Air::eval',
                      actual_values == evaluations)


@pytest.mark.parametrize('flags', [[], ['--no-simplify'], ['--release-storage']])
@pytest.mark.parametrize('entry', ['RowResiduals', 'CoefficientResiduals', 'PointResiduals'])
def test_maintained_requests_match_direct_evaluation(toolchain, journal, directory, entry, flags):
    client = Client(toolchain, journal, directory, entry, flags)
    cases = {name: case for name, case in EXPECTED.items() if case['entry'] == entry}
    assert cases
    for name, expected in cases.items():
        request = maintained(name)
        actual = client.run(name, request)
        inputs = request['roles']['Evaluator']['inputs']
        if entry == 'RowResiduals':
            check_rows(journal, name, expected, actual)
        elif entry == 'CoefficientResiduals':
            check_coefficients(journal, name, expected, actual, inputs['width'])
        else:
            residuals = unframe(actual['residuals'], extension=True)
            journal.check(f'{name}: Ext8 residuals equal Air::eval',
                          residuals == numbers(expected['residuals']))
            assert len(numbers(expected['points'])) == inputs['points']


def test_row_and_coefficient_layouts():
    # The same 112 cells are 8 row-major assignments or 14 slot polynomials of
    # width 8. Only the operation and the view that prepared them decide which.
    rows = maintained('rows-honest')['roles']['Evaluator']['inputs']
    coefficients = maintained('coefficients-honest')['roles']['Evaluator']['inputs']
    assert len(unframe(rows['assignments'])) == rows['rows'] * SLOTS
    assert len(unframe(coefficients['coefficients'])) == coefficients['width'] * SLOTS
    assert len(numbers(EXPECTED['rows-honest']['residuals'])) == rows['rows'] * ASSERTIONS


def test_wrong_shapes_refuse_before_evaluation(toolchain, journal, directory):
    rows = Client(toolchain, journal, directory, 'RowResiduals')
    request = maintained('rows-honest')
    inputs = request['roles']['Evaluator']['inputs']
    cells = unframe(inputs['assignments'])
    for name, change in [('short', {'assignments': frame(cells[:-1])}),
                         ('long', {'assignments': frame(cells + [0])}),
                         ('row-count', {'rows': inputs['rows'] - 1})]:
        changed = json.loads(json.dumps(request))
        changed['roles']['Evaluator']['inputs'].update(change)
        report = rows.run(f'rows-{name}', changed, refuses='entry-run-incomplete')
        journal.check(f'rows {name}: ring-input-shape', stopped(report) == 'refused:ring-input-shape')

    polynomials = Client(toolchain, journal, directory, 'CoefficientResiduals')
    request = maintained('coefficients-honest')
    inputs = request['roles']['Evaluator']['inputs']
    cells = unframe(inputs['coefficients'])
    for name, change, cause in [
            ('width', {'width': inputs['width'] + 1}, 'refused:ring-input-shape'),
            ('short', {'coefficients': frame(cells[:-1])}, 'refused:ring-input-shape'),
            # A width the provider cannot represent refuses even with matching cells.
            ('provider-width', {'coefficients': frame([0] * SLOTS * 66), 'width': 66},
             'refused:ring-coefficient-width')]:
        changed = json.loads(json.dumps(request))
        changed['roles']['Evaluator']['inputs'].update(change)
        report = polynomials.run(f'coefficients-{name}', changed, refuses='entry-run-incomplete')
        journal.check(f'coefficients {name}: {cause}', stopped(report) == cause)

    points = Client(toolchain, journal, directory, 'PointResiduals')
    request = maintained('points-honest')
    inputs = request['roles']['Evaluator']['inputs']
    changed = json.loads(json.dumps(request))
    changed['roles']['Evaluator']['inputs']['assignments'] = frame(
        unframe(inputs['assignments'], extension=True)[:-1], extension=True)
    report = points.run('points-short', changed, refuses='entry-run-incomplete')
    journal.check('points short: ring-input-shape', stopped(report) == 'refused:ring-input-shape')
    # A KoalaBear frame is not an Ext8 vector.
    changed['roles']['Evaluator']['inputs']['assignments'] = maintained('rows-honest')[
        'roles']['Evaluator']['inputs']['assignments']
    points.run('points-base-frame', changed, refuses=True)


def test_arena_authority_comes_from_the_host_manifest(toolchain, journal, directory):
    client = Client(toolchain, journal, directory, 'RowResiduals')
    request = maintained('rows-honest')
    report = client.run('no-manifest', request, assets=None, refuses='entry-run-incomplete')
    journal.check('no manifest: ring-asset-missing', stopped(report) == 'refused:ring-asset-missing')
    # Another export's manifest is valid but does not contain the bound arena.
    other = 'compiler/adapters/plonky3/fixtures/counter-guarded/ring-assets.json'
    report = client.run('other-export', request, assets=other, refuses='entry-run-incomplete')
    journal.check('other export: ring-asset-missing', stopped(report) == 'refused:ring-asset-missing')
    # The bound identity cannot name a stale or different arena.
    stale = journal.write('stale-assets.json', ['zkc.ring-assets/0', [
        [EXPORT['arena_sha256'], str(FIXTURES / 'counter-guarded/arena.json')]]])
    client.run('stale-arena', request, assets=stale, refuses='ring-asset-identity')
    changed = json.loads(json.dumps(ARENA))
    constant = next(node for node in changed[2] if node[0] == 'constant')
    constant[2] = str(int(constant[2]) + 1)
    changed_path = directory / 'changed.ring.json'
    changed_path.write_text(json.dumps(changed, separators=(',', ':')))
    edited = journal.write('edited-assets.json', ['zkc.ring-assets/0', [
        [EXPORT['arena_sha256'], str(changed_path)]]])
    client.run('edited-arena', request, assets=edited, refuses='ring-asset-identity')


def test_satisfied_describes_only_the_supplied_assignment(toolchain, journal, directory):
    # The source cannot tell a closed view from an arbitrary matrix: zero
    # selectors and zero reads make every residual zero. Satisfaction of the
    # AIR rests on the adapter's view of an authorized instance and its trace.
    client = Client(toolchain, journal, directory, 'RowResiduals')
    request = maintained('rows-changed-trace')
    inputs = request['roles']['Evaluator']['inputs']
    inputs['assignments'] = frame([0] * (inputs['rows'] * SLOTS))
    actual = client.run('zero-assignment', request)
    assert actual['satisfied'] is True
    assert unframe(actual['residuals']) == [0] * (inputs['rows'] * ASSERTIONS)
