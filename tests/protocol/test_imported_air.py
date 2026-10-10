"""Imported AIR bindings and polynomial views through source and the Entry Host.

The adapter emits actual trace requests and prepared polynomial assignments from
the recurrence fixture. Their expectations come from direct `Air::eval`, not
from the exported arena. These tests read the
committed fixtures and never build the optional adapter; its fixture check
regenerates the same files from the pinned upstream AIR.
"""

from input_files import input_files
import json
from hashlib import sha256
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
PROJECT = ROOT / 'examples/projects/imported-air'
FIXTURES = ROOT / 'compiler/adapters/plonky3/fixtures'
RECURRENCE = FIXTURES / 'recurrence'
P = 2130706433
EXPECTED = json.loads((RECURRENCE / 'source-expected.json').read_text())
EXPORT = json.loads((RECURRENCE / 'export.json').read_text())
ARENA = json.loads((RECURRENCE / 'arena.json').read_text())
ASSERTIONS = len(EXPORT['assertions'])
SLOTS = len(EXPORT['slots'])


def frame(values, extension=False):
    return [[str(w) for w in v] for v in values] if extension else [str(v) for v in values]


def unframe(text, extension=False):
    return [[int(w) for w in v] for v in text] if extension else [int(v) for v in text]


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
    values = json.loads((RECURRENCE / f'source-{case}.json').read_text())
    for name in ('height', 'width', 'rows', 'points'):
        if name in values:
            values[name] = int(values[name])
    return values


class Client:
    """One compiled Entry of the source client, run from the repository root."""

    def __init__(self, toolchain, journal, directory, entry, flags=()):
        self.tools, self.journal, self.directory = toolchain, journal, directory
        self.package = directory / f'{entry}.zkpkg'
        report = journal.json([toolchain.runtime, '--json', 'compile', f'--compiler={toolchain.compiler}',
                               f'--project={PROJECT}/zkc.toml',
                               f'imported_air::{entry}', f'--output={self.package}', *flags])
        self.pin = report['package_sha256']

    def run(self, name, request, refuses=None):
        path = input_files(self.journal, name, roles={'Evaluator': {'inputs': request}})
        output = self.directory / f'{name}.outputs.json'
        command = [self.tools.runtime, '--json', 'run', f'--package={self.package}', f'--sha256={self.pin}', *path, f'--results={output}']
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


def test_source_binds_the_exported_arena(toolchain, journal, directory):
    client = Client(toolchain, journal, directory, 'RowResiduals')
    package = json.loads(client.package.read_text())
    arena = (RECURRENCE / 'arena.json').read_bytes()
    instance = json.loads((RECURRENCE / 'instance.json').read_text())
    assert [EXPORT['arena_sha256'], arena.decode()] in package['assets']
    # The interface also retains its declared relation even when this Entry
    # only invokes the prepared polynomial view.
    bundle = (RECURRENCE / 'bundle.json').read_text().strip()
    assert [sha256(bundle.encode()).hexdigest(), bundle] in package['assets']
    assert len(package['assets']) == 2
    assert EXPORT['arena_sha256'] == sha256(arena).hexdigest()
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
@pytest.mark.parametrize('entry', ['TraceResiduals', 'RowResiduals', 'CoefficientResiduals', 'PointResiduals'])
def test_maintained_requests_match_direct_evaluation(toolchain, journal, directory, entry, flags):
    client = Client(toolchain, journal, directory, entry, flags)
    cases = {name: case for name, case in EXPECTED.items() if case['entry'] == entry}
    assert cases
    for name, expected in cases.items():
        request = maintained(name)
        actual = client.run(name, request)
        inputs = request
        if entry in ('TraceResiduals', 'RowResiduals'):
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
    rows = maintained('rows-honest')
    coefficients = maintained('coefficients-honest')
    assert len(unframe(rows['assignments'])) == rows['rows'] * SLOTS
    assert len(unframe(coefficients['coefficients'])) == coefficients['width'] * SLOTS
    assert len(numbers(EXPECTED['rows-honest']['residuals'])) == rows['rows'] * ASSERTIONS


def test_wrong_shapes_refuse_before_evaluation(toolchain, journal, directory):
    rows = Client(toolchain, journal, directory, 'RowResiduals')
    request = maintained('rows-honest')
    inputs = request
    cells = unframe(inputs['assignments'])
    for name, change in [('short', {'assignments': frame(cells[:-1])}),
                         ('long', {'assignments': frame(cells + [0])}),
                         ('row-count', {'rows': inputs['rows'] - 1})]:
        changed = json.loads(json.dumps(request))
        changed.update(change)
        report = rows.run(f'rows-{name}', changed, refuses='entry-run-incomplete')
        journal.check(f'rows {name}: ring-input-shape', stopped(report) == 'refused:ring-input-shape')

    polynomials = Client(toolchain, journal, directory, 'CoefficientResiduals')
    request = maintained('coefficients-honest')
    inputs = request
    cells = unframe(inputs['coefficients'])
    for name, change, cause in [
            ('width', {'width': inputs['width'] + 1}, 'refused:ring-input-shape'),
            ('short', {'coefficients': frame(cells[:-1])}, 'refused:ring-input-shape'),
            # A width the provider cannot represent refuses even with matching cells.
            ('provider-width', {'coefficients': frame([0] * SLOTS * 66), 'width': 66},
             'refused:ring-coefficient-width')]:
        changed = json.loads(json.dumps(request))
        changed.update(change)
        report = polynomials.run(f'coefficients-{name}', changed, refuses='entry-run-incomplete')
        journal.check(f'coefficients {name}: {cause}', stopped(report) == cause)

    points = Client(toolchain, journal, directory, 'PointResiduals')
    request = maintained('points-honest')
    inputs = request
    changed = json.loads(json.dumps(request))
    changed['assignments'] = frame(
        unframe(inputs['assignments'], extension=True)[:-1], extension=True)
    report = points.run('points-short', changed, refuses='entry-run-incomplete')
    journal.check('points short: ring-input-shape', stopped(report) == 'refused:ring-input-shape')
    # Extension coordinates require the exact native degree.
    changed['assignments'] = [['1', '0']]
    points.run('points-base-frame', changed, refuses=True)


def test_arena_authority_comes_from_the_package(toolchain, journal, directory):
    client = Client(toolchain, journal, directory, 'RowResiduals')
    request = maintained('rows-honest')
    original = json.loads(client.package.read_text())
    for name, assets, refusal in [
        ('missing', [], 'entry-asset-missing'),
        ('stale', [[EXPORT['arena_sha256'],
                    (FIXTURES / 'counter-guarded/arena.json').read_text()]], 'ring-asset-identity'),
    ]:
        package = {**original, 'assets': assets}
        text = json.dumps(package, separators=(',', ':'))
        client.package.write_text(text)
        client.pin = sha256(text.encode()).hexdigest()
        client.run(name, request, refuses=refusal)
    # Even a valid edited arena cannot stand under the captured identity.
    changed = json.loads(json.dumps(ARENA))
    constant = next(node for node in changed[2] if node[0] == 'constant')
    constant[2] = str(int(constant[2]) + 1)
    original['assets'] = [[EXPORT['arena_sha256'], json.dumps(changed, separators=(',', ':'))]]
    text = json.dumps(original, separators=(',', ':'))
    client.package.write_text(text)
    client.pin = sha256(text.encode()).hexdigest()
    client.run('edited-arena', request, refuses='ring-asset-identity')


def test_satisfied_describes_only_the_supplied_assignment(toolchain, journal, directory):
    # The source cannot tell a closed view from an arbitrary matrix: zero
    # selectors and zero reads make every residual zero. Satisfaction of the
    # AIR rests on the adapter's view of an authorized instance and its trace.
    client = Client(toolchain, journal, directory, 'RowResiduals')
    request = maintained('rows-changed-trace')
    inputs = request
    inputs['assignments'] = frame([0] * (inputs['rows'] * SLOTS))
    actual = client.run('zero-assignment', request)
    assert actual['satisfied'] is True
    assert unframe(actual['residuals']) == [0] * (inputs['rows'] * ASSERTIONS)


def test_trace_view_uses_bound_reads_configuration_and_scopes(toolchain, journal, directory):
    client = Client(toolchain, journal, directory, 'TraceResiduals')
    request = maintained('trace-honest')
    changed = json.loads(json.dumps(request))
    inputs = changed
    configuration = unframe(inputs['configuration'])
    configuration[0] += 1
    inputs['configuration'] = frame(configuration)
    actual = client.run('changed-configuration', changed)
    # On row zero, y_next - x*y - fixed - C changes by -1, and
    # acc_next - acc - x*y*x*fixed changes by -20 (x=2, y=5).
    expected = [0] * (inputs['height'] * ASSERTIONS)
    expected[5], expected[6] = P - 1, P - 20
    assert unframe(actual['residuals']) == expected
    assert actual['satisfied'] is False

    changed = json.loads(json.dumps(request))
    inputs = changed
    inputs['trace'] = frame([0] * len(unframe(inputs['trace'])))
    actual = client.run('zero-trace', changed)
    assert actual['satisfied'] is False
    assert any(unframe(actual['residuals']))


def test_trace_view_refuses_fabricated_assignments_and_wrong_shapes(toolchain, journal, directory):
    client = Client(toolchain, journal, directory, 'TraceResiduals')
    request = maintained('trace-honest')
    inputs = request
    cases = [
        ('prepared', 'trace', maintained('rows-honest')['assignments'],
         'relation-table-witness-shape'),
        ('zero-prepared', 'trace', frame([0] * (SLOTS * inputs['height'])),
         'relation-table-witness-shape'),
        ('short-trace', 'trace', frame(unframe(inputs['trace'])[:-1]), 'relation-table-witness-shape'),
        ('short-configuration', 'configuration', frame(unframe(inputs['configuration'])[:-1]),
         'relation-table-configuration-shape'),
        ('short-public', 'public_data', frame(unframe(inputs['public_data'])[:-1]),
         'relation-table-public-shape'),
        ('height', 'height', 7, 'bundle-height'),
    ]
    for name, port, value, cause in cases:
        changed = json.loads(json.dumps(request))
        changed[port] = value
        report = client.run(name, changed, refuses='entry-run-incomplete')
        assert stopped(report) == f'refused:{cause}'


@pytest.mark.parametrize('flags', [[], ['--no-simplify'], ['--release-storage']])
def test_disclosed_trace_proof_uses_verifier_data_and_packaged_relation(
        toolchain, journal, directory, flags):
    client = Client(toolchain, journal, directory, 'DisclosedTraceProof', flags)
    inputs = maintained('trace-honest')
    def scalar(n):
        return str(n)

    x0, y0, final_acc = unframe(inputs['public_data'])
    public = {'configuration': inputs['configuration'], 'height': inputs['height'],
              'x0': scalar(x0), 'y0': scalar(y0), 'final_acc': scalar(final_acc)}
    producer = input_files(journal, 'producer.json', public=public, witness={'trace': inputs['trace']})
    verifier = input_files(journal, 'verifier.json', public=public)
    proof = directory / 'trace.bin'
    journal.json([toolchain.runtime, '--json', 'prove', f'--package={client.package}', f'--sha256={client.pin}', *producer, f'--output={proof}', '--allow-header-only'])
    result = journal.json([toolchain.runtime, '--json', 'verify', f'--package={client.package}', f'--sha256={client.pin}', *verifier, f'--proof={proof}', '--allow-header-only'])
    assert result['status'] == 'accepted'
    package = json.loads(client.package.read_text())
    interface = json.loads(package['interface'])
    (relation,) = interface['relations']
    assert relation['definition']['kind'] == 'bundle'
    assert [i['purpose'] for i in relation['inputs']] == [
        'statement', 'statement', 'statement', 'witness', 'parameter']
    (asset,) = package['assets']
    assert asset[0] == relation['definition']['asset'] == sha256(asset[1].encode()).hexdigest()
    assert json.loads(asset[1])[0] == 'zkc.relation-bundle/0'

    bad_trace = maintained('trace-changed-trace')['trace']
    producer = input_files(journal, 'invalid-producer.json', public=public, witness={'trace': bad_trace})
    invalid = directory / 'invalid-trace.bin'
    journal.json([toolchain.runtime, '--json', 'prove', f'--package={client.package}', f'--sha256={client.pin}', *producer, f'--output={invalid}', '--allow-header-only'])
    journal.json([toolchain.runtime, '--json', 'verify', f'--package={client.package}', f'--sha256={client.pin}', *verifier, f'--proof={invalid}', '--allow-header-only'], refuses='artifact-rejected')


@pytest.mark.parametrize('extra', ['table', 'channel'])
def test_reference_protocol_refuses_relations_with_additional_obligations(
        toolchain, journal, directory, extra):
    bundle = json.loads((RECURRENCE / 'bundle.json').read_text())
    if extra == 'table':
        # This second table always fails. Checking only the first table could
        # otherwise accept a false target with the very same source ABI.
        bundle[3].append(['extra', 'required', ['fixed', 8], 'finite', [],
            ['zkc.ring/0', [], [['constant', 'koala-bear', '1']], [0]],
            [], [[0, ['all']]], []])
    else:
        bundle[2].append(['extra', 'field-balance', ['koala-bear'], 'koala-bear'])
    asset = journal.write(f'{extra}.bundle.json', bundle)
    journal.json([toolchain.runtime, '--json', 'compile', f'--compiler={toolchain.compiler}',
        f'--module=imported_air={PROJECT}/main.zkc',
        f'--asset=export=ring-json={RECURRENCE}/arena.json',
        f'--asset=recurrence=relation-bundle-json={asset}',
        'imported_air::DisclosedTraceProof',
        f'--output={directory}/{extra}.zkpkg'], refuses='source.bound')


@pytest.mark.parametrize('mutation,code', [
    ('missing', 'entry-asset-missing'),
    ('noncanonical', 'entry-asset-canonical'),
    ('identity', 'relation-asset-identity'),
    ('table', 'relation-table-index'),
    ('authority', 'entry-asset-relation'),
])
def test_host_independently_checks_packaged_bundle_and_references(
        toolchain, journal, directory, mutation, code):
    client = Client(toolchain, journal, directory, 'TraceResiduals')
    package = json.loads(client.package.read_text())
    if mutation == 'missing':
        package['assets'] = []
    elif mutation == 'noncanonical':
        package['assets'][0][1] += ' '
    elif mutation == 'identity':
        body = json.loads(package['assets'][0][1])
        body[3][0][0] = 'changed-table-name'
        package['assets'][0][1] = json.dumps(body, separators=(',', ':'))
    elif mutation == 'table':
        artifact = json.loads(package['artifact'])
        program = json.loads(artifact['candidate'])
        for binding in program[1]:
            if binding[1] == 'relation.table_rows':
                binding[2][1] = '1'
        artifact['candidate'] = json.dumps(program, separators=(',', ':'))
        package['artifact'] = json.dumps(artifact, separators=(',', ':'))
    else:
        interface = json.loads(package['interface'])
        proof_client = Client(toolchain, journal, directory, 'DisclosedTraceProof')
        proof_package = json.loads(proof_client.package.read_text())
        interface['relations'] = json.loads(proof_package['interface'])['relations']
        interface['relations'][0]['inputs'][0]['purpose'] = 'parameter'
        package['interface'] = json.dumps(interface, separators=(',', ':'))
    text = json.dumps(package, separators=(',', ':'))
    client.package.write_text(text)
    client.pin = sha256(text.encode()).hexdigest()
    result = client.run(mutation, maintained('trace-honest'), refuses=code)
    assert result['phase'] == 'admission'


@pytest.mark.parametrize('field,table,code', [
    ('koala-bear', 1, 'source.asset-table'),
    ('koala-bear.ext8-binomial3', 0, 'source.asset-carrier'),
])
def test_source_closure_checks_bundle_table_and_field(toolchain, journal, directory,
                                                     field, table, code):
    source = directory / 'reference.zkc'
    source.write_text(f'''
module reference;
domain F = field("{field}");
domain R = bundle(asset recurrence);
type Vector = builtin("vector", F);
fn evaluate(w: Vector, c: Vector, p: Vector, h: index) -> Vector {{
  return kernel<F,{table}>("relation.table_rows", w, c, p, h; R);
}}
protocol Check roles(V)(w: Vector @V, c: Vector @V, p: Vector @V, h: index @V)
    -> (out: Vector @V) {{
  let out @V = evaluate(w, c, p, h);
  return (out = out);
}}
run Run = Check;
''')
    journal.json([toolchain.runtime, '--json', 'compile', f'--compiler={toolchain.compiler}',
        f'--module=reference={source}',
        f'--asset=recurrence=relation-bundle-json={RECURRENCE}/bundle.json',
        'reference::Run', f'--output={directory}/reference.zkpkg'], refuses=code)
