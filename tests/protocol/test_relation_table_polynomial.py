"""The polynomial view of a captured Bundle table through source and the Entry Host.

A source client binds the recurrence Bundle through the four polynomial table
kernels. Shapes, descriptors and scopes are compared with values derived by
hand from the Bundle text; point values are compared with the recurrence's
constraints, written from its AIR definition and evaluated in the independent
integer model of `koala-bear.ext8-binomial3`.
"""
from input_files import input_files, decimal_values
import json
from hashlib import sha256
from pathlib import Path

import pytest

import octic_reference as octic

ROOT = Path(__file__).resolve().parents[2]
RECURRENCE = ROOT / 'compiler/adapters/plonky3/fixtures/recurrence'
BUNDLE = (RECURRENCE / 'bundle.json').read_text().strip()
P = octic.P

SOURCE = '''
module polynomial_view;
domain Base = field("koala-bear");
domain Extension = field("koala-bear.ext8-binomial3");
domain Recurrence = bundle(asset recurrence);
type Vector<F: Field> = builtin("vector", F);

// Field, table and relation are static; the height and indices are data.
fn shape_of<F: Field, Table: nat, B: Bundle>(height: index)
    -> (index, index, index, index, index, index, index) {
  return kernel<F,Table>("relation.table_shape", height; B);
}
fn input_of<F: Field, Table: nat, B: Bundle>(height: index, slot: index)
    -> (index, index, index) {
  return kernel<F,Table>("relation.table_input", height, slot; B);
}
fn scope_of<F: Field, Table: nat, B: Bundle>(height: index, assertion: index)
    -> (index, index) {
  return kernel<F,Table>("relation.table_scope", height, assertion; B);
}
fn point_of<F: Field, Table: nat, B: Bundle>(assignments: Vector<F>) -> Vector<F> {
  return kernel<F,Table>("relation.table_point", assignments; B);
}

protocol View roles(Evaluator)
    (height: index @Evaluator, slot: index @Evaluator,
     assertion: index @Evaluator, ood: Vector<Extension> @Evaluator,
     base: Vector<Base> @Evaluator)
    -> (shape: (index, index, index, index, index, index, index) @Evaluator,
        input: (index, index, index) @Evaluator,
        scope: (index, index) @Evaluator,
        ood_values: Vector<Extension> @Evaluator,
        base_values: Vector<Base> @Evaluator) {
  let s @Evaluator = shape_of<FIELD,TABLE,Recurrence>(height);
  let i @Evaluator = input_of<FIELD,TABLE,Recurrence>(height, slot);
  let c @Evaluator = scope_of<FIELD,TABLE,Recurrence>(height, assertion);
  let e @Evaluator = point_of<Extension,TABLE,Recurrence>(ood);
  let b @Evaluator = point_of<Base,TABLE,Recurrence>(base);
  return (shape = s, input = i, scope = c, ood_values = e, base_values = b);
}
run Polynomial = View;
'''


def source(field='Extension', table=0):
    return SOURCE.replace('FIELD', field).replace('TABLE', str(table))


def frame(values, extension=False):
    return [[str(w) for w in v] for v in values] if extension else [str(v) for v in values]


def unframe(text, extension=False):
    return [[int(w) for w in v] for v in text] if extension else [int(v) for v in text]


def base(n):
    return [n % P] + [0] * 7


def sub(a, b):
    return octic.add(a, [(P - x) % P for x in b])


def reference(v):
    """Recurrence constraints from the AIR definition, in assertion order.

    Inputs: x, y, p, acc; next-row x', y', acc'; fixed k; x0, y0, final acc.
    """
    x, y, p, acc, x1, y1, acc1, k, x0, y0, last = v
    m = octic.mul
    return [sub(p, m(x, y)), sub(x, x0), sub(y, y0), acc, sub(x1, y),
            sub(y1, octic.add(octic.add(p, k), base(123456789))),
            sub(acc1, octic.add(acc, m(m(p, x), k))), sub(acc, last), sub(x1, x0)]


def points(seed, n):
    state, result = seed, []
    for _ in range(n):
        value = []
        for _ in range(8):
            state = (state * 6364136223846793005 + 1442695040888963407) % 2**64
            value.append((state >> 33) % P)
        result.append(value)
    return result


class Client:
    def __init__(self, toolchain, journal, directory, text, bundle=None, refuses=None):
        self.tools, self.journal, self.directory = toolchain, journal, directory
        module = directory / 'polynomial_view.zkc'
        module.write_text(text)
        asset = journal.write('bundle.json', bundle) if bundle else RECURRENCE / 'bundle.json'
        self.package = directory / 'polynomial.zkpkg'
        report = journal.json([toolchain.runtime, '--json', 'compile', f'--compiler={toolchain.compiler}',
                               f'--module=polynomial_view={module}',
                               f'--asset=recurrence=relation-bundle-json={asset}',
                               'polynomial_view::Polynomial',
                               f'--output={self.package}'], refuses=refuses)
        self.pin = None if refuses else report['package_sha256']

    def run(self, name, inputs, refuses=None):
        path = input_files(self.journal, name, roles={'Evaluator': {'inputs': inputs}})
        output = self.directory / f'{name}.outputs.json'
        command = [self.tools.runtime, '--json', 'run', f'--package={self.package}', f'--sha256={self.pin}', *path, f'--results={output}']
        report = self.journal.json(command, cwd=ROOT, refuses=refuses)
        if refuses:
            assert report['status'] == 'refused'
            assert not output.exists(), 'a refused run published outputs'
            return report
        assert report['status'] == 'executed'
        return json.loads(output.read_text())['roles']['Evaluator']

    def repackage(self, package):
        text = json.dumps(package, separators=(',', ':'))
        self.package.write_text(text)
        self.pin = sha256(text.encode()).hexdigest()


def stopped(report):
    (role,) = report['execution']['roles']
    state, detail = role['after']
    assert state == 'stopped' and detail['cause'][0] == 'backend'
    return detail['cause'][1]['text']


def inputs(height=8, slot=0, assertion=0, ood=None, row=None):
    ood = points(1, 11) if ood is None else ood
    row = [v[0] for v in points(2, 11)] if row is None else row
    return {'height': height, 'slot': slot, 'assertion': assertion,
            'ood': frame(ood, extension=True), 'base': frame(row)}


# Hand-derived from the Bundle text: widths 4 witness and 1 configuration,
# 3 public slots, 11 inputs and 9 assertions; the cubic transition on rows
# [0, 7) has quotient degree 3*7 - 7 = 14, two chunks of length 8.
SHAPE = [4, 1, 0, 3, 11, 9, 2]
INPUTS = [[1, 0, 0], [1, 1, 0], [1, 2, 0], [1, 3, 0], [1, 0, 1], [1, 1, 1], [1, 3, 1],
          [2, 0, 0], [0, 0, 0], [0, 1, 0], [0, 2, 0]]
SCOPES = [[0, 8], [0, 1], [0, 1], [0, 1], [0, 7], [0, 7], [0, 7], [7, 8], [7, 8]]


def test_shape_descriptors_scopes_and_points_match_independent_derivations(
        toolchain, journal, directory):
    client = Client(toolchain, journal, directory, source())
    package = json.loads(client.package.read_text())
    assert package['assets'] == [[sha256(BUNDLE.encode()).hexdigest(), BUNDLE]]
    for case, (slot, assertion) in enumerate(zip(range(11), [0, 1, 2, 3, 4, 5, 6, 7, 8, 8, 0])):
        ood = points(10 + case, 11)
        row = [v[0] for v in points(30 + case, 11)]
        actual = client.run(f'view-{case}', inputs(8, slot, assertion, ood, row))
        journal.check(f'shape {case}', actual['shape'] == decimal_values(SHAPE))
        journal.check(f'input {slot}', actual['input'] == decimal_values(INPUTS[slot]))
        journal.check(f'scope {assertion}', actual['scope'] == decimal_values(SCOPES[assertion]))
        journal.check(f'Ext8 point {case} equals the integer model',
                      unframe(actual['ood_values'], extension=True) == reference(ood))
        journal.check(f'base point {case} equals its embedding',
                      unframe(actual['base_values']) ==
                      [v[0] for v in reference([base(n) for n in row])])


@pytest.mark.parametrize('name,change,cause', [
    ('height-policy', {'height': 16}, 'bundle-height'),
    ('height-two-adic', {'height': 6}, 'bundle-polynomial-two-adic'),
    ('height-one', {'height': 1}, 'bundle-polynomial-two-adic'),
    ('slot', {'slot': 11}, 'relation-table-input-index'),
    ('assertion', {'assertion': 9}, 'relation-table-assertion-index'),
    ('short-point', {'ood': frame(points(3, 10), extension=True)}, 'relation-table-point-shape'),
    ('long-point', {'base': frame([0] * 12)}, 'relation-table-point-shape'),
])
def test_execution_refuses_heights_indices_and_lengths(
        toolchain, journal, directory, name, change, cause):
    client = Client(toolchain, journal, directory, source())
    report = client.run(name, {**inputs(), **change}, refuses='entry-run-incomplete')
    journal.check(f'{name}: {cause}', stopped(report) == f'refused:{cause}')


def extension_bundle():
    """The recurrence over Ext8 slots, groups, inputs and constants."""
    return json.loads(BUNDLE.replace('"koala-bear"', '"koala-bear.ext8-binomial3"'))


@pytest.mark.parametrize('field,table,bundle,code', [
    ('Extension', 1, None, 'source.asset-table'),
    ('Base', 0, 'extension', 'source.asset-carrier'),
    ('Extension', 0, 'height', 'source.asset-table'),
])
def test_source_closure_checks_table_carrier_and_two_adic_premise(
        toolchain, journal, directory, field, table, bundle, code):
    text = source(field, table)
    if bundle == 'extension':
        # An Ext8 arena is never narrowed to KoalaBear. Points stay Ext8.
        text = text.replace('point_of<Base,', 'point_of<Extension,').replace(
            'base: Vector<Base>', 'base: Vector<Extension>').replace(
            'base_values: Vector<Base>', 'base_values: Vector<Extension>')
        value = extension_bundle()
    elif bundle == 'height':
        value = json.loads(BUNDLE)
        value[3][0][2] = ['fixed', 12]
    else:
        value = None
    Client(toolchain, journal, directory, text, value, refuses=code)


def test_extension_tables_keep_every_coordinate(toolchain, journal, directory):
    text = source().replace('point_of<Base,', 'point_of<Extension,').replace(
        'base: Vector<Base>', 'base: Vector<Extension>').replace(
        'base_values: Vector<Base>', 'base_values: Vector<Extension>')
    client = Client(toolchain, journal, directory, text, extension_bundle())
    ood, other = points(50, 11), points(51, 11)
    request = inputs(ood=ood)
    request['base'] = frame(other, extension=True)
    actual = client.run('extension', request)
    assert actual['shape'] == decimal_values(SHAPE)
    assert unframe(actual['ood_values'], extension=True) == reference(ood)
    assert unframe(actual['base_values'], extension=True) == reference(other)


@pytest.mark.parametrize('mutation,code', [
    ('missing', 'entry-asset-missing'),
    ('tampered', 'relation-asset-identity'),
    ('table', 'relation-table-index'),
    ('carrier', 'entry-asset-carrier'),
    ('non-two-adic', 'refused:bundle-polynomial-two-adic'),
])
def test_host_preflight_checks_every_polynomial_reference(
        toolchain, journal, directory, mutation, code):
    client = Client(toolchain, journal, directory, source('Base'))
    package = json.loads(client.package.read_text())
    identity = sha256(BUNDLE.encode()).hexdigest()
    if mutation == 'missing':
        package['assets'] = []
    elif mutation == 'tampered':
        body = json.loads(BUNDLE)
        body[3][0][0] = 'changed-table-name'
        package['assets'] = [[identity, json.dumps(body, separators=(',', ':'))]]
    else:
        artifact = json.loads(package['artifact'])
        candidate = artifact['candidate']
        if mutation == 'table':
            program = json.loads(candidate)
            for binding in program[1]:
                if binding[1] == 'relation.table_shape':
                    binding[2][1] = '1'
            candidate = json.dumps(program, separators=(',', ':'))
        else:
            if mutation == 'non-two-adic':
                body = json.loads(BUNDLE)
                body[3][0][2] = ['fixed', 3]
            else:
                # A KoalaBear reference to an Ext8 table, under its own identity.
                body = extension_bundle()
            body = json.dumps(body, separators=(',', ':'))
            replacement = sha256(body.encode()).hexdigest()
            candidate = candidate.replace(identity, replacement)
            package['assets'] = [[replacement, body]]
        artifact['candidate'] = candidate
        package['artifact'] = json.dumps(artifact, separators=(',', ':'))
    client.repackage(package)
    result = client.run(mutation, inputs(), refuses=code)
    assert result['phase'] == 'admission'


BATCH = '''
module polynomial_view;
domain Base = field("koala-bear");
domain Extension = field("koala-bear.ext8-binomial3");
domain Recurrence = bundle(asset recurrence);
type Vector<F: Field> = builtin("vector", F);

// The batch substitution, the same substitution one row at a time, and the
// dense residuals of the actual columns.
fn points_of<F: Field, Table: nat, B: Bundle>(assignments: Vector<F>, rows: index)
    -> Vector<F> {
  return kernel<F,Table>("relation.table_points", assignments, rows; B);
}
fn point_of<F: Field, Table: nat, B: Bundle>(assignments: Vector<F>) -> Vector<F> {
  return kernel<F,Table>("relation.table_point", assignments; B);
}
fn rows_of<F: Field, Table: nat, B: Bundle>(w: Vector<F>, c: Vector<F>, p: Vector<F>,
    h: index) -> Vector<F> {
  return kernel<F,Table>("relation.table_rows", w, c, p, h; B);
}

protocol Batch roles(Evaluator)
    (subgroup: Vector<Base> @Evaluator, subgroup_rows: index @Evaluator,
     ood: Vector<Extension> @Evaluator, ood_rows: index @Evaluator,
     single: Vector<Extension> @Evaluator, witness: Vector<Base> @Evaluator,
     configuration: Vector<Base> @Evaluator, public_data: Vector<Base> @Evaluator,
     height: index @Evaluator)
    -> (subgroup_values: Vector<Base> @Evaluator,
        ood_values: Vector<Extension> @Evaluator,
        single_values: Vector<Extension> @Evaluator,
        dense: Vector<Base> @Evaluator) {
  let s @Evaluator = points_of<Base,0,Recurrence>(subgroup, subgroup_rows);
  let o @Evaluator = points_of<Extension,0,Recurrence>(ood, ood_rows);
  let p @Evaluator = point_of<Extension,0,Recurrence>(single);
  let d @Evaluator = rows_of<Base,0,Recurrence>(witness, configuration, public_data, height);
  return (subgroup_values = s, ood_values = o, single_values = p, dense = d);
}
run Polynomial = Batch;
'''

# The recurrence fixture's honest data: one witness group of width 4, one
# configuration group of width 1 and three public slots.
WITNESS = [int(v) for v in json.loads((RECURRENCE / 'bundle-witness.json').read_text())[2][0][0]]
CONFIGURATION = [int(v) for v in
                 json.loads((RECURRENCE / 'bundle-configuration.json').read_text())[2][0][1][0]]
PUBLICS = [int(v) for v in json.loads((RECURRENCE / 'bundle-instance.json').read_text())[2]]


def subgroup_assignments(witness, height=8):
    """Row-major assignments of every arena input on the subgroup of order 8,
    read through the hand-derived descriptors."""
    matrices = {1: (witness, 4), 2: (CONFIGURATION, 1)}
    values = []
    for row in range(height):
        for kind, column, rotation in INPUTS:
            if kind == 0:
                values.append(PUBLICS[column])
            else:
                matrix, width = matrices[kind]
                values.append(matrix[((row + rotation) % height) * width + column])
    return values


def batch_inputs(witness=WITNESS, ood=None, **change):
    ood = points(70, 5 * 11) if ood is None else ood
    request = {'subgroup': frame(subgroup_assignments(witness)), 'subgroup_rows': 8,
               'ood': frame(ood, extension=True), 'ood_rows': len(ood) // 11,
               'single': frame(ood[33:44], extension=True), 'witness': frame(witness),
               'configuration': frame(CONFIGURATION), 'public_data': frame(PUBLICS),
               'height': 8}
    return {**request, **change}


@pytest.mark.parametrize('changed', [False, True])
def test_batches_match_points_dense_rows_and_the_integer_model(
        toolchain, journal, directory, changed):
    client = Client(toolchain, journal, directory, BATCH)
    witness = list(WITNESS)
    if changed:
        witness[0] = 3  # Nonzero residuals on the first and, wrapping, last row.
    actual = client.run('batch', batch_inputs(witness))
    assignments = subgroup_assignments(witness)
    batch = unframe(actual['subgroup_values'])
    expected = [value[0] for row in range(8)
                for value in reference([base(n) for n in assignments[row * 11:(row + 1) * 11]])]
    journal.check('subgroup batch equals the integer model', batch == expected)
    dense, nonzero = unframe(actual['dense']), 0
    for assertion, (begin, end) in enumerate(SCOPES):
        for row in range(begin, end):
            at = row * 9 + assertion
            journal.check(f'assertion {assertion} row {row} equals the dense residual',
                          batch[at] == dense[at])
            nonzero += dense[at] != 0
    journal.check('changed data has nonzero scoped residuals', (nonzero > 0) == changed)
    ood = points(70, 5 * 11)
    values = unframe(actual['ood_values'], extension=True)
    journal.check('Ext8 batch equals the integer model', values == [
        value for row in range(5) for value in reference(ood[row * 11:(row + 1) * 11])])
    journal.check('one row of the batch equals the scalar point',
                  unframe(actual['single_values'], extension=True) == values[27:36])


def test_empty_batches_and_shape_refusals(toolchain, journal, directory):
    client = Client(toolchain, journal, directory, BATCH)
    actual = client.run('empty', batch_inputs(
        ood=[], subgroup=frame([]), subgroup_rows=0,
        single=frame(points(5, 11), extension=True)))
    journal.check('zero rows give empty results',
                  unframe(actual['subgroup_values']) == []
                  and unframe(actual['ood_values'], extension=True) == [])
    for name, change in [('long', {'subgroup': frame([0] * 89)}),
                         ('short-rows', {'ood_rows': 6}),
                         ('huge-rows', {'ood_rows': 2**40})]:
        report = client.run(name, batch_inputs(**change), refuses='entry-run-incomplete')
        journal.check(f'{name}: point shape',
                      stopped(report) == 'refused:relation-table-point-shape')


def test_host_preflight_checks_batch_references(toolchain, journal, directory):
    client = Client(toolchain, journal, directory, BATCH)
    package = json.loads(client.package.read_text())
    artifact = json.loads(package['artifact'])
    program = json.loads(artifact['candidate'])
    changed = 0
    for binding in program[1]:
        if binding[1] == 'relation.table_points':
            binding[2][1] = '1'
            changed += 1
    assert changed
    artifact['candidate'] = json.dumps(program, separators=(',', ':'))
    package['artifact'] = json.dumps(artifact, separators=(',', ':'))
    client.repackage(package)
    result = client.run('points-table', batch_inputs(), refuses='relation-table-index')
    assert result['phase'] == 'admission'
