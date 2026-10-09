"""The polynomial view of a captured Bundle table through source and the Entry Host.

A source client binds the recurrence Bundle through the four polynomial table
kernels. Shapes, descriptors and scopes are compared with values derived by
hand from the Bundle text; point values are compared with the recurrence's
constraints, written from its AIR definition and evaluated in the independent
integer model of `koala-bear.ext8-binomial3`.
"""
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
entry Polynomial = View;
'''


def source(field='Extension', table=0):
    return SOURCE.replace('FIELD', field).replace('TABLE', str(table))


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
    return [words[i:i + 8] for i in range(0, len(words), 8)] if extension else words


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
        self.package = directory / 'polynomial.entry'
        report = journal.json([toolchain.runtime, 'compile', f'--compiler={toolchain.compiler}',
                               f'--module=polynomial_view={module}',
                               f'--asset=recurrence=relation-bundle-json={asset}',
                               '--entry=polynomial_view::Polynomial',
                               f'--output={self.package}'], refuses=refuses)
        self.pin = None if refuses else report['package_sha256']

    def run(self, name, inputs, refuses=None):
        request = {'format': 'zkc.entry-run/0', 'session': 'relation_table_polynomial',
                   'roles': {'Evaluator': {'inputs': inputs}}}
        path = self.journal.write(f'{name}.request.json', request)
        output = self.directory / f'{name}.outputs.json'
        command = [self.tools.runtime, 'run', self.package, self.pin, path, f'--results={output}']
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
        journal.check(f'shape {case}', actual['shape'] == SHAPE)
        journal.check(f'input {slot}', actual['input'] == INPUTS[slot])
        journal.check(f'scope {assertion}', actual['scope'] == SCOPES[assertion])
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
    assert actual['shape'] == SHAPE
    assert unframe(actual['ood_values'], extension=True) == reference(ood)
    assert unframe(actual['base_values'], extension=True) == reference(other)


@pytest.mark.parametrize('mutation,code', [
    ('missing', 'entry-asset-missing'),
    ('tampered', 'relation-asset-identity'),
    ('table', 'relation-table-index'),
    ('carrier', 'entry-asset-carrier'),
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
            # A KoalaBear reference to an Ext8 table, under that table's identity.
            body = json.dumps(extension_bundle(), separators=(',', ':'))
            replacement = sha256(body.encode()).hexdigest()
            candidate = candidate.replace(identity, replacement)
            package['assets'] = [[replacement, body]]
        artifact['candidate'] = candidate
        package['artifact'] = json.dumps(artifact, separators=(',', ':'))
    client.repackage(package)
    result = client.run(mutation, inputs(), refuses=code)
    assert result['phase'] == 'admission'
