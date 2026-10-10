"""The interaction view of captured Bundle tables through source and the Entry Host.

A source client binds the accumulator machine through the four interaction
kernels and the polynomial batch. Policies and descriptors are compared with
values derived by hand from the machine's definition. Records on each present
table's subgroup, restricted to the reported scopes and summed per channel
tuple, are compared with the balances of the independent C++ and Rust Bundle
evaluators. Records at extension points are compared with the machine's
interaction expressions, written from its definition and evaluated in the
independent integer model of `koala-bear.ext8-binomial3`. A synthetic Bundle
covers the interaction forms the machine does not use. Agreement on these
carriers is evidence about the kernels, not a reduction or a proof.
"""
from hashlib import sha256
from input_files import input_files
import json
from pathlib import Path

import pytest

import octic_reference as octic

ROOT = Path(__file__).resolve().parents[2]
MACHINE = ROOT / 'compiler/adapters/accumulator-machine/fixtures'
MACHINE_TEXT = (MACHINE / 'bundle.json').read_text().strip()
RECURRENCE = ROOT / 'compiler/adapters/plonky3/fixtures/recurrence/bundle.json'
P = octic.P
KB, EXT = 'koala-bear', 'koala-bear.ext8-binomial3'
ONE = [1] + [0] * 7

SOURCE = '''
module interaction_view;
domain Base = field("koala-bear");
domain Extension = field("koala-bear.ext8-binomial3");
domain Machine = bundle(asset machine);
type Vector<F: Field> = builtin("vector", F);

// Field, table and relation are static; heights, indices and points are data.
fn policy_of<F: Field, Table: nat, B: Bundle>() -> (index, index, index, index, index) {
  return kernel<F,Table>("relation.table_policy"; B);
}
fn counts_of<F: Field, Table: nat, B: Bundle>(height: index) -> (index, index) {
  return kernel<F,Table>("relation.table_interactions", height; B);
}
fn interaction_of<F: Field, Table: nat, B: Bundle>(height: index, i: index)
    -> (index, index, index, index, index, index, index, index, index, index, index, index) {
  return kernel<F,Table>("relation.table_interaction", height, i; B);
}
fn records_of<F: Field, Table: nat, B: Bundle>(assignments: Vector<F>, rows: index)
    -> Vector<F> {
  return kernel<F,Table>("relation.table_record_points", assignments, rows; B);
}
fn points_of<F: Field, Table: nat, B: Bundle>(assignments: Vector<F>, rows: index)
    -> Vector<F> {
  return kernel<F,Table>("relation.table_points", assignments, rows; B);
}
// Facts of a generic Bundle term, substituted from the captured asset.
fn facts<B: Bundle>() -> index where B::Channels <= 4 {
  return index<B::Tables * 100 + B::Publics * 10 + B::Channels>();
}
// Stands in for the descriptor of a table without interactions.
fn no_descriptor(h: index)
    -> (index, index, index, index, index, index, index, index, index, index, index, index) {
  return (h, h, h, h, h, h, h, h, h, h, h, h);
}

protocol View roles(Evaluator)
    (height: index @Evaluator, interaction: index @Evaluator,
     subgroup: Vector<SUB> @Evaluator, subgroup_rows: index @Evaluator,
     ood: Vector<Extension> @Evaluator, ood_rows: index @Evaluator)
    -> (policy: (index, index, index, index, index) @Evaluator,
        counts: (index, index) @Evaluator,
        descriptor: (index, index, index, index, index, index, index, index,
                     index, index, index, index) @Evaluator,
        subgroup_records: Vector<SUB> @Evaluator,
        subgroup_residuals: Vector<SUB> @Evaluator,
        ood_records: Vector<Extension> @Evaluator,
        facts: index @Evaluator) {
  let p @Evaluator = policy_of<FIELD,TABLE,Machine>();
  let c @Evaluator = counts_of<FIELD,TABLE,Machine>(height);
  let d @Evaluator = interaction_of<FIELD,TABLE,Machine>(height, interaction);
  let s @Evaluator = records_of<SUB,TABLE,Machine>(subgroup, subgroup_rows);
  let r @Evaluator = points_of<SUB,TABLE,Machine>(subgroup, subgroup_rows);
  let o @Evaluator = records_of<Extension,TABLE,Machine>(ood, ood_rows);
  let f @Evaluator = facts<Machine>();
  return (policy = p, counts = c, descriptor = d, subgroup_records = s,
          subgroup_residuals = r, ood_records = o, facts = f);
}
run Interactions = View;
'''

# Only the policy: no execution height is involved.
POLICY_SOURCE = '''
module interaction_view;
domain Base = field("koala-bear");
domain Extension = field("koala-bear.ext8-binomial3");
domain Machine = bundle(asset machine);

fn policy_of<F: Field, Table: nat, B: Bundle>() -> (index, index, index, index, index) {
  return kernel<F,Table>("relation.table_policy"; B);
}

protocol Policy roles(Evaluator)(unused: index @Evaluator)
    -> (policy: (index, index, index, index, index) @Evaluator) {
  let p @Evaluator = policy_of<FIELD,TABLE,Machine>();
  return (policy = p);
}
run Interactions = Policy;
'''


def source(table, field='Base', sub='Base', text=SOURCE):
    return text.replace('FIELD', field).replace('TABLE', str(table)).replace('SUB', sub)


def frame(values, extension=False):
    return [[str(w) for w in v] for v in values] if extension else [str(v) for v in values]


def unframe(text, extension=False):
    return [[int(w) for w in v] for v in text] if extension else [int(v) for v in text]


def points(seed, n):
    state, result = seed, []
    for _ in range(n):
        value = []
        for _ in range(8):
            state = (state * 6364136223846793005 + 1442695040888963407) % 2**64
            value.append((state >> 33) % P)
        result.append(value)
    return result


def base(n):
    return [n % P] + [0] * 7


class Client:
    def __init__(self, toolchain, journal, directory, text, bundle=None, refuses=None):
        self.tools, self.journal, self.directory = toolchain, journal, directory
        directory.mkdir(parents=True, exist_ok=True)
        module = directory / 'interaction_view.zkc'
        module.write_text(text)
        asset = journal.write('bundle.json', bundle) if bundle else MACHINE / 'bundle.json'
        self.package = directory / 'interactions.zkpkg'
        report = journal.json([toolchain.runtime, 'compile', f'--compiler={toolchain.compiler}',
                               f'--module=interaction_view={module}',
                               f'--asset=machine=relation-bundle-json={asset}',
                               'interaction_view::Interactions',
                               f'--output={self.package}'], refuses=refuses)
        self.pin = None if refuses else report['package_sha256']

    def run(self, name, inputs, refuses=None):
        path = input_files(self.journal, name, roles={'Evaluator': {'inputs': inputs}})
        output = self.directory / f'{name}.outputs.json'
        command = [self.tools.runtime, 'run', f'--package={self.package}', f'--sha256={self.pin}', *path, f'--results={output}']
        report = self.journal.json(command, cwd=ROOT, refuses=refuses)
        if refuses:
            assert report['status'] == 'refused'
            assert not output.exists(), 'a refused run published outputs'
            return report
        assert report['status'] == 'executed'
        values = json.loads(output.read_text())['roles']['Evaluator']
        for key in ('descriptor', 'counts', 'policy'):
            if key in values:
                values[key] = [int(v) for v in values[key]]
        if 'facts' in values:
            values['facts'] = int(values['facts'])
        return values

    def repackage(self, package):
        text = json.dumps(package, separators=(',', ':'))
        self.package.write_text(text)
        self.pin = sha256(text.encode()).hexdigest()


def stopped(report):
    (role,) = report['execution']['roles']
    state, detail = role['after']
    assert state == 'stopped' and detail['cause'][0] == 'backend'
    return detail['cause'][1]['text']


def inputs(height=16, interaction=0, subgroup=(), subgroup_rows=0, ood=(), ood_rows=0,
           extension=False):
    return {'height': height, 'interaction': interaction,
            'subgroup': frame(list(subgroup), extension), 'subgroup_rows': subgroup_rows,
            'ood': frame(list(ood), extension=True), 'ood_rows': ood_rows}


def carriers(run):
    return [json.loads((MACHINE / run / f'{part}.json').read_text())
            for part in ['bundle-configuration', 'bundle-instance', 'bundle-witness']]


def present_tables(bundle, configuration, instance, witness):
    """Per present table: its height and every group's integer columns, read
    from the carrier with authority over it."""
    result = {}
    for t, table in enumerate(bundle[3]):
        entry = instance[3][t]
        if entry[0] != 'present':
            continue
        authority, *policy = table[2]
        height = {'fixed': policy[0], 'config': configuration[2][t][0],
                  'instance': entry[1]}[authority]
        supplied = {'config': iter(configuration[2][t][1]), 'public': iter(entry[2]),
                    'witness': iter(witness[2][t])}
        groups = [[int(v) for v in next(supplied[g[1]])] for g in table[4]]
        result[t] = height, groups
    return result


def subgroup_assignments(bundle, t, height, groups, publics):
    """Row-major assignments of every arena input on the subgroup of order
    `height`, through the Bundle's own bindings; a read rotates modulo the
    height."""
    table, values = bundle[3][t], []
    for row in range(height):
        for binding in table[6]:
            if binding[0] == 'public':
                values.append(int(publics[binding[1]]))
            else:
                _, group, offset, column = binding
                width = table[4][group][3]
                values.append(groups[group][((row + int(offset)) % height) * width + column])
    return values


def evaluator_balances(toolchain, journal, candidate):
    """Multiset balances from the C++ and Rust Bundle evaluators, which must agree."""
    wire = json.dumps(candidate, separators=(',', ':')) + '\n'
    reports = []
    for executable in [toolchain.tool('compiler', 'test/zkc-relation_bundle_conformance-test'),
                       toolchain.driver('relation_bundle_conformance')]:
        (row,) = journal.run([executable], stdin=wire).splitlines()
        reports.append(json.loads(row))
    assert reports[0] == reports[1]
    result = reports[0]['result']
    assert result['satisfied']
    return {(b[1], tuple(int(x) for x in b[3])): [b[4], b[5]]
            for b in result['balances'] if b[0] == 'multiset' and b[2] is None}


# Hand-derived from the machine's definition. Policies: (optional, authority
# 0 fixed / 1 config / 2 instance, min, max, power of two). Counts: the
# interactions and the sum of arity + 1. Descriptors at height h: kind 1
# multiset, channel 0 program / 1 memory, side 0 push / 1 pull, global, the
# whole table, arity, bound 1, tuple degree and count degree.
POLICIES = {0: [0, 2, 4, 16, 1], 1: [0, 1, 4, 16, 1], 2: [1, 1, 8, 32, 1]}
COUNTS = {0: [2, 9], 1: [1, 4], 2: [1, 5]}


def descriptors(t, h):
    return {
        # Program pull (pc, opcode, operand) once per row; memory push of
        # (clock, operand, load*after + store*before, store), load + store times.
        0: [[1, 0, 1, 0, 0, 0, h, 3, 1, 1, 1, 0], [1, 1, 0, 0, 0, 0, h, 4, 1, 1, 2, 1]],
        # Program push of the configured instruction, `use` times.
        1: [[1, 0, 0, 0, 0, 0, h, 3, 1, 1, 1, 1]],
        # Memory pull of (clock, address, value, write), `event` times.
        2: [[1, 1, 1, 0, 0, 0, h, 4, 1, 1, 1, 1]],
    }[t]


CPU = ['pc', 'clock', 'opcode', 'operand', 'accumulator_before', 'accumulator_after',
       'select_set', 'select_add', 'select_load', 'select_store', 'select_halt']


def machine_records(t, read):
    """One row's records written from the machine's interaction expressions;
    `read(group, column)` is the value read at offset zero."""
    add, mul = octic.add, octic.mul
    if t == 0:
        def c(name):
            return read(0, CPU.index(name))
        value = add(mul(c('select_load'), c('accumulator_after')),
                    mul(c('select_store'), c('accumulator_before')))
        return [c('pc'), c('opcode'), c('operand'), ONE,
                c('clock'), c('operand'), value, c('select_store'),
                add(c('select_load'), c('select_store'))]
    if t == 1:  # instructions (pc, opcode, operand); use.
        return [read(0, 0), read(0, 1), read(0, 2), read(1, 0)]
    # schedule (clock, address); cells (before, after, event, write, value).
    return [read(0, 0), read(0, 1), read(1, 4), read(1, 3), read(1, 2)]


def ood_case(bundle, t, seed, rows):
    """Random Ext8 assignments and the hand-written records of each row."""
    bindings = bundle[3][t][6]
    values = points(seed, rows * len(bindings))
    expected = []
    for row in range(rows):
        assigned = {tuple(b): values[row * len(bindings) + i] for i, b in enumerate(bindings)}
        expected += machine_records(t, lambda g, c: assigned[('read', g, '0', c)])
    return values, expected


@pytest.mark.parametrize('run', ['store-load', 'arithmetic-only', 'store-load-initial-seven'])
def test_machine_records_match_the_evaluators_and_the_integer_model(
        toolchain, journal, directory, run):
    bundle = json.loads(MACHINE_TEXT)
    configuration, instance, witness = carriers(run)
    balances = evaluator_balances(toolchain, journal, [bundle, configuration, instance, witness])
    tables = present_tables(bundle, configuration, instance, witness)
    totals = {}
    for t in range(3):
        client = Client(toolchain, journal, directory / f'table-{t}', source(t))
        if t not in tables:
            # The arithmetic run has no memory table; its policy and
            # descriptors stay those of the declaration.
            actual = client.run(f'absent-{t}', inputs(height=8))
            journal.check(f'{run}: absent policy', actual['policy'] == POLICIES[t])
            continue
        height, groups = tables[t]
        assignments = subgroup_assignments(bundle, t, height, groups, instance[2])
        ood, expected = ood_case(bundle, t, 100 + t, 3)
        width, column = COUNTS[t][1], 0
        for i, descriptor in enumerate(descriptors(t, height)):
            actual = client.run(f'{run}-{t}-{i}', inputs(
                height, i, assignments, height, ood, 3))
            journal.check(f'{run} table {t}: policy', actual['policy'] == POLICIES[t])
            journal.check(f'{run} table {t}: counts', actual['counts'] == COUNTS[t])
            journal.check(f'{run} table {t} interaction {i}: descriptor',
                          actual['descriptor'] == descriptor)
            journal.check(f'{run}: generic facts', actual['facts'] == 322)
            # The same assignments satisfy every assertion on its scope.
            residuals = unframe(actual['subgroup_residuals'])
            journal.check(f'{run} table {t}: honest residuals',
                          len(residuals) % height == 0 and not any(
                              residuals[row * (len(residuals) // height) + a]
                              for a, (_, scope) in enumerate(bundle[3][t][7])
                              for row in scope_rows(scope, height)))
            records = unframe(actual['subgroup_records'])
            journal.check(f'{run} table {t}: subgroup width', len(records) == height * width)
            journal.check(f'{run} table {t}: Ext8 records equal the integer model',
                          unframe(actual['ood_records'], extension=True) == expected)
            # Each run reports one descriptor, so each interaction's records
            # are summed once, at its own run, through the kernel's own
            # channel, side, scope and arity.
            _, channel, side, _, _, begin, end, arity = actual['descriptor'][:8]
            for row in range(begin, end):
                at = row * width + column
                key = (channel, tuple(records[at:at + arity]))
                totals.setdefault(key, [0, 0])[side] += records[at + arity]
            column += arity + 1
    journal.check(f'{run}: subgroup records sum to the evaluators\' balances',
                  totals == balances and len(balances) >= 4)


def scope_rows(scope, h):
    kind = scope[0]
    if kind == 'all':
        return range(h)
    if kind == 'first':
        return range(1)
    if kind == 'last':
        return range(h - 1, h)
    if kind == 'interior':
        return range(scope[1], h - scope[2]) if scope[1] + scope[2] < h else range(0)
    return range(scope[1], scope[2])


def test_base_records_are_the_lifted_extension_records(toolchain, journal, directory):
    bundle = json.loads(MACHINE_TEXT)
    client = Client(toolchain, journal, directory, source(0))
    rows = 4
    row_values = [v[0] for v in points(7, rows * len(bundle[3][0][6]))]
    actual = client.run('lifted', inputs(16, 1, row_values, rows,
                                         [base(n) for n in row_values], rows))
    journal.check('base records lift to the Ext8 records',
                  [base(n) for n in unframe(actual['subgroup_records'])]
                  == unframe(actual['ood_records'], extension=True))
    journal.check('nine values per record row', len(unframe(actual['subgroup_records'])) == 36)


@pytest.mark.parametrize('name,change,cause', [
    ('height-policy', {'height': 32}, 'bundle-height'),
    ('height-power-policy', {'height': 12}, 'bundle-height'),
    ('height-one', {'height': 1}, 'bundle-height'),
    ('height-zero', {'height': 0}, 'bundle-height'),
    ('interaction-index', {'interaction': 2}, 'relation-table-interaction-index'),
    ('interaction-huge', {'interaction': 2**64 - 1}, 'relation-table-interaction-index'),
    ('short-records', {'ood': frame(points(3, 15), extension=True), 'ood_rows': 1},
     'relation-table-point-shape'),
    ('long-records', {'ood': frame(points(3, 17), extension=True), 'ood_rows': 1},
     'relation-table-point-shape'),
    ('huge-rows', {'ood': frame([], extension=True), 'ood_rows': 2**40},
     'relation-table-point-shape'),
])
def test_execution_refuses_heights_indices_and_lengths(
        toolchain, journal, directory, name, change, cause):
    client = Client(toolchain, journal, directory, source(0))
    report = client.run(name, {**inputs(), **change}, refuses='entry-run-incomplete')
    journal.check(f'{name}: {cause}', stopped(report) == f'refused:{cause}')


def test_zero_rows_and_tables_without_interactions(toolchain, journal, directory):
    client = Client(toolchain, journal, directory, source(2))
    actual = client.run('zero-rows', inputs(height=8))
    journal.check('zero rows give empty records and residuals',
                  unframe(actual['subgroup_records']) == []
                  and unframe(actual['subgroup_residuals']) == []
                  and unframe(actual['ood_records'], extension=True) == [])
    # The recurrence has no interactions: no records for any row count, but
    # every row still needs one value per arena input.
    recurrence = json.loads(RECURRENCE.read_text())
    client = Client(toolchain, journal, directory / 'recurrence', source(0), recurrence)
    actual = client.run('recurrence', inputs(8, 0, [0] * 33, 3, points(4, 22), 2),
                        refuses='entry-run-incomplete')
    journal.check('the recurrence has no interaction 0',
                  stopped(actual) == 'refused:relation-table-interaction-index')
    text = source(0).replace('interaction_of<Base,0,Machine>(height, interaction)',
                             'no_descriptor(height)')
    counts = Client(toolchain, journal, directory / 'recurrence-counts', text, recurrence)
    actual = counts.run('recurrence-counts', inputs(8, 0, [0] * 33, 3, points(4, 22), 2))
    journal.check('no interactions, no record columns', actual['counts'] == [0, 0])
    journal.check('fixed height 8 policy', actual['policy'] == [0, 0, 8, 8, 0])
    journal.check('empty records for every row count',
                  unframe(actual['subgroup_records']) == []
                  and unframe(actual['ood_records'], extension=True) == [])
    journal.check('the recurrence facts', actual['facts'] == 130)
    for name, change in [('short', {'ood': frame(points(4, 21), extension=True)}),
                         ('rows', {'ood_rows': 3})]:
        report = counts.run(name, {**inputs(8, 0, [0] * 33, 3, points(4, 22), 2), **change},
                            refuses='entry-run-incomplete')
        journal.check(f'{name}: shape', stopped(report) == 'refused:relation-table-point-shape')


def assorted(height=('instance', 2, 64, False)):
    """Every interaction form the machine does not use, as the Rust unit tests
    build it: field balances with no declared bound, a declared 0 and a
    declared 2^64-1, a local key 0 and the largest key 4096, pulls and pushes
    with bounds 3, 1 and p-1, an empty tuple, every scope kind, an Ext8 tuple
    output over KoalaBear columns, outputs shared by several records, a read
    windowed only by an interaction and a public slot only the assertion
    reads. Inputs: w1, s, w0, q, w0@1, w2, w0@-1."""
    def field_balance(locality, scope, count, declared):
        return ['field-balance', 0, locality, scope, [0, 1], count, declared]
    return ['zkc.relation-bundle/0', [['s', KB]],
            [['balance', 'field-balance', [EXT, KB], KB], ['bag', 'multiset', [KB], KB],
             ['flag', 'multiset', [], KB]],
            [['mixed', 'optional', list(height), 'finite',
              [['w', 'witness', KB, 3], ['q', 'public', KB, 1]],
              ['zkc.ring/0', [KB] * 7,
               [['input', 0], ['embed', EXT, 0], ['mul', 0, 0], ['input', 3],
                ['constant', KB, '1'], ['input', 4], ['input', 5], ['input', 6],
                ['input', 2], ['mul', 8, 0], ['input', 1], ['neg', 10], ['add', 9, 11]],
               [1, 2, 3, 4, 5, 6, 7, 12]],
              [['read', 0, '0', 1], ['public', 0], ['read', 0, '0', 0], ['read', 1, '0', 0],
               ['read', 0, '1', 0], ['read', 0, '0', 2], ['read', 0, '-1', 0]],
              [[7, ['all']]],
              [field_balance(['local', 0], ['interior', 1, 1], 2, None),
               field_balance(['global'], ['interval', 1, 4], 3, 0),
               ['multiset', 1, ['global'], ['first'], 'pull', [4], 5, 3],
               ['multiset', 1, ['local', 4096], ['interval', 0, 4], 'push', [4], 5, 1],
               ['multiset', 2, ['global'], ['all'], 'push', [], 5, P - 1],
               field_balance(['global'], ['last'], 6, 2**64 - 1)]]]]


# kind, channel, side, local, key, begin, end, arity, bounded, bound, tuple
# degree and count degree at height 8. A field balance has no side.
ASSORTED = [[0, 0, 0, 1, 0, 1, 7, 2, 0, 0, 2, 1],
            [0, 0, 0, 0, 0, 1, 4, 2, 1, 0, 2, 0],
            [1, 1, 1, 0, 0, 0, 1, 1, 1, 3, 1, 1],
            [1, 1, 0, 1, 4096, 0, 4, 1, 1, 1, 1, 1],
            [1, 2, 0, 0, 0, 0, 8, 0, 1, P - 1, 0, 1],
            [0, 0, 0, 0, 0, 7, 8, 2, 1, 2**64 - 1, 2, 1]]


def assorted_records(v):
    w1, _, _, q, following, w2, preceding = v
    square = octic.mul(w1, w1)
    return [w1, square, q, w1, square, ONE, following, w2, following, w2, w2,
            w1, square, preceding]


def test_every_interaction_form_is_described_and_substituted(toolchain, journal, directory):
    client = Client(toolchain, journal, directory, source(0, 'Extension', 'Extension'),
                    assorted())
    ood = points(60, 3 * 7)
    expected = [r for row in range(3) for r in assorted_records(ood[row * 7:row * 7 + 7])]
    for i, descriptor in enumerate(ASSORTED):
        actual = client.run(f'form-{i}', inputs(8, i, ood, 3, ood, 3, extension=True))
        journal.check(f'interaction {i}', actual['descriptor'] == descriptor)
        journal.check('six interactions, fourteen record values', actual['counts'] == [6, 14])
        journal.check('optional instance policy', actual['policy'] == [1, 2, 2, 64, 0])
        journal.check('records equal the integer model',
                      unframe(actual['ood_records'], extension=True) == expected
                      and unframe(actual['subgroup_records'], extension=True) == expected)
        journal.check('one table, one public slot, three channels', actual['facts'] == 113)
    # The public slot read only by the assertion keeps its column and is
    # ignored by the records.
    changed = [list(v) for v in ood]
    changed[7 + 1] = base(99)
    actual = client.run('unused-slot', inputs(8, 0, ood, 3, changed, 3, extension=True))
    journal.check('an assertion-only slot does not change the records',
                  unframe(actual['ood_records'], extension=True) == expected)
    # Interval(1, 4) needs height 4; Interval(0, 4) reading row + 1 needs 5.
    for height, cause in [(2, 'bundle-scope-height'), (4, 'bundle-window'),
                          (128, 'bundle-height')]:
        report = client.run(f'window-{height}', inputs(height, 0, ood, 3, ood, 3, extension=True),
                            refuses='entry-run-incomplete')
        journal.check(f'height {height}: {cause}', stopped(report) == f'refused:{cause}')


@pytest.mark.parametrize('kernels,field,height,code', [
    # The Ext8 tuple output: KoalaBear refuses the whole-table admission.
    ('policy', 'Base', None, 'source.asset-carrier'),
    ('view', 'Base', None, 'source.asset-carrier'),
    ('policy', 'Extension', None, None),
    # A fixed non-power-of-two height admits every interaction kernel.
    ('policy', 'Extension', ('fixed', 12), None),
    ('view', 'Extension', ('fixed', 12), None),
])
def test_source_closure_checks_carriers_without_polynomial_premises(
        toolchain, journal, directory, kernels, field, height, code):
    bundle = assorted(height) if height else assorted()
    text = POLICY_SOURCE if kernels == 'policy' else SOURCE.replace(
        'points_of<SUB,TABLE,Machine>(subgroup, subgroup_rows)', 's')
    client = Client(toolchain, journal, directory, source(0, field, 'Extension', text),
                    bundle, refuses=code)
    if code is None:
        values = {'unused': 0} if kernels == 'policy' else inputs(12, 0, extension=True)
        actual = client.run('policy', values)
        expected = [1, 0, 12, 12, 0] if height else [1, 2, 2, 64, 0]
        journal.check('the declared policy', actual['policy'] == expected)


def test_source_closure_checks_the_table_index(toolchain, journal, directory):
    Client(toolchain, journal, directory, source(3), refuses='source.asset-table')
    Client(toolchain, journal, directory / 'policy', source(3, text=POLICY_SOURCE),
           refuses='source.asset-table')


@pytest.mark.parametrize('mutation,code', [
    ('missing', 'entry-asset-missing'),
    ('tampered', 'relation-asset-identity'),
    ('records-table', 'relation-table-index'),
    ('policy-table', 'relation-table-index'),
    ('carrier', 'entry-asset-carrier'),
])
def test_host_preflight_checks_every_interaction_reference(
        toolchain, journal, directory, mutation, code):
    client = Client(toolchain, journal, directory, source(0))
    package = json.loads(client.package.read_text())
    identity = sha256(MACHINE_TEXT.encode()).hexdigest()
    artifact = json.loads(package['artifact'])
    candidate = artifact['candidate']

    def replace_asset(body):
        nonlocal candidate
        text = json.dumps(body, separators=(',', ':'))
        replacement = sha256(text.encode()).hexdigest()
        candidate = candidate.replace(identity, replacement)
        package['assets'] = [[replacement, text]]

    if mutation == 'missing':
        package['assets'] = []
    elif mutation == 'tampered':
        body = json.loads(MACHINE_TEXT)
        body[3][0][0] = 'changed-table-name'
        package['assets'] = [[identity, json.dumps(body, separators=(',', ':'))]]
    elif mutation.endswith('-table'):
        contract = {'records': 'relation.table_record_points',
                    'policy': 'relation.table_policy'}[mutation.split('-')[0]]
        program = json.loads(candidate)
        changed = 0
        for binding in program[1]:
            if binding[1] == contract:
                binding[2][1] = '3'
                changed += 1
        assert changed
        candidate = json.dumps(program, separators=(',', ':'))
    elif mutation == 'carrier':
        # A first table whose assertion is KoalaBear but whose tuple output is
        # Ext8: the polynomial references stay admitted, the interaction
        # references do not.
        replace_asset(assorted())
    artifact['candidate'] = candidate
    package['artifact'] = json.dumps(artifact, separators=(',', ':'))
    client.repackage(package)
    result = client.run(mutation, inputs(), refuses=code)
    assert result['phase'] == 'admission'


def test_host_admits_a_policy_reference_without_a_two_adic_height(
        toolchain, journal, directory):
    client = Client(toolchain, journal, directory, source(0, text=POLICY_SOURCE))
    package = json.loads(client.package.read_text())
    identity = sha256(MACHINE_TEXT.encode()).hexdigest()
    body = json.loads(MACHINE_TEXT)
    body[3][0][2] = ['fixed', 12]
    text = json.dumps(body, separators=(',', ':'))
    replacement = sha256(text.encode()).hexdigest()
    artifact = json.loads(package['artifact'])
    artifact['candidate'] = artifact['candidate'].replace(identity, replacement)
    package['artifact'] = json.dumps(artifact, separators=(',', ':'))
    package['assets'] = [[replacement, text]]
    client.repackage(package)
    actual = client.run('fixed-twelve', {'unused': 0})
    journal.check('the declared fixed height', actual['policy'] == [0, 0, 12, 12, 0])
