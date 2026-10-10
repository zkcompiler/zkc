"""External AIR artifacts cross both independent bundle consumers unchanged."""
from copy import deepcopy
from hashlib import sha256
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
FIXTURES = ROOT / 'compiler/adapters/plonky3/fixtures'


def identity(bundle):
    return sha256(json.dumps(bundle, separators=(',', ':')).encode()).hexdigest()


def rebind(candidate):
    for carrier in candidate[1:]:
        carrier[1] = identity(candidate[0])
    return candidate


def test_exported_bundles_and_mutations_agree(toolchain, journal):
    cases = []
    for directory in sorted(FIXTURES.iterdir()):
        original = [json.loads((directory / f'{name}.json').read_text()) for name in [
            'bundle', 'bundle-configuration', 'bundle-instance', 'bundle-witness']]
        failures = json.loads((directory / 'expected.json').read_text())['upstream_failures']
        cases.append((directory.name, original, not failures, failures))
        changed = deepcopy(original)
        changed[3][2][0][0][1] = str(int(changed[3][2][0][0][1]) + 1)
        cases.append((f'{directory.name}: witness', changed, False, None))
        changed = deepcopy(original)
        changed[2][1] = '0' * 64
        cases.append((f'{directory.name}: identity', changed, 'bundle-relation', None))
        changed = deepcopy(original)
        changed[3][2][0].append([])
        cases.append((f'{directory.name}: witness authority', changed, 'bundle-group-count', None))
        changed = deepcopy(original)
        changed[0][3][0][6][0] = ['challenge', 0]
        cases.append((f'{directory.name}: challenge in deterministic relation', rebind(changed), 'bundle-input-kind', None))
        changed = deepcopy(original)
        changed[3][2][0][0][0] = '00'
        cases.append((f'{directory.name}: noncanonical value', changed, 'bundle-value', None))
        changed = deepcopy(original)
        changed[0][3][0][3] = 'finite'
        if directory.name != 'counter-guarded':
            cases.append((f'{directory.name}: finite wrap', rebind(changed), 'bundle-window', None))
        if directory.name == 'recurrence':
            changed = deepcopy(original)
            changed[2][2][-1] = str(int(changed[2][2][-1]) + 1)
            cases.append(('changed public', changed, False, None))
            changed = deepcopy(original)
            changed[1][2][0][1][0][1] = str(int(changed[1][2][0][1][0][1]) + 1)
            cases.append(('changed configuration', changed, False, None))
            changed = deepcopy(original)
            changed[2][3][0][1] = 8
            cases.append(('override fixed height', changed, 'bundle-height-authority', None))

    # Exact mixed-field presentation: X^8 = 3, with the base constant supplied
    # by configuration and embedded explicitly into the extension expression.
    base, ext = 'koala-bear', 'koala-bear.ext8-binomial3'
    arena = ['zkc.ring/0', [ext, base], [
        ['input', 0], ['mul', 0, 0], ['mul', 1, 1], ['mul', 2, 2],
        ['input', 1], ['embed', ext, 4], ['neg', 5], ['add', 3, 6]], [7]]
    bundle = ['zkc.relation-bundle/0', [], [], [[
        'extension', 'required', ['fixed', 1], 'finite',
        [['x', 'witness', ext, 1], ['constant', 'config', base, 1]],
        arena, [['read', 0, '0', 0], ['read', 1, '0', 0]], [[0, ['all']]], []]]]
    mixed = rebind([bundle, ['zkc.relation-configuration/0', '', [[None, [['3']]]]],
        ['zkc.relation-instance/0', '', [], [['present', None, []]]],
        ['zkc.relation-witness/0', '', [[[[str(x) for x in [0, 1, 0, 0, 0, 0, 0, 0]]]]]]])
    cases.append(('extension relation', mixed, True, []))
    changed = deepcopy(mixed)
    changed[3][2][0][0][0][0] = '1'
    cases.append(('extension mutation', changed, False, None))

    # Tiny, constant-only carriers must not expand into millions of records or
    # wide tuple coordinates. No large witness or result is allocated here.
    for field, count in [(base, 17), (ext, 9)]:
        bundle = ['zkc.relation-bundle/0', [], [], [[
            'constant', 'required', ['fixed', 65536], 'finite', [],
            ['zkc.ring/0', [], [['constant', field, '0']], [0]], [],
            [[0, ['all']]] * count, []]]]
        candidate = rebind([bundle, ['zkc.relation-configuration/0', '', [[None, []]]],
            ['zkc.relation-instance/0', '', [], [['present', None, []]]],
            ['zkc.relation-witness/0', '', [[]]]])
        cases.append((f'{field}: result expansion', candidate, 'bundle-result-limit', None))
        scoped = deepcopy(candidate)
        scoped[0][3][0][7] = [[0, ['first']]] * count
        cases.append((f'{field}: scoped small result', rebind(scoped), True, []))
    wide = deepcopy(candidate)
    wide[0][2] = [['wide', 'field-balance', [ext] * 64, ext]]
    wide[0][3][0][7] = []
    wide[0][3][0][8] = [['field-balance', 0, ['global'], ['all'], [0] * 64, 0, None]]
    cases.append(('wide extension tuple expansion', rebind(wide), 'bundle-result-limit', None))

    wire = ''.join(json.dumps(c, separators=(',', ':')) + '\n' for _, c, _, _ in cases)
    replies = []
    for executable in [toolchain.tool('compiler', 'test/zkc-relation_bundle_conformance-test'),
                       toolchain.driver('relation_bundle_conformance')]:
        replies.append([json.loads(row) for row in journal.run([executable], stdin=wire).splitlines()])
    assert len(replies[0]) == len(replies[1]) == len(cases)
    for (name, candidate, expected, failures), cpp, rust in zip(cases, *replies):
        assert cpp == rust, (name, cpp, rust)
        if isinstance(expected, str):
            assert not cpp['accepted'], (name, cpp)
            assert cpp['error'] == expected, (name, cpp)
        else:
            assert cpp['accepted'], (name, cpp)
            assert cpp['identity'] == identity(candidate[0])
            assert cpp['result']['satisfied'] == expected, (name, cpp)
            if failures is not None:
                found = sorted([row, assertion] for _, assertion, row, value in cpp['result']['residuals']
                               if value != '0' and value != ['0'] * 8)
                assert found == sorted(failures), (name, found, failures)


def staged_case(extension=False):
    """Two actual phases: y = alpha*x, then z = y+beta, with final claims."""
    field = 'koala-bear.ext8-binomial3' if extension else 'koala-bear'
    def scalar(n):
        return [str(n), *(['0'] * 7)] if extension else str(n)
    xs = [[str(n), '1', *(['0'] * 6)] for n in [1, 2, 3]] if extension else ['1', '2', '3']
    alpha = ['2', *(['0'] * 6), '1'] if extension else '2'
    # (n+X)(2+X^7) = (2n+3)+2X+nX^7, since X^8 = 3.
    ys = [[str(2*n+3), '2', *(['0'] * 5), str(n)] for n in [1, 2, 3]] if extension else ['2', '4', '6']
    zs = deepcopy(ys)
    for i, y in enumerate(ys):
        if extension:
            zs[i][0] = str(int(y[0]) + 4)
        else:
            zs[i] = str(int(y) + 4)
    minus = ['zkc.ring/0', [field, field],
             [['input', 0], ['input', 1], ['neg', 1], ['add', 0, 2]], [3]]
    bundle = ['zkc.relation-bundle/0', [['final', field]], [], [[
        'trace', 'optional', ['fixed', 3], 'finite', [['x', 'witness', field, 1]],
        minus, [['read', 0, '0', 0], ['public', 0]], [[0, ['last']]], []]]]
    base = rebind([bundle, ['zkc.relation-configuration/0', '', [[None, []]]],
                   ['zkc.relation-instance/0', '', [xs[-1]], [['present', None, []]]],
                   ['zkc.relation-witness/0', '', [[xs]]]])
    phases = []
    for phase, op in [(1, 'mul'), (2, 'add')]:
        arena = ['zkc.ring/0', [field] * 4, [
            ['input', 0], ['input', 1], [op, 0, 1], ['neg', 2],
            ['input', 2], ['add', 4, 3], ['input', 3], ['neg', 6], ['add', 4, 7]], [5, 8]]
        phases.append([[[f'coin{phase}', field]], [[f'claim{phase}', field]], [[
            [[f'aux{phase}', field, 1]], arena,
            [['read', phase-1, 0, '0', 0], ['challenge', phase, 0],
             ['read', phase, 0, '0', 0], ['claim', phase, 0]],
            [[0, ['all']], [1, ['last']]]]]])
    # Check the claims independently of rows: c1 = alpha*public, c2 = c1+beta.
    global_arena = ['zkc.ring/0', [field] * 5, [
        ['input', 0], ['input', 1], ['mul', 0, 1], ['neg', 2], ['input', 2],
        ['add', 4, 3], ['input', 3], ['add', 4, 6], ['neg', 7],
        ['input', 4], ['add', 9, 8]], [5, 10]]
    staged = ['zkc.relation-staged/0', identity(bundle), phases,
              [global_arena, [['public', 0], ['challenge', 1, 0], ['claim', 1, 0],
                              ['challenge', 2, 0], ['claim', 2, 0]], [0, 1]], []]
    assignment = ['zkc.relation-staged-assignment/0', identity(staged), [
        [[alpha], [ys[-1]], [[ys]]], [[scalar(4)], [zs[-1]], [[zs]]]]]
    return [*base, staged, assignment]


def bind_staged(candidate):
    for carrier in candidate[1:4]:
        carrier[1] = identity(candidate[0])
    candidate[4][1] = identity(candidate[0])
    candidate[5][1] = identity(candidate[4])
    return candidate


def test_staged_assignments_agree(toolchain, journal):
    cases = []
    for extension in [False, True]:
        original = staged_case(extension)
        label = 'extension' if extension else 'base'
        cases.append((f'{label}: two actual phases', original, True))
        changed = deepcopy(original)
        changed[4][2][0][2][0][3] = [
            [0, ['first']], [1, ['last']], [0, ['interior', 1, 1]],
            [0, ['interval', 0, 0]], [0, ['all']], [0, ['interior', 3, 3]]]
        cases.append((f'{label}: overlapping and empty scopes', bind_staged(changed), True))
        for name, part in [('challenge', 0), ('claim', 1), ('auxiliary row', 2)]:
            changed = deepcopy(original)
            values = changed[5][2][0][part]
            if part == 2:
                values = values[0][0]
            if extension:
                values[0][0] = str(int(values[0][0]) + 1)
            else:
                values[0] = str(int(values[0]) + 1)
            cases.append((f'{label}: changed {name}', changed, False))
        changed = deepcopy(original)
        changed[5][2][0][0] = []
        cases.append((f'{label}: missing challenge', changed, 'staged-slot-shape'))
        changed = deepcopy(original)
        changed[5][2][1][1].append(deepcopy(changed[5][2][1][1][0]))
        cases.append((f'{label}: extra claim', changed, 'staged-slot-shape'))
        changed = deepcopy(original)
        changed[5][2][1][2][0][0].pop()
        cases.append((f'{label}: auxiliary group shape', changed, 'bundle-group-shape'))
        changed = deepcopy(original)
        changed[4][2][0][2][0][2][1] = ['challenge', 2, 0]
        cases.append((f'{label}: future challenge', bind_staged(changed), 'staged-phase-order'))
        changed = deepcopy(original)
        changed[4][2][0][2][0][2][2] = ['read', 2, 0, '0', 0]
        cases.append((f'{label}: future auxiliary read', bind_staged(changed), 'staged-phase-order'))
        changed = deepcopy(original)
        changed[4][2][0][2][0][2][0] = ['read', 0, 0, '1', 0]
        cases.append((f'{label}: undefined finite window', bind_staged(changed), 'bundle-window'))
        changed = deepcopy(original)
        changed[4][2][0][2][0][3][0][1] = ['interval', 0, 4]
        cases.append((f'{label}: scope beyond actual height', bind_staged(changed), 'bundle-scope-height'))
        changed = deepcopy(original)
        changed[4][3][1][0] = ['read', 0, 0, '0', 0]
        cases.append((f'{label}: global read', bind_staged(changed), 'staged-global-read'))
        changed = deepcopy(original)
        changed[5][1] = '0' * 64
        cases.append((f'{label}: assignment identity', changed, 'staged-program'))
        changed = deepcopy(original)
        changed[4][1] = None
        changed[5][1] = identity(changed[4])
        cases.append((f'{label}: relation identity shape', changed, 'staged-schema'))
        changed = deepcopy(original)
        changed[4][2][0][0][0][1] = 0
        cases.append((f'{label}: challenge field shape', bind_staged(changed), 'staged-schema'))
        changed = deepcopy(original)
        changed[4][2][0][2][0][0][0][1] = 0
        cases.append((f'{label}: group field shape', bind_staged(changed), 'staged-schema'))
        changed = deepcopy(original)
        changed[4][4] = [['characteristic-exceeds', 'unknown-field', 1]]
        cases.append((f'{label}: premise field refusal', bind_staged(changed), 'staged-premise'))
        changed = deepcopy(original)
        changed[4][2][0][2][0][0] *= 257
        cases.append((f'{label}: group schema bound', bind_staged(changed), 'staged-schema'))
        changed = deepcopy(original)
        changed[4][2][0][2][0][3] *= 2049
        cases.append((f'{label}: assertion schema bound', bind_staged(changed), 'staged-schema'))
        changed = deepcopy(original)
        changed[4][2][0][2] *= 257
        cases.append((f'{label}: table schema bound', bind_staged(changed), 'staged-schema'))
        changed = deepcopy(original)
        changed[2][3][0] = ['absent']
        changed[3][2][0] = None
        cases.append((f'{label}: unexpected absent-table data', changed, 'staged-presence'))
        changed = deepcopy(changed)
        for data in changed[5][2]:
            data[2][0] = None
        cases.append((f'{label}: absent table with global checks', changed, True))
        # Premises are recorded obligations, not hidden assertions. The row
        # residual is zero, so this nonzero premise is deliberately false.
        changed = deepcopy(original)
        changed[4][4] = [['nonzero', 1, 0, 0, ['all']],
                         ['characteristic-exceeds', 'koala-bear', 2130706433]]
        cases.append((f'{label}: premises remain assumptions', bind_staged(changed), True))

    # A compact program may expand its output without any auxiliary data.
    empty = ['zkc.ring/0', [], [], []]
    for extension, count in [(False, 17), (True, 9)]:
        field = 'koala-bear.ext8-binomial3' if extension else 'koala-bear'
        constant = ['zkc.ring/0', [], [['constant', field, '0']], [0]]
        bundle = ['zkc.relation-bundle/0', [], [], [[
            'large', 'required', ['fixed', 65536], 'finite', [], empty, [], [], []]]]
        original = rebind([bundle, ['zkc.relation-configuration/0', '', [[None, []]]],
                           ['zkc.relation-instance/0', '', [], [['present', None, []]]],
                           ['zkc.relation-witness/0', '', [[]]]])
        staged = ['zkc.relation-staged/0', identity(bundle), [[[], [], [[
            [], constant, [], [[0, ['all']]] * count]]]], [empty, [], []], []]
        assignment = ['zkc.relation-staged-assignment/0', identity(staged), [[[], [], [[]]]]]
        candidate = [*original, staged, assignment]
        cases.append((f'{field}: staged result expansion', candidate, 'bundle-result-limit'))
        changed = deepcopy(candidate)
        changed[4][2][0][2][0][3] = [[0, ['first']]] * count
        cases.append((f'{field}: scoped staged result', bind_staged(changed), True))
        changed = deepcopy(candidate)
        changed[4][2][0][2][0][3].pop()
        changed[4][3] = [constant, [], [0]]
        cases.append((f'{field}: global shares output budget', bind_staged(changed), 'bundle-result-limit'))
        changed = deepcopy(candidate)
        split = count // 2
        changed[4][2][0][2][0][3] = [[0, ['all']]] * split
        phase = deepcopy(changed[4][2][0])
        phase[2][0][3] = [[0, ['all']]] * (count - split)
        changed[4][2].append(phase)
        changed[5][2].append([[], [], [[]]])
        cases.append((f'{field}: phases share output budget', bind_staged(changed), 'bundle-result-limit'))

    # Declared challenge slots count with auxiliary coordinates before group
    # lengths or supplied values are traversed. This carrier stays tiny.
    changed = deepcopy(candidate)
    changed[0][3][0][2] = ['fixed', 1 << 20]
    changed[4][2] = [[[['coin', 'koala-bear']], [], [[
        [['aux', 'koala-bear', 4]], empty, [], []]]]]
    changed[5][2] = [[['0'], [], [[[]]]]]
    cases.append(('slots share staged coordinate budget', bind_staged(changed), 'bundle-data-limit'))

    wire = ''.join(json.dumps(c, separators=(',', ':')) + '\n' for _, c, _ in cases)
    replies = []
    for executable in [toolchain.tool('compiler', 'test/zkc-relation_bundle_conformance-test'),
                       toolchain.driver('relation_bundle_conformance')]:
        replies.append([json.loads(row) for row in journal.run([executable], stdin=wire).splitlines()])
    assert len(replies[0]) == len(replies[1]) == len(cases)
    for (name, candidate, expected), cpp, rust in zip(cases, *replies):
        assert cpp == rust, (name, cpp, rust)
        if isinstance(expected, str):
            assert cpp == {'accepted': False, 'error': expected}, (name, cpp)
        else:
            assert cpp['accepted'], (name, cpp)
            assert cpp['result']['satisfied'], (name, cpp)
            assert cpp['staged_result']['satisfied'] == expected, (name, cpp)
            assert cpp['staged_identity'] == identity(candidate[4])
            assert cpp['staged'] == candidate[4]
            assert cpp['assignment'] == candidate[5]



def test_formation_analysis_is_bounded(toolchain, journal):
    """Small DAGs with shared roots must not expand into huge read-set facts."""
    field = 'koala-bear'
    empty = ['zkc.ring/0', [], [], []]

    def arena(width, outputs=1):
        nodes = [['input', i] for i in range(width)]
        level = list(range(width))
        while len(level) > 1:
            parents = []
            for left, right in zip(level[::2], level[1::2]):
                parents.append(len(nodes))
                nodes.append(['add', left, right])
            level = parents
        return ['zkc.ring/0', [field] * width, nodes, level * outputs]

    def base_case(width, outputs=1, references=None, tables=1, blank=False):
        tables_data = [[
            f'trace{t}', 'required', ['fixed', 1], 'cyclic',
            [['x', 'witness', field, width]],
            empty if blank else arena(width, outputs),
            [] if blank else [['read', 0, '0', i] for i in range(width)],
            [] if blank else [[i % outputs, ['all']]
                              for i in range(outputs if references is None else references)],
            []] for t in range(tables)]
        return rebind([
            ['zkc.relation-bundle/0', [], [], tables_data],
            ['zkc.relation-configuration/0', '', [[None, []]] * tables],
            ['zkc.relation-instance/0', '', [], [['present', None, []]] * tables],
            ['zkc.relation-witness/0', '', [[['0'] * width]] * tables]])

    def staged_case_for_analysis(width, references, phases):
        candidate = base_case(width, blank=True)
        table = [[], arena(width), [['read', 0, 0, '0', i] for i in range(width)],
                 [[0, ['all']]] * references]
        candidate.extend([
            ['zkc.relation-staged/0', '', [[[], [], [table]]] * phases,
             [empty, [], []], []],
            ['zkc.relation-staged-assignment/0', '', [[[], [], [[]]]] * phases]])
        return bind_staged(candidate)

    cases = [
        ('shared roots within budget', base_case(4, 4), True),
        ('retained inputs', base_case(2048, 2049), False),
        ('retained inputs across tables', base_case(1024, 2049, tables=2), False),
        ('repeated static checks', base_case(8192, references=2730), False),
        ('small staged program', staged_case_for_analysis(4, 3, 2), True),
        ('staged repeated checks', staged_case_for_analysis(8192, 2730, 1), False),
        ('staged cumulative checks', staged_case_for_analysis(4096, 2730, 2), False),
    ]
    global_case = staged_case_for_analysis(1, 0, 1)
    global_case[4][2][0][2][0] = [[], empty, [], []]
    global_case[0][1] = [[f'p{i}', field] for i in range(8192)]
    global_case[2][2] = ['0'] * 8192
    global_case[4][3] = [arena(8192), [['public', i] for i in range(8192)], [0] * 2730]
    cases.append(('global analysis', bind_staged(global_case), False))

    rows = [json.dumps(c, separators=(',', ':')) for _, c, _ in cases]
    assert all(len(row) < 1024 * 1024 for row in rows)
    wire = ''.join(row + '\n' for row in rows)
    replies = []
    for executable in [toolchain.tool('compiler', 'test/zkc-relation_bundle_conformance-test'),
                       toolchain.driver('relation_bundle_conformance')]:
        replies.append([json.loads(row) for row in journal.run([executable], stdin=wire).splitlines()])
    assert len(replies[0]) == len(replies[1]) == len(cases)
    for (name, _, accepted), cpp, rust in zip(cases, *replies):
        assert cpp == rust, (name, cpp, rust)
        if accepted:
            assert cpp['accepted'] and cpp['result']['satisfied'], (name, cpp)
            if 'staged_result' in cpp:
                assert cpp['staged_result']['satisfied'], (name, cpp)
        else:
            assert cpp == {'accepted': False, 'error': 'bundle-analysis-limit'}, (name, cpp)



def test_interaction_balances_and_refusals_agree(toolchain, journal):
    field, modulus = 'koala-bear', 2130706433
    bundle = ['zkc.relation-bundle/0', [], [
        ['field', 'field-balance', [field], field],
        ['natural', 'multiset', [field], field]], [[
            'counts', 'required', ['fixed', 2], 'cyclic',
            [['values', 'witness', field, 3]],
            ['zkc.ring/0', [field] * 3,
             [['input', 0], ['input', 1], ['input', 2], ['neg', 2]], [0, 1, 2, 3]],
            [['read', 0, '0', i] for i in range(3)], [], [
                ['field-balance', 0, ['global'], ['all'], [0], 1, None],
                ['field-balance', 0, ['global'], ['all'], [0], 3, None],
                ['multiset', 1, ['global'], ['all'], 'push', [0], 1, 3],
                ['multiset', 1, ['global'], ['all'], 'pull', [0], 2, 3]]]]]
    original = rebind([bundle,
        ['zkc.relation-configuration/0', '', [[None, []]]],
        ['zkc.relation-instance/0', '', [], [['present', None, []]]],
        ['zkc.relation-witness/0', '', [[['5', '1', '1', '5', '2', '2']]]]])
    cases = [('balanced field and natural counts', original, True)]
    changed = deepcopy(original)
    changed[3][2][0][0][-1] = '1'
    cases.append(('unequal counts', changed, False))
    changed = deepcopy(original)
    changed[3][2][0][0][1:3] = ['4', '4']
    cases.append(('multiplicity range', changed, False))
    changed = deepcopy(original)
    changed[0][3][0][8][0][2] = ['local', 0]
    cases.append(('local partition differs from global', rebind(changed), False))
    changed = deepcopy(original)
    for interaction in changed[0][3][0][8][2:]:
        interaction[-1] = modulus - 1
    changed[3][2][0][0] = ['5', str(modulus - 1), '0', '5', '1', '0']
    cases.append(('field cancellation is not natural equality', rebind(changed), False))
    changed = deepcopy(original)
    changed[0][3][0][8][2][-1] = 0
    cases.append(('invalid multiplicity bound', rebind(changed), 'bundle-multiset-bound'))
    changed = deepcopy(original)
    changed[0][3][0][2] = ['instance', 1, 4, False]
    changed[0][3][0][4][0][1] = 'config'
    cases.append(('configuration height authority', rebind(changed), 'bundle-config-height'))
    changed = deepcopy(original)
    table = changed[0][3][0]
    table[4][0][3] = 4
    table[5][1].append(field)
    table[6].append(['read', 0, '0', 3])
    cases.append(('unused declared input', rebind(changed), 'bundle-unused-input'))
    changed = deepcopy(original)
    changed[0][3][0][2] = ['fixed', 32768]
    changed[0][3][0][7] = [[0, ['all']]] * 4092
    changed[3][2][0][0] = ['0'] * (32768 * 3)
    cases.append(('work limit', rebind(changed), 'bundle-work-limit'))
    changed = deepcopy(original)
    changed[0][3][0][2] = ['fixed', 1 << 20]
    table = changed[0][3][0]
    table[4:9] = [[], ['zkc.ring/0', [], [['constant', field, '1']], [0]], [], [],
                  [['field-balance', 0, ['global'], ['all'], [0], 0, None]] * 5]
    changed[3][2][0] = []
    cases.append(('contribution limit on compact input', rebind(changed), 'bundle-contribution-limit'))

    wire = ''.join(json.dumps(c, separators=(',', ':')) + '\n' for _, c, _ in cases)
    replies = []
    for executable in [toolchain.tool('compiler', 'test/zkc-relation_bundle_conformance-test'),
                       toolchain.driver('relation_bundle_conformance')]:
        replies.append([json.loads(row) for row in journal.run([executable], stdin=wire).splitlines()])
    assert len(replies[0]) == len(replies[1]) == len(cases)
    for (name, _, expected), cpp, rust in zip(cases, *replies):
        assert cpp == rust, (name, cpp, rust)
        if isinstance(expected, str):
            assert cpp == {'accepted': False, 'error': expected}, (name, cpp)
        else:
            assert cpp['accepted'] and cpp['result']['satisfied'] == expected, (name, cpp)
