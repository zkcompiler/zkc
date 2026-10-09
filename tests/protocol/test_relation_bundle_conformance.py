"""External AIR artifacts cross both independent bundle consumers unchanged."""
from copy import deepcopy
from hashlib import sha256
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
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
