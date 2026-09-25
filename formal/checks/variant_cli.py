#!/usr/bin/env python3
"""Independent active-sum source/candidate and execution fixtures.

Run after `lake build interactive-protocol`. Imported fixture constructors also
serve the cross-tool differential corpus; expected outcomes are handwritten.
"""
import copy
import json
from pathlib import Path
import subprocess
import sys
import tempfile

FORMAL = Path(__file__).resolve().parents[1]
TOOL = FORMAL / '.lake/build/bin/interactive-protocol'


sys.path.insert(0, str(FORMAL.parent / 'compiler/test/support'))
from variant_codec import descriptor  # noqa: E402 - standalone fixture import


CHOICE = descriptor('pkg/result{T=index}', [['Some', ['index']], ['None', []]])


def source(alternative='Some'):
    payload = ['x'] if alternative == 'Some' else []
    body = [['variant', 'pack', CHOICE, alternative, payload, 'value'],
            ['match', 'select', 'value', ['fallback'], [
                ['Some', ['active'], [['op', 'sum', 'add', [], ['active', 'fallback'], ['sum']],
                                      ['yield', ['sum']]]],
                ['None', [], [['yield', ['fallback']]]]], ['out']],
            ['return', ['out']]]
    args = [['x', 'index'], ['fallback', 'index']]
    return ['zkc.protocol/1', [['add', 'index.add', [], '']],
            [['function', 'Select', args, ['index'], body, ['Select', []]]],
            [['protocol', 'Main', ['P'], [], [[n, 'P', t] for n, t in args], [['P', 'index']], [],
              [['local', 'invoke', 'P', 'Select', ['x', 'fallback'], ['out']], ['return', ['out']]]]],
            [['instance', 'root', 'Main', [], [], [['P', 'P']]]], [['entry', 'main', 'root']]]


TAG = descriptor('pkg/tag', [['yes', []], ['no', []]])

# Every external contract that carries transcript history, and the three that
# touch none: docs/spec/realization/external-constructions.md.
HISTORY = [('external.openvm.observe', ['s', 'w'], ['s2']),
           ('external.openvm.sample', ['s'], ['s2', 'i']),
           ('external.openvm.sample_ext', ['s'], ['s2', 'c']),
           ('external.openvm.sample_bits', ['s', 'n'], ['s2', 'i']),
           ('external.openvm.check_witness', ['s', 'n', 'm'], ['s2', 'ok']),
           ('external.monero.update', ['s', 'w'], ['s2', 'h'])]
PURE = [('external.monero.init', ['s'], ['s2']),
        ('external.monero.hash', ['s'], ['s2']),
        ('external.openvm.init', [], ['s2'])]


def effect_source(contract, arm, functions=()):
    """A local match whose selected arm holds the body under test."""
    args = [['s', 'indices'], ['w', 'indices'], ['n', 'index'], ['m', 'index']]
    body = [['variant', 'pack', TAG, 'yes', [], 'v'],
            ['match', 'select', 'v', ['s', 'w', 'n', 'm'],
             [['yes', [], arm], ['no', [], [['yield', ['s']]]]], ['out']],
            ['return', ['out']]]
    fns = [['function', 'Work', args, ['indices'], body, ['Work', []]]] + list(functions)
    return ['zkc.protocol/1', [['kernel', contract, [], '']], fns,
            [['protocol', 'Main', ['P'], [], [[n, 'P', t] for n, t in args], [['P', 'indices']], [],
              [['local', 'invoke', 'P', 'Work', ['s', 'w', 'n', 'm'], ['out']], ['return', ['out']]]]],
            [['instance', 'root', 'Main', [], [], [['P', 'P']]]], [['entry', 'main', 'root']]]


def external_arm(contract, inputs, outputs):
    return effect_source(contract, [['op', 'effect', 'kernel', [], inputs, outputs],
                                    ['yield', ['s2']]])


def tagged_witness(leaf):
    """Two candidates differing only in the payload leaf spelling. The witness
    check runs outside the arm, where it is allowed, and supplies the bool."""
    args = [['s', 'indices'], ['n', 'index'], ['m', 'index']]
    ty = descriptor('pkg/tag', [['yes', [leaf]], ['no', []]])
    body = [['op', 'witness', 'kernel', [], ['s', 'n', 'm'], ['s2', 'ok']],
            ['variant', 'pack', ty, 'yes', ['ok'], 'v'],
            ['match', 'select', 'v', ['s2'],
             [['yes', ['b'], [['yield', ['s2']]]], ['no', [], [['yield', ['s2']]]]], ['out']],
            ['return', ['out']]]
    return ['zkc.protocol/1', [['kernel', 'external.openvm.check_witness', [], '']],
            [['function', 'Work', args, ['indices'], body, ['Work', []]]],
            [['protocol', 'Main', ['P'], [], [[n, 'P', t] for n, t in args], [['P', 'indices']], [],
              [['local', 'invoke', 'P', 'Work', ['s', 'n', 'm'], ['out']], ['return', ['out']]]]],
            [['instance', 'root', 'Main', [], [], [['P', 'P']]]], [['entry', 'main', 'root']]]


def physical_type(ty):
    if ty.startswith('variant:'):
        return ty + '@logical.variant/1'
    return ty + '@native.' + ty + '/1'


def physical_body(body):
    result = copy.deepcopy(body)
    for op in result:
        if op[0] == 'variant':
            op[2] = physical_type(op[2])
        elif op[0] == 'match':
            for arm in op[4]:
                arm[2] = physical_body(arm[2])
    return result


def candidate(s, physical=False):
    args = copy.deepcopy(s[2][0][2])
    results = copy.deepcopy(s[2][0][3])
    body = copy.deepcopy(s[2][0][4])
    if physical:
        args = [[n, physical_type(t)] for n, t in args]
        results = [physical_type(t) for t in results]
    # Role-free local stops lose the common source's empty owner slot at projection.
    def projected(stmts):
        for op in stmts:
            if op[0] == 'stop' and len(op) == 4:
                op.pop(2)
            elif op[0] == 'match':
                for arm in op[4]:
                    projected(arm[2])
    projected(body)
    if physical:
        body = physical_body(body)
    return ['zkc.participants/1', [['add', 'index.add', [], 'native/index.add' if physical else '']],
            'physical' if physical else 'logical',
            [['function', 'Select', args, results, body, ['Select', []]]],
            [['participant', 'p', 'root', 'P', [], args, results,
              [['local', 'invoke', 'Select', ['x', 'fallback'], ['out']], ['return', ['out']]]]],
            [['entry', 'main', [['P', 'p']]]]]


def inputs():
    return ['zkc.reference-inputs/1', 'main', 'test',
            [['P', [['x', ['index', '5']], ['fallback', ['index', '7']]]]], [], [], []]


def invoke(root, command, *trees):
    paths = []
    for i, tree in enumerate(trees):
        path = root / f'input-{i}.json'
        path.write_text(json.dumps(tree))
        paths.append(str(path))
    p = subprocess.run([str(TOOL), command, *paths], capture_output=True, text=True, timeout=30)
    try:
        return json.loads(p.stdout)
    except ValueError as error:
        raise AssertionError((p.returncode, p.stdout, p.stderr)) from error


def main():
    passed = 0
    failures = []

    def check(condition, name, result):
        nonlocal passed
        if condition:
            passed += 1
        else:
            failures.append((name, result))

    with tempfile.TemporaryDirectory(prefix='zkc-variant-') as temp:
        root = Path(temp)
        for alternative, value, count in [('Some', '12', 2), ('None', '7', 0)]:
            s = source(alternative)
            r = invoke(root, '--admit', s)
            check(r[0] == 'checked', f'{alternative} admission', r)
            r = invoke(root, '--reference', s, inputs())
            check(r[3] == ['returned', [['index', value]]] and len(r[4]) == count,
                  f'{alternative} result and active events', r)
            check(r[5] == [], f'{alternative} resource state', r)
            if count:
                check(r[4][0][1][1][4][-1] == ['match', 'select', 'Some'], 'local origin', r)
            for physical in [False, True]:
                c = candidate(s, physical)
                r = invoke(root, '--check', s, c)
                check(r[0] == 'checked', f'{alternative} correspondence {physical}', r)
                bad = copy.deepcopy(c)
                bad[3][0][4][1][4][1][2] = [['op', 'changed', 'add', [], ['fallback', 'fallback'], ['double']],
                                          ['yield', ['double']]]
                r = invoke(root, '--check', s, bad)
                check(r == ['refused', 'source-local-unmatched'], f'{alternative} dormant mutation {physical}', r)
            r = invoke(root, '--physical-local-reference', s, candidate(s, True), inputs(),
                       ['zkc.local-resources/1', '67108864', []])
            check(r[1] == ['returned', [['index', value]]] and r[4][1:3] == ['1', '512'] and r[4][4] == '0',
                  f'{alternative} physical result and cleanup', r)
        mutations = {
            'missing': lambda s: s[2][0][4][1][4].pop(),
            'duplicate': lambda s: s[2][0][4][1][4][1].__setitem__(0, 'Some'),
            'unknown': lambda s: s[2][0][4][1][4][1].__setitem__(0, 'Other'),
            'wrong-payload': lambda s: s[2][0][4][0].__setitem__(4, []),
            'arm-isolation': lambda s: s[2][0][4][1][4][1].__setitem__(2, [['yield', ['active']]]),
            'scrutinee-isolation': lambda s: s[2][0][4][1][4][1].__setitem__(2, [['yield', ['value']]]),
            'capture-collision': lambda s: s[2][0][4][1][4][0].__setitem__(1, ['fallback']),
            # A stop inside a role-free local function names no participant.
            'stop-owner': lambda s: s[2][0][4][1][4][0].__setitem__(2, [['stop', 'halt', 'P', 'reject']]),
            # An arm is its alternative, its payload binders and its body.
            'arm-shape': lambda s: s[2][0][4][1][4].__setitem__(1, ['None', []]),
            # A variant is a local value, never a protocol port.
            'protocol-boundary': lambda s: s[3][0][4][0].__setitem__(2, CHOICE),
            # Only a variant is matched, and only into a variant type is one packed.
            'scrutinee-type': lambda s: s[2][0][4][1].__setitem__(2, 'x'),
            'pack-type': lambda s: s[2][0][4][0].__setitem__(2, 'index'),
        }
        expected = {'missing': 'variant-arms', 'duplicate': 'variant-arms',
                    'unknown': 'variant-arms', 'wrong-payload': 'variant-payload-types',
                    'arm-isolation': 'unbound:active', 'scrutinee-isolation': 'unbound:value',
                    'capture-collision': 'ssa-rebinding', 'stop-owner': 'local-stop-role',
                    'arm-shape': 'variant-arm', 'protocol-boundary': 'variant-protocol-boundary',
                    'scrutinee-type': 'variant-type', 'pack-type': 'variant-type'}
        for name, change in mutations.items():
            s = source()
            change(s)
            r = invoke(root, '--admit', s)
            check(r == ['refused', expected[name]], name, r)
        # The candidate's arms are checked by the same shape rule on their own.
        c = candidate(source())
        c[3][0][4][1][4][1] = ['None', []]
        r = invoke(root, '--check', source(), c)
        check(r == ['refused', 'variant-arm'], 'candidate arm shape', r)
        s = source()
        s[2][0][4][1][4][0][2] = [['stop', 'halt', '', 'reject']]
        r = invoke(root, '--reference', s, inputs())
        check(r[3][:2] == ['reject', 'explicit-stop'] and not r[4], 'uncatchable selected stop', r)
        r = invoke(root, '--physical-local-reference', s, candidate(s, True), inputs(),
                   ['zkc.local-resources/1', '67108864', []])
        check(r[1][:2] == ['reject', 'explicit-stop'] and r[4][1:3] == ['0', '0'] and r[4][4] == '0',
              'physical stopped cleanup', r)
        # Neither nested descriptors nor active resource handles are flattened
        # into fictitious inactive payloads.
        nested = descriptor('pkg/nested', [['Wrap', [CHOICE]]])
        s = source()
        original = s[2][0][4][1]
        s[2][0][4][1:2] = [['variant', 'outer', nested, 'Wrap', ['value'], 'wrapped'],
                           ['match', 'outer_select', 'wrapped', ['fallback'],
                            [['Wrap', ['value'], [original, ['yield', ['out']]]]], ['out']]]
        r = invoke(root, '--reference', s, inputs())
        check(r[3] == ['returned', [['index', '12']]], 'nested active selection', r)
        r = invoke(root, '--check', s, candidate(s, True))
        check(r[0] == 'checked', 'nested physical correspondence', r)
        # Helpers inside match are expanded with payload/capture renaming.
        s = source()
        s[2].append(['function', 'Plus', [['a', 'index'], ['b', 'index']], ['index'],
                     [['op', 'plus', 'add', [], ['a', 'b'], ['r']], ['return', ['r']]], ['Plus', []]])
        s[2][0][4][1][4][0][2][0] = ['apply', 'sum', 'Plus', [], ['active', 'fallback'], ['sum']]
        r = invoke(root, '--reference', s, inputs())
        check(r[3] == ['returned', [['index', '12']]], 'helper in selected arm', r)
        s[2][1][4] = [['stop', 'halt', '', 'abort']]
        r = invoke(root, '--reference', s, inputs())
        check(r[3][:2] == ['abort', 'explicit-stop'] and not r[4], 'stop-only helper does not mint output', r)
        # A private tag must not schedule a protocol transcript effect, whether
        # the effect is the internal transcript family or an external duplex
        # state that carries the same history.
        for contract, ins, outs in HISTORY:
            r = invoke(root, '--admit', external_arm(contract, ins, outs))
            check(r == ['refused', 'variant-challenge'], f'{contract} in an arm', r)
        for contract, ins, outs in PURE:
            r = invoke(root, '--admit', external_arm(contract, ins, outs))
            check(r[0] == 'checked', f'{contract} in an arm admitted', r)
        helper = ['function', 'Effect', [['s', 'indices']], ['indices'],
                  [['op', 'effect', 'kernel', [], ['s'], ['s2', 'i']], ['return', ['s2']]],
                  ['Effect', []]]
        r = invoke(root, '--admit', effect_source('external.openvm.sample',
                   [['apply', 'call', 'Effect', [], ['s'], ['s2']], ['yield', ['s2']]], [helper]))
        check(r == ['refused', 'variant-challenge'], 'history effect through a helper', r)
        r = invoke(root, '--admit', effect_source('external.openvm.sample',
                   [['for', 'repeat', 'i', 'n', 'm', [['carried', 's']], [],
                     [['op', 'effect', 'kernel', [], ['carried'], ['next', 'drawn']],
                      ['yield', ['next']]], ['sampled']],
                    ['yield', ['sampled']]]))
        check(r == ['refused', 'variant-challenge'], 'history effect under a nested loop', r)
        # One logical type has one spelling; `bool:` is not a second name for it.
        r = invoke(root, '--admit', tagged_witness('bool'))
        check(r[0] == 'checked', 'canonical payload leaf', r)
        r = invoke(root, '--admit', tagged_witness('bool:'))
        check(r == ['refused', 'binding-type'], 'noncanonical payload leaf', r)
    for name, result in failures:
        print(f'FAIL {name}: {result}')
    if failures:
        raise SystemExit(f'{len(failures)} failures; {passed} checks passed')
    print(f'finite local variant CLI: {passed} checks passed')


if __name__ == '__main__':
    main()
