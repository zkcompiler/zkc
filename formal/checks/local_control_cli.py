#!/usr/bin/env python3
"""Executable Lean local-control regressions; run after lake build of both tools.

Handwritten source/candidate trees, independent expected outcomes/accounting.
No native compiler, prover, network, or golden generated candidate is required.
"""
import copy
import json
from pathlib import Path
import subprocess
import tempfile

FORMAL = Path(__file__).resolve().parents[1]
INTERACTIVE = FORMAL / '.lake/build/bin/interactive-protocol'
ARTIFACT = FORMAL / '.lake/build/bin/artifact-reference'
checks = 0


def check(condition, context):
    global checks
    assert condition, context
    checks += 1


def invoke(root, executable, command, *trees):
    paths = []
    for i, tree in enumerate(trees):
        path = root / f'input-{i}.json'
        path.write_text(json.dumps(tree))
        paths.append(str(path))
    result = subprocess.run([str(executable), command, *paths], capture_output=True, text=True, timeout=30)
    try:
        return json.loads(result.stdout)
    except Exception as error:
        raise AssertionError((result.returncode, result.stdout, result.stderr)) from error


def source():
    args = [['choose', 'bool'], ['lo', 'index'], ['hi', 'index'], ['x', 'index']]
    loop = ['for', 'loop', 'i', 'lo', 'hi', [['acc', 'x']], [],
            [['op', 'plus', 'add', [], ['acc', 'i'], ['sum']], ['yield', ['sum']]], ['total']]
    body = [['if', 'branch', 'choose', ['lo', 'hi', 'x'],
             [loop, ['yield', ['total']]], [['yield', ['x']]], ['out']], ['return', ['out']]]
    return ['zkc.protocol/1', [['add', 'index.add', [], '']],
            [['function', 'Sum', args, ['index'], body, ['Sum', []]]],
            [['protocol', 'Main', ['P'], [], [[n, 'P', t] for n, t in args], [['P', 'index']], [],
              [['local', 'invoke', 'P', 'Sum', [n for n, _ in args], ['out']], ['return', ['out']]]]],
            [['instance', 'root', 'Main', [], [], [['P', 'P']]]], [['entry', 'main', 'root']]]


def candidate(s, physical=False):
    args = copy.deepcopy(s[2][0][2])
    results = ['index']
    if physical:
        args = [[n, t + '@native.' + t + '/1'] for n, t in args]
        results = ['index@native.index/1']
    return ['zkc.participants/1', [['add', 'index.add', [], 'native/index.add' if physical else '']],
            'physical' if physical else 'logical',
            [['function', 'Sum', args, results, copy.deepcopy(s[2][0][4]), ['Sum', []]]],
            [['participant', 'p', 'root', 'P', [], args, results,
              [['local', 'invoke', 'Sum', [n for n, _ in args], ['out']], ['return', ['out']]]]],
            [['entry', 'main', [['P', 'p']]]]]


def inputs(choose=True, lo=0, hi=4, x=0):
    return ['zkc.reference-inputs/1', 'main', 'test', [['P', [
        ['choose', ['bool', str(choose).lower()]], ['lo', ['index', str(lo)]],
        ['hi', ['index', str(hi)]], ['x', ['index', str(x)]]]]], [], [], []]


def generic(s):
    g = copy.deepcopy(s)
    body = g[2][0][4]
    body[0][4][0][7][0] = ['op', 'plus', 'index.add', [], [], ['acc', 'i'], ['sum']]
    declaration = ['generic_function', 'SumDef', [], [], g[2][0][2], ['index'], body]
    g[1], g[2] = [], []
    return ['zkc.library/1', [declaration], [['configure', 'Sum', 'SumDef', [], []]], g]


def helper_source(s):
    h = copy.deepcopy(s)
    helper = ['function', 'Plus', [['a', 'index'], ['b', 'index']], ['index'],
              [['op', 'added', 'add', [], ['a', 'b'], ['r']], ['return', ['r']]], ['Plus', []]]
    h[2][0][4][0][4][0][7][0] = ['apply', 'plus', 'Plus', [], ['acc', 'i'], ['sum']]
    h[2].append(helper)
    return h


def main():
    with tempfile.TemporaryDirectory(prefix='zkc-lean-local-control-') as temporary:
        root = Path(temporary)
        s = source()
        for form in [s, generic(s), helper_source(s)]:
            result = invoke(root, INTERACTIVE, '--admit', form)
            check(result[0] == 'checked', ('admit', result))
            for choose, lo, hi, x, expected in [(True, 0, 4, 0, 6), (True, 3, 3, 7, 7),
                                               (True, 5, 2, 9, 9), (False, 0, 4, 11, 11),
                                               (True, 2, 5, 1, 10)]:
                result = invoke(root, INTERACTIVE, '--reference', form, inputs(choose, lo, hi, x))
                check(result[3] == ['returned', [['index', str(expected)]]], ('execute', result))
                requests = [e for e in result[4] if e[0] == 'request']
                check(len(requests) == (max(hi-lo, 0) if choose else 0), ('reached requests', requests))
                if requests:
                    path = requests[0][1][1][4]
                    helper = form[0] == 'zkc.protocol/1' and len(form[2]) > 1
                    branch_site, loop_site = ('lc_6_branch', 'lc_4_loop') if helper else ('branch', 'loop')
                    check(path[-2:] == [['if', branch_site, 'then'], ['for', loop_site, str(lo)]], ('path', path))
        for physical in [False, True]:
            c = candidate(s, physical)
            result = invoke(root, INTERACTIVE, '--check', s, c)
            check(result[0] == 'checked', ('candidate', result))
            # Type-correct mutations in branch condition, dormant body and loop bound.
            for change in ['bound', 'body', 'capture']:
                bad = copy.deepcopy(c)
                if change == 'bound':
                    bad[3][0][4][0][4][0][3:5] = ['hi', 'lo']
                elif change == 'body':
                    bad[3][0][4][0][5] = [['op', 'changed', 'add', [], ['x', 'lo'], ['new']], ['yield', ['new']]]
                else:
                    bad[3][0][4][0][3] = ['hi', 'lo', 'x']
                result = invoke(root, INTERACTIVE, '--check', s, bad)
                check(result[0] == 'refused', ('candidate mutation', change, result))
        c = candidate(s, True)
        storage = ['zkc.local-resources/1', '67108864', []]
        # 4 root inputs, 4 local inputs, 3 branch inputs, 4*(index+carry+sum),
        # loop result, branch result, wrapper result and root return = 27 scalars.
        for params, expected, instructions, allocations in [((True, 0, 4, 0), 6, 14, 27),
                                                            ((True, 4, 4, 7), 7, 6, 15),
                                                            ((False, 0, 4, 7), 7, 5, 14)]:
            result = invoke(root, INTERACTIVE, '--physical-local-reference', s, c, inputs(*params), storage)
            check(result[1] == ['returned', [['index', str(expected)]]], ('physical result', result))
            check(result[4] == [str(instructions), '1', '512', str(allocations * 512), '0'],
                  ('physical accounting', result[4], instructions, allocations))
        result = invoke(root, INTERACTIVE, '--physical-local-reference', s, c,
                        inputs(True, 0, 1048577, 0), storage)
        check(result[1][:2] == ['exhausted', 'local-bound-limit'] and
              result[4] == ['3', '0', '0', '5632', '0'], ('bound stop cleanup', result))
        check(not result[5], ('unreached body has no backend attempts', result[5]))
        # Input-length selection plus indexed field-vector access, through both twins.
        f = 'field:bls12-381.fr'
        v = 'vector:bls12-381.fr'
        declarations = [['length', 'vector.length', ['bls12-381.fr'], ''],
                        ['zero_index', 'index.constant', [], ''],
                        ['zero_field', 'field.constant', ['bls12-381.fr'], ''],
                        ['get', 'vector.get', ['bls12-381.fr'], ''],
                        ['add', 'field.add', ['bls12-381.fr'], '']]
        body = [['op', 'length', 'length', [], ['xs'], ['n']],
                ['op', 'lower', 'zero_index', ['0'], [], ['zero']],
                ['op', 'initial', 'zero_field', ['0'], [], ['initial']],
                ['for', 'sum_loop', 'i', 'zero', 'n', [['acc', 'initial']], ['xs'],
                 [['op', 'element', 'get', [], ['xs', 'i'], ['item']],
                  ['op', 'plus', 'add', [], ['acc', 'item'], ['next']], ['yield', ['next']]], ['out']],
                ['return', ['out']]]
        vector_source = ['zkc.protocol/1', declarations,
                         [['function', 'Sum', [['xs', v]], [f], body, ['Sum', []]]],
                         [['protocol', 'Main', ['P'], [], [['xs', 'P', v]], [['P', f]], [],
                           [['local', 'invoke', 'P', 'Sum', ['xs'], ['out']], ['return', ['out']]]]],
                         s[4], s[5]]
        vp, fp = v + '@arkworks.fr-vector/1', f + '@arkworks.fr/1'
        physical_declarations = [[name, contract, args,
                                  ('native/' if contract.startswith('index.') else 'arkworks/') + contract]
                                 for name, contract, args, _ in declarations]
        vector_candidate = ['zkc.participants/1', physical_declarations, 'physical',
                            [['function', 'Sum', [['xs', vp]], [fp], body, ['Sum', []]]],
                            [['participant', 'p', 'root', 'P', [], [['xs', vp]], [fp],
                              [['local', 'invoke', 'Sum', ['xs'], ['out']], ['return', ['out']]]]],
                            c[5]]
        for xs, expected, instructions, total in [(['1', '2', '3'], '6', '16', '10976'),
                                                ([], '0', '7', '3584')]:
            vector_inputs = ['zkc.reference-inputs/1', 'main', 'test', [['P', [['xs', [v, xs]]]]], [], [], []]
            result = invoke(root, INTERACTIVE, '--reference', vector_source, vector_inputs)
            check(result[3] == ['returned', [[f, expected]]], ('input-length vector sum', result))
            result = invoke(root, INTERACTIVE, '--physical-local-reference', vector_source,
                            vector_candidate, vector_inputs, storage)
            check(result[1] == ['returned', [[f, expected]]], ('physical vector sum', result))
            check(result[4] == [instructions, '1', '512', total, '0'], ('physical vector accounting', result))
        # An admitted large finite count stops at the shared runtime iteration
        # ceiling, without host stack overflow or allocating an unrolled body.
        large = copy.deepcopy(s)
        large[2][0][4][0][4][0][7] = [['yield', ['acc']]]
        result = invoke(root, INTERACTIVE, '--reference', large, inputs(True, 0, 100001, 0))
        check(result[3][:2] == ['exhausted', 'local-iteration-limit'] and not result[4],
              ('logical iteration budget', result[3]))
        result = invoke(root, INTERACTIVE, '--physical-local-reference', large, candidate(large, True),
                        inputs(True, 0, 100001, 0), storage)
        check(result[1][:2] == ['limit', 'iterations'] and
              result[4] == ['100003', '0', '0', '102405632', '0'], ('physical iteration cleanup', result))
        # Malformed unreachable regions are rejected before selecting a Boolean.
        for malformed in [[], [['return', ['x']]], [['yield', ['absent']]], [['yield', ['choose']]]]:
            bad = copy.deepcopy(s)
            bad[2][0][4][0][5] = malformed
            result = invoke(root, INTERACTIVE, '--admit', bad)
            check(result[0] == 'refused', ('malformed dormant', result))
        # Identity traverses local regions with lexical SSA and function-wide sites.
        # Its body helper is covered in Lean tests; the artifact executable is
        # exercised here with a full two-role construction descriptor.
        identity_source = copy.deepcopy(s)
        protocol = identity_source[3][0]
        protocol[2] = ['P', 'V']
        protocol[4].extend([['accepted', 'V', 'bool'], ['coins', 'V', 'rng:bls12-381.fr']])
        protocol[5] = [['V', 'bool']]
        protocol[7][-1] = ['return', ['accepted']]
        identity_source[4][0][5] = [['P', 'P'], ['V', 'V']]
        descriptor = ['zkc.construction/1', 'main', 'P', 'V', [['accepted', [['V', 'accepted']]]],
                      ['coins', []], '0', 'merlin3.bls12-381.fr64be/1', 'normalized']
        result = invoke(root, ARTIFACT, 'identity', identity_source, descriptor)
        check(result[0] == 'zkc.identity-inspection/1', ('identity', result))
        normalized = result[3]
        changed = copy.deepcopy(identity_source)
        changed[2][0][4][0][4][0][7][0][2] = 'multiply'
        changed[1].append(['multiply', 'index.mul', [], ''])
        changed_identity = invoke(root, ARTIFACT, 'identity', changed, descriptor)
        check(changed_identity[0] == 'zkc.identity-inspection/1' and changed_identity[3] != normalized,
              ('nested operation identity mutation', changed_identity))
        renamed = copy.deepcopy(identity_source)
        loop = renamed[2][0][4][0][4][0]
        loop[2] = 'renamed_i'
        loop[5][0][0] = 'renamed_acc'
        loop[7][0][4] = ['renamed_acc', 'renamed_i']
        renamed_identity = invoke(root, ARTIFACT, 'identity', renamed, descriptor)
        check(renamed_identity[0] == 'zkc.identity-inspection/1' and renamed_identity[3] == normalized,
              ('local induction/carry alpha identity', renamed_identity))
    print(f'{checks} Lean local-control CLI assertions passed')


if __name__ == '__main__':
    main()
