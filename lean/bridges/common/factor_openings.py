"""Finite native/Lean controls for composed Sumcheck and public factor checks."""
import copy
import hashlib
import json

from contracts import label
from native_entry import native_subject

from structured import render
from verify import read_json, render_client

MODULUS = 52435875175126190479447740508185965837690552500527637822603658699938581184513


def factor(coefficients, first, second):
    a, b, c, d = coefficients
    return (a + second * b + first * (c + second * d)) % MODULUS


def product(left, right):
    result = [[0] * 3 for _ in range(3)]
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            x, y = i // 2 + j // 2, i % 2 + j % 2
            result[x][y] = (result[x][y] + a * b) % MODULUS
    return result


def transcript(left, right, first, second, attack='honest'):
    rows = product(left, right)
    message = [(2*a+b+c) % MODULUS for a, b, c in rows]
    claim = (2*message[0]+message[1]+message[2]) % MODULUS
    next_message = [(rows[0][j]+first*rows[1][j]+first*first*rows[2][j]) % MODULUS for j in range(3)]
    if attack == 'first-boundary':
        message[0] = (message[0] + 1) % MODULUS
    if attack == 'second-boundary':
        next_message[0] = (next_message[0] + 1) % MODULUS
    if attack == 'terminal':
        next_message[0] = (next_message[0] + 1) % MODULUS
        next_message[1] = (next_message[1] - 2) % MODULUS
    replies = {label(f'first{i}'): value for i, value in enumerate(message)}
    replies.update({label(f'second{i}'): value for i, value in enumerate(next_message)})
    replies.update({label('draw0', False): first, label('draw1', False): second,
                    label('deliver0'): first, label('deliver1'): second,
                    label('left'): (factor(left, first, second) + (attack == 'left')) % MODULUS,
                    label('right'): (factor(right, first, second) + (attack == 'right')) % MODULUS})
    return claim, replies


def check_factor_forms(suite, root, execute):
    sources, fixtures = {}, []
    for form in ('Expanded', 'Horner', 'WrongPoint', 'WrongResidual'):
        flags = ['--source-format=zkc',
                 '--module=factor_openings=lean/bridges/common/fixtures/factor-openings.zkc',
                 '--subject=factor_openings::' + form + 'Protocol']
        text, interface_text, interface = native_subject(execute, suite.args.compiler, flags)
        if not (interface['original'] == hashlib.sha256(text.encode()).hexdigest()):
            raise AssertionError("bridges/common/factor_openings.py:54: interface['original'] == hashlib.sha256(text.encode()).hexdigest()")
        symbol = interface['protocol']
        data = suite.exercise(text, symbol)
        fixture = root / f'lean/ZkcExamples/NativePrograms/fixtures/factor-{form.lower()}.json'
        if not (data == json.loads(fixture.read_text())):
            raise AssertionError(f'factor/{form}: source drift')
        constructor = fixture.parent.parent / 'Variants' / f'Factor{form}Data.lean'
        if not (render(data, f'ZkcExamples.NativePrograms.Variants.Factor{form}Data') == constructor.read_text()):
            raise AssertionError("bridges/common/factor_openings.py:60: render(data, f'ZkcExamples.NativePrograms.Variants.Factor{form}Data') == constructor.read_text()")
        request = read_json(root / 'lean/bridges/common/requests/factor-openings.json')
        client = root / f'lean/security/ZkcSecurity/Examples/NativePrograms/Factor{form}.lean'
        if not (render_client(data, request, f'Factor{form}',
                              positive=form not in ('WrongPoint', 'WrongResidual')) == client.read_text()):
            raise AssertionError("bridges/common/factor_openings.py:63: render_client(data, request, f'Factor{form}') == client.read_text()")
        sources[form] = text, symbol
        fixtures.append({'form': form, 'source': data[2]})

    stopped_prefixes = 0
    def replay(form, left, right, first, second, attack='honest', role=1, stops=False):
        nonlocal stopped_prefixes
        text, symbol = sources[form]
        native, exported, _ = suite.export(text, symbol)
        claim, replies = transcript(left, right, first, second, attack)
        request = ['scalar-control', role, [*left, *right, claim, 7 if role == 1 else None], []]
        for _ in range(16):
            result = suite.compare(native, exported, symbol, request)
            if not result[3] or result[3][-1][1] != ['missing']:
                return result
            action = result[3][-1][0]
            if stops:
                for reason in ('reject', 'abort', 'exhausted', 'incomplete', 'refused'):
                    interrupted = copy.deepcopy(request)
                    interrupted[3].append([action, ['stop', reason]])
                    observed = suite.compare(native, exported, symbol, interrupted)
                    if not (observed[1] == ['stopped', reason]):
                        raise AssertionError("bridges/common/factor_openings.py:84: observed[1] == ['stopped', reason]")
                    if not (observed[2] == len(interrupted[3])):
                        raise AssertionError('bridges/common/factor_openings.py:85: observed[2] == len(interrupted[3])')
                    stopped_prefixes += 1
            request[3].append([action, ['return', None if action[0] == 'send' else replies[action[1]]]])
        raise AssertionError('composed action bound')

    equalities, outcomes = 0, {}
    expected = {'honest': ['returned', True], 'first-boundary': ['stopped', 'reject'],
                'second-boundary': ['stopped', 'reject'], 'terminal': ['returned', False],
                'left': ['stopped', 'reject'], 'right': ['returned', False]}
    for case in range(24):
        left = [suite.rng.randrange(97) for _ in range(4)]
        right = [suite.rng.randrange(97) for _ in range(4)]
        first, second = suite.rng.randrange(97), suite.rng.randrange(2, 48)
        attack = list(expected)[case % len(expected)]
        results = [replay(form, left, right, first, second, attack,
                          stops=(case == 0)) for form in ('Expanded', 'Horner')]
        if not (results[0] == results[1]):
            raise AssertionError('bridges/common/factor_openings.py:101: results[0] == results[1]')
        if not (results[0][1] == expected[attack]):
            raise AssertionError('bridges/common/factor_openings.py:102: results[0][1] == expected[attack]')
        if attack == 'left':
            if not (results[0][2] == 11 and all(event[0][1] != label('right') for event in results[0][3])):
                raise AssertionError("bridges/common/factor_openings.py:104: results[0][2] == 11 and all(event[0][1] != label('right') for event in results[0][3])")
        equalities += 1
        outcomes[attack] = results[0][1]
    # Exercise the actual honest prover projection too; verifier security remains
    # quantified over arbitrary causal messages in its separate Lean theorem.
    for form in ('Expanded', 'Horner'):
        if not (replay(form, [2, 3, 5, 7], [11, 13, 17, 19], 3, 5, role=0)[1] == ['returned', None]):
            raise AssertionError("bridges/common/factor_openings.py:110: replay(form, [2, 3, 5, 7], [11, 13, 17, 19], 3, 5, role=0)[1] == ['returned', None]")
    wrong_point = [replay(form, [0, 0, 1, 0], [1, 0, 0, 0], 1, 0)
                   for form in ('Expanded', 'WrongPoint')]
    if not (wrong_point[0][1] == ['returned', True] and wrong_point[1][1] == ['stopped', 'reject']):
        raise AssertionError("bridges/common/factor_openings.py:113: wrong_point[0][1] == ['returned', True] and wrong_point[1][1] == ['stopped', 'reject']")
    wrong_residual = [replay(form, [0, 1, 0, 0], [1, 0, 0, 0], 3, 5)
                      for form in ('Expanded', 'WrongResidual')]
    if not (wrong_residual[0][1] == ['returned', True] and wrong_residual[1][1] == ['returned', False]):
        raise AssertionError("bridges/common/factor_openings.py:116: wrong_residual[0][1] == ['returned', True] and wrong_residual[1][1] == ['returned', False]")
    return {'fixtures': fixtures, 'verifier_execution_equalities': equalities,
            'stopped_prefix_controls': stopped_prefixes, 'outcomes': outcomes,
            'wrong_point_outcomes': [r[1] for r in wrong_point],
            'wrong_residual_outcomes': [r[1] for r in wrong_residual],
            'interpretation': 'finite BLS scalar-field differential evidence, independent of symbolic security proofs'}
