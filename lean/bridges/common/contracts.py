"""Fixture and differential controls for reusable verifier contracts.

The catalog selects maintained examples, not security theorems. Lean separately
checks each positive certificate and proves the negative certificates impossible.
"""
import hashlib
import json

from native_entry import native_run
from snapshot import render


def label(name, exchange=True):
    return 'label_' + name.encode().hex() + ('_0' if exchange else '')


def check_contract_forms(suite, root, execute, originals):
    catalog = {
        'Schnorr': ('Helpers', 'Reordered', 'EarlyChallenge'),
        'Sumcheck': ('Helpers', 'Horner', 'WrongResidual'),
    }
    sources = {(family, 'Original'): source for family, source in originals.items()}
    fixtures = []
    for family, forms in catalog.items():
        module = family.lower() + '_forms'
        for form in forms:
            flags = ['--source-format=zkc',
                     f'--module={module}=lean/bridges/common/fixtures/{family.lower()}-forms.zkc',
                     f'--entry={module}::{form}']
            text, interface = native_run(execute, suite.args.compiler, flags)
            assert interface['original'] == hashlib.sha256(text.encode()).hexdigest()
            symbol = interface['protocol']
            data = suite.exercise(text, symbol)
            fixture = root / f'lean/ZkcExamples/NativePrograms/fixtures/{family.lower()}-{form.lower()}.json'
            assert data == json.loads(fixture.read_text()), f'{family}/{form}: source correspondence drift'
            constructor = fixture.parent.parent / 'Variants' / f'{family}{form}Data.lean'
            assert render(data, f'ZkcExamples.NativePrograms.Variants.{family}{form}Data') == constructor.read_text()
            sources[family, form] = text, symbol
            fixtures.append({'family': family, 'form': form, 'source': data[1]})
            if family == 'Sumcheck' and form != 'WrongResidual':
                suite.sumcheck(text, symbol)

    def replay(source, inputs, reply):
        text, symbol = source
        native, exported, _ = suite.export(text, symbol)
        request = ['zkc.common-run/0', 1, inputs, []]
        for _ in range(16):
            result = suite.compare(native, exported, symbol, request)
            if not result[3] or result[3][-1][1] != ['missing']:
                return result
            action = result[3][-1][0]
            request[3].append([action, ['return', None if action[0] == 'send' else reply(action)]])
        raise AssertionError('contract fixture exceeded action limit')

    # Each comparison observes the whole verifier execution, including replies
    # consumed and events. Branches are reached intentionally, not left to chance.
    comparisons = 0
    for case in range(24):
        base, key, commitment, challenge, response = [suite.rng.randrange(97) for _ in range(5)]
        values = {label('commitment'): commitment, label('challenge', False): challenge,
                  label('response'): response}
        outcomes = [replay(sources['Schnorr', form], [base, key, None, None, 7],
                           lambda action: values[action[1]])
                    for form in ('Original', 'Helpers', 'Reordered')]
        assert outcomes[0] == outcomes[1] == outcomes[2]
        comparisons += 2

        coefficients = [suite.rng.randrange(97) for _ in range(9)]
        first, second = [suite.rng.randrange(97) for _ in range(2)]
        rows = [coefficients[i:i+3] for i in (0, 3, 6)]
        message = [(2*a+b+c) % 97 for a, b, c in rows]
        next_message = [(rows[0][j] + first*rows[1][j] + first*first*rows[2][j]) % 97 for j in range(3)]
        claim = (2*message[0] + message[1] + message[2]) % 97
        if case % 3 == 1:
            message[0] = (message[0] + 1) % 97
        elif case % 3 == 2:
            next_message[0] = (next_message[0] + 1) % 97
            next_message[1] = (next_message[1] - 2) % 97
        values = {label(f'first{i}'): message[i] for i in range(3)}
        values.update({label(f'second{i}'): next_message[i] for i in range(3)})
        values.update({label('draw0', False): first, label('draw1', False): second})
        outcomes = [replay(sources['Sumcheck', form], [*coefficients, claim, 7],
                           lambda action: values[action[1]])
                    for form in ('Original', 'Helpers', 'Horner')]
        assert outcomes[0] == outcomes[1] == outcomes[2]
        comparisons += 2

    first_actions = []
    for form in ('Original', 'EarlyChallenge'):
        text, symbol = sources['Schnorr', form]
        native, exported, _ = suite.export(text, symbol)
        result = suite.compare(native, exported, symbol, ['zkc.common-run/0', 1, [1, 1, None, None, 7], []])
        assert result[1] == ['stopped', 'incomplete']
        first_actions.append(result[3][0][0])
    assert first_actions[0][0] == 'receive' and first_actions[1][0] == 'draw'

    values = {label(f'first{i}'): v for i, v in enumerate([0, 2, 0])}
    values.update({label(f'second{i}'): v for i, v in enumerate([1, 0, 0])})
    values.update({label('draw0', False): 1, label('draw1', False): 0})
    residual = [replay(sources['Sumcheck', form], [0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 7],
                       lambda action: values[action[1]])
                for form in ('Original', 'WrongResidual')]
    assert residual[0][1] == ['returned', True]
    assert residual[1][1] == ['stopped', 'reject']
    return {'fixtures': fixtures, 'verifier_execution_equalities': comparisons,
            'early_challenge_first_actions': first_actions,
            'wrong_residual_outcomes': [result[1] for result in residual],
            'interpretation': 'finite differential evidence; theorem certificates checked separately by Lean'}
