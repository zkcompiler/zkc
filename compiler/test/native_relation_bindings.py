"""Structured relation ports retain actual components and executable checks."""
import json
from pathlib import Path
import re

from cases import case, counted
from commands import Commands
from tools import compiler, records

OUT = records()
commands = Commands(OUT)
fixtures = Path(__file__).parent / 'fixtures/mathematical'
manifest = []
policy_data = ['zkc.native-proof-policy/4', 'main', 'P', 'V', '1', '', '', ['0', '1'], []]
policy = OUT / 'policy.json'
policy.write_text(json.dumps(policy_data))
for family in ['r1cs', 'air']:
    source = fixtures / f'relation-{family}.mlir'
    text = source.read_text()
    for suffix, options in [('', ()), ('_plain', ('--no-simplify',)),
                            ('_release', ('--release-storage',))]:
        name = family + suffix
        with case(name):
            deployment = commands.run([compiler, 'protocol-proof', source, policy, *options])
            envelope = json.loads(deployment)
            assert envelope[0] == 'zkc.native-proof/4'
            assert json.loads(envelope[4])[0] == 'zkc.program/1'
            assert len(envelope[4]) < 40000
            (OUT / f'{name}.deployment').write_text(deployment)
            manifest.append(dict(name=name, family=family))
            (OUT / f'{name}.bundle').write_text(commands.run([
                compiler, 'protocol-bundle', source, *options]))
    with case(f'{family} source-relative binding'):
        candidate = commands.run([compiler, 'protocol-construct-proof', source, policy])
        path = OUT / 'candidate.mlir'
        path.write_text(candidate)
        commands.run([compiler, 'protocol-check-proof', source, policy, path])
        # Retained metadata can be well-formed yet describe another statement.
        changed = candidate.replace('acceptance = 1 : i64', 'acceptance = 0 : i64')
        assert changed != candidate
        commands.verified(changed)
        path.write_text(changed)
        commands.run([compiler, 'protocol-check-proof', source, policy, path],
                     refuses='native-proof-correspondence')
        changed = candidate.replace('relation_revision = "1"', 'relation_revision = "2"')
        commands.verified(changed, 'mathematical-projection')
        changed, count = re.subn(r'("algebra.exec.field_equal"\()(%\w+), (%\w+)',
                                r'\1\3, \3', candidate, count=1)
        assert count == 1
        path.write_text(changed)
        commands.run([compiler, 'protocol-check-proof', source, policy, path],
                     refuses='native-proof-correspondence')
    with case(f'{family} exact actual entry selection'):
        commands.verified(text.replace('selectors=["V","V","P"]',
                                       'selectors=["V","V","V"]'),
                          'mathematical-formation')
        commands.verified(text.replace('acceptance=1 : i64', 'acceptance=2 : i64'),
                          'mathematical-formation')
    with case(f'{family} witness cannot be a verifier input'):
        path = OUT / f'{family}_public_witness.mlir'
        path.write_text(text.replace('input_roles=[["V"],["V"],["P"]]',
                                     'input_roles=[["V"],["V"],["P","V"]]'))
        p = list(policy_data)
        p[7] = ['0', '1', '2']
        altered = OUT / 'public-witness.policy'
        altered.write_text(json.dumps(p))
        commands.run([compiler, 'protocol-proof', path, altered],
                     refuses='native-proof-private-verifier-witness')
    with case(f'{family} deployment selects the declared decision'):
        path = OUT / 'decoy.mlir'
        path.write_text(text.replace('arith.constant false', 'arith.constant true'))
        p = list(policy_data)
        p[4] = '0'
        altered = OUT / 'decoy.policy'
        altered.write_text(json.dumps(p))
        commands.run([compiler, 'protocol-proof', path, altered],
                     refuses='native-proof-statement-acceptance')
    with case(f'{family} every statement must designate the deployment decision'):
        statement = next(line for line in text.splitlines() if ' protocol.statement ' in line)
        path = OUT / 'two-statements.mlir'
        path.write_text(text.replace(statement, statement + '\n' + statement))
        commands.run([compiler, 'protocol-proof', path, policy])
        other = statement.replace('acceptance=1 : i64', 'acceptance=0 : i64')
        path.write_text(text.replace(statement, statement + '\n' + other))
        commands.run([compiler, 'protocol-proof', path, policy],
                     refuses='native-proof-statement-acceptance')
    for purpose in ['parameter', 'statement']:
        with case(f'{family} {purpose} must be validator-bound'):
            path = OUT / 'private-public.mlir'
            path.write_text(text.replace('"statement","witness"',
                                         f'"statement","{purpose}"'))
            commands.run([compiler, 'protocol-proof', path, policy],
                         refuses='native-proof-statement-public-input')
    with case(f'{family} shared configuration and renamed relation identity'):
        shared = text.replace('input_roles=[["V"],["V"],["P"]]',
                              'input_roles=[["P","V"],["V"],["P"]]')
        shared = shared.replace('selectors=["V","V","P"]',
                                'selectors=["P","V","P"]')
        shared = shared.replace('kind="external"', 'kind="alternate"')
        shared = shared.replace('key="example/', 'key="renamed/').replace(
            'revision="1"', 'revision="2"')
        path = OUT / f'{family}_shared.mlir'
        path.write_text(shared)
        (OUT / f'{family}_shared.deployment').write_text(commands.run([
            compiler, 'protocol-proof', path, policy]))
        manifest.append(dict(name=f'{family}_shared', family=family))
    with case(f'{family} structured data through transcript construction'):
        first, witness = ('!ms', '!v') if family == 'r1cs' else ('!config', '!trace')
        derived = '!s = !protocol.service_ref<"random.bls12-381.fr/1">\n' + text
        derived = derived.replace(f'%witness:{witness}):', f'%witness:{witness},%random:!s):')
        derived = derived.replace(f'function_type=({first},!v,{witness})',
                                  f'function_type=({first},!v,{witness},!s)')
        derived = derived.replace('input_roles=[["V"],["V"],["P"]]',
                                  'input_roles=[["V"],["V"],["P"],["V"]]')
        derived = derived.replace(' %received = protocol.exchange',
            ' %draw = "protocol.query"(%random) {method="draw",owner="V",site="draw"} : (!s)->!f\n'
            ' %challenge = protocol.exchange %draw {sender="V",receiver="P",site="challenge"} : !f\n'
            ' %received = protocol.exchange')
        # The draw exercises construction; these direct checkers do not claim
        # a random-combination argument or a cryptographic soundness bound.
        path = OUT / f'{family}_derived.mlir'
        path.write_text(derived)
        p = list(policy_data)
        p[5:7] = ['merlin3.bls12-381.fr64be/1', '3']
        p[8] = [['draw', 'challenge']]
        altered = OUT / 'derived.policy'
        altered.write_text(json.dumps(p))
        candidate = commands.run([compiler, 'protocol-construct-proof', path, altered])
        target = OUT / 'derived.candidate.mlir'
        target.write_text(candidate)
        commands.run([compiler, 'protocol-check-proof', path, altered, target])
        (OUT / f'{family}_derived.deployment').write_text(commands.run([
            compiler, 'protocol-proof', path, altered]))
        manifest.append(dict(name=f'{family}_derived', family=family))
        requirement = OUT / 'public-coin.json'
        requirement.write_text(json.dumps(dict(
            format='zkc.public-coin-requirement/1', entry='main', prover='P', verifier='V',
            service=3, decision=1, bound_inputs=[0, 1],
            draws=[dict(query_site='draw', delivery_site='challenge')])))
        commands.run([compiler, 'protocol-public-coin', path, requirement],
                     refuses='public-coin-verifier-local')
        # The public-coin view has its own total-verifier profile. Check its
        # structured statement retention without claiming local-body analysis.
        total = re.sub(r' %accepted = "protocol.local_call"[^\n]+',
                       ' %accepted = arith.constant true', derived)
        assert total != derived
        path = OUT / 'total-view.mlir'
        path.write_text(total)
        view = json.loads(commands.run([compiler, 'protocol-public-coin', path, requirement]))
        assert view['statement_inputs'] == [0, 1]
        assert view['bound_non_statement_inputs'] == []
        assert view['decision_dependencies'] == []  # constant-true test decision
        # The total verifier view cannot summarize an owner-local early exit.
        early = total.replace(
            ' "protocol.return"(%unused,%accepted)',
            ' "protocol.finish_if"(%accepted,%unused,%accepted) '
            '{owner="V",site="finish"} : (i1,i1,i1)->()\n'
            ' "protocol.return"(%unused,%accepted)',
        )
        assert early != total
        path.write_text(early)
        commands.run([compiler, 'protocol-public-coin', path, requirement],
                     refuses='public-coin-dependence')

    with case(f'{family} renamed roles and reordered entry ports'):
        first, witness = ('!ms', '!v') if family == 'r1cs' else ('!config', '!trace')
        moved = text.replace(f'%configuration:{first},%public:!v,%witness:{witness}',
                             f'%witness:{witness},%configuration:{first},%public:!v')
        moved = moved.replace(f'function_type=({first},!v,{witness})',
                              f'function_type=({witness},{first},!v)')
        moved = moved.replace('input_roles=[["V"],["V"],["P"]]',
                              'input_roles=[["P"],["V"],["V"]]')
        moved = moved.replace('"P"', '"Prover"').replace('"V"', '"Checker"')
        moved = moved.replace('sym_name="main"', 'sym_name="verify_relation"')
        path = OUT / f'{family}_reordered.mlir'
        path.write_text(moved)
        p = list(policy_data)
        p[1:4] = ['verify_relation', 'Prover', 'Checker']
        p[7] = ['1', '2']
        altered = OUT / 'reordered.policy'
        altered.write_text(json.dumps(p))
        (OUT / f'{family}_reordered.deployment').write_text(commands.run([
            compiler, 'protocol-proof', path, altered]))
        manifest.append(dict(name=f'{family}_reordered', family=family, order=[2, 0, 1]))
with case('same-typed statement operands still require source correspondence'):
    source = fixtures / 'relation-r1cs.mlir'
    candidate = commands.run([compiler, 'protocol-construct-proof', source, policy])
    changed = candidate.replace('inputs = [0, 1, 2], relation =',
                                'inputs = [0, 2, 1], relation =').replace(
        'selectors = ["V", "V", "P"]', 'selectors = ["V", "P", "V"]')
    assert changed != candidate
    commands.verified(changed)
    path = OUT / 'swapped.mlir'
    path.write_text(changed)
    commands.run([compiler, 'protocol-check-proof', source, policy, path],
                 refuses='native-proof-correspondence')
with case('logical relation data does not install a native wire codec'):
    # A logical static array is supported independently of native array codecs.
    unsupported = '''!m = tensor<4x!algebra.field<"koala-bear">>
module { "protocol.module"() ({
relation.declare @relation {kind="external",key="example/foreign",revision="1",signature=(!m)->i1,purposes=["parameter"]}
"protocol.func"() ({ ^entry(%data:!m,%ok:i1):
 protocol.statement @relation(%data) {selectors=["V"],acceptance=0 : i64} : !m
 "protocol.return"(%ok) : (i1)->()
}) {sym_name="main",function_type=(!m,i1)->i1,roles=["P","V"],input_roles=[["V"],["V"]],output_roles=[["V"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
'''
    commands.verified(unsupported)
    path = OUT / 'unsupported.mlir'
    path.write_text(unsupported)
    p = list(policy_data)
    p[4] = '0'
    altered = OUT / 'unsupported.policy'
    altered.write_text(json.dumps(p))
    commands.run([compiler, 'protocol-proof', path, altered],
                 refuses='native-proof-wire-type')
(OUT / 'manifest.json').write_text(json.dumps(manifest))
counted()
