"""Compact independently executable proofs from existing general protocol clients."""
import hashlib
import json
import re
from pathlib import Path
from cases import case, counted
from commands import Commands
from tools import compiler, records

OUT = records()
commands = Commands(OUT)
FIXTURES = Path(__file__).parent / 'fixtures/mathematical'
SUITES = ['merlin3.bls12-381.fr64be/1', 'spongefish0.7.4.keccak.bls12-381.fr64be/1']
manifest = []

def expanded(caller, callee):
    return f'apply_{len(caller)}_{caller}_{callee}'

def policy(family, suite):
    if family == 'nested':
        draws = [[expanded(expanded('segment', step), site) for site in ('draw_challenge', 'challenge')]
                 for step in ('first', 'second')]
        return ['zkc.native-proof-policy/4', 'main', 'P', 'V', '0', suite, '5', ['0', '1', '3'], draws]
    return ['zkc.native-proof-policy/4', 'main', 'P', 'V', '0', suite, '4', ['1', '2', '3'], [['draw', 'challenge']]]

for family, fixture in [('sumcheck', 'iterated-sumcheck'), ('cubic', 'cubic-sumcheck'), ('nested', 'nested-schnorr')]:
    source = (FIXTURES / (fixture + '.mlir')).read_text()
    for suite_index, suite in enumerate(SUITES):
        for suffix, options in [('', ()), ('_plain', ('--no-simplify',)), ('_release', ('--release-storage',)), ('_plain_release', ('--no-simplify', '--release-storage'))]:
            name = f'{family}_{suite_index}{suffix}'
            with case(name):
                src, pol = OUT / (name + '.mlir'), OUT / (name + '.policy')
                src.write_text(source); pol.write_text(json.dumps(policy(family, suite)))
                result = commands.run([compiler, 'protocol-proof', src, pol, *options])
                envelope = json.loads(result)
                assert envelope[0] == 'zkc.native-proof/4'
                assert envelope[1] == hashlib.sha256(source.encode()).hexdigest()
                assert json.loads(envelope[4])[0] == 'zkc.program/1'
                (OUT / (name + '.deployment')).write_text(result)
                manifest.append(dict(name=name, family=family))
                if not suffix and suite_index == 0:
                    large = OUT / (name + '.large.mlir')
                    large.write_text(source.replace('maximum=8:i64', 'maximum=100000:i64'))
                    other = json.loads(commands.run([compiler, 'protocol-proof', large, pol]))
                    assert len(other[4]) < len(envelope[4]) + 100

# Constant source counts exercise simplification without replacing explicit
# induction operands with a runtime-frame convention.
for n in (0, 1, 2):
    for suite_index, suite in enumerate(SUITES):
        name = f'constant_{n}_{suite_index}'
        with case(name):
            text = (FIXTURES / 'iterated-sumcheck.mlir').read_text()
            text = text.replace('   %count = protocol.exchange %n',
                                f'   %fixed = "data.index"() {{value="{n}"}} : ()->ui64\n   %count = protocol.exchange %fixed')
            text = text.replace('(%n,%T,%U)', '(%fixed,%T,%U)')
            src, pol = OUT / (name + '.mlir'), OUT / (name + '.policy')
            src.write_text(text); pol.write_text(json.dumps(policy('sumcheck', suite)))
            (OUT / (name + '.deployment')).write_text(commands.run([compiler, 'protocol-proof', src, pol]))
            manifest.append(dict(name=name, family='sumcheck', count=n))

# Public arrays use the same canonical native codec as round messages.
for suite_index, suite in enumerate(SUITES):
    name = f'public_array_{suite_index}'
    with case(name):
        text = (FIXTURES / 'iterated-sumcheck.mlir').read_text()
        text = text.replace('%claim:!f,%coins:!rng)', '%claim:!f,%coins:!rng,%config:!a)')
        text = text.replace('function_type=(ui64,!t,!t,!f,!rng)', 'function_type=(ui64,!t,!t,!f,!rng,!a)')
        text = text.replace('input_roles=[["P"],["P","V"],["P","V"],["V"],["V"]]',
                            'input_roles=[["P"],["P","V"],["P","V"],["V"],["V"],["P","V"]]')
        selected = policy('sumcheck', suite)
        selected[7].append('5')
        src, pol = OUT / (name + '.mlir'), OUT / (name + '.policy')
        src.write_text(text); pol.write_text(json.dumps(selected))
        (OUT / (name + '.deployment')).write_text(commands.run([compiler, 'protocol-proof', src, pol]))
        manifest.append(dict(name=name, family='sumcheck', count=2))

with case('distinct field-array shapes retain distinct transcript bindings'):
    def library(fixture, prefix):
        text = (FIXTURES / (fixture + '.mlir')).read_text()
        text = re.sub(r'!(f|t|p|a|q|state|rng)(?![A-Za-z0-9_.])', lambda m: '!' + prefix + m[1], text)
        text = re.sub(r'@([A-Za-z_][A-Za-z0-9_]*)', lambda m: '@' + prefix + m[1], text)
        text = re.sub(r'sym_name="([^"]+)"', lambda m: 'sym_name="' + prefix + m[1] + '"', text)
        text = re.sub(r'variant:([0-9a-f]+)', lambda m: 'variant:' + bytes.fromhex(m[1]).replace(b'poly.residual.product', ('poly.residual.' + prefix + 'product').encode()).hex(), text)
        aliases, body = text.split('module { "protocol.module"() ({', 1)
        return aliases, body.rsplit('}) {profile=', 1)[0]
    qa, qb = library('iterated-sumcheck', 'q_')
    ca, cb = library('cubic-sumcheck', 'c_')
    main = r'''"protocol.func"() ({ ^entry(%n:ui64,%T:!q_t,%U:!q_t,%q:!q_f,%c:!q_f,%coins:!q_rng):
      %quadratic:3 = "protocol.apply"(%n,%T,%U,%q,%coins) {callee=@q_main,roles=["P","V"],site="quadratic"} : (ui64,!q_t,!q_t,!q_f,!q_rng)->(i1,!q_p,!q_f)
      %cubic:3 = "protocol.apply"(%n,%T,%U,%c,%coins) {callee=@c_main,roles=["P","V"],site="cubic"} : (ui64,!q_t,!q_t,!q_f,!q_rng)->(i1,!q_p,!q_f)
      %ok = arith.andi %quadratic#0, %cubic#0 : i1
      "protocol.return"(%ok) : (i1)->()
    }) {sym_name="main",function_type=(ui64,!q_t,!q_t,!q_f,!q_f,!q_rng)->i1,roles=["P","V"],input_roles=[["P"],["P","V"],["P","V"],["V"],["V"],["V"]],output_roles=[["V"]]} : ()->()'''
    source = qa + ca + 'module { "protocol.module"() ({' + qb + cb + main + '}) {profile=#protocol.profile<protocol>} : ()->() }'
    src = OUT / 'mixed_shapes.mlir'; src.write_text(source)
    p = ['zkc.native-proof-policy/4','main','P','V','0',SUITES[0],'5',['1','2','3','4'],
         [[expanded(call,site) for site in ('draw','challenge')] for call in ('quadratic','cubic')]]
    pol = OUT / 'mixed_shapes.policy'; pol.write_text(json.dumps(p))
    result = json.loads(commands.run([compiler,'protocol-proof',src,pol]))
    bindings = json.loads(result[4])[1]
    arrays = [b for b in bindings if 'transcript.native.indexed.observe.data' in b and b[2][-1].startswith('field_array<')]
    assert len(arrays) == 2, arrays
    assert {b[2][-1] for b in arrays} == {'field_array<bls12-381.fr,3>', 'field_array<bls12-381.fr,4>'}, arrays

with case('iterated source correspondence checks real control operands'):
    src, pol = OUT / 'sumcheck_0.mlir', OUT / 'sumcheck_0.policy'
    original = commands.run([compiler, 'protocol-construct-proof', src, pol])
    candidate = OUT / 'constructed.mlir'
    candidate.write_text(original)
    commands.run([compiler, 'protocol-check-proof', src, pol, candidate])
    # The verifier's received count and table-derived count are both ui64.
    # Replacing the actual loop operand is well typed but changes correspondence.
    changed, count = re.subn(r'("protocol.loop"\()(%0)(, %4, %arg2, %1)', r'\1%2\3', original)
    assert count == 1
    candidate.write_text(changed)
    commands.run([compiler, 'protocol-check-proof', src, pol, candidate], refuses='native-proof-correspondence')
    # Retired construction metadata cannot authorize current helpers.
    assert 'zkc.native-construction/4' in original
    for tag in ('1', '2', '3', '5', 'unknown'):
        candidate.write_text(original.replace('zkc.native-construction/4', 'zkc.native-construction/' + tag))
        commands.run([compiler, 'protocol-check-proof', src, pol, candidate], refuses='native-proof-candidate')
    # Updating both the action metadata and loop bounds cannot authorize a
    # different source maximum.
    candidate.write_text(original.replace('maximum = 8 : i64', 'maximum = 9 : i64'))
    commands.run([compiler, 'protocol-check-proof', src, pol, candidate], refuses='native-proof-correspondence')

with case('nested source correspondence retains actual coordinate operands'):
    src, pol = OUT / 'nested_0.mlir', OUT / 'nested_0.policy'
    original = commands.run([compiler, 'protocol-construct-proof', src, pol])
    candidate = OUT / 'nested_constructed.mlir'
    candidate.write_text(original)
    commands.run([compiler, 'protocol-check-proof', src, pol, candidate])
    # Find a helper call with distinct outer and inner induction arguments.
    # Both substitutions remain well typed and preserve helper/action metadata.
    calls = re.finditer(
        r'(local\.call @_transcript_\d+\([^\n()]*, )(%arg\d+), (%arg\d+)(\) \{site = )',
        original,
    )
    call = next(m for m in calls if m[2] != m[3])
    for name, coordinates in [('swapped', (call[3], call[2])),
                              ('repeated', (call[3], call[3]))]:
        changed = call[1] + ', '.join(coordinates) + call[4]
        candidate = OUT / ('nested_' + name + '.mlir')
        candidate.write_text(original[:call.start()] + changed + original[call.end():])
        commands.run([compiler, 'protocol-check-proof', src, pol, candidate],
                     refuses='native-proof-correspondence')

with case('retired policy refuses loop source before preparation'):
    source = OUT / 'sumcheck_0.mlir'
    p = policy('sumcheck', SUITES[0]); p[0] = 'zkc.native-proof-policy/1'
    pol = OUT / 'flat.policy'; pol.write_text(json.dumps(p))
    commands.run([compiler, 'protocol-proof', source, pol], refuses='native-proof-policy')
with case('cross-block draw delivery is not admitted'):
    text = (FIXTURES / 'iterated-sumcheck.mlir').read_text()
    # A draw before a loop may not be delivered by its body.
    text = text.replace('   %done:3 =', '   %early = "protocol.query"(%coins) {method="draw",owner="V",site="early"} : (!rng)->!f\n   %done:3 =')
    src = OUT / 'prefix.mlir'; src.write_text(text)
    p = policy('sumcheck', SUITES[0]); p[8].insert(0, ['early', 'unused'])
    pol = OUT / 'prefix.policy'; pol.write_text(json.dumps(p))
    commands.run([compiler, 'protocol-proof', src, pol], refuses='native-proof-loop-prefix')

(OUT / 'manifest.json').write_text(json.dumps(manifest))
counted()
