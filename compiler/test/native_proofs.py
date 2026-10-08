"""Source-checked native proof deployments; protocol clients share one pipeline."""
import hashlib
import json
from pathlib import Path
import re

from cases import case, counted
from commands import Commands
from tools import compiler, records

OUT = records()
commands = Commands(OUT)
FIXTURES = Path(__file__).parent / 'fixtures/mathematical'
SUITES = ['merlin3.bls12-381.fr64be/1', 'spongefish0.7.4.keccak.bls12-381.fr64be/1']
manifest = []
schnorr = (FIXTURES / 'schnorr-services.mlir').read_text()
field = '!algebra.field<"bls12-381.fr">'
service = '!protocol.service_ref<"random.bls12-381.fr/1">'


def compile_case(name, source, policy, family='schnorr', rounds=1, *options):
    source_path, policy_path = OUT / f'{name}.mlir', OUT / f'{name}.policy'
    source_path.write_text(source)
    policy_path.write_text(json.dumps(policy))
    deployment = commands.run([compiler, 'protocol-proof', source_path, policy_path, *options])
    (OUT / f'{name}.deployment').write_text(deployment)
    envelope = json.loads(deployment)
    assert envelope[0] == 'zkc.native-proof/4'
    assert envelope[1] == hashlib.sha256(source.encode()).hexdigest()
    assert envelope[2][1] == policy
    assert envelope[5] == hashlib.sha256(envelope[4].encode()).hexdigest()
    assert json.loads(envelope[4])[0] == 'zkc.program/1'
    manifest.append(dict(name=name, family=family, rounds=rounds))
    return source_path, policy_path


def policy(suite, public=None):
    return ['zkc.native-proof-policy/4', 'main', 'Alice', 'Bob', '0', suite,
            '4' if suite else '', public or ['0', '2'],
            [['draw_challenge', 'challenge']] if suite else []]


def with_pure_helpers(source):
    helpers = f'''func.func private @plus(%a: {field}, %b: {field}) -> {field} {{
  %r = algebra.field_add %a, %b : ({field}, {field}) -> {field}
  return %r : {field}
}}
func.func private @response(%a: {field}, %b: {field}) -> {field} {{
  %r = func.call @plus(%a, %b) : ({field}, {field}) -> {field}
  return %r : {field}
}}
'''
    return source.replace('relation.declare', helpers + 'relation.declare', 1).replace(
        f'%z = algebra.field_add %k, %cx : ({field}, {field}) -> {field}',
        f'%z = func.call @response(%k, %cx) : ({field}, {field}) -> {field}')


for i, suite in enumerate(SUITES):
    for name, fixture, public in [('schnorr', 'schnorr-services', ['0', '2']),
                                  ('dleq', 'dleq-services', ['0', '2', '5', '6']),
                                  ('affine', 'schnorr-affine', ['0', '2'])]:
        for suffix, options in [('', ()), ('_plain', ('--no-simplify',)),
                                ('_release', ('--release-storage',)),
                                ('_plain_release', ('--no-simplify', '--release-storage'))]:
            with case(f'{name} suite {i}{suffix}'):
                compile_case(f'{name}_{i}{suffix}', (FIXTURES / f'{fixture}.mlir').read_text(),
                             policy(suite, public), name, 1, *options)
    with case(f'pure mathematical helper expansion suite {i}'):
        compile_case(f'helpers_{i}', with_pure_helpers(schnorr), policy(suite))
    with case(f'reordered data services and selected result suite {i}'):
        arguments = re.search(r'\^entry\((.*)\):', schnorr)[1].split(', ')
        types = [a.split(': ', 1)[1] for a in arguments]
        owners = [['Alice', 'Bob'], ['Alice'], ['Alice', 'Bob'], ['Alice'], ['Bob']]
        source = schnorr.replace(', '.join(arguments), ', '.join(reversed(arguments)))
        source = source.replace('function_type=(' + ', '.join(types) + ')',
                                'function_type=(' + ', '.join(reversed(types)) + ')')
        source = re.sub(r'input_roles=\[.*?\], output_roles=',
                        'input_roles=' + json.dumps(list(reversed(owners))) + ', output_roles=', source)
        source = source.replace('acceptance=0 : i64', 'acceptance=1 : i64')
        source = source.replace('"protocol.return"(%ok) : (i1) -> ()',
                                '%no = arith.constant false\n"protocol.return"(%no, %ok) : (i1, i1) -> ()')
        source = source.replace(' -> (i1), roles=', ' -> (i1, i1), roles=')
        source = source.replace('output_roles=[["Bob"]]', 'output_roles=[["Bob"], ["Bob"]]')
        p = policy(suite, ['2', '4']); p[4] = '1'; p[6] = '0'
        compile_case(f'reordered_{i}', source, p)
        manifest[-1].update(value_ports=[4, 3, 2, 1, 0], nonce_port=1, challenge_port=0)
    with case(f'role entry and site renaming suite {i}'):
        renamed = schnorr.replace('Alice', 'Sender').replace('Bob', 'Checker').replace('sym_name="main"', 'sym_name="proof"')
        renamed = renamed.replace('site="commitment"', 'site="_transcript_0"')
        p = policy(suite)
        p[1:4] = ['proof', 'Sender', 'Checker']
        compile_case(f'renamed_{i}', renamed, p)
    with case(f'all verifier inputs including guard-only and unused suite {i}'):
        guarded = schnorr.replace(f'%challenge_service: {service}):', f'%challenge_service: {service}, %go: i1, %unused: i1):')
        guarded = guarded.replace(f', {service}) -> (i1)', f', {service}, i1, i1) -> (i1)')
        guarded = guarded.replace('["Alice"], ["Bob"]], output_roles', '["Alice"], ["Bob"], ["Bob"], ["Bob"]], output_roles')
        guarded = guarded.replace('%lhs =', 'protocol.guard %go {owner="Bob", site="before_decision"}\n%lhs =')
        compile_case(f'guarded_{i}', guarded, policy(suite, ['0', '2', '5', '6']))
    with case(f'two draws and post-final messages suite {i}'):
        start, end = schnorr.index('%k ='), schnorr.index('"protocol.return"')
        body = schnorr[start:end]
        variables = re.findall(r'^(%[A-Za-z_]+)(?= =)', body, re.M)
        second = re.sub(r'%[A-Za-z_]+', lambda m: m[0] + '_second' if m[0] in variables else m[0], body)
        second = re.sub(r'site="([^"]+)"', r'site="\1_second"', second)
        source = schnorr[:end] + second + '%accepted = arith.andi %ok, %ok_second : i1\n' + schnorr[end:].replace('"protocol.return"(%ok)', '"protocol.return"(%accepted)')
        p = policy(suite)
        p[8].append(['draw_challenge_second', 'challenge_second'])
        compile_case(f'two_rounds_{i}', source, p, rounds=2)
    with case(f'static application with renamed roles suite {i}'):
        child = schnorr.replace('sym_name="main"', 'sym_name="child"').replace('Alice', 'A').replace('Bob', 'B')
        child = '\n'.join(line for line in child.splitlines() if not line.startswith('protocol.statement'))
        statement = next(line for line in schnorr.splitlines() if line.startswith('protocol.statement'))
        signature = re.search(r'function_type=(.*?) -> \(i1\)', child)[1]
        arguments = schnorr[schnorr.index('^entry(')+7:schnorr.index('):\nprotocol.statement')]
        values = ', '.join(re.findall(r'(%\w+):', arguments))
        call = f'''"protocol.func"() ({{
^entry({arguments}):
{statement}
%ok = "protocol.apply"({values}) {{callee=@child, roles=["Alice","Bob"], site="invoke"}} : {signature} -> i1
"protocol.return"(%ok) : (i1) -> ()
}}) {{sym_name="main", function_type={signature} -> (i1), roles=["Alice", "Bob"], input_roles=[["Alice", "Bob"], ["Alice"], ["Alice", "Bob"], ["Alice"], ["Bob"]], output_roles=[["Bob"]]}} : () -> ()
'''
        source = child.replace('}) {profile=', call + '}) {profile=')
        p = policy(suite)
        p[8] = [['apply_6_invoke_draw_challenge', 'apply_6_invoke_challenge']]
        compile_case(f'applied_{i}', source, p)
        manifest[-1].update(origin_protocol='child', origin_path=['invoke'])
    with case(f'pure helpers inside static application suite {i}'):
        compile_case(f'applied_helpers_{i}', with_pure_helpers(source), p)
        manifest[-1].update(origin_protocol='child', origin_path=['invoke'])
    with case(f'nested static application suite {i}'):
        middle = call.replace(statement, '').replace('sym_name="main"', 'sym_name="middle"').replace('site="invoke"', 'site="inner"')
        outer = call.replace('callee=@child', 'callee=@middle')
        source = child.replace('}) {profile=', middle + outer + '}) {profile=')
        p = policy(suite)
        expanded = 'apply_6_invoke_inner'
        p[8] = [[f'apply_{len(expanded)}_{expanded}_draw_challenge', f'apply_{len(expanded)}_{expanded}_challenge']]
        compile_case(f'nested_{i}', source, p)
        manifest[-1].update(origin_protocol='child', origin_path=['invoke', 'inner'])
    with case(f'positional role swap application suite {i}'):
        swapped = child.replace('roles=["A", "B"], input_roles', 'roles=["B", "A"], input_roles')
        outer = call.replace('callee=@child, roles=["Alice","Bob"]', 'callee=@child, roles=["Bob","Alice"]')
        source = swapped.replace('}) {profile=', outer + '}) {profile=')
        p = policy(suite)
        p[8] = [['apply_6_invoke_draw_challenge', 'apply_6_invoke_challenge']]
        compile_case(f'swapped_{i}', source, p)
        manifest[-1].update(origin_protocol='child', origin_path=['invoke'])
    with case(f'Boolean message after the response suite {i}'):
        source = schnorr.replace('%lhs =', '%flag = arith.constant true\n%sent_flag = protocol.exchange %flag {sender="Alice", receiver="Bob", site="flag"} : i1\n%lhs =')
        compile_case(f'bool_{i}', source, policy(suite))
        manifest[-1]['bool_message'] = True

with case('affine producer with additional service authority'):
    source = (FIXTURES / 'schnorr-affine.mlir').read_text()
    source = source.replace(f'%challenge_service: {service}):', f'%challenge_service: {service}, %extra: {service}):')
    source = source.replace(f', {service}) -> (i1)', f', {service}, {service}) -> (i1)')
    source = source.replace('["Alice"], ["Bob"]], output_roles', '["Alice"], ["Bob"], ["Alice"]], output_roles')
    compile_case('affine_setup', source, policy(SUITES[0]), 'affine')


with case('authored fixed public challenge no transcript control'):
    authored = schnorr.replace(f'%challenge_service: {service}', f'%c: {field}')
    authored = authored.replace(f', {service}) -> (i1)', f', {field}) -> (i1)')
    authored = '\n'.join(line for line in authored.splitlines() if not line.startswith('%c =') and not line.startswith('%challenge ='))
    authored = re.sub(r'%challenge\b', '%c', authored)
    authored = authored.replace('["Alice"], ["Bob"]], output_roles', '["Alice"], ["Alice", "Bob"]], output_roles')
    authored = authored.replace('"protocol.return"', 'protocol.guard %ok {owner="Bob", site="decision"}\n"protocol.return"')
    compile_case('authored', authored, policy('', ['0', '2', '4']))

with case('source-relative actual candidate checking'):
    source_path, policy_path = OUT / 'schnorr_0.mlir', OUT / 'schnorr_0.policy'
    candidate = commands.run([compiler, 'protocol-construct-proof', source_path, policy_path])
    candidate_path = OUT / 'candidate.mlir'
    candidate_path.write_text(candidate)
    commands.run([compiler, 'protocol-check-proof', source_path, policy_path, candidate_path])
    # A well-typed arithmetic mutation must fail full SSA correspondence.
    changed, count = re.subn(r'(algebra.field_add )(%\w+), (%\w+)', r'\1\3, \3', candidate, count=1)
    assert count == 1
    candidate_path.write_text(changed)
    commands.run([compiler, 'protocol-check-proof', source_path, policy_path, candidate_path], refuses='native-proof-correspondence')

with case('constructed transcript helpers have a closed body and one use per role'):
    # These mutations preserve ordinary types and action occurrences. The
    # construction record must also constrain inserted helper bodies and reuse.
    extra, count = re.subn(r'(?m)^(      return %)',
                           r'      %unused = "local.bool_constant"() {value = true, site = "unused"} : () -> i1\n\1', candidate, count=1)
    assert count == 1
    commands.verified(extra, 'mathematical-projection: invalid inserted transcript helper')
    # The two scalar-observation helpers have identical callable signatures.
    helpers = re.findall(r'local.func @(_transcript_\d+)\(%arg0: [^\n]+, %arg1: !algebra.field<"bls12-381.fr">\)', candidate)
    assert len(helpers) == 2, helpers
    repeated = candidate.replace(f'callee = @{helpers[1]}', f'callee = @{helpers[0]}').replace(
        f'local.call @{helpers[1]}', f'local.call @{helpers[0]}')
    assert repeated != candidate
    commands.verified(repeated, 'mathematical-projection: repeated inserted transcript helper')

with case('retained action cannot disguise an extra inserted helper call'):
    absorb = re.search(r'(?m)^      (%\w+) = local.call @(_transcript_\d+)\((%\w+), (%\w+)\) \{site = "([^\"]+)"\}( : [^\n]+)', candidate)
    assert absorb
    state, helper, _, payload, site, signature = absorb.groups()
    challenge = re.search(r'(?m)^      %\w+:2 = local.call @_transcript_\d+\(' + re.escape(state) + r'\)[^\n]+', candidate)
    assert challenge
    inserted_call = f'      %extra_state = local.call @{helper}({state}, {payload}) {{site = "authored_extra"}}{signature}\n'
    forged = candidate.replace(challenge[0], inserted_call + challenge[0].replace(f'({state})', '(%extra_state)'), 1)
    participant = re.search(r'"protocol.participant"[^\n]+sym_name = "([^\"]+)"', candidate)[1]
    extra = f'{{callee = @{helper}, kind = "protocol.local_call", site = "authored_extra", targets = [{{operation = "local.call", participant = @{participant}}}]}}'
    original_next = '{kind = "protocol.query", site = "draw_challenge",'
    assert original_next in forged
    forged = forged.replace(original_next, extra + ', ' + original_next, 1)
    inserted = f'{{callee = @{helper}, kind = "protocol.local_call", site = "{site}", targets = [{{operation = "local.call", participant = @{participant}}}]}}'
    assert inserted in forged
    forged = forged.replace(inserted, inserted + ', ' + extra, 1)
    commands.verified(forged, 'mathematical-projection: inserted transcript helper used by retained action')

with case('private verifier witness and omitted public input refuse before simplification'):
    source_path, policy_path = OUT / 'bad.mlir', OUT / 'bad.policy'
    source_path.write_text(schnorr)
    p = policy(SUITES[0]); p[7] = ['0']
    policy_path.write_text(json.dumps(p))
    commands.run([compiler, 'protocol-proof', source_path, policy_path], refuses='native-proof-public-bindings')
    p = policy(SUITES[0]); policy_path.write_text(json.dumps(p))
    private = schnorr.replace('purposes=["parameter", "statement", "witness"]', 'purposes=["witness", "statement", "witness"]')
    source_path.write_text(private)
    commands.run([compiler, 'protocol-proof', source_path, policy_path], refuses='native-proof-private-verifier-witness')

with case('producer-selected witness shared with validator still refuses'):
    shared = schnorr.replace('[["Alice", "Bob"], ["Alice"],',
                             '[["Alice", "Bob"], ["Alice", "Bob"],')
    commands.verified(shared, None)
    source_path.write_text(shared)
    p = policy(SUITES[0], ['0', '1', '2'])
    policy_path.write_text(json.dumps(p))
    commands.run([compiler, 'protocol-proof', source_path, policy_path],
                 refuses='native-proof-private-verifier-witness')
    policy_path.write_text(json.dumps(policy(SUITES[0])))

with case('expanded source occurrence collision has an origin diagnostic'):
    collision = call.replace('"protocol.return"(%ok)', '%extra = protocol.exchange %g {sender="Alice", receiver="Bob", site="apply_6_invoke_commitment"} : !algebra.group<"bls12-381.g1">\n"protocol.return"(%ok)')
    source_path.write_text(child.replace('}) {profile=', collision + '}) {profile='))
    commands.verified(source_path.read_text(), None)
    commands.run([compiler, 'protocol-proof', source_path, policy_path], refuses='native-proof-origin')

with case('recursive pure helpers remain outside admitted source'):
    source_path.write_text(with_pure_helpers(schnorr).replace('func.call @plus', 'func.call @response'))
    commands.run([compiler, 'protocol-proof', source_path, policy_path], refuses='mathematical-formation')

with case('an unused verifier draw cannot disappear'):
    source_path.write_text(schnorr.replace('%lhs =', f'%unused_coin = "protocol.query"(%challenge_service) {{method="draw", owner="Bob", site="unused_draw"}} : ({service}) -> {field}\n%lhs ='))
    commands.run([compiler, 'protocol-proof', source_path, policy_path], refuses='native-proof-draw-selection')
with case('derived challenge delivery refuses'):
    source_path.write_text(schnorr.replace('%challenge =', f'%derived = algebra.field_add %c, %c : ({field}, {field}) -> {field}\n%challenge =').replace('protocol.exchange %c ', 'protocol.exchange %derived '))
    commands.run([compiler, 'protocol-proof', source_path, policy_path], refuses='native-proof-reverse-message')

with case('extra roles remain interactive and refuse the selected proof profile'):
    source_path.write_text(schnorr.replace('roles=["Alice", "Bob"], input_roles', 'roles=["Alice", "Bob", "Observer"], input_roles'))
    commands.verified(source_path.read_text(), None)
    commands.run([compiler, 'protocol-proof', source_path, policy_path], refuses='native-proof-interface')
with case('draw and delivery cannot enclose another message'):
    source_path.write_text(schnorr.replace('%challenge =', '%intervening = protocol.exchange %r {sender="Alice", receiver="Bob", site="intervening"} : !algebra.group<"bls12-381.g1">\n%challenge ='))
    commands.verified(source_path.read_text(), None)
    commands.run([compiler, 'protocol-proof', source_path, policy_path], refuses='native-proof-prefix')
with case('unused validator services are not ambient inputs'):
    added = schnorr.replace(f'%challenge_service: {service}):', f'%challenge_service: {service}, %other: {service}):')
    added = added.replace(f', {service}) -> (i1)', f', {service}, {service}) -> (i1)')
    added = added.replace('["Alice"], ["Bob"]], output_roles', '["Alice"], ["Bob"], ["Bob"]], output_roles')
    source_path.write_text(added)
    commands.verified(added, None)
    commands.run([compiler, 'protocol-proof', source_path, policy_path], refuses='native-proof-verifier-service')
with case('all unsigned public data must be bound'):
    added = schnorr.replace(f'%challenge_service: {service}):', f'%challenge_service: {service}, %n: ui64):')
    added = added.replace(f', {service}) -> (i1)', f', {service}, ui64) -> (i1)')
    added = added.replace('["Alice"], ["Bob"]], output_roles', '["Alice"], ["Bob"], ["Bob"]], output_roles')
    source_path.write_text(added)
    commands.verified(added, None)
    commands.run([compiler, 'protocol-proof', source_path, policy_path], refuses='native-proof-public-bindings')
with case('retired and unknown policy tags refuse before source preparation'):
    source_path.write_text(schnorr)
    for tag in ('1', '2', '3', '0', '5', '99', 'unknown'):
        selected = policy(SUITES[0])
        selected[0] = 'zkc.native-proof-policy/' + tag
        policy_path.write_text(json.dumps(selected))
        commands.run([compiler, 'protocol-proof', source_path, policy_path], refuses='native-proof-policy')


(OUT / 'manifest.json').write_text(json.dumps(manifest))
counted()
