"""Retained protocol calls, independent contextual SSA, and effective sites."""
import hashlib
import json
from pathlib import Path

from cases import case, counted
from commands import Commands
from entry_artifacts import compile_run_package
from tools import compiler, records

commands = Commands(records())
root = Path(__file__).resolve().parents[2]
reference = Path(compiler).parent / 'test/zkc-structured_reference-test'
field = ['field', 'bls12-381.fr']
service = 'random.bls12-381.fr/0'
serial = 0
# Frontend role identities are positional native names, separate from the DSL
# labels in language-interface. Handwritten MLIR controls use explicit names.
first_role, second_role = 'role00000000', 'role00000001'


def export(source, symbol='main', refusal=None, keep=None):
    text = commands.source('protocol-structured', source, '--symbol=' + symbol,
                           refuses=refusal, keep=keep)
    return None if refusal else json.loads(text)


def run(source, inputs, role='P', replies=(), symbol='main', refusal=None, capacity=1000000):
    global serial
    serial += 1
    path = commands.directory / f'application-{serial}.mlir'
    path.write_text(source)
    request = commands.write(f'application-{serial}.json',
                             ['zkc.structured-open-request/0', role, inputs, list(replies), capacity])
    text = commands.run([reference, 'open', path, symbol, request], refuses=refusal,
                        keep=f'application-{serial}-result.json')
    return None if refusal else json.loads(text)


def reply(action, value=None, stop=None):
    return ['reply', action, ['stop', stop] if stop else
            ['unit'] if action[0] == 'send' else ['value', value]]


def trace(replies):
    return [event for i, row in enumerate(replies)
            for event in [['request', i, row[1]], ['reply', i, row[2]]]]


def returned(values, replies=()):
    return ['zkc.structured-open-result/0', ['returned', values], trace(replies), len(replies)]


def stopped(reason, site, replies=(), extra=()):
    return ['zkc.structured-open-result/0', ['stopped', reason, site],
            trace(replies) + list(extra) + [['stop', reason, site, len(replies)]], len(replies)]


def frontend(path):
    flags = ['--source-format=zkc', '--entry=sample::Demo', f'--module=sample={path}']
    child = compile_run_package(commands, *flags)
    source = child['original']
    interface = json.loads(child['interface'])
    (commands.directory / (path.stem + '.mlir')).write_text(source)
    (commands.directory / (path.stem + '-interface.json')).write_text(child['interface'])
    return source, interface['protocol']


def protocol(name, body='', roles=('P', 'Q'), inputs=(('go', 'i1', ('P', 'Q')),),
             outputs=(), returns=()):
    ins = ','.join(t for _, t, _ in inputs)
    outs = ','.join(t for t, _ in outputs)
    args = ','.join(f'%{n}:{t}' for n, t, _ in inputs)
    arguments = f'^entry({args}):' if inputs else ''
    return f'''"protocol.func"() ({{ {arguments}
      {body}
      "protocol.return"({','.join(returns)}) : ({outs})->()
    }}) {{sym_name="{name}",origin=["{name}",[]],function_type=({ins})->({outs}),roles={json.dumps(roles)},
      input_roles={json.dumps([scope for _, _, scope in inputs])},
      output_roles={json.dumps([scope for _, scope in outputs])}}} : ()->()'''


def module(*definitions):
    return '''!F = !algebra.field<"bls12-381.fr">
!S = !protocol.service_ref<"random.bls12-381.fr/0">
module { "protocol.module"() ({
''' + '\n'.join(definitions) + '\n}) {profile=#protocol.profile<protocol>} : ()->() }'


def apply(callee='child', site='A', roles=('P', 'Q'), args='%go', inputs='i1', outputs='', result=''):
    return f'''{result}"protocol.apply"({args}) {{callee=@{callee},roles={json.dumps(roles)},
        site="{site}"}} : ({inputs})->({outputs})'''


def guard(site='C', owner='P', argument='%go'):
    return f'"protocol.guard"({argument}) {{owner="{owner}",site="{site}"}} : (i1)->()'


def refuse(source, native, exported=None, observed=None):
    export(source, refusal=exported or native)
    run(source, [], refusal=observed or 'structured-reference-source')


with case('whole-unchanged-application-and-independent-participant-inputs'):
    source, symbol = frontend(root / 'compiler/test/fixtures/language/application.zkc')
    snapshot = export(source, symbol)
    assert snapshot[2] == 'sha256:' + hashlib.sha256(source.encode()).hexdigest()
    assert len(snapshot) == 11 and len(snapshot[7]) == 4
    calls = [instruction for definition in snapshot[7] for instruction in definition[9][1]
             if instruction[0][0] == 'protocol_apply']
    assert len(calls) == 3
    assert all(len(c[0]) == 3 and c[3] == [] and c[4] for c in calls)
    assert any(c[0][2] == [second_role, first_role] for c in calls)
    assert any(c[1] == [] and c[2] == [] for c in calls)
    assert run(source, ['2', '3'], first_role, symbol=symbol) == returned(['6', None])
    assert run(source, ['5', '7'], second_role, symbol=symbol) == returned([None, '12'])


service_source, service_symbol = frontend(root / 'compiler/test/fixtures/language/service_order.zkc')
with case('whole-service-order-actual-received-value'):
    export(service_source, service_symbol)
    action = ['receive', 'apply_2_s3_s5_0', second_role, first_role, field]
    replies = [reply(action, '19')]
    assert run(service_source, [None, None, None], first_role, replies, service_symbol) == returned(['19', None], replies)


for alias in (True, False):
    with case(f'service-handles-and-ordered-residual-state-{alias}'):
        # Independent two-provider state: the original SSA reference only
        # consumes these exact requests; it does not simulate fresh providers.
        counts = [0, 0]
        handles = [0, 0 if alias else 1]
        replies = []
        draws = []
        for site, handle in [('s0', handles[0]), ('apply_2_s3_s0', handles[0]),
                             ('apply_2_s3_s2', handles[1])]:
            counts[handle] += 1
            draws.append(counts[handle])
            replies.append(reply(['draw', site, second_role, service, str(handle), 'bls12-381.fr'], str(counts[handle])))
        value = draws[1] + draws[2]
        replies.append(reply(['send', 'apply_2_s3_s5_0', second_role, first_role, field, str(value)]))
        counts[0] += 1
        replies.append(reply(['draw', 's6', second_role, service, '0', 'bls12-381.fr'], str(counts[0])))
        expected = str(draws[0] + value + counts[0])
        assert run(service_source, [True, '0', str(handles[1])], second_role, replies,
                   service_symbol) == returned([None, expected], replies)
        assert counts == ([4, 0] if alias else [3, 1])


with case('callee-provider-stop-consumption-and-no-suffix'):
    first = reply(['draw', 's0', second_role, service, '0', 'bls12-381.fr'], '2')
    action = ['draw', 'apply_2_s3_s0', second_role, service, '0', 'bls12-381.fr']
    stop = reply(action, stop='abort')
    suffix = reply(['draw', 'never', second_role, service, '0', 'bls12-381.fr'], '99')
    assert run(service_source, [True, '0', '0'], second_role, [first, stop, suffix], service_symbol) == stopped(
        'abort', action[1], [first, stop])
    assert run(service_source, [True, '0', '0'], second_role, [first], service_symbol) == stopped(
        'incomplete', action[1], [first], [['request', 1, action]])
    assert run(service_source, [True, '0', '0'], second_role, [first, suffix], service_symbol) == stopped(
        'refused', action[1], [first], [['request', 1, action]])
    malformed = reply(action, 'not-a-field')
    assert run(service_source, [True, '0', '0'], second_role, [first, malformed], service_symbol) == stopped(
        'refused', action[1], [first], [['request', 1, action]])


with case('nested-wrapper-top-down-prefix-and-root-role-mapping'):
    source, symbol = frontend(root / 'compiler/test/fixtures/structured-source/application-wrapper.zkc')
    export(source, symbol)
    action = ['receive', 'apply_13_apply_2_s0_s3_s5_0', second_role, first_role, field]
    replies = [reply(action, '31')]
    assert run(source, [None, None, None], first_role, replies, symbol) == returned(['31', None], replies)
    action = ['draw', 'apply_2_s0_s0', second_role, service, '8', 'bls12-381.fr']
    replies = [reply(action, '7')]
    assert run(source, [False, '8', '8'], second_role, replies, symbol) == stopped(
        'reject', 'apply_2_s0_s2', replies)


helper_return = '''%result = "exec.returned"(%x) : (!F)->!exec.outcome<(!F)>
  func.return %result : !exec.outcome<(!F)>'''


def helper_stop(site):
    return f'''%stop = "exec.reject"(%scope) {{reason="abort",site="{site}"}} : (!runtime.scope)->!exec.stop
  cf.br ^stopped(%stop : !exec.stop)
^stopped(%reason:!exec.stop):
  %failure = "exec.failed"(%reason) : (!exec.stop)->!exec.outcome<(!F)>
  func.return %failure : !exec.outcome<(!F)>'''


helper = '''func.func @work(%scope:!runtime.scope,%x:!F,%unused:!F)->!exec.outcome<(!F)> attributes {no_inline,runtime.origin=["work",[]]} {
''' + helper_return + '\n}'
ports = (('x', '!F', ('P',)), ('unused', '!F', ('P',)))
child = protocol('child', '%v = "protocol.local_call"(%x,%unused) {callee=@work,role="P",site="work"} : (!F,!F)->!F',
                 inputs=ports, outputs=(('!F', ('P',)),), returns=('%v',))
parent = protocol('main', apply(args='%x,%unused', inputs='!F,!F', outputs='!F', result='%v = '),
                  inputs=ports, outputs=(('!F', ('P',)),), returns=('%v',))
local_source = module(helper, child, parent)
with case('missing-unused-local-input-qualified-call-stop'):
    snapshot = export(local_source)
    main = next(row for row in snapshot[7] if row[1] == 'main')
    assert main[9] == ['block', [
        [['protocol_apply', 'child', ['P', 'Q']], [0, 1], [['apply', 'field', [['domain', 'Field', 'bls12-381.fr']]]], [], 'A']
    ], ['return', [0]]]
    assert run(local_source, ['7', None]) == stopped('incomplete', 'apply_1_A_work')
    assert run(local_source, ['7', '8']) == returned(['7'])
    assert run(local_source, [None, None], 'Q') == returned([None])


with case('helper-body-stop-remains-unqualified'):
    source = local_source.replace(helper_return, helper_stop('helper_stop'))
    export(source)
    assert run(source, ['7', '8']) == stopped('abort', 'helper_stop')
    assert run(source.replace('site="A"', 'site="B"'), ['7', '8']) == stopped('abort', 'helper_stop')
    assert run(source, ['7', None]) == stopped('incomplete', 'apply_1_A_work')


with case('protocol-optional-projection-is-not-strict-local-entry'):
    source = module(protocol('child', inputs=ports, outputs=(('!F', ('P',)),), returns=('%x',)), parent)
    export(source)
    assert run(source, ['7', None]) == returned(['7'])


pure = '''func.func private @identity(%x:!F)->!F { func.return %x : !F }'''
stopping = '''func.func @stop(%scope:!runtime.scope)->!exec.outcome<> attributes {no_inline,runtime.origin=["stop",[]]} {
  %stop = "exec.reject"(%scope) {reason="abort",site="helper_stop"} : (!runtime.scope)->!exec.stop
  cf.br ^stopped(%stop : !exec.stop)
^stopped(%reason:!exec.stop):
  %failure = "exec.failed"(%reason) : (!exec.stop)->!exec.outcome<>
  func.return %failure : !exec.outcome<>
}'''
subset = module(pure, stopping,
    protocol('child', '''%one = "algebra.constant"() {value=#algebra.literal<!F, 1 : ui255>} : ()->!F
      %v = func.call @identity(%one) : (!F)->!F
      "protocol.local_call"() {callee=@stop,role="A",site="stop"} : ()->()''',
             roles=('A',), inputs=()),
    protocol('main', apply(roles=('P',), args='', inputs='') + '''
      %answer = "algebra.constant"() {value=#algebra.literal<!F, 7 : ui255>} : ()->!F''', inputs=(),
             outputs=(('!F', ('Q',)),), returns=('%answer',)))
with case('outside-roster-zero-result-child-and-native-projection'):
    snapshot = export(subset)
    assert all(instruction[4] == '' for definition in snapshot[7]
               for instruction in definition[9][1]
               if instruction[0][0] in ('field.constant', 'call'))
    assert run(subset, [], 'Q') == returned(['7'])
    assert run(subset, [], 'P') == stopped('abort', 'helper_stop')
    projected = commands.verified(subset, None, '--zkc-project-protocol', '--zkc-lower-math')
    (commands.directory / 'outside-roster-projected.mlir').write_text(projected)
    # The actual Q participant has no child-owned Local call or guard. Inspect
    # its exported participant operations, not a hand-expanded expected program.
    physical = commands.verified(projected, None, '--zkc-select-physical')
    participants = json.loads(commands.source('protocol-export', physical))
    (commands.directory / 'outside-roster-projected.json').write_text(json.dumps(participants, indent=2))
    outsider = next(p for p in participants[3] if p[2:4] == ['main', 'Q'])
    owner = next(p for p in participants[3] if p[2:4] == ['main', 'P'])
    assert not any(op[0] == 'local' and op[2] == 'stop' for op in outsider[6])
    assert owner[6] == [['local', 'apply_1_A_stop', 'stop', [], []], ['return', []]]
    assert 'identity' not in json.dumps(outsider)
    # Lowering also emits the outsider's own constant as a Local calculation.
    # Its only reachable helper returns 7, with no child constant 1 or stop.
    [calculation, result] = outsider[6]
    assert calculation[0] == 'local' and result == ['return', calculation[4]]
    function = next(f for f in participants[2] if f[1] == calculation[2])
    [constant, result] = function[4]
    assert constant[0] == 'op' and constant[3:5] == [['7'], []]
    assert next(b for b in participants[1] if b[0] == constant[2])[1] == 'field.constant'
    assert result == ['return', constant[5]]


finite_source = (root / 'compiler/test/fixtures/finite/total-state.mlir').read_text()
finite_operation = '"data.finite_fold"(%xs,%a,%b) {domain=@items,step=@step} : (!V,!F,!F)->(!F,!F)'
finite_wrapper = protocol('main', apply(roles=('P',), args='%xs,%a,%b',
    inputs='!V,!F,!F', outputs='!F,!F', result='%r:2 = '),
    inputs=(('xs', '!V', ('P',)), ('a', '!F', ('P',)), ('b', '!F', ('P',)),
            ('outside', '!F', ('Q',))),
    outputs=(('!F', ('P',)), ('!F', ('P',)), ('!F', ('Q',))),
    returns=('%r#0', '%r#1', '%outside'))
for indirect in (False, True):
    with case(f'single-role-math-fold-in-multi-role-application-indirect-{indirect}'):
        source = finite_source
        if indirect:
            source = source.replace(finite_operation,
                'func.call @fold_helper(%xs,%a,%b) : (!V,!F,!F)->(!F,!F)')
            helper = f'''func.func private @fold_helper(%xs:!V,%a:!F,%b:!F)->(!F,!F) {{
              %r:2 = {finite_operation}
              func.return %r#0,%r#1 : !F,!F
            }}'''
            source = source.replace(' "protocol.func"() ({', helper + '\n "protocol.func"() ({', 1)
        source = source.replace('sym_name="main",origin=["main",[]]', 'sym_name="child",origin=["child",[]]').replace('["P"]', '["A"]')
        source = source.replace('}) {profile=', finite_wrapper + '\n}) {profile=', 1)
        label = 'single-role-math-' + ('helper' if indirect else 'direct')
        (commands.directory / (label + '.mlir')).write_text(source)
        snapshot = export(source, keep=label + '.snapshot.json')
        assert snapshot[2] == 'sha256:' + hashlib.sha256(source.encode()).hexdigest()
        definitions = {row[1]: row for row in snapshot[7]}
        assert definitions['child'][6][1] == ['A']
        assert definitions['main'][6][1] == ['P', 'Q']
        assert definitions['main'][9][1][0][0] == ['protocol_apply', 'child', ['P']]
        # The existing indexed callback updates (a,b) to (b,xs[i]). These
        # literal answers are independent of native expansion or projection.
        observations = [
            ('owner-three-elements', 'P', [['3', '5', '7'], '1', '2', None],
             returned(['5', '7', None])),
            ('owner-empty', 'P', [[], '1', '2', None], returned(['1', '2', None])),
            ('outsider', 'Q', [None, None, None, '41'], returned([None, None, '41'])),
        ]
        for _, role, inputs, expected in observations:
            assert run(source, inputs, role) == expected
        # The outsider finishes without entering the child's block, domain or
        # callback. The valid owner computation can exhaust observer work;
        # this is capacity evidence, not an out-of-bounds Math stop.
        assert run(source, [None, None, None, '41'], 'Q', capacity=5) == returned([None, None, '41'])
        run(source, [None, None, None, '41'], 'Q', capacity=4,
            refusal='structured-reference-capacity')
        run(source, [['3', '5', '7'], '1', '2', None], capacity=20,
            refusal='structured-reference-capacity')
        # Both evaluation and helper argument copying spend observer fuel.
        # Their first exhausted category can differ across these two forms.
        (commands.directory / (label + '.expected.json')).write_text(json.dumps({
            'state_rule': '(a,b) -> (b,xs[i]); initial (1,2)',
            'observations': [dict(name=name, role=role, inputs=inputs, expected=expected)
                             for name, role, inputs, expected in observations],
            'outsider_capacity': 5,
            'owner_capacity_refusal': {'capacity': 20, 'diagnostic': 'structured-reference-capacity'},
        }, indent=2) + '\n')
        prepared = commands.verified(source, None, '--zkc-prepare-protocol')
        assert '"protocol.apply"' not in prepared
        (commands.directory / (label + '.prepared.mlir')).write_text(prepared)
        projected = commands.verified(prepared, None, '--zkc-project-protocol', '--zkc-lower-math')
        (commands.directory / (label + '.projected.mlir')).write_text(projected)
        physical = commands.verified(projected, None, '--zkc-select-physical')
        participants = json.loads(commands.source('protocol-export', physical,
                                                   keep=label + '.participants.json'))
        outsider = next(p for p in participants[3] if p[2:4] == ['main', 'Q'])
        # Its only input is its own suffix value. No child Math or Local
        # helper, finite work, checked read or effect remains at this endpoint.
        [outside_input] = outsider[4]
        assert outside_input[1] == 'field:bls12-381.fr@arkworks.fr/0'
        assert outsider[5:7] == [[outside_input[1]], [['return', [outside_input[0]]]]]


with case('partial-math-directly-in-two-role-protocol-is-refused'):
    source = finite_source.replace('roles=["P"]', 'roles=["P","Q"]', 1)
    (commands.directory / 'two-role-math-refused.mlir').write_text(source)
    commands.verified(source)
    export(source, refusal='structured-source-multirole-math')
    run(source, [[], '1', '2'], refusal='structured-reference-unsupported')


with case('input-and-output-boundary-masks'):
    one = (('x', '!F', ('A',)),)
    source = module(protocol('child', roles=('A', 'B'), inputs=one,
                             outputs=(('!F', ('A',)),), returns=('%x',)),
                    protocol('main', apply(roles=('Q', 'P'), args='%x', inputs='!F', outputs='!F', result='%y = '),
                             inputs=(('x', '!F', ('P', 'Q')),),
                             outputs=(('!F', ('Q',)),), returns=('%y',)))
    export(source)
    assert run(source, ['11'], 'P') == returned([None])
    assert run(source, ['17'], 'Q') == returned(['17'])


with case('permuted-actions-and-independent-received-value'):
    source = module(protocol('child', '''%got = "protocol.exchange"(%x)
      {sender="A",receiver="B",site="message"} : (!F)->!F''', roles=('A', 'B'),
      inputs=(('x', '!F', ('A',)),), outputs=(('!F', ('B',)),), returns=('%got',)),
      protocol('main', apply(roles=('Q', 'P'), args='%x', inputs='!F', outputs='!F', result='%y = '),
      inputs=(('x', '!F', ('Q',)),), outputs=(('!F', ('P',)),), returns=('%y',)))
    export(source)
    action = ['receive', 'apply_1_A_message', 'Q', 'P', field]
    replies = [reply(action, '29')]
    assert run(source, [None], 'P', replies) == returned(['29'], replies)
    action = ['send', 'apply_1_A_message', 'Q', 'P', field, '7']
    replies = [reply(action)]
    assert run(source, ['7'], 'Q', replies) == returned([None], replies)


with case('nested-permutations-compose-through-distinct-local-rosters'):
    source = module(protocol('leaf', '''%got = "protocol.exchange"(%x)
      {sender="L",receiver="R",site="C"} : (!F)->!F''', roles=('L', 'R'),
      inputs=(('x', '!F', ('L',)),), outputs=(('!F', ('R',)),), returns=('%got',)),
      protocol('middle', apply('leaf', 'B', ('B', 'A'), '%x', '!F', '!F', '%y = '),
        roles=('A', 'B'), inputs=(('x', '!F', ('B',)),),
        outputs=(('!F', ('A',)),), returns=('%y',)),
      protocol('main', apply('middle', 'A', ('Q', 'P'), '%x', '!F', '!F', '%y = '),
        inputs=(('x', '!F', ('P',)),), outputs=(('!F', ('Q',)),), returns=('%y',)))
    export(source)
    site = 'apply_11_apply_1_A_B_C'
    received = [reply(['receive', site, 'P', 'Q', field], '29')]
    sent = [reply(['send', site, 'P', 'Q', field, '7'])]
    assert run(source, [None], 'Q', received) == returned(['29'], received)
    assert run(source, ['7'], 'P', sent) == returned([None], sent)


with case('full-unused-input-availability-is-a-source-obligation'):
    source = module(protocol('child', inputs=ports),
      protocol('main', apply(args='%x,%unused', inputs='!F,!F'),
               inputs=(('x', '!F', ('P',)), ('unused', '!F', ('Q',)))))
    refuse(source, 'mathematical-formation')


with case('service-alias-origin-checked-in-unused-component'):
    source = module(protocol('child', inputs=(('left', '!S', ('P',)), ('right', '!S', ('Q',)))),
      protocol('main', inputs=()),
      protocol('dormant', apply(args='%handle,%handle', inputs='!S,!S'),
               inputs=(('handle', '!S', ('P',)),)))
    refuse(source, 'mathematical-formation')


with case('runtime-service-aliases-checked-before-participant-masking'):
    service_ports = (('left', '!S', ('P',)), ('right', '!S', ('Q',)))
    source = module(protocol('child', inputs=service_ports),
                    protocol('main', apply(args='%left,%right', inputs='!S,!S'), inputs=service_ports))
    export(source)
    assert run(source, ['1', '2']) == returned([])
    run(source, ['1', '1'], refusal='structured-reference-input')


with case('helper-stop-namespace-is-separate-from-protocol-sites'):
    source = local_source.replace(helper_return, helper_stop('apply_1_A_work'))
    export(source)
    assert run(source, ['7', '8']) == stopped('abort', 'apply_1_A_work')


plain = module(protocol('child', guard()), protocol('main', apply()))
with case('default-public-and-explicit-visibility-refusals'):
    export(plain)
    for visibility in ('public', 'private', 'nested'):
        refuse(plain.replace('sym_name="child"', f'sym_name="child",sym_visibility="{visibility}"'),
               'mathematical-formation')


for name, changed, code in [
    ('duplicate-role', plain.replace('roles=["P", "Q"],\n        site=', 'roles=["P", "P"],\n        site='), 'protocol-application'),
    ('foreign-role', plain.replace('roles=["P", "Q"],\n        site=', 'roles=["P", "R"],\n        site='), 'protocol-application'),
    ('missing-role', plain.replace('roles=["P", "Q"],\n        site=', 'roles=["P"],\n        site='), 'protocol-application'),
    ('unresolved', plain.replace('callee=@child', 'callee=@missing'), 'protocol-application'),
    ('missing-full-abi', plain.replace('"protocol.apply"(%go)', '"protocol.apply"()').replace('site="A"} : (i1)->()', 'site="A"} : ()->()'), 'protocol-application'),
    ('wrong-result', plain.replace('site="A"} : (i1)->()', 'site="A"} : (i1)->i1'), 'protocol-application'),
    ('extra-attribute', plain.replace('site="A"', 'site="A",extra="bad"'), 'mathematical-formation'),
]:
    with case('application-refuses-' + name):
        assert changed != plain
        refuse(changed, code)


with case('selected-root-is-not-a-distinct-callable-kind'):
    source = module(protocol('main', guard()), protocol('dormant', apply('main')))
    snapshot = export(source)
    assert snapshot[7][1][9][1][0][0] == ['protocol_apply', 'main', ['P', 'Q']]
    assert run(source, [True]) == returned([])


for name, body in [('cycle', apply('dormant')), ('missing', apply('missing')),
                   ('bad-owner', guard(owner='Missing'))]:
    with case('unused-component-' + name):
        source = module(protocol('main'), protocol('dormant', body))
        refuse(source, 'mathematical-formation' if name == 'bad-owner' else 'protocol-application')


with case('entry-statement-cannot-be-rebound-as-component'):
    text = (root / 'compiler/test/fixtures/mathematical/schnorr-services.mlir').read_text()
    definitions = text.split('"protocol.module"() ({', 1)[1].rsplit('}) {profile=', 1)[0]
    definitions = definitions.replace('sym_name="main"', 'sym_name="child"')
    group_type = '!algebra.group<"bls12-381.g1">'
    ports = (('g', group_type, ('Alice', 'Bob')), ('x', '!F', ('Alice',)),
             ('y', group_type, ('Alice', 'Bob')), ('nonce', '!S', ('Alice',)),
             ('challenge', '!S', ('Bob',)))
    wrapper = protocol('main', apply(roles=('Alice', 'Bob'), args='%g,%x,%y,%nonce,%challenge',
        inputs=','.join(port[1] for port in ports), outputs='i1', result='%ok = '),
        roles=('Alice', 'Bob'), inputs=ports, outputs=(('i1', ('Bob',)),), returns=('%ok',))
    refuse(module(definitions, wrapper), 'protocol-application')


for name, body in [
    ('completion', '"protocol.finish_if"(%go) {owner="P",site="finish"} : (i1)->()'),
    ('construction-start', '"protocol.construction_start"() {roles=["P","Q"],site="start"} : ()->()'),
]:
    with case('unused-unsupported-' + name):
        source = module(protocol('main'), protocol('dormant', body))
        commands.verified(source)
        refuse(source, None, 'structured-source-operation', 'structured-reference-unsupported')


with case('protocol-and-helper-targets-remain-distinct'):
    source = module(pure, protocol('main', apply('identity', args='%x', inputs='!F', outputs='!F', result='%v = '),
        inputs=(('x', '!F', ('P', 'Q')),)))
    refuse(source, 'protocol-application')


for owner in ('P', 'Q'):
    with case('authored-generated-site-collision-' + owner):
        source = module(protocol('child', guard()),
                        protocol('main', apply() + guard('apply_1_A_C', owner)))
        commands.verified(source)
        commands.verified(source, 'mathematical-formation', '--zkc-prepare-protocol')
        refuse(source, None, 'structured-source-site', 'structured-reference-site')


with case('shared-callee-checked-per-occurrence'):
    source = module(protocol('child', guard()), protocol('main',
                    apply(site='A') + apply(site='B') + guard('apply_1_B_C')))
    refuse(source, None, 'structured-source-site', 'structured-reference-site')


with case('effective-sites-share-one-set-across-operation-categories'):
    source = module(stopping, protocol('child', guard()), protocol('main', apply() +
      '"protocol.local_call"() {callee=@stop,role="Q",site="apply_1_A_C"} : ()->()'))
    commands.verified(source)
    refuse(source, None, 'structured-source-site', 'structured-reference-site')


with case('unused-root-effective-collision'):
    source = module(protocol('main'), protocol('child', guard()),
                    protocol('dormant', apply() + guard('apply_1_A_C')))
    refuse(source, None, 'structured-source-site', 'structured-reference-site')


with case('harmless-prefix-and-erased-header-are-legal'):
    source = module(protocol('main', guard('apply_1_A_C')))
    export(source)
    assert run(source, [False]) == stopped('reject', 'apply_1_A_C')
    source = module(protocol('child', guard()), protocol('empty'),
                    protocol('main', apply() + apply('empty', 'apply_1_A_C')))
    export(source)
    assert run(source, [True]) == returned([])


with case('nested-empty-call-header-does-not-claim-effective-site'):
    source = module(protocol('empty'), protocol('child', apply('empty', 'B')),
                    protocol('main', apply() + guard('apply_1_A_B')))
    export(source)
    assert run(source, [False]) == stopped('reject', 'apply_1_A_B')


with case('generated-and-stored-site-limits-differ'):
    source = module(protocol('child', guard('C' * 260)), protocol('main', apply(site='A' * 260)))
    export(source)
    assert run(source, [False]) == stopped('reject', 'apply_260_' + 'A' * 260 + '_' + 'C' * 260)
    source = module(protocol('main', guard('C' * 513)))
    refuse(source, None, 'structured-source-limit', 'structured-reference-capacity')


with case('site-free-exponential-dag-charged-before-expansion'):
    definitions = [protocol('leaf', inputs=())]
    previous = 'leaf'
    for i in range(16):
        name = f'branch{i}'
        definitions.append(protocol(name, apply(previous, 'left', args='', inputs='') +
                                    apply(previous, 'right', args='', inputs=''), inputs=()))
        previous = name
    definitions.append(protocol('main', inputs=()))
    refuse(module(*definitions), 'protocol-application')


with case('native-application-depth-counts-root-nodes'):
    for length in (64, 65):
        definitions = [protocol('leaf', inputs=())]
        previous = 'leaf'
        for i in range(length - 1):
            name = 'main' if i == length - 2 else f'chain{i}'
            definitions.append(protocol(name, apply(previous, 'A', args='', inputs=''), inputs=()))
            previous = name
        source = module(*definitions)
        if length == 64:
            export(source)
        else:
            refuse(source, 'protocol-application')


commands.save()
print(f'Structured applications: {counted()} cases; evidence: {commands.directory}')
