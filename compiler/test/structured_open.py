"""Whole-unit open export and independent original-SSA scripted execution."""
import copy
import json
from pathlib import Path

from cases import case, counted
from commands import Commands
from entry_artifacts import compile_run_package
from tools import compiler, records

commands = Commands(records())
repository_root = Path(__file__).resolve().parents[2]
fixtures = Path(__file__).parent / 'fixtures'
reference = Path(compiler).parent / 'test/zkc-structured_reference-test'
field = ['field', 'bls12-381.fr']
group = ['group', 'bls12-381.g1']
contract = 'random.bls12-381.fr/0'
modulus = 52435875175126190479447740508185965837690552500527637822603658699938581184513
serial = 0


def export(source, symbol='main', refusal=None, keep=None):
    text = commands.source('protocol-structured', source, '--symbol=' + symbol,
                           refuses=refusal, keep=keep)
    return None if refusal else json.loads(text)


def definitions(data):
    return {row[1]: row for row in data[7]}


def run(source, inputs, role='P', replies=(), symbol='main', capacity=1000000,
        refusal=None, closed=False, request=None):
    global serial
    serial += 1
    path = commands.directory / f'source-{serial}.mlir'
    path.write_text(source)
    if request is None:
        request = inputs if closed else ['zkc.structured-open-request/0', role, inputs, list(replies), capacity]
    request_path = commands.write(f'request-{serial}.json', request)
    request_path.write_text(json.dumps(request, separators=(',', ':')) + '\n')
    text = commands.run([reference, *([] if closed else ['open']), path, symbol, request_path],
                        refuses=refusal, keep=f'result-{serial}.json')
    return None if refusal else json.loads(text)


def reply(action, value=None, stop=None):
    response = ['stop', stop] if stop else ['unit'] if action[0] == 'send' else ['value', value]
    return ['reply', action, response]


def returned(values, records=(), position=0):
    return ['zkc.structured-open-result/0', ['returned', values], list(records), position]


def trace(replies):
    return [event for i, row in enumerate(replies)
            for event in [['request', i, row[1]], ['reply', i, row[2]]]]


def frontend(entry, modules, *, proof=False):
    retained = entry.replace('::', '-')
    flags = ['--source-format=zkc', '--entry=' + entry,
             *[f'--module={name}={path}' for name, path in modules.items()]]
    if proof:
        source = commands.run([compiler, 'language-emit', *flags], keep=retained + '.mlir')
        interface = json.loads(commands.run([compiler, 'language-interface', *flags], keep=retained + '-interface.json'))
    else:
        child = compile_run_package(commands, *flags)
        source = child['original']
        interface = json.loads(child['interface'])
        (commands.directory / (retained + '.mlir')).write_text(source)
        (commands.directory / (retained + '-interface.json')).write_text(child['interface'])
    symbol = interface['protocol']
    return source, symbol, export(source, symbol, keep=retained + '-structured.json')


components = (fixtures / 'structured-source/open-components.mlir').read_text()
services = (fixtures / 'structured-source/open-services.mlir').read_text()
groups = (fixtures / 'structured-source/open-groups.mlir').read_text()
schnorr = (fixtures / 'mathematical/schnorr-services.mlir').read_text()
total = (fixtures / 'finite/total-state.mlir').read_text()
unit = (fixtures / 'finite/unit-state.mlir').read_text()

with case('disjoint-helper-results-and-independent-protocol-rosters'):
    data = export(components)
    defs = definitions(data)
    assert defs['main'][6] == ['protocol', ['P', 'V'], [['P'], ['V']],
                               [['P'], ['P'], ['V'], ['P', 'V']]]
    assert defs['other'][6] == ['protocol', ['Reader', 'Writer', 'Auditor'], [['Auditor']], [['Auditor']]]
    assert defs['nested'][6] == [] and len(defs['nested']) == 10
    assert run(components, ['11', '99']) == returned(['11', '11', None, '5'])
    assert run(components, ['88', '22'], 'V') == returned([None, None, '22', '5'])
    assert run(components, ['11', None]) == returned(['11', '11', None, '5'])
    assert run(components, ['37'], 'Auditor', symbol='other') == returned(['37'])
    assert definitions(export(components, 'other')) == defs
    run(components, ['1', '2'], 'Auditor', refusal='structured-reference-input')

with case('unused-disjoint-helper-intermediate-refused'):
    bad = components.replace('func.return %x : !F',
                             '%unused = algebra.field_add %x,%ignored : (!F,!F)->!F\nfunc.return %x : !F', 1)
    export(bad, refusal='mathematical-formation')
    run(bad, ['1', '2'], refusal='structured-reference-source')

with case('select-depends-on-condition-and-both-values'):
    selected = components.replace('%c = func.call @constant(%y) : (!F)->!F',
                                  '%c = arith.select %flag,%x,%x : !F')
    selected = selected.replace('^entry(%x:!F,%y:!F)', '^entry(%x:!F,%y:!F,%flag:i1)')
    selected = selected.replace('function_type=(!F,!F)->', 'function_type=(!F,!F,i1)->')
    selected = selected.replace('input_roles=[["P"],["V"]]', 'input_roles=[["P"],["V"],["P"]]')
    selected = selected.replace('output_roles=[["P"],["P"],["V"],["P","V"]]',
                                'output_roles=[["P"],["P"],["V"],["P"]]')
    export(selected)
    assert run(selected, ['7', '8', True]) == returned(['7', '7', None, '7'])
    assert run(selected, ['7', '8', False], 'V') == returned([None, None, '8', None])
    export(selected.replace('output_roles=[["P"],["P"],["V"],["P"]]',
                            'output_roles=[["P"],["P"],["V"],["P","V"]]'),
           refusal='structured-source-original')

with case('group-scale-order-domain-and-additive-test-model'):
    defs = definitions(export(groups))
    ops = defs['scale'][9][1]
    assert [op[0] for op in ops] == [['group.identity', group[1]], ['group.scale', group[1], field[1]],
                                    ['group.add', group[1]], ['group.equal', group[1]]]
    assert ops[1][1] == [1, 2]
    assert run(groups, ['7', '3'], 'V') == returned(['21', False])
    assert run(groups, ['7', '1'], 'V') == returned(['7', True])
    assert run(groups, [str(modulus - 1), '2'], 'V') == returned([str(modulus - 2), False])
    assert run(groups, ['0', '3']) == returned(['0', None])
    export(groups.replace('group_scale %g,%s : (!G,!F)', 'group_scale %s,%g : (!F,!G)'),
           refusal='structured-source-original')
    export(groups.replace('bls12-381.fr', 'bn254.fr'), refusal='structured-source-original')
    run(groups, [str(modulus), '1'], refusal='structured-reference-input')

with case('service-alias-and-distinct-handles-exact-query-order'):
    defs = definitions(export(services))
    ops = defs['main'][9][1]
    assert ops[0] == [['draw', 'P', field[1]], [0], [field], [], 'first']
    assert ops[1] == [['draw', 'P', field[1]], [2], [field], [], 'second']
    for handles in [('17', '17'), ('17', '29'), ('0', '18446744073709551615')]:
        script = [reply(['draw', site, 'P', contract, handle, field[1]], value)
                  for site, handle, value in zip(['first', 'second'], handles, ['3', '8'])]
        assert run(services, [*handles, True], replies=script) == returned(['3', '8', None], trace(script), 2)
        assert run(services, [*handles, True], 'V') == returned([None, None, True])
    assert run(services, [None, None, False], 'V') == returned([None, None, False])
    assert run(services, [None, '17', True]) == [
        'zkc.structured-open-result/0', ['stopped', 'incomplete', 'first'],
        [['stop', 'incomplete', 'first', 0]], 0]
    run(services, ['18446744073709551616', '1', True], refusal='structured-reference-input')

with case('missing-mismatched-invalid-and-stopping-replies'):
    action = ['draw', 'first', 'P', contract, '17', field[1]]
    script = [reply(action, '3')]
    missing = run(services, ['17', '17', True])
    assert missing == ['zkc.structured-open-result/0', ['stopped', 'incomplete', 'first'],
                       [['request', 0, action], ['stop', 'incomplete', 'first', 0]], 0]
    for changed in [reply(action[:-2] + ['18', field[1]], '3'),
                    ['reply', action, ['unit']], reply(action, str(modulus)), reply(action, None)]:
        result = run(services, ['17', '17', True], replies=[changed])
        assert result[1] == ['stopped', 'refused', 'first'] and result[-1] == 0
        assert result[2] == [['request', 0, action], ['stop', 'refused', 'first', 0]]
    for reason in ['abort', 'reject', 'incomplete', 'exhausted', 'refused']:
        stopped = [reply(action, stop=reason)]
        result = run(services, ['17', '17', True], replies=stopped)
        assert result == ['zkc.structured-open-result/0', ['stopped', reason, 'first'],
                          trace(stopped) + [['stop', reason, 'first', 1]], 1]
    # The first result is consumed, then the missing second reply stops at position one.
    result = run(services, ['17', '17', True], replies=script)
    assert result[1] == ['stopped', 'incomplete', 'second'] and result[-1] == 1
    run(services, ['17', '17', True], replies=[['unexpected']], refusal='structured-reference-input')
    for capacity in [0, 1000001, 1]:
        run(services, ['17', '17', True], capacity=capacity, refusal='structured-reference-capacity')
    run(services, ['17', '17', True], replies=[script[0]] * 4097, refusal='structured-reference-capacity')

with case('exact-open-request-shape'):
    for request in [[], ['1', '2'], ['zkc.structured-open-request/0', 'P', ['1', '2'], [], 100, 'extra'],
                    ['zkc.structured-open-request/0', 'P', ['1', '2'], [], True]]:
        run(components, [], request=request, refusal='structured-reference-input')
    run(components, ['1', '2'], closed=True, refusal='structured-reference-input')

with case('draw-reply-matches-every-action-field-and-leaves-suffix-unconsumed'):
    action = ['draw', 'first', 'P', contract, '17', field[1]]
    for position, replacement in enumerate(['receive', 'wrong_site', 'V', 'random.bn254.fr/0', '18', 'bn254.fr']):
        changed = action.copy()
        changed[position] = replacement
        result = run(services, ['17', '17', True], replies=[reply(changed, '3')])
        assert result == ['zkc.structured-open-result/0', ['stopped', 'refused', 'first'],
                          [['request', 0, action], ['stop', 'refused', 'first', 0]], 0]
    script = [reply(['draw', site, 'P', contract, '17', field[1]], '3') for site in ['first', 'second']]
    assert run(services, ['17', '17', True], replies=script + [reply(action, '99')]) == returned(
        ['3', '3', None], trace(script), 2)

with case('role-count-boundary-is-per-protocol'):
    roster = ['P', 'V'] + [f'Observer{i}' for i in range(14)]
    source = components.replace('roles=["P","V"]', 'roles=' + json.dumps(roster))
    assert definitions(export(source))['main'][6][1] == roster
    assert run(source, ['11', '22'], 'Observer13') == returned([None, None, None, None])
    excessive = source.replace(json.dumps(roster), json.dumps(roster + ['Extra']))
    export(excessive, refusal='structured-source-role')
    run(excessive, [], refusal='structured-reference-unsupported')

with case('replay-record-capacity-is-independent-of-request-byte-capacity'):
    sites = [('site' + str(i)).ljust(401, 'x') for i in range(1800)]

    def draw_script():
        return [reply(['draw', site, 'P', contract, '17', field[1]], str(modulus - 1)) for site in sites]

    padding = 1024 * 1024 - len(json.dumps(trace(draw_script()), separators=(',', ':')))
    assert 0 <= padding <= sum(512 - len(site) for site in sites)
    for i, site in enumerate(sites):
        size = min(padding, 512 - len(site))
        sites[i] += 'x' * size
        padding -= size
    for excess in [False, True]:
        if excess:
            sites[-1] += 'x'
        script = draw_script()
        request = ['zkc.structured-open-request/0', 'P', ['17', '17', True], script, 1000000]
        assert len(json.dumps(request, separators=(',', ':'))) < 1024 * 1024
        assert len(json.dumps(trace(script), separators=(',', ':'))) == 1024 * 1024 + excess
        operations = '\n'.join(f'%{name} = "protocol.query"(%first) {{method="draw",owner="P",site="{site}"}} : (!S)->!F'
                               for name, site in zip(['a', 'b'] + [f'v{i}' for i in range(1798)], sites))
        many = services[:services.index('%a =')] + operations + '\n' + services[services.index('"protocol.guard"'):]
        result = run(many, [], request=request, refusal='structured-reference-capacity' if excess else None)
        if not excess:
            assert result == returned([str(modulus - 1), str(modulus - 1), None], trace(script), 1800)

with case('receive-vector-capacity-remains-a-reference-diagnostic'):
    source = '''!V = !algebra.field_vector<"bls12-381.fr">
    module { "protocol.module"() ({
      "protocol.func"() ({ ^entry(%x:!V):
        %received = "protocol.exchange"(%x) {sender="P",receiver="V",site="vector"} : (!V)->!V
        "protocol.return"(%received) : (!V)->()
      }) {sym_name="main",origin=["main",[]],function_type=(!V)->!V,roles=["P","V"],input_roles=[["P"]],output_roles=[["V"]]} : ()->()
    }) {profile=#protocol.profile<protocol>} : ()->() }'''
    export(source)
    action = ['receive', 'vector', 'P', 'V', ['vector', field[1]]]
    script = [reply(action, ['1', '2'])]
    assert run(source, [None], 'V', replies=script) == returned([['1', '2']], trace(script), 1)
    run(source, [None], 'V', replies=[reply(action, ['0'] * 4097)], refusal='structured-reference-capacity')

with case('guard-owner-and-nonowner-after-query-effects'):
    script = [reply(['draw', site, 'P', contract, '17', field[1]], '3')
              for site in ['first', 'second']]
    result = run(services, ['17', '17', False], replies=script)
    assert result == ['zkc.structured-open-result/0', ['stopped', 'reject', 'check'],
                      trace(script) + [['stop', 'reject', 'check', 2]], 2]
    assert run(services, ['17', '17', False], 'V', replies=script) == returned([None, None, False])
    assert run(services, ['17', '17', None], replies=script) == [
        'zkc.structured-open-result/0', ['stopped', 'incomplete', 'check'],
        trace(script) + [['stop', 'incomplete', 'check', 2]], 2]

with case('local-zero-results-run-only-at-owner-and-sequence-all-inputs'):
    helper = '''func.func private @halt(%scope:!runtime.scope,%x:!F,%y:!F)
        ->!exec.outcome<> attributes {no_inline,runtime.origin=["halt",[]]} {
      %stop = "exec.reject"(%scope) {reason="abort",site="halted"} : (!runtime.scope)->!exec.stop
      cf.br ^failed(%stop : !exec.stop)
    ^failed(%cause:!exec.stop):
      %result = "exec.failed"(%cause) : (!exec.stop)->!exec.outcome<>
      func.return %result : !exec.outcome<>
    }'''
    source = components.replace('  func.func private @first', helper + '\n  func.func private @first', 1)
    source = source.replace('%a = func.call @nested',
                            '"protocol.local_call"(%x,%x) {callee=@halt,role="P",site="call"} : (!F,!F)->()\n%a = func.call @nested')
    export(source)
    assert run(source, ['11', '22']) == ['zkc.structured-open-result/0', ['stopped', 'abort', 'halted'],
                                       [['stop', 'abort', 'halted', 0]], 0]
    assert run(source, ['11', '22'], 'V') == returned([None, None, '22', '5'])
    assert run(source, [None, '22'])[1] == ['stopped', 'incomplete', 'call']
    export(source.replace('"protocol.local_call"(%x,%x)', '"protocol.local_call"(%x,%y)'),
           refusal='structured-source-original')
    shared = source.replace('"protocol.local_call"(%x,%x)', '"protocol.local_call"(%x,%y)').replace(
        'input_roles=[["P"],["V"]]', 'input_roles=[["P"],["P","V"]]')
    export(shared)
    assert run(shared, ['11', None])[1] == ['stopped', 'incomplete', 'call']

with case('closed-finite-regression-and-owned-local-finite-in-open-root'):
    assert run(total, [['3', '5', '7'], '1', '2'], closed=True) == ['returned', ['5', '7']]
    assert run(unit, [[], True], closed=True) == ['returned', [True]]
    assert run(unit, [['3'], False], closed=True) == ['returned', [False]]
    assert run(unit, [['3'], True], closed=True) == ['stopped', 'abort']
    multi = unit.replace('roles=["P"]', 'roles=["P","V"]', 1)
    export(multi)
    assert run(multi, [['3'], True], 'V') == returned([None])
    assert run(multi, [['3'], True])[1] == ['stopped', 'abort', 'body_stop']
    unsupported = total.replace('roles=["P"]', 'roles=["P","V"]', 1)
    export(unsupported, refusal='structured-source-multirole-math')
    run(unsupported, [[], '1', '2'], refusal='structured-reference-unsupported')

with case('multi-role-math-finite-refusal-follows-retained-calls-and-dormant-roots'):
    operation = '"algebra.finite_fold"(%xs,%a,%b) {domain=@items,step=@step} : (!V,!F,!F)->(!F,!F)'
    source = total.replace(operation, 'func.call @fold_helper(%xs,%a,%b) : (!V,!F,!F)->(!F,!F)')
    helper = f'''func.func private @fold_helper(%xs:!V,%a:!F,%b:!F) -> (!F,!F) {{
      %r:2 = {operation}
      func.return %r#0,%r#1 : !F,!F
    }}'''
    source = source.replace(' "protocol.func"() ({', helper + '\n "protocol.func"() ({', 1)
    export(source)
    assert run(source, [['3', '5', '7'], '1', '2'], closed=True) == ['returned', ['5', '7']]
    source = source.replace('roles=["P"]', 'roles=["P","V"]', 1)
    export(source, refusal='structured-source-multirole-math')
    run(source, [[], '1', '2'], refusal='structured-reference-unsupported')
    selected_root = '''"protocol.func"() ({
      %yes = arith.constant true
      "protocol.return"(%yes) : (i1)->()
    }) {sym_name="selected",origin=["selected",[]],function_type=()->i1,roles=["Reader"],input_roles=[],output_roles=[["Reader"]]} : ()->()'''
    source = source.replace('module { "protocol.module"() ({', 'module { "protocol.module"() ({\n' + selected_root)
    export(source, symbol='selected', refusal='structured-source-multirole-math')
    run(source, [], 'Reader', symbol='selected', refusal='structured-reference-unsupported')

for items in [[], ['2'], ['2', '3', '5']]:
    for enabled in [False, True]:
        with case(f'closed-nested-control-{len(items)}-{enabled}'):
            source = (fixtures / 'structured-source/nested-controls.mlir').read_text()
            left, right = '7', '11'
            for item in items:
                left, right = right, item
            expected = ['returned', [left, right]] if enabled else ['stopped', 'abort']
            assert run(source, [items, '7', '11', enabled], closed=True) == expected

for lower, upper in [(0, 0), (2, 1), (0, 1), (1, 3), (2, 5)]:
    for enabled in [False, True]:
        with case(f'closed-loop-captures-{lower}-{upper}-{enabled}'):
            source = (fixtures / 'structured-source/loops-and-captures.mlir').read_text()
            left, right, capture, other = '7', '11', '13', '17'
            count = max(upper - lower, 0)
            for _ in range(count):
                first, second = (capture, right) if enabled else (left, other)
                left, right = second, first
            if enabled:
                for _ in range(count):
                    left, right = right, left
            expected = ['stopped', 'reject'] if count and not enabled else ['returned', [right, capture]]
            assert run(source, ['7', '11', '13', '17', str(lower), str(upper), enabled],
                       symbol='entry', closed=True) == expected

with case('statement-zero-and-nonzero-acceptance-and-opaque-relation-metadata'):
    data = export(schnorr)
    assert data[5] == [['relation', 'schnorr_relation', 'public', 'external', 'example/schnorr', '0',
                        [group, group, field], [['bool']], ['parameter', 'statement', 'witness'], None]]
    statement = definitions(data)['main'][9][1][0]
    assert statement == [['statement', 'schnorr_relation', ['Bob', 'Bob', 'Alice'], 0, None], [0, 2, 1], [], [], '']
    nonzero = schnorr.replace('acceptance=0', 'acceptance=1').replace(
        '"protocol.return"(%ok) : (i1)', '"protocol.return"(%g,%ok) : (!algebra.group<"bls12-381.g1">,i1)').replace(
        '-> (i1), roles=', '-> (!algebra.group<"bls12-381.g1">,i1), roles=').replace(
        'output_roles=[["Bob"]]', 'output_roles=[["Alice","Bob"],["Bob"]]')
    assert definitions(export(nonzero))['main'][9][1][0][0][3] == 1
    opaque = schnorr.replace('kind="external"', 'kind="opaque/Kind:0"').replace(
        'key="example/schnorr"', 'key="do-not-infer/formula"').replace('revision="0"', 'revision="opaque-revision"')
    assert export(opaque)[5][0][3:6] == ['opaque/Kind:0', 'do-not-infer/formula', 'opaque-revision']

with case('schnorr-independent-receive-send-alias-and-cross-owner-service-alias'):
    actions = [['receive', 'commitment', 'Alice', 'Bob', group],
               ['draw', 'draw_challenge', 'Bob', contract, '29', field[1]],
               ['send', 'challenge', 'Bob', 'Alice', field, '5'],
               ['receive', 'response', 'Alice', 'Bob', field]]
    script = [reply(action, value) for action, value in zip(actions, ['14', '5', None, '22'])]
    result = run(schnorr, ['2', '123', '6', '17', '29'], 'Bob', script)
    assert result == returned([True], trace(script), 4)
    altered = copy.deepcopy(script)
    altered[-1][2] = ['value', '23']
    assert run(schnorr, ['2', '123', '6', '17', '29'], 'Bob', altered)[1] == ['returned', [False]]
    for position in range(4):
        prefix = script[:position] + [reply(actions[position], stop='abort')]
        result = run(schnorr, ['2', None, '6', None, '29'], 'Bob', prefix)
        assert result[1] == ['stopped', 'abort', actions[position][1]]
        assert result[-1] == position + 1 and result[2] == trace(prefix) + [['stop', 'abort', actions[position][1], position + 1]]
    run(schnorr, ['2', '3', '6', '17', '17'], 'Bob', refusal='structured-reference-input')
    # Prover receives a challenge independent of the verifier's local value.
    prover = [reply(['draw', 'nonce', 'Alice', contract, '17', field[1]], '7'),
              reply(['send', 'commitment', 'Alice', 'Bob', group, '14']),
              reply(['receive', 'challenge', 'Bob', 'Alice', field], '11'),
              reply(['send', 'response', 'Alice', 'Bob', field, '40'])]
    assert run(schnorr, ['2', '3', '6', '17', None], 'Alice', prover) == returned([None], trace(prover), 4)

for label, changed in [
    ('duplicate-role', components.replace('roles=["P","V"]', 'roles=["P","P"]')),
    ('unknown-input-role', components.replace('input_roles=[["P"],["V"]]', 'input_roles=[["Unknown"],["V"]]')),
    ('empty-scope', components.replace('input_roles=[["P"],["V"]]', 'input_roles=[[],["V"]]')),
    ('scope-count', components.replace('input_roles=[["P"],["V"]]', 'input_roles=[["P"]]')),
    ('duplicate-query-site', services.replace('site="second"', 'site="first"')),
    ('empty-query-site', services.replace('site="first"', 'site=""')),
    ('missing-query-site', services.replace(',site="first"', '')),
    ('wrong-query-owner', services.replace('owner="P",site="first"', 'owner="V",site="first"')),
    ('unknown-query-method', services.replace('method="draw"', 'method="unknown"')),
    ('query-unknown-attribute', services.replace('site="first"', 'site="first",unknown=true')),
    ('shared-service-owner', services.replace('input_roles=[["P"],["P"]', 'input_roles=[["P","V"],["P"]')),
    ('statement-selector', schnorr.replace('selectors=["Bob","Bob","Alice"]', 'selectors=["Bob","Bob","Bob"]')),
    ('statement-acceptance', schnorr.replace('acceptance=0', 'acceptance=1')),
    ('relation-unknown-attribute', schnorr.replace('kind="external"', 'unknown=true,kind="external"')),
    ('statement-artificial-site', schnorr.replace('acceptance=0', 'site="invented",acceptance=0')),
    ('group-unknown-attribute', groups.replace('"algebra.group_identity"()', '"algebra.group_identity"() {unknown=true}')),
]:
    with case('native-formation-' + label):
        export(changed, refusal='structured-source-original')
        run(changed, [], refusal='structured-reference-source')

for label, operation in [
    ('restrict', '%bad = "protocol.restrict_roles"(%first) {roles=["P"]} : (!S)->!S'),
    ('select', '%bad = arith.select %flag,%first,%second : !S'),
    ('exchange', '%bad = "protocol.exchange"(%first) {sender="P",receiver="V",site="bad"} : (!S)->!S'),
]:
    with case('service-reference-cannot-' + label):
        bad = services.replace('%a = "protocol.query"', operation + '\n%a = "protocol.query"', 1)
        export(bad, refusal='structured-source-original')
        run(bad, [], refusal='structured-reference-source')

with case('service-reference-cannot-be-returned'):
    bad = services.replace('"protocol.return"(%a,%b,%flag) : (!F,!F,i1)',
                           '"protocol.return"(%first,%b,%flag) : (!S,!F,i1)').replace(
        'function_type=(!S,!S,i1)->(!F,!F,i1)', 'function_type=(!S,!S,i1)->(!S,!F,i1)')
    export(bad, refusal='structured-source-original')
    run(bad, [], refusal='structured-reference-source')

with case('restrict-has-no-artificial-site'):
    restricted = components.replace('%a = func.call @nested',
                                    '%narrow = "protocol.restrict_roles"(%x) {roles=["P"]} : (!F)->!F\n%a = func.call @nested')
    assert definitions(export(restricted))['main'][9][1][0] == [['restrict', ['P']], [0], [field], [], '']
    export(restricted.replace('roles=["P"]} : (!F)', 'roles=["P"],site="invented"} : (!F)'),
           refusal='structured-source-original')
    export(restricted.replace('roles=["P"]} : (!F)', 'roles=["V"]} : (!F)'),
           refusal='structured-source-original')

with case('dormant-protocol-owners-use-their-own-roster'):
    owned = components.replace('"protocol.return"(%x) : (!F)->()',
        '%yes = arith.constant true\n"protocol.guard"(%yes) {owner="Auditor",site="audit"} : (i1)->()\n"protocol.return"(%x) : (!F)->()')
    assert definitions(export(owned))['other'][9][1][1][0] == ['guard', 'Auditor']
    assert run(owned, ['37'], 'Auditor', symbol='other') == returned(['37'])

with case('unused-relations-retained-and-conflicting-identities-refused'):
    declaration = schnorr.split('relation.declare ', 1)[1].split('\n', 1)[0]
    unused = components.replace('  func.func private @first',
                                'relation.declare ' + declaration + '\n  func.func private @first', 1)
    assert len(export(unused)[5]) == 1
    assert run(unused, ['11', '22']) == returned(['11', '11', None, '5'])
    malformed = unused.replace('kind="external"', 'unknown=true,kind="external"')
    export(malformed, refusal='structured-source-original')
    run(malformed, [], refusal='structured-reference-source')
    conflicting = unused.replace('  func.func private @first',
                                 'relation.declare ' + declaration.replace('@schnorr_relation', '@conflict').replace(
                                     '["parameter", "statement", "witness"]', '["witness", "statement", "witness"]') +
                                 '\n  func.func private @first', 1)
    export(conflicting, refusal='relation-declaration-conflict')
    many = components.replace('  func.func private @first', '\n'.join(
        'relation.declare ' + declaration.replace('@schnorr_relation', f'@r{i}') for i in range(129)) +
        '\n  func.func private @first', 1)
    export(many, refusal='structured-source-limit')
    run(many, [], refusal='structured-reference-capacity')

with case('actual-schnorr-library-interactive-retains-formula-and-relation'):
    source, symbol, data = frontend('example::Interactive', {
        'example': repository_root / 'examples/projects/schnorr/main.zkc',
        'schnorr': repository_root / 'libraries/protocols/sigma/schnorr/lib.zkc'})
    assert len(data[5]) == 1
    assert data[5][0][3] == 'zkc.language.formula/0'
    assert len([d for d in data[7] if d[2] == 'math']) == 1
    assert len([d for d in data[7] if d[2] == 'protocol']) == 1
    assert not any(op[0][0] == 'statement' for op in definitions(data)[symbol][9][1])
    script = []
    for value in ['14', '5', None, '22']:
        pending = run(source, ['2', '6', None, None, '29'], 'role00000001', script, symbol=symbol)
        assert pending[1][1] == 'incomplete'
        script.append(reply(pending[2][-2][2], value))
    assert run(source, ['2', '6', None, None, '29'], 'role00000001', script, symbol=symbol) == returned([True], trace(script), 4)
    _, proof_symbol, proof = frontend('example::Proof', {
        'example': repository_root / 'examples/projects/schnorr/main.zkc',
        'schnorr': repository_root / 'libraries/protocols/sigma/schnorr/lib.zkc'}, proof=True)
    assert any(op[0][0] == 'statement' for op in definitions(proof)[proof_symbol][9][1])

for form in ['Helpers', 'Reordered', 'EarlyChallenge']:
    with case('retained-source-form-' + form):
        source, symbol, data = frontend('schnorr_forms::' + form, {
            'schnorr_forms': repository_root / 'lean/bridges/common/fixtures/schnorr-forms.zkc'})
        defs = definitions(data)
        assert data[5] == []
        assert sum(d[2] == 'math' for d in data[7]) == (2 if form == 'Helpers' else 0)
        ops = defs[symbol][9][1]
        assert sum(op[0][0] == 'call' for op in ops) == (2 if form == 'Helpers' else 0)
        first = run(source, ['2', '6', None, None, '29'], 'role00000001', symbol=symbol)
        assert first[2][0][2][0] == ('draw' if form == 'EarlyChallenge' else 'receive')
        # Resolve native action spellings by a missing-reply probe, not by SSA export coordinates.
        script = []
        values = iter(['14', '5', None, '22'] if form != 'EarlyChallenge' else ['5', '14', None, '22'])
        for _ in range(4):
            pending = run(source, ['2', '6', None, None, '29'], 'role00000001', script, symbol=symbol)
            action = pending[2][-2][2]
            script.append(reply(action, next(values)))
        assert run(source, ['2', '6', None, None, '29'], 'role00000001', script, symbol=symbol) == returned([True], trace(script), 4)

commands.save()
print(f'structured-open: {counted()} cases')
