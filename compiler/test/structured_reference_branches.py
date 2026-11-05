"""Selected mathematical regions in the bounded original-SSA test observer."""
import json
from pathlib import Path

from cases import case, counted
from commands import Commands
from entry_artifacts import compile_run_package
from tools import compiler, records
from variant_types import variant

commands = Commands(records())
fixtures = Path(__file__).parent / 'fixtures/structured-source'
reference = Path(compiler).parent / 'test/zkc-structured_reference-test'
serial = 0


def run(source, inputs, *, capacity=1000000, refusal=None, symbol='main', closed=False, role='P', replies=()):
    global serial
    serial += 1
    path = commands.directory / f'branch-{serial}.mlir'
    path.write_text(source)
    request = commands.write(f'branch-{serial}.json', inputs if closed else [
        'zkc.structured-open-request/0', role, inputs, list(replies), capacity])
    output = commands.run([reference, *([] if closed else ['open']), path, symbol, request],
                          refuses=refusal, keep=f'branch-{serial}-result.json')
    return None if refusal else json.loads(output)


def returned(values):
    return ['zkc.structured-open-result/0', ['returned', values], [], 0]


def protocol(arguments, results, body, declarations=''):
    """One-role original protocol with explicit ordered native ABI."""
    ports = ','.join(f'%arg{i}:{t}' for i, t in enumerate(arguments))
    inputs, outputs = ','.join(arguments), ','.join(results)
    return ('module { "protocol.module"() ({\n' + declarations + '\n'
            f'"protocol.func"() ({{ ^entry({ports}):\n{body}\n'
            f'}}) {{sym_name="main",origin=["main",[]],function_type=({inputs})->({outputs}),'
            f'roles=["P"],input_roles={json.dumps([["P"]]*len(arguments))},'
            f'output_roles={json.dumps([["P"]]*len(results))}}} : ()->()\n'
            '}) {profile=#protocol.profile<protocol>} : ()->() }')


nested = (fixtures / 'reference-branches.mlir').read_text()
for outer in [False, True]:
    for inner in [False, True]:
        with case(f'nested-boolean-{outer}-{inner}-helper-captures-and-ordered-results'):
            left, right = ['2', '3'], ['5', '7', '11']
            first = left if outer and inner else right
            second = right if inner and outer else left
            assert run(nested, [outer, inner, left, right]) == returned([
                first, str(len(first)), second, str(len(second))])
            assert run(nested, [outer, inner, left, right], closed=True) == [
                'returned', [first, str(len(first)), second, str(len(second))]]

with case('missing-selector-and-unused-missing-capture'):
    assert run(nested, [None, True, ['2'], ['3']]) == returned([None, None, None, None])
    assert run(nested, [False, False, None, ['3']]) == returned([['3'], '1', None, None])
    assert run(nested, [True, True, ['2'], None]) == returned([['2'], '1', None, None])

# Dead, admitted total instructions still cost dynamic observer work when their
# arm executes. They must cost nothing when that arm is dormant.
work = '\n'.join(f'%dead{i} = "data.index"() {{value={i}:ui64}} : ()->ui64' for i in range(40))
expensive = protocol(['i1'], ['i1'], '''
%value = "data.branch"(%arg0) ({
  %yes = arith.constant true
  "data.yield"(%yes) : (i1)->()
}, {
''' + work + '''
  %no = arith.constant false
  "data.yield"(%no) : (i1)->()
}) {alternatives=["then","else"]} : (i1)->i1
"protocol.return"(%value) : (i1)->()
''')
with case('selected-entry-and-work-capacity-boundary'):
    # Root invocation, root block, branch, arm block, constant, yield, return.
    assert run(expensive, [True], capacity=7) == returned([True])
    run(expensive, [True], capacity=6, refusal='structured-reference-capacity')
    assert run(expensive, [False], capacity=47) == returned([False])
    run(expensive, [False], capacity=46, refusal='structured-reference-capacity')
    run(expensive, [False], capacity=7, refusal='structured-reference-capacity')

with case('unsupported-total-operation-in-dormant-arm-still-refuses'):
    unsupported = expensive.replace(
        '%dead0 = "data.index"() {value=0:ui64} : ()->ui64',
        '%dead0 = "data.index_wrapping_add"(%one,%one) : (ui64,ui64)->ui64')
    unsupported = unsupported.replace('%dead0 =', '%one = "data.index"() {value=1:ui64} : ()->ui64\n%dead0 =')
    run(unsupported, [True], refusal='structured-reference-unsupported: data.index_wrapping_add')

with case('malformed-dormant-yield-and-ambient-capture-refuse-native-admission'):
    run(expensive.replace('"data.yield"(%no) : (i1)->()',
                          '"data.yield"() : ()->()'), [True], refusal='structured-reference-source')
    ambient = expensive.replace('"data.yield"(%no)', '"data.yield"(%arg0)')
    run(ambient, [True], refusal='structured-reference-source')

leaf = ['Leaf', [('some', ['index', 'bool']), ('none', [])]]
leaf_type = variant(*leaf)
container_type = variant('Container', [('wrapped', [leaf, 'vector:bls12-381.fr']), ('empty', [])])
variant_source = protocol([container_type, 'ui64'], [leaf_type, 'ui64'], f'''
%item,%number = "data.branch"(%arg0,%arg1) ({{
^wrapped(%payload:{leaf_type},%values:!data.field_vector<"bls12-381.fr">,%capture:ui64):
  %index = "data.branch"(%payload,%capture) ({{
  ^some(%n:ui64,%flag:i1,%fallback:ui64):
    "data.yield"(%n) : (ui64)->()
  }}, {{
  ^none(%fallback:ui64):
    "data.yield"(%fallback) : (ui64)->()
  }}) {{alternatives=["some","none"]}} : ({leaf_type},ui64)->ui64
  "data.yield"(%payload,%index) : ({leaf_type},ui64)->()
}}, {{
^empty(%fallback:ui64):
  %none = "data.make"() {{alternative="none"}} : ()->{leaf_type}
  "data.yield"(%none,%fallback) : ({leaf_type},ui64)->()
}}) {{alternatives=["wrapped","empty"]}} : ({container_type},ui64)->({leaf_type},ui64)
"protocol.return"(%item,%number) : ({leaf_type},ui64)->()
''')
for value, expected in [
    (['wrapped', [['some', ['19', True]], ['2', '3']]], [['some', ['19', True]], '19']),
    (['wrapped', [['none', []], []]], [['none', []], '23']),
    (['empty', []], [['none', []], '23']),
]:
    with case(f'nested-variant-payload-before-captures-{value}'):
        assert run(variant_source, [value, '23']) == returned(expected)

with case('variant-input-rejects-unknown-label-missing-extra-and-wrong-payload'):
    for value in [['unknown', []], ['empty', ['0']], ['wrapped', []],
                  ['wrapped', [['some', ['19', 'true']], []]]]:
        run(variant_source, [value, '23'], refusal='structured-reference-input')

with case('variant-construction-total-projection-and-tag-preserve-nominal-carrier'):
    pair = variant('Pair', [('pair', ['index', 'bool'])])
    source_pair = protocol(['ui64', 'i1'], ['ui64', 'i1', 'i1', pair], f'''
%pair = "data.make"(%arg0,%arg1) {{alternative="pair"}} : (ui64,i1)->{pair}
%n = "data.get"(%pair) {{index=0:i64}} : ({pair})->ui64
%b = "data.get"(%pair) {{index=1:i64}} : ({pair})->i1
%tag = "data.is"(%pair) {{alternative="pair"}} : ({pair})->i1
"protocol.return"(%n,%b,%tag,%pair) : (ui64,i1,i1,{pair})->()
''')
    assert run(source_pair, ['31', False], capacity=16) == returned([
        '31', False, True, ['pair', ['31', False]]])
    run(source_pair, ['31', False], capacity=15, refusal='structured-reference-capacity')

def shared_variant(depth):
    aliases = '!T0 = !data.variant<#data.identity<["atom","Leaf"]>, [#data.alternative<"leaf">]>\n'
    body = '%v0 = "data.make"() {alternative="leaf"} : ()->!T0\n'
    for level in range(1, depth + 1):
        aliases += (f'!T{level} = !data.variant<#data.identity<["atom","Node{level}"]>, '
                    f'[#data.alternative<"node", [!T{level-1}, !T{level-1}]>]>\n')
        body += (f'%v{level} = "data.make"(%v{level-1},%v{level-1}) {{alternative="node"}} '
                 f': (!T{level-1},!T{level-1})->!T{level}\n')
    body += f'"protocol.return"(%v{depth}) : (!T{depth})->()'
    return aliases + protocol([], [f'!T{depth}'], body)


with case('shared-nested-variant-output-expansion-is-bounded-before-serialization'):
    shared = shared_variant(8)
    expected = ['leaf', []]
    for _ in range(8):
        expected = ['node', [expected, expected]]
    # 28 evaluation units plus 2555 expanded carrier/label/leaf units.
    assert run(shared, [], capacity=2583) == returned([expected])
    run(shared, [], capacity=2582, refusal='structured-reference-capacity')
    run(shared, [], capacity=1000, refusal='structured-reference-capacity')

with case('native-metadata-expansion-limit-precedes-observer-evaluation'):
    run(shared_variant(20), [], refusal='structured-reference-source')

with case('variant-entry-payload-and-capture-work-boundary'):
    selected = protocol([leaf_type, 'ui64'], ['ui64', 'i1'], f'''
%n,%b = "data.branch"(%arg0,%arg1) ({{
^some(%index:ui64,%flag:i1,%capture:ui64):
  "data.yield"(%index,%flag) : (ui64,i1)->()
}}, {{
^none(%capture:ui64):
  %no = arith.constant false
  "data.yield"(%capture,%no) : (ui64,i1)->()
}}) {{alternatives=["some","none"]}} : ({leaf_type},ui64)->(ui64,i1)
"protocol.return"(%n,%b) : (ui64,i1)->()
''')
    assert run(selected, [['some', ['19', True]], '23'], capacity=9) == returned(['19', True])
    run(selected, [['some', ['19', True]], '23'], capacity=8, refusal='structured-reference-capacity')
    assert run(selected, [['none', []], '23'], capacity=8) == returned(['23', False])
    run(selected, [['none', []], '23'], capacity=7, refusal='structured-reference-capacity')

with case('ordered-guard-in-dormant-math-arm-is-not-admitted-as-total'):
    guarded = expensive.replace('"data.yield"(%no)',
        '"protocol.guard"(%no) {owner="P",site="forbidden"} : (i1)->()\n"data.yield"(%no)')
    run(guarded, [True], refusal='structured-reference-source')

with case('ordered-query-and-guard-stop-prefixes-around-selection'):
    services = (fixtures / 'open-services.mlir').read_text()
    selection = '''%selected = "data.branch"(%flag,%a,%b) ({
    ^then(%x:!F,%y:!F): "data.yield"(%x) : (!F)->()
    }, {
    ^else(%x:!F,%y:!F): "data.yield"(%y) : (!F)->()
    }) {alternatives=["then","else"]} : (i1,!F,!F)->!F
    '''
    services = services.replace('"protocol.return"(%a,%b,%flag)',
                                selection + '"protocol.return"(%selected,%b,%flag)')
    contract = 'random.bls12-381.fr/0'
    actions = [['draw', site, 'P', contract, '17', 'bls12-381.fr'] for site in ['first', 'second']]
    replies = [['reply', action, ['value', value]] for action, value in zip(actions, ['3', '8'])]
    trace = [event for i, row in enumerate(replies)
             for event in [['request', i, row[1]], ['reply', i, row[2]]]]
    assert run(services, ['17','17',True], replies=replies) == [
        'zkc.structured-open-result/0', ['returned', ['3','8',None]], trace, 2]
    assert run(services, ['17','17',False], replies=replies) == [
        'zkc.structured-open-result/0', ['stopped', 'reject', 'check'],
        trace + [['stop', 'reject', 'check', 2]], 2]
    stopped = [['reply', actions[0], ['stop', 'abort']]]
    assert run(services, ['17','17',True], replies=stopped) == [
        'zkc.structured-open-result/0', ['stopped', 'abort', 'first'],
        [['request', 0, actions[0]], ['reply', 0, ['stop', 'abort']],
         ['stop', 'abort', 'first', 1]], 1]

with case('zero-result-selected-arms-keep-work'):
    empty = expensive.replace('%value = "data.branch"', '"data.branch"').replace(
        '"data.yield"(%yes)', '"data.yield"()').replace(
        '"data.yield"(%no)', '"data.yield"()').replace(
        ': (i1)->()\n}', ': ()->()\n}').replace(
        ': (i1)->i1', ': (i1)->()').replace('"protocol.return"(%value)',
        '"protocol.return"(%arg0)')
    assert run(empty, [True], capacity=7) == returned([True])
    run(empty, [False], capacity=7, refusal='structured-reference-capacity')

# Use the actual language package producer. Scoped stops are valid here; a stop
# inside data.branch itself is forbidden total mathematics, not a dormant value.
source = commands.directory / 'selected-source.zkc'
source.write_text('''module sample;
domain F=field("bls12-381.fr");
math fn selected(a:bool,b:bool,c:bool)->bool { return a && (b || c); }
fn checked(a:bool,b:bool,c:bool,go:bool)->bool {
  return if go { selected(a,b,c) } else { stop "abort"; };
}
protocol Run roles(P)(a:bool@P,b:bool@P,c:bool@P,go:bool@P)->(result:bool@P) {
  return checked(a,b,c,go);
}
entry fn Demo(inputs:Run::Inputs) { return Run::run(inputs); }
''')
child = compile_run_package(commands, '--source-format=zkc', '--entry=sample::Demo',
                            f'--module=sample={source}')
symbol = json.loads(child['interface'])['protocol']
original = child['original']
for a in [False, True]:
    for b in [False, True]:
        for c in [False, True]:
            with case(f'language-package-selected-bool-and-dormant-stop-{a}-{b}-{c}'):
                assert run(original, [a,b,c,True], symbol=symbol, role='role00000000') == returned([a and (b or c)])
with case('selected-scoped-stop-preserves-prefix-and-skips-math'):
    result = run(original, [True,True,True,False], symbol=symbol, role='role00000000')
    assert result[1][:2] == ['stopped', 'abort']
    assert result[2] == [['stop', 'abort', result[1][2], 0]] and result[3] == 0

commands.save()
print(f'structured-reference-branches: {counted()} cases; evidence: {commands.directory}')
