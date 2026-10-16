"""Retained primitive bindings, unchanged library closures, and independent SSA laws."""
import hashlib
import json
import re
from pathlib import Path

from cases import case, counted
from commands import Commands
from tools import compiler, records

commands = Commands(records())
root = Path(__file__).resolve().parents[2]
fixtures = Path(__file__).parent / 'fixtures/structured-source'
reference = Path(compiler).parent / 'test/zkc-structured_reference-test'
field = '!algebra.field<"bls12-381.fr">'
vector = '!algebra.field_vector<"bls12-381.fr">'
maximum = (1 << 64) - 1
modulus = 52435875175126190479447740508185965837690552500527637822603658699938581184513
ports = {'i': 'ui64', 'b': 'i1', 'f': field, 'v': vector}
catalogue = {
    'index.constant': ('', 'i'), 'index.add': ('ii', 'i'),
    'index.sub': ('ii', 'i'), 'index.mul': ('ii', 'i'),
    'index.div': ('ii', 'i'), 'index.mod': ('ii', 'i'),
    'index.equal': ('ii', 'b'), 'index.less': ('ii', 'b'),
    'vector.empty': ('', 'v'), 'vector.length': ('v', 'i'),
    'vector.sum': ('v', 'f'), 'vector.split': ('v', 'vv'),
    'vector.append': ('vf', 'v'), 'vector.equal': ('vv', 'b'),
    'field.equal': ('ff', 'b'),
}
serial = 0


def export(source, symbol='main', refusal=None, keep=None):
    result = commands.source('protocol-structured', source, '--symbol=' + symbol,
                             refuses=refusal, keep=keep)
    return None if refusal else json.loads(result)


def run(source, inputs, symbol='main', role='P', replies=(), capacity=1000000, refusal=None):
    global serial
    serial += 1
    path = commands.directory / f'primitive-{serial}.mlir'
    path.write_text(source)
    request = commands.write(f'primitive-{serial}-request.json',
                             ['zkc.structured-open-request/0', role, inputs, list(replies), capacity])
    result = commands.run([reference, 'open', path, symbol, request], refuses=refusal,
                          keep=f'primitive-{serial}-result.json')
    return None if refusal else json.loads(result)


def returned(values):
    return ['zkc.structured-open-result/0', ['returned', values], [], 0]


def stopped(reason='refused', site='primitive'):
    return ['zkc.structured-open-result/0', ['stopped', reason, site],
            [['stop', reason, site, 0]], 0]


def binding(contract, name='operation', implementation=''):
    arguments = [] if contract.startswith('index.') else ['bls12-381.fr']
    return ('"local.binding"() {sym_name=' + json.dumps(name) + ',contract=' + json.dumps(contract) +
            ',arguments=' + json.dumps(arguments) + ',implementation=' + json.dumps(implementation) + '} : ()->()')


def wrapped(inputs, outputs, body, results, declarations='', after=''):
    args = ','.join(f'%a{i}:{t}' for i, t in enumerate(inputs))
    actuals = ','.join(f'%a{i}' for i in range(len(inputs)))
    ins, outs = ','.join(inputs), ','.join(outputs)
    scopes_in, scopes_out = json.dumps([['P']] * len(inputs)), json.dumps([['P']] * len(outputs))
    call_results = '' if not outputs else '%result = ' if len(outputs) == 1 else f'%result:{len(outputs)} = '
    returned_results = '' if not outputs else '%result' if len(outputs) == 1 else ','.join(f'%result#{i}' for i in range(len(outputs)))
    return f'''module {{ "protocol.module"() ({{
{declarations}
"local.func"() ({{ ^entry({args}):
{body}
"local.return"({','.join(results)}) : ({outs})->()
}}) {{sym_name="work",function_type=({ins})->({outs}),logical_origin=["work",[]]}} : ()->()
"protocol.func"() ({{ ^entry({args}):
{call_results}"protocol.local_call"({actuals}) {{callee=@work,role="P",site="call"}} : ({ins})->({outs})
{after}
"protocol.return"({returned_results}) : ({outs})->()
}}) {{sym_name="main",function_type=({ins})->({outs}),roles=["P","V"],input_roles={scopes_in},output_roles={scopes_out}}} : ()->()
}}) {{profile=#protocol.profile<protocol>}} : ()->() }}'''


def primitive(contract, parameters=(), drop=False, reverse=False, name='operation'):
    ins, outs = catalogue[contract]
    inputs, outputs = [ports[x] for x in ins], [ports[x] for x in outs]
    actuals = ','.join(f'%a{i}' for i in range(len(inputs)))
    result = '%r' if len(outputs) == 1 else f'%r:{len(outputs)}'
    body = (f'{result} = "algebra.exec.{contract.replace(".", "_")}"({actuals}) '
            f'{{binding=@{name},parameters={json.dumps(list(parameters))},site="primitive"}} : '
            f'({",".join(inputs)})->({",".join(outputs)})')
    results = ['%r'] if len(outputs) == 1 else [f'%r#{i}' for i in range(len(outputs))]
    return wrapped(inputs, [] if drop else outputs, body,
                   [] if drop else list(reversed(results)) if reverse else results, binding(contract, name))


def reject_native(source, inputs):
    export(source, refusal='structured-source-original')
    run(source, inputs, refusal='structured-reference-source')


with case('all-fifteen-exact-bindings-and-descriptors'):
    for contract, (inputs, outputs) in catalogue.items():
        parameters = [str(maximum)] if contract == 'index.constant' else []
        snapshot = export(primitive(contract, parameters))
        assert len(snapshot) == 8 and snapshot[4:6] == [[], []]
        assert snapshot[6] == [['binding', 'operation', contract,
                                [] if contract.startswith('index.') else ['bls12-381.fr'], '']]
        work = snapshot[7][0]
        op = work[9][1][0]
        assert op[0] == ['exec', 'algebra.exec.' + contract.replace('.', '_'), 'operation', parameters]
        assert op[1] == list(range(len(inputs))) and len(op[2]) == len(outputs)
        assert op[3:] == [[], 'primitive']
        assert work[9][2] == ['return', list(range(len(outputs)))]

arithmetic = [
    ('index.constant', [], [str(maximum)], [str(maximum)]),
    ('index.add', [str(maximum), '0'], [str(maximum)], []),
    ('index.add', [str(maximum - 1), '1'], [str(maximum)], []),
    ('index.add', [str(maximum), '1'], None, []),
    ('index.mul', ['0', str(maximum)], ['0'], []),
    ('index.mul', [str(maximum), '1'], [str(maximum)], []),
    ('index.mul', [str(maximum), '2'], None, []),
    ('index.sub', ['0', '0'], ['0'], []),
    ('index.sub', ['7', '2'], ['5'], []),
    ('index.sub', ['0', '1'], None, []),
    ('index.div', [str(maximum), '8'], ['2305843009213693951'], []),
    ('index.mod', [str(maximum), '8'], ['7'], []),
    ('index.div', ['0', '0'], None, []),
    ('index.mod', [str(maximum), '0'], None, []),
    ('index.equal', [str(maximum), str(maximum)], [True], []),
    ('index.equal', ['0', str(maximum)], [False], []),
    ('index.less', ['0', str(maximum)], [True], []),
    ('index.less', [str(maximum), '0'], [False], []),
    ('index.less', [str(maximum), str(maximum)], [False], []),
]
for number, (contract, inputs, outputs, parameters) in enumerate(arithmetic):
    with case(f'checked-arithmetic-{number}-{contract}'):
        assert run(primitive(contract, parameters), inputs) == (stopped() if outputs is None else returned(outputs))

vector_cases = [
    ('vector.empty', [], [[]]), ('vector.length', [[]], ['0']),
    ('vector.length', [['3', '3', '9']], ['3']),
    ('vector.sum', [[]], ['0']), ('vector.sum', [[str(modulus - 1), '2']], ['1']),
    ('vector.sum', [['7', '7', '7']], ['21']),
    ('vector.split', [[]], None), ('vector.split', [['1']], None),
    ('vector.split', [['1', '2', '3']], None),
    ('vector.split', [['1', '7', '2', '9']], [['1', '7'], ['2', '9']]),
    ('vector.split', [['1', '2', '3', '4', '5', '6']], [['1', '2', '3'], ['4', '5', '6']]),
    ('vector.append', [['3', '3'], '8'], [['3', '3', '8']]),
    ('vector.append', [[], '0'], [['0']]),
    ('vector.equal', [[], []], [True]), ('vector.equal', [['3'], ['3', '0']], [False]),
    ('vector.equal', [['1', '7'], ['7', '1']], [False]),
    ('vector.equal', [['1', '7'], ['1', '7']], [True]),
    ('field.equal', ['3', '3'], [True]), ('field.equal', ['3', '4'], [False]),
]
for number, (contract, inputs, outputs) in enumerate(vector_cases):
    with case(f'vector-field-law-{number}-{contract}'):
        assert run(primitive(contract), inputs) == (stopped() if outputs is None else returned(outputs))

with case('same-typed-split-permutation-is-a-different-program'):
    source = primitive('vector.split', reverse=True)
    assert export(source)[7][0][9][2] == ['return', [1, 0]]
    assert run(source, [['1', '7', '2', '9']]) == returned([['2', '9'], ['1', '7']])

with case('renamed-binding-is-retained-without-helper-name-trust'):
    source = primitive('index.sub', name='index.mul')
    assert export(source)[6][0][1:3] == ['index.mul', 'index.sub']
    assert run(source, ['9', '2']) == returned(['7'])
    changed = source.replace('index_sub', 'index_add').replace('contract="index.sub"', 'contract="index.add"')
    export(changed)
    assert run(changed, ['9', '2']) == returned(['11'])

with case('unused-supported-bindings-retained-in-order-and-independently-admitted'):
    source = primitive('index.add')
    source = source.replace(binding('index.add'), binding('vector.split', 'unused') + '\n' + binding('index.add'))
    assert [b[1] for b in export(source)[6]] == ['unused', 'operation']
    assert run(source, ['1', '2']) == returned(['3'])
    bad = source.replace('contract="vector.split"', 'contract="vector.product"')
    export(bad, refusal='structured-source-binding')
    run(bad, ['1', '2'], refusal='structured-reference-binding')

with case('nonempty-implementation-refused-even-when-unused'):
    source = primitive('index.add').replace(binding('index.add'),
        binding('index.add', 'unused', 'native/index.add') + '\n' + binding('index.add'))
    export(source, refusal='structured-source-implementation')
    run(source, ['1', '2'], refusal='structured-reference-implementation')

with case('exact-binding-name-bound-and-table-bound'):
    source = primitive('index.add', name='n' * 256)
    export(source)
    assert run(source, ['1', '2']) == returned(['3'])
    for name in ['n' * 257, '9name', 'a/b', 'é', '']:
        reject_native(primitive('index.add').replace('@operation', '@' + json.dumps(name)).replace('sym_name="operation"', 'sym_name=' + json.dumps(name)), ['1', '2'])
    source = primitive('index.add').replace(binding('index.add'), '\n'.join(binding('index.add', 'b' + str(i)) for i in range(127)) + '\n' + binding('index.add'))
    assert len(export(source)[6]) == 128
    assert run(source, ['1', '2']) == returned(['3'])
    source = source.replace(binding('index.add'), binding('index.add', 'extra') + '\n' + binding('index.add'))
    export(source, refusal='structured-source-limit')
    run(source, ['1', '2'], refusal='structured-reference-capacity')

base = primitive('index.add')
for name, bad in [
    ('kind-contract', base.replace('algebra.exec.index_add', 'algebra.exec.index_mul')),
    ('domain-count', base.replace('arguments=[]', 'arguments=["bls12-381.fr"]')),
    ('missing-binding', base.replace('binding=@operation', 'binding=@missing')),
    ('wrong-symbol-kind', base.replace('binding=@operation', 'binding=@work')),
    ('duplicate-symbol', base.replace('sym_name="operation"', 'sym_name="work"')),
    ('extra-parameter', base.replace('parameters=[]', 'parameters=["1"]')),
    ('non-string-parameter', base.replace('parameters=[]', 'parameters=[1:i64]')),
    ('missing-parameter-array', base.replace('parameters=[],', '')),
    ('wrong-port', base.replace('ui64', 'i1')),
    ('empty-site', base.replace('site="primitive"', 'site=""')),
    ('extra-exec-attribute', base.replace('parameters=[]', 'parameters=[],unexpected=true')),
    ('extra-binding-attribute', base.replace('implementation=""', 'implementation="",unexpected=true')),
    ('call-binding', base.replace('callee=@work', 'callee=@operation')),
]:
    with case('native-admission-' + name):
        reject_native(bad, ['1', '2'])

for literal in ['00', '+1', '-1', '1 ', str(maximum + 1), '9' * 100]:
    with case('canonical-u64-parameter-' + literal[:24]):
        reject_native(primitive('index.constant', [literal]), [])

with case('nominal-domain-profile-on-unused-binding'):
    source = primitive('index.add').replace(binding('index.add'),
        binding('vector.sum', 'unused').replace('bls12-381.fr', 'bn254.fr') + '\n' + binding('index.add'))
    export(source, refusal='structured-source-binding')
    run(source, ['1', '2'], refusal='structured-reference-binding')
    reject_native(source.replace('bn254.fr', 'bls12-381.g1'), ['1', '2'])

with case('binding-visibility-is-not-silently-dropped'):
    source = base.replace('implementation=""', 'implementation="",sym_visibility="private"')
    export(source, refusal='interactive-unknown-attribute')
    run(source, ['1', '2'], refusal='structured-reference-source')

with case('exec-owner-and-pure-local-owner-remain-distinct'):
    math = base.replace('"local.func"', '"func.func"').replace('"local.return"', '"func.return"')
    math = math.replace('logical_origin=["work",[]]', 'sym_visibility="private"')
    math = math.replace('"protocol.local_call"', '"func.call"').replace('callee=@work,role="P",site="call"', 'callee=@work')
    reject_native(math, ['1', '2'])
    protocol = base.replace('"protocol.local_call"(%a0,%a1) {callee=@work,role="P",site="call"}',
                            '"algebra.exec.index_add"(%a0,%a1) {binding=@operation,parameters=[],site="call"}')
    reject_native(protocol, ['1', '2'])
    pure = primitive('index.constant', ['0']).replace('"algebra.exec.index_constant"() {binding=@operation,parameters=["0"],site="primitive"}',
                                                    '"data.index"() {value="0"}')
    reject_native(pure, [])

with case('primitive-sites-and-split-full-result-abi'):
    duplicate = base.replace('"local.return"(%r)',
        '%unused = "algebra.exec.index_add"(%a0,%a1) {binding=@operation,parameters=[],site="primitive"} : (ui64,ui64)->ui64\n"local.return"(%r)')
    reject_native(duplicate, ['1', '2'])
    split = primitive('vector.split')
    # Keep the helper/caller two-result signature but use a single-result exec.
    bad = split.replace('%r:2 =', '%r =').replace(f'({vector})->({vector},{vector})', f'({vector})->({vector})', 1)
    bad = bad.replace('"local.return"(%r#0,%r#1)', '"local.return"(%r,%r)')
    reject_native(bad, [['1', '2']])

with case('same-helper-two-invocations-have-fresh-ssa-values'):
    source = base.replace('"protocol.return"(%result)',
        '%second = "protocol.local_call"(%result,%a1) {callee=@work,role="P",site="second"} : (ui64,ui64)->ui64\n"protocol.return"(%second)')
    export(source)
    assert run(source, ['7', '3']) == returned(['13'])

with case('unsupported-unused-math-and-dormant-local-arm'):
    unused = 'func.func private @dormant(%a:ui64,%b:ui64) -> i1 { %r = "data.index_less"(%a,%b) : (ui64,ui64)->i1\nreturn %r : i1 }'
    source = base.replace(binding('index.add'), unused + '\n' + binding('index.add'))
    export(source, refusal='structured-source-operation')
    run(source, ['1', '2'], refusal='structured-reference-unsupported')
    body = f'''"local.if"(%a0,%a1) ({{ ^yes(%xs:{vector}):
      "local.yield"() : ()->()
    }}, {{ ^no(%xs:{vector}):
      %r = "algebra.exec.vector_product"(%xs) {{binding=@operation,parameters=[],site="dormant"}} : ({vector})->{field}
      "local.yield"() : ()->()
    }}) {{site="choose"}} : (i1,{vector})->()'''
    source = wrapped(['i1', vector], [], body, [], binding('vector.product'))
    export(source, refusal='structured-source-binding')
    run(source, [True, []], refusal='structured-reference-binding')

with case('dormant-map-declaration-is-not-filtered'):
    declarations = (f'func.func private @formula(%x:{field}) -> {field} {{ return %x : {field} }}\n'
                    f'algebra.map_realize @dormant = @formula [true] : ({vector})->{vector}\n')
    source = base.replace(binding('index.add'), declarations + binding('index.add'))
    snapshot = export(source)
    assert any(row[1] == 'dormant' for row in snapshot[7])
    assert run(source, ['1', '2']) == returned(['3'])
    source = source.replace(f'algebra.map_realize @dormant = @formula [true] : ({vector})->{vector}',
                            f'local.realize @dormant = @formula : ({field})->{field}')
    snapshot = export(source)
    assert any(row[1] == 'dormant' for row in snapshot[7])
    assert run(source, ['1', '2']) == returned(['3'])

with case('strict-dropped-results-and-zero-result-local-stop'):
    for contract, inputs in [('index.div', ['1', '0']), ('vector.split', [[]])]:
        source = primitive(contract, drop=True)
        export(source)
        assert run(source, inputs) == stopped()
        assert run(source, [None] * len(inputs), role='V') == returned([])
        assert run(source, [None] * len(inputs)) == stopped('incomplete', 'call')
    source = primitive('index.div', drop=True).replace('"protocol.return"()',
        '%later = "protocol.exchange"(%a0) {sender="P",receiver="V",site="later"} : (ui64)->ui64\n"protocol.return"()')
    export(source)
    assert run(source, ['1', '0']) == stopped()

with case('vector-observer-capacity-distinct-from-source-refusal'):
    assert run(primitive('vector.append'), [['0'] * 4095, '1']) == returned([['0'] * 4095 + ['1']])
    assert run(primitive('vector.length'), [['0'] * 4096]) == returned(['4096'])
    assert run(primitive('vector.sum'), [['1'] * 4096]) == returned(['4096'])
    assert run(primitive('vector.equal'), [['1'] * 4096, ['1'] * 4096]) == returned([True])
    run(primitive('vector.append'), [['0'] * 4096, '1'], refusal='structured-reference-capacity')
    run(primitive('vector.length'), [['0'] * 4097], refusal='structured-reference-capacity')
    run(primitive('vector.sum'), [['0'] * 64], capacity=32, refusal='structured-reference-capacity')
    run(primitive('vector.sum'), [[str(modulus)]], refusal='structured-reference-input')

with case('received-vector-malformation-and-capacity-stay-distinct'):
    source = primitive('vector.sum').replace('%result = "protocol.local_call"(%a0)',
        f'%received = "protocol.exchange"(%a0) {{sender="P",receiver="V",site="receive"}} : ({vector})->{vector}\n%result = "protocol.local_call"(%received)')
    source = source.replace('callee=@work,role="P"', 'callee=@work,role="V"').replace('output_roles=[["P"]]', 'output_roles=[["V"]]')
    export(source)
    action = ['receive', 'receive', 'P', 'V', ['vector', 'bls12-381.fr']]
    def replies(value):
        return [['reply', action, ['value', value]]]
    assert run(source, [None], role='V', replies=replies(['3', '7'])) == [
        'zkc.structured-open-result/0', ['returned', ['10']],
        [['request', 0, action], ['reply', 0, ['value', ['3', '7']]]], 1]
    assert run(source, [None], role='V', replies=replies([str(modulus)])) == [
        'zkc.structured-open-result/0', ['stopped', 'refused', 'receive'],
        [['request', 0, action], ['stop', 'refused', 'receive', 0]], 0]
    run(source, [None], role='V', replies=replies(['0'] * 4097), refusal='structured-reference-capacity')


def frontend(label):
    caller = fixtures / 'primitive-callers.zkc'
    modules = {re.search(r'^module\s+([\w:]+)\s*;', path.read_text(), re.M)[1]: path
               for path in [caller, *sorted((root / 'libraries/zkc').glob('*.zkc'))]}
    before = {str(path): hashlib.sha256(path.read_bytes()).hexdigest() for path in modules.values()}
    commands.write(label + '-inputs.json', before)
    flags = ['--source-format=zkc', '--entry=primitive_examples::' + label + 'Entry',
             *[f'--module={name}={path}' for name, path in sorted(modules.items())]]
    source = commands.run([compiler, 'language-emit', *flags], keep=label + '.mlir')
    interface = json.loads(commands.run([compiler, 'language-interface', *flags], keep=label + '-interface.json'))
    assert before == {str(path): hashlib.sha256(path.read_bytes()).hexdigest() for path in modules.values()}
    assert interface['original'] == hashlib.sha256(source.encode()).hexdigest()
    snapshot = export(source, interface['protocol'], keep=label + '-structured.json')
    assert snapshot[2] == 'sha256:' + interface['original']
    # Whole emitter bytes go directly to export and reference. No extraction or
    # post-emission deletion of declarations/branches is used for positive cases.
    assert not any(op in source for op in ['"local.realize"', '"algebra.map_realize"',
                                          '"protocol.apply"', '"protocol.repeat"'])
    return source, interface['protocol'], snapshot


captured = {}
for label in ('Shape', 'Table', 'Halves', 'Sequence', 'PureIndex'):
    with case('unchanged-library-whole-closure-' + label):
        captured[label] = frontend(label)


def run_capture(label, inputs, role=0):
    source, symbol, data = captured[label]
    protocol = next(row for row in data[7] if row[1] == symbol)
    return run(source, inputs, symbol, role=protocol[6][1][role])

with case('actual-multilinear-shape-guards-and-contiguous-halves'):
    shape, shape_symbol, shape_data = captured['Shape']
    table, table_symbol, _ = captured['Table']
    halves, halves_symbol, halves_data = captured['Halves']
    assert any(row[8] and row[8][0] == 's3h7a6b6311h6d756c74696c696e6561724h726f7773' for row in shape_data[7])
    assert any(row[8] and row[8][0] == 's3h7a6b6311h6d756c74696c696e6561726h68616c766573' for row in halves_data[7])
    valid = [['1', '7', '2', '9'], '1', '2']
    assert run_capture('Shape', valid) == returned([True])
    assert run_capture('Table', valid) == returned(valid)
    assert run_capture('Halves', valid) == returned([['1', '7'], ['2', '9']])
    for inputs in [[[], '0', '0'], [[], '64', '1'], [['1', '2', '3'], '1', '2'], [[], '0', '1']]:
        assert run_capture('Shape', inputs) == returned([False])
        assert run_capture('Table', inputs)[1][0:2] == ['stopped', 'reject']
    assert run_capture('Shape', [['9'], '0', '1']) == returned([True])
    assert run_capture('Table', [['9'], '0', '1']) == returned([['9'], '0', '1'])
    assert run_capture('Halves', [['9'], '0', '1'])[1][0:2] == ['stopped', 'reject']

with case('independent-vector-integer-example'):
    assert run_capture('Sequence', [['3', '8'], '5', '2']) == returned([['3', '8', '5'], '1', '1', '2', '16', False, False, []])
    assert run_capture('Sequence', [[], '5', '1']) == returned([['5'], '1', '0', '0', '5', False, True, []])
    assert run_capture('Sequence', [[], '5', '0'])[1][0:2] == ['stopped', 'refused']

with case('pure-index-distinct-descriptors-and-availability'):
    source, symbol, data = captured['PureIndex']
    assert data[6] == []
    ops = data[7][-1][9][1]
    assert [op[0] for op in ops] == [['index.constant', '0'], ['index.equal']]
    assert all(op[4] == '' for op in ops)
    assert run_capture('PureIndex', ['0']) == returned([True])
    assert run_capture('PureIndex', [str(maximum)]) == returned([False])
    assert run_capture('PureIndex', [None]) == returned([None])
    assert run_capture('PureIndex', ['0'], role=1) == returned([None])

commands.save()
print(f'structured-primitives: {counted()} cases')
