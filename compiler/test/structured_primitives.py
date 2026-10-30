"""Retained primitive bindings, unchanged library closures, and independent SSA laws."""
import hashlib
import itertools
import json
from pathlib import Path

from cases import case, counted
from commands import Commands
from entry_artifacts import compile_run_package
from tools import compiler, records
from project import project_inputs
from scoped_sources import invocation, scoped_function

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
    inputs, outputs = catalogue[contract]
    signature = '(' + ','.join(['!runtime.scope'] + [ports[p] for p in inputs]) + ') -> !exec.outcome<(' + ','.join(ports[p] for p in outputs) + ')>'
    return ('"runtime.binding"() {sym_name=' + json.dumps(name) + ',contract=' + json.dumps(contract) +
            ',arguments=' + json.dumps(arguments) + ',implementation=' + json.dumps(implementation) + ',function_type=' + signature + '} : ()->()')


def wrapped(inputs, outputs, body, results, declarations='', after=''):
    args = ','.join(f'%a{i}:{t}' for i, t in enumerate(inputs))
    actuals = ','.join(f'%a{i}' for i in range(len(inputs)))
    ins, outs = ','.join(inputs), ','.join(outputs)
    scopes_in, scopes_out = json.dumps([['P']] * len(inputs)), json.dumps([['P']] * len(outputs))
    call_results = '' if not outputs else '%result = ' if len(outputs) == 1 else f'%result:{len(outputs)} = '
    returned_results = '' if not outputs else '%result' if len(outputs) == 1 else ','.join(f'%result#{i}' for i in range(len(outputs)))
    return f'''module {{ "protocol.module"() ({{
{declarations}
{scoped_function('work', inputs, outputs, body, results)}
"protocol.func"() ({{ ^entry({args}):
{call_results}"protocol.local_call"({actuals}) {{callee=@work,role="P",site="call"}} : ({ins})->({outs})
{after}
"protocol.return"({returned_results}) : ({outs})->()
}}) {{sym_name="main",origin=["main",[]],function_type=({ins})->({outs}),roles=["P","V"],input_roles={scopes_in},output_roles={scopes_out}}} : ()->()
}}) {{profile=#protocol.profile<protocol>}} : ()->() }}'''


def primitive(contract, parameters=(), drop=False, reverse=False, name='operation'):
    ins, outs = catalogue[contract]
    inputs, outputs = [ports[x] for x in ins], [ports[x] for x in outs]
    body = invocation('exec.apply', inputs, outputs,
        f'binding=@{name},parameters=[{", ".join(str(p) + " : ui64" for p in parameters)}],site="primitive"')
    results = ['%r'] if len(outputs) == 1 else [f'%r{i}' for i in range(len(outputs))]
    return wrapped(inputs, [] if drop else outputs, body,
                   [] if drop else list(reversed(results)) if reverse else results, binding(contract, name))


def reject_native(source, inputs):
    export(source, refusal='structured-source-original')
    run(source, inputs, refusal='structured-reference-source')


def logical(kind):
    name = {'i': 'index', 'b': 'bool', 'f': 'field', 'v': 'vector'}[kind]
    arguments = [['domain', 'Field', 'bls12-381.fr']] if kind in 'fv' else []
    return ['apply', name, arguments]


with case('all-fifteen-exact-bindings-and-descriptors'):
    for contract, (inputs, outputs) in catalogue.items():
        parameters = [str(maximum)] if contract == 'index.constant' else []
        snapshot = export(primitive(contract, parameters))
        assert len(snapshot) == 11 and snapshot[4:6] == [[], []]
        assert snapshot[6] == [['binding', 'operation', contract,
                                [] if contract.startswith('index.') else [['domain', 'Field', 'bls12-381.fr']], '',
                                [logical(x) for x in inputs], [logical(x) for x in outputs]]]
        work = snapshot[7][0]
        op = work[9][1][0]
        assert op[0] == ['exec', 'exec.apply', 'operation', [['natural', x] for x in parameters]]
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
    changed = source.replace('contract="index.sub"', 'contract="index.add"')
    export(changed)
    assert run(changed, ['9', '2']) == returned(['11'])

with case('unused-supported-bindings-retained-in-order-and-independently-admitted'):
    source = primitive('index.add')
    source = source.replace(binding('index.add'), binding('vector.split', 'unused') + '\n' + binding('index.add'))
    assert [b[1] for b in export(source)[6]] == ['unused', 'operation']
    assert run(source, ['1', '2']) == returned(['3'])
    bad = source.replace('contract="vector.split"', 'contract="vector.product"')
    bad = bad.replace('!exec.outcome<(' + vector + ',' + vector + ')>',
                      '!exec.outcome<(' + field + ')>')
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
    ('binding-port-contract', base.replace('contract="index.add"', 'contract="index.less"')),
    ('retired-per-primitive-operation', base.replace('exec.apply', 'algebra.exec.index_add')),
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
    with case('byte-spelling-is-not-a-native-parameter-' + literal[:24]):
        source = primitive('index.constant', [literal])
        source = source.replace(f'parameters=[{literal} : ui64]',
                                'parameters=' + json.dumps([literal]))
        reject_native(source, [])

with case('nominal-domain-profile-on-unused-binding'):
    source = primitive('index.add').replace(binding('index.add'),
        binding('vector.sum', 'unused').replace('bls12-381.fr', 'bn254.fr') + '\n' + binding('index.add'))
    # Another installed field is exported with its rows; Lean refuses it.
    assert [row[1] for row in export(source)[9][0]] == ['bn254.fr', 'bn254.g1', 'bn254.g2', 'bn254.gt']
    run(source, ['1', '2'], refusal='structured-reference-binding')
    reject_native(source.replace('bn254.fr', 'bls12-381.g1'), ['1', '2'])

with case('binding-visibility-is-not-silently-dropped'):
    source = base.replace('implementation=""', 'implementation="",sym_visibility="private"')
    reject_native(source, ['1', '2'])

with case('scoped-invocations-and-pure-computations-remain-distinct'):
    # A mathematical call cannot erase the implicit scope and outcome ABI.
    math = base.replace('"protocol.local_call"', '"func.call"').replace('callee=@work,role="P",site="call"', 'callee=@work')
    reject_native(math, ['1', '2'])
    protocol = base.replace('"protocol.local_call"(%a0,%a1) {callee=@work,role="P",site="call"}',
                            '"exec.apply"(%a0,%a1) {binding=@operation,parameters=[],site="call"}')
    reject_native(protocol, ['1', '2'])
    pure = base.replace('%value_attempt =', '%unscoped = "data.index"() {value=0 : ui64} : ()->ui64\n%value_attempt =')
    reject_native(pure, ['1', '2'])

with case('primitive-sites-and-split-full-result-abi'):
    duplicate = base.replace('%done =', invocation('exec.apply', ['ui64', 'ui64'], ['ui64'],
        'binding=@operation,parameters=[],site="primitive"', names=['%unused'], label='duplicate') + '\n%done =')
    reject_native(duplicate, ['1', '2'])
    # Keep the helper/caller two-result signature but use a single-result
    # outcome and dispatch payload for the two-result primitive binding.
    bad = wrapped([vector], [vector, vector],
        invocation('exec.apply', [vector], [vector], 'binding=@operation,parameters=[],site="primitive"'),
        ['%r', '%r'], binding('vector.split'))
    reject_native(bad, [['1', '2']])

with case('same-helper-two-invocations-have-fresh-ssa-values'):
    source = base.replace('"protocol.return"(%result)',
        '%second = "protocol.local_call"(%result,%a1) {callee=@work,role="P",site="second"} : (ui64,ui64)->ui64\n"protocol.return"(%second)')
    export(source)
    assert run(source, ['7', '3']) == returned(['13'])

with case('retained-unused-total-math-and-unsupported-dormant-scoped-arm'):
    unused = 'func.func private @dormant(%a:ui64,%b:ui64) -> i1 { %r = "data.index_less"(%a,%b) : (ui64,ui64)->i1\nreturn %r : i1 }'
    source = base.replace(binding('index.add'), unused + '\n' + binding('index.add'))
    export(source)
    assert run(source, ['1', '2']) == returned(['3'])
    path = commands.directory / 'dormant-arm.zkc'
    path.write_text('''module dormant;
domain Fr=field("bls12-381.fr");
type Vector<F:Field>=builtin("vector",F);
fn choose(go:bool,xs:Vector<Fr>,x:Fr)->Fr {
  return if go {x} else {kernel<Fr>("vector.sum",xs)};
}
protocol Run roles(P)(go:bool@P,xs:Vector<Fr>@P,x:Fr@P)->(r:Fr@P){return choose(go,xs,x);}
''')
    source = commands.run([compiler, 'language-emit', '--source-format=zkc',
        f'--module=dormant={path}', '--subject=dormant::Run'])
    symbol = 's7h646f726d616e743h52756e'
    snapshot = export(source, symbol)
    role = next(row for row in snapshot[7] if row[1] == symbol)[6][1][0]
    assert run(source, [True, [], '7'], symbol, role) == returned(['7'])
    assert run(source, [False, ['3', '5'], '7'], symbol, role) == returned(['8'])
    bad = source.replace('contract = "vector.sum"', 'contract = "vector.product"')
    assert bad != source
    commands.verified(bad)
    export(bad, symbol, refusal='structured-source-binding')
    run(bad, [True, [], '7'], symbol, role, refusal='structured-reference-binding')

with case('dormant-collection-and-computation-are-not-filtered'):
    formula = f'func.func private @formula(%x:{field}) -> {field} {{ return %x : {field} }}\n'
    domain = f'''"data.domain"() ({{^entry(%xs:{vector}):
      %items="data.domain_elements"(%xs):({vector})->!data.domain<{field}>
      "data.domain_yield"(%items):(!data.domain<{field}>)->()
    }}) {{sym_name="items",sym_visibility="private",function_type=({vector})->!data.domain<{field}>}}:()->()'''
    callback = scoped_function('item', [field, vector], [field], '', ['%a0'], private=True)
    collection = scoped_function('dormant', [vector], [vector],
        invocation('exec.collect', [vector], [vector], 'domain=@items,body=@item,site="collect"'), ['%r'])
    declarations = domain + callback + collection
    source = base.replace(binding('index.add'), declarations + binding('index.add'))
    snapshot = export(source)
    assert any(row[0:2] == ['function', 'dormant'] for row in snapshot[7])
    assert any(row[0] == 'collect' for row in snapshot[7])
    assert run(source, ['1', '2']) == returned(['3'])
    computation = scoped_function('dormant', [field], [field],
        invocation('exec.compute', [field], [field],
            'callee=@formula,site="compute",policy=[false,false,false]'), ['%r'])
    source = base.replace(binding('index.add'), formula + computation + binding('index.add'))
    snapshot = export(source)
    assert any(row[0:2] == ['function', 'dormant'] for row in snapshot[7])
    assert any(row[0] == 'realize' and row[4] == 'formula' for row in snapshot[7])
    assert run(source, ['1', '2']) == returned(['3'])

with case('numerical-selection-policies-do-not-change-source-meaning'):
    formula = f'func.func private @formula(%x:{field}) -> {field} {{ return %x : {field} }}'
    source = wrapped([field], [field], invocation('exec.compute', [field], [field],
        'callee=@formula,site="compute"'), ['%r'], formula)
    definitions = export(source)[7]
    assert run(source, ['7']) == returned(['7'])
    for options in itertools.product([False, True], repeat=3):
        policy = json.dumps(options)
        selected = source.replace('site="compute"', f'site="compute",policy={policy}')
        assert export(selected)[7] == definitions
        assert run(selected, ['7']) == returned(['7'])
    for policy in ['[]', '[true,false]', '[true,false,true,false]', '[true,false,1:i64]']:
        reject_native(source.replace('site="compute"', f'site="compute",policy={policy}'), ['7'])
    reject_native(source.replace('site="compute"', 'site="compute",unexpected=true'), ['7'])

with case('strict-dropped-results-and-zero-result-scoped-stop'):
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
    modules, assets = project_inputs(fixtures / 'primitive-callers.toml')
    assert not assets
    before = {str(path): hashlib.sha256(path.read_bytes()).hexdigest() for path in modules.values()}
    commands.write(label + '-inputs.json', before)
    flags = ['--source-format=zkc', '--entry=primitive_examples::' + label + 'Entry',
             *[f'--module={name}={path}' for name, path in sorted(modules.items())]]
    child = compile_run_package(commands, *flags)
    source = child['original']
    interface = json.loads(child['interface'])
    (commands.directory / (label + '.mlir')).write_text(source)
    (commands.directory / (label + '-interface.json')).write_text(child['interface'])
    assert before == {str(path): hashlib.sha256(path.read_bytes()).hexdigest() for path in modules.values()}
    assert interface['original'] == hashlib.sha256(source.encode()).hexdigest()
    snapshot = export(source, interface['protocol'], keep=label + '-structured.json')
    assert snapshot[2] == 'sha256:' + interface['original']
    # Whole emitter bytes go directly to export and reference. No extraction or
    # post-emission deletion of declarations/branches is used for positive cases.
    assert not any(op in source for op in ['"algebra.map_realize"',
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
    assert any(row[0] == 'function' and row[8] and row[8][0] == 's3h7a6b6311h6d756c74696c696e6561724h726f7773' for row in shape_data[7])
    assert any(row[0] == 'function' and row[8] and row[8][0] == 's3h7a6b6311h6d756c74696c696e6561726h68616c766573' for row in halves_data[7])
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
