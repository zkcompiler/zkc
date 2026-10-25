"""Original realization/map metadata and independent whole-source SSA behavior."""
import hashlib
import json
from pathlib import Path

from cases import case, counted
from commands import Commands
from entry_artifacts import compile_run_package
from tools import compiler, records
from project import project_inputs

commands = Commands(records())
root = Path(__file__).resolve().parents[2]
fixtures = Path(__file__).parent / 'fixtures/structured-source'
reference = Path(compiler).parent / 'test/zkc-structured_reference-test'
modulus = 52435875175126190479447740508185965837690552500527637822603658699938581184513
maximum = str((1 << 64) - 1)
serial = 0


def export(source, symbol='main', refusal=None, keep=None):
    result = commands.source('protocol-structured', source, '--symbol=' + symbol,
                             refuses=refusal, keep=keep)
    if refusal:
        return None
    snapshot = json.loads(result)
    assert snapshot[2] == 'sha256:' + hashlib.sha256(source.encode()).hexdigest()
    return snapshot


def run(source, inputs, symbol='main', role='P', replies=(), capacity=1000000, refusal=None):
    global serial
    serial += 1
    path = commands.directory / f'map-{serial}.mlir'
    path.write_text(source)
    request = commands.write(f'map-{serial}-request.json',
                             ['zkc.structured-open-request/0', role, inputs, list(replies), capacity])
    result = commands.run([reference, 'open', path, symbol, request], refuses=refusal,
                          keep=f'map-{serial}-result.json')
    return None if refusal else json.loads(result)


def returned(values):
    return ['zkc.structured-open-result/0', ['returned', values], [], 0]


def stopped(reason='refused', site='map'):
    return ['zkc.structured-open-result/0', ['stopped', reason, site],
            [['stop', reason, site, 0]], 0]


def wrap_unit(body):
    return '''!F = !algebra.field<"bls12-381.fr">
!V = !algebra.field_vector<"bls12-381.fr">
module { "protocol.module"() ({
''' + body + '\n}) {profile=#protocol.profile<protocol>} : ()->() }\n'

empty_main = '''"protocol.func"() ({ "protocol.return"() : ()->() })
{sym_name="main",function_type=()->(),roles=["P"],input_roles=[],output_roles=[]} : ()->()'''

def reference_chain(edges, preparation='map', reverse=False):
    # main -> work -> prepared -> hN -> ... -> h0: N + 3 edges.
    helpers = ['func.func private @h0(%x:!F)->!F { func.return %x : !F }']
    for i in range(1, edges - 2):
        helpers.append(f'''func.func private @h{i}(%x:!F)->!F {{
%r = func.call @h{i - 1}(%x) : (!F)->!F
func.return %r : !F }}''')
    if reverse:
        helpers.reverse()
    lifted = '!V' if preparation == 'map' else '!F'
    declaration = (f'algebra.map_realize @prepared = @h{edges - 3} [true] : (!V)->!V'
                   if preparation == 'map' else
                   f'local.realize @prepared = @h{edges - 3} : (!F)->!F')
    body = '\n'.join(helpers) + '\n' + declaration + f'''
local.func @work(%x:{lifted})->{lifted} attributes {{logical_origin=["work",[]]}} {{
%r = local.apply @prepared(%x) {{site="prepare"}} : ({lifted})->{lifted}
local.return %r : {lifted} }}
"protocol.func"() ({{
^entry(%x:{lifted}):
%r = "protocol.local_call"(%x) {{callee=@work,role="P",site="work"}} : ({lifted})->{lifted}
"protocol.return"(%r) : ({lifted})->()
}}) {{sym_name="main",function_type=({lifted})->{lifted},roles=["P","V"],input_roles=[["P"]],output_roles=[["P"]]}} : ()->()'''
    return wrap_unit(body)


def instruction_budget_source(extra=''):
    constants = '\n'.join(f'%c{i} = "algebra.constant"() {{value="0"}} : ()->!F' for i in range(4094))
    return wrap_unit('func.func private @formula(%x:!F)->!F {\n' + constants + '''
func.return %x : !F }
local.realize @realized = @formula : (!F)->!F
algebra.map_realize @mapped = @formula [true] : (!V)->!V
''' + extra + '\n' + empty_main)


mapped = (fixtures / 'map-declarations.mlir').read_text()
realized = (fixtures / 'realization-projection.mlir').read_text()
vector_type = ['vector', 'bls12-381.fr']
field_type = ['field', 'bls12-381.fr']
map_args = [['2', '7'], ['11', '13'], ['8', '9'], '3']

with case('exact-original-declaration-records-and-full-projection-abi'):
    snapshot = export(mapped)
    assert len(snapshot) == 10
    row = next(row for row in snapshot[7] if row[1] == 'mapped')
    assert row == ['map', 'mapped', [vector_type] * 3 + [field_type],
                   [vector_type], 'formula', [True, True, True, False]]
    assert [row[1] for row in snapshot[7]] == ['square', 'formula', 'mapped', 'work', 'main']
    snapshot = export(realized)
    assert snapshot[7][1] == ['realize', 'realized', [vector_type, ['index'], ['index']],
                              [vector_type], 'value']
    assert run(realized, [['2', '7'], maximum, maximum]) == returned([['2', '7']])
    assert run(realized, [['2', '7'], None, maximum]) == stopped('incomplete', 'work')

with case('map-actual-formula-ordered-rows-and-broadcast'):
    expected = [[str(modulus - 25), '147']]
    assert run(mapped, map_args) == returned(expected)
    # A valid different helper body must change the meaning, even with exactly
    # the same declaration and helper names.
    changed = mapped.replace('"algebra.field_subtract"(%sq,%b)', '"algebra.field_add"(%sq,%b)')
    export(changed)
    assert run(changed, map_args) == returned([['63', '251']])
    renamed = mapped.replace('@square', '@different').replace('@formula', '@another')
    export(renamed)
    assert run(renamed, map_args) == returned(expected)

with case('nested-zero-and-multiple-result-math-calls'):
    source = (fixtures / 'map-tuple-helpers.mlir').read_text()
    export(source)
    assert run(source, map_args) == returned([[str(modulus - 25), '147']])

with case('realization-total-profile-keeps-pure-index-and-group-values'):
    source = realized.replace('   func.return %xs',
        '   %max = "data.index"() {value="' + maximum + '"} : ()->ui64\n'
        '   %unused = "data.index_equal"(%max,%dimension) : (ui64,ui64)->i1\n'
        '   func.return %xs')
    export(source)
    assert run(source, [['2'], maximum, '1']) == returned([['2']])
    source = realized.replace('!algebra.field_vector<"bls12-381.fr">', '!algebra.group<"bls12-381.g1">')
    export(source)
    assert run(source, ['7', maximum, '1']) == returned(['7'])

with case('other-installed-fields-export-with-their-rows'):
    # The map profile lifts any installed field; Lean admits only its own rows.
    source = mapped.replace('bls12-381.fr', 'koala-bear')
    commands.verified(source)
    nominals, services = export(source)[9]
    assert nominals == [['nominal', 'koala-bear', 'Field', [],
                         ['TwoAdicField', 'Field', 'CommRing', 'CharacteristicNotTwo', 'PrimeField'],
                         '2130706433']] and services == []
    run(source, [], refusal='structured-reference-unsupported')

with case('shape-checks-include-unused-rows-and-empty-first-row'):
    assert run(mapped, [[], [], [], '3']) == returned([[]])
    for inputs in [[[], ['1'], [], '3'], [['2'], ['11'], [], '3'],
                   [['2'], [], ['8'], '3'], [[], [], ['8'], '3']]:
        assert run(mapped, inputs) == stopped()
    assert run(mapped, [[], [], [], None]) == stopped('incomplete', 'work')

with case('realization-preserves-zero-and-multiple-results'):
    # The root realization is not subject to the map's single result rule.
    for source in [realized.replace('->!V', '->(!V,ui64)')
                   .replace('func.return %xs : !V', 'func.return %xs,%dimension : !V,ui64')
                   .replace('%r =', '%r:2 =').replace('local.return %r : !V', 'local.return %r#0,%r#1 : !V,ui64')
                   .replace('"protocol.return"(%r) : (!V)', '"protocol.return"(%r#0,%r#1) : (!V,ui64)')
                   .replace('output_roles=[["P"]]', 'output_roles=[["P"],["P"]]'),
                   realized.replace('->!V', '->()').replace('func.return %xs : !V', 'func.return')
                   .replace('%r = ', '').replace('local.return %r : !V', 'local.return')
                   .replace('"protocol.return"(%r) : (!V)', '"protocol.return"() : ()')
                   .replace('output_roles=[["P"]]', 'output_roles=[]')]:
        export(source)
        result = run(source, [['2', '7'], '9', maximum])
        assert result == returned([['2', '7'], '9'] if '->(!V,ui64)' in source else [])
        assert run(source, [['2', '7'], None, maximum]) == stopped('incomplete', 'work')

native_negatives = {
    'direct-protocol-map': mapped.replace('callee=@work,role=', 'callee=@mapped,role='),
    'direct-protocol-realize': realized.replace('callee=@work,role=', 'callee=@realized,role='),
    'unknown-map-attribute': mapped.replace('[true, true, true, false] :', '[true, true, true, false] {extra="x"} :'),
    'invented-map-visibility': mapped.replace('[true, true, true, false] :', '[true, true, true, false] {sym_visibility="private"} :'),
    'invented-realize-origin': realized.replace('@realized = @value :', '@realized = @value {logical_origin=["value",[]]} :'),
    'no-row': mapped.replace('[true, true, true, false]', '[false, false, false, false]'),
    'short-mask': mapped.replace('[true, true, true, false]', '[true, true, false]'),
    'empty-mask': mapped.replace('[true, true, true, false]', '[]'),
    'long-mask': mapped.replace('[true, true, true, false]', '[true, true, true, false, false]'),
    'wrong-mask-attribute-type': mapped.replace(
        'algebra.map_realize @mapped = @formula [true, true, true, false] : (!V,!V,!V,!F)->!V',
        '"algebra.map_realize"() {sym_name="mapped",helper=@formula,function_type=(!V,!V,!V,!F)->!V,rowwise=array<i64: 1,1,1,0>} : ()->()'),
    'invented-realize-implementation': realized.replace('@realized = @value :', '@realized = @value {implementation="chosen"} :'),
    'wrong-lift': mapped.replace('[true, true, true, false]', '[true, true, false, true]'),
    'missing-map-helper': mapped.replace('@mapped = @formula', '@mapped = @missing'),
    'missing-realize-helper': realized.replace('@realized = @value', '@realized = @missing'),
    'public-map-helper': mapped.replace('func.func private @formula', 'func.func @formula'),
    'public-realize-helper': realized.replace('func.func private @value', 'func.func @value'),
    'wrong-kind-helper': mapped.replace('@mapped = @formula', '@mapped = @work'),
    'dropped-realize-argument': realized.replace('@realized = @value : (!V,ui64,ui64)', '@realized = @value : (!V,ui64)'),
    'realize-premise': realized.replace('->!V {\n   func.return', '->!V attributes {data.preconditions=[#data.index_bound<1,0,0>]} {\n   func.return'),
    'map-symbol-collision': mapped.replace('algebra.map_realize @mapped', 'algebra.map_realize @work'),
    'binding-preparation-collision': mapped.replace(' local.func @work',
        ' "local.binding"() {sym_name="mapped",contract="index.add",arguments=[],implementation=""} : ()->()\n local.func @work'),
    'realize-symbol-collision': realized.replace('local.realize @realized', 'local.realize @work'),
    'map-cycle': mapped.replace('%r = "algebra.field_multiply"(%x,%x) : (!F,!F)->!F', '%r = func.call @square(%x) : (!F)->!F'),
    'realize-cycle': realized.replace('   func.return %xs', '   %again = func.call @value(%xs,%dimension,%width) : (!V,ui64,ui64)->!V\n   func.return %again'),
    'unused-bad-map': mapped.replace(' local.func @work', ' algebra.map_realize @unused = @missing [true] : (!V)->!V\n local.func @work'),
    'unused-bad-realize': realized.replace(' local.func @work', ' local.realize @unused = @missing : (!V)->!V\n local.func @work'),
    'wrong-call-owner': mapped.replace('role="P",site="work"', 'role="V",site="work"'),
}
for label, source in native_negatives.items():
    with case('native-formation-' + label):
        export(source, refusal='structured-source-original')
        run(source, [], refusal='structured-reference-source')

for label, operation in {
    'equality': '%bad = "algebra.field_equal"(%a,%b) : (!F,!F)->i1',
    'index': '%bad = "data.index"() {value="0"} : ()->ui64',
    'other-field': '%bad = "algebra.constant"() {value="1"} : ()->!algebra.field<"bn254.fr">',
    'other-lean-admitted-field': '%bad = "algebra.constant"() {value="1"} : ()->!algebra.field<"koala-bear">',
    'select': '%yes = arith.constant true\n%bad = arith.select %yes,%a,%b : !F',
}.items():
    with case('dead-map-formula-' + label):
        source = mapped.replace('   func.return %p', operation + '\n   func.return %p')
        export(source, refusal='structured-source-original')
        run(source, [], refusal='structured-reference-source')

with case('finite-realization-admission-preserves-original-declaration'):
    source = (fixtures / 'realization-finite.mlir').read_text()
    commands.verified(source)
    export(source)
    assert run(source, []) == returned([])
    # The same finite Math remains supported outside a realization closure.
    source = source.replace(' local.realize @realized = @sum : (!V)->!F\n', '')
    export(source)
    assert run(source, []) == returned([])

with case('finite-realization-executes-empty-and-ordered-domains'):
    source = (fixtures / 'realization-finite.mlir').read_text()
    source = source.replace(empty_main.replace('\n{sym_name', '\n {sym_name'), '''local.func @work(%xs:!V)->!F attributes {logical_origin=["finite-sum",[]]} {
   %result = local.apply @realized(%xs) {site="calculate"} : (!V)->!F
   local.return %result : !F
 }
 "protocol.func"() ({
 ^entry(%xs:!V):
   %result = "protocol.local_call"(%xs) {callee=@work,role="P",site="work"} : (!V)->!F
   "protocol.return"(%result) : (!F)->()
 }) {sym_name="main",function_type=(!V)->!F,roles=["P"],input_roles=[["P"]],output_roles=[["P"]]} : ()->()''')
    # The fixture indents its header; match the same declaration independently
    # of that leading whitespace without changing any body or realization.
    assert 'local.func @work' in source
    export(source)
    for rows in [[], [1], [2, 5, 2], [modulus - 1, 2]]:
        assert run(source, [[str(value) for value in rows]]) == returned([str(sum(rows) % modulus)])

with case('dormant-realization-transitive-profile-and-dead-calls'):
    source = (fixtures / 'realization-finite.mlir').read_text()
    source = source.replace(' local.realize @realized = @sum : (!V)->!F', '''
 func.func private @projection(%xs:!V)->!V {
   %unused = func.call @sum(%xs) : (!V)->!F
   func.return %xs : !V
 }
 local.realize @realized = @projection : (!V)->!V''')
    commands.verified(source)
    export(source)
    assert run(source, []) == returned([])

with case('nested-realization-premise-needs-native-call-evidence'):
    source = realized.replace(' func.func private @value', '''
 func.func private @bounded(%xs:!V,%i:ui64)->!V attributes {data.preconditions=[#data.index_bound<1,0,0>]} {
   func.return %xs : !V
 }
 func.func private @value''', 1)
    marker = '   func.return %xs : !V\n }\n local.realize'
    assert source.count(marker) == 1
    source = source.replace(marker,
        '   %dead = func.call @bounded(%xs,%dimension) : (!V,ui64)->!V\n' + marker, 1)
    commands.verified(source, 'finite-bound')
    export(source, refusal='structured-source-original')
    run(source, [], refusal='structured-reference-source')

with case('native-valid-nested-realization-premise-via-finite-index-evidence'):
    source = (fixtures / 'realization-finite.mlir').read_text()
    source = source.replace('"data.domain_elements"(%xs)',
                            '"data.domain_indices"(%xs) {axis=0:i64}')
    source = source.replace('!data.domain<!F>', '!data.domain<ui64>')
    source = source.replace('@step(%acc:!F,%x:!F,%xs:!V)->!F {',
        '@step(%acc:!F,%x:ui64,%xs:!V)->!F attributes {data.preconditions=[#data.index_bound<1,2,0>]} {')
    source = source.replace('"algebra.field_add"(%acc,%x)', '"algebra.field_add"(%acc,%acc)')
    assert source.count('data.preconditions=') == 1
    commands.verified(source)
    # Internal callback premises are discharged at the finite binder.
    # This admits the computation without asserting unconditional return.
    export(source)
    assert run(source, []) == returned([])

with case('numeric-native-mask-syntax-is-a-typed-boolean'):
    original, numeric = '[true, true, true, false]', '[true, true, 1, false]'
    assert mapped.count(original) == 1
    source = mapped.replace(original, numeric, 1)
    assert source.count(numeric) == 1 and original not in source and source != mapped
    before, after = export(mapped), export(source)
    mask = next(row for row in after[7] if row[0] == 'map')[5]
    assert mask == [True, True, True, False] and all(type(row) is bool for row in mask)
    assert before[2] != after[2]
    assert before[:2] + before[3:] == after[:2] + after[3:]
    assert run(source, map_args) == run(mapped, map_args)

with case('original-byte-digest-includes-comments-and-line-endings'):
    source = '// original bytes: \u03bb\r\n' + mapped.replace('\n', '\r\n')
    before, after = export(mapped), export(source)
    assert before[2] != after[2]
    assert before[:2] + before[3:] == after[:2] + after[3:]

with case('native-preparation-name-bound-and-separate-wire-helper-bound'):
    for source, name in [(mapped, 'mapped'), (realized, 'realized')]:
        export(source.replace('@' + name, '@' + 'n' * 128))
        bad = source.replace('@' + name, '@' + 'n' * 129)
        export(bad, refusal='structured-source-original')
        run(bad, [], refusal='structured-reference-source')
    export(mapped.replace('@formula', '@' + 'h' * 512))
    bad = mapped.replace('@formula', '@' + 'h' * 513)
    export(bad, refusal='structured-source-limit')
    run(bad, [], refusal='structured-reference-capacity')

with case('preparations-share-the-existing-definition-table-limit'):
    declarations = ''.join(f' local.realize @unused{i} = @value : (!V,ui64,ui64)->!V\n'
                           for i in range(124))
    source = realized.replace(' local.func @work', declarations + ' local.func @work')
    assert len(export(source)[7]) == 128
    assert run(source, [['2'], '0', '1']) == returned([['2']])
    source = source.replace(' local.func @work',
        ' local.realize @extra = @value : (!V,ui64,ui64)->!V\n local.func @work')
    export(source, refusal='structured-source-limit')
    run(source, [], refusal='structured-reference-capacity')

for preparation in ('map', 'realize'):
    for reverse in (False, True):
        with case(f'{preparation}-reference-edges-63-64-65-reverse-{reverse}'):
            inputs = [['7']] if preparation == 'map' else ['7']
            source = reference_chain(63, preparation, reverse)
            commands.verified(source)
            export(source)
            assert run(source, inputs) == returned(inputs)

            # 64 edges are admitted. Runtime root depth is 1: entering the
            # last scalar helper would need depth 65, even with ample fuel.
            source = reference_chain(64, preparation, reverse)
            commands.verified(source)
            export(source)
            if preparation == 'map':
                assert run(source, [[]]) == returned([[]])
            else:
                assert run(source, inputs, role='V') == returned([None])
            run(source, inputs, refusal='structured-reference-capacity')
            assert 'evaluation steps or depth' in commands.last.stderr

            # Math has only 63 helper nodes here; native formation accepts it.
            # The full path includes the protocol, Local and preparation edges.
            source = reference_chain(65, preparation, reverse)
            commands.verified(source)
            export(source, refusal='structured-source-limit')
            run(source, inputs, role='V', refusal='structured-reference-capacity')
            assert 'reference depth' in commands.last.stderr

for extra in ('map', 'realize'):
    with case('derived-instruction-4096-4097-' + extra):
        # 4094 stored constant instructions + two dormant preparations.
        # Neither helper evaluation nor production Ring expansion is involved.
        source = instruction_budget_source()
        commands.verified(source)
        snapshot = export(source)
        assert len(snapshot[7]) == 4
        assert len(snapshot[7][0][9][1]) == 4094
        assert [row[0] for row in snapshot[7]] == ['function', 'realize', 'map', 'function']
        assert run(source, []) == returned([])
        declaration = ('algebra.map_realize @extra = @formula [true] : (!V)->!V'
                       if extra == 'map' else
                       'local.realize @extra = @formula : (!F)->!F')
        source = instruction_budget_source(declaration)
        commands.verified(source)
        export(source, refusal='structured-source-limit')
        run(source, [], refusal='structured-reference-capacity')
        assert 'preparation instructions' in commands.last.stderr

with case('retained-ssa-admission-is-distinct-from-expanded-ring-capacity'):
    body = []
    previous = '%x'
    for i in range(1024):
        body.append(f'%v{i} = algebra.field_add {previous}, %x : (!F,!F)->!F')
        previous = f'%v{i}'
    source = '''!F = !algebra.field<"bls12-381.fr">
!V = !algebra.field_vector<"bls12-381.fr">
module { "protocol.module"() ({
func.func private @chain(%x:!F)->!F {
''' + '\n'.join(body) + f'\nfunc.return {previous} : !F\n' + '''}
algebra.map_realize @mapped = @chain [true] : (!V)->!V
"protocol.func"() ({ "protocol.return"() : ()->() })
{sym_name="main",function_type=()->(),roles=["P"],input_roles=[],output_roles=[]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }'''
    export(source)
    assert run(source, []) == returned([])
    commands.verified(source, 'algebra-map-formula', '--zkc-prepare-protocol')

with case('observer-capacity-is-not-map-refusal'):
    # 4 * 4096 tuple entries exceed the vector bound but fit the work budget.
    inputs = [['2'] * 4096, ['1'] * 4096, ['8'] * 4096, '3']
    assert run(mapped, inputs) == returned([['15'] * 4096])
    run(mapped, inputs, capacity=32, refusal='structured-reference-capacity')
    run(mapped, [['2'] * 4097, [], [], '3'], refusal='structured-reference-capacity')
    assert run(mapped, [['2'], [], [], '3']) == stopped()

with case('discarded-map-result-zero-result-wrapper-and-later-interaction'):
    source = mapped.replace('local.func @work(%a:!V,%b:!V,%c:!V,%s:!F)->!V',
                            'local.func @work(%a:!V,%b:!V,%c:!V,%s:!F)->()')
    source = source.replace('local.return %r : !V', 'local.return')
    source = source.replace('%r = "protocol.local_call"', '"protocol.local_call"')
    source = source.replace('site="work"} : (!V,!V,!V,!F)->!V', 'site="work"} : (!V,!V,!V,!F)->()')
    source = source.replace('"protocol.return"(%r) : (!V)', '"protocol.return"() : ()')
    source = source.replace('function_type=(!V,!V,!V,!F)->!V', 'function_type=(!V,!V,!V,!F)->()')
    source = source.replace('roles=["P"]', 'roles=["P","V"]').replace('output_roles=[["P"]]', 'output_roles=[]')
    export(source)
    assert run(source, [[], ['1'], [], '3']) == stopped()
    assert run(source, [None] * 4) == stopped('incomplete', 'work')
    assert run(source, [None] * 4, role='V') == returned([])
    source = source.replace('"protocol.return"()',
        '%later = "protocol.exchange"(%a) {sender="P",receiver="V",site="later"} : (!V)->!V\n"protocol.return"()')
    export(source)
    assert run(source, [[], ['1'], [], '3']) == stopped()

with case('received-row-malformation-capacity-and-shape-remain-distinct'):
    source = mapped.replace('%r = "protocol.local_call"(%a,%b,%c,%s)',
        '%received = "protocol.exchange"(%a) {sender="P",receiver="V",site="receive"} : (!V)->!V\n'
        '%r = "protocol.local_call"(%received,%b,%c,%s)')
    source = source.replace('callee=@work,role="P"', 'callee=@work,role="V"')
    source = source.replace('roles=["P"]', 'roles=["P","V"]')
    source = source.replace('input_roles=[["P"],["P"],["P"],["P"]]', 'input_roles=[["P"],["V"],["V"],["V"]]')
    source = source.replace('output_roles=[["P"]]', 'output_roles=[["V"]]')
    export(source)
    action = ['receive', 'receive', 'P', 'V', vector_type]
    inputs = [None, ['11'], ['8'], '3']
    def replies(value):
        return [['reply', action, ['value', value]]]
    assert run(source, inputs, role='V', replies=replies([str(modulus)])) == [
        'zkc.structured-open-result/0', ['stopped', 'refused', 'receive'],
        [['request', 0, action], ['stop', 'refused', 'receive', 0]], 0]
    assert run(source, inputs, role='V', replies=replies([])) == [
        'zkc.structured-open-result/0', ['stopped', 'refused', 'map'],
        [['request', 0, action], ['reply', 0, ['value', []]], ['stop', 'refused', 'map', 1]], 1]
    run(source, inputs, role='V', replies=replies(['0'] * 4097), refusal='structured-reference-capacity')


def frontend(label):
    modules, assets = project_inputs(fixtures / 'map-callers.toml')
    assert not assets
    before = {str(path): hashlib.sha256(path.read_bytes()).hexdigest() for path in modules.values()}
    commands.write(label + '-inputs.json', before)
    flags = ['--source-format=zkc', '--entry=map_examples::' + label + 'Entry',
             *[f'--module={name}={path}' for name, path in sorted(modules.items())]]
    child = compile_run_package(commands, *flags)
    emitted = child['original'].encode()
    (commands.directory / (label + '.mlir')).write_bytes(emitted)
    assert (commands.directory / (label + '.mlir')).read_bytes() == emitted
    source = emitted.decode()
    interface = json.loads(child['interface'])
    (commands.directory / (label + '-interface.json')).write_text(child['interface'])
    assert before == {str(path): hashlib.sha256(path.read_bytes()).hexdigest() for path in modules.values()}
    assert interface['original'] == hashlib.sha256(emitted).hexdigest()
    snapshot = export(source, interface['protocol'], keep=label + '-structured.json')
    assert snapshot[2] == 'sha256:' + interface['original']
    assert not any(op in source for op in ['"protocol.apply"', '"protocol.repeat"'])
    return source, interface['protocol'], snapshot


captured = {}
for label in ('First', 'Prefix', 'LinearCombination', 'ConstantRows', 'RealizeValues'):
    with case('unchanged-library-whole-closure-' + label):
        captured[label] = frontend(label)


def run_capture(label, inputs, role=0):
    source, symbol, snapshot = captured[label]
    protocol = next(row for row in snapshot[7] if row[1] == symbol)
    return run(source, inputs, symbol, role=protocol[6][1][role])


with case('actual-multilinear-fix-first-and-prefix-with-projections'):
    values = ['1', '7', '4', '9', '2', '8', '6', '12']
    assert run_capture('First', [values, '2', '2', '3']) == returned([['4', '10', '10', '18'], '1', '2'])
    assert run_capture('Prefix', [values, '2', '2', ['3', '5']]) == returned([['34', '50'], '0', '2'])
    assert run_capture('Prefix', [values, '2', '2', []]) == returned([values, '2', '2'])
    assert run_capture('Prefix', [values, '2', '2', ['3', '5', '7']])[1][:2] == ['stopped', 'reject']
    assert run_capture('First', [[], '0', '0', '3'])[1][:2] == ['stopped', 'reject']
    for dimension in ['63', '64', maximum]:
        assert run_capture('First', [[], dimension, '1', '3'])[1][:2] == ['stopped', 'reject']
    assert run_capture('RealizeValues', [values, '2', '2']) == returned([values])
    assert run_capture('RealizeValues', [values, None, '2'])[1][:2] == ['stopped', 'incomplete']

with case('independent-fr-linear-combination-unused-inputs-and-broadcast-order'):
    inputs = ['3', ['2', '7'], '5', ['11', '13'], ['8', '9'], '17']
    assert run_capture('LinearCombination', inputs, role=1) == returned([None])
    assert run_capture('LinearCombination', inputs) == returned([[str(modulus - 46), str(modulus - 41)]])
    assert run_capture('LinearCombination', ['5', inputs[1], '3', *inputs[3:]]) == returned([[str(modulus - 20), str(modulus - 1)]])
    assert run_capture('LinearCombination', [*inputs[:4], ['8'], '17'])[1][:2] == ['stopped', 'refused']
    assert run_capture('LinearCombination', [*inputs[:5], None])[1][:2] == ['stopped', 'incomplete']
    assert run_capture('ConstantRows', [[], [], '17']) == returned([[]])
    assert run_capture('ConstantRows', [[], ['9'], '17'])[1][:2] == ['stopped', 'refused']
    assert run_capture('ConstantRows', [['2', '4'], ['9', '3'], '17']) == returned([['7', '7']])

commands.save()
print(f'structured-maps: {counted()} cases')
