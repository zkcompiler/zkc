"""Original realization/map metadata and independent whole-source SSA behavior."""
import hashlib
import json
import re
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
{sym_name="main",origin=["main",[]],function_type=()->(),roles=["P"],input_roles=[],output_roles=[]} : ()->()'''

def participant(inputs, outputs, values=None, roles='["P"]'):
    args = [f'%p{i}' for i in range(len(inputs))]
    result = [f'%r{i}' for i in range(len(outputs))]
    produced = ','.join(result) + ' = ' if result else ''
    values = args if values is None else values
    return f'''"protocol.func"() ({{
^entry({','.join(f'{v}:{t}' for v,t in zip(args,inputs))}):
{produced}"protocol.local_call"({','.join(values)}) {{callee=@work,role="P",site="work"}} : ({','.join(inputs)})->({','.join(outputs)})
"protocol.return"({','.join(result)}) : ({','.join(outputs)})->()
}}) {{sym_name="main",origin=["main",[]],function_type=({','.join(inputs)})->({','.join(outputs)}),roles={roles},input_roles=[{','.join('["P"]' for _ in inputs)}],output_roles=[{','.join('["P"]' for _ in outputs)}]}} : ()->()'''


def projection(outputs):
    inputs = ['!V','ui64','ui64']
    results = ['%xs','%dimension'][:len(outputs)]
    math_return = 'func.return' + (' ' + ','.join(results) + ' : ' + ','.join(outputs) if outputs else '')
    helper = 'func.func private @value(%xs:!V,%dimension:ui64,%width:ui64)->(' + ','.join(outputs) + ') {\n' + math_return + '\n}'
    result_names = [f'%r{i}' for i in range(len(outputs))]
    body = invocation('exec.compute', inputs, outputs, 'callee=@value,site="realize"', names=result_names)
    work = scoped_function('work', inputs, outputs, body, result_names)
    return wrap_unit(helper + '\n' + work + '\n' + participant(inputs, outputs))


def reference_chain(edges, preparation='map', reverse=False):
    # Actual native references: main -> work -> row -> hN ... h0 for
    # collections; main -> work -> hN ... h0 for computations.
    overhead = 3 if preparation == 'map' else 2
    helpers = ['func.func private @h0(%x:!F)->!F { func.return %x : !F }']
    for i in range(1, edges - overhead + 1):
        helpers.append(f'''func.func private @h{i}(%x:!F)->!F {{
%r = func.call @h{i - 1}(%x) : (!F)->!F
func.return %r : !F }}''')
    if reverse:
        helpers.reverse()
    target = f'h{edges - overhead}'
    if preparation == 'map':
        helpers.append('''"data.domain"() ({
^entry(%xs:!V):
%rows = "data.domain_elements"(%xs) : (!V)->!data.domain<!F>
"data.domain_yield"(%rows) : (!data.domain<!F>)->()
}) {sym_name="rows",sym_visibility="private",function_type=(!V)->!data.domain<!F>} : ()->()''')
        body = invocation('exec.compute',['!F'],['!F'],f'callee=@{target},site="compute"',values=['%a0'])
        helpers.append(scoped_function('row',['!F','!V'],['!F'],body,['%r'],private=True))
        inputs = ['!V']
        body = invocation('exec.collect', inputs, inputs, 'domain=@rows,body=@row,site="map"')
    else:
        inputs = ['!F']
        body = invocation('exec.compute', inputs, inputs, f'callee=@{target},site="compute"')
    helpers.append(scoped_function('work',inputs,inputs,body,['%r']))
    helpers.append(participant(inputs,inputs,roles='["P","V"]'))
    return wrap_unit('\n'.join(helpers))


def instruction_budget_source(constants, extra=False):
    body = '\n'.join(f'%c{i} = "algebra.constant"() {{value="0"}} : ()->!F' for i in range(constants))
    helper = 'func.func private @formula(%x:!F)->!F {\n' + body + '\nfunc.return %x : !F }'
    body = invocation('exec.compute',['!F'],['!F'],'callee=@formula,site="compute"')
    work = scoped_function('work',['!F'],['!F'],body,['%r'])
    if extra:
        helper += '\nfunc.func private @unused(%x:!F)->!F { %y = algebra.field_add %x,%x : (!F,!F)->!F func.return %y : !F }'
    return wrap_unit(helper + '\n' + work + '\n' + empty_main)



mapped = (fixtures / 'map-declarations.mlir').read_text()
realized = (fixtures / 'realization-projection.mlir').read_text()
vector_type = ['vector', 'bls12-381.fr']
field_type = ['field', 'bls12-381.fr']
map_args = [['2', '7'], ['11', '13'], ['8', '9'], '3']

with case('exact-original-declaration-records-and-full-projection-abi'):
    snapshot = export(mapped)
    assert len(snapshot) == 11
    collection = next(row for row in snapshot[7] if row[0] == 'collect')
    assert collection[2:] == ['private', [vector_type] * 3 + [field_type],
                             [vector_type], 'rows', 'row', '']
    assert snapshot[4] == [['domain','rows',[vector_type]*3,
                           [['elements',0],['elements',1],['elements',2],['zip',[2,1,0]]],0]]
    assert [row[1] for row in snapshot[7] if row[0] == 'function'] == ['square','formula','row','work','main']
    snapshot = export(realized)
    computation = next(row for row in snapshot[7] if row[0] == 'realize')
    assert computation[2:] == [[vector_type, ['index'], ['index']], [vector_type], 'value']
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
    for outputs in [[], ['!V','ui64']]:
        source = projection(outputs)
        export(source)
        result = run(source, [['2', '7'], '9', maximum])
        assert result == returned([['2', '7'], '9'] if outputs else [])
        assert run(source, [['2', '7'], None, maximum]) == stopped('incomplete', 'work')



native_negatives = {
    'direct-protocol-math': (mapped, 'callee=@work,role=', 'callee=@formula,role='),
    'direct-protocol-computation-helper': (realized, 'callee=@work,role=', 'callee=@value,role='),
    'unknown-collection-attribute': (mapped, 'body=@row,site=', 'body=@row,extra="x",site='),
    'invented-collection-visibility': (mapped, 'body=@row,site=', 'body=@row,sym_visibility="private",site='),
    'invented-computation-origin': (realized, 'callee=@value,site=', 'callee=@value,logical_origin=["value",[]],site='),
    'missing-domain': (mapped, 'domain=@rows', 'domain=@missing'),
    'missing-body': (mapped, 'body=@row', 'body=@missing'),
    'wrong-domain-kind': (mapped, 'domain=@rows', 'domain=@formula'),
    'empty-domain-items': (mapped, '"data.domain_zip"(%as,%bs,%cs) : (!data.domain<!F>,!data.domain<!F>,!data.domain<!F>)', '"data.domain_zip"() : ()'),
    'short-domain-items': (mapped, '"data.domain_zip"(%as,%bs,%cs) : (!data.domain<!F>,!data.domain<!F>,!data.domain<!F>)', '"data.domain_zip"(%as,%bs) : (!data.domain<!F>,!data.domain<!F>)'),
    'long-domain-items': (mapped, '"data.domain_zip"(%as,%bs,%cs) : (!data.domain<!F>,!data.domain<!F>,!data.domain<!F>)', '"data.domain_zip"(%as,%bs,%cs,%cs) : (!data.domain<!F>,!data.domain<!F>,!data.domain<!F>,!data.domain<!F>)'),
    'wrong-domain-reference-type': (mapped, 'domain=@rows', 'domain="rows"'),
    'invented-computation-implementation': (realized, 'callee=@value,site=', 'callee=@value,implementation="chosen",site='),
    'wrong-domain-input-type': (mapped, '"data.domain_elements"(%a) : (!V)', '"data.domain_elements"(%a) : (!F)'),
    'missing-map-formula': (mapped, 'callee=@formula', 'callee=@missing'),
    'missing-computation-helper': (realized, 'callee=@value', 'callee=@missing'),
    'public-map-formula': (mapped, 'func.func private @formula', 'func.func @formula'),
    'public-computation-helper': (realized, 'func.func private @value', 'func.func @value'),
    'public-collection-body': (mapped, 'func.func private @row', 'func.func @row'),
    'wrong-kind-helper': (mapped, 'callee=@formula', 'callee=@work'),
    'dropped-computation-argument': (realized, '"exec.compute"(%scope,%a0,%a1,%a2)', '"exec.compute"(%scope,%a0,%a1)'),
    'computation-premise': (realized, '->!V {\n   func.return', '->!V attributes {data.preconditions=[#data.index_bound<1,0,0>]} {\n   func.return'),
    'domain-symbol-collision': (mapped, 'sym_name="rows"', 'sym_name="work"'),
    'binding-function-collision': (mapped, 'func.func @work', '"runtime.binding"() {sym_name="work",contract="index.add",arguments=[],implementation=""} : ()->()\nfunc.func @work'),
    'computation-symbol-collision': (realized, 'func.func private @value', 'func.func private @work'),
    'map-cycle': (mapped, '%r = "algebra.field_multiply"(%x,%x) : (!F,!F)->!F', '%r = func.call @square(%x) : (!F)->!F'),
    'computation-cycle': (realized, '   func.return %xs', '   %again = func.call @value(%xs,%dimension,%width) : (!V,ui64,ui64)->!V\n   func.return %again'),
    'unused-bad-map': (mapped, 'func.func @work', scoped_function('unused',['!V']*3+['!F'],['!V'],invocation('exec.collect',['!V']*3+['!F'],['!V'],'domain=@rows,body=@missing,site="map"'),['%r']) + '\nfunc.func @work'),
    'unused-bad-computation': (realized, 'func.func @work', scoped_function('unused',['!V','ui64','ui64'],['!V'],invocation('exec.compute',['!V','ui64','ui64'],['!V'],'callee=@missing,site="compute"'),['%r']) + '\nfunc.func @work'),
    'wrong-call-owner': (mapped, 'role="P",site="work"', 'role="V",site="work"'),
}
for label, (original, before, after) in native_negatives.items():
    with case('native-formation-' + label):
        assert before in original
        source = original.replace(before, after)
        assert source != original
        export(source, refusal='structured-source-original')
        run(source, [], refusal='structured-reference-source')

# General collection callbacks are not restricted to the old one-field ring
# recognizer. All actual operations still belong to admission, even if unused.
for label, operation in {
    'equality': '%bad = "algebra.field_equal"(%a,%b) : (!F,!F)->i1',
    'index': '%bad = "data.index"() {value="0"} : ()->ui64',
    'other-field': '%bad = "algebra.constant"() {value="1"} : ()->!algebra.field<"bn254.fr">',
    'other-lean-admitted-field': '%bad = "algebra.constant"() {value="1"} : ()->!algebra.field<"koala-bear">',
    'select': '%yes = arith.constant true\n%bad = arith.select %yes,%a,%b : !F',
}.items():
    with case('dead-collection-formula-' + label):
        source = mapped.replace('   func.return %p', operation + '\n   func.return %p')
        assert source != mapped
        export(source)
        if 'field' in label:
            run(source, [], refusal='structured-reference-unsupported')
        else:
            assert run(source, map_args) == returned([[str(modulus - 25), '147']])
        # Corrupt the unused operation's type: its result being unused cannot
        # hide an invalid instruction from native formation or either reader.
        invalid = (operation.replace('arith.select %yes', 'arith.select %a') if label == 'select'
                   else operation.replace('->', '->!runtime.scope //', 1))
        bad = source.replace(operation, invalid)
        assert bad != source
        export(bad, refusal='structured-source-original')
        run(bad, [], refusal='structured-reference-source')


with case('finite-realization-admission-preserves-original-declaration'):
    source = (fixtures / 'realization-finite.mlir').read_text()
    commands.verified(source)
    export(source)
    assert run(source, []) == returned([])
    # The same finite Math remains supported outside a realization closure.
    start = source.index(' func.func @realized(')
    end = source.index(' "protocol.func"', start)
    source = source[:start] + source[end:]
    assert 'exec.compute' not in source
    export(source)
    assert run(source, []) == returned([])

with case('finite-realization-executes-empty-and-ordered-domains'):
    source = (fixtures / 'realization-finite.mlir').read_text()
    source = source.replace(empty_main.replace('\n{sym_name', '\n {sym_name'), '''func.func @work(%scope:!runtime.scope,%xs:!V)->!exec.outcome<(!F)> attributes {no_inline,runtime.origin=["finite-sum",[]]} {
   %call = "func.call"(%scope,%xs) {callee=@realized,runtime.site="calculate"} : (!runtime.scope,!V)->!exec.outcome<(!F)>
   "exec.dispatch"(%call)[^done,^failed] : (!exec.outcome<(!F)>)->()
 ^done(%value:!F):
   %result = "exec.returned"(%value) : (!F)->!exec.outcome<(!F)>
   func.return %result : !exec.outcome<(!F)>
 ^failed(%stop:!exec.stop):
   %failure = "exec.failed"(%stop) : (!exec.stop)->!exec.outcome<(!F)>
   func.return %failure : !exec.outcome<(!F)>
 }
 "protocol.func"() ({
 ^entry(%xs:!V):
   %result = "protocol.local_call"(%xs) {callee=@work,role="P",site="work"} : (!V)->!F
   "protocol.return"(%result) : (!F)->()
 }) {sym_name="main",origin=["main",[]],function_type=(!V)->!F,roles=["P"],input_roles=[["P"]],output_roles=[["P"]]} : ()->()''')
    # The fixture indents its header; match the same declaration independently
    # of that leading whitespace without changing any body or realization.
    assert 'func.func @work' in source
    export(source)
    for private in [False, True]:
        candidate = source.replace('func.func @realized(', 'func.func private @realized(') if private else source
        export(candidate)
        for rows in [[], [1], [2, 5, 2], [modulus - 1, 2]]:
            assert run(candidate, [[str(value) for value in rows]]) == returned([str(sum(rows) % modulus)])

with case('dormant-realization-transitive-profile-and-dead-calls'):
    source = (fixtures / 'realization-finite.mlir').read_text()
    start = source.index(' func.func @realized(')
    end = source.index(' "protocol.func"', start)
    wrapper = source[start:end]
    changed = wrapper.replace('callee=@sum', 'callee=@projection').replace('!F', '!V')
    assert changed != wrapper and 'callee=@projection' in changed
    source = source[:start] + ''' func.func private @projection(%xs:!V)->!V {
   %unused = func.call @sum(%xs) : (!V)->!F
   func.return %xs : !V
 }
''' + changed + source[end:]
    commands.verified(source)
    export(source)
    assert run(source, []) == returned([])

with case('nested-realization-premise-needs-native-call-evidence'):
    source = realized.replace(' func.func private @value', '''
 func.func private @bounded(%xs:!V,%i:ui64)->!V attributes {data.preconditions=[#data.index_bound<1,0,0>]} {
   func.return %xs : !V
 }
 func.func private @value''', 1)
    marker = '   func.return %xs : !V\n }\nfunc.func @work'
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

with case('numeric-native-boolean-syntax-is-a-typed-boolean'):
    # Row ownership now lives in the actual domain, not a redundant mask.
    # Preserve the typed-Boolean syntax control on an actual Math operation.
    original = mapped.replace('   func.return %p', '   %yes = arith.constant true\n   func.return %p')
    source = original.replace('arith.constant true', 'arith.constant 1 : i1')
    assert source != original
    before, after = export(original), export(source)
    formula = next(row for row in after[7] if row[1] == 'formula')
    boolean = formula[9][1][-1][0]
    assert boolean == ['bool.constant', True] and type(boolean[1]) is bool
    assert before[2] != after[2]
    assert before[:2] + before[3:] == after[:2] + after[3:]
    assert run(source, map_args) == run(original, map_args)


with case('original-byte-digest-includes-comments-and-line-endings'):
    source = '// original bytes: \u03bb\r\n' + mapped.replace('\n', '\r\n')
    before, after = export(mapped), export(source)
    assert before[2] != after[2]
    assert before[:2] + before[3:] == after[:2] + after[3:]

with case('native-callback-name-bound-and-separate-wire-helper-bound'):
    # Finite callback keys obey the native Program name bound. Plain Math
    # references keep the separate structured-wire string bound.
    export(re.sub(r'@row\b', '@' + 'n' * 128, mapped))
    bad = re.sub(r'@row\b', '@' + 'n' * 129, mapped)
    export(bad, refusal='structured-source-original')
    assert 'local-realization-callback' in commands.last.stderr
    run(bad, [], refusal='structured-reference-source')
    for source, name in [(mapped, 'formula'), (realized, 'value')]:
        export(re.sub('@' + name + r'\b', '@' + 'h' * 512, source))
        bad = re.sub('@' + name + r'\b', '@' + 'h' * 513, source)
        export(bad, refusal='structured-source-limit')
        run(bad, [], refusal='structured-reference-capacity')

with case('computations-share-the-existing-definition-table-limit'):
    # value/work/main plus one derived computation, and 124 plain dormant
    # functions: the export table contains exactly 128 definitions.
    declarations = ''.join(f'func.func private @unused{i}(%x:!F)->!F {{ func.return %x : !F }}\n'
                           for i in range(124))
    source = realized.replace('func.func @work', declarations + 'func.func @work')
    assert len(export(source)[7]) == 128
    assert run(source, [['2'], '0', '1']) == returned([['2']])
    source = source.replace('func.func @work',
        'func.func private @extra(%x:!F)->!F { func.return %x : !F }\nfunc.func @work')
    export(source, refusal='structured-source-limit')
    # The independent interpreter counts native declarations, including the
    # actual scoped body; export-local derived rows are not native functions.
    assert run(source, [['2'], '0', '1']) == returned([['2']])
    source = source.replace('func.func @work',
        'func.func private @overflow(%x:!F)->!F { func.return %x : !F }\nfunc.func @work')
    run(source, [], refusal='structured-reference-capacity')


for preparation in ('map', 'realize'):
    derived_edges = 2 if preparation == 'map' else 1
    inputs = [['7']] if preparation == 'map' else ['7']
    for reverse in (False, True):
        with case(f'{preparation}-exported-reference-edges-63-64-65-reverse-{reverse}'):
            # The exported table inserts one declaration for Compute and one
            # for Collect. Keep the wire depth limit on that actual graph.
            for edges in [63,64]:
                source = reference_chain(edges - derived_edges, preparation, reverse)
                commands.verified(source)
                export(source)
                assert run(source, inputs) == returned(inputs)
            source = reference_chain(65 - derived_edges, preparation, reverse)
            commands.verified(source)
            export(source, refusal='structured-source-limit')
            if preparation == 'map':
                assert run(source, inputs) == returned(inputs)
            else:
                assert run(source, inputs, role='V') == returned([None])

        with case(f'{preparation}-native-reference-edges-63-64-65-reverse-{reverse}'):
            source = reference_chain(63, preparation, reverse)
            commands.verified(source)
            assert run(source, inputs) == returned(inputs)
            source = reference_chain(64, preparation, reverse)
            commands.verified(source)
            # The native observer starts invocation depth at one. It reaches
            # depth 65 only on a reached full path, even with ample fuel.
            if preparation == 'map':
                assert run(source, [[]]) == returned([[]])
            else:
                assert run(source, inputs, role='V') == returned([None])
            run(source, inputs, refusal='structured-reference-capacity')
            assert 'evaluation steps or depth' in commands.last.stderr
            source = reference_chain(65, preparation, reverse)
            commands.verified(source)
            run(source, inputs, role='V', refusal='structured-reference-capacity')
            assert 'reference depth' in commands.last.stderr

with case('derived-instruction-export-4096-4097'):
    # 4094 pure instructions, one actual Compute and its derived declaration.
    source = instruction_budget_source(4094)
    commands.verified(source)
    snapshot = export(source)
    assert len(snapshot[7]) == 4
    assert len(snapshot[7][0][9][1]) == 4094
    assert [row[0] for row in snapshot[7]] == ['function','function','function','realize']
    export(instruction_budget_source(4094, extra=True), refusal='structured-source-limit')

with case('independent-native-instruction-4096-4097'):
    # The native CFG observer additionally visits returned/failed packaging.
    # Its separate 4096-operation ceiling must remain exact as well.
    source = instruction_budget_source(4093)
    assert run(source, []) == returned([])
    run(instruction_budget_source(4093, extra=True), [], refusal='structured-reference-capacity')
    assert 'operations or signature' in commands.last.stderr

with case('retained-ssa-admission-is-distinct-from-optional-ring-selection'):
    body = []
    previous = '%a'
    for i in range(1024):
        body.append(f'%v{i} = algebra.field_add {previous}, %a : (!F,!F)->!F')
        previous = f'%v{i}'
    source = mapped.replace('   func.return %p', '\n'.join(body) + f'\n   func.return {previous}')
    export(source)
    assert run(source, map_args) == returned([['2050', '7175']])
    # A general collection can use the checked ordinary route if the optional
    # Ring recipe exceeds its capacity. Admission is not recipe selection.
    commands.verified(source, None, '--zkc-prepare-protocol')


with case('observer-capacity-is-not-map-refusal'):
    # 4 * 4096 tuple entries exceed the vector bound but fit the work budget.
    inputs = [['2'] * 4096, ['1'] * 4096, ['8'] * 4096, '3']
    assert run(mapped, inputs) == returned([['15'] * 4096])
    run(mapped, inputs, capacity=32, refusal='structured-reference-capacity')
    run(mapped, [['2'] * 4097, [], [], '3'], refusal='structured-reference-capacity')
    assert run(mapped, [['2'], [], [], '3']) == stopped()

with case('discarded-map-result-zero-result-wrapper-and-later-interaction'):
    start = mapped.index('func.func @work')
    end = mapped.index(' "protocol.func"', start)
    body = invocation('exec.collect',['!V']*3+['!F'],['!V'],'domain=@rows,body=@row,site="map"')
    work = scoped_function('work',['!V']*3+['!F'],[],body,[])
    source = mapped[:start] + work + '\n' + mapped[end:]
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
